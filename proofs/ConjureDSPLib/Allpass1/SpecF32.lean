module

public import ConjureDSPLib.Code.Funs

/-!
# The first-order all-pass filter in f32: what the translated Rust does

About `coeff_f32`, `step_f32`, `process_f32`, `step_fma_f32` and `process_fma_f32` from
`src/allpass1.rs`, as Aeneas translated them. This file proves:

1. `coeff_f32_eq`: the design function computes exactly `(t - 1) / (t + 1)` with
   `t = libm.tanModel_f32 (PI * corner_hz / sample_rate_hz)`, and never fails.
2. `step_f32_eq`: one Rust step is exactly `apStep_f32`, `y = c * (x - y1) + x1` in Lean's
   `Float32` (IEEE binary32), with the new state `(x, y)`, and never fails.
3. `process_f32_spec`: the Rust block loop never fails and produces exactly the outputs and final
   state of `filt_f32`, which applies `apStep_f32` to each sample in turn.
4. `step_fma_f32_eq`, `process_fma_f32_spec`: the same for the fused functions, with
   `y = c.fma (x - y1) x1` (`apStep_fma_f32`, `filt_fma_f32`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.allpass1

/-- The design function computes exactly `(t - 1) / (t + 1)`, with
`t = libm.tanModel_f32 (PI * corner_hz / sample_rate_hz)` (multiplication first), each operation
in binary32; `1` is the binary32 number 1. It never fails (given the libm model). -/
theorem coeff_f32_eq (corner_hz sample_rate_hz : Float32) :
    coeff_f32 corner_hz sample_rate_hz =
      ok ((libm.tanModel_f32 (core.f32.consts.PI * corner_hz / sample_rate_hz) - 1) /
        (libm.tanModel_f32 (core.f32.consts.PI * corner_hz / sample_rate_hz) + 1)) := by
  simp only [coeff_f32, libm.math.tanf.tanf, bind_ok]
  rfl

/-- One all-pass step in binary32: the output `y = c * (x - y1) + x1` and the new state
`(x1, y1) = (x, y)`, computed in the same order as the Rust code. -/
def apStep_f32 (c : Float32) (s : StateF32) (x : Float32) : Float32 × StateF32 :=
  let y := c * (x - s.y1) + s.x1
  (y, { x1 := x, y1 := y })

/-- One Rust step is exactly `apStep_f32`, and cannot fail. -/
theorem step_f32_eq (c : Float32) (s : StateF32) (x : Float32) :
    step_f32 c s x = ok (apStep_f32 c s x) := rfl

/-- The filter on binary32 numbers: run `apStep_f32` over a list of input samples from state `s`,
returning the final state and the list of outputs. -/
def filt_f32 (c : Float32) : StateF32 → List Float32 → StateF32 × List Float32
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_f32 c (apStep_f32 c s x).2 xs
    (r.1, (apStep_f32 c s x).1 :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_f32_set_step (c : Float32) (s : StateF32) (l : List Float32) (j : ℕ)
    (hj : j < l.length) :
    (l.set j (apStep_f32 c s l[j]).1).take (j + 1) ++
        (filt_f32 c (apStep_f32 c s l[j]).2 ((l.set j (apStep_f32 c s l[j]).1).drop (j + 1))).2 =
      l.take j ++ (filt_f32 c s (l.drop j)).2 ∧
    (filt_f32 c (apStep_f32 c s l[j]).2 ((l.set j (apStep_f32 c s l[j]).1).drop (j + 1))).1 =
      (filt_f32 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (apStep_f32 c s l[j]).1).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (apStep_f32 c s l[j]).1).take (j + 1) =
      l.take j ++ [(apStep_f32 c s l[j]).1] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_f32]

/-- The loop, started at position `i`, leaves the first `i` samples alone and filters the rest.
`f ⦃ P ⦄` is Aeneas's notation for "running `f` never fails, and its result satisfies `P`". -/
theorem process_f32_loop_spec (c : Float32) (state : StateF32) (buf : Slice Float32)
    (i : Std.Usize) (hi : i.val ≤ buf.length) :
    process_f32_loop c state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_f32 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_f32 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_f32_loop
  -- Invariant on the loop state `(s, b, j)`: the buffer keeps its length, and finishing the job
  -- from here (keep `b`'s first `j` samples, filter the rest from state `s`) gives the same answer
  -- as filtering from the start.
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_f32 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_f32 c state (buf.val.drop i.val)).2 ∧
      (filt_f32 c x.1 (x.2.1.val.drop x.2.2.val)).1 = (filt_f32 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_f32_loop.body, step_f32_eq]
    step*
    · -- Still looping: name the step's output and new state, then rebuild the invariant one
      -- sample further on.
      subst fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_f32_set_step c st b.val j.val hjl
      generalize hT : apStep_f32 c st (↑b)[↑j] = T at h1 h2
      obtain ⟨y, s'⟩ := T
      step*
      subst s_post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: the whole buffer is processed.
      have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_f32] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The Rust block-processing function never fails, and its output samples and final state are
exactly those of `filt_f32`, sample by sample. -/
theorem process_f32_spec (c : Float32) (state : StateF32) (buf : Slice Float32) :
    process_f32 c state buf ⦃ fun r =>
      r.2.val = (filt_f32 c state buf.val).2 ∧ r.1 = (filt_f32 c state buf.val).1 ⦄ := by
  simpa using process_f32_loop_spec c state buf 0#usize (by simp)

/-! ## The fused functions -/

/-- One fused all-pass step in binary32: `y = c.fma (x - y1) x1`, `x - y1` rounded first, then
`c·(x - y1) + x1` rounded once; the new state is `(x, y)`. -/
def apStep_fma_f32 (c : Float32) (s : StateF32) (x : Float32) : Float32 × StateF32 :=
  let y := c.fma (x - s.y1) s.x1
  (y, { x1 := x, y1 := y })

/-- One fused Rust step is exactly `apStep_fma_f32`, and cannot fail. -/
theorem step_fma_f32_eq (c : Float32) (s : StateF32) (x : Float32) :
    step_fma_f32 c s x = ok (apStep_fma_f32 c s x) := by
  simp only [step_fma_f32, lift, bind_ok]
  rfl

/-- The fused filter on binary32 numbers: run `apStep_fma_f32` over a list of input samples from
state `s`, returning the final state and the list of outputs. -/
def filt_fma_f32 (c : Float32) : StateF32 → List Float32 → StateF32 × List Float32
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_fma_f32 c (apStep_fma_f32 c s x).2 xs
    (r.1, (apStep_fma_f32 c s x).1 :: r.2)

/-- One loop iteration on plain lists, for the fused filter. -/
theorem filt_fma_f32_set_step (c : Float32) (s : StateF32) (l : List Float32) (j : ℕ)
    (hj : j < l.length) :
    (l.set j (apStep_fma_f32 c s l[j]).1).take (j + 1) ++
        (filt_fma_f32 c (apStep_fma_f32 c s l[j]).2
          ((l.set j (apStep_fma_f32 c s l[j]).1).drop (j + 1))).2 =
      l.take j ++ (filt_fma_f32 c s (l.drop j)).2 ∧
    (filt_fma_f32 c (apStep_fma_f32 c s l[j]).2
        ((l.set j (apStep_fma_f32 c s l[j]).1).drop (j + 1))).1 =
      (filt_fma_f32 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (apStep_fma_f32 c s l[j]).1).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (apStep_fma_f32 c s l[j]).1).take (j + 1) =
      l.take j ++ [(apStep_fma_f32 c s l[j]).1] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_fma_f32]

/-- The fused loop, started at position `i`, leaves the first `i` samples alone and filters the
rest. -/
theorem process_fma_f32_loop_spec (c : Float32) (state : StateF32) (buf : Slice Float32)
    (i : Std.Usize) (hi : i.val ≤ buf.length) :
    process_fma_f32_loop c state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_fma_f32 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_fma_f32 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_fma_f32_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_fma_f32 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_fma_f32 c state (buf.val.drop i.val)).2 ∧
      (filt_fma_f32 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_fma_f32 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_fma_f32_loop.body, step_fma_f32_eq]
    step*
    · subst fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_fma_f32_set_step c st b.val j.val hjl
      generalize hT : apStep_fma_f32 c st (↑b)[↑j] = T at h1 h2
      obtain ⟨y, s'⟩ := T
      step*
      subst s_post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_fma_f32] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The fused Rust block-processing function never fails, and its output samples and final state
are exactly those of `filt_fma_f32`, sample by sample. -/
theorem process_fma_f32_spec (c : Float32) (state : StateF32) (buf : Slice Float32) :
    process_fma_f32 c state buf ⦃ fun r =>
      r.2.val = (filt_fma_f32 c state buf.val).2 ∧ r.1 = (filt_fma_f32 c state buf.val).1 ⦄ := by
  simpa using process_fma_f32_loop_spec c state buf 0#usize (by simp)

end conjure_dsp_lib.allpass1

end
