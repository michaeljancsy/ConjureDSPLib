module

public import ConjureDSPLib.Code.ConjureDspLib

/-!
# The state-variable filter in f32: what the translated Rust does

About `CoeffsF32.new`, `step_f32` and `process_f32` from `src/svf.rs`, as Aeneas translated
them. This file proves:

1. `CoeffsF32.new_eq`: the Rust constructor never fails, keeps `g`, `k` and the output mix, and
   computes `d` as exactly `1 / (1 + g * (g + k))` in Lean's `Float32` (IEEE binary32), in that
   order.
2. `step_f32_eq`: one Rust step is exactly `svfStep_f32` in binary32, in the Rust code's order,
   and never fails.
3. `process_f32_spec`: the Rust block loop never fails and produces exactly the outputs and final
   state of `filt_f32`, which applies `svfStep_f32` to each sample in turn.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.svf

/-- The Rust constructor never fails: it keeps `g`, `k`, `m_hp`, `m_bp` and `m_lp`, and computes
`d = 1 / (1 + g * (g + k))` in binary32, in that order (`1` is the binary32 number 1). -/
theorem CoeffsF32.new_eq (g k m_hp m_bp m_lp : Float32) :
    CoeffsF32.new g k m_hp m_bp m_lp =
      ok { g := g, k := k, d := 1 / (1 + g * (g + k)), m_hp := m_hp, m_bp := m_bp,
           m_lp := m_lp } := rfl

/-- One trapezoidal state-variable-filter step in binary32, high-pass signal first: the output
and the new state, computed in the same order as the Rust code. -/
def svfStep_f32 (c : CoeffsF32) (s : StateF32) (x : Float32) : Float32 × StateF32 :=
  let hp := (x - (c.k + c.g) * s.s1 - s.s2) * c.d
  let bp := c.g * hp + s.s1
  let lp := c.g * bp + s.s2
  (c.m_hp * hp + c.m_bp * bp + c.m_lp * lp, { s1 := c.g * hp + bp, s2 := c.g * bp + lp })

/-- One Rust step is exactly `svfStep_f32`, and cannot fail. -/
theorem step_f32_eq (c : CoeffsF32) (s : StateF32) (x : Float32) :
    step_f32 c s x = ok (svfStep_f32 c s x) := rfl

/-- The filter on binary32 numbers: run `svfStep_f32` over a list of input samples from state `s`,
returning the final state and the list of outputs. -/
def filt_f32 (c : CoeffsF32) : StateF32 → List Float32 → StateF32 × List Float32
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_f32 c (svfStep_f32 c s x).2 xs
    (r.1, (svfStep_f32 c s x).1 :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_f32_set_step (c : CoeffsF32) (s : StateF32) (l : List Float32) (j : ℕ)
    (hj : j < l.length) :
    (l.set j (svfStep_f32 c s l[j]).1).take (j + 1) ++
        (filt_f32 c (svfStep_f32 c s l[j]).2 ((l.set j (svfStep_f32 c s l[j]).1).drop (j + 1))).2 =
      l.take j ++ (filt_f32 c s (l.drop j)).2 ∧
    (filt_f32 c (svfStep_f32 c s l[j]).2 ((l.set j (svfStep_f32 c s l[j]).1).drop (j + 1))).1 =
      (filt_f32 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (svfStep_f32 c s l[j]).1).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (svfStep_f32 c s l[j]).1).take (j + 1) =
      l.take j ++ [(svfStep_f32 c s l[j]).1] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_f32]

/-- The loop, started at position `i`, leaves the first `i` samples alone and filters the rest.
`f ⦃ P ⦄` is Aeneas's notation for "running `f` never fails, and its result satisfies `P`". -/
theorem process_f32_loop_spec (c : CoeffsF32) (state : StateF32) (buf : Slice Float32)
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
      generalize hT : svfStep_f32 c st (↑b)[↑j] = T at h1 h2
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
theorem process_f32_spec (c : CoeffsF32) (state : StateF32) (buf : Slice Float32) :
    process_f32 c state buf ⦃ fun r =>
      r.2.val = (filt_f32 c state buf.val).2 ∧ r.1 = (filt_f32 c state buf.val).1 ⦄ := by
  simpa using process_f32_loop_spec c state buf 0#usize (by simp)

end conjure_dsp_lib.svf

end
