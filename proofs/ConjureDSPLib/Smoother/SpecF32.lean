module

public import ConjureDSPLib.Code.Funs

/-!
# The smoother in f32: what the translated Rust does

The same two facts as `SpecF64.lean`, for `step_f32` and `process_f32`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.smoother

/-- One Rust smoother step is `state + (1 - a) * (target - state)` in binary32 arithmetic, in
that order, and cannot fail. -/
theorem step_f32_eq (a state target : Float32) :
    step_f32 a state target = ok (state + (1 - a) * (target - state)) := rfl

/-- The smoother on binary32 numbers, with `c` standing for the already computed `1 - a`: run it
over a list of input samples from state `s`, returning the final state and the list of outputs.
-/
def filt_f32 (c : Float32) : Float32 → List Float32 → Float32 × List Float32
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := s + c * (x - s)
    let r := filt_f32 c y xs
    (r.1, y :: r.2)

/-- One loop iteration on plain lists, as `one_pole.filt_f32_set_step`. -/
theorem filt_f32_set_step (c s : Float32) (l : List Float32) (j : ℕ) (hj : j < l.length) :
    (l.set j (s + c * (l[j] - s))).take (j + 1) ++
        (filt_f32 c (s + c * (l[j] - s))
          ((l.set j (s + c * (l[j] - s))).drop (j + 1))).2 =
      l.take j ++ (filt_f32 c s (l.drop j)).2 ∧
    (filt_f32 c (s + c * (l[j] - s))
        ((l.set j (s + c * (l[j] - s))).drop (j + 1))).1 =
      (filt_f32 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (s + c * (l[j] - s))).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (s + c * (l[j] - s))).take (j + 1) = l.take j ++ [s + c * (l[j] - s)] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_f32]

/-- The smoother's loop, started at position `i` with `c` already computed, leaves the first `i`
samples alone and smooths the rest. -/
theorem process_f32_loop_spec (state : Float32) (buf : Slice Float32) (c : Float32) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    process_f32_loop state buf c i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_f32 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_f32 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_f32_loop
  -- The same invariant as `one_pole.process_f32_loop_spec`, with this `filt_f32`.
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_f32 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_f32 c state (buf.val.drop i.val)).2 ∧
      (filt_f32 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_f32 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_f32_loop.body]
    step*
    · -- Still looping: rebuild the invariant one sample further on.
      subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_f32_set_step c st b.val j.val hjl
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

/-- The Rust smoother never fails, and its output samples and final state are exactly those of
`filt_f32` with `c = 1 - a` computed once in binary32, sample by sample. -/
theorem process_f32_spec (a state : Float32) (buf : Slice Float32) :
    process_f32 a state buf ⦃ fun r =>
      r.2.val = (filt_f32 (1 - a) state buf.val).2 ∧
      r.1 = (filt_f32 (1 - a) state buf.val).1 ⦄ := by
  -- `process_f32` computes `1 - a` with the literal `1` stored as its bit pattern; Lean sees
  -- that this is the same `1`.
  have h := process_f32_loop_spec state buf (1 - a) 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.take_zero, List.drop_zero, List.nil_append] at h
  exact h

end conjure_dsp_lib.smoother

end
