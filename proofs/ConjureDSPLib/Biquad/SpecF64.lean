module

public import ConjureDSPLib.Code.ConjureDspLib

/-!
# The biquad filter in f64: what the translated Rust does

About `step_f64` and `process_f64` from `src/biquad.rs`, as Aeneas translated them. This file
proves:

1. `step_f64_eq`: one Rust step is exactly the transposed-direct-form-II step `tdf2_f64` in
   Lean's `Float` (IEEE binary64), and never fails.
2. `process_f64_spec`: the Rust block loop never fails and produces exactly the outputs and final
   state of `filt_f64`, which applies `tdf2_f64` to each sample in turn.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.biquad

/-- One transposed-direct-form-II step in binary64: the output and the new state, computed in
the same order as the Rust code. -/
def tdf2_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Float × StateF64 :=
  let y := c.b0 * x + s.s1
  (y, { s1 := c.b1 * x - c.a1 * y + s.s2, s2 := c.b2 * x - c.a2 * y })

/-- One Rust step is exactly `tdf2_f64`, and cannot fail. -/
theorem step_f64_eq (c : CoeffsF64) (s : StateF64) (x : Float) :
    step_f64 c s x = ok (tdf2_f64 c s x) := rfl

/-- The filter on binary64 numbers: run `tdf2_f64` over a list of input samples from state `s`,
returning the final state and the list of outputs. -/
def filt_f64 (c : CoeffsF64) : StateF64 → List Float → StateF64 × List Float
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_f64 c (tdf2_f64 c s x).2 xs
    (r.1, (tdf2_f64 c s x).1 :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_f64_set_step (c : CoeffsF64) (s : StateF64) (l : List Float) (j : ℕ)
    (hj : j < l.length) :
    (l.set j (tdf2_f64 c s l[j]).1).take (j + 1) ++
        (filt_f64 c (tdf2_f64 c s l[j]).2 ((l.set j (tdf2_f64 c s l[j]).1).drop (j + 1))).2 =
      l.take j ++ (filt_f64 c s (l.drop j)).2 ∧
    (filt_f64 c (tdf2_f64 c s l[j]).2 ((l.set j (tdf2_f64 c s l[j]).1).drop (j + 1))).1 =
      (filt_f64 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (tdf2_f64 c s l[j]).1).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (tdf2_f64 c s l[j]).1).take (j + 1) =
      l.take j ++ [(tdf2_f64 c s l[j]).1] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_f64]

/-- The loop, started at position `i`, leaves the first `i` samples alone and filters the rest.
`f ⦃ P ⦄` is Aeneas's notation for "running `f` never fails, and its result satisfies `P`". -/
theorem process_f64_loop_spec (c : CoeffsF64) (state : StateF64) (buf : Slice Float)
    (i : Std.Usize) (hi : i.val ≤ buf.length) :
    process_f64_loop c state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_f64 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_f64_loop
  -- Invariant on the loop state `(s, b, j)`: the buffer keeps its length, and finishing the job
  -- from here (keep `b`'s first `j` samples, filter the rest from state `s`) gives the same answer
  -- as filtering from the start.
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).1 = (filt_f64 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_f64_loop.body, step_f64_eq]
    step*
    · -- Still looping: name the step's output and new state, then rebuild the invariant one
      -- sample further on.
      subst fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_f64_set_step c st b.val j.val hjl
      generalize hT : tdf2_f64 c st (↑b)[↑j] = T at h1 h2
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
      simp [hjl, filt_f64] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The Rust block-processing function never fails, and its output samples and final state are
exactly those of `filt_f64`, sample by sample. -/
theorem process_f64_spec (c : CoeffsF64) (state : StateF64) (buf : Slice Float) :
    process_f64 c state buf ⦃ fun r =>
      r.2.val = (filt_f64 c state buf.val).2 ∧ r.1 = (filt_f64 c state buf.val).1 ⦄ := by
  simpa using process_f64_loop_spec c state buf 0#usize (by simp)

end conjure_dsp_lib.biquad

end
