module

public import ConjureDSPLib.Code.ConjureDspLib

/-!
# The translated f32 filter (single precision, what plug-in audio paths use)

The same two facts as `Spec.lean`, for the `f32` versions of the Rust functions.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.one_pole

/-- **Proof 1 (f32).** One Rust f32 step is `x + a * y_prev` in Lean's `Float32`, and cannot fail. -/
theorem step_f32_eq (a y_prev x : Float32) :
    step_f32 a y_prev x = ok (x + a * y_prev) := rfl

/-- The textbook filter on single-precision numbers. -/
def filt32 (a : Float32) : Float32 → List Float32 → Float32 × List Float32
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := x + a * s
    let r := filt32 a y xs
    (r.1, y :: r.2)

theorem filt32_set_step (a s : Float32) (l : List Float32) (j : ℕ) (hj : j < l.length) :
    (l.set j (l[j] + a * s)).take (j + 1) ++
        (filt32 a (l[j] + a * s) ((l.set j (l[j] + a * s)).drop (j + 1))).2 =
      l.take j ++ (filt32 a s (l.drop j)).2 ∧
    (filt32 a (l[j] + a * s) ((l.set j (l[j] + a * s)).drop (j + 1))).1 =
      (filt32 a s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (l[j] + a * s)).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (l[j] + a * s)).take (j + 1) = l.take j ++ [l[j] + a * s] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt32]

theorem process_f32_loop_spec (a state : Float32) (buf : Slice Float32) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    process_f32_loop a state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt32 a state (buf.val.drop i.val)).2 ∧
      r.1 = (filt32 a state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_f32_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt32 a x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt32 a state (buf.val.drop i.val)).2 ∧
      (filt32 a x.1 (x.2.1.val.drop x.2.2.val)).1 = (filt32 a state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_f32_loop.body, step_f32_eq]
    step*
    · subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt32_set_step a st b.val j.val hjl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt32] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- **Proof 3 (f32).** The Rust f32 block function never fails, and its outputs and final state
are exactly those of `filt32`, sample by sample. -/
theorem process_f32_spec (a state : Float32) (buf : Slice Float32) :
    process_f32 a state buf ⦃ fun r =>
      r.2.val = (filt32 a state buf.val).2 ∧ r.1 = (filt32 a state buf.val).1 ⦄ := by
  simpa using process_f32_loop_spec a state buf 0#usize (by simp)

end conjure_dsp_lib.one_pole

end
