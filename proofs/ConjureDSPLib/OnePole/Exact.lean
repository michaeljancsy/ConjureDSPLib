module

public import ConjureDSPLib.OnePole.Block
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The one-pole filter in exact arithmetic

The filter `y = x + A * y_prev` (`process_f64` / `process_f32` in `src/one_pole.rs`), on real
numbers. This file proves:

1. `filt_real_abs_le_outBound`: when `|A| < 1`, from state `S` with every input at most `M` in
   size, every output and the final state are at most `outBound A M S = |S| + M / (1 - |A|)` in
   size: the exact filter is stable.
2. `filt_real_replicate`: when `A ≠ 1`, from state `r`, a steady input `X` held for `n` samples
   gives the outputs `X / (1 - A) + A^(k+1) * (r - X / (1 - A))` for `k = 0, ..., n - 1`, and so
   the final state `X / (1 - A) + A^n * (r - X / (1 - A))`.
3. `tendsto_filt_real_replicate`: when `|A| < 1`, that final state tends to `X / (1 - A)` as `n`
   grows: a steady input settles at `X / (1 - A)`, not at `X`.

These are about exact arithmetic only. The floating-point error bounds are in `Block.lean`,
`BlockF64.lean` and `BlockF32.lean`.
-/

@[expose] public section

namespace conjure_dsp_lib.one_pole

/-- The induction behind `filt_real_abs_le_outBound`: a bound `B` with `M + |A|·B ≤ B` on the
state stays a bound on every output and on the final state. -/
theorem filt_real_abs_le_of_invariant (A M B : ℝ) (hB : M + |A| * B ≤ B) :
    ∀ (xs : List ℝ) (r : ℝ), (∀ x ∈ xs, |x| ≤ M) → |r| ≤ B →
      (∀ y ∈ (filt_real A r xs).2, |y| ≤ B) ∧ |(filt_real A r xs).1| ≤ B := by
  intro xs
  induction xs with
  | nil => intro r _ hr; exact ⟨by simp [filt_real], hr⟩
  | cons x xs ih =>
    intro r hM hr
    have hy : |x + A * r| ≤ B := by
      calc |x + A * r| ≤ |x| + |A * r| := abs_add_le _ _
        _ = |x| + |A| * |r| := by rw [abs_mul]
        _ ≤ M + |A| * B :=
          add_le_add (hM x (by simp)) (mul_le_mul_of_nonneg_left hr (abs_nonneg A))
        _ ≤ B := hB
    obtain ⟨h1, h2⟩ := ih (x + A * r) (fun z hz => hM z (List.mem_cons_of_mem _ hz)) hy
    refine ⟨?_, h2⟩
    intro y hy'
    simp only [filt_real, List.mem_cons] at hy'
    rcases hy' with rfl | hy'
    · exact hy
    · exact h1 y hy'

/-- **Stability in exact arithmetic.** When `|A| < 1`, from state `S` with every input at most
`M ≥ 0` in size, every output of the exact filter, and its final state, is at most
`outBound A M S = |S| + M / (1 - |A|)` in size, however long the block. -/
theorem filt_real_abs_le_outBound (A M S : ℝ) (hA : |A| < 1) (hM0 : 0 ≤ M) (xs : List ℝ)
    (hM : ∀ x ∈ xs, |x| ≤ M) :
    (∀ y ∈ (filt_real A S xs).2, |y| ≤ outBound A M S) ∧
      |(filt_real A S xs).1| ≤ outBound A M S := by
  obtain ⟨_, hSB, hB, _⟩ :=
    block_constants A 0 0 M S le_rfl le_rfl hM0 (by simpa using hA)
  exact filt_real_abs_le_of_invariant A M (outBound A M S) hB xs S hM hSB

/-- A steady input `X` held for `n` samples, from state `r`, when `A ≠ 1`: the `k`-th output
(counting from 0) is `X / (1 - A) + A^(k+1) * (r - X / (1 - A))`, and the final state is
`X / (1 - A) + A^n * (r - X / (1 - A))`. -/
theorem filt_real_replicate (A r X : ℝ) (hA : A ≠ 1) (n : ℕ) :
    filt_real A r (List.replicate n X) =
      (X / (1 - A) + A ^ n * (r - X / (1 - A)),
        (List.range n).map fun k => X / (1 - A) + A ^ (k + 1) * (r - X / (1 - A))) := by
  have h1 : (1 - A) ≠ 0 := sub_ne_zero.mpr (Ne.symm hA)
  induction n generalizing r with
  | zero => simp [filt_real]
  | succ n ih =>
    have e : X + A * r = X / (1 - A) + A * (r - X / (1 - A)) := by
      field_simp
      ring
    simp only [List.replicate_succ, filt_real, ih, List.range_succ_eq_map,
      List.map_cons, List.map_map, Prod.mk.injEq, List.cons.injEq]
    refine ⟨by rw [e]; ring, by rw [e]; ring, ?_⟩
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ]
    rw [e]
    ring

/-- When `|A| < 1`, the filter's state after a steady input `X` held for `n` samples tends to
`X / (1 - A)` as `n` grows, from any starting state `r`. -/
theorem tendsto_filt_real_replicate (A r X : ℝ) (hA : |A| < 1) :
    Filter.Tendsto (fun n : ℕ => (filt_real A r (List.replicate n X)).1)
      Filter.atTop (nhds (X / (1 - A))) := by
  have hA1 : A ≠ 1 := by
    intro h
    rw [h, abs_one] at hA
    exact lt_irrefl _ hA
  simp only [filt_real_replicate A r X hA1]
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hA).mul_const (r - X / (1 - A))
  have h2 := h.const_add (X / (1 - A))
  simpa using h2

end conjure_dsp_lib.one_pole

end
