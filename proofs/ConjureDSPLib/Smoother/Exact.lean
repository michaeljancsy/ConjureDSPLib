module

public import ConjureDSPLib.OnePole.Exact
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The smoother in exact arithmetic

The smoother `y = y_prev + (1 - A) * (x - y_prev)` (`process_f64` / `process_f32` in
`src/smoother.rs`), on real numbers. This file proves:

1. `filt_real_eq_one_pole_filt_real`: it is the one-pole filter `one_pole.filt_real`
   (`y = x' + A * y_prev`) fed the inputs scaled by `1 - A`, with the same outputs and final
   state.
2. `filt_real_replicate`: from state `r`, a steady input `X` held for `n` samples gives the
   outputs `X + A^(k+1) * (r - X)` for `k = 0, ..., n - 1`, and so the final state
   `X + A^n * (r - X)`.
3. `tendsto_filt_real_replicate`: in exact arithmetic, when `|A| < 1`, that final state tends to
   `X` as `n` grows: a steady input settles on itself.
4. `filt_real_abs_le`: in exact arithmetic, when `|A| < 1`, from state `S` with every input at
   most `M` in size, every output and the final state are at most `|S| + |1 - A| * M / (1 - |A|)`
   in size (this is `smoother.outBound A M S`, defined in `Smoother/Block.lean`, which imports
   this file): the exact smoother is stable.
5. `replicate_output_between`, `replicate_output_closer`, `replicate_output_alternates`: about
   the outputs `X + A^(k+1) * (r - X)` of `filt_real_replicate`. When `0 ≤ A ≤ 1` each lies
   between `X` and `r` and is no farther from `X` than the one before (a glide with no
   overshoot); when `A < 0` and `r ≠ X`, consecutive outputs are on opposite sides of `X`.

These are about exact arithmetic only. In floating point the smoother and the one-pole round
differently, and the smoother need not land exactly on its input. The smoother's floating-point
error bounds are in `Block.lean`, `BlockF64.lean` and `BlockF32.lean`.
-/

@[expose] public section

namespace conjure_dsp_lib.smoother

/-- The smoother in exact real arithmetic: run it over a list of inputs from state `r`,
returning the final state and the list of outputs. -/
noncomputable def filt_real (A : ℝ) : ℝ → List ℝ → ℝ × List ℝ
  | r, [] => (r, [])
  | r, x :: xs =>
    let y := r + (1 - A) * (x - r)
    let t := filt_real A y xs
    (t.1, y :: t.2)

/-- In exact arithmetic the smoother is the one-pole filter `one_pole.filt_real` with every input
first multiplied by `1 - A`: the same outputs and the same final state, from any state `r`. -/
theorem filt_real_eq_one_pole_filt_real (A r : ℝ) (xs : List ℝ) :
    filt_real A r xs = one_pole.filt_real A r (xs.map fun x => (1 - A) * x) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    have e : r + (1 - A) * (x - r) = (1 - A) * x + A * r := by ring
    simp only [filt_real, one_pole.filt_real, List.map_cons, e, ih]

/-- A steady input `X` held for `n` samples, from state `r`: the `k`-th output (counting from 0)
is `X + A^(k+1) * (r - X)`, and the final state is `X + A^n * (r - X)`. -/
theorem filt_real_replicate (A r X : ℝ) (n : ℕ) :
    filt_real A r (List.replicate n X) =
      (X + A ^ n * (r - X), (List.range n).map fun k => X + A ^ (k + 1) * (r - X)) := by
  induction n generalizing r with
  | zero => simp [filt_real]
  | succ n ih =>
    have e : r + (1 - A) * (X - r) = X + A * (r - X) := by ring
    simp only [List.replicate_succ, filt_real, e, ih, List.range_succ_eq_map,
      List.map_cons, List.map_map, Prod.mk.injEq, List.cons.injEq]
    refine ⟨by ring, by ring, ?_⟩
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ]
    ring

/-- When `|A| < 1`, the smoother's state after a steady input `X` held for `n` samples tends to
`X` as `n` grows, from any starting state `r`. -/
theorem tendsto_filt_real_replicate (A r X : ℝ) (hA : |A| < 1) :
    Filter.Tendsto (fun n : ℕ => (filt_real A r (List.replicate n X)).1)
      Filter.atTop (nhds X) := by
  simp only [filt_real_replicate]
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hA).mul_const (r - X)
  have h2 := h.const_add X
  simpa using h2

/-- **Stability in exact arithmetic.** When `|A| < 1`, from state `S` with every input at most
`M ≥ 0` in size, every output of the exact smoother, and its final state, is at most
`|S| + |1 - A| * M / (1 - |A|)` in size, however long the block. -/
theorem filt_real_abs_le (A M S : ℝ) (hA : |A| < 1) (hM0 : 0 ≤ M) (xs : List ℝ)
    (hM : ∀ x ∈ xs, |x| ≤ M) :
    (∀ y ∈ (filt_real A S xs).2, |y| ≤ |S| + |1 - A| * M / (1 - |A|)) ∧
      |(filt_real A S xs).1| ≤ |S| + |1 - A| * M / (1 - |A|) := by
  rw [filt_real_eq_one_pole_filt_real]
  have hM' : ∀ x ∈ xs.map (fun x => (1 - A) * x), |x| ≤ |1 - A| * M := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hM z hz) (abs_nonneg _)
  exact one_pole.filt_real_abs_le_outBound A (|1 - A| * M) S hA
    (mul_nonneg (abs_nonneg _) hM0) _ hM'

/-- **No overshoot.** When `0 ≤ A ≤ 1`, the output `X + A^(k+1) * (r - X)` of a steady input `X`
from state `r` (`filt_real_replicate`) lies between `X` and `r`. -/
theorem replicate_output_between (A r X : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (k : ℕ) :
    min X r ≤ X + A ^ (k + 1) * (r - X) ∧ X + A ^ (k + 1) * (r - X) ≤ max X r := by
  have hp0 : 0 ≤ A ^ (k + 1) := pow_nonneg hA0 _
  have hp1 : A ^ (k + 1) ≤ 1 := pow_le_one₀ hA0 hA1
  rcases le_total X r with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor <;> nlinarith
  · rw [min_eq_right h, max_eq_left h]
    constructor <;> nlinarith

/-- **A glide.** When `0 ≤ A ≤ 1`, each output of a steady input `X` from state `r`
(`filt_real_replicate`) is no farther from `X` than the one before. -/
theorem replicate_output_closer (A r X : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (k : ℕ) :
    |X + A ^ (k + 2) * (r - X) - X| ≤ |X + A ^ (k + 1) * (r - X) - X| := by
  have hp0 : 0 ≤ A ^ (k + 1) := pow_nonneg hA0 _
  have e1 : X + A ^ (k + 2) * (r - X) - X = A * (A ^ (k + 1) * (r - X)) := by ring
  have e2 : X + A ^ (k + 1) * (r - X) - X = A ^ (k + 1) * (r - X) := by ring
  rw [e1, e2, abs_mul, abs_of_nonneg hA0]
  have := abs_nonneg (A ^ (k + 1) * (r - X))
  nlinarith

/-- **Alternation.** When `A < 0` and `r ≠ X`, consecutive outputs of a steady input `X` from
state `r` (`filt_real_replicate`) are on opposite sides of `X`: the product of their distances
from `X`, with sign, is negative. -/
theorem replicate_output_alternates (A r X : ℝ) (hA : A < 0) (hr : r ≠ X) (k : ℕ) :
    (X + A ^ (k + 1) * (r - X) - X) * (X + A ^ (k + 2) * (r - X) - X) < 0 := by
  have hne : A ^ (k + 1) * (r - X) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hA.ne) (sub_ne_zero.mpr hr)
  have hsq : 0 < (A ^ (k + 1) * (r - X)) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  have e : (X + A ^ (k + 1) * (r - X) - X) * (X + A ^ (k + 2) * (r - X) - X) =
      (A ^ (k + 1) * (r - X)) ^ 2 * A := by ring
  rw [e]
  exact mul_neg_of_pos_of_neg hsq hA

end conjure_dsp_lib.smoother

end
