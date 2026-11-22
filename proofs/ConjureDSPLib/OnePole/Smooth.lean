module

public import ConjureDSPLib.OnePole.Block
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The one-pole smoother on real numbers

The smoother `y = y_prev + (1 - A) * (x - y_prev)` (`smooth_f64` / `smooth_f32` in
`src/one_pole.rs`), in exact real arithmetic. This file proves:

1. `filt_smooth_real_eq_filt_real`: it is the one-pole filter `filt_real` (`y = x' + A * y_prev`)
   fed the inputs scaled by `1 - A`, with the same outputs and final state.
2. `filt_smooth_real_replicate`: from state `r`, a steady input `X` held for `n` samples gives
   the outputs `X + A^(k+1) * (r - X)` for `k = 0, ..., n - 1`, and so the final state
   `X + A^n * (r - X)`.
3. `tendsto_filt_smooth_real_replicate`: when `|A| < 1`, that final state tends to `X` as `n`
   grows: a steady input settles on itself.

These are about exact arithmetic only. In floating point the smoother and the one-pole round
differently, and no error bound for the smoother is proved here.
-/

@[expose] public section

namespace conjure_dsp_lib.one_pole

/-- The smoother in exact real arithmetic: run it over a list of inputs from state `r`,
returning the final state and the list of outputs. -/
noncomputable def filt_smooth_real (A : ℝ) : ℝ → List ℝ → ℝ × List ℝ
  | r, [] => (r, [])
  | r, x :: xs =>
    let y := r + (1 - A) * (x - r)
    let t := filt_smooth_real A y xs
    (t.1, y :: t.2)

/-- In exact arithmetic the smoother is the one-pole filter `filt_real` with every input first
multiplied by `1 - A`: the same outputs and the same final state, from any state `r`. -/
theorem filt_smooth_real_eq_filt_real (A r : ℝ) (xs : List ℝ) :
    filt_smooth_real A r xs = filt_real A r (xs.map fun x => (1 - A) * x) := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    have e : r + (1 - A) * (x - r) = (1 - A) * x + A * r := by ring
    simp only [filt_smooth_real, filt_real, List.map_cons, e, ih]

/-- A steady input `X` held for `n` samples, from state `r`: the `k`-th output (counting from 0)
is `X + A^(k+1) * (r - X)`, and the final state is `X + A^n * (r - X)`. -/
theorem filt_smooth_real_replicate (A r X : ℝ) (n : ℕ) :
    filt_smooth_real A r (List.replicate n X) =
      (X + A ^ n * (r - X), (List.range n).map fun k => X + A ^ (k + 1) * (r - X)) := by
  induction n generalizing r with
  | zero => simp [filt_smooth_real]
  | succ n ih =>
    have e : r + (1 - A) * (X - r) = X + A * (r - X) := by ring
    simp only [List.replicate_succ, filt_smooth_real, e, ih, List.range_succ_eq_map,
      List.map_cons, List.map_map, Prod.mk.injEq, List.cons.injEq]
    refine ⟨by ring, by ring, ?_⟩
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Nat.succ_eq_add_one, pow_succ]
    ring

/-- When `|A| < 1`, the smoother's state after a steady input `X` held for `n` samples tends to
`X` as `n` grows, from any starting state `r`. -/
theorem tendsto_filt_smooth_real_replicate (A r X : ℝ) (hA : |A| < 1) :
    Filter.Tendsto (fun n : ℕ => (filt_smooth_real A r (List.replicate n X)).1)
      Filter.atTop (nhds X) := by
  simp only [filt_smooth_real_replicate]
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hA).mul_const (r - X)
  have h2 := h.const_add X
  simpa using h2

end conjure_dsp_lib.one_pole

end
