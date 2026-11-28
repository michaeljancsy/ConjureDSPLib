module

public import ConjureDSPLib.Delay.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# The interpolated delay read: index facts shared by both precisions

`tap_index_spec` and `wrap_index_spec` describe the index arithmetic of `read_interp_f64` and
`read_interp_f32`: the index of the sample `k` samples back from the write index, and moving an
index on by one with wrap-around. Neither mentions a float. `lagrange4_real_abs_le` is about the
interpolation formula in exact arithmetic.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.delay

/-- The index of the sample `k` samples back from the write index `w`, as the code computes
it, is `(p + L - k) mod L`. -/
theorem tap_index_spec (len w k : Std.Usize) (L p : ℕ) (hlen : len.val = L) (hL : 0 < L)
    (hw : w.val = p % L) (hk : k.val ≤ L - 1) :
    (if k ≤ w then w - k else do let i ← len - k; w + i) ⦃ r =>
      r.val = (p + L - k.val) % L ∧ r.val < L ⦄ := by
  have he := read_index_eq L p k.val k.val w.val hL (by omega) hw
  have hwL : w.val < L := by rw [hw]; exact Nat.mod_lt _ hL
  have hmin : min k.val (L - 1) = k.val := by omega
  rw [hmin] at he
  split
  · rename_i h
    have h' : k.val ≤ w.val := by scalar_tac
    step*
  · rename_i h
    have h' : ¬ k.val ≤ w.val := by scalar_tac
    step*

/-- Moving an index on by one, back to 0 at `L`: from `(q mod L)` to `((q + 1) mod L)`. -/
theorem wrap_index_spec (len i : Std.Usize) (L q : ℕ) (hlen : len.val = L) (hL : 0 < L)
    (hi : i.val = q % L + 1) :
    (if i = len then ok 0#usize else ok i) ⦃ r => r.val = (q + 1) % L ∧ r.val < L ⦄ := by
  have hs := succ_mod_eq q L hL
  have hq := Nat.mod_lt q hL
  split
  · rename_i h
    have h' : q % L + 1 = L := by rw [← hi, h, hlen]
    simp only [WP.spec_ok, h', ite_true] at hs ⊢
    exact ⟨by rw [hs]; rfl, by simp; omega⟩
  · rename_i h
    have h' : q % L + 1 ≠ L := fun e => h (UScalar.eq_of_val_eq (by rw [hi, hlen, e]))
    simp only [WP.spec_ok, h', ite_false] at hs ⊢
    exact ⟨by rw [hs, hi], by omega⟩

/-- The four-point Lagrange formula of `read_interp_f64` / `read_interp_f32` in exact
arithmetic: the same weights and sums as the code, on real numbers. -/
noncomputable def lagrange4_real (t xm1 x0 x1 x2 : ℝ) : ℝ :=
  -(t * (t - 1) * (t - 2)) / 6 * xm1 + (t + 1) * (t - 1) * (t - 2) * (1 / 2) * x0 +
    -((t + 1) * t * (t - 2)) * (1 / 2) * x1 + (t + 1) * t * (t - 1) / 6 * x2

/-- **Size of the interpolated value, in exact arithmetic.** For `0 ≤ t ≤ 1` and four samples at
most `M` in size, the exact formula is at most `(1 + t - t²)·M ≤ (5/4)·M` in size: the sizes of
the four weights add up to `1 + t - t²`. -/
theorem lagrange4_real_abs_le (t xm1 x0 x1 x2 M : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hm1 : |xm1| ≤ M) (hx0 : |x0| ≤ M) (hx1 : |x1| ≤ M) (hx2 : |x2| ≤ M) :
    |lagrange4_real t xm1 x0 x1 x2| ≤ (1 + t - t ^ 2) * M ∧ (1 + t - t ^ 2) * M ≤ 5 / 4 * M := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hm1
  have h1t : 0 ≤ 1 - t := by linarith
  have h2t : 0 ≤ 2 - t := by linarith
  have ht1 : 0 ≤ t + 1 := by linarith
  have a : 0 ≤ t * (1 - t) * (2 - t) / 6 := div_nonneg (mul_nonneg (mul_nonneg h0 h1t) h2t) (by norm_num)
  have b : 0 ≤ (t + 1) * (1 - t) * (2 - t) / 2 :=
    div_nonneg (mul_nonneg (mul_nonneg ht1 h1t) h2t) (by norm_num)
  have c : 0 ≤ (t + 1) * t * (2 - t) / 2 := div_nonneg (mul_nonneg (mul_nonneg ht1 h0) h2t) (by norm_num)
  have d : 0 ≤ (t + 1) * t * (1 - t) / 6 := div_nonneg (mul_nonneg (mul_nonneg ht1 h0) h1t) (by norm_num)
  have e : lagrange4_real t xm1 x0 x1 x2 =
      -(t * (1 - t) * (2 - t) / 6) * xm1 + (t + 1) * (1 - t) * (2 - t) / 2 * x0 +
        (t + 1) * t * (2 - t) / 2 * x1 + -((t + 1) * t * (1 - t) / 6) * x2 := by
    unfold lagrange4_real; ring
  rw [e]
  refine ⟨?_, ?_⟩
  · have k1 := abs_add_le (-(t * (1 - t) * (2 - t) / 6) * xm1 +
        (t + 1) * (1 - t) * (2 - t) / 2 * x0 + (t + 1) * t * (2 - t) / 2 * x1)
      (-((t + 1) * t * (1 - t) / 6) * x2)
    have k2 := abs_add_le (-(t * (1 - t) * (2 - t) / 6) * xm1 +
        (t + 1) * (1 - t) * (2 - t) / 2 * x0) ((t + 1) * t * (2 - t) / 2 * x1)
    have k3 := abs_add_le (-(t * (1 - t) * (2 - t) / 6) * xm1)
        ((t + 1) * (1 - t) * (2 - t) / 2 * x0)
    rw [abs_mul, abs_neg, abs_of_nonneg a] at k3
    rw [abs_mul, abs_of_nonneg b] at k3
    rw [abs_mul, abs_of_nonneg c] at k2
    rw [abs_mul, abs_neg, abs_of_nonneg d] at k1
    have m1 := mul_le_mul_of_nonneg_left hm1 a
    have m0 := mul_le_mul_of_nonneg_left hx0 b
    have m2 := mul_le_mul_of_nonneg_left hx1 c
    have m3 := mul_le_mul_of_nonneg_left hx2 d
    have hs : t * (1 - t) * (2 - t) / 6 * M + (t + 1) * (1 - t) * (2 - t) / 2 * M +
        (t + 1) * t * (2 - t) / 2 * M + (t + 1) * t * (1 - t) / 6 * M = (1 + t - t ^ 2) * M := by
      ring
    linarith
  · have : 1 + t - t ^ 2 ≤ 5 / 4 := by nlinarith [sq_nonneg (t - 1 / 2)]
    exact mul_le_mul_of_nonneg_right this hM

end conjure_dsp_lib.delay

end
