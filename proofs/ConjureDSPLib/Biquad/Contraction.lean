module

public import ConjureDSPLib.Biquad.Block
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A contraction for biquads with complex poles

Most audio biquads (low-pass, high-pass, band-pass, peaking, shelving filters with enough
resonance) have a pair of complex poles `r·e^{±iθ}`: in coefficients, `a1² < 4·a2`. With
`ω = √(a2 - a1²/4) = r·sin θ`, measure a pair `(v₁, v₂)` by the length of

`(ω·v₁, v₂ - (a1/2)·v₁)`.

In these coordinates the biquad's state-update map is a rotation scaled by `√a2 = r`, so it
shrinks every pair by exactly the pole radius `r` (`contract_complexPoles`). When `a2 < 1` (both
poles inside the unit circle) this gives a `Contraction` with `ρ = √a2`.

The price is `cInf = (1 + |a1|/2)/ω + 1`: when the poles are close to the real axis (small `ω`,
as in a low-pass filter with a low cutoff), small errors in the measure can mean large errors in
the state values. That is how these filters behave in floating point, not an artifact of the
proof.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- `ω = √(a2 - a1²/4)`, the imaginary part of the poles. -/
noncomputable def poleIm (c : CoeffsReal) : ℝ := Real.sqrt (c.a2 - c.a1 ^ 2 / 4)

/-- The measure: the length of `(ω·v₁, v₂ - (a1/2)·v₁)`. -/
noncomputable def complexNorm (c : CoeffsReal) (v₁ v₂ : ℝ) : ℝ :=
  Real.sqrt ((poleIm c * v₁) ^ 2 + (v₂ - c.a1 / 2 * v₁) ^ 2)

/-- The length of a sum of two pairs is at most the sum of their lengths. -/
theorem sqrt_sum_sq_add_le (a b p q : ℝ) :
    Real.sqrt ((a + p) ^ 2 + (b + q) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (p ^ 2 + q ^ 2) := by
  have hA := Real.sqrt_nonneg (a ^ 2 + b ^ 2)
  have hP := Real.sqrt_nonneg (p ^ 2 + q ^ 2)
  rw [Real.sqrt_le_left (by positivity)]
  have hAA := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ a ^ 2 + b ^ 2)
  have hPP := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p ^ 2 + q ^ 2)
  -- Cauchy–Schwarz in two dimensions: a·p + b·q ≤ √(a² + b²)·√(p² + q²).
  have hcs : a * p + b * q ≤ Real.sqrt (a ^ 2 + b ^ 2) * Real.sqrt (p ^ 2 + q ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    nlinarith [sq_nonneg (a * q - b * p)]
  nlinarith [hcs]

/-- With complex poles, `ω² = a2 - a1²/4`. -/
theorem poleIm_sq (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2) :
    poleIm c ^ 2 = c.a2 - c.a1 ^ 2 / 4 :=
  Real.sq_sqrt (by linarith)

/-- With complex poles, `ω > 0`. -/
theorem poleIm_pos (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2) : 0 < poleIm c :=
  Real.sqrt_pos.mpr (by linarith)

/-- **The state-update map shrinks the measure by exactly `√a2`**, the pole radius. -/
theorem contract_complexPoles (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2) (v₁ v₂ : ℝ) :
    complexNorm c (-c.a1 * v₁ + v₂) (-c.a2 * v₁) = Real.sqrt c.a2 * complexNorm c v₁ v₂ := by
  have hω := poleIm_sq c h
  have ha2 : 0 ≤ c.a2 := by nlinarith [sq_nonneg c.a1]
  unfold complexNorm
  rw [← Real.sqrt_mul ha2]
  congr 1
  linear_combination ((v₂ - c.a1 * v₁) ^ 2 - c.a2 * v₁ ^ 2) * hω

/-- Each coordinate of `(x, y)` is at most its length. -/
theorem abs_le_sqrt_sum_sq_left (x y : ℝ) : |x| ≤ Real.sqrt (x ^ 2 + y ^ 2) :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg y])

theorem abs_le_sqrt_sum_sq_right (x y : ℝ) : |y| ≤ Real.sqrt (x ^ 2 + y ^ 2) :=
  Real.abs_le_sqrt (by nlinarith [sq_nonneg x])

/-- The length of `(x, y)` is at most `|x| + |y|`. -/
theorem sqrt_sum_sq_le_abs_add (x y : ℝ) : Real.sqrt (x ^ 2 + y ^ 2) ≤ |x| + |y| := by
  rw [Real.sqrt_le_left (by positivity)]
  have := abs_nonneg x; have := abs_nonneg y
  nlinarith [sq_abs x, sq_abs y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]

/-- **A `Contraction` for biquads with complex poles inside the unit circle**
(`a1² < 4·a2` and `a2 < 1`): the measure `complexNorm`, with `ρ = √a2`,
`cInf = (1 + |a1|/2)/ω + 1` and `K = ω + |a1|/2 + 1`, where `ω = √(a2 - a1²/4)`. -/
noncomputable def complexContraction (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2)
    (h1 : c.a2 < 1) : Contraction c where
  N := complexNorm c
  ρ := Real.sqrt c.a2
  cInf := (1 + |c.a1| / 2) / poleIm c + 1
  K := poleIm c + |c.a1| / 2 + 1
  nonneg _ _ := Real.sqrt_nonneg _
  add_le u₁ u₂ v₁ v₂ := by
    unfold complexNorm
    have e1 : poleIm c * (u₁ + v₁) = poleIm c * u₁ + poleIm c * v₁ := by ring
    have e2 : u₂ + v₂ - c.a1 / 2 * (u₁ + v₁) = (u₂ - c.a1 / 2 * u₁) + (v₂ - c.a1 / 2 * v₁) := by
      ring
    rw [e1, e2]
    exact sqrt_sum_sq_add_le _ _ _ _
  contract v₁ v₂ := le_of_eq (contract_complexPoles c h v₁ v₂)
  ρ_nonneg := Real.sqrt_nonneg _
  ρ_lt_one := by
    rw [Real.sqrt_lt' one_pos]; simpa using h1
  cInf_nonneg := by
    have := poleIm_pos c h
    positivity
  K_nonneg := by
    have := poleIm_pos c h
    positivity
  le_fst v₁ v₂ := by
    have hω := poleIm_pos c h
    have h0 := abs_le_sqrt_sum_sq_left (poleIm c * v₁) (v₂ - c.a1 / 2 * v₁)
    rw [abs_mul, abs_of_pos hω] at h0
    have hN := Real.sqrt_nonneg ((poleIm c * v₁) ^ 2 + (v₂ - c.a1 / 2 * v₁) ^ 2)
    unfold complexNorm
    set N := Real.sqrt ((poleIm c * v₁) ^ 2 + (v₂ - c.a1 / 2 * v₁) ^ 2)
    have hv : |v₁| ≤ N / poleIm c := by rw [le_div_iff₀ hω]; linarith
    have : N / poleIm c ≤ ((1 + |c.a1| / 2) / poleIm c + 1) * N := by
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      have : N / poleIm c ≤ (1 + |c.a1| / 2) * N / poleIm c :=
        div_le_div_of_nonneg_right (by nlinarith [abs_nonneg c.a1]) hω.le
      linarith
    linarith
  le_snd v₁ v₂ := by
    have hω := poleIm_pos c h
    have h0 := abs_le_sqrt_sum_sq_left (poleIm c * v₁) (v₂ - c.a1 / 2 * v₁)
    have h0' := abs_le_sqrt_sum_sq_right (poleIm c * v₁) (v₂ - c.a1 / 2 * v₁)
    rw [abs_mul, abs_of_pos hω] at h0
    unfold complexNorm
    set N := Real.sqrt ((poleIm c * v₁) ^ 2 + (v₂ - c.a1 / 2 * v₁) ^ 2)
    have hN : 0 ≤ N := Real.sqrt_nonneg _
    have hv : |v₁| ≤ N / poleIm c := by rw [le_div_iff₀ hω]; linarith
    have h2 : |v₂| ≤ N + |c.a1| / 2 * |v₁| := by
      calc |v₂| = |(v₂ - c.a1 / 2 * v₁) + c.a1 / 2 * v₁| := by ring_nf
        _ ≤ |v₂ - c.a1 / 2 * v₁| + |c.a1 / 2 * v₁| := abs_add_le _ _
        _ = |v₂ - c.a1 / 2 * v₁| + |c.a1| / 2 * |v₁| := by
          rw [abs_mul, abs_div, abs_two]
        _ ≤ N + |c.a1| / 2 * |v₁| := by linarith
    have h3 : |c.a1| / 2 * |v₁| ≤ |c.a1| / 2 * (N / poleIm c) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    have h4 : |c.a1| / 2 * (N / poleIm c) ≤ (1 + |c.a1| / 2) / poleIm c * N := by
      have e : (1 + |c.a1| / 2) / poleIm c * N - |c.a1| / 2 * (N / poleIm c) = N / poleIm c := by
        field_simp; ring
      have : 0 ≤ N / poleIm c := div_nonneg hN hω.le
      linarith
    nlinarith
  le_sum v₁ v₂ := by
    have hω := poleIm_pos c h
    unfold complexNorm
    refine (sqrt_sum_sq_le_abs_add _ _).trans ?_
    have h2 : |v₂ - c.a1 / 2 * v₁| ≤ |v₂| + |c.a1| / 2 * |v₁| := by
      calc |v₂ - c.a1 / 2 * v₁| ≤ |v₂| + |c.a1 / 2 * v₁| := abs_sub _ _
        _ = |v₂| + |c.a1| / 2 * |v₁| := by rw [abs_mul, abs_div, abs_two]
    rw [abs_mul, abs_of_pos hω]
    nlinarith [abs_nonneg v₁, abs_nonneg v₂, abs_nonneg c.a1]

end conjure_dsp_lib.biquad

end
