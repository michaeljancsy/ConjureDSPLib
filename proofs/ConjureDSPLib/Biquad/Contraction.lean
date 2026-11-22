module

public import ConjureDSPLib.Biquad.Block
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Norm

/-!
# A contraction for biquads with complex poles

Many audio biquads have a pair of complex poles `r·e^{±iθ}`: for example RBJ low-pass,
high-pass, band-pass, notch and all-pass filters do exactly when `Q > 1/2`. In coefficients:
`a1² < 4·a2`. With `ω = √(a2 - a1²/4) = r·sin θ`, measure a pair `(v₁, v₂)` by the length of

`(ω·v₁, v₂ - (a1/2)·v₁)`

(the norm of the complex number `ω·v₁ + (v₂ - (a1/2)·v₁)·i`). In these coordinates the biquad's
state-update map is a rotation scaled by `√a2 = r`, so it multiplies the measure of every pair by
exactly `√a2`, the pole radius (`complexPoleNorm_update`). When `a2 < 1` (both poles inside the
unit circle) this gives a `Contraction` with `ρ = √a2` (`complexPolesContraction`).

The price is `cInf = (1 + |a1|/2)/ω + 1`: when the poles are close to the real axis (small `ω`,
as in a low-pass filter with a low cutoff), small errors in the measure can mean large errors in
the state values. Much of this is real: the filter's own worst-case error gain also grows steeply
as `ω` shrinks (about 1.3 × 10⁴ for a 100 Hz Butterworth low-pass at 48 kHz, worked out by hand,
not proved); the proof's factor `cInf·K/(1 − ρ)` is within about 4× of it at 100 Hz, 1 kHz and
10 kHz.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- `ω = √(a2 - a1²/4)`, the imaginary part of the poles (0 when the poles are real). -/
noncomputable def poleIm (c : CoeffsReal) : ℝ := Real.sqrt (c.a2 - c.a1 ^ 2 / 4)

/-- The measure: the length of `(ω·v₁, v₂ - (a1/2)·v₁)`, as the norm of a complex number. -/
noncomputable def complexPoleNorm (c : CoeffsReal) (v₁ v₂ : ℝ) : ℝ :=
  ‖(⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ : ℂ)‖

/-- With complex poles, `ω² = a2 - a1²/4`. -/
theorem poleIm_sq (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2) :
    poleIm c ^ 2 = c.a2 - c.a1 ^ 2 / 4 :=
  Real.sq_sqrt (by linarith)

/-- With complex poles, `ω > 0`. -/
theorem poleIm_pos (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2) : 0 < poleIm c :=
  Real.sqrt_pos.mpr (by linarith)

/-- **The state-update map multiplies the measure by exactly `√a2`**, the pole radius, when
`a1² < 4·a2`. -/
theorem complexPoleNorm_update (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2) (v₁ v₂ : ℝ) :
    complexPoleNorm c (-c.a1 * v₁ + v₂) (-c.a2 * v₁) =
      Real.sqrt c.a2 * complexPoleNorm c v₁ v₂ := by
  have hω := poleIm_sq c h
  have ha2 : 0 ≤ c.a2 := by nlinarith [sq_nonneg c.a1]
  simp only [complexPoleNorm, Complex.norm_def, Complex.normSq_mk]
  rw [← Real.sqrt_mul ha2]
  congr 1
  linear_combination ((v₂ - c.a1 * v₁) ^ 2 - c.a2 * v₁ ^ 2) * hω

/-- **A `Contraction` for biquads with complex poles inside the unit circle**
(`a1² < 4·a2` and `a2 < 1`): the measure `complexPoleNorm`, with `ρ = √a2`,
`cInf = (1 + |a1|/2)/ω + 1` and `K = ω + |a1|/2 + 1`, where `ω = √(a2 - a1²/4)`. -/
noncomputable def complexPolesContraction (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2)
    (h1 : c.a2 < 1) : Contraction c where
  N := complexPoleNorm c
  ρ := Real.sqrt c.a2
  cInf := (1 + |c.a1| / 2) / poleIm c + 1
  K := poleIm c + |c.a1| / 2 + 1
  nonneg _ _ := norm_nonneg _
  add_le u₁ u₂ v₁ v₂ := by
    unfold complexPoleNorm
    have e : (⟨poleIm c * (u₁ + v₁), u₂ + v₂ - c.a1 / 2 * (u₁ + v₁)⟩ : ℂ) =
        ⟨poleIm c * u₁, u₂ - c.a1 / 2 * u₁⟩ + ⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ := by
      apply Complex.ext <;> simp <;> ring
    rw [e]
    exact norm_add_le _ _
  contract v₁ v₂ := le_of_eq (complexPoleNorm_update c h v₁ v₂)
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
    have h0 := Complex.abs_re_le_norm (⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ : ℂ)
    rw [abs_mul, abs_of_pos hω] at h0
    unfold complexPoleNorm
    set N := ‖(⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ : ℂ)‖
    have hN : 0 ≤ N := norm_nonneg _
    have hv : |v₁| ≤ N / poleIm c := by rw [le_div_iff₀ hω]; linarith
    have : N / poleIm c ≤ ((1 + |c.a1| / 2) / poleIm c + 1) * N := by
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      have : N / poleIm c ≤ (1 + |c.a1| / 2) * N / poleIm c :=
        div_le_div_of_nonneg_right (by nlinarith [abs_nonneg c.a1]) hω.le
      linarith
    linarith
  le_snd v₁ v₂ := by
    have hω := poleIm_pos c h
    have h0 := Complex.abs_re_le_norm (⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ : ℂ)
    have h0' := Complex.abs_im_le_norm (⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ : ℂ)
    rw [abs_mul, abs_of_pos hω] at h0
    unfold complexPoleNorm
    set N := ‖(⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ : ℂ)‖
    have hN : 0 ≤ N := norm_nonneg _
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
    unfold complexPoleNorm
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h2 : |v₂ - c.a1 / 2 * v₁| ≤ |v₂| + |c.a1| / 2 * |v₁| := by
      calc |v₂ - c.a1 / 2 * v₁| ≤ |v₂| + |c.a1 / 2 * v₁| := abs_sub _ _
        _ = |v₂| + |c.a1| / 2 * |v₁| := by rw [abs_mul, abs_div, abs_two]
    simp only
    rw [abs_mul, abs_of_pos hω]
    nlinarith [abs_nonneg v₁, abs_nonneg v₂, abs_nonneg c.a1]

end conjure_dsp_lib.biquad

end
