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
as `ω` shrinks (about 1.3 × 10⁴ for a 100 Hz Butterworth low-pass at 48 kHz), and the proof's
factor `cInf·K/(1 − ρ)` is within about 4× of it at 100 Hz, 1 kHz and 10 kHz; both figures are
worked out outside Lean, not proved.

`complexPolesContraction_bounds` bounds `cInf`, `K` and `ρ` by rational numbers whose squares are
on either side of `ω²` and `a2`; `complexPolesContraction_block_bounds_le`, `_ge` and
`complexPolesContraction_smallness_fails` combine it with `block_bounds_le`, `block_bounds_ge`
and `smallness_fails`.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- `ω = √(a2 - a1²/4)`, the imaginary part of the poles (0 when the poles are real). -/
noncomputable def poleIm (c : CoeffsReal) : ℝ := Real.sqrt (c.a2 - c.a1 ^ 2 / 4)

/-- The measure: the length of `(ω·v₁, v₂ - (a1/2)·v₁)`, as the norm of a complex number. -/
noncomputable def complexPoleNorm (c : CoeffsReal) (v₁ v₂ : ℝ) : ℝ :=
  ‖(⟨poleIm c * v₁, v₂ - c.a1 / 2 * v₁⟩ : ℂ)‖

/-- The zero pair measures zero. -/
theorem complexPoleNorm_zero (c : CoeffsReal) : complexPoleNorm c 0 0 = 0 := by
  unfold complexPoleNorm
  rw [show (⟨poleIm c * 0, 0 - c.a1 / 2 * 0⟩ : ℂ) = 0 from Complex.ext (by simp) (by simp)]
  exact norm_zero

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

/-- For `complexPolesContraction`, `cInf·K·κ > 0` (`κ = roundGain c`): `cInf ≥ 1`, `K ≥ 1` and
`κ ≥ 2`. -/
theorem complexPolesContraction_cInf_K_roundGain_pos (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2)
    (h1 : c.a2 < 1) :
    0 < (complexPolesContraction c h h1).cInf * (complexPolesContraction c h h1).K *
      roundGain c := by
  have hω := poleIm_pos c h
  show 0 < ((1 + |c.a1| / 2) / poleIm c + 1) * (poleIm c + |c.a1| / 2 + 1) * roundGain c
  unfold roundGain
  positivity

/-- **`cInf`, `K` and `ρ` of `complexPolesContraction`, between rational numbers.** `ω` and
`ρ = √a2` are square roots; numbers whose squares are on either side of `ω² = a2 - a1²/4` and of
`a2` bound them: if `0 < ωl`, `0 ≤ ωu`, `ωl² ≤ a2 - a1²/4 ≤ ωu²`, `0 ≤ ρu` and
`ρl² ≤ a2 ≤ ρu²`, then `(1 + |a1|/2)/ωu + 1 ≤ cInf ≤ (1 + |a1|/2)/ωl + 1`,
`ωl + |a1|/2 + 1 ≤ K ≤ ωu + |a1|/2 + 1` and `ρl ≤ ρ ≤ ρu`. -/
theorem complexPolesContraction_bounds (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2)
    (h1 : c.a2 < 1) {ωl ωu ρl ρu : ℝ} (hωl : 0 < ωl) (hωu : 0 ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ c.a2 - c.a1 ^ 2 / 4) (hωu2 : c.a2 - c.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρu : 0 ≤ ρu) (hρl2 : ρl ^ 2 ≤ c.a2) (hρu2 : c.a2 ≤ ρu ^ 2) :
    (1 + |c.a1| / 2) / ωu + 1 ≤ (complexPolesContraction c h h1).cInf ∧
      (complexPolesContraction c h h1).cInf ≤ (1 + |c.a1| / 2) / ωl + 1 ∧
      ωl + |c.a1| / 2 + 1 ≤ (complexPolesContraction c h h1).K ∧
      (complexPolesContraction c h h1).K ≤ ωu + |c.a1| / 2 + 1 ∧
      ρl ≤ (complexPolesContraction c h h1).ρ ∧ (complexPolesContraction c h h1).ρ ≤ ρu := by
  have hω0 := poleIm_pos c h
  have hωl' : ωl ≤ poleIm c := (le_abs_self ωl).trans (Real.abs_le_sqrt hωl2)
  have hωu' : poleIm c ≤ ωu := by
    have := Real.sqrt_le_sqrt hωu2
    rwa [Real.sqrt_sq hωu] at this
  have hρl' : ρl ≤ Real.sqrt c.a2 := (le_abs_self ρl).trans (Real.abs_le_sqrt hρl2)
  have hρu' : Real.sqrt c.a2 ≤ ρu := by
    have := Real.sqrt_le_sqrt hρu2
    rwa [Real.sqrt_sq hρu] at this
  have ha : 0 ≤ 1 + |c.a1| / 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_, hρl', hρu'⟩
  · show (1 + |c.a1| / 2) / ωu + 1 ≤ (1 + |c.a1| / 2) / poleIm c + 1
    have := div_le_div_of_nonneg_left ha hω0 hωu'
    linarith
  · show (1 + |c.a1| / 2) / poleIm c + 1 ≤ (1 + |c.a1| / 2) / ωl + 1
    have := div_le_div_of_nonneg_left ha hωl hωl'
    linarith
  · show ωl + |c.a1| / 2 + 1 ≤ poleIm c + |c.a1| / 2 + 1
    linarith
  · show poleIm c + |c.a1| / 2 + 1 ≤ ωu + |c.a1| / 2 + 1
    linarith

/-- **The whole-block bounds with `complexPolesContraction`, from rational numbers.**
`block_bounds_le` with `ci = (1 + |a1|/2)/ωl + 1` and `k = ωu + |a1|/2 + 1` from
`complexPolesContraction_bounds`: if `0 ≤ M`, `0 ≤ α`, `0 ≤ β`, the start `s` measures at most
`n₀`, `0 < ωl`, `0 ≤ ωu`, `ωl² ≤ a2 - a1²/4 ≤ ωu²`, `0 ≤ ρu`, `a2 ≤ ρu²` and
`ci·k·κ·β < 1 − ρu` (`κ = roundGain c`), then the conclusions of `block_bounds_le` hold for
`complexPolesContraction`, with `Sb' = stateBoundAt c M α β n₀ ci k ρu`. -/
theorem complexPolesContraction_block_bounds_le (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2)
    (h1 : c.a2 < 1) (M α β η n₀ ωl ωu ρu : ℝ) (s : ℝ × ℝ) (hM0 : 0 ≤ M) (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (hs : complexPoleNorm c s.1 s.2 ≤ n₀) (hωl : 0 < ωl) (hωu : 0 ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ c.a2 - c.a1 ^ 2 / 4) (hωu2 : c.a2 - c.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρu : 0 ≤ ρu) (hρu2 : c.a2 ≤ ρu ^ 2)
    (hsm : ((1 + |c.a1| / 2) / ωl + 1) * (ωu + |c.a1| / 2 + 1) * roundGain c * β < 1 - ρu) :
    let C := complexPolesContraction c h h1
    let ci := (1 + |c.a1| / 2) / ωl + 1
    let k := ωu + |c.a1| / 2 + 1
    C.cInf * C.K * roundGain c * β < 1 - C.ρ ∧
      computedStateBound c C M α β s ≤ stateBoundAt c M α β n₀ ci k ρu ∧
      localErrBound c C M α β s ≤ α + β * stateBoundAt c M α β n₀ ci k ρu ∧
      α ≤ C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s ∧
      C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s ≤
        outErrBoundAt c M α β n₀ ci k ρu ∧
      stepValueBound c η M (computedStateBound c C M α β s) ≤
        stepValueBound c η M (stateBoundAt c M α β n₀ ci k ρu) := by
  intro C ci k
  have ha2 : (0 : ℝ) ^ 2 ≤ c.a2 := by nlinarith [sq_nonneg c.a1]
  obtain ⟨-, hci, -, hk, -, hρ⟩ :=
    complexPolesContraction_bounds c h h1 hωl hωu hωl2 hωu2 hρu ha2 hρu2
  exact block_bounds_le c C M α β η n₀ ci k ρu s hM0 hα hβ hs hci hk hρ hsm

/-- **The whole-block bounds with `complexPolesContraction`, from below.** `block_bounds_ge`
with `ci = (1 + |a1|/2)/ωu + 1` and `k = ωl + |a1|/2 + 1` from
`complexPolesContraction_bounds`: if `0 ≤ M`, `0 ≤ α`, `0 ≤ β`, the condition
`cInf·K·κ·β < 1 − ρ` holds (`κ = roundGain c`), `0 < ωl ≤ ωu`,
`ωl² ≤ a2 - a1²/4 ≤ ωu²` and `ρl² ≤ a2`, then the conclusions of `block_bounds_ge` hold for
`complexPolesContraction`. -/
theorem complexPolesContraction_block_bounds_ge (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2)
    (h1 : c.a2 < 1) (M α β ωl ωu ρl : ℝ) (s : ℝ × ℝ) (hM0 : 0 ≤ M) (hα : 0 ≤ α)
    (hβ : 0 ≤ β)
    (hsmall : (complexPolesContraction c h h1).cInf * (complexPolesContraction c h h1).K *
      roundGain c * β < 1 - (complexPolesContraction c h h1).ρ)
    (hωl : 0 < ωl) (hωu : ωl ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ c.a2 - c.a1 ^ 2 / 4) (hωu2 : c.a2 - c.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρl2 : ρl ^ 2 ≤ c.a2) :
    let C := complexPolesContraction c h h1
    let ci := (1 + |c.a1| / 2) / ωu + 1
    let k := ωl + |c.a1| / 2 + 1
    stateBoundAt c M α β 0 ci k ρl ≤ computedStateBound c C M α β s ∧
      outErrBoundAt c M α β 0 ci k ρl ≤
        C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s := by
  intro C ci k
  have hωu0 : 0 < ωu := hωl.trans_le hωu
  obtain ⟨hci, -, hk, -, hρ, -⟩ := complexPolesContraction_bounds c h h1 hωl hωu0.le hωl2 hωu2
    (Real.sqrt_nonneg c.a2)
    hρl2 (Real.sq_sqrt (by nlinarith [sq_nonneg c.a1])).ge
  exact block_bounds_ge c C M α β ci k ρl s hM0 hα hβ hsmall (by positivity) (by positivity)
    hci hk hρ

/-- **When the condition fails, for `complexPolesContraction`.** `smallness_fails` with
`ci = (1 + |a1|/2)/ωu + 1` and `k = ωl + |a1|/2 + 1`: if `0 < ωl ≤ ωu`,
`ωl² ≤ a2 - a1²/4 ≤ ωu²`, `ρl² ≤ a2`, `0 ≤ β` and `1 − ρl ≤ ci·k·κ·β` (`κ = roundGain c`), then
`cInf·K·κ·β < 1 − ρ` is false for `complexPolesContraction`. -/
theorem complexPolesContraction_smallness_fails (c : CoeffsReal) (h : c.a1 ^ 2 < 4 * c.a2)
    (h1 : c.a2 < 1) (β ωl ωu ρl : ℝ) (hβ : 0 ≤ β) (hωl : 0 < ωl) (hωu : ωl ≤ ωu)
    (hωl2 : ωl ^ 2 ≤ c.a2 - c.a1 ^ 2 / 4) (hωu2 : c.a2 - c.a1 ^ 2 / 4 ≤ ωu ^ 2)
    (hρl2 : ρl ^ 2 ≤ c.a2)
    (hfail : 1 - ρl ≤ ((1 + |c.a1| / 2) / ωu + 1) * (ωl + |c.a1| / 2 + 1) * roundGain c * β) :
    ¬ (complexPolesContraction c h h1).cInf * (complexPolesContraction c h h1).K *
      roundGain c * β < 1 - (complexPolesContraction c h h1).ρ := by
  have hωu0 : 0 < ωu := hωl.trans_le hωu
  obtain ⟨hci, -, hk, -, hρ, -⟩ := complexPolesContraction_bounds c h h1 hωl hωu0.le hωl2 hωu2
    (Real.sqrt_nonneg c.a2) hρl2 (Real.sq_sqrt (by nlinarith [sq_nonneg c.a1])).ge
  exact smallness_fails _ _ β _ _ ρl hβ (by positivity) hci hk hρ hfail

end conjure_dsp_lib.biquad

end
