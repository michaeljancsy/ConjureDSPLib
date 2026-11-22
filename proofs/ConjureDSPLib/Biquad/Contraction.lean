module

public import ConjureDSPLib.Biquad.Block
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.Norm

/-!
# Contractions for biquads with poles inside the unit circle

Many audio biquads have a pair of complex poles `r·e^{±iθ}`: for example RBJ low-pass,
high-pass, band-pass, notch and all-pass filters do exactly when `Q > 1/2` (worked out outside
Lean, not proved). In coefficients:
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

## Real poles

When `a1² > 4·a2` the poles are real and distinct: `p, q = (-a1 ± d)/2` with
`d = √(a1² - 4·a2) = p - q` (`poleGap`). For example RBJ low-pass filters with `Q < 1/2` have
such poles (worked out outside Lean, not proved). The coordinates `p·v₁ + v₂` and `q·v₁ + v₂` of
a pair are multiplied by `p` and `q` by the state-update map (`realPoleCoord_update`), so their
sizes added up, `realPoleNorm`, shrink by
`ρ = (|a1| + d)/2 = max(|p|, |q|)` (`max_abs_realPoles`). Both poles are inside the unit circle
exactly when `a2 < 1` and `|a1| < 1 + a2` (`realPoles_lt_one_iff`), and then this gives a
`Contraction` (`realPolesContraction`) with `cInf = 1/d` and `K = 2`. `cInf = 1/(p - q)` grows
without bound as the two poles merge. `realPolesContraction_bounds` and
`realPolesContraction_block_bounds_le` bound the constants from rational numbers on either side
of `d`.

When `a1² = 4·a2` both poles are `p = -a1/2`. The state-update map is then not diagonalisable
(it is similar to a Jordan block), and no measure shrinks every pair by `|p|` itself (both worked
out outside Lean, not proved); `repeatedPoleContraction` uses `ε·|v₁| + |p·v₁ + v₂|` for a
chosen `ε > 0`, with `ρ = |p| + ε`, `cInf = 1 + 1/ε` and `K = 1`, when `|p| + ε < 1`.

When 1 is a pole (`1 + a1 + a2 = 0`) the state-update map leaves the pair `(1, -a2)` unchanged
(`update_one_neg_a2_of_pole_one`), so no `Contraction` exists (`isEmpty_contraction_of_pole_one`).
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

/-! ## Distinct real poles -/

/-- `d = √(a1² - 4·a2)`, the distance between the two poles when they are real (0 when they are
complex). -/
noncomputable def poleGap (c : CoeffsReal) : ℝ := Real.sqrt (c.a1 ^ 2 - 4 * c.a2)

/-- The measure for real poles `p = (-a1 + d)/2` and `q = (-a1 - d)/2` (`d = poleGap c`):
`|p·v₁ + v₂| + |q·v₁ + v₂|`, the sizes of the pair's two coordinates along the poles. -/
noncomputable def realPoleNorm (c : CoeffsReal) (v₁ v₂ : ℝ) : ℝ :=
  |(-c.a1 + poleGap c) / 2 * v₁ + v₂| + |(-c.a1 - poleGap c) / 2 * v₁ + v₂|

/-- The zero pair measures zero. -/
theorem realPoleNorm_zero (c : CoeffsReal) : realPoleNorm c 0 0 = 0 := by
  simp [realPoleNorm]

/-- With real poles, `d² = a1² - 4·a2`. -/
theorem poleGap_sq (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2) :
    poleGap c ^ 2 = c.a1 ^ 2 - 4 * c.a2 :=
  Real.sq_sqrt (by linarith)

/-- With distinct real poles, `d > 0`. -/
theorem poleGap_pos (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2) : 0 < poleGap c :=
  Real.sqrt_pos.mpr (by linarith)

/-- Both poles `(-a1 ± d)/2` are at most `(|a1| + d)/2` in size. -/
theorem abs_realPoles_le (c : CoeffsReal) :
    |(-c.a1 + poleGap c) / 2| ≤ (|c.a1| + poleGap c) / 2 ∧
      |(-c.a1 - poleGap c) / 2| ≤ (|c.a1| + poleGap c) / 2 := by
  have hd : 0 ≤ poleGap c := Real.sqrt_nonneg _
  have h1 := le_abs_self c.a1
  have h2 := neg_abs_le c.a1
  exact ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- `(|a1| + d)/2` is the larger of the poles' sizes `|(-a1 + d)/2|` and `|(-a1 - d)/2|`. -/
theorem max_abs_realPoles (c : CoeffsReal) :
    max |(-c.a1 + poleGap c) / 2| |(-c.a1 - poleGap c) / 2| = (|c.a1| + poleGap c) / 2 := by
  have hd : 0 ≤ poleGap c := Real.sqrt_nonneg _
  obtain ⟨hp, hq⟩ := abs_realPoles_le c
  rcases le_total 0 c.a1 with ha | ha
  · have hq' : |(-c.a1 - poleGap c) / 2| = (|c.a1| + poleGap c) / 2 := by
      rw [abs_of_nonpos (by linarith), abs_of_nonneg ha]; ring
    rw [hq', max_eq_right hp]
  · have hp' : |(-c.a1 + poleGap c) / 2| = (|c.a1| + poleGap c) / 2 := by
      rw [abs_of_nonneg (by linarith), abs_of_nonpos ha]
    rw [hp', max_eq_left hq]

/-- **Both real poles are inside the unit circle exactly when the coefficients are in the
stability triangle.** With distinct real poles (`a1² > 4·a2`), the larger pole size
`(|a1| + d)/2` is below 1 if and only if `a2 < 1` and `|a1| < 1 + a2`. -/
theorem realPoles_lt_one_iff (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2) :
    (|c.a1| + poleGap c) / 2 < 1 ↔ c.a2 < 1 ∧ |c.a1| < 1 + c.a2 := by
  have hd := poleGap_sq c h
  have hd0 := poleGap_pos c h
  have ha := sq_abs c.a1
  have ha0 := abs_nonneg c.a1
  constructor
  · intro hρ
    refine ⟨?_, ?_⟩
    · nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    have h3 : poleGap c < 2 - |c.a1| := by
      rw [poleGap, Real.sqrt_lt' (by linarith)]
      nlinarith
    linarith

/-- **The state-update map multiplies each coordinate by its pole**, when `a1² > 4·a2`: with
`p = (-a1 + d)/2`, `q = (-a1 - d)/2` and the new pair `(-a1·v₁ + v₂, -a2·v₁)`, its coordinate
`p·(-a1·v₁ + v₂) + (-a2·v₁)` is `p·(p·v₁ + v₂)`, and the same with `q`. -/
theorem realPoleCoord_update (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2) (v₁ v₂ : ℝ) :
    (-c.a1 + poleGap c) / 2 * (-c.a1 * v₁ + v₂) + -c.a2 * v₁ =
        (-c.a1 + poleGap c) / 2 * ((-c.a1 + poleGap c) / 2 * v₁ + v₂) ∧
      (-c.a1 - poleGap c) / 2 * (-c.a1 * v₁ + v₂) + -c.a2 * v₁ =
        (-c.a1 - poleGap c) / 2 * ((-c.a1 - poleGap c) / 2 * v₁ + v₂) := by
  have hd := poleGap_sq c h
  exact ⟨by linear_combination (-v₁ / 4) * hd, by linear_combination (-v₁ / 4) * hd⟩

/-- **The measure of the new pair**, when `a1² > 4·a2`: `|p|·|p·v₁ + v₂| + |q|·|q·v₁ + v₂|`
(from `realPoleCoord_update`). -/
theorem realPoleNorm_update (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2) (v₁ v₂ : ℝ) :
    realPoleNorm c (-c.a1 * v₁ + v₂) (-c.a2 * v₁) =
      |(-c.a1 + poleGap c) / 2| * |(-c.a1 + poleGap c) / 2 * v₁ + v₂| +
        |(-c.a1 - poleGap c) / 2| * |(-c.a1 - poleGap c) / 2 * v₁ + v₂| := by
  obtain ⟨e1, e2⟩ := realPoleCoord_update c h v₁ v₂
  rw [realPoleNorm, e1, e2, abs_mul, abs_mul]

/-- **A `Contraction` for biquads with distinct real poles inside the unit circle**
(`a1² > 4·a2`, `a2 < 1` and `|a1| < 1 + a2`; by `realPoles_lt_one_iff` the last two say that
both poles `p, q = (-a1 ± d)/2` are less than 1 in size): the measure `realPoleNorm`, with
`ρ = (|a1| + d)/2 = max(|p|, |q|)` (`max_abs_realPoles`), `cInf = 1/d` and `K = 2`, where
`d = √(a1² - 4·a2) = p - q`. The state-update map multiplies `p·v₁ + v₂` by `p` and `q·v₁ + v₂`
by `q` (`realPoleCoord_update`). -/
noncomputable def realPolesContraction (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2)
    (h1 : c.a2 < 1) (h2 : |c.a1| < 1 + c.a2) : Contraction c where
  N := realPoleNorm c
  ρ := (|c.a1| + poleGap c) / 2
  cInf := 1 / poleGap c
  K := 2
  nonneg _ _ := by unfold realPoleNorm; positivity
  add_le u₁ u₂ v₁ v₂ := by
    unfold realPoleNorm
    have e1 : (-c.a1 + poleGap c) / 2 * (u₁ + v₁) + (u₂ + v₂) =
        ((-c.a1 + poleGap c) / 2 * u₁ + u₂) + ((-c.a1 + poleGap c) / 2 * v₁ + v₂) := by ring
    have e2 : (-c.a1 - poleGap c) / 2 * (u₁ + v₁) + (u₂ + v₂) =
        ((-c.a1 - poleGap c) / 2 * u₁ + u₂) + ((-c.a1 - poleGap c) / 2 * v₁ + v₂) := by ring
    rw [e1, e2]
    linarith [abs_add_le ((-c.a1 + poleGap c) / 2 * u₁ + u₂) ((-c.a1 + poleGap c) / 2 * v₁ + v₂),
      abs_add_le ((-c.a1 - poleGap c) / 2 * u₁ + u₂) ((-c.a1 - poleGap c) / 2 * v₁ + v₂)]
  contract v₁ v₂ := by
    rw [realPoleNorm_update c h]
    obtain ⟨hp, hq⟩ := abs_realPoles_le c
    unfold realPoleNorm
    have h3 := mul_le_mul_of_nonneg_right hp (abs_nonneg ((-c.a1 + poleGap c) / 2 * v₁ + v₂))
    have h4 := mul_le_mul_of_nonneg_right hq (abs_nonneg ((-c.a1 - poleGap c) / 2 * v₁ + v₂))
    linarith
  ρ_nonneg := by have := poleGap_pos c h; positivity
  ρ_lt_one := (realPoles_lt_one_iff c h).mpr ⟨h1, h2⟩
  cInf_nonneg := by have := poleGap_pos c h; positivity
  K_nonneg := by norm_num
  le_fst v₁ v₂ := by
    have hd := poleGap_pos c h
    unfold realPoleNorm
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hd]
    have e : |v₁| * poleGap c = |((-c.a1 + poleGap c) / 2 * v₁ + v₂) -
        ((-c.a1 - poleGap c) / 2 * v₁ + v₂)| := by
      rw [← abs_of_pos hd, ← abs_mul, abs_of_pos hd]; congr 1; ring
    rw [e]
    exact abs_sub _ _
  le_snd v₁ v₂ := by
    have hd := poleGap_pos c h
    have hρ := (realPoles_lt_one_iff c h).mpr ⟨h1, h2⟩
    obtain ⟨hp, hq⟩ := abs_realPoles_le c
    unfold realPoleNorm
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hd]
    set wp := (-c.a1 + poleGap c) / 2 * v₁ + v₂
    set wq := (-c.a1 - poleGap c) / 2 * v₁ + v₂
    have e : |v₂| * poleGap c =
        |(-c.a1 + poleGap c) / 2 * wq - (-c.a1 - poleGap c) / 2 * wp| := by
      rw [← abs_of_pos hd, ← abs_mul, abs_of_pos hd]; congr 1; simp only [wp, wq]; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h3 := mul_le_mul_of_nonneg_right hp (abs_nonneg wq)
    have h4 := mul_le_mul_of_nonneg_right hq (abs_nonneg wp)
    have h5 : (|c.a1| + poleGap c) / 2 * (|wp| + |wq|) ≤ |wp| + |wq| := by
      have := add_nonneg (abs_nonneg wp) (abs_nonneg wq)
      nlinarith
    nlinarith
  le_sum v₁ v₂ := by
    have hρ := (realPoles_lt_one_iff c h).mpr ⟨h1, h2⟩
    obtain ⟨hp, hq⟩ := abs_realPoles_le c
    unfold realPoleNorm
    have h3 : |(-c.a1 + poleGap c) / 2 * v₁ + v₂| ≤ |v₁| + |v₂| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      nlinarith [abs_nonneg v₁]
    have h4 : |(-c.a1 - poleGap c) / 2 * v₁ + v₂| ≤ |v₁| + |v₂| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul]
      nlinarith [abs_nonneg v₁]
    linarith

/-- For `realPolesContraction`, `cInf·K·κ > 0` (`κ = roundGain c`): `cInf = 1/d > 0`, `K = 2` and
`κ ≥ 2`. -/
theorem realPolesContraction_cInf_K_roundGain_pos (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2)
    (h1 : c.a2 < 1) (h2 : |c.a1| < 1 + c.a2) :
    0 < (realPolesContraction c h h1 h2).cInf * (realPolesContraction c h h1 h2).K *
      roundGain c := by
  have hd := poleGap_pos c h
  show 0 < 1 / poleGap c * 2 * roundGain c
  unfold roundGain
  positivity

/-- **`cInf`, `K` and `ρ` of `realPolesContraction`, between rational numbers.** `d` is a square
root; numbers whose squares are on either side of `d² = a1² - 4·a2` bound it: if `0 < dl`,
`0 ≤ du` and `dl² ≤ a1² - 4·a2 ≤ du²`, then `1/du ≤ cInf ≤ 1/dl`, `K = 2` and
`(|a1| + dl)/2 ≤ ρ ≤ (|a1| + du)/2`. -/
theorem realPolesContraction_bounds (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2) (h1 : c.a2 < 1)
    (h2 : |c.a1| < 1 + c.a2) {dl du : ℝ} (hdl : 0 < dl) (hdu : 0 ≤ du)
    (hdl2 : dl ^ 2 ≤ c.a1 ^ 2 - 4 * c.a2) (hdu2 : c.a1 ^ 2 - 4 * c.a2 ≤ du ^ 2) :
    1 / du ≤ (realPolesContraction c h h1 h2).cInf ∧
      (realPolesContraction c h h1 h2).cInf ≤ 1 / dl ∧
      (realPolesContraction c h h1 h2).K = 2 ∧
      (|c.a1| + dl) / 2 ≤ (realPolesContraction c h h1 h2).ρ ∧
      (realPolesContraction c h h1 h2).ρ ≤ (|c.a1| + du) / 2 := by
  have hd0 := poleGap_pos c h
  have hdl' : dl ≤ poleGap c := (le_abs_self dl).trans (Real.abs_le_sqrt hdl2)
  have hdu' : poleGap c ≤ du := by
    have := Real.sqrt_le_sqrt hdu2
    rwa [Real.sqrt_sq hdu] at this
  refine ⟨?_, ?_, rfl, ?_, ?_⟩
  · exact one_div_le_one_div_of_le hd0 hdu'
  · exact one_div_le_one_div_of_le hdl hdl'
  · show (|c.a1| + dl) / 2 ≤ (|c.a1| + poleGap c) / 2
    linarith
  · show (|c.a1| + poleGap c) / 2 ≤ (|c.a1| + du) / 2
    linarith

/-- **The whole-block bounds with `realPolesContraction`, from rational numbers.**
`block_bounds_le` with `ci = 1/dl`, `k = 2` and `ρu = (|a1| + du)/2` from
`realPolesContraction_bounds`: if `0 ≤ M`, `0 ≤ α`, `0 ≤ β`, the start `s` measures at most
`n₀`, `0 < dl`, `0 ≤ du`, `dl² ≤ a1² - 4·a2 ≤ du²` and `ci·k·κ·β < 1 − ρu`
(`κ = roundGain c`), then the conclusions of `block_bounds_le` hold for `realPolesContraction`,
with `Sb' = stateBoundAt c M α β n₀ ci k ρu`. -/
theorem realPolesContraction_block_bounds_le (c : CoeffsReal) (h : 4 * c.a2 < c.a1 ^ 2)
    (h1 : c.a2 < 1) (h2 : |c.a1| < 1 + c.a2) (M α β η n₀ dl du : ℝ) (s : ℝ × ℝ) (hM0 : 0 ≤ M)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : realPoleNorm c s.1 s.2 ≤ n₀) (hdl : 0 < dl) (hdu : 0 ≤ du)
    (hdl2 : dl ^ 2 ≤ c.a1 ^ 2 - 4 * c.a2) (hdu2 : c.a1 ^ 2 - 4 * c.a2 ≤ du ^ 2)
    (hsm : 1 / dl * 2 * roundGain c * β < 1 - (|c.a1| + du) / 2) :
    let C := realPolesContraction c h h1 h2
    let ci := 1 / dl
    let ρu := (|c.a1| + du) / 2
    C.cInf * C.K * roundGain c * β < 1 - C.ρ ∧
      computedStateBound c C M α β s ≤ stateBoundAt c M α β n₀ ci 2 ρu ∧
      localErrBound c C M α β s ≤ α + β * stateBoundAt c M α β n₀ ci 2 ρu ∧
      α ≤ C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s ∧
      C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s ≤
        outErrBoundAt c M α β n₀ ci 2 ρu ∧
      stepValueBound c η M (computedStateBound c C M α β s) ≤
        stepValueBound c η M (stateBoundAt c M α β n₀ ci 2 ρu) := by
  intro C ci ρu
  obtain ⟨-, hci, hk, -, hρ⟩ := realPolesContraction_bounds c h h1 h2 hdl hdu hdl2 hdu2
  exact block_bounds_le c C M α β η n₀ ci 2 ρu s hM0 hα hβ hs hci hk.le hρ hsm

/-! ## A repeated real pole -/

/-- The measure for a repeated pole `p = -a1/2`, with a chosen weight `ε`:
`ε·|v₁| + |p·v₁ + v₂|`. -/
noncomputable def repeatedPoleNorm (c : CoeffsReal) (ε v₁ v₂ : ℝ) : ℝ :=
  ε * |v₁| + |-c.a1 / 2 * v₁ + v₂|

/-- `(1 + 1/ε)` times the measure, expanded: `ε·|v₁| + |p·v₁ + v₂| + |v₁| + |p·v₁ + v₂|/ε`. -/
theorem one_add_inv_mul_repeatedPoleNorm (c : CoeffsReal) {ε : ℝ} (hε : 0 < ε) (v₁ v₂ : ℝ) :
    (1 + 1 / ε) * repeatedPoleNorm c ε v₁ v₂ =
      ε * |v₁| + |-c.a1 / 2 * v₁ + v₂| + |v₁| + |-c.a1 / 2 * v₁ + v₂| / ε := by
  unfold repeatedPoleNorm
  field_simp
  ring

/-- **A `Contraction` for biquads with a repeated real pole inside the unit circle**
(`a1² = 4·a2`, so both poles are `p = -a1/2`), for any `ε > 0` with `|a1|/2 + ε < 1`: the
measure `repeatedPoleNorm c ε`, with `ρ = |p| + ε`, `cInf = 1 + 1/ε` and `K = 1`. The
state-update map is not diagonalisable here (it is similar to a Jordan block), and no measure
shrinks every pair by `|p|` itself (both worked out outside Lean, not proved); a smaller `ε`
gives a `ρ` closer to `|p|` but a larger `cInf`. -/
noncomputable def repeatedPoleContraction (c : CoeffsReal) (h : c.a1 ^ 2 = 4 * c.a2) {ε : ℝ}
    (hε : 0 < ε) (h1 : |c.a1| / 2 + ε < 1) : Contraction c where
  N := repeatedPoleNorm c ε
  ρ := |c.a1| / 2 + ε
  cInf := 1 + 1 / ε
  K := 1
  nonneg _ _ := by unfold repeatedPoleNorm; positivity
  add_le u₁ u₂ v₁ v₂ := by
    unfold repeatedPoleNorm
    have e : -c.a1 / 2 * (u₁ + v₁) + (u₂ + v₂) =
        (-c.a1 / 2 * u₁ + u₂) + (-c.a1 / 2 * v₁ + v₂) := by ring
    rw [e]
    have := abs_add_le (-c.a1 / 2 * u₁ + u₂) (-c.a1 / 2 * v₁ + v₂)
    have := abs_add_le u₁ v₁
    nlinarith
  contract v₁ v₂ := by
    unfold repeatedPoleNorm
    have hp : |-c.a1 / 2| = |c.a1| / 2 := by rw [abs_div, abs_neg, abs_two]
    set w := -c.a1 / 2 * v₁ + v₂
    have e1 : -c.a1 * v₁ + v₂ = -c.a1 / 2 * v₁ + w := by simp only [w]; ring
    have e2 : -c.a1 / 2 * (-c.a1 * v₁ + v₂) + -c.a2 * v₁ = -c.a1 / 2 * w := by
      simp only [w]; linear_combination (v₁ / 4) * h
    rw [e2, e1, abs_mul, hp]
    have h3 : |-c.a1 / 2 * v₁ + w| ≤ |c.a1| / 2 * |v₁| + |w| := by
      refine (abs_add_le _ _).trans ?_; rw [abs_mul, hp]
    have h4 := mul_le_mul_of_nonneg_left h3 hε.le
    have := mul_nonneg (mul_nonneg hε.le hε.le) (abs_nonneg v₁)
    have := abs_nonneg w
    have := abs_nonneg c.a1
    nlinarith
  ρ_nonneg := by positivity
  ρ_lt_one := h1
  cInf_nonneg := by positivity
  K_nonneg := by norm_num
  le_fst v₁ v₂ := by
    show |v₁| ≤ (1 + 1 / ε) * repeatedPoleNorm c ε v₁ v₂
    rw [one_add_inv_mul_repeatedPoleNorm c hε]
    have : 0 ≤ |-c.a1 / 2 * v₁ + v₂| / ε := by positivity
    have := abs_nonneg v₁
    have := abs_nonneg (-c.a1 / 2 * v₁ + v₂)
    nlinarith
  le_snd v₁ v₂ := by
    show |v₂| ≤ (1 + 1 / ε) * repeatedPoleNorm c ε v₁ v₂
    rw [one_add_inv_mul_repeatedPoleNorm c hε]
    have h3 : |v₂| ≤ |-c.a1 / 2 * v₁ + v₂| + |c.a1| / 2 * |v₁| := by
      calc |v₂| = |(-c.a1 / 2 * v₁ + v₂) - (-c.a1 / 2 * v₁)| := by ring_nf
        _ ≤ |-c.a1 / 2 * v₁ + v₂| + |-c.a1 / 2 * v₁| := abs_sub _ _
        _ = |-c.a1 / 2 * v₁ + v₂| + |c.a1| / 2 * |v₁| := by
          rw [abs_mul, abs_div, abs_neg, abs_two]
    have : 0 ≤ |-c.a1 / 2 * v₁ + v₂| / ε := by positivity
    have := abs_nonneg v₁
    have h4 : |c.a1| / 2 * |v₁| ≤ |v₁| := by nlinarith
    nlinarith
  le_sum v₁ v₂ := by
    unfold repeatedPoleNorm
    have h3 : |-c.a1 / 2 * v₁ + v₂| ≤ |c.a1| / 2 * |v₁| + |v₂| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_div, abs_neg, abs_two]
    have := abs_nonneg v₁
    nlinarith

/-! ## A pole at 1 -/

/-- **When 1 is a pole, the state-update map leaves `(1, -a2)` unchanged**: if
`1 + a1 + a2 = 0`, then `-a1·1 + (-a2) = 1` and `-a2·1 = -a2`. -/
theorem update_one_neg_a2_of_pole_one (c : CoeffsReal) (h : 1 + c.a1 + c.a2 = 0) :
    -c.a1 * 1 + -c.a2 = 1 ∧ -c.a2 * 1 = -c.a2 :=
  ⟨by linarith, mul_one _⟩

/-- **No `Contraction` exists when 1 is a pole** (`1 + a1 + a2 = 0`): the state-update map then
leaves the pair `(1, -a2)` unchanged (`update_one_neg_a2_of_pole_one`), so no measure can shrink
it. -/
theorem isEmpty_contraction_of_pole_one (c : CoeffsReal) (h : 1 + c.a1 + c.a2 = 0) :
    IsEmpty (Contraction c) := by
  refine ⟨fun C => ?_⟩
  have hc := C.contract 1 (-c.a2)
  obtain ⟨e1, e2⟩ := update_one_neg_a2_of_pole_one c h
  rw [e1, e2] at hc
  have hN := C.nonneg 1 (-c.a2)
  have hρ := C.ρ_lt_one
  have h0 : C.N 1 (-c.a2) = 0 := by nlinarith
  have := C.le_fst 1 (-c.a2)
  rw [h0, mul_zero, abs_one] at this
  linarith

end conjure_dsp_lib.biquad

end
