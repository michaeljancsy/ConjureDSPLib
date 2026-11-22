module

public import ConjureDSPLib.Svf.Block
public import ConjureDSPLib.Biquad.Contraction

/-!
# Contractions for the state-variable filter

## The SVF's state-update map is similar to a biquad's

`svfStep_real_linear` (in `Svf/Block.lean`) writes one SVF step as `s ↦ A·s + b·x`.
`poleBiquad c` is the biquad whose feedback coefficients are `a1 = −(a11 + a22)` and
`a2 = a11·a22 − a12·a21`, the coefficients of `A`'s characteristic polynomial `z² + a1·z + a2`;
its feed-forward coefficients are `0` and play no part here. In terms of `g`, `k` and `d`:
`a1 = 4·g²·d + 2·g·d·k − 2` and `a2 = 1 − 2·g·d·k` (`poleBiquad_a1`, `poleBiquad_a2`), and when
`d·(1 + g·(g + k)) = 1` (as it is in exact arithmetic) `a1 = 2·d·(g² − 1)` and
`a2 = d·(1 − g·k + g²)` (`poleBiquad_a1_of_d`, `poleBiquad_a2_of_d`).

The change of coordinates `P(v₁, v₂) = (v₁, −a22·v₁ + a12·v₂)` (`toBiquadCoords`) turns the SVF's
state-update map into the biquad's, `(w₁, w₂) ↦ (−a1·w₁ + w₂, −a2·w₁)`:
`P(A·v) = T(P·v)` for every pair `v` (`toBiquadCoords_update`, from the Cayley–Hamilton
theorem for 2 × 2 matrices). `P` is invertible when `a12 = −2·g·d ≠ 0`. So any biquad
`Contraction` of `poleBiquad c`, for example `biquad.complexPolesContraction`,
`biquad.realPolesContraction` or `biquad.repeatedPoleContraction`, gives an SVF `Contraction`
with the measure `N(P·v)` (`ofBiquad`). Its constants are crude: in
`cInf' = cInf·(1 + (1 + |a22|)/|a12|)`, the factor `1 + (1 + |a22|)/|a12|` grows like `1/(g·d)`
as `g` shrinks, on top of the biquad's own `cInf` (worked out outside Lean, not proved).

That the SVF and `poleBiquad c` (with suitable feed-forward coefficients) have the same transfer
function is not proved.

## Complex poles, measured directly

`complexPolesContraction` measures a pair `(v₁, v₂)` by the length of
`(p·v₁, v₂ + (k/2)·v₁)`, with `p = √(1/d − g·(g + k) − k²/4)`: the biquad's `complexPoleNorm` for
the coefficients `a1 = −k`, `a2 = 1/d − g·(g + k)` (`normCoeffs`). In these coordinates the SVF's
state-update map is a rotation scaled by `√(1 − 2·g·d·k)`, so it multiplies every pair's measure
by exactly that (`complexPoleNorm_update`). When `d > 0`, `g·k > 0` and `p² > 0` this gives a
`Contraction` with `ρ = √(1 − 2·g·d·k)`, `cInf = (1 + |k|/2)/p + 1` and `K = p + |k|/2 + 1`.
When `d·(1 + g·(g + k)) = 1` exactly, `1/d − g·(g + k) = 1` (`normCoeffs_a2_of_d`), so
`p² = 1 − k²/4`, which does not depend on `g`. For `k = 1/0.7071`, `p` is about `0.707`, `cInf`
about 3.41 and `K` about 2.41 at every cutoff, while for the biquad `cInf` grows like `1/ω` as the
cutoff falls (worked out outside Lean, not proved).
-/

@[expose] public section

namespace conjure_dsp_lib.svf

/-! ## The matching biquad -/

/-- The biquad whose state-update map has the characteristic polynomial of the SVF's:
`a1 = −(a11 + a22)` and `a2 = a11·a22 − a12·a21`. Its feed-forward coefficients are `0`; only `a1`
and `a2` enter a biquad `Contraction`. -/
def poleBiquad (c : CoeffsReal) : biquad.CoeffsReal where
  b0 := 0
  b1 := 0
  b2 := 0
  a1 := -(a11 c + a22 c)
  a2 := a11 c * a22 c - a12 c * a21 c

/-- `a1 = 4·g²·d + 2·g·d·k − 2`. -/
theorem poleBiquad_a1 (c : CoeffsReal) :
    (poleBiquad c).a1 = 4 * c.g ^ 2 * c.d + 2 * c.g * c.d * c.k - 2 := by
  simp only [poleBiquad, a11, a22]; ring

/-- `a2 = 1 − 2·g·d·k`. -/
theorem poleBiquad_a2 (c : CoeffsReal) : (poleBiquad c).a2 = 1 - 2 * c.g * c.d * c.k := by
  simp only [poleBiquad, a11, a12, a21, a22]; ring

/-- When `d·(1 + g·(g + k)) = 1`: `a1 = 2·d·(g² − 1)`. -/
theorem poleBiquad_a1_of_d (c : CoeffsReal) (hd : c.d * (1 + c.g * (c.g + c.k)) = 1) :
    (poleBiquad c).a1 = 2 * c.d * (c.g ^ 2 - 1) := by
  rw [poleBiquad_a1]; linear_combination 2 * hd

/-- When `d·(1 + g·(g + k)) = 1`: `a2 = d·(1 − g·k + g²)`. -/
theorem poleBiquad_a2_of_d (c : CoeffsReal) (hd : c.d * (1 + c.g * (c.g + c.k)) = 1) :
    (poleBiquad c).a2 = c.d * (1 - c.g * c.k + c.g ^ 2) := by
  rw [poleBiquad_a2]; linear_combination (-1) * hd

/-- The change of coordinates `P(v₁, v₂) = (v₁, −a22·v₁ + a12·v₂)`. -/
def toBiquadCoords (c : CoeffsReal) (v : ℝ × ℝ) : ℝ × ℝ := (v.1, -a22 c * v.1 + a12 c * v.2)

/-- **The SVF's state-update map is similar to the biquad's.** For every pair `v`,
`P(A·v) = T(P·v)`, where `A` is the SVF's state-update matrix (`a11` … `a22`),
`T(w₁, w₂) = (−a1·w₁ + w₂, −a2·w₁)` is the state-update map of `poleBiquad c`, and
`P = toBiquadCoords c`. -/
theorem toBiquadCoords_update (c : CoeffsReal) (v : ℝ × ℝ) :
    toBiquadCoords c (a11 c * v.1 + a12 c * v.2, a21 c * v.1 + a22 c * v.2) =
      (-(poleBiquad c).a1 * (toBiquadCoords c v).1 + (toBiquadCoords c v).2,
        -(poleBiquad c).a2 * (toBiquadCoords c v).1) := by
  simp only [toBiquadCoords, poleBiquad, Prod.mk.injEq]
  constructor <;> ring

/-- **Any biquad `Contraction` of `poleBiquad c` gives an SVF `Contraction`**, when
`a12 = −2·g·d ≠ 0`: the measure `N(P·v)` with `P = toBiquadCoords c`, the same `ρ`,
`cInf' = cInf·(1 + (1 + |a22|)/|a12|)` and `K' = K·(1 + |a22| + |a12|)`. -/
noncomputable def ofBiquad (c : CoeffsReal) (C : biquad.Contraction (poleBiquad c))
    (h : a12 c ≠ 0) : Contraction c where
  N v₁ v₂ := C.N v₁ (-a22 c * v₁ + a12 c * v₂)
  ρ := C.ρ
  cInf := C.cInf * (1 + (1 + |a22 c|) / |a12 c|)
  K := C.K * (1 + |a22 c| + |a12 c|)
  nonneg _ _ := C.nonneg _ _
  add_le u₁ u₂ v₁ v₂ := by
    have e : -a22 c * (u₁ + v₁) + a12 c * (u₂ + v₂) =
        (-a22 c * u₁ + a12 c * u₂) + (-a22 c * v₁ + a12 c * v₂) := by ring
    rw [e]
    exact C.add_le _ _ _ _
  contract v₁ v₂ := by
    have h := toBiquadCoords_update c (v₁, v₂)
    simp only [toBiquadCoords, Prod.mk.injEq] at h
    rw [h.2, h.1]
    exact C.contract _ _
  ρ_nonneg := C.ρ_nonneg
  cInf_nonneg := by have := C.cInf_nonneg; positivity
  K_nonneg := by have := C.K_nonneg; positivity
  ρ_lt_one := C.ρ_lt_one
  le_fst v₁ v₂ := by
    have h1 := C.le_fst v₁ (-a22 c * v₁ + a12 c * v₂)
    have hN := C.nonneg v₁ (-a22 c * v₁ + a12 c * v₂)
    have hc := C.cInf_nonneg
    have hX : 0 ≤ (1 + |a22 c|) / |a12 c| := by positivity
    have : 0 ≤ C.cInf * ((1 + |a22 c|) / |a12 c|) * C.N v₁ (-a22 c * v₁ + a12 c * v₂) := by
      positivity
    linarith [show C.cInf * (1 + (1 + |a22 c|) / |a12 c|) * C.N v₁ (-a22 c * v₁ + a12 c * v₂) =
      C.cInf * C.N v₁ (-a22 c * v₁ + a12 c * v₂) +
        C.cInf * ((1 + |a22 c|) / |a12 c|) * C.N v₁ (-a22 c * v₁ + a12 c * v₂) by ring]
  le_snd v₁ v₂ := by
    have ha : 0 < |a12 c| := abs_pos.mpr h
    set N := C.N v₁ (-a22 c * v₁ + a12 c * v₂)
    have hN : 0 ≤ N := C.nonneg _ _
    have hc := C.cInf_nonneg
    have h1 : |v₁| ≤ C.cInf * N := C.le_fst _ _
    have h2 : |-a22 c * v₁ + a12 c * v₂| ≤ C.cInf * N := C.le_snd _ _
    -- `a12·v₂ = (−a22·v₁ + a12·v₂) + a22·v₁`.
    have h3 : |a12 c| * |v₂| ≤ C.cInf * N + |a22 c| * (C.cInf * N) := by
      rw [← abs_mul]
      calc |a12 c * v₂| = |(-a22 c * v₁ + a12 c * v₂) + a22 c * v₁| := by ring_nf
        _ ≤ |-a22 c * v₁ + a12 c * v₂| + |a22 c * v₁| := abs_add_le _ _
        _ = |-a22 c * v₁ + a12 c * v₂| + |a22 c| * |v₁| := by rw [abs_mul]
        _ ≤ C.cInf * N + |a22 c| * (C.cInf * N) := by gcongr
    have h4 : |v₂| ≤ (1 + |a22 c|) / |a12 c| * (C.cInf * N) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ ha]; linarith
    have : 0 ≤ C.cInf * N := by positivity
    nlinarith
  le_sum v₁ v₂ := by
    have hK := C.K_nonneg
    refine (C.le_sum _ _).trans ?_
    have h : |-a22 c * v₁ + a12 c * v₂| ≤ |a22 c| * |v₁| + |a12 c| * |v₂| := by
      calc _ ≤ |-a22 c * v₁| + |a12 c * v₂| := abs_add_le _ _
        _ = |a22 c| * |v₁| + |a12 c| * |v₂| := by rw [abs_mul, abs_mul, abs_neg]
    have h' : |v₁| + |-a22 c * v₁ + a12 c * v₂| ≤ (1 + |a22 c| + |a12 c|) * (|v₁| + |v₂|) := by
      have := abs_nonneg v₁
      have := abs_nonneg v₂
      have := abs_nonneg (a22 c)
      have := abs_nonneg (a12 c)
      nlinarith
    calc C.K * (|v₁| + |-a22 c * v₁ + a12 c * v₂|)
        ≤ C.K * ((1 + |a22 c| + |a12 c|) * (|v₁| + |v₂|)) := mul_le_mul_of_nonneg_left h' hK
      _ = C.K * (1 + |a22 c| + |a12 c|) * (|v₁| + |v₂|) := by ring

/-! ## Complex poles, measured directly -/

/-- The biquad coefficients `a1 = −k`, `a2 = 1/d − g·(g + k)` (feed-forward coefficients `0`),
whose `biquad.complexPoleNorm` is the SVF measure of `complexPolesContraction`:
`|(p·v₁, v₂ + (k/2)·v₁)|` with `p = biquad.poleIm (normCoeffs c) = √(1/d − g·(g + k) − k²/4)`. -/
noncomputable def normCoeffs (c : CoeffsReal) : biquad.CoeffsReal where
  b0 := 0
  b1 := 0
  b2 := 0
  a1 := -c.k
  a2 := 1 / c.d - c.g * (c.g + c.k)

/-- When `d·(1 + g·(g + k)) = 1` (as in exact arithmetic), `1/d − g·(g + k) = 1`, so
`p² = 1 − k²/4` in `complexPolesContraction`, whatever `g`. -/
theorem normCoeffs_a2_of_d (c : CoeffsReal) (hd : c.d * (1 + c.g * (c.g + c.k)) = 1) :
    (normCoeffs c).a2 = 1 := by
  have h0 : c.d ≠ 0 := by rintro h; rw [h, zero_mul] at hd; exact zero_ne_one hd
  simp only [normCoeffs]
  field_simp
  linear_combination (-1) * hd

/-- `p² · d = 1 − d·g·(g + k) − d·k²/4`, with `p = biquad.poleIm (normCoeffs c)`, when
`k² < 4·(1/d − g·(g + k))` and `d ≠ 0`. -/
theorem poleIm_sq_mul_d (c : CoeffsReal) (hd : c.d ≠ 0)
    (h : (normCoeffs c).a1 ^ 2 < 4 * (normCoeffs c).a2) :
    biquad.poleIm (normCoeffs c) ^ 2 * c.d = 1 - c.d * (c.g * (c.g + c.k)) - c.d * c.k ^ 2 / 4 := by
  rw [biquad.poleIm_sq _ h]
  simp only [normCoeffs]
  field_simp

/-- `1 − 2·g·d·k ≥ 0`: it is `(1 − g·d·k − 2·g²·d)² + 4·(g·d·p)²`. -/
theorem stateMap_det_nonneg (c : CoeffsReal) (hd : c.d ≠ 0)
    (h : (normCoeffs c).a1 ^ 2 < 4 * (normCoeffs c).a2) : 0 ≤ 1 - 2 * c.g * c.d * c.k := by
  have hp := poleIm_sq_mul_d c hd h
  have e : 1 - 2 * c.g * c.d * c.k =
      (1 - c.g * c.d * c.k - 2 * c.g ^ 2 * c.d) ^ 2 +
        4 * (c.g * c.d * biquad.poleIm (normCoeffs c)) ^ 2 := by
    linear_combination (-4 * c.g ^ 2 * c.d) * hp
  rw [e]; positivity

/-- **The state-update map multiplies the measure by exactly `√(1 − 2·g·d·k)`**, when `d ≠ 0`
and `k² < 4·(1/d − g·(g + k))`. -/
theorem complexPoleNorm_update (c : CoeffsReal) (hd : c.d ≠ 0)
    (h : (normCoeffs c).a1 ^ 2 < 4 * (normCoeffs c).a2) (v₁ v₂ : ℝ) :
    biquad.complexPoleNorm (normCoeffs c) (a11 c * v₁ + a12 c * v₂) (a21 c * v₁ + a22 c * v₂) =
      Real.sqrt (1 - 2 * c.g * c.d * c.k) * biquad.complexPoleNorm (normCoeffs c) v₁ v₂ := by
  have hp := poleIm_sq_mul_d c hd h
  have hdet := stateMap_det_nonneg c hd h
  simp only [biquad.complexPoleNorm, Complex.norm_def, Complex.normSq_mk]
  rw [← Real.sqrt_mul hdet]
  congr 1
  generalize biquad.poleIm (normCoeffs c) = p at hp ⊢
  simp only [normCoeffs, a11, a12, a21, a22]
  apply mul_left_cancel₀ hd
  linear_combination
    (((1 - 2 * c.g * c.d * (c.k + c.g)) * v₁ + -(2 * c.g * c.d) * v₂) ^ 2 -
      (1 - 2 * c.g * c.d * c.k) * v₁ ^ 2) * hp

/-- **A `Contraction` for the SVF with complex poles**, when `d > 0`, `g·k > 0` and
`k² < 4·(1/d − g·(g + k))`: the measure `biquad.complexPoleNorm (normCoeffs c)`, the length of
`(p·v₁, v₂ + (k/2)·v₁)` with `p = √(1/d − g·(g + k) − k²/4)`, with `ρ = √(1 − 2·g·d·k)`,
`cInf = (1 + |k|/2)/p + 1` and `K = p + |k|/2 + 1` (written with `|−k|`, the size of
`(normCoeffs c).a1`). -/
noncomputable def complexPolesContraction (c : CoeffsReal) (hd : 0 < c.d)
    (hgk : 0 < c.g * c.k) (h : (normCoeffs c).a1 ^ 2 < 4 * (normCoeffs c).a2) :
    Contraction c where
  N := biquad.complexPoleNorm (normCoeffs c)
  ρ := Real.sqrt (1 - 2 * c.g * c.d * c.k)
  cInf := (1 + |(normCoeffs c).a1| / 2) / biquad.poleIm (normCoeffs c) + 1
  K := biquad.poleIm (normCoeffs c) + |(normCoeffs c).a1| / 2 + 1
  nonneg _ _ := norm_nonneg _
  add_le u₁ u₂ v₁ v₂ := by
    unfold biquad.complexPoleNorm
    have e : (⟨biquad.poleIm (normCoeffs c) * (u₁ + v₁),
        u₂ + v₂ - (normCoeffs c).a1 / 2 * (u₁ + v₁)⟩ : ℂ) =
        ⟨biquad.poleIm (normCoeffs c) * u₁, u₂ - (normCoeffs c).a1 / 2 * u₁⟩ +
          ⟨biquad.poleIm (normCoeffs c) * v₁, v₂ - (normCoeffs c).a1 / 2 * v₁⟩ := by
      apply Complex.ext <;> simp <;> ring
    rw [e]
    exact norm_add_le _ _
  contract v₁ v₂ := le_of_eq (complexPoleNorm_update c hd.ne' h v₁ v₂)
  ρ_nonneg := Real.sqrt_nonneg _
  ρ_lt_one := by
    rw [Real.sqrt_lt' one_pos]
    have : 0 < c.g * c.k * c.d := mul_pos hgk hd
    nlinarith
  cInf_nonneg := by
    have := biquad.poleIm_pos _ h
    positivity
  K_nonneg := by
    have := biquad.poleIm_pos _ h
    positivity
  le_fst v₁ v₂ := by
    set q := normCoeffs c
    have hω := biquad.poleIm_pos q h
    have h0 := Complex.abs_re_le_norm (⟨biquad.poleIm q * v₁, v₂ - q.a1 / 2 * v₁⟩ : ℂ)
    rw [abs_mul, abs_of_pos hω] at h0
    unfold biquad.complexPoleNorm
    set N := ‖(⟨biquad.poleIm q * v₁, v₂ - q.a1 / 2 * v₁⟩ : ℂ)‖
    have hN : 0 ≤ N := norm_nonneg _
    have hv : |v₁| ≤ N / biquad.poleIm q := by rw [le_div_iff₀ hω]; linarith
    have : N / biquad.poleIm q ≤ ((1 + |q.a1| / 2) / biquad.poleIm q + 1) * N := by
      rw [add_mul, one_mul, div_mul_eq_mul_div]
      have : N / biquad.poleIm q ≤ (1 + |q.a1| / 2) * N / biquad.poleIm q :=
        div_le_div_of_nonneg_right (by nlinarith [abs_nonneg q.a1]) hω.le
      linarith
    linarith
  le_snd v₁ v₂ := by
    set q := normCoeffs c
    have hω := biquad.poleIm_pos q h
    have h0 := Complex.abs_re_le_norm (⟨biquad.poleIm q * v₁, v₂ - q.a1 / 2 * v₁⟩ : ℂ)
    have h0' := Complex.abs_im_le_norm (⟨biquad.poleIm q * v₁, v₂ - q.a1 / 2 * v₁⟩ : ℂ)
    rw [abs_mul, abs_of_pos hω] at h0
    unfold biquad.complexPoleNorm
    set N := ‖(⟨biquad.poleIm q * v₁, v₂ - q.a1 / 2 * v₁⟩ : ℂ)‖
    have hN : 0 ≤ N := norm_nonneg _
    have hv : |v₁| ≤ N / biquad.poleIm q := by rw [le_div_iff₀ hω]; linarith
    have h2 : |v₂| ≤ N + |q.a1| / 2 * |v₁| := by
      calc |v₂| = |(v₂ - q.a1 / 2 * v₁) + q.a1 / 2 * v₁| := by ring_nf
        _ ≤ |v₂ - q.a1 / 2 * v₁| + |q.a1 / 2 * v₁| := abs_add_le _ _
        _ = |v₂ - q.a1 / 2 * v₁| + |q.a1| / 2 * |v₁| := by
          rw [abs_mul, abs_div, abs_two]
        _ ≤ N + |q.a1| / 2 * |v₁| := by linarith
    have h3 : |q.a1| / 2 * |v₁| ≤ |q.a1| / 2 * (N / biquad.poleIm q) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    have h4 : |q.a1| / 2 * (N / biquad.poleIm q) ≤ (1 + |q.a1| / 2) / biquad.poleIm q * N := by
      have e : (1 + |q.a1| / 2) / biquad.poleIm q * N - |q.a1| / 2 * (N / biquad.poleIm q) =
          N / biquad.poleIm q := by
        field_simp; ring
      have : 0 ≤ N / biquad.poleIm q := div_nonneg hN hω.le
      linarith
    nlinarith
  le_sum v₁ v₂ := by
    set q := normCoeffs c
    have hω := biquad.poleIm_pos q h
    unfold biquad.complexPoleNorm
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h2 : |v₂ - q.a1 / 2 * v₁| ≤ |v₂| + |q.a1| / 2 * |v₁| := by
      calc |v₂ - q.a1 / 2 * v₁| ≤ |v₂| + |q.a1 / 2 * v₁| := abs_sub _ _
        _ = |v₂| + |q.a1| / 2 * |v₁| := by rw [abs_mul, abs_div, abs_two]
    simp only
    rw [abs_mul, abs_of_pos hω]
    nlinarith [abs_nonneg v₁, abs_nonneg v₂, abs_nonneg q.a1]

/-- **`cInf`, `K` and `ρ` of `complexPolesContraction`, from rational numbers.** With
`p² = 1/d − g·(g + k) − k²/4`: if `0 < pl`, `0 ≤ pu`, `pl² ≤ p² ≤ pu²`, `0 ≤ ρu` and
`1 − 2·g·d·k ≤ ρu²`, then `cInf ≤ (1 + |k|/2)/pl + 1`, `K ≤ pu + |k|/2 + 1` and `ρ ≤ ρu`. -/
theorem complexPolesContraction_bounds (c : CoeffsReal) (hd : 0 < c.d) (hgk : 0 < c.g * c.k)
    (h : (normCoeffs c).a1 ^ 2 < 4 * (normCoeffs c).a2) {pl pu ρu : ℝ} (hpl : 0 < pl)
    (hpu : 0 ≤ pu)
    (hpl2 : pl ^ 2 ≤ 1 / c.d - c.g * (c.g + c.k) - c.k ^ 2 / 4)
    (hpu2 : 1 / c.d - c.g * (c.g + c.k) - c.k ^ 2 / 4 ≤ pu ^ 2)
    (hρu : 0 ≤ ρu) (hρu2 : 1 - 2 * c.g * c.d * c.k ≤ ρu ^ 2) :
    (complexPolesContraction c hd hgk h).cInf ≤ (1 + |c.k| / 2) / pl + 1 ∧
      (complexPolesContraction c hd hgk h).K ≤ pu + |c.k| / 2 + 1 ∧
      (complexPolesContraction c hd hgk h).ρ ≤ ρu := by
  have hω0 := biquad.poleIm_pos _ h
  have e : (normCoeffs c).a2 - (normCoeffs c).a1 ^ 2 / 4 =
      1 / c.d - c.g * (c.g + c.k) - c.k ^ 2 / 4 := by
    simp only [normCoeffs]; ring
  have hω : biquad.poleIm (normCoeffs c) = Real.sqrt (1 / c.d - c.g * (c.g + c.k) - c.k ^ 2 / 4) :=
    by rw [biquad.poleIm, e]
  have hpl' : pl ≤ biquad.poleIm (normCoeffs c) := by
    rw [hω]; exact (le_abs_self pl).trans (Real.abs_le_sqrt hpl2)
  have hpu' : biquad.poleIm (normCoeffs c) ≤ pu := by
    rw [hω]
    have := Real.sqrt_le_sqrt hpu2
    rwa [Real.sqrt_sq hpu] at this
  have hρu' : Real.sqrt (1 - 2 * c.g * c.d * c.k) ≤ ρu := by
    have := Real.sqrt_le_sqrt hρu2
    rwa [Real.sqrt_sq hρu] at this
  have ha : |(normCoeffs c).a1| = |c.k| := by simp [normCoeffs]
  have hk : 0 ≤ 1 + |c.k| / 2 := by positivity
  refine ⟨?_, ?_, hρu'⟩
  · show (1 + |(normCoeffs c).a1| / 2) / biquad.poleIm (normCoeffs c) + 1 ≤ (1 + |c.k| / 2) / pl + 1
    rw [ha]
    have := div_le_div_of_nonneg_left hk hpl hpl'
    linarith
  · show biquad.poleIm (normCoeffs c) + |(normCoeffs c).a1| / 2 + 1 ≤ pu + |c.k| / 2 + 1
    rw [ha]
    linarith

/-- The start `(0, 0)` measures zero. -/
theorem complexPolesContraction_N_zero (c : CoeffsReal) (hd : 0 < c.d) (hgk : 0 < c.g * c.k)
    (h : (normCoeffs c).a1 ^ 2 < 4 * (normCoeffs c).a2) :
    (complexPolesContraction c hd hgk h).N 0 0 = 0 :=
  biquad.complexPoleNorm_zero _

/-- `norm_num` with the coefficients `c` and the bound formulas unfolded: closes the statements
about rational numbers in the worked examples of `Svf/BlockF64.lean` and `Svf/BlockF32.lean`. It
lives here rather than in `Svf/Block.lean` because it also unfolds `normCoeffs`, defined in this
file. -/
scoped macro "svf_bound_norm_num" "[" c:ident "]" : tactic =>
  `(tactic| norm_num [$c:ident, normCoeffs, stateBoundAt, outErrBoundAt, inputGain, outGain,
    bx1, bx2, cs1, cs2, stepErrOut, stepErrState, stepValueBound, errY, errY3, errY4, errY1,
    errY2, errT1, errT2, errL, errR, errB, errQ, errH, errD2, errD1, errP, errK1, opY, opY3, opY4,
    opY1, opY2, opT1, opT2, opL, opR, opB, opQ, opH, opD2, opD1, opP, opK1, abs_of_neg,
    abs_of_pos])

end conjure_dsp_lib.svf

end
