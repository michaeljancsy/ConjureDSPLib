module

public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.MulDiv
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError.Rounding
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Facts about Lean's floats and FloatLib's models of them

Shared by the error-bound proofs of every filter.
-/

@[expose] public section

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib

/-- The exact real value of a binary64 number, through FloatLib's model. -/
noncomputable abbrev real_f64 (v : Float) : ℝ := toReal (ofFloat v : Binary64)

/-- The exact real value of a binary32 number, through FloatLib's model. -/
noncomputable abbrev real_f32 (v : Float32) : ℝ := toReal (ofFloat32 v : Binary32)

/-- A finite Lean `Float`, imported into FloatLib's binary64 type, is still finite. (FloatLib
proves this internally but keeps the lemma private.) -/
theorem isFinite_ofFloat (v : Float) (h : v.isFinite = true) :
    isFinite (ofFloat v : Binary64) = true := by
  unfold isFinite
  simp only [toModel_ofFloat]
  have h' : (Model.toModel (Model.ofFloatModel v.toModel)).isFinite = true := by
    simpa only [Model.toModel_ofFloatModel, Float.isFinite, Float.Model.isFinite] using h
  rwa [Model.isFinite_toModel (by decide)] at h'

/-- A finite Lean `Float32`, imported into FloatLib's binary32 type, is still finite. -/
theorem isFinite_ofFloat32 (v : Float32) (h : v.isFinite = true) :
    isFinite (ofFloat32 v : Binary32) = true := by
  unfold isFinite
  simp only [toModel_ofFloat32]
  have h' : (Model.toModel (Model.ofFloat32Model v.toModel)).isFinite = true := by
    simpa only [Model.toModel_ofFloat32Model, Float32.isFinite, Float32.Model.isFinite] using h
  rwa [Model.isFinite_toModel (by decide)] at h'

/-- A Lean `Float` is finite exactly when FloatLib's binary64 copy of it is. -/
theorem isFinite_ofFloat_iff (v : Float) :
    isFinite (ofFloat v : Binary64) = true ↔ v.isFinite = true := by
  refine ⟨fun h => ?_, isFinite_ofFloat v⟩
  unfold isFinite at h
  simp only [toModel_ofFloat] at h
  have e := Model.isFinite_toModel (fmt := FloatFormat.binary64) (by decide)
    (Model.ofFloatModel v.toModel)
  rw [Model.toModel_ofFloatModel] at e
  have h' : Model.isFinite (Model.ofFloatModel v.toModel) = true := h
  rw [← e] at h'
  simpa only [Float.isFinite, Float.Model.isFinite] using h'

/-- A Lean `Float32` is finite exactly when FloatLib's binary32 copy of it is. -/
theorem isFinite_ofFloat32_iff (v : Float32) :
    isFinite (ofFloat32 v : Binary32) = true ↔ v.isFinite = true := by
  refine ⟨fun h => ?_, isFinite_ofFloat32 v⟩
  unfold isFinite at h
  simp only [toModel_ofFloat32] at h
  have e := Model.isFinite_toModel (fmt := FloatFormat.binary32) (by decide)
    (Model.ofFloat32Model v.toModel)
  rw [Model.toModel_ofFloat32Model] at e
  have h' : Model.isFinite (Model.ofFloat32Model v.toModel) = true := h
  rw [← e] at h'
  simpa only [Float32.isFinite, Float32.Model.isFinite] using h'

/-- Binary64's unit roundoff `u = 2⁻⁵³`: the largest relative error of one rounding. -/
noncomputable abbrev unitRoundoff_f64 : ℝ := Model.unitRoundoffAt FloatFormat.binary64

/-- Binary64's underflow error `η`: half the smallest subnormal spacing, the largest absolute
error of one rounding near zero. -/
noncomputable abbrev underflowErr_f64 : ℝ := Model.underflowErrorAt FloatFormat.binary64

/-- Binary32's unit roundoff `u = 2⁻²⁴`. -/
noncomputable abbrev unitRoundoff_f32 : ℝ := Model.unitRoundoffAt FloatFormat.binary32

/-- Binary32's underflow error `η`. -/
noncomputable abbrev underflowErr_f32 : ℝ := Model.underflowErrorAt FloatFormat.binary32

/-- The largest finite binary64 value, as a real number (about 1.8 × 10³⁰⁸). -/
noncomputable abbrev maxFinite_f64 : ℝ :=
  Model.toReal (Model.posMaxFinite FloatFormat.binary64)

/-- The largest finite binary32 value, as a real number (about 3.4 × 10³⁸). -/
noncomputable abbrev maxFinite_f32 : ℝ :=
  Model.toReal (Model.posMaxFinite FloatFormat.binary32)

/-- Binary64's unit roundoff is exactly `2⁻⁵³`. -/
theorem unitRoundoff_f64_eq : unitRoundoff_f64 = 2 ^ (-53 : ℤ) := by
  unfold unitRoundoff_f64
  rw [Model.unitRoundoffAt_eq]
  norm_num [FloatFormat.binary64]

/-- Binary32's unit roundoff is exactly `2⁻²⁴`. -/
theorem unitRoundoff_f32_eq : unitRoundoff_f32 = 2 ^ (-24 : ℤ) := by
  unfold unitRoundoff_f32
  rw [Model.unitRoundoffAt_eq]
  norm_num [FloatFormat.binary32]

/-- Binary64's underflow error is exactly `2⁻¹⁰⁷⁵`, half the smallest subnormal `2⁻¹⁰⁷⁴`. -/
theorem underflowErr_f64_eq : underflowErr_f64 = 2 ^ (-1075 : ℤ) := by
  unfold underflowErr_f64
  rw [Model.underflowErrorAt_eq]
  have h : FloatFormat.minSubnormalExponent FloatFormat.binary64 = -1074 := by decide
  rw [h]
  norm_num

/-- binary64's underflow error is at most `2⁻²⁰⁰`. -/
-- A crude bound, used instead of the exact `2⁻¹⁰⁷⁵`: it keeps the numbers `norm_num` works with
-- small.
theorem underflowErr_f64_le : underflowErr_f64 ≤ 2 ^ (-200 : ℤ) := by
  rw [underflowErr_f64_eq]; exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)

/-- Binary32's underflow error is exactly `2⁻¹⁵⁰`, half the smallest subnormal `2⁻¹⁴⁹`. -/
theorem underflowErr_f32_eq : underflowErr_f32 = 2 ^ (-150 : ℤ) := by
  unfold underflowErr_f32
  rw [Model.underflowErrorAt_eq]
  have h : FloatFormat.minSubnormalExponent FloatFormat.binary32 = -149 := by decide
  rw [h]
  norm_num

/-- The largest finite binary64 value is exactly `(2⁵³ - 1)·2⁹⁷¹`. -/
theorem maxFinite_f64_eq : maxFinite_f64 = (2 ^ 53 - 1) * 2 ^ 971 := by
  unfold maxFinite_f64
  rw [Model.toReal_posMaxFinite_of_eq FloatFormat.binary64 (significand := 2 ^ 53 - 1)
    (exponent := 971) (by decide) (by decide)]
  norm_num

/-- The largest finite binary32 value is exactly `(2²⁴ - 1)·2¹⁰⁴`. -/
theorem maxFinite_f32_eq : maxFinite_f32 = (2 ^ 24 - 1) * 2 ^ 104 := by
  unfold maxFinite_f32
  rw [Model.toReal_posMaxFinite_of_eq FloatFormat.binary32 (significand := 2 ^ 24 - 1)
    (exponent := 104) (by decide) (by decide)]
  norm_num

/-- The sum of two finite `Float`s is finite when the exact sum is at most the largest finite
value in size. -/
theorem isFinite_add_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f64 x + real_f64 y| ≤ maxFinite_f64) : (x + y).isFinite = true := by
  rw [← isFinite_ofFloat_iff, ofFloat_add_of_isFinite x y hx hy]
  refine isFinite_add_of_mixedError (x₀ := real_f64 x + real_f64 y) (r := 0) (a := 0)
    (isFinite_ofFloat x hx) (isFinite_ofFloat y hy) ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- The difference of two finite `Float`s is finite when the exact difference is at most the
largest finite value in size. -/
theorem isFinite_sub_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f64 x - real_f64 y| ≤ maxFinite_f64) : (x - y).isFinite = true := by
  rw [← isFinite_ofFloat_iff, ofFloat_sub_of_isFinite x y hx hy]
  refine isFinite_sub_of_mixedError (x₀ := real_f64 x - real_f64 y) (r := 0) (a := 0)
    (isFinite_ofFloat x hx) (isFinite_ofFloat y hy) ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- The product of two finite `Float`s is finite when the exact product is at most the largest
finite value in size. -/
theorem isFinite_mul_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f64 x * real_f64 y| ≤ maxFinite_f64) : (x * y).isFinite = true := by
  rw [← isFinite_ofFloat_iff, ofFloat_mul_of_isFinite x y hx hy]
  refine isFinite_mul_of_mixedError (x₀ := real_f64 x * real_f64 y) (r := 0) (a := 0)
    (isFinite_ofFloat x hx) (isFinite_ofFloat y hy) ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- The sum of two finite `Float32`s is finite when the exact sum is at most the largest finite
value in size. -/
theorem isFinite_add_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f32 x + real_f32 y| ≤ maxFinite_f32) : (x + y).isFinite = true := by
  rw [← isFinite_ofFloat32_iff, ofFloat32_add_of_isFinite x y hx hy]
  refine isFinite_add_of_mixedError (x₀ := real_f32 x + real_f32 y) (r := 0) (a := 0)
    (isFinite_ofFloat32 x hx) (isFinite_ofFloat32 y hy) ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- The difference of two finite `Float32`s is finite when the exact difference is at most the
largest finite value in size. -/
theorem isFinite_sub_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f32 x - real_f32 y| ≤ maxFinite_f32) : (x - y).isFinite = true := by
  rw [← isFinite_ofFloat32_iff, ofFloat32_sub_of_isFinite x y hx hy]
  refine isFinite_sub_of_mixedError (x₀ := real_f32 x - real_f32 y) (r := 0) (a := 0)
    (isFinite_ofFloat32 x hx) (isFinite_ofFloat32 y hy) ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- The product of two finite `Float32`s is finite when the exact product is at most the largest
finite value in size. -/
theorem isFinite_mul_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f32 x * real_f32 y| ≤ maxFinite_f32) : (x * y).isFinite = true := by
  rw [← isFinite_ofFloat32_iff, ofFloat32_mul_of_isFinite x y hx hy]
  refine isFinite_mul_of_mixedError (x₀ := real_f32 x * real_f32 y) (r := 0) (a := 0)
    (isFinite_ofFloat32 x hx) (isFinite_ofFloat32 y hy) ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- One binary64 addition of finite numbers with a finite result is within `u·|x + y| + η` of
the exact sum, where `x`, `y` are the operands' exact values, `u` the unit roundoff and `η` the
underflow error. -/
theorem abs_real_add_sub_le_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x + y).isFinite = true) :
    |real_f64 (x + y) - (real_f64 x + real_f64 y)| ≤
      unitRoundoff_f64 * |real_f64 x + real_f64 y| + underflowErr_f64 := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_add_of_isFinite x y hx hy] at h ⊢
  rw [toReal_add_eq_roundAt h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- One binary64 subtraction of finite numbers with a finite result is within `u·|x - y| + η` of
the exact difference. -/
theorem abs_real_sub_sub_le_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x - y).isFinite = true) :
    |real_f64 (x - y) - (real_f64 x - real_f64 y)| ≤
      unitRoundoff_f64 * |real_f64 x - real_f64 y| + underflowErr_f64 := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_sub_of_isFinite x y hx hy] at h ⊢
  rw [toReal_sub_eq_roundAt h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- One binary64 multiplication of finite numbers with a finite result is within `u·|x·y| + η`
of the exact product. -/
theorem abs_real_mul_sub_le_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x * y).isFinite = true) :
    |real_f64 (x * y) - real_f64 x * real_f64 y| ≤
      unitRoundoff_f64 * |real_f64 x * real_f64 y| + underflowErr_f64 := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_mul_of_isFinite x y hx hy] at h ⊢
  rw [toReal_mul_eq_roundAt h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- One binary32 addition of finite numbers with a finite result is within `u·|x + y| + η` of
the exact sum. -/
theorem abs_real_add_sub_le_f32 (x y : Float32) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hr : (x + y).isFinite = true) :
    |real_f32 (x + y) - (real_f32 x + real_f32 y)| ≤
      unitRoundoff_f32 * |real_f32 x + real_f32 y| + underflowErr_f32 := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_add_of_isFinite x y hx hy] at h ⊢
  rw [toReal_add_eq_roundAt h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- One binary32 subtraction of finite numbers with a finite result is within `u·|x - y| + η` of
the exact difference. -/
theorem abs_real_sub_sub_le_f32 (x y : Float32) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hr : (x - y).isFinite = true) :
    |real_f32 (x - y) - (real_f32 x - real_f32 y)| ≤
      unitRoundoff_f32 * |real_f32 x - real_f32 y| + underflowErr_f32 := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_sub_of_isFinite x y hx hy] at h ⊢
  rw [toReal_sub_eq_roundAt h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- One binary32 multiplication of finite numbers with a finite result is within `u·|x·y| + η`
of the exact product. -/
theorem abs_real_mul_sub_le_f32 (x y : Float32) (hx : x.isFinite = true)
    (hy : y.isFinite = true) (hr : (x * y).isFinite = true) :
    |real_f32 (x * y) - real_f32 x * real_f32 y| ≤
      unitRoundoff_f32 * |real_f32 x * real_f32 y| + underflowErr_f32 := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_mul_of_isFinite x y hx hy] at h ⊢
  rw [toReal_mul_eq_roundAt h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- The quotient of two finite `Float`s, the divisor nonzero, is finite when the exact quotient
is at most the largest finite value in size. -/
theorem isFinite_div_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hy0 : real_f64 y ≠ 0) (h : |real_f64 x / real_f64 y| ≤ maxFinite_f64) :
    (x / y).isFinite = true := by
  rw [← isFinite_ofFloat_iff, ofFloat_div_of_isFinite x y hx hy]
  have hz : isZero (ofFloat y : Binary64) = false := by
    cases hz : isZero (ofFloat y : Binary64)
    · rfl
    · exact absurd ((isZero_eq_true_iff_toReal_eq_zero (isFinite_ofFloat y hy)).mp hz) hy0
  refine isFinite_div_of_mixedError (x₀ := real_f64 x / real_f64 y) (r := 0) (a := 0)
    (isFinite_ofFloat x hx) (isFinite_ofFloat y hy) hz ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- One binary64 division of finite numbers with a finite result is within `u·|x / y| + η` of the
exact quotient. -/
theorem abs_real_div_sub_le_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x / y).isFinite = true) :
    |real_f64 (x / y) - real_f64 x / real_f64 y| ≤
      unitRoundoff_f64 * |real_f64 x / real_f64 y| + underflowErr_f64 := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_div_of_isFinite x y hx hy] at h ⊢
  rw [toReal_div_eq_roundAt (isFinite_ofFloat y hy) h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- A finite `Float` is at most the largest finite value in size. -/
theorem abs_real_le_maxFinite_f64 (x : Float) (hx : x.isFinite = true) :
    |real_f64 x| ≤ maxFinite_f64 :=
  abs_toReal_le_posMaxFinite_of_isFinite (isFinite_ofFloat x hx)


/-- The quotient of two finite `Float32`s, the divisor nonzero, is finite when the exact quotient
is at most the largest finite value in size. -/
theorem isFinite_div_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hy0 : real_f32 y ≠ 0) (h : |real_f32 x / real_f32 y| ≤ maxFinite_f32) :
    (x / y).isFinite = true := by
  rw [← isFinite_ofFloat32_iff, ofFloat32_div_of_isFinite x y hx hy]
  have hz : isZero (ofFloat32 y : Binary32) = false := by
    cases hz : isZero (ofFloat32 y : Binary32)
    · rfl
    · exact absurd ((isZero_eq_true_iff_toReal_eq_zero (isFinite_ofFloat32 y hy)).mp hz) hy0
  refine isFinite_div_of_mixedError (x₀ := real_f32 x / real_f32 y) (r := 0) (a := 0)
    (isFinite_ofFloat32 x hx) (isFinite_ofFloat32 y hy) hz ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

/-- One binary32 division of finite numbers with a finite result is within `u·|x / y| + η` of the
exact quotient. -/
theorem abs_real_div_sub_le_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x / y).isFinite = true) :
    |real_f32 (x / y) - real_f32 x / real_f32 y| ≤
      unitRoundoff_f32 * |real_f32 x / real_f32 y| + underflowErr_f32 := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_div_of_isFinite x y hx hy] at h ⊢
  rw [toReal_div_eq_roundAt (isFinite_ofFloat32 y hy) h]
  exact Model.abs_roundAt_sub_le_unitRoundoffAt _ _

/-- A finite `Float32` is at most the largest finite value in size. -/
theorem abs_real_le_maxFinite_f32 (x : Float32) (hx : x.isFinite = true) :
    |real_f32 x| ≤ maxFinite_f32 :=
  abs_toReal_le_posMaxFinite_of_isFinite (isFinite_ofFloat32 x hx)

/-- **A decibel bound from a power bound.** If `0 < x ≤ r` and `r ^ m · 10 ^ n ≤ 1` (`m > 0`),
then `20·log₁₀ x ≤ -(20·n / m)`: `x` in decibels relative to 1 (for example the one-pole's `E / B`,
or the biquad's bound `cInf·Ê + L` relative to 1.0). The power bound is a statement about rational
numbers that `norm_num` checks. -/
theorem twenty_logb_le_of_pow_le (x r : ℝ) (m n : ℕ) (hx : 0 < x) (hxr : x ≤ r) (hm : 0 < m)
    (hr : r ^ m * 10 ^ n ≤ 1) : 20 * Real.logb 10 x ≤ -(20 * n / m) := by
  have hr0 : 0 < r := hx.trans_le hxr
  have h1 : Real.logb 10 x ≤ Real.logb 10 r := Real.logb_le_logb_of_le (by norm_num) hx hxr
  have hpow : r ^ m ≤ ((10 : ℝ) ^ n)⁻¹ := by
    rw [← one_div, le_div_iff₀ (by positivity)]
    exact hr
  have h2 : (m : ℝ) * Real.logb 10 r ≤ -n := by
    rw [← Real.logb_pow]
    calc Real.logb 10 (r ^ m) ≤ Real.logb 10 ((10 : ℝ) ^ n)⁻¹ :=
          Real.logb_le_logb_of_le (by norm_num) (by positivity) hpow
      _ = -n := by rw [Real.logb_inv, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h3 : Real.logb 10 r ≤ -n / m := by
    rw [le_div_iff₀ hm']; linarith
  have : -(20 * (n : ℝ) / m) = 20 * (-n / m) := by ring
  rw [this]
  linarith

end conjure_dsp_lib

end
