module

public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.MulDiv
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError.Rounding
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import FloatLib.Floats.Formats.BinaryInterchange.Rounding.Proof
public import FloatLib.Floats.Formats.BinaryInterchange.Arithmetic.Finiteness
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.Operations.Proof.RoundToIntegral

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

section ModelFacts

open Float.Model (UnpackedFloat Format)

open FloatLib.Numerics in
/-- Lean's conversion of a natural number is FloatLib's nearest-even rounding of it. This
restates FloatLib's `Model.ofModel_ofInt_eq_roundDyadic` (in
`FloatLib/Floats/Formats/IEEE754/Native/Integer/Rounding.lean`) for natural numbers, with the
same proof. That FloatLib module is not imported because it is not built in the pinned package
folder. -/
theorem ofModel_ofNat_eq_roundDyadic (fmt : FloatFormat) (hfmt : fmt.isIEEE = true) (n : ℕ) :
    Model.ofModel fmt (Float.Model.UnpackedFloat.ofInt fmt.toModel (n : Int)) =
      Model.roundDyadic fmt (Dyadic.ofScaledInt n 0) := by
  unfold Float.Model.UnpackedFloat.ofInt Float.Model.UnpackedFloat.normalize
  rw [Model.roundDyadic, ite_eq_left hfmt]
  cases n with
  | zero => simp [Dyadic.ofScaledInt, Model.ieeeRoundDyadic, Model.modelSign]
  | succ n =>
      have hp : (0 : Int) < ((n + 1 : ℕ) : Int) := by simp
      have hc := Int.compare_eq_gt.mpr hp
      rw [hc]
      change Model.ofModel fmt (Float.Model.UnpackedFloat.round fmt.toModel .positive
          (n + 1) 0) =
        Model.ofModel fmt (Float.Model.UnpackedFloat.round fmt.toModel
          (Model.modelSign (decide (((n + 1 : ℕ) : Int) < 0))) (n + 1) 0)
      rw [decide_eq_false (not_lt.mpr hp.le)]
      rfl

/-- Unpacking a packed value of Lean's binary64 model is Lean core's `UnpackedFloat.unpack` of
`UnpackedFloat.pack`. -/
theorem unpack_pack_f64 (u : UnpackedFloat) :
    (Float.Model.pack u).unpack =
      UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 u) := by
  simp [Float.Model.pack, Float.Model.unpack]

/-- A sum with an operand that is not finite (infinite or NaN) is not finite. -/
theorem isFinite_add_eq_false_f64 (x y : Float) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x + y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.add Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.add, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A difference with an operand that is not finite is not finite. -/
theorem isFinite_sub_eq_false_f64 (x y : Float) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x - y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.sub Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.sub, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A product with an operand that is not finite is not finite (infinity times zero is NaN). -/
theorem isFinite_mul_eq_false_f64 (x y : Float) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x * y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.mul Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  rcases h with h | h <;>
  · cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.mul, UnpackedFloat.isFinite]

/-- A quotient whose dividend is not finite is not finite, whatever the divisor. -/
theorem isFinite_div_eq_false_f64 (x y : Float) (h : x.isFinite = false) :
    (x / y).isFinite = false := by
  show (Float.Model.pack (UnpackedFloat.div Format.binary64 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float.isFinite, Float.Model.isFinite] at h
  unfold Float.Model.isFinite
  rw [unpack_pack_f64]
  cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
    simp_all [UnpackedFloat.div, UnpackedFloat.isFinite]

/-- A Lean `Float` is the packed form of its own unpacked form. -/
theorem ofModel_pack_eq_of_unpack_f64 (x : Float) (u : UnpackedFloat)
    (h : u = x.toModel.unpack) : Float.ofModel (Float.Model.pack u) = x := by
  rcases x with ⟨⟨b, hb⟩⟩
  subst h
  simp only [Float.Model.pack, Float.Model.unpack, Float.ofModel.injEq,
    Float.Model.mk.injEq]
  rw [Model.pack_unpack_of_valid _ _ hb]

/-- A `Float` that unpacks to a zero has the bits of that packed zero. -/
theorem toBits_of_unpack_eq_zero_f64 (x : Float) (s : UnpackedFloat.Sign)
    (h : x.toModel.unpack = .zero s) :
    x.toBits = UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.zero s)) := by
  rcases x with ⟨⟨b, hb⟩⟩
  simp only [Float.Model.unpack] at h
  simp only [Float.toBits]
  rw [← h, Model.pack_unpack_of_valid _ _ hb]

/-- Adding a zero to `x` gives exactly `x`, unless `x` is `-0` (bits `0x8000000000000000`). -/
theorem add_zero_of_ne_negZero_f64 (x z : Float) (τ : UnpackedFloat.Sign)
    (hz : z.toModel.unpack = .zero τ) (hx : x.toBits ≠ 0x8000000000000000) : x + z = x := by
  show Float.ofModel (Float.Model.pack (UnpackedFloat.add Format.binary64 x.toModel.unpack
    z.toModel.unpack)) = x
  apply ofModel_pack_eq_of_unpack_f64
  rw [hz]
  cases h : x.toModel.unpack with
  | zero σ =>
    cases σ with
    | negative => exact absurd ((toBits_of_unpack_eq_zero_f64 x _ h).trans (by decide)) hx
    | positive => cases τ <;> rfl
  | _ => rfl

/-- `8·2^1020` is at most the largest finite binary64 value. -/
theorem maxFinite_f64_ge : (8 : ℝ) * 2 ^ 1020 ≤ maxFinite_f64 := by
  rw [maxFinite_f64_eq]
  have h : (8 : ℝ) * 2 ^ 1020 = 2 ^ 52 * 2 ^ 971 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
  rw [h]
  gcongr
  norm_num

/-- binary64's unit roundoff is at most `1/16` (a crude bound that keeps the arithmetic
linear). -/
theorem unitRoundoff_f64_le : unitRoundoff_f64 ≤ 1 / 16 := by
  rw [unitRoundoff_f64_eq, zpow_neg]; norm_num

/-- binary64's underflow error is not negative. -/
theorem underflowErr_f64_nonneg : 0 ≤ underflowErr_f64 := by
  rw [underflowErr_f64_eq]; positivity

/-- Any `N ≤ 2^53` times binary64's underflow error is at most 1. -/
theorem mul_underflowErr_f64_le (N : ℝ) (hN : N ≤ 2 ^ 53) : N * underflowErr_f64 ≤ 1 := by
  have h1 : (2 : ℝ) ^ 53 * 2 ^ (-1075 : ℤ) ≤ 1 := by
    rw [zpow_neg, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 53 ≤ 1075)
  calc N * underflowErr_f64 ≤ 2 ^ 53 * 2 ^ (-1075 : ℤ) := by
        rw [underflowErr_f64_eq]
        exact mul_le_mul_of_nonneg_right hN (by positivity)
    _ ≤ 1 := h1

/-- The real value of a finite sum of finite binary64 numbers is the exact sum rounded to
nearest. -/
theorem real_add_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x + y).isFinite = true) :
    real_f64 (x + y) = Model.roundAt FloatFormat.binary64 (real_f64 x + real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_add_of_isFinite x y hx hy] at h ⊢
  exact toReal_add_eq_roundAt h

/-- The real value of a finite difference of finite binary64 numbers is the exact difference
rounded to nearest. -/
theorem real_sub_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x - y).isFinite = true) :
    real_f64 (x - y) = Model.roundAt FloatFormat.binary64 (real_f64 x - real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_sub_of_isFinite x y hx hy] at h ⊢
  exact toReal_sub_eq_roundAt h

/-- The real value of a finite product of finite binary64 numbers is the exact product
rounded to nearest. -/
theorem real_mul_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x * y).isFinite = true) :
    real_f64 (x * y) = Model.roundAt FloatFormat.binary64 (real_f64 x * real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_mul_of_isFinite x y hx hy] at h ⊢
  exact toReal_mul_eq_roundAt h

/-- The real value of a finite quotient of finite binary64 numbers is the exact quotient
rounded to nearest. -/
theorem real_div_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x / y).isFinite = true) :
    real_f64 (x / y) = Model.roundAt FloatFormat.binary64 (real_f64 x / real_f64 y) := by
  have h := isFinite_ofFloat _ hr
  unfold real_f64
  rw [ofFloat_div_of_isFinite x y hx hy] at h ⊢
  exact toReal_div_eq_roundAt (isFinite_ofFloat y hy) h

/-- Unpacking a packed value of Lean's binary32 model is Lean core's `UnpackedFloat.unpack` of
`UnpackedFloat.pack`. -/
theorem unpack_pack_f32 (u : UnpackedFloat) :
    (Float32.Model.pack u).unpack =
      UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32 u) := by
  simp [Float32.Model.pack, Float32.Model.unpack]

/-- A sum with an operand that is not finite (infinite or NaN) is not finite. -/
theorem isFinite_add_eq_false_f32 (x y : Float32) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x + y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.add Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.add, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A difference with an operand that is not finite is not finite. -/
theorem isFinite_sub_eq_false_f32 (x y : Float32) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x - y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.sub Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  rcases h with h | h
  all_goals
    cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.sub, UnpackedFloat.isFinite]
  all_goals split_ifs <;> simp

/-- A product with an operand that is not finite is not finite (infinity times zero is NaN). -/
theorem isFinite_mul_eq_false_f32 (x y : Float32) (h : x.isFinite = false ∨ y.isFinite = false) :
    (x * y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.mul Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  rcases h with h | h <;>
  · cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
      simp_all [UnpackedFloat.mul, UnpackedFloat.isFinite]

/-- A quotient whose dividend is not finite is not finite, whatever the divisor. -/
theorem isFinite_div_eq_false_f32 (x y : Float32) (h : x.isFinite = false) :
    (x / y).isFinite = false := by
  show (Float32.Model.pack (UnpackedFloat.div Format.binary32 x.toModel.unpack
    y.toModel.unpack)).isFinite = false
  simp only [Float32.isFinite, Float32.Model.isFinite] at h
  unfold Float32.Model.isFinite
  rw [unpack_pack_f32]
  cases hx : x.toModel.unpack <;> cases hy : y.toModel.unpack <;>
    simp_all [UnpackedFloat.div, UnpackedFloat.isFinite]

/-- A Lean `Float32` is the packed form of its own unpacked form. -/
theorem ofModel_pack_eq_of_unpack_f32 (x : Float32) (u : UnpackedFloat)
    (h : u = x.toModel.unpack) : Float32.ofModel (Float32.Model.pack u) = x := by
  rcases x with ⟨⟨b, hb⟩⟩
  subst h
  simp only [Float32.Model.pack, Float32.Model.unpack, Float32.ofModel.injEq,
    Float32.Model.mk.injEq]
  rw [Model.pack_unpack_of_valid _ _ hb]

/-- A `Float32` that unpacks to a zero has the bits of that packed zero. -/
theorem toBits_of_unpack_eq_zero_f32 (x : Float32) (s : UnpackedFloat.Sign)
    (h : x.toModel.unpack = .zero s) :
    x.toBits = UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 (.zero s)) := by
  rcases x with ⟨⟨b, hb⟩⟩
  simp only [Float32.Model.unpack] at h
  simp only [Float32.toBits]
  rw [← h, Model.pack_unpack_of_valid _ _ hb]

/-- Adding a zero to `x` gives exactly `x`, unless `x` is `-0` (bits `0x80000000`). -/
theorem add_zero_of_ne_negZero_f32 (x z : Float32) (τ : UnpackedFloat.Sign)
    (hz : z.toModel.unpack = .zero τ) (hx : x.toBits ≠ 0x80000000) : x + z = x := by
  show Float32.ofModel (Float32.Model.pack (UnpackedFloat.add Format.binary32 x.toModel.unpack
    z.toModel.unpack)) = x
  apply ofModel_pack_eq_of_unpack_f32
  rw [hz]
  cases h : x.toModel.unpack with
  | zero σ =>
    cases σ with
    | negative => exact absurd ((toBits_of_unpack_eq_zero_f32 x _ h).trans (by decide)) hx
    | positive => cases τ <;> rfl
  | _ => rfl

/-- `8·2^124` is at most the largest finite binary32 value. -/
theorem maxFinite_f32_ge : (8 : ℝ) * 2 ^ 124 ≤ maxFinite_f32 := by
  rw [maxFinite_f32_eq]
  have h : (8 : ℝ) * 2 ^ 124 = 2 ^ 23 * 2 ^ 104 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
  rw [h]
  gcongr
  norm_num

/-- binary32's unit roundoff is at most `1/16` (a crude bound that keeps the arithmetic
linear). -/
theorem unitRoundoff_f32_le : unitRoundoff_f32 ≤ 1 / 16 := by
  rw [unitRoundoff_f32_eq, zpow_neg]; norm_num

/-- binary32's underflow error is not negative. -/
theorem underflowErr_f32_nonneg : 0 ≤ underflowErr_f32 := by
  rw [underflowErr_f32_eq]; positivity

/-- Any `N ≤ 2^24` times binary32's underflow error is at most 1. -/
theorem mul_underflowErr_f32_le (N : ℝ) (hN : N ≤ 2 ^ 24) : N * underflowErr_f32 ≤ 1 := by
  have h1 : (2 : ℝ) ^ 24 * 2 ^ (-150 : ℤ) ≤ 1 := by
    rw [zpow_neg, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact_mod_cast pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 24 ≤ 150)
  calc N * underflowErr_f32 ≤ 2 ^ 24 * 2 ^ (-150 : ℤ) := by
        rw [underflowErr_f32_eq]
        exact mul_le_mul_of_nonneg_right hN (by positivity)
    _ ≤ 1 := h1

/-- The real value of a finite sum of finite binary32 numbers is the exact sum rounded to
nearest. -/
theorem real_add_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x + y).isFinite = true) :
    real_f32 (x + y) = Model.roundAt FloatFormat.binary32 (real_f32 x + real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_add_of_isFinite x y hx hy] at h ⊢
  exact toReal_add_eq_roundAt h

/-- The real value of a finite difference of finite binary32 numbers is the exact difference
rounded to nearest. -/
theorem real_sub_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x - y).isFinite = true) :
    real_f32 (x - y) = Model.roundAt FloatFormat.binary32 (real_f32 x - real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_sub_of_isFinite x y hx hy] at h ⊢
  exact toReal_sub_eq_roundAt h

/-- The real value of a finite product of finite binary32 numbers is the exact product
rounded to nearest. -/
theorem real_mul_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x * y).isFinite = true) :
    real_f32 (x * y) = Model.roundAt FloatFormat.binary32 (real_f32 x * real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_mul_of_isFinite x y hx hy] at h ⊢
  exact toReal_mul_eq_roundAt h

/-- The real value of a finite quotient of finite binary32 numbers is the exact quotient
rounded to nearest. -/
theorem real_div_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hr : (x / y).isFinite = true) :
    real_f32 (x / y) = Model.roundAt FloatFormat.binary32 (real_f32 x / real_f32 y) := by
  have h := isFinite_ofFloat32 _ hr
  unfold real_f32
  rw [ofFloat32_div_of_isFinite x y hx hy] at h ⊢
  exact toReal_div_eq_roundAt (isFinite_ofFloat32 y hy) h

end ModelFacts

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
