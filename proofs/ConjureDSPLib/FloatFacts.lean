module

public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.MulDiv
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.MixedError.Rounding

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
  have e := Model.isFinite_toModel (fmt := FloatFormat.binary64) (by decide) (Model.ofFloatModel v.toModel)
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
  have e := Model.isFinite_toModel (fmt := FloatFormat.binary32) (by decide) (Model.ofFloat32Model v.toModel)
  rw [Model.toModel_ofFloat32Model] at e
  have h' : Model.isFinite (Model.ofFloat32Model v.toModel) = true := h
  rw [← e] at h'
  simpa only [Float32.isFinite, Float32.Model.isFinite] using h'

/-- The largest finite binary64 value, as a real number (about 1.8 × 10³⁰⁸). -/
noncomputable abbrev maxFinite_f64 : ℝ :=
  Model.toReal (Model.posMaxFinite FloatFormat.binary64)

/-- The largest finite binary32 value, as a real number (about 3.4 × 10³⁸). -/
noncomputable abbrev maxFinite_f32 : ℝ :=
  Model.toReal (Model.posMaxFinite FloatFormat.binary32)

/-- The sum of two finite `Float`s is finite when the exact sum is at most the largest finite
value in size. -/
theorem isFinite_add_f64 (x y : Float) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f64 x + real_f64 y| ≤ maxFinite_f64) : (x + y).isFinite = true := by
  rw [← isFinite_ofFloat_iff, ofFloat_add_of_isFinite x y hx hy]
  refine isFinite_add_of_mixedError (x₀ := real_f64 x + real_f64 y) (r := 0) (a := 0)
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

/-- The product of two finite `Float32`s is finite when the exact product is at most the largest
finite value in size. -/
theorem isFinite_mul_f32 (x y : Float32) (hx : x.isFinite = true) (hy : y.isFinite = true)
    (h : |real_f32 x * real_f32 y| ≤ maxFinite_f32) : (x * y).isFinite = true := by
  rw [← isFinite_ofFloat32_iff, ofFloat32_mul_of_isFinite x y hx hy]
  refine isFinite_mul_of_mixedError (x₀ := real_f32 x * real_f32 y) (r := 0) (a := 0)
    (isFinite_ofFloat32 x hx) (isFinite_ofFloat32 y hy) ⟨le_refl 0, le_refl 0, by simp⟩ ?_
  exact le_of_eq_of_le (by ring) h

end conjure_dsp_lib

end
