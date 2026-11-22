module

public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.MulDiv
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real

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

end conjure_dsp_lib

end
