module

public import ConjureDSPLib.OnePole.SpecF32
public import ConjureDSPLib.FloatFacts
public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.MulDiv
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real

/-!
# The one-pole filter in f32: from one step to real numbers

The single-precision version of `BridgeF64.lean`: FloatLib's `Binary32` model of Lean's `Float32`
gives the exact real value of each step, and its error bound. For binary32 the unit roundoff
`u` is 2⁻²⁴. `step_f32_eq` in `SpecF32.lean` says the Rust `step_f32` computes exactly
`x + a * y`, so these facts apply to it.
-/

@[expose] public section

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.one_pole

/-- When `a`, `y`, `x`, the rounded product `a * y` and the result are all finite, the real value of the Rust f32 step's
result is `x + a·y` with the product rounded to the nearest binary32 number, then the sum. -/
theorem step_f32_toReal (a y x : Float32)
    (ha : a.isFinite = true) (hy : y.isFinite = true) (hx : x.isFinite = true)
    (hp : (a * y).isFinite = true) (hr : (x + a * y).isFinite = true) :
    toReal (ofFloat32 (x + a * y) : Binary32) =
      Model.roundAt FloatFormat.binary32
        (toReal (ofFloat32 x : Binary32) +
          Model.roundAt FloatFormat.binary32
            (toReal (ofFloat32 a : Binary32) * toReal (ofFloat32 y : Binary32))) := by
  have hsum := isFinite_ofFloat32 _ hr
  rw [ofFloat32_add_of_isFinite x (a * y) hx hp] at hsum ⊢
  rw [toReal_add_eq_roundAt hsum]
  have hprod := isFinite_ofFloat32 _ hp
  rw [ofFloat32_mul_of_isFinite a y ha hy] at hprod ⊢
  rw [toReal_mul_eq_roundAt hprod]
  rfl

/-- When `a`, `y`, `x`, the rounded product `a * y` and the result are all finite (no
overflow), one f32 step is within
`u·|x + a·y| + (1 + u)·(u·|a·y| + η) + η` of exact real arithmetic, with the binary32 constants
`u = unitRoundoffAt binary32` (2⁻²⁴) and `η = underflowErrorAt binary32`. -/
theorem step_f32_error (a y x : Float32)
    (ha : a.isFinite = true) (hy : y.isFinite = true) (hx : x.isFinite = true)
    (hp : (a * y).isFinite = true) (hr : (x + a * y).isFinite = true) :
    let X := toReal (ofFloat32 x : Binary32)
    let A := toReal (ofFloat32 a : Binary32)
    let Y := toReal (ofFloat32 y : Binary32)
    let u := Model.unitRoundoffAt FloatFormat.binary32
    let η := Model.underflowErrorAt FloatFormat.binary32
    |toReal (ofFloat32 (x + a * y) : Binary32) - (X + A * Y)| ≤
      |X + A * Y| * u + (|A * Y| * u + η) * (1 + u) + η := by
  intro X A Y u η
  rw [step_f32_toReal a y x ha hy hx hp hr]
  obtain ⟨δ1, η1, h1, hd1, he1, -⟩ := Model.roundAt_standardModel FloatFormat.binary32 (A * Y)
  rw [h1]
  obtain ⟨δ2, η2, h2, hd2, he2, -⟩ :=
    Model.roundAt_standardModel FloatFormat.binary32 (X + (A * Y * (1 + δ1) + η1))
  rw [h2]
  have hu : 0 ≤ u := (abs_nonneg _).trans hd1
  have hη : 0 ≤ η := (abs_nonneg _).trans he1
  have k1 : |A * Y * δ1 + η1| ≤ |A * Y| * u + η := by
    refine (abs_add_le _ _).trans (add_le_add ?_ he1)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hd1 (abs_nonneg _)
  have k2 : |1 + δ2| ≤ 1 + u := (abs_add_le _ _).trans (by simpa using hd2)
  have e : (X + (A * Y * (1 + δ1) + η1)) * (1 + δ2) + η2 - (X + A * Y) =
      (X + A * Y) * δ2 + (A * Y * δ1 + η1) * (1 + δ2) + η2 := by ring
  rw [e]
  calc |(X + A * Y) * δ2 + (A * Y * δ1 + η1) * (1 + δ2) + η2|
      ≤ |(X + A * Y) * δ2| + |(A * Y * δ1 + η1) * (1 + δ2)| + |η2| := abs_add_three _ _ _
    _ = |X + A * Y| * |δ2| + |A * Y * δ1 + η1| * |1 + δ2| + |η2| := by rw [abs_mul, abs_mul]
    _ ≤ |X + A * Y| * u + (|A * Y| * u + η) * (1 + u) + η := by
      refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hd2 (abs_nonneg _)) ?_) he2
      exact mul_le_mul k1 k2 (abs_nonneg _) (by positivity)

end conjure_dsp_lib.one_pole

end
