module

public import ConjureDSPLib.OnePole.Spec
public import FloatLib.Floats.Formats.IEEE754.Native.AddSub
public import FloatLib.Floats.Formats.IEEE754.Native.MulDiv
public import FloatLib.Floats.Formats.BinaryInterchange.Analysis.StandardModel
public import FloatLib.Floats.Formats.BinaryInterchange.Configured.Real

@[expose] public section

open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.one_pole

/-- A finite Lean `Float`, imported into FloatLib's binary64 type, is still finite. (FloatLib
proves this internally but keeps the lemma private.) -/
theorem isFinite_ofFloat (v : Float) (h : v.isFinite = true) :
    isFinite (ofFloat v : Binary64) = true := by
  unfold isFinite
  simp only [toModel_ofFloat]
  have h' : (Model.toModel (Model.ofFloatModel v.toModel)).isFinite = true := by
    simpa only [Model.toModel_ofFloatModel, Float.isFinite, Float.Model.isFinite] using h
  rwa [Model.isFinite_toModel (by decide)] at h'

/-- **Proof 2, exact form.** For finite values, the real value of the Rust step's result is
`x + a·y` rounded twice: the product `a·y` is rounded to the nearest binary64 number, then the sum
is rounded again. `toReal` reads off a binary64 value's exact real number. -/
theorem step_f64_toReal (a y x : Float)
    (ha : a.isFinite = true) (hy : y.isFinite = true) (hx : x.isFinite = true)
    (hp : (a * y).isFinite = true) (hr : (x + a * y).isFinite = true) :
    toReal (ofFloat (x + a * y) : Binary64) =
      Model.roundAt FloatFormat.binary64
        (toReal (ofFloat x : Binary64) +
          Model.roundAt FloatFormat.binary64
            (toReal (ofFloat a : Binary64) * toReal (ofFloat y : Binary64))) := by
  have hsum := isFinite_ofFloat _ hr
  rw [ofFloat_add_of_isFinite x (a * y) hx hp] at hsum ⊢
  rw [toReal_add_eq_roundAt hsum]
  have hprod := isFinite_ofFloat _ hp
  rw [ofFloat_mul_of_isFinite a y ha hy] at hprod ⊢
  rw [toReal_mul_eq_roundAt hprod]
  rfl

/-- **Proof 2, error bound.** One Rust step differs from exact real arithmetic by at most
`u·|x + a·y| + (1 + u)·(u·|a·y| + η) + η`, where `u = unitRoundoffAt binary64` is the relative
rounding error (2⁻⁵³ for binary64) and `η = underflowErrorAt binary64` is the tiny absolute error
possible for results near zero (half the smallest subnormal spacing). Here `x`, `a`, `y` stand for
the exact real values of the inputs. -/
theorem step_f64_error (a y x : Float)
    (ha : a.isFinite = true) (hy : y.isFinite = true) (hx : x.isFinite = true)
    (hp : (a * y).isFinite = true) (hr : (x + a * y).isFinite = true) :
    let X := toReal (ofFloat x : Binary64)
    let A := toReal (ofFloat a : Binary64)
    let Y := toReal (ofFloat y : Binary64)
    let u := Model.unitRoundoffAt FloatFormat.binary64
    let η := Model.underflowErrorAt FloatFormat.binary64
    |toReal (ofFloat (x + a * y) : Binary64) - (X + A * Y)| ≤
      |X + A * Y| * u + (|A * Y| * u + η) * (1 + u) + η := by
  intro X A Y u η
  rw [step_f64_toReal a y x ha hy hx hp hr]
  obtain ⟨δ1, η1, h1, hd1, he1, -⟩ := Model.roundAt_standardModel FloatFormat.binary64 (A * Y)
  rw [h1]
  obtain ⟨δ2, η2, h2, hd2, he2, -⟩ :=
    Model.roundAt_standardModel FloatFormat.binary64 (X + (A * Y * (1 + δ1) + η1))
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
