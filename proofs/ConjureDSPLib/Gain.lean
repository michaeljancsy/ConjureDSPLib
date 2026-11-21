module

public import ConjureDSPLib.Code.ConjureDspLib

/-!
# Gain

`apply_gain` and `apply_gain_f32` are exactly one IEEE multiplication, and never fail.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.gain

/-- The Rust `apply_gain` is `gain * x` in binary64 arithmetic, and cannot fail. -/
theorem apply_gain_eq (gain x : Float) : apply_gain gain x = ok (gain * x) := rfl

/-- The Rust `apply_gain_f32` is `gain * x` in binary32 arithmetic, and cannot fail. -/
theorem apply_gain_f32_eq (gain x : Float32) : apply_gain_f32 gain x = ok (gain * x) := rfl

end conjure_dsp_lib.gain
