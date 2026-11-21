module

public import ConjureDSPLib.Code.ConjureDspLib

/-!
# Gain

`apply_f64` and `apply_f32` are exactly Lean's `Float.mul` / `Float32.mul`, and never fail.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.gain

/-- The Rust `apply_f64` is `gain * x` on Lean's binary64 `Float`, and cannot fail. -/
theorem apply_f64_eq (gain x : Float) : apply_f64 gain x = ok (gain * x) := rfl

/-- The Rust `apply_f32` is `gain * x` on Lean's binary32 `Float32`, and cannot fail. -/
theorem apply_f32_eq (gain x : Float32) : apply_f32 gain x = ok (gain * x) := rfl

end conjure_dsp_lib.gain
