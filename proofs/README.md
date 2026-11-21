# What is proved

Lean proofs about the Rust code in `src/`, checked by `scripts/prove.sh`. Every theorem below
depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`; none uses
`sorry`. Lean names are in the namespace `conjure_dsp_lib`.

| Rust function | Theorem | File | Says |
|---|---|---|---|
| `gain::apply_gain`, `apply_gain_f32` | `gain.apply_gain_eq`, `gain.apply_gain_f32_eq` | `Gain.lean` | Exactly one IEEE multiplication `gain * x`; never fails. |
| `one_pole::step` | `one_pole.step_eq` | `OnePole/Spec.lean` | Exactly `x + a * y_prev` in binary64; never fails. |
| `one_pole::process` | `one_pole.process_spec` | `OnePole/Spec.lean` | Never fails (no panic, no out-of-bounds index), and its outputs and final state are exactly those of the textbook filter `filt`, sample by sample. |
| `one_pole::step` | `one_pole.step_toReal` | `OnePole/Bridge.lean` | For finite values, the result's real value is `x + a·y` with the product rounded to nearest, then the sum rounded to nearest. |
| `one_pole::step` | `one_pole.step_error` | `OnePole/Bridge.lean` | One step is within `u·\|x + a·y\| + (1 + u)(u·\|a·y\| + η) + η` of exact real arithmetic (`u = 2⁻⁵³`, `η` = half the smallest subnormal gap). |
| `one_pole::step_f32`, `process_f32` | `one_pole.step_f32_eq`, `one_pole.process_f32_spec` | `OnePole/SpecF32.lean` | The same two facts in binary32. |
| `one_pole::step_f32` | `one_pole.step_f32_toReal`, `one_pole.step_f32_error` | `OnePole/BridgeF32.lean` | The same real-number link and error bound in binary32 (`u = 2⁻²⁴`). |

## What is assumed, not proved

- Charon and Aeneas translate the Rust code into Lean faithfully.
- Rust's `f32`/`f64` operations and Lean's `Float32`/`Float` operations are the same IEEE 754
  round-to-nearest operations. FloatLib relates Lean's floats to real numbers; nothing here
  verifies machine instructions or compiler optimizations.
- The one-pole error bound covers one step. A bound over a whole block is issue #3.
