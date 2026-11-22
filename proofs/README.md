# What is proved

Lean proofs about the Rust code in `src/`, checked by `scripts/prove.sh`. Every theorem below
depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`; none uses
`sorry`. Every module is also replayed through Lean's kernel with `leanchecker`. Lean names are in
the namespace `conjure_dsp_lib`.

"Never fails" means the translated function always returns normally: no panic, no out-of-bounds
index, no arithmetic overflow on indices, and it terminates.

| Rust function | Theorem | File | Says |
|---|---|---|---|
| `gain::apply_f64`, `apply_f32` | `gain.apply_f64_eq`, `gain.apply_f32_eq` | `Gain.lean` | Exactly `gain * x` (Lean's `Float.mul` / `Float32.mul`); never fails. |
| `one_pole::step_f64` | `one_pole.step_f64_eq` | `OnePole/SpecF64.lean` | Exactly `x + a * state` in binary64; never fails. |
| `one_pole::process_f64` | `one_pole.process_f64_spec` | `OnePole/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `x + a * state` in binary64 to each sample in turn (Lean's `filt_f64`). |
| `one_pole::step_f64` | `one_pole.step_f64_toReal` | `OnePole/BridgeF64.lean` | When `a`, `state`, `x`, the rounded product `a·state` and the result are all finite (no overflow): the result's real value is `x + a·state` with the product rounded to nearest, then the sum rounded to nearest. |
| `one_pole::step_f64` | `one_pole.step_f64_error` | `OnePole/BridgeF64.lean` | Under the same no-overflow conditions: one step is within `u·\|x + a·y\| + (1 + u)(u·\|a·y\| + η) + η` of exact real arithmetic (`y` = `state`, `u = 2⁻⁵³`, `η` = half the smallest subnormal gap). |
| `one_pole::step_f32`, `process_f32` | `one_pole.step_f32_eq`, `one_pole.process_f32_spec` | `OnePole/SpecF32.lean` | The same two facts in binary32 (Lean's `filt_f32`). |
| `one_pole::step_f32` | `one_pole.step_f32_toReal`, `one_pole.step_f32_error` | `OnePole/BridgeF32.lean` | The same real-number link and error bound in binary32 (`u = 2⁻²⁴`), under the same no-overflow conditions. |
| `one_pole::process_f64` | `one_pole.process_f64_block_error` (and `filt_f64_block_error`, the same about `filt_f64`) | `OnePole/BlockF64.lean` | **Whole-block error.** Under the conditions below: never fails, and every output sample and the final state are within `E` of the exact real-number filter `filt_real`, for a block of any length. |
| `one_pole::process_f32` | `one_pole.process_f32_block_error` (and `filt_f32_block_error`) | `OnePole/BlockF32.lean` | The same in binary32. |
| `one_pole::process_f64` | `one_pole.process_f64_block_error_of_inputs` (and `noOverflow_f64_of_inputs`) | `OnePole/BlockF64.lean` | **The same, with conditions on the inputs only:** no step overflows, proved from the inputs rather than assumed, when `M + (1 + u)·(B + E) + η` is at most the largest finite binary64 value (about 1.8 × 10³⁰⁸). |
| `one_pole::process_f32` | `one_pole.process_f32_block_error_of_inputs` (and `noOverflow_f32_of_inputs`) | `OnePole/BlockF32.lean` | The same in binary32 (largest finite value about 3.4 × 10³⁸). |
| `biquad::step_f64` | `biquad.step_f64_eq` | `Biquad/SpecF64.lean` | Exactly the transposed-direct-form-II step `tdf2_f64` (output `b0·x + s1`, new state `b1·x - a1·y + s2` and `b2·x - a2·y`) in binary64, in the Rust code's order; never fails. |
| `biquad::process_f64` | `biquad.process_f64_spec` | `Biquad/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `tdf2_f64` to each sample in turn (Lean's `filt_f64`). |
| `biquad::step_f32`, `process_f32` | `biquad.step_f32_eq`, `biquad.process_f32_spec` | `Biquad/SpecF32.lean` | The same two facts in binary32. |
| (the biquad's form) | `biquad.filt_real_eq_df1_real_zero`, `biquad.filt_real_eq_df1_real` | `Biquad/Textbook.lean` | In exact arithmetic, the transposed form from a zero state gives exactly the textbook recurrence `y[n] = b0·x[n] + b1·x[n-1] + b2·x[n-2] - a1·y[n-1] - a2·y[n-2]` with zero history (and, in general, from the state that matches a given history). |

The `toReal` and error theorems are stated about the expression `x + a * y`; the `step_*_eq`
theorems are what tie that expression to the Rust functions. The whole-block theorems are stated
about `process_f64` / `process_f32` directly. Their real-number argument is in `OnePole/Block.lean`
(`block_error_real`), shared by both precisions.

The whole-block theorems compare the Rust outputs with the exact filter run on the exact real
values of the stored floats: `A` is the value of `a`, `S` of the starting `state`, and the inputs
are the values of the stored samples. (So turning a decimal coefficient into a float is not
covered: 0.99 is stored in f32 as 0.9900000095.) Their conditions:

- `a`, the starting state and every input are finite, and no step overflows (`NoOverflow_f64` /
  `NoOverflow_f32`: every rounded product `a * state` and every output is finite). The
  `_of_inputs` theorems need no no-overflow condition: they prove it, given the other conditions
  here and that `M + (1 + u)·(B + E) + η` (with `B` and `E` below) is at most the largest finite
  value;
- every input is at most `M` in size;
- `|A| + |A|·u·(2 + u) < 1`, which is `|A|·(1 + u)² < 1`: stable, with a little room for
  rounding. Any `|A| ≤ 1 - 2⁻⁵¹` (f64) or `|A| ≤ 1 - 2⁻²²` (f32) satisfies it (simple
  algebra, not a Lean theorem).

Then, with `B = |S| + M / (1 - |A|)` (a bound on the exact filter's outputs):

`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`

### What the whole-block bound means in practice

These numbers are worked out by hand from the formula for `E`; Lean does not prove them. They are
for inputs at most 1.0 in size and a starting state of 0, so the exact output stays within
`B = 1 / (1 - a)`. `η` is negligible at this scale. The last column is `20·log₁₀(E / B)`.

| Precision | `a` | `B` | `E` | `E` relative to `B` |
|---|---|---|---|---|
| f32 | 0.5 | 2 | 3.6 × 10⁻⁷ | −135.0 dB |
| f32 | 0.99 | 100 | 1.2 × 10⁻³ | −98.5 dB |
| f32 | 0.999 | 1000 | 0.12 | −78.5 dB |
| f64 | 0.99 | 100 | 2.2 × 10⁻¹² | −273.1 dB |
| f64 | 0.999 | 1000 | 2.2 × 10⁻¹⁰ | −253.1 dB |

The bound grows like `1 / (1 - a)²` as `a` approaches 1: slow smoothers in f32 lose the most.
It is a worst case: typical rounding errors partly cancel and are much smaller. The size limit of
the `_of_inputs` theorems is far from binding: with `a = 0.999`, inputs at most 1 and a start of
0, `B + E` is about 1000, against a largest finite value of about 3.4 × 10³⁸ in f32.

## What is assumed, not proved

- Charon and Aeneas translate the Rust code into Lean faithfully.
- Aeneas's float model (from the pinned `conjure` commit) has a single NaN: any operation that
  produces a NaN drops its sign and payload. So anything that reads a NaN's sign or bit pattern
  (`to_bits`, `is_sign_*`, `copysign`, `recip`, casts, and `from_bits` of a NaN bit pattern) can
  differ from compiled Rust. `min`/`max` of +0 and −0 may return either; Rust leaves this open
  too, and the model does not let a proof depend on which. No proof here relies on NaN bit
  patterns, NaN signs, or which zero `min`/`max` returns.
- Not modelled: `sin`, `exp` and other transcendental functions, and the `NAN` constant. This
  crate uses none of them.
- Rust's `f32`/`f64` operations and Lean's `Float32`/`Float` operations are the same IEEE 754
  round-to-nearest operations. FloatLib relates Lean's floats to real numbers; nothing here
  verifies machine instructions or compiler optimizations. In particular, the proofs assume a
  separate multiply and add: Rust does not fuse `x + a * y` (or the biquad's `b0 * x + s1` and
  `b1 * x - a1 * y + s2`) into one multiply-add instruction unless the code asks for `mul_add`,
  and this code does not.
- The biquad's floating-point error bound is not proved yet (issue #5, second part). The
  textbook equivalence is in exact arithmetic: in floating point the transposed form and the
  textbook form round differently.

## Layout

- `Code/` is generated by Aeneas from the whole crate. Never edit it by hand.
- One file per Rust module while it has one proof file (`Gain.lean`); a folder once it has more
  (`OnePole/`). Inside a folder: `SpecF64.lean`/`SpecF32.lean` say what the translated code
  computes; `BridgeF64.lean`/`BridgeF32.lean` relate one step to real numbers; `Block.lean` holds
  the whole-block argument on real numbers only, shared by both precisions, and
  `BlockF64.lean`/`BlockF32.lean` apply it to the Rust functions; `Textbook.lean` (real numbers
  only) shows the code's form of a filter equals the textbook formula.
- Names: Lean names about one precision end in `_f64` or `_f32`, like the Rust names
  (`filt_f64`, `real_f32`, `NoOverflow_f64`), and the filter functions keep the `filt_` prefix
  (`filt_real`). Otherwise Lean names follow Mathlib: definitions that are statements start with
  a capital (`WithinStepErr`), other definitions are lowerCamelCase (`stepErr`), and theorems are
  snake case, keeping the casing of any definition they mention, except that a capitalized one
  starts lowercase (`filt_f64_withinStepErr`, `noOverflow_f64_of_inputs`).
- `FloatFacts.lean` holds facts about floats shared by every module's proofs, including
  `real_f64` / `real_f32` (the exact real value of a float).
