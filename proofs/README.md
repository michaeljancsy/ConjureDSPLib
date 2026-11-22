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
| `gain::ramp_f64` | `gain.ramp_f64_spec` | `Gain.lean` | Never fails, and the output samples are exactly `rampList_f64 start end` of the input samples: with `n` the block's length, sample `i` (`x`) becomes `x * (start + ((end - start) / castNat_f64 n) * castNat_f64 i)` (`rampGain_f64`), each operation in binary64 (Lean's `Float`) in that order. For an empty block, `rampList_f64` is the empty list. |
| (`i as f64` for a `usize` `i`) | `gain.usize_toFloat_eq_castNat_f64` | `Gain.lean` | Aeneas's translation of the cast, `UScalar.toFloat i`, equals `castNat_f64` of the value of `i`: Lean's own conversion of that natural number to binary64 (`Float.Model.ofNat`). How that conversion rounds is Lean core's definition and is not proved here. |
| `gain::ramp_f32` | `gain.ramp_f32_spec`, `gain.usize_toFloat32_eq_castNat_f32` | `Gain.lean` | The same two facts in binary32 (`rampList_f32`, `rampGain_f32`, `castNat_f32`, Lean's `Float32`). |
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
| `one_pole::smooth_step_f64` | `one_pole.smooth_step_f64_eq` | `OnePole/SpecF64.lean` | Exactly `state + (1 - a) * (target - state)` in binary64, in that order (`1` is the binary64 number 1); never fails. |
| `one_pole::smooth_f64` | `one_pole.smooth_f64_spec` | `OnePole/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `state + c * (x - state)` in binary64 to each sample in turn, with `c = 1 - a` computed once in binary64 before the first sample (Lean's `filt_smooth_f64 (1 - a)`). |
| `one_pole::smooth_step_f32`, `smooth_f32` | `one_pole.smooth_step_f32_eq`, `one_pole.smooth_f32_spec` | `OnePole/SpecF32.lean` | The same two facts in binary32 (Lean's `filt_smooth_f32`). |
| (the smoother's form) | `one_pole.filt_smooth_real_eq_filt_real` | `OnePole/Smooth.lean` | In exact arithmetic, for any `A`, starting state `r` and list of inputs: the smoother `y = y_prev + (1 - A)·(x - y_prev)` (`filt_smooth_real`) gives exactly the same outputs and final state as the one-pole `y = x' + A·y_prev` (`filt_real`) run from the same state on the inputs `x' = (1 - A)·x`. |
| (the smoother's form) | `one_pole.filt_smooth_real_replicate` | `OnePole/Smooth.lean` | In exact arithmetic, for any `A`, starting state `r`, input `X` and number of samples `n`: the input `X` held for `n` samples gives the outputs `X + A^(k+1)·(r - X)` for `k = 0, …, n - 1` and the final state `X + A^n·(r - X)`. |
| (the smoother's form) | `one_pole.tendsto_filt_smooth_real_replicate` | `OnePole/Smooth.lean` | In exact arithmetic, when `\|A\| < 1`: for any starting state `r` and input `X`, the final state after `X` is held for `n` samples tends to `X` as `n` grows. |
| `biquad::step_f64` | `biquad.step_f64_eq` | `Biquad/SpecF64.lean` | Exactly the transposed-direct-form-II step `tdf2_f64` (output `b0·x + s1`, new state `b1·x - a1·y + s2` and `b2·x - a2·y`) in binary64, in the Rust code's order; never fails. |
| `biquad::process_f64` | `biquad.process_f64_spec` | `Biquad/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `tdf2_f64` to each sample in turn (Lean's `filt_f64`). |
| `biquad::step_f32`, `process_f32` | `biquad.step_f32_eq`, `biquad.process_f32_spec` | `Biquad/SpecF32.lean` | The same two facts in binary32. |
| (the biquad's form) | `biquad.filt_real_eq_df1_real_zero`, `biquad.filt_real_eq_df1_real` | `Biquad/Textbook.lean` | In exact arithmetic, the transposed form from a zero state gives exactly the textbook recurrence `y[n] = b0·x[n] + b1·x[n-1] + b2·x[n-2] - a1·y[n-1] - a2·y[n-2]` with zero history (and, in general, from the state that matches a given history). |
| `biquad::step_f64` | `biquad.tdf2_f64_localErr` | `Biquad/BlockF64.lean` | When the coefficients, state and input are finite and no intermediate result overflows (`StepFinite_f64`), with both state values at most `Sb` and the input at most `M` in size: the output `y` is within `α + β·Sb` of `b0·x + s1`, and each new state value within `α + β·Sb` of the exact step from the same state and the computed output `y` (`b1·x - a1·y + s2`, `b2·x - a2·y`), where `α = 7u((\|b0\| + \|b1\| + \|b2\|)M + 4(\|a1\| + \|a2\|)\|b0\|M + (3(\|a1\| + \|a2\|) + 1)η) + 4η` and `β = 7u(2(\|a1\| + \|a2\|) + 1)` (`localErrBase_f64`, `localErrSlope_f64`), all on the exact values of the stored floats. |
| `biquad::process_f64` | `biquad.process_f64_block_error` (and `filt_f64_block_error`, the same about `filt_f64`) | `Biquad/BlockF64.lean` | **Whole-block error.** Given a `Contraction` for the real values of the stored coefficients (`realCoeffs_f64`), finite coefficients and starting state, no overflow (`NoOverflow_f64`), every input at most `M` in size with `M ≥ 0`, and `cInf·K·κ·β < 1 - ρ` with `κ = 2 + \|a1\| + \|a2\|`: never fails; each output sample is within `cInf·Ê + L` of the corresponding output of `filt_real` run on the real values of the stored inputs from the real value of the stored starting state (`realState_f64`); each final state value is within `cInf·Ê` of the exact one; for a block of any length. `β`, `L` and `Ê` are listed below the table. |
| `biquad::step_f32`, `process_f32` | `biquad.tdf2_f32_localErr`, `biquad.process_f32_block_error` (and `filt_f32_block_error`) | `Biquad/BlockF32.lean` | The same in binary32. |
| `biquad::step_f64` | `biquad.stepFinite_f64` | `Biquad/BlockF64.lean` | When the coefficients, both state values and the input are finite, both state values are at most `Sb` and the input at most `M` in size, and `V` (listed below the table, at that `Sb`) is at most the largest finite binary64 value: none of the step's nine operations overflows (`StepFinite_f64`). |
| `biquad::process_f64` | `biquad.noOverflow_f64_of_inputs` | `Biquad/BlockF64.lean` | Given a `Contraction` for the real values of the stored coefficients, finite coefficients, any numbers `Sb`, `M`, `R`, `Ê` (not necessarily those listed below the table) with `ρ·R + K·G·M ≤ R`, `ρ·Ê + K·κ·(α + β·Sb) ≤ Ê`, `cInf·(R + Ê) ≤ Sb` and `V` (at that `Sb`) at most the largest finite binary64 value, a starting state with both values finite, a real pair `r` with `N(r) ≤ R` and `N(S − r) ≤ Ê` where `S` is the starting state's real value, and every input finite and at most `M` in size: no step overflows (`NoOverflow_f64`). |
| `biquad::process_f64` | `biquad.process_f64_block_error_of_inputs` (and `filt_f64_block_error_of_inputs`, the same about `filt_f64`) | `Biquad/BlockF64.lean` | **Whole-block error, with conditions on the inputs only.** Given a `Contraction` for the real values of the stored coefficients, finite coefficients and starting state, every input finite and at most `M` in size with `M ≥ 0`, `cInf·K·κ·β < 1 - ρ`, and `V` with `Sb` as below (`stepValueBound_f64`) at most the largest finite binary64 value (about 1.8 × 10³⁰⁸): no step overflows (`NoOverflow_f64`), and the conclusion of `process_f64_block_error` holds: never fails; each output sample is within `cInf·Ê + L` of the corresponding output of `filt_real` run on the real values of the stored inputs from the real value of the stored starting state; each final state value is within `cInf·Ê` of the exact one; for a block of any length. |
| `biquad::step_f32`, `process_f32` | `biquad.stepFinite_f32`, `biquad.noOverflow_f32_of_inputs`, `biquad.process_f32_block_error_of_inputs` (and `filt_f32_block_error_of_inputs`) | `Biquad/BlockF32.lean` | The same three in binary32 (largest finite value about 3.4 × 10³⁸). |
| (biquads with complex poles) | `biquad.complexPolesContraction`, `biquad.complexPoleNorm_update` | `Biquad/Contraction.lean` | A `Contraction` for any biquad with complex poles inside the unit circle (`a1² < 4·a2`, `a2 < 1`): for example RBJ low-pass, high-pass, band-pass, notch and all-pass filters with `Q > 1/2`, provided `a1² < 4·a2` still holds after the coefficients are rounded (it fails in f32 for a 1 Hz Butterworth low-pass at 48 kHz). Measured by `complexPoleNorm`, the state-update map multiplies every pair's measure by exactly `√a2`, the pole radius (`ρ = √a2`). `cInf = (1 + \|a1\|/2)/ω + 1` and `K = ω + \|a1\|/2 + 1` with `ω = √(a2 - a1²/4)`; `cInf` grows like `1/ω` as the poles approach the real axis. |

For the biquad whole-block theorems (`Biquad/Block.lean`, `Biquad/BlockF64.lean`), every
quantity below is computed from the real values of the stored coefficients, with `u` and `η` of
the precision, `N`, `ρ`, `cInf` and `K` from the given `Contraction`, and `S` the real value of
the stored starting state:

- `G = |b1 - a1·b0| + |b2 - a2·b0|` (`inputGain`) and `κ = 2 + |a1| + |a2|` (`roundGain`);
- `α = localErrBase_f64` / `localErrBase_f32` and `β = localErrSlope_f64` / `localErrSlope_f32`
  (formulas in the `tdf2_f64_localErr` row);
- `R = N(S) + K·G·M/(1 - ρ)` (`exactStateBound`);
- `Sb = cInf·(R·(1 - ρ) + K·κ·α)/(1 - ρ - cInf·K·κ·β)` (`computedStateBound`);
- `L = α + β·Sb` (`localErrBound`, `localErrBound_f64` / `localErrBound_f32`);
- `Ê = K·κ·L/(1 - ρ)` (`stateErrBound`, `stateErrBound_f64` / `stateErrBound_f32`);
- `V = 4·(|b0| + |b1| + |b2|)·M + 4·(|a1| + |a2|)·(4·|b0|·M + 2·Sb + 3·η) + Sb + 5·η`
  (`stepValueBound`; `stepValueBound_f64` / `stepValueBound_f32` take `Sb` from
  `computedStateBound_f64` / `computedStateBound_f32`, the `Sb` above). `step_values_le` shows
  that, when `0 ≤ u ≤ 1`, `0 ≤ η`, both state values are at most `Sb` and the input at most `M`
  in size, and each earlier rounding of the step is within `u·|e| + η` of its exact operation `e`,
  the exact value of each of the step's nine operations is at most `V` in size.

The `toReal` and error theorems are stated about the expression `x + a * y`; the `step_*_eq`
theorems are what tie that expression to the Rust functions. The whole-block theorems are stated
about `process_f64` / `process_f32` directly. Their real-number argument is in `OnePole/Block.lean`
(`block_error_real`), shared by both precisions; the biquad's is in `Biquad/Block.lean`.

For the one-pole, the whole-block theorems compare the Rust outputs with the exact filter run on
the exact real values of the stored floats: `A` is the value of `a`, `S` of the starting `state`,
and the inputs are the values of the stored samples. (So turning a decimal coefficient into a
float is not covered: 0.99 is stored in f32 as 0.9900000095.) The biquad theorems likewise use
the real values of the stored coefficients (`realCoeffs_f64`), starting state (`realState_f64`)
and inputs. The one-pole's conditions:

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

For the biquad, using `complexPolesContraction`, for an RBJ-cookbook Butterworth low-pass
(`Q = 0.7071`) at 48 kHz, with its coefficients rounded to each precision, inputs at most 1.0 and
a start from zero, the proved bound `cInf·Ê + L` on each output's error is as follows (worked out
by hand, not proved; dB relative to 1.0):

| Cutoff | f32 | f64 |
|---|---|---|
| 100 Hz | 17 (above 1.0) | 1.0 × 10⁻⁸ (−159.9 dB) |
| 1 kHz | 5.4 × 10⁻² (−25.3 dB) | 1.0 × 10⁻¹⁰ (−200.0 dB) |
| 10 kHz | 1.8 × 10⁻⁴ (−74.9 dB) | 3.4 × 10⁻¹³ (−249.5 dB) |

In f32 the condition `cInf·K·κ·β < 1 - ρ` fails below about 82.4 Hz, so nothing is proved there,
and the bound is above 1.0 below about 250 Hz.

These bounds are much larger than the one-pole's. Part of that is real: at low cutoffs the poles
sit near the real axis, and the filter's own worst-case error gain is large (about 1.3 × 10⁴ at
100 Hz). Part is slack in the proof: the state bound `Sb` used for the per-step rounding is about
7–23× the true largest state (at 100 Hz, 1 kHz and 10 kHz), the per-step bound is crude, and the
contraction step adds a factor of about 4. Typical rounding errors are much smaller. In f64 the
bound is below −120 dB from about 10 Hz to about 23.8 kHz, and −80 dB at 1 Hz. In f32 it is below
−25 dB only from about 1 kHz to about 21 kHz, above 1.0 below about 250 Hz and above about 23 kHz,
and absent below about 82.4 Hz. The bound is not monotonic in the cutoff (for example f32: −74.9 dB
at 10 kHz, −37.9 dB at 20 kHz). Everything in this paragraph is worked out by hand, not proved.

For the same filter, inputs and start, the cap `V` of the biquad whole-block `_of_inputs`
theorems (`filt_*_block_error_of_inputs`, `process_*_block_error_of_inputs`), at the `Sb` they use
(`computedStateBound_f64` / `_f32`), is as follows (worked out by hand, not proved):

| Cutoff | f32 `Sb` | f32 `V` | f64 `Sb` | f64 `V` |
|---|---|---|---|---|
| 100 Hz | 25 | 6.2 × 10² | 8.0 | 2.0 × 10² |
| 1 kHz | 8.3 | 1.9 × 10² | 8.3 | 1.8 × 10² |
| 10 kHz | 7.3 | 41 | 7.3 | 41 |

At these cutoffs `V` is below the largest finite value (about 3.4 × 10³⁸ in f32, 1.8 × 10³⁰⁸ in
f64) by a factor of more than 10³⁵ (worked out by hand, not proved). With
`complexPolesContraction`, in f32 below about 82.4 Hz the biquad whole-block `_of_inputs` theorems
prove nothing, because their condition `cInf·K·κ·β < 1 - ρ` fails there, as for the other
whole-block theorems. The hypotheses of `noOverflow_f32_of_inputs` cannot all hold there either:
its `ρ·Ê + K·κ·(α + β·Sb) ≤ Ê`, `cInf·(R + Ê) ≤ Sb`, `N(r) ≤ R` and `N(S − r) ≤ Ê` together
imply that condition when `α > 0` and `cInf·K·κ > 0`, as for `complexPolesContraction` (shown by
hand, not proved).

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
  separate multiply and add: Rust does not fuse `x + a * y` (or the smoother's
  `state + c * (x - state)`, or the biquad's `b0 * x + s1` and `b1 * x - a1 * y + s2`) into one
  multiply-add instruction unless the code asks for `mul_add`, and this code does not.
- No floating-point error bound is proved for the smoother (`one_pole::smooth_*`) yet. The
  one-pole's error theorems are about `x + a * y` and do not apply to the smoother's order of
  operations, `state + (1 - a) * (target - state)`. The theorems in `OnePole/Smooth.lean` are in
  exact arithmetic only: in floating point, the smoother and `process_*` fed `(1 - a)·x` round
  differently and can give different results.
- The biquad's whole-block error bound is proved for any given `Contraction` of its state-update
  map. One is supplied only for complex poles inside the unit circle (`complexPolesContraction`),
  so for real-pole biquads (for example an RBJ low-pass with `Q ≤ 1/2`) no bound is proved yet. It
  also assumes `cInf·K·κ·β < 1 - ρ` (false in f32 for a 48 kHz Butterworth low-pass below about
  82.4 Hz). `process_f64_block_error` / `process_f32_block_error` also assume that no step
  overflows (`NoOverflow_f64` / `NoOverflow_f32`), a condition on the computed values; the
  whole-block `_of_inputs` theorems instead assume that every input is finite and that `V` is at
  most the largest finite value, and prove that no step overflows (through
  `noOverflow_f64_of_inputs` / `_f32`, which assumes the proof's invariant bounds instead). The
  textbook equivalence is in exact arithmetic: in floating point the transposed form and the
  textbook form round differently.

## Layout

- `Code/` is generated by Aeneas from the whole crate. Never edit it by hand.
- One file per Rust module while it has one proof file (`Gain.lean`); a folder once it has more
  (`OnePole/`). Inside a folder: `SpecF64.lean`/`SpecF32.lean` say what the translated code
  computes; `BridgeF64.lean`/`BridgeF32.lean` relate one step to real numbers; `Block.lean` holds
  the whole-block argument on real numbers only, shared by both precisions, and
  `BlockF64.lean`/`BlockF32.lean` apply it to the Rust functions; `Smooth.lean` (real numbers
  only) relates the one-pole smoother to the one-pole filter; `Textbook.lean` (real numbers
  only) shows the code's form of a filter equals the textbook formula; `Contraction.lean` (real
  numbers only) builds a `Contraction` for biquads with complex poles inside the unit circle.
- Names: Lean names about one precision end in `_f64` or `_f32`, like the Rust names
  (`filt_f64`, `real_f32`, `NoOverflow_f64`), and the filter functions keep the `filt_` prefix
  (`filt_real`). Otherwise Lean names follow Mathlib: definitions that are statements start with
  a capital (`WithinStepErr`), other definitions are lowerCamelCase (`stepErr`), and theorems are
  snake case, keeping the casing of any definition they mention, except that a capitalized one
  starts lowercase (`filt_f64_withinStepErr`, `noOverflow_f64_of_inputs`).
- `FloatFacts.lean` holds facts about floats shared by every module's proofs, including
  `real_f64` / `real_f32` (the exact real value of a float).
