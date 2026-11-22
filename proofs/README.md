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
| `smoother::step_f64` | `smoother.step_f64_eq` | `Smoother/SpecF64.lean` | Exactly `state + (1 - a) * (target - state)` in binary64, in that order (`1` is the binary64 number 1); never fails. |
| `smoother::process_f64` | `smoother.process_f64_spec` | `Smoother/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `state + c * (x - state)` in binary64 to each sample in turn, with `c = 1 - a` computed once in binary64 before the first sample (Lean's `smoother.filt_f64 (1 - a)`). |
| `smoother::step_f32`, `process_f32` | `smoother.step_f32_eq`, `smoother.process_f32_spec` | `Smoother/SpecF32.lean` | The same two facts in binary32 (Lean's `smoother.filt_f32`). |
| (the smoother, exact arithmetic) | `smoother.filt_real_eq_one_pole_filt_real` | `Smoother/Exact.lean` | In exact arithmetic, for any `A`, starting state `r` and list of inputs: the smoother `y = y_prev + (1 - A)·(x - y_prev)` (`smoother.filt_real`) gives exactly the same outputs and final state as the one-pole `y = x' + A·y_prev` (`one_pole.filt_real`) run from the same state on the inputs `x' = (1 - A)·x`. |
| (the smoother, exact arithmetic) | `smoother.filt_real_replicate` | `Smoother/Exact.lean` | In exact arithmetic, for any `A`, starting state `r`, input `X` and number of samples `n`: the input `X` held for `n` samples gives the outputs `X + A^(k+1)·(r - X)` for `k = 0, …, n - 1` and the final state `X + A^n·(r - X)`. |
| (the smoother, exact arithmetic) | `smoother.tendsto_filt_real_replicate` | `Smoother/Exact.lean` | In exact arithmetic, when `\|A\| < 1`: for any starting state `r` and input `X`, the final state after `X` is held for `n` samples tends to `X` as `n` grows. |
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
| (biquads with complex poles) | `biquad.complexPolesContraction`, `biquad.complexPoleNorm_update` | `Biquad/Contraction.lean` | A `Contraction` for any biquad with complex poles inside the unit circle (`a1² < 4·a2`, `a2 < 1`): for example RBJ low-pass, high-pass, band-pass, notch and all-pass filters with `Q > 1/2` (worked out outside Lean, not proved), provided `a1² < 4·a2` still holds after the coefficients are rounded (it fails in f32 for a 1 Hz Butterworth low-pass at 48 kHz, `lowPass1Hz_real_poles_f32`). Measured by `complexPoleNorm`, the state-update map multiplies every pair's measure by exactly `√a2`, the pole radius (`ρ = √a2`). `cInf = (1 + \|a1\|/2)/ω + 1` and `K = ω + \|a1\|/2 + 1` with `ω = √(a2 - a1²/4)`; `cInf` grows like `1/ω` as the poles approach the real axis. |
| (biquads with distinct real poles) | `biquad.realPolesContraction`, `biquad.realPoleNorm_update`, `biquad.realPoles_lt_one_iff` | `Biquad/Contraction.lean` | A `Contraction` for any biquad with distinct real poles inside the unit circle (`a1² > 4·a2`, `a2 < 1`, `\|a1\| < 1 + a2`; given the first, the other two say both poles are less than 1 in size, `realPoles_lt_one_iff`): for example an RBJ low-pass with `Q < 1/2` (worked out outside Lean, not proved), provided `a1² > 4·a2`, `a2 < 1` and `\|a1\| < 1 + a2` still hold after the coefficients are rounded (the last fails in f32 for a 1 Hz Butterworth low-pass at 48 kHz, `lowPass1Hz_pole_one_f32`). Measured by `realPoleNorm`, `ρ = (\|a1\| + d)/2`, the larger pole size (`max_abs_realPoles`), `cInf = 1/d` and `K = 2`, where `d = √(a1² − 4·a2)` is the distance between the poles; `cInf = 1/d` grows without bound as `d → 0`. The state-update map multiplies `p·v₁ + v₂` by `p` and `q·v₁ + v₂` by `q` (`realPoleCoord_update`). |
| (biquads with a repeated real pole) | `biquad.repeatedPoleContraction` | `Biquad/Contraction.lean` | A `Contraction` for any biquad with a repeated real pole `p = -a1/2` (`a1² = 4·a2`), for any chosen `ε > 0` with `\|p\| + ε < 1`: measured by `repeatedPoleNorm`, `ε·\|v₁\| + \|p·v₁ + v₂\|`, with `ρ = \|p\| + ε`, `cInf = 1 + 1/ε` and `K = 1`. |
| (biquads with a pole at 1) | `biquad.isEmpty_contraction_of_pole_one` | `Biquad/Contraction.lean` | When 1 is a pole (`1 + a1 + a2 = 0`), no `Contraction` exists: the state-update map leaves the pair `(1, -a2)` unchanged (`update_one_neg_a2_of_pole_one`). |
| `delay::process_f64` | `delay.process_f64_ok` | `Delay/SpecF64.lean` | Never fails, for every buffer, position, delay and audio. |
| `delay::process_f64` | `delay.process_f64_empty_buffer` | `Delay/SpecF64.lean` | With an empty buffer: never fails, and returns the buffer, position and audio unchanged. |
| `delay::process_f64` | `delay.process_f64_spec` | `Delay/SpecF64.lean` | For a buffer of length `L > 0`, any position `p`, any delay `delay_samples` and `n` input samples, with `d = min(delay_samples, L - 1)` and the history `H = buffer.rotate p ++ audio` (Mathlib's `List.rotate`: the buffer read oldest first from index `p mod L`, then the input): never fails; the output has `n` samples, and for each `j < n` output sample `j` is element `L + j - d` of `H`; the new buffer has length `L`; the new position is `(p + n) mod L`; and the new buffer read oldest first from the new position (`buffer'.rotate p'`) is `H` without its first `n` elements, that is, its last `L` elements. |
| `delay::process_f64` | `delay.process_f64_spec_of_lt` | `Delay/SpecF64.lean` | The same, when `delay_samples < L`, with `d = delay_samples`. |
| `delay::process_f64` | `delay.process_f64_getElem` | `Delay/SpecF64.lean` | For a buffer of length `L > 0`, with `p`, `n`, `d` and `H` as in `process_f64_spec`: never fails; the output has `n` samples, and for each `j < n` output sample `j` equals `H[L + j - d]` (Lean's `getElem`, with both indices proved in range in the statement). |
| `delay::process_f64` | `delay.process_f64_zero_prefix` | `Delay/SpecF64.lean` | For a buffer of length `L > 0` whose elements are all the float `0`, any position, any `delay_samples` and `n` input samples, with `d = min(delay_samples, L - 1)`: never fails, and output sample `j` is `0` for every `j < min(d, n)`. |
| `delay::process_f64` | `delay.process_f64_append` | `Delay/SpecF64.lean` | For any buffer (empty or not), position and `delay_samples` (the same in every call), and input `audio` equal to `audio₁` followed by `audio₂`: a call on `audio₁`, a call on `audio₂` with the buffer and position the first call returned, and one call on `audio` from the starting buffer and position all never fail; the two calls end with the same buffer and position as the one call, and their output samples, joined, are its output samples. |
| `delay::process_f64` | `delay.process_f64_state_indep` | `Delay/SpecF64.lean` | For any buffer (empty or not), position and audio, and any two delays `d₁` and `d₂`: a call with `d₁` and a call with `d₂`, from the same buffer, position and audio, both never fail and return the same new buffer and the same new position; only their output samples may differ. |
| `delay::process_f32` | `delay.process_f32_ok`, `delay.process_f32_empty_buffer`, `delay.process_f32_spec`, `delay.process_f32_spec_of_lt`, `delay.process_f32_getElem`, `delay.process_f32_zero_prefix`, `delay.process_f32_append`, `delay.process_f32_state_indep` | `Delay/SpecF32.lean` | The same eight facts for `f32` samples. |
| `svf::CoeffsF64::new` | `svf.CoeffsF64.new_eq` | `Svf/SpecF64.lean` | Never fails; keeps `g`, `k`, `m_hp`, `m_bp` and `m_lp`, and computes `d` as exactly `1 / (1 + g * (g + k))` in binary64, in that order (`1` is the binary64 number 1). |
| `svf::step_f64` | `svf.step_f64_eq` | `Svf/SpecF64.lean` | Exactly the step `svfStep_f64` in binary64, in the Rust code's order; never fails. With `hp = ((x - (k + g) * s1) - s2) * d`, `bp = g * hp + s1` and `lp = g * bp + s2`, the output is `(m_hp * hp + m_bp * bp) + m_lp * lp` and the new state is `s1 = g * hp + bp`, `s2 = g * bp + lp`. |
| `svf::process_f64` | `svf.process_f64_spec` | `Svf/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `svfStep_f64` to each sample in turn (Lean's `filt_f64`). |
| `svf::CoeffsF32::new`, `step_f32`, `process_f32` | `svf.CoeffsF32.new_eq`, `svf.step_f32_eq`, `svf.process_f32_spec` | `Svf/SpecF32.lean` | The same three facts in binary32 (`svfStep_f32`, `filt_f32`). |
| `svf::CoeffsF64::low_pass`, `high_pass`, `band_pass`, `notch`, `all_pass` | `svf.CoeffsF64.low_pass_eq`, `high_pass_eq`, `band_pass_eq`, `notch_eq`, `all_pass_eq` | `Svf/SpecF64.lean` | Never fails, and returns exactly the coefficients with `g = libm.tanModel_f64 (PI * cutoff_hz / sample_rate_hz)` (`PI` is `core.f64.consts.PI`, Rust's binary64 constant for π, bits `0x400921FB54442D18`; multiplication first), `k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix `(m_hp, m_bp, m_lp)` `(0, 0, 1)`, `(1, 0, 0)`, `(0, k, 0)`, `(1, 0, 1)` and `(1, -k, 1)` respectively, each operation in binary64 in that order. `libm.tanModel_f64` is an unknown function standing for libm's `tan` (see below). That these are low-pass, high-pass, band-pass, notch and all-pass responses is not proved. |
| `svf::CoeffsF64::bell` | `svf.CoeffsF64.bell_eq` | `Svf/SpecF64.lean` | Never fails, and returns exactly the coefficients with `A = libm.powModel_f64 10 (gain_db / 40)`, `g` as above, `k = 1 / (q * A)`, `d = 1 / (1 + g * (g + k))` and the mix `(1, k * A * A, 1)`, each operation in binary64 in that order. That this is a bell (peak) response is not proved. |
| `svf::CoeffsF64::low_shelf`, `high_shelf` | `svf.CoeffsF64.low_shelf_eq`, `high_shelf_eq` | `Svf/SpecF64.lean` | Never fails, and returns exactly the coefficients with `A = libm.powModel_f64 10 (gain_db / 40)`, `g = libm.tanModel_f64 (PI * cutoff_hz / sample_rate_hz) / libm.sqrtModel_f64 A` (low shelf) or `… * libm.sqrtModel_f64 A` (high shelf), `k = 1 / q`, `d = 1 / (1 + g * (g + k))` and the mix `(1, k * A, A * A)` (low shelf) or `(A * A, k * A, 1)` (high shelf), each operation in binary64 in that order. That these are shelving responses is not proved. |
| `svf::CoeffsF32::low_pass` … `high_shelf` | `svf.CoeffsF32.low_pass_eq` … `high_shelf_eq` | `Svf/SpecF32.lean` | The same eight facts in binary32, with `core.f32.consts.PI` and the unknown functions `libm.tanModel_f32`, `libm.powModel_f32` and `libm.sqrtModel_f32` standing for libm's `tanf`, `powf` and `sqrtf`. |
| (the SVF, exact arithmetic) | `svf.svfStep_real_linear` | `Svf/Block.lean` | For any real `g`, `k`, `d` and mix, one step of `svf.svfStep_real` (the Rust step's operations, in the same order, in exact arithmetic) is linear: the new state is `A·s + b·x` and the output `cOut·s + dx·x`, with `A`, `b`, `cOut` and `dx` listed below the table. It does not use `d = 1/(1 + g·(g + k))`. |
| `svf::step_f64` | `svf.svfStep_f64_localErr` | `Svf/BlockF64.lean` | When the coefficients, state and input are finite and none of the step's sixteen intermediate results overflows (`StepFinite_f64`), with both state values at most `Sb` and the input at most `M` in size: the output is within `Ly` of the exact step's from the same state (`svf.svfStep_real`), and the distances of the two new state values from the exact step's add up to at most `Ls` (`Ly`, `Ls` listed below the table), all on the exact values of the stored floats. |
| `svf::process_f64` | `svf.process_f64_block_error` (and `filt_f64_block_error`, the same about `filt_f64`) | `Svf/BlockF64.lean` | **Whole-block error.** Given an `svf.Contraction` for the real values of the stored coefficients (`svf.realCoeffs_f64`), finite coefficients and starting state, no overflow (`NoOverflow_f64`), every input at most `M` in size with `M ≥ 0`, and a number `Sb ≥ 0` with `cInf·(R + Ê) ≤ Sb`: never fails; each output sample is within `outGain·cInf·Ê + Ly` of the corresponding output of `svf.filt_real` run on the real values of the stored inputs from the real value of the stored starting state (`svf.realState_f64`); each final state value is within `cInf·Ê` of the exact one; for a block of any length. `outGain`, `R`, `Ê` and `Ly` are listed below the table. |
| `svf::step_f64` | `svf.stepFinite_f64` | `Svf/BlockF64.lean` | When the coefficients, both state values and the input are finite, both state values are at most `Sb` and the input at most `M` in size, and `V` (listed below the table) is at most the largest finite binary64 value: none of the step's sixteen operations overflows (`StepFinite_f64`). |
| `svf::process_f64` | `svf.noOverflow_f64_of_inputs` | `Svf/BlockF64.lean` | Given an `svf.Contraction` for the real values of the stored coefficients, finite coefficients, any numbers `Sb`, `M`, `R`, `Ê` with `ρ·R + K·G·M ≤ R`, `ρ·Ê + K·Ls ≤ Ê`, `cInf·(R + Ê) ≤ Sb` and `V` at most the largest finite binary64 value, a starting state with both values finite, a real pair `r` with `N(r) ≤ R` and `N(S − r) ≤ Ê` where `S` is the starting state's real value, and every input finite and at most `M` in size: no step overflows (`NoOverflow_f64`). |
| `svf::process_f64` | `svf.process_f64_block_error_of_inputs` (and `filt_f64_block_error_of_inputs`) | `Svf/BlockF64.lean` | **Whole-block error, with conditions on the inputs only.** As `svf.process_f64_block_error`, but with every input finite and `V` at most the largest finite binary64 value (about 1.8 × 10³⁰⁸) in place of the no-overflow condition: no step overflows (`NoOverflow_f64`), and the conclusion of `svf.process_f64_block_error` holds. |
| `svf::step_f32`, `process_f32` | `svf.svfStep_f32_localErr`, `svf.process_f32_block_error` (and `filt_f32_block_error`), `svf.stepFinite_f32`, `svf.noOverflow_f32_of_inputs`, `svf.process_f32_block_error_of_inputs` (and `filt_f32_block_error_of_inputs`) | `Svf/BlockF32.lean` | The same five in binary32 (largest finite value about 3.4 × 10³⁸). |
| (the SVF and the biquad, exact arithmetic) | `svf.toBiquadCoords_update`, `svf.poleBiquad_a1`, `svf.poleBiquad_a2` | `Svf/Contraction.lean` | Let `a1 = −(A₁₁ + A₂₂)` and `a2 = A₁₁·A₂₂ − A₁₂·A₂₁` (`svf.poleBiquad`): `a1 = 4g²d + 2gdk − 2` and `a2 = 1 − 2gdk`. The change of coordinates `P(v₁, v₂) = (v₁, −A₂₂·v₁ + A₁₂·v₂)` takes the SVF's state-update map to the biquad's with these `a1`, `a2`: `P(A·v) = T(P·v)` for every pair `v`, with `T(w₁, w₂) = (−a1·w₁ + w₂, −a2·w₁)`. That the SVF has the transfer function of any biquad is not proved. |
| (SVF `Contraction`s from biquad ones) | `svf.ofBiquad` | `Svf/Contraction.lean` | When `A₁₂ = −2gd ≠ 0`: any biquad `Contraction` for `svf.poleBiquad` (for example `biquad.complexPolesContraction`, `realPolesContraction` or `repeatedPoleContraction`, under their conditions on `a1`, `a2`) gives an `svf.Contraction` with the measure `N(P·v)`, the same `ρ`, `cInf' = cInf·(1 + (1 + \|A₂₂\|)/\|A₁₂\|)` and `K' = K·(1 + \|A₂₂\| + \|A₁₂\|)`. The factor `1 + (1 + \|A₂₂\|)/\|A₁₂\|` grows like `1/(g·d)` as `g` shrinks, and the biquad's `cInf` grows too; with `biquad.complexPolesContraction`, `cInf'` grows like about `1/g²` (worked out outside Lean, not proved). |
| (the SVF with complex poles) | `svf.complexPolesContraction`, `svf.complexPoleNorm_update`, `svf.complexPolesContraction_bounds`, `svf.normCoeffs_a2_of_d` | `Svf/Contraction.lean` | An `svf.Contraction` when `d > 0`, `g·k > 0` and `k² < 4·(1/d − g·(g + k))`: it measures `(v₁, v₂)` by the length of `(p·v₁, v₂ + (k/2)·v₁)` with `p = √(1/d − g·(g + k) − k²/4)` (the biquad's `complexPoleNorm` for `a1 = −k`, `a2 = 1/d − g·(g + k)`); the state-update map multiplies every pair's measure by exactly `√(1 − 2gdk)`, and `ρ = √(1 − 2gdk)`, `cInf = (1 + \|k\|/2)/p + 1`, `K = p + \|k\|/2 + 1`. When `d·(1 + g·(g + k)) = 1`, `1/d − g·(g + k) = 1`, so `p² = 1 − k²/4`, whatever `g`. |

For the SVF design functions (`low_pass` to `high_shelf`), "never fails" holds given the libm model
in `Code/FunsExternal.lean`, which assumes that libm's functions never panic (see "What is
assumed, not proved").

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

For the SVF whole-block theorems (`Svf/Block.lean`, `Svf/BlockF64.lean`, `Svf/BlockF32.lean`),
every quantity below is computed from the real values of the stored `g`, `k`, `d` and mix
`(m_hp, m_bp, m_lp)` (`svf.realCoeffs_f64` / `_f32`), with `u` and `η` of the precision, `N`,
`ρ`, `cInf` and `K` from the given `svf.Contraction`, `S` the real value of the stored starting
state, and `Sb ≥ 0` a number chosen by whoever uses the theorem:

- `A = [[1 − 2gd(k + g), −2gd], [2g(1 − gd(k + g)), 1 − 2g²d]]` (`svf.a11` … `svf.a22`),
  `b = (2gd, 2g²d)` (`svf.bx1`, `svf.bx2`),
  `cOut = (−m_hp·d·(k + g) + (m_bp + m_lp·g)·(1 − gd(k + g)), −(m_hp + m_bp·g)·d + m_lp·(1 − g²d))`
  (`svf.cs1`, `svf.cs2`) and `dx = (m_hp + m_bp·g + m_lp·g²)·d` (`svf.dx`);
- `G = |2gd| + |2g²d|` (`svf.inputGain`) and `outGain = |cOut₁| + |cOut₂|` (`svf.outGain`);
- `Ly` and `Ls` (`stepErrOut_f64` / `_f32`, `stepErrState_f64` / `_f32`): bounds on one step's
  rounding error in the output, and in the new state (both values' errors added), when both state
  values are at most `Sb` and the input at most `M` (`svf.step_chain`). They are built in
  `Svf/Block.lean` from sixteen per-operation terms, one per rounding (`svf.opK1` … `svf.opT2` bound
  the operations' exact values, `svf.errK1` … `svf.errT2` the errors carried forward); `Ly = errY`
  and `Ls = errT1 + errT2`;
- `R = N(S) + K·G·M/(1 − ρ)` (`svf.exactStateBound`) and `Ê = K·Ls/(1 − ρ)`
  (`svf.stateErrBound`, `stateErrBound_f64` / `_f32`);
- the condition on `Sb`: `cInf·(R + Ê) ≤ Sb`. The biquad's `Sb` is a closed form; here any `Sb`
  with this property will do, and the worked examples below give one;
- `V = stepValueBound_f64` / `_f32`: the sum of the sixteen `opX`.

The `toReal` and error theorems are stated about the expression `x + a * y`; the `step_*_eq`
theorems are what tie that expression to the Rust functions. The whole-block theorems are stated
about `process_f64` / `process_f32` directly. Their real-number argument is in `OnePole/Block.lean`
(`block_error_real`), shared by both precisions; the biquad's is in `Biquad/Block.lean` and the
SVF's in `Svf/Block.lean`, both using the facts about a `Contraction` in `TwoState.lean`.

For the one-pole, the whole-block theorems compare the Rust outputs with the exact filter run on
the exact real values of the stored floats: `A` is the value of `a`, `S` of the starting `state`,
and the inputs are the values of the stored samples. (So turning a decimal coefficient into a float
is not covered: 0.99 is stored in f32 as 0.9900000095, worked out outside Lean, not proved.) The
biquad theorems likewise use the real values of the stored coefficients (`realCoeffs_f64`),
starting state (`realState_f64`) and inputs. The one-pole's conditions:

- `a`, the starting state and every input are finite, and no step overflows (`NoOverflow_f64` /
  `NoOverflow_f32`: every rounded product `a * state` and every output is finite). The
  `_of_inputs` theorems need no no-overflow condition: they prove it, given the other conditions
  here and that `M + (1 + u)·(B + E) + η` (with `B` and `E` below) is at most the largest finite
  value;
- every input is at most `M` in size;
- `|A| + |A|·u·(2 + u) < 1`, which is `|A|·(1 + u)² < 1`: stable, with a little room for
  rounding. Every real `A` with `|A| ≤ 1 - 2⁻⁵¹` satisfies it in f64
  (`stability_of_abs_le_f64`), and every real `A` with `|A| ≤ 1 - 2⁻²²` satisfies it in f32
  (`stability_of_abs_le_f32`), where `u` is `2⁻⁵³` in f64 and `2⁻²⁴` in f32
  (`unitRoundoff_f64_eq`, `unitRoundoff_f32_eq`).

Then, with `B = |S| + M / (1 - |A|)` (a bound on the exact filter's outputs):

`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`

### What the whole-block bound means in practice

For inputs at most `M = 1` in size and a starting state of value `S = 0`, the theorems below
prove, for every real `A` whose size is at most the bound in the third column: the stability
condition holds, and `B`, `E`, `E / B` and `20·log₁₀(E / B)` (`E` relative to `B`, in decibels)
are at most the values shown. Here `B` and `E` are `outBound A 1 0` and `errBound A u η 1 0`,
with `u` and `η` the precision's rounding constants. The values shown were chosen a little above
the values of the formulas at that bound (worked out outside Lean, not proved), so each proved
bound can be slightly weaker than the formula's value.

| Precision | `a` | Size of `A` at most | `B` | `E` | `E / B` | `E` relative to `B` | Theorem |
|---|---|---|---|---|---|---|---|
| f32 | 0.5 | 0.5 | ≤ 2 | ≤ 3.6 × 10⁻⁷ | ≤ 1.79 × 10⁻⁷ | ≤ −134.9 dB | `table_row_le_of_abs_le_05_f32` |
| f32 | 0.99 | 0.990001 | ≤ 100.02 | ≤ 1.19 × 10⁻³ | ≤ 1.187 × 10⁻⁵ | ≤ −98.5 dB | `table_row_le_of_abs_le_099_f32` |
| f32 | 0.999 | 0.999001 | ≤ 1001.01 | ≤ 0.12 | ≤ 1.193 × 10⁻⁴ | ≤ −78.4 dB | `table_row_le_of_abs_le_0999_f32` |
| f64 | 0.99 | 0.99 | ≤ 100 | ≤ 2.21 × 10⁻¹² | ≤ 2.21 × 10⁻¹⁴ | ≤ −273.1 dB | `table_row_le_of_abs_le_099_f64` |
| f64 | 0.999 | 0.999 | ≤ 1000 | ≤ 2.22 × 10⁻¹⁰ | ≤ 2.22 × 10⁻¹³ | ≤ −253.0 dB | `table_row_le_of_abs_le_0999_f64` |

Each bound in the third column covers the value the precision stores for `a`: f32 stores 0.5
exactly, 0.99 as 0.9900000095 and 0.999 as 0.9990000129, and f64 stores 0.99 as
0.98999999999999999112 and 0.999 as 0.99899999999999999911, just below the decimal values. These
stored values are worked out outside Lean, not proved. The theorems are about every real `A` within
the bound, so they hold whatever value is stored, as long as it is within the bound. The table
rests on `table_row_le_of_abs_le` in `OnePole/Block.lean`, which uses
`outBound_errBound_le_of_abs_le`: when `0 ≤ u`, `0 ≤ η`, `|A| ≤ a` and `a + a·u·(2 + u) < 1`, each
of `B`, `E` and `E / B` (with `M = 1`, `S = 0`) is at most its value at `|A| = a`.

How `E` grows as the size of `A` approaches 1: for inputs at most 1 and a start from 0, if
`1/2 ≤ |A| ≤ 1 - 2⁻²⁰` in f32 (`errBound_between_of_abs_le_f32`) or `1/2 ≤ |A| ≤ 1 - 2⁻⁴⁹` in f64
(`errBound_between_of_abs_le_f64`), then `u / (1 - |A|)² ≤ E ≤ 3·u / (1 - |A|)²`, where `u` is
`2⁻²⁴` in f32 and `2⁻⁵³` in f64 (`unitRoundoff_f32_eq`, `unitRoundoff_f64_eq`). So, within a factor
of 3, `E` grows like `1 / (1 - |A|)²`. Both rest on `errBound_between_of_abs_le` in
`OnePole/Block.lean`.

The size limit of the one-pole `process_f32_block_error_of_inputs` is proved to hold for slow
smoothers in f32 (the third row of the table above): for every
real `A` with `|A| ≤ 0.999001`, inputs at most `M = 1` in size and a starting state of value
`S = 0`, the stability condition holds, `B ≤ 1001.01`, `E ≤ 0.12`, and `M + (1 + u)·(B + E) + η`
is at most the largest finite binary32 value (`block_constants_le_of_abs_le_f32`). That value is
exactly `(2²⁴ - 1)·2¹⁰⁴` (`maxFinite_f32_eq`), and in f32 `u = 2⁻²⁴` and `η = 2⁻¹⁵⁰`
(`unitRoundoff_f32_eq`, `underflowErr_f32_eq`).

For the biquad, the theorems below take an RBJ-cookbook Butterworth low-pass (`Q = 0.7071`) at
48 kHz, with `M = 1` (inputs at most 1 in size) and a start from zero, for stored coefficients
whose real values are exact numbers given in `Biquad/BlockF64.lean` and `Biquad/BlockF32.lean`
(`lowPass100Hz_f64`, `lowPass100Hz_f32` and so on, each with its bits). That these are the
cookbook formulas' coefficients (computed in binary64 and, for f32, each rounded to binary32) is
worked out outside Lean, not proved: the formulas use `cos` and `sin`, which are outside the
model.

For each row the theorem proves:

- the coefficients have complex poles inside the unit circle;
- with `complexPolesContraction`, the condition `cInf·K·κ·β < 1 − ρ` of the whole-block theorems
  holds;
- `cInf·Ê + L` (the bound on each output's error) and its value in decibels relative to 1.0 (only
  where it is below 1.0), `Sb = computedStateBound_f32` / `_f64` and
  `V = stepValueBound_f32` / `_f64` (the cap of the whole-block `_of_inputs` theorems) are at most
  the values shown;
- `V·10³⁵ ≤` the largest finite value, which is exactly `(2²⁴ − 1)·2¹⁰⁴` in f32 and
  `(2⁵³ − 1)·2⁹⁷¹` in f64 (`maxFinite_f32_eq`, `maxFinite_f64_eq`);
- for f32 at 100 Hz, also `cInf·Ê + L ≥ 17`, so above 1.0 (no dB value is shown).

| Precision | Cutoff | `cInf·Ê + L` | In dB | `Sb` | `V` | Theorem |
|---|---|---|---|---|---|---|
| f32 | 100 Hz | ≤ 17.1 (and ≥ 17) | (above 1.0) | ≤ 25.1 | ≤ 619 | `lowPass100Hz_bounds_f32` |
| f32 | 1 kHz | ≤ 0.0542 | ≤ −25.3 dB | ≤ 8.35 | ≤ 186 | `lowPass1kHz_bounds_f32` |
| f32 | 10 kHz | ≤ 1.81 × 10⁻⁴ | ≤ −74.8 dB | ≤ 7.28 | ≤ 41.4 | `lowPass10kHz_bounds_f32` |
| f64 | 100 Hz | ≤ 1.02 × 10⁻⁸ | ≤ −159.8 dB | ≤ 8.04 | ≤ 199 | `lowPass100Hz_bounds_f64` |
| f64 | 1 kHz | ≤ 1.01 × 10⁻¹⁰ | ≤ −199.9 dB | ≤ 8.29 | ≤ 185 | `lowPass1kHz_bounds_f64` |
| f64 | 10 kHz | ≤ 3.37 × 10⁻¹³ | ≤ −249.4 dB | ≤ 7.28 | ≤ 41.4 | `lowPass10kHz_bounds_f64` |

The values shown were chosen a little above the values of the formulas (a little below, for the
lower bounds; worked out outside Lean, not proved), so each proved bound can be slightly weaker
than the formula's value. `ω` and `ρ = √a2` are not rational: each theorem bounds them by
rational numbers whose squares are on either side of `a2 − a1²/4` and `a2`
(`complexPolesContraction_bounds`). `block_bounds_le` and
`block_bounds_ge` in `Biquad/Block.lean` turn bounds on `cInf`, `K` and `ρ` into bounds on `Sb`
and `cInf·Ê + L` (`stateBoundAt`, `outErrBoundAt`); `block_bounds_of_rat_f64` / `_f32` apply them
to the whole-block constants, and what is left is arithmetic on rational numbers, which `norm_num`
checks.

For the same filter, `M = 1` and start, the theorems below state facts at single cutoffs; the
last two items (three theorems) are about RBJ low-pass filters with `Q = 0.4` and `Q = 0.5` at
1 kHz instead, whose poles are real. Each one that bounds `cInf·Ê + L` also proves that the
coefficients have poles inside the unit circle (complex, or real where that is said) and that the
condition `cInf·K·κ·β < 1 − ρ` holds for the `Contraction` it uses.

- In f32 at 82 Hz the condition `cInf·K·κ·β < 1 − ρ` is false for `complexPolesContraction`
  (`lowPass82Hz_smallness_fails_f32`), so the whole-block theorems used with it prove nothing
  there; at 83 Hz it holds and `cInf·Ê + L ≤ 606` (`lowPass83Hz_bound_f32`).
- In f32 the bound `cInf·Ê + L` is at least 1.07 at 240 Hz (`lowPass240Hz_bound_f32`), at most
  0.979 at 250 Hz (`lowPass250Hz_bound_f32`), and at least 1.13 at 23 kHz
  (`lowPass23kHz_bound_f32`).
- In f32 the bound is at most 0.0346 and at most −29.2 dB at 21 kHz (`lowPass21kHz_bound_f32`),
  and at least 0.0127, at most 0.0128 and at most −37.8 dB at 20 kHz (`lowPass20kHz_bound_f32`).
  So it is not monotonic in the cutoff: at least 17 at 100 Hz, at most 1.81 × 10⁻⁴ at 10 kHz, at
  least 0.0127 at 20 kHz.
- In f64 the bound is at most 1.02 × 10⁻⁴ and at most −79.8 dB at 1 Hz
  (`lowPass1Hz_bound_f64`), at most 1.02 × 10⁻⁶ and at most −119.8 dB at 10 Hz
  (`lowPass10Hz_bound_f64`), and at most 2.73 × 10⁻⁷ and at most −131.2 dB at 23.8 kHz
  (`lowPass23800Hz_bound_f64`).
- In f32 at 1 Hz the stored coefficients have real poles (`a1² < 4·a2` fails,
  `lowPass1Hz_real_poles_f32`), and one of them is exactly 1 (`1 + a1 + a2 = 0`), so no
  `Contraction` exists for them and the whole-block theorems prove nothing there
  (`lowPass1Hz_pole_one_f32`).
- For an RBJ low-pass with `Q = 0.4` at 1 kHz (coefficients `lowPass1kHzQ04_f32` and
  `lowPass1kHzQ04_f64`; that they are the cookbook formulas' coefficients with `Q = 0.4` is worked
  out outside Lean, not proved), the stored poles are real, distinct and inside the unit circle,
  and with `realPolesContraction`: in f32 `cInf·Ê + L` is at most 0.00559 and at most −45 dB,
  `Sb ≤ 2.75` and `V ≤ 56.3` (`lowPass1kHzQ04_bounds_f32`); in f64 it is at most 1.04 × 10⁻¹¹
  and at most −219.6 dB, `Sb ≤ 2.75` and `V ≤ 56.2` (`lowPass1kHzQ04_bounds_f64`).
- For an RBJ low-pass with `Q = 0.5` at 1 kHz in f32 (coefficients `lowPass1kHzQ05_f32`, worked
  out outside Lean in the same way; in exact arithmetic this filter's two poles are equal, also
  worked out outside Lean, not proved), the stored poles are real and distinct but close:
  `a1² − 4·a2` is below 1.3 × 10⁻⁷, so `cInf = 1/d` is above 2700. With `realPolesContraction`
  the condition holds, but `cInf·Ê + L` is only shown to be at most 734
  (`lowPass1kHzQ05_bound_f32`).

Nothing is proved for a whole range of cutoffs, which would need `cos` and `sin`. Worked out
outside Lean, not proved: in f32 the condition fails at every cutoff below about 82.4 Hz where the
stored poles are complex (below about 3 Hz they are real at some cutoffs, as at 1 Hz), the bound
is above 1.0 below about 247.6 Hz and above about 22.96 kHz, and below −25 dB only from
about 982 Hz to about 21.4 kHz; in f64 the bound is below −120 dB from about 10.08 Hz to about
23.87 kHz.

These bounds are much larger than the one-pole's. Part of that is real: at low cutoffs the poles
sit near the real axis, and the filter's own worst-case error gain is large (about 1.3 × 10⁴ at
100 Hz). Part is slack in the proof: the state bound `Sb` used for the per-step rounding is about
7–23× the true largest state (at 100 Hz, 1 kHz and 10 kHz), the per-step bound is crude, and the
contraction step adds a factor of about 4. The figures in this paragraph are worked out outside
Lean, not proved: the true worst-case error gain and the true largest state are sums over the
filter's whole impulse response, which no theorem here bounds.

Where the condition `cInf·K·κ·β < 1 − ρ` fails, as in f32 at 82 Hz, the biquad whole-block
`_of_inputs` theorems (`filt_*_block_error_of_inputs`, `process_*_block_error_of_inputs`) prove
nothing, as for the other whole-block theorems. The hypotheses of `noOverflow_f32_of_inputs`
cannot all hold there either: its `ρ·Ê + K·κ·(α + β·Sb) ≤ Ê`, `cInf·(R + Ê) ≤ Sb`, `N(r) ≤ R` and
`N(S − r) ≤ Ê` together imply that condition when `α > 0` and `cInf·K·κ > 0`
(`biquad.smallness_of_invariant`). Both of these always hold here: `α = localErrBase_f32` is
positive (for `M ≥ 0`) because `η > 0` (`localErrBase_pos`), and `cInf·K·κ > 0` for every
`complexPolesContraction` (`complexPolesContraction_cInf_K_roundGain_pos`).

For the SVF, the theorems below take `CoeffsF64::low_pass` and `CoeffsF32::low_pass` with
`Q = 0.7071` at 48 kHz (so `k` is `1/0.7071` rounded to the precision, and the mix is `(0, 0, 1)`),
with `M = 1` (inputs at most 1 in size) and a start from zero, for stored coefficients whose real
values are exact numbers given in `Svf/BlockF64.lean` and `Svf/BlockF32.lean`
(`svf.lowPass20Hz_f64`, `svf.lowPass20Hz_f32` and so on, each with its bits). That these are the
values the Rust design functions store is worked out outside Lean, not proved: they come from
running them, and `g` comes from libm's `tan` (`tanf` in f32), which is outside the model.

For each row the theorem proves, with `svf.complexPolesContraction` and the `Sb` shown:

- the stored coefficients meet its conditions (`d > 0`, `g·k > 0`, `k² < 4·(1/d − g·(g + k))`);
- the condition `cInf·(R + Ê) ≤ Sb` of the whole-block theorems holds;
- `outGain·cInf·Ê + Ly` (the bound on each output's error), its value in decibels relative to
  1.0, and `V = stepValueBound_f32` / `_f64` (the cap of the whole-block `_of_inputs` theorems)
  are at most the values shown;
- `V·10³⁵ ≤` the largest finite value.

| Precision | Cutoff | `outGain·cInf·Ê + Ly` | In dB | `Sb` (chosen) | `V` | Theorem |
|---|---|---|---|---|---|---|
| f32 | 20 Hz | ≤ 0.0126 | ≤ −37.9 dB | 11.68 | ≤ 165 | `svf.lowPass20Hz_bounds_f32` |
| f32 | 100 Hz | ≤ 0.00267 | ≤ −51.4 dB | 11.69 | ≤ 166 | `svf.lowPass100Hz_bounds_f32` |
| f32 | 1 kHz | ≤ 0.000459 | ≤ −66.7 dB | 11.88 | ≤ 180 | `svf.lowPass1kHz_bounds_f32` |
| f32 | 10 kHz | ≤ 0.000475 | ≤ −66.4 dB | 14.78 | ≤ 409 | `svf.lowPass10kHz_bounds_f32` |
| f64 | 20 Hz | ≤ 2.35 × 10⁻¹¹ | ≤ −212.5 dB | 11.67 | ≤ 165 | `svf.lowPass20Hz_bounds_f64` |
| f64 | 100 Hz | ≤ 4.98 × 10⁻¹² | ≤ −226.0 dB | 11.69 | ≤ 166 | `svf.lowPass100Hz_bounds_f64` |
| f64 | 1 kHz | ≤ 8.55 × 10⁻¹³ | ≤ −241.3 dB | 11.88 | ≤ 180 | `svf.lowPass1kHz_bounds_f64` |
| f64 | 10 kHz | ≤ 8.84 × 10⁻¹³ | ≤ −241.0 dB | 14.78 | ≤ 409 | `svf.lowPass10kHz_bounds_f64` |

The values shown were chosen a little above the values of the formulas (worked out outside Lean,
not proved), so each proved bound can be slightly weaker than the formula's value. `p` and
`ρ = √(1 − 2gdk)` are not rational: each theorem bounds them by rational numbers whose squares
are on either side of `p²` and `1 − 2gdk` (`svf.complexPolesContraction_bounds`), and
`svf.block_bounds_le` and `svf.block_bounds_of_rat_f64` / `_f32` leave arithmetic on rational
numbers, which `norm_num` checks.

The biquad table above has rows at 100 Hz, 1 kHz and 10 kHz for an RBJ-cookbook low-pass with the
same `Q` and sample rate. The SVF's numbers are smaller at 100 Hz and 1 kHz and larger at 10 kHz, in
both precisions (in f32 at 1 kHz, at most 0.000459 against at most 0.0542). These are upper bounds
on each proof's bound, so only in f32 at 100 Hz, where the biquad's bound is also proved to be at
least 17, is the SVF's bound itself proved smaller. Nothing here compares the filters' actual
errors, or proves that they have the same frequency response. One reason for the difference: with
`svf.complexPolesContraction`, `cInf` and `K` are about 3.41 and 2.41 at every cutoff, while the
biquad's `cInf` grows like `1/ω` as the cutoff falls (worked out outside Lean, not proved). There is
no biquad row at 20 Hz (see "Observations").

## Observations (not proofs)

What is listed here is observed or expected behaviour, not proved.

- The whole-block bounds are worst cases. Typical rounding errors partly cancel, and are much
  smaller than the one-pole's `E`, the biquad's `cInf·Ê + L` and the SVF's
  `outGain·cInf·Ê + Ly`.
- At low cutoffs in f32 the SVF's whole-block theorem gives a bound where the biquad's, used with
  `biquad.complexPolesContraction`, gives none. At 20 Hz the SVF's bound is at most 0.0126
  (`svf.lowPass20Hz_bounds_f32`, proved), while for the RBJ-cookbook biquad the condition
  `cInf·K·κ·β < 1 − ρ` fails at every cutoff below about 82.4 Hz where the stored poles are complex
  (worked out outside Lean, not proved; it is proved to fail at 82 Hz,
  `biquad.lowPass82Hz_smallness_fails_f32`). That the SVF's actual errors are smaller than the
  biquad's at low cutoffs is expected, not proved.
- For RBJ-cookbook low-pass and high-pass biquads (which have the same poles), binary32
  coefficients can put a pole on or outside the unit circle at very low cutoffs (computed in
  Python, not proved; `Q` = 0.5, 0.7071, 2 and 10, cutoffs in 0.01 Hz steps up to 200 Hz and
  1 Hz steps up to half the sample rate, testing `a2 < 1` and `|a1| < 1 + a2`). With the
  coefficients computed in binary64 and then rounded to binary32, this happens at some cutoffs
  below about 2.1 Hz at 44.1 kHz, 2.2 Hz at 48 kHz and 4.4 Hz at 96 kHz. With them computed in
  binary32 throughout, it happens at some cutoffs up to about 2.8 Hz at 44.1 kHz, 3 Hz at 48 kHz and 6 Hz at
  96 kHz, the worst case being `Q = 0.5`. It also happens at some cutoffs within 6 Hz of half the
  sample rate. One case is proved: the f32 1 Hz Butterworth low-pass at 48 kHz has a pole at
  exactly 1 (`lowPass1Hz_pole_one_f32`).

## What is assumed, not proved

- Charon and Aeneas translate the Rust code into Lean faithfully.
- Aeneas's float model (from the pinned `conjure` commit) has a single NaN: any operation that
  produces a NaN drops its sign and payload. So anything that reads a NaN's sign or bit pattern
  (`to_bits`, `is_sign_*`, `copysign`, `recip`, casts, and `from_bits` of a NaN bit pattern) can
  differ from compiled Rust. `min`/`max` of +0 and −0 may return either; Rust leaves this open
  too, and the model does not let a proof depend on which. No proof here relies on NaN bit
  patterns, NaN signs, or which zero `min`/`max` returns.
- Not modelled: `sin`, `exp` and other transcendental functions from Rust's standard library,
  and the `NAN` constant. This crate uses none of them.
- The crate's one dependency, `libm` 0.2.16 (a pure-Rust port of the musl and FreeBSD maths
  libraries, pinned exactly, default features off), is not translated. Its `tan`, `pow` and
  `sqrt` (and the binary32 `tanf`, `powf` and `sqrtf`) are modelled in the hand-written
  `Code/FunsExternal.lean` as unknown functions that always return a float and return the same
  float for the same arguments: `libm.tanModel_f64` and the others are Lean `opaque` constants,
  which no proof can look inside (they are not axioms). So the proofs assume that these functions
  never panic, always return, and return the same float for the same arguments; their accuracy, and
  even which float they return, are taken on trust. Nothing about the frequency responses of the
  coefficients the SVF design functions compute is proved.
- Rust's `f32`/`f64` operations and Lean's `Float32`/`Float` operations are the same IEEE 754
  round-to-nearest operations. FloatLib relates Lean's floats to real numbers; nothing here
  verifies machine instructions or compiler optimizations. In particular, the proofs assume a
  separate multiply and add: Rust does not fuse `x + a * y` (or the smoother's
  `state + c * (x - state)`, or the biquad's `b0 * x + s1` and `b1 * x - a1 * y + s2`, or the
  SVF's `x - (k + g) * s1`, `1 + g * (g + k)`, `g * hp + s1`, `g * bp + s2`, `g * hp + bp`,
  `g * bp + lp` and its output mix) into one multiply-add instruction unless the code asks for
  `mul_add`, and this code does not.
- No floating-point error bound is proved for the smoother (`smoother::*`), and in floating
  point it need not land exactly on its input. The theorems in `Smoother/Exact.lean` are in
  exact arithmetic only.
- For the state-variable filter (`svf::*`), the floating-point error bound is proved, under the
  conditions in the table above, for any stored coefficients for which an `svf.Contraction` of the
  state-update map is given (`svf.process_f64_block_error`, `svf.process_f32_block_error` and their
  `_of_inputs` forms), provided a number `Sb` with `cInf·(R + Ê) ≤ Sb` exists. One is supplied for
  complex poles (`svf.complexPolesContraction`: `d > 0`, `g·k > 0` and `k² < 4·(1/d − g·(g + k))`),
  and any biquad `Contraction` of `svf.poleBiquad` gives one (`svf.ofBiquad`, when `g·d ≠ 0`), whose
  `cInf` is the biquad's `cInf` times `1 + (1 + |A₂₂|)/|A₁₂|`, a factor that grows like `1/(g·d)`
  as `g` shrinks (the growth worked out outside Lean, not proved). Worked examples are proved only for the low-pass values in
  the SVF table above, whose stored coefficients are worked out outside Lean, not proved.
- Not proved for the state-variable filter: its frequency response, or that it equals any biquad's;
  stability for all coefficients, including that the coefficients the design functions compute meet
  the conditions above at every cutoff (they depend on libm's `tan`, outside the model); and that
  the code matches Zavalishin's filter. Nor, for the design functions (`low_pass` to `high_shelf`),
  whose names and formulas follow A. Simper (Cytomic), that the coefficients give the named
  responses.
- The biquad's whole-block error bound is proved for any given `Contraction` of its state-update
  map. One is supplied for complex poles inside the unit circle (`complexPolesContraction`), for
  distinct real poles inside it (`realPolesContraction`, for example an RBJ low-pass with
  `Q < 1/2`, worked out outside Lean, not proved) and for a repeated real pole inside it
  (`repeatedPoleContraction`). None is supplied when a pole is on or outside the unit circle, and
  when 1 is a pole none exists (`isEmpty_contraction_of_pole_one`; the f32 1 Hz Butterworth
  low-pass at 48 kHz has one, `lowPass1Hz_pole_one_f32`).
- Real poles that are distinct but close together have a large `cInf = 1/(p − q)` in
  `realPolesContraction` (above 2700 for an RBJ low-pass with `Q = 1/2` in f32 at 1 kHz,
  `lowPass1kHzQ05_bound_f32`). `repeatedPoleContraction` needs exactly equal poles, and no
  measure whose `cInf` stays bounded as the poles merge is supplied.
- The biquad's whole-block bound also assumes `cInf·K·κ·β < 1 - ρ` (false in f32 for a 48 kHz
  Butterworth low-pass at 82 Hz, `lowPass82Hz_smallness_fails_f32`).
  `process_f64_block_error` / `process_f32_block_error` also assume that no step overflows
  (`NoOverflow_f64` / `NoOverflow_f32`), a condition on the computed values; the whole-block
  `_of_inputs` theorems instead assume that every input is finite and that `V` is at most the
  largest finite value, and prove that no step overflows (through `noOverflow_f64_of_inputs` /
  `_f32`, which assumes the proof's invariant bounds instead). The textbook equivalence is in
  exact arithmetic: in floating point the transposed form and the textbook form round
  differently.

## Layout

- `Code/` is generated by Aeneas from the whole crate (`Types.lean`, `Funs.lean`). Never edit
  those by hand. The exception is `Code/FunsExternal.lean`, written by hand: the models of the
  external `libm` functions the crate calls, which `Funs.lean` imports. Aeneas writes a template
  for it declaring those functions as axioms; `scripts/prove.sh` moves the template to
  `target/FunsExternal_Template.lean`, outside the Lean library.
- One file per Rust module while it has one proof file (`Gain.lean`); a folder once it has more
  (`OnePole/`). Inside a folder: `SpecF64.lean`/`SpecF32.lean` say what the translated code
  computes; `BridgeF64.lean`/`BridgeF32.lean` relate one step to real numbers; `Block.lean` holds
  the whole-block argument on real numbers only, shared by both precisions, and
  `BlockF64.lean`/`BlockF32.lean` apply it to the Rust functions; `Exact.lean` (real numbers
  only, `Smoother/`) proves what the filter does in exact arithmetic; `Textbook.lean` (real
  numbers only) shows the code's form of a filter equals the textbook formula;
  `Contraction.lean` (real numbers only) builds a `Contraction` for biquads with complex poles,
  distinct real poles or a repeated real pole inside the unit circle (`Biquad/`), or for the SVF
  with complex poles or from a biquad one (`Svf/`); `Basic.lean` (`Delay/`)
  holds facts about lists, natural numbers and Aeneas's `Result` that both precisions' files use.
- Names: Lean names about one precision end in `_f64` or `_f32`, like the Rust names
  (`filt_f64`, `real_f32`, `NoOverflow_f64`), and the filter functions keep the `filt_` prefix
  (`filt_real`). Otherwise Lean names follow Mathlib: definitions that are statements start with
  a capital (`WithinStepErr`), other definitions are lowerCamelCase (`stepErr`), and theorems are
  snake case, keeping the casing of any definition they mention, except that a capitalized one
  starts lowercase (`filt_f64_withinStepErr`, `noOverflow_f64_of_inputs`).
- `FloatFacts.lean` holds facts about floats shared by every module's proofs, including
  `real_f64` / `real_f32` (the exact real value of a float).
- `TwoState.lean` (real numbers only) holds what the biquad's and the SVF's whole-block arguments
  share: `two_state.Contraction`, the `Contraction` structure for a filter with two state values
  and any 2 × 2 state-update matrix (`biquad.Contraction` is it at the companion matrix
  `(−a1, 1; −a2, 0)`, `svf.Contraction` at the SVF's `A`), and the facts about it that both
  use.
