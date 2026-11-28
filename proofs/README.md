# What is proved

Lean proofs about the Rust code in `src/`, checked by `scripts/prove.sh`. Every theorem below
depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`; none uses
`sorry`. Every module is also replayed through Lean's kernel with `leanchecker`. Lean names are in
the namespace `conjure_dsp_lib`.

"Never fails" means the translated function always returns normally: no panic, no out-of-bounds
index, no arithmetic overflow on indices, and it terminates.

| Rust function | Theorem | File | Says |
|---|---|---|---|
| `gain::apply_f64`, `apply_f32` | `gain.apply_f64_eq`, `gain.apply_f32_eq` | `Gain/SpecF64.lean`, `Gain/SpecF32.lean` | Exactly `gain * x` (Lean's `Float.mul` / `Float32.mul`); never fails. |
| `gain::ramp_f64` | `gain.ramp_f64_spec` | `Gain/SpecF64.lean` | Never fails, and the output samples are exactly `rampList_f64 start end` of the input samples: with `n` the block's length, sample `i` (`x`) becomes `x * (start + ((end - start) / castNat_f64 n) * castNat_f64 i)` (`rampGain_f64`), each operation in binary64 (Lean's `Float`) in that order. For an empty block, `rampList_f64` is the empty list. |
| (`i as f64` for a `usize` `i`) | `gain.usize_toFloat_eq_castNat_f64` (`Gain/SpecF64.lean`), `gain.real_castNat_f64_eq_roundAt`, `gain.real_castNat_f64`, `gain.isFinite_castNat_f64` | `Gain/BridgeF64.lean` | Aeneas's translation of the cast, `UScalar.toFloat i`, equals `castNat_f64` of the value of `i`: Lean's own conversion of that natural number to binary64 (`Float.Model.ofNat`). For every `k ≤ 2^64` (every `usize`), `castNat_f64 k` is finite and its real value is `k` rounded to the nearest binary64 number, ties to even (FloatLib's `roundAt`); for `k ≤ 2^53` that is exactly `k`. |
| `gain::ramp_f64` | `gain.rampGain_f64_not_finite` | `Gain/BridgeF64.lean` | If `start` or `end` is not finite, or `end - start` is not finite (it overflowed), `rampGain_f64 start end n i` is infinite or NaN, for every `n` and every `i`, `i = 0` included. |
| `gain::ramp_f64` | `gain.rampGain_f64_zero`, `gain.rampGain_f64_zero_negZero` | `Gain/BridgeF64.lean` | When `end - start` is finite (so `start` and `end` are finite and the difference did not overflow) and `1 ≤ n < 2^64`: the first gain `rampGain_f64 start end n 0` equals `start` as a Lean `Float` (bit for bit), unless `start` is `-0` (bits `0x8000000000000000`); then the first gain is `+0` or `-0`. |
| `gain::ramp_f64` | `gain.rampGain_f64_error`; `gain.ramp_line_zero`, `gain.ramp_line_last`, `gain.ramp_line_end` (`Gain/Line.lean`) | `Gain/BridgeF64.lean` | **Accuracy.** When `start` and `end` are finite and at most `2^1020` in size, `1 ≤ n ≤ 2^53` and `i < n`: the gain of sample `i` is finite, and its real value is within `u·\|S\| + 5u·\|E - S\| + (2n + 4)·η` of the straight line `S + (E - S)·i/n`, where `S`, `E` are the real values of `start`, `end`, `u = 2⁻⁵³` and `η = 2⁻¹⁰⁷⁵`. That line is `S` at `i = 0`, and for `n ≥ 1` it is `E - (E - S)/n` at `i = n - 1` and `E` at `i = n`. |
| `gain::ramp_f64` | `gain.rampStep_f64_error`, `gain.rampGain_f64_last_error`, `gain.rampGain_f64_succ_sub`, `gain.rampGain_f64_next_block`, `gain.rampGain_f64_zero` | `Gain/BridgeF64.lean` | **Steps.** Under the same conditions: the step `rampStep_f64 start end n` (`(end - start) / castNat_f64 n`) has a real value `s` within `3u·\|E - S\| + 3η` of `(E - S)/n`; the last gain (`i = n - 1`) is within `u·\|S\| + 8u·\|E - S\| + (2n + 7)·η` of `E - s`; and for `i + 1 < n`, gain `i + 1` minus gain `i` is within `2u·\|S\| + 13u·\|E - S\| + (4n + 11)·η` of `s`. A following block from `end` to any `end₂`, of any length `1 ≤ m < 2^64`, starts at exactly `end` when `end₂ - end` is finite and `end` is not `-0` (`rampGain_f64_zero` applied to that block, with no condition on this block); with this block under the accuracy conditions as well, `end` minus this block's last gain is within `u·\|S\| + 8u·\|E - S\| + (2n + 7)·η` of `s` (`rampGain_f64_next_block`). |
| `gain::ramp_f64` | `gain.rampGain_f64_mono` | `Gain/BridgeF64.lean` | **Direction.** For `n ≤ 2^64`, `i ≤ j ≤ 2^64`, and gains `i` and `j` both finite: if `S ≤ E`, the real value of gain `i` is at most that of gain `j`; if `E ≤ S`, the real value of gain `j` is at most that of gain `i`. |
| `gain::ramp_f32` | `gain.ramp_f32_spec`, `gain.usize_toFloat32_eq_castNat_f32` | `Gain/SpecF32.lean` | The same two facts in binary32 (`rampList_f32`, `rampGain_f32`, `castNat_f32`, Lean's `Float32`). |
| `gain::ramp_f32` | the `_f32` versions of the gain theorems above (`gain.real_castNat_f32_eq_roundAt`, `gain.real_castNat_f32`, `gain.isFinite_castNat_f32`, `gain.rampGain_f32_not_finite`, `gain.rampGain_f32_zero`, `gain.rampGain_f32_zero_negZero`, `gain.rampGain_f32_error`, `gain.rampStep_f32_error`, `gain.rampGain_f32_last_error`, `gain.rampGain_f32_succ_sub`, `gain.rampGain_f32_next_block`, `gain.rampGain_f32_mono`) | `Gain/BridgeF32.lean` | The same facts in binary32, with `2^24` in place of `2^53` (exact conversion, and the largest `n` of the accuracy bounds), `2^124` in place of `2^1020`, `u = 2⁻²⁴`, `η = 2⁻¹⁵⁰`, and `-0` having bits `0x80000000`. |
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
| (the one-pole, exact arithmetic) | `one_pole.filt_real_abs_le_outBound` | `OnePole/Exact.lean` | **Stability.** In exact arithmetic, when `\|A\| < 1`: from state `S`, with every input at most `M ≥ 0` in size, every output of `one_pole.filt_real` and its final state are at most `one_pole.outBound A M S = \|S\| + M/(1 - \|A\|)` in size, for a block of any length. |
| (the one-pole, exact arithmetic) | `one_pole.filt_real_replicate` | `OnePole/Exact.lean` | In exact arithmetic, when `A ≠ 1`, for any starting state `r`, input `X` and number of samples `n`: the input `X` held for `n` samples gives the outputs `X/(1 - A) + A^(k+1)·(r - X/(1 - A))` for `k = 0, …, n - 1` and the final state `X/(1 - A) + A^n·(r - X/(1 - A))`. |
| (the one-pole, exact arithmetic) | `one_pole.tendsto_filt_real_replicate` | `OnePole/Exact.lean` | In exact arithmetic, when `\|A\| < 1`: for any starting state `r` and input `X`, the final state after `X` is held for `n` samples tends to `X/(1 - A)` as `n` grows. |
| `smoother::step_f64` | `smoother.step_f64_eq` | `Smoother/SpecF64.lean` | Exactly `state + (1 - a) * (target - state)` in binary64, in that order (`1` is the binary64 number 1); never fails. |
| `smoother::process_f64` | `smoother.process_f64_spec` | `Smoother/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `state + c * (x - state)` in binary64 to each sample in turn, with `c = 1 - a` computed once in binary64 before the first sample (Lean's `smoother.filt_f64 (1 - a)`). |
| `smoother::step_f32`, `process_f32` | `smoother.step_f32_eq`, `smoother.process_f32_spec` | `Smoother/SpecF32.lean` | The same two facts in binary32 (Lean's `smoother.filt_f32`). |
| (the smoother, exact arithmetic) | `smoother.filt_real_eq_one_pole_filt_real` | `Smoother/Exact.lean` | In exact arithmetic, for any `A`, starting state `r` and list of inputs: the smoother `y = y_prev + (1 - A)·(x - y_prev)` (`smoother.filt_real`) gives exactly the same outputs and final state as the one-pole `y = x' + A·y_prev` (`one_pole.filt_real`) run from the same state on the inputs `x' = (1 - A)·x`. |
| (the smoother, exact arithmetic) | `smoother.filt_real_replicate` | `Smoother/Exact.lean` | In exact arithmetic, for any `A`, starting state `r`, input `X` and number of samples `n`: the input `X` held for `n` samples gives the outputs `X + A^(k+1)·(r - X)` for `k = 0, …, n - 1` and the final state `X + A^n·(r - X)`. |
| (the smoother, exact arithmetic) | `smoother.tendsto_filt_real_replicate` | `Smoother/Exact.lean` | In exact arithmetic, when `\|A\| < 1`: for any starting state `r` and input `X`, the final state after `X` is held for `n` samples tends to `X` as `n` grows. |
| (the smoother, exact arithmetic) | `smoother.replicate_output_between`, `smoother.replicate_output_closer`, `smoother.replicate_output_alternates` | `Smoother/Exact.lean` | In exact arithmetic, for the outputs `X + A^(k+1)·(r - X)` of a steady input `X` from state `r` (`smoother.filt_real_replicate`): when `0 ≤ A ≤ 1`, each output lies between `X` and `r`, and output `k + 1` is no farther from `X` than output `k`; when `A < 0` and `r ≠ X`, outputs `k` and `k + 1` are on opposite sides of `X` (the product of their differences from `X` is negative). |
| (the smoother, exact arithmetic) | `smoother.filt_real_abs_le` (and `smoother.filt_real_abs_le_outBound` in `Smoother/Block.lean`, the same stated with `smoother.outBound`) | `Smoother/Exact.lean` | **Stability.** In exact arithmetic, when `\|A\| < 1`: from state `S`, with every input at most `M ≥ 0` in size, every output of `smoother.filt_real` and its final state are at most `\|S\| + \|1 - A\|·M/(1 - \|A\|)` in size (`smoother.outBound A M S`), for a block of any length. |
| `smoother::process_f64` | `smoother.coeff_f64_error`, `smoother.coeff_f64_exact` | `Smoother/BridgeF64.lean` | The coefficient `c = 1 - a`, computed once per block in binary64: when `a` and `1 - a` are finite, the value of `c` is within `u·\|1 - a\| + η` of `1 - a` (here `a` stands for its value); when the value of `a` is between 1/2 and 2, `c` is exactly `1 - a` (Sterbenz's lemma). |
| `smoother::step_f64` | `smoother.step_f64_error` | `Smoother/BridgeF64.lean` | When `c`, `state`, `x`, the rounded difference `x - state`, the rounded product `c * (x - state)` and the result are all finite (no overflow): one step `state + c * (x - state)`, with its three roundings (the difference, the product and the sum), is within `stepErr (1 - C) u η S X` of the exact step `S + C·(X - S)`, where `C`, `S`, `X` are the values of `c`, `state`, `x`. Written out, with `d = u·\|X - S\| + η` (the difference's error) and `p = u·\|C\|·(\|X - S\| + d) + η + \|C\|·d` (the product's), the bound is `u·(\|S + C·(X - S)\| + p) + η + p`. |
| `smoother::process_f32` | `smoother.coeff_f32_error`, `smoother.coeff_f32_exact` | `Smoother/BridgeF32.lean` | The same as the `process_f64` coefficient row, in binary32 (`u = 2⁻²⁴`). |
| `smoother::step_f32` | `smoother.step_f32_error` | `Smoother/BridgeF32.lean` | The same in binary32. |
| `smoother::process_f64` | `smoother.process_f64_block_error` (and `filt_f64_block_error`, the same about `filt_f64`) | `Smoother/BlockF64.lean` | **Whole-block error.** Under the conditions below: never fails, and every output sample and the final state are within `E` of the exact smoother `smoother.filt_real A` with the stored coefficient (`A = 1 - C`, `C` the value of the stored `c = 1 - a`), run on the same stored inputs from the same stored start, for a block of any length. |
| `smoother::process_f32` | `smoother.process_f32_block_error` (and `filt_f32_block_error`) | `Smoother/BlockF32.lean` | The same in binary32. |
| `smoother::process_f64` | `smoother.process_f64_block_error_of_inputs` (and `noOverflow_f64_of_inputs`) | `Smoother/BlockF64.lean` | **The same, with conditions on the inputs only:** no step overflows, proved from the inputs rather than assumed, when the value of `a` is at most 1 in size and `G + W + (1 + u)·\|C\|·G + η` (below) is at most the largest finite binary64 value (about 1.8 × 10³⁰⁸). |
| `smoother::process_f32` | `smoother.process_f32_block_error_of_inputs` (and `noOverflow_f32_of_inputs`) | `Smoother/BlockF32.lean` | The same in binary32 (largest finite value about 3.4 × 10³⁸). |
| `smoother::process_f64` | `smoother.process_f64_settle_of_inputs` | `Smoother/BlockF64.lean` | **Settling on a steady input.** When every sample is `x` (value `X`, with `\|X\| ≤ M`), under the conditions of `process_f64_block_error_of_inputs`: never fails, and after a block of `n` samples the state is within `\|A\|^n·\|S - X\| + E` of `X`, where `S` is the value of the starting state. |
| `smoother::process_f32` | `smoother.process_f32_settle_of_inputs` | `Smoother/BlockF32.lean` | The same in binary32. |
| `smoother::step_coeff_f64` | `smoother.step_coeff_f64_eq` | `Smoother/SpecF64.lean` | Exactly `state + c * (target - state)` in binary64, in that order, with `c` as given; never fails. |
| `smoother::process_coeff_f64` | `smoother.process_coeff_f64_spec` | `Smoother/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `state + c * (x - state)` in binary64 to each sample in turn, with `c` as given (Lean's `smoother.filt_f64 c`). |
| `smoother::step_f64`, `process_f64` | `smoother.step_f64_eq_step_coeff`, `smoother.process_f64_eq_process_coeff` | `Smoother/SpecF64.lean` | For every `a`, state, target and block: `step_f64 a` returns the same float as `step_coeff_f64` with `c = 1 - a` computed in binary64, and `process_f64 a` returns the same outputs and final state as `process_coeff_f64` with that `c`. |
| `smoother::step_coeff_f32`, `process_coeff_f32` | `smoother.step_coeff_f32_eq`, `smoother.process_coeff_f32_spec`, `smoother.step_f32_eq_step_coeff`, `smoother.process_f32_eq_process_coeff` | `Smoother/SpecF32.lean` | The same four facts in binary32. |
| `smoother::process_coeff_f64` | `smoother.process_coeff_f64_block_error`, `smoother.process_coeff_f64_block_error_of_inputs`, `smoother.process_coeff_f64_settle_of_inputs` | `Smoother/BlockF64.lean` | The whole-block error, the same with conditions on the inputs only, and settling on a steady input, as the three `process_f64` theorems above, with `C` the value of the given `c` and `A = 1 - C`. The conditions are the same, written with `c` for `1 - a`, except that the `_of_inputs` and settling theorems assume `c` finite in place of `a` finite with value at most 1 in size. |
| `smoother::process_coeff_f32` | `smoother.process_coeff_f32_block_error`, `smoother.process_coeff_f32_block_error_of_inputs`, `smoother.process_coeff_f32_settle_of_inputs` | `Smoother/BlockF32.lean` | The same in binary32. |
| `linear_smoother::set_target_f64` | `linear_smoother.set_target_f64_spec` | `LinearSmoother/SpecF64.lean` | Never fails. It sets the target; with `steps = 0` it also sets the value to the target, the step to `0` and `remaining` to 0, and otherwise it sets the step to `(target - value) / castNat_f64 steps` in binary64 (`gain.rampStep_f64 value target steps`) and `remaining` to `steps`, keeping the value. |
| `linear_smoother::step_f64` | `linear_smoother.step_f64_spec` | `LinearSmoother/SpecF64.lean` | Never fails. It returns `nextValue_f64 s`: the value itself when `remaining = 0`, the target when `remaining = 1`, and `target - step * castNat_f64 (remaining - 1)` otherwise, in binary64 in that order; it stores that as the value, takes one off `remaining` (leaving 0 at 0) and keeps the step and the target. |
| `linear_smoother::process_f64` | `linear_smoother.process_f64_spec`, `linear_smoother.process_f64_ok` | `LinearSmoother/SpecF64.lean` | Never fails, for every state and block. Output sample `j` is `valueAfter_f64 s (j + 1)`: the value itself when `remaining = 0`, the target once `remaining ≤ j + 1`, and `target - step * castNat_f64 (remaining - (j + 1))` before that. The state left has the same step and target, `remaining` reduced by the block's length (not below 0), and the last output as its value (the value unchanged for an empty block). |
| `linear_smoother::set_target_f64`, `process_f64` | `linear_smoother.set_target_process_f64_lands`, `linear_smoother.process_f64_lands`, `linear_smoother.process_f64_at_rest` | `LinearSmoother/SpecF64.lean` | **Landing.** After `set_target_f64 s target steps`, a block of any length never fails, and every output sample `j` with `steps ≤ j + 1` (step number `steps` and every later one) is `target` as a Lean `Float` (bit for bit); when the block has at least `steps` samples, the state left holds `target` as its value, with `remaining = 0`. With `remaining = 0`, a block leaves the value, step, target and `remaining` as they were, and every output sample is the value. |
| `linear_smoother::set_target_f64`, `process_f64` | `linear_smoother.valueAfter_set_target_f64` | `LinearSmoother/SpecF64.lean` | After `set_target_f64 s target steps`, for `1 ≤ k < steps`, the value after `k` steps is `rampValue_f64 value target steps k`, which is `target - gain.rampStep_f64 value target steps * castNat_f64 (steps - k)` in binary64, in that order. |
| `linear_smoother::step_f64` | `linear_smoother.rampValue_f64_error` (and `gain.ramp_error_real`, `Gain/Line.lean`) | `LinearSmoother/BridgeF64.lean` | **Accuracy.** When `start` and `target` are finite and at most `2^1020` in size, `1 ≤ n ≤ 2^53` and `k < n`: `rampValue_f64 start target n k` is finite, and its real value is within `u·\|T\| + 5u·\|T - S\| + (2n + 4)·η` of the straight line `S + (T - S)·k/n`, where `S`, `T` are the values of `start`, `target`, `u = 2⁻⁵³` and `η = 2⁻¹⁰⁷⁵`. |
| `linear_smoother::set_target_f32`, `step_f32`, `process_f32` | the `_f32` versions of the theorems above (`linear_smoother.set_target_f32_spec`, `step_f32_spec`, `process_f32_spec`, `process_f32_ok`, `set_target_process_f32_lands`, `process_f32_lands`, `process_f32_at_rest`, `valueAfter_set_target_f32`, `rampValue_f32_error`) | `LinearSmoother/SpecF32.lean`, `LinearSmoother/BridgeF32.lean` | The same in binary32, with `2^124` in place of `2^1020`, `2^24` in place of `2^53`, `u = 2⁻²⁴` and `η = 2⁻¹⁵⁰`. |
| `allpass1::coeff_f64` | `allpass1.coeff_f64_eq` | `Allpass1/SpecF64.lean` | Never fails, and returns exactly `(t - 1) / (t + 1)` with `t = libm.tanModel_f64 (PI * corner_hz / sample_rate_hz)` (`PI` is `core.f64.consts.PI`; multiplication first), each operation in binary64 in that order (`1` is the binary64 number 1). That this gives a 90° phase shift at `corner_hz` is not proved. |
| `allpass1::step_f64` | `allpass1.step_f64_eq` | `Allpass1/SpecF64.lean` | Exactly `apStep_f64`: the output `y = c * (x - y1) + x1` in binary64, in that order, and the new state `(x1, y1) = (x, y)`; never fails. |
| `allpass1::process_f64` | `allpass1.process_f64_spec` | `Allpass1/SpecF64.lean` | Never fails, and its outputs and final state are exactly those of applying `apStep_f64` to each sample in turn (Lean's `allpass1.filt_f64`). |
| `allpass1::coeff_f32`, `step_f32`, `process_f32` | `allpass1.coeff_f32_eq`, `allpass1.step_f32_eq`, `allpass1.process_f32_spec` | `Allpass1/SpecF32.lean` | The same three facts in binary32, with `core.f32.consts.PI` and `libm.tanModel_f32`. |
| (the all-pass, exact arithmetic) | `allpass1.filt_real_abs_le_outBound` | `Allpass1/Block.lean` | **Stability.** In exact arithmetic, when `\|C\| < 1`: from the state `(x1, S)`, with `x1` and every input at most `M ≥ 0` in size, every output of `allpass1.filt_real` and its final previous output are at most `allpass1.outBound C M S = \|S\| + (1 + \|C\|)·M/(1 - \|C\|)` in size, for a block of any length. |
| `allpass1::step_f64` | `allpass1.apStep_f64_error` (and `allpass1.stepErr_of_roundings`, real numbers, in `Allpass1/Block.lean`) | `Allpass1/BlockF64.lean` | When `c`, the state, `x` and the step's three rounded results (`x - y1`, `c * (x - y1)` and the output) are finite: the output is within `stepErr C u η X1 Y1 X` of the exact step `C·(X - Y1) + X1`, where `C`, `X1`, `Y1`, `X` are the values of `c`, `x1`, `y1`, `x`. Written out, with `D = X - Y1`, `d = u·\|D\| + η` and `p = u·\|C\|·(\|D\| + d) + η + \|C\|·d`, the bound is `u·(\|C·D + X1\| + p) + η + p`. |
| `allpass1::process_f64` | `allpass1.process_f64_block_error` (and `filt_f64_block_error`, the same about `filt_f64`) | `Allpass1/BlockF64.lean` | **Whole-block error.** Under the conditions below: never fails; every output sample and the final `y1` are within `E` of the exact filter `allpass1.filt_real C (X1, S)`, run on the values of the stored inputs from the values of the stored state, and the final `x1` has exactly the exact filter's final previous input as its value; for a block of any length. |
| `allpass1::process_f64` | `allpass1.process_f64_block_error_of_inputs` (and `noOverflow_f64_of_inputs`) | `Allpass1/BlockF64.lean` | **The same, with conditions on the inputs only:** no step overflows, proved from the inputs rather than assumed, when `M + (1 + u)·((1 + u)·(M + B + E) + η) + η` is at most the largest finite binary64 value (about 1.8 × 10³⁰⁸). |
| `allpass1::step_f32`, `process_f32` | `allpass1.apStep_f32_error`, `allpass1.process_f32_block_error` (and `filt_f32_block_error`), `allpass1.process_f32_block_error_of_inputs` (and `noOverflow_f32_of_inputs`) | `Allpass1/BlockF32.lean` | The same in binary32 (largest finite value about 3.4 × 10³⁸). |
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
| (biquads with complex poles) | `biquad.complexPolesContraction`, `biquad.complexPoleNorm_update` | `Biquad/Contraction.lean` | A `Contraction` for any biquad with complex poles inside the unit circle (`a1² < 4·a2`, `a2 < 1`): for example RBJ low-pass, high-pass, band-pass, notch and all-pass filters with `Q > 1/2` (worked out outside Lean, not proved), provided `a1² < 4·a2` still holds after the coefficients are rounded (it fails for the binary32 coefficients `lowPass1Hz_f32`, those of a 1 Hz Butterworth low-pass at 48 kHz, worked out outside Lean, not proved: `lowPass1Hz_real_poles_f32`). Measured by `complexPoleNorm`, the state-update map multiplies every pair's measure by exactly `√a2`, the pole radius (`ρ = √a2`). `cInf = (1 + \|a1\|/2)/ω + 1` and `K = ω + \|a1\|/2 + 1` with `ω = √(a2 - a1²/4)`; `cInf` grows like `1/ω` as the poles approach the real axis. |
| (biquads with distinct real poles) | `biquad.realPolesContraction`, `biquad.realPoleNorm_update`, `biquad.realPoles_lt_one_iff` | `Biquad/Contraction.lean` | A `Contraction` for any biquad with distinct real poles inside the unit circle (`a1² > 4·a2`, `a2 < 1`, `\|a1\| < 1 + a2`; given the first, the other two say both poles are less than 1 in size, `realPoles_lt_one_iff`): for example an RBJ low-pass with `Q < 1/2` (worked out outside Lean, not proved), provided `a1² > 4·a2`, `a2 < 1` and `\|a1\| < 1 + a2` still hold after the coefficients are rounded (the last fails for the binary32 coefficients `lowPass1Hz_f32`, those of a 1 Hz Butterworth low-pass at 48 kHz, worked out outside Lean, not proved: `lowPass1Hz_pole_one_f32`). Measured by `realPoleNorm`, `ρ = (\|a1\| + d)/2`, the larger pole size (`max_abs_realPoles`), `cInf = 1/d` and `K = 2`, where `d = √(a1² − 4·a2)` is the distance between the poles; `cInf = 1/d` grows without bound as `d → 0`. The state-update map multiplies `p·v₁ + v₂` by `p` and `q·v₁ + v₂` by `q` (`realPoleCoord_update`). |
| (biquads with a repeated real pole) | `biquad.repeatedPoleContraction` | `Biquad/Contraction.lean` | A `Contraction` for any biquad with a repeated real pole `p = -a1/2` (`a1² = 4·a2`), for any chosen `ε > 0` with `\|p\| + ε < 1`: measured by `repeatedPoleNorm`, `ε·\|v₁\| + \|p·v₁ + v₂\|`, with `ρ = \|p\| + ε`, `cInf = 1 + 1/ε` and `K = 1`. |
| (biquads with poles close together) | `biquad.closePolesContraction`, `biquad.closePoleCoord_update` | `Biquad/Contraction.lean` | A `Contraction` for any biquad, with real or complex poles, for any chosen `ε > 0` with `ρ = \|a1\|/2 + max(ε, \|a1²/4 − a2\|/ε) < 1`: measured by `repeatedPoleNorm`, `ε·\|v₁\| + \|p·v₁ + v₂\|` with `p = −a1/2`, with this `ρ`, `cInf = 1/ε` and `K = 1`. With `w = p·v₁ + v₂` and `δ = a1²/4 − a2`, the state-update map takes `v₁` to `p·v₁ + w` and `w` to `p·w + δ·v₁` (`closePoleCoord_update`). `cInf = 1/ε` does not depend on the distance between the poles, so, unlike `realPolesContraction`'s `1/d`, it does not grow as they merge. Worked out outside Lean, not proved: `ρ < 1` needs `\|p\| + √\|δ\| < 1`, which for complex poles is stricter than both poles being inside the unit circle, and `cInf = 1/ε` is always above `1/(1 − \|p\|)`. |
| (biquads with a pole at 1) | `biquad.isEmpty_contraction_of_pole_one` | `Biquad/Contraction.lean` | When 1 is a pole (`1 + a1 + a2 = 0`), no `Contraction` exists: the state-update map leaves the pair `(1, -a2)` unchanged (`update_one_neg_a2_of_pole_one`). |
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
| `delay::process_f64` | `delay.process_f64_ok` | `Delay/SpecF64.lean` | Never fails, for every buffer, position, delay and audio. |
| `delay::process_f64` | `delay.process_f64_empty_buffer` | `Delay/SpecF64.lean` | With an empty buffer: never fails, and returns the buffer, position and audio unchanged. |
| `delay::process_f64` | `delay.process_f64_spec` | `Delay/SpecF64.lean` | For a buffer of length `L > 0`, any position `p`, any delay `delay_samples` and `n` input samples, with `d = min(delay_samples, L - 1)` and the history `H = buffer.rotate p ++ audio` (Mathlib's `List.rotate`: the buffer read oldest first from index `p mod L`, then the input): never fails; the output has `n` samples, and for each `j < n` output sample `j` is element `L + j - d` of `H`; the new buffer has length `L`; the new position is `(p + n) mod L`; and the new buffer read oldest first from the new position (`buffer'.rotate p'`) is `H` without its first `n` elements, that is, its last `L` elements. |
| `delay::process_f64` | `delay.process_f64_spec_of_lt` | `Delay/SpecF64.lean` | The same, when `delay_samples < L`, with `d = delay_samples`. |
| `delay::process_f64` | `delay.process_f64_getElem` | `Delay/SpecF64.lean` | For a buffer of length `L > 0`, with `p`, `n`, `d` and `H` as in `process_f64_spec`: never fails; the output has `n` samples, and for each `j < n` output sample `j` equals `H[L + j - d]` (Lean's `getElem`, with both indices proved in range in the statement). |
| `delay::process_f64` | `delay.process_f64_zero_prefix` | `Delay/SpecF64.lean` | For a buffer of length `L > 0` whose elements are all the float `0`, any position, any `delay_samples` and `n` input samples, with `d = min(delay_samples, L - 1)`: never fails, and output sample `j` is `0` for every `j < min(d, n)`. |
| `delay::process_f64` | `delay.process_f64_append` | `Delay/SpecF64.lean` | For any buffer (empty or not), position and `delay_samples` (the same in every call), and input `audio` equal to `audio₁` followed by `audio₂`: a call on `audio₁`, a call on `audio₂` with the buffer and position the first call returned, and one call on `audio` from the starting buffer and position all never fail; the two calls end with the same buffer and position as the one call, and their output samples, joined, are its output samples. |
| `delay::process_f64` | `delay.process_f64_state_indep` | `Delay/SpecF64.lean` | For any buffer (empty or not), position and audio, and any two delays `d₁` and `d₂`: a call with `d₁` and a call with `d₂`, from the same buffer, position and audio, both never fail and return the same new buffer and the same new position; only their output samples may differ. |
| `delay::process_f32` | `delay.process_f32_ok`, `delay.process_f32_empty_buffer`, `delay.process_f32_spec`, `delay.process_f32_spec_of_lt`, `delay.process_f32_getElem`, `delay.process_f32_zero_prefix`, `delay.process_f32_append`, `delay.process_f32_state_indep` | `Delay/SpecF32.lean` | The same eight facts for `f32` samples. |
| `delay::read_f64` | `delay.read_f64_ok`, `delay.read_f64_empty_buffer` | `Delay/SpecF64.lean` | Never fails, for every buffer, position and delay; with an empty buffer it returns `0`. |
| `delay::read_f64` | `delay.read_f64_spec` | `Delay/SpecF64.lean` | For a buffer of length `L > 0`, any position `p` and any `delay_samples`, with `d = min(delay_samples, L - 1)`: never fails, and returns element `(p + L - d) mod L` of the buffer (`buffer[(p + L - d) mod L]? = some y`). It returns only the sample: the buffer and position are not changed. |
| `delay::read_f64` | `delay.read_f64_rotate` | `Delay/SpecF64.lean` | The same, when `d ≥ 1`: the result is element `L - d` of `buffer.rotate p`, the buffer read oldest first from index `p mod L`. When `p` is where the next write goes, that is the sample written `d` writes ago (worked out outside Lean, not proved: it also needs `write_f64_rotate` and at least `d` earlier writes). |
| `delay::write_f64` | `delay.write_f64_ok`, `delay.write_f64_empty_buffer` | `Delay/SpecF64.lean` | Never fails, for every buffer, position and sample; with an empty buffer it returns the buffer and position unchanged. |
| `delay::write_f64` | `delay.write_f64_spec`, `delay.write_f64_rotate` | `Delay/SpecF64.lean` | For a buffer of length `L > 0`, any position `p` and sample `x`: never fails; the new buffer is the old one with element `p mod L` replaced by `x` (`List.set`), and the new position is `(p + 1) mod L`; the new buffer has length `L`, and read oldest first from the new position it is `buffer.rotate p ++ [x]` without its first element. |
| `delay::read_f64`, `write_f64` | `delay.write_f64_eq_process_state`, `delay.read_write_f64_eq_process` | `Delay/SpecF64.lean` | With `audio` the one-sample block `[x]`: for any buffer (empty or not), position and delay, `write_f64` of `x` and `process_f64` on `audio` both never fail and return the same buffer and the same position. When `d = min(delay_samples, L - 1) ≥ 1`, also `read_f64` at the same position, before the write, never fails, and the output of `process_f64` is `[y]`, `y` being the sample `read_f64` returned. (With `d = 0` they differ: `process_f64` returns `x` itself and `read_f64` the sample that `x` overwrites; worked out outside Lean from `process_f64_spec`, `read_f64_spec` and `write_f64_spec`, not proved as a theorem.) |
| `delay::read_f32`, `write_f32` | `delay.read_f32_ok`, `delay.read_f32_empty_buffer`, `delay.read_f32_spec`, `delay.read_f32_rotate`, `delay.write_f32_ok`, `delay.write_f32_empty_buffer`, `delay.write_f32_spec`, `delay.write_f32_rotate`, `delay.write_f32_eq_process_state`, `delay.read_write_f32_eq_process` | `Delay/SpecF32.lean` | The same ten facts for `f32` samples. |
| `delay::read_interp_f64` | `delay.read_interp_f64_short_buffer`, `delay.read_interp_f64_ok` | `Delay/InterpF64.lean` | Never fails, for every buffer, position and delay; with a buffer of fewer than 5 samples it returns `0`. |
| `delay::read_interp_f64` | `delay.read_interp_f64_spec`, `delay.interpPoint_f64_fst_le` | `Delay/InterpF64.lean` | For a buffer of length `L ≥ 5`, with `(n, t) = interpPoint_f64 L delay` (with `whole` the translated `delay as usize`: `(2, 0)` if `whole < 2`, `(L - 3, 1)` if `whole > L - 3`, and `(whole, delay - castNat_f64 whole)` otherwise; `2 ≤ n ≤ L - 3`): never fails, and returns exactly `lagrange4_f64 t xm1 x0 x1 x2`, where `xm1`, `x0`, `x1` and `x2` are the buffer's elements at `(position + L - k) mod L` for `k = n - 1`, `n`, `n + 1` and `n + 2` (the elements `read_f64` returns at those delays, `read_f64_spec`), and `lagrange4_f64` is `((wm1·xm1 + w0·x0) + w1·x1) + w2·x2` with `wm1 = -(t·(t - 1)·(t - 2))/6`, `w0 = (t + 1)·(t - 1)·(t - 2)·0.5`, `w1 = -((t + 1)·t·(t - 2))·0.5` and `w2 = (t + 1)·t·(t - 1)/6`, each operation in binary64 in that order, products left to right. |
| (`d as usize` for a float `d`) | `toUScalar_usize_val_f64`, `toUScalar_usize_val_f32` | `Cast.lean` | For every finite `d` of value `D`, the translated cast is `min(⌊D⌋₊, USize.size - 1)`: the integer part of `D` (0 when `D < 1`, negative `D` included), capped at the largest `usize`. |
| `delay::read_interp_f64` | `delay.read_interp_f64_frac` | `Delay/InterpF64.lean` | For a finite `delay` of value `D` and `5 ≤ L ≤ 2^53`: `t` is finite, with value between 0 and 1; when `D < 2`, `n = 2` and `t` has value 0; when `2 ≤ D < L - 2`, `n = ⌊D⌋₊` and `t` has value exactly `D - n` (the subtraction is exact, by Sterbenz's lemma); when `D ≥ L - 2`, `n = L - 3` and `t` has value 1. |
| `delay::read_interp_f64`, `read_f64` | `delay.read_interp_f64_whole`, `delay.read_interp_f64_whole_eq_read` | `Delay/InterpF64.lean` | **At a whole-number delay.** For `5 ≤ L ≤ 2^53`, a finite `delay` whose value is a whole number `D` with `2 ≤ D ≤ L - 2`, and every sample in the buffer finite: `read_interp_f64` never fails and returns a finite value equal, as a real number, to the buffer's element at `(position + L - D) mod L`; for any `usize` `d` of value `D`, `read_f64` at `d` never fails and returns that element. So the two results have the same value; as floats they can differ only in the sign of a zero (worked out outside Lean, not proved). |
| (the interpolation, exact arithmetic) | `delay.lagrange4_real_abs_le` | `Delay/Interp.lean` | In exact arithmetic, for `0 ≤ t ≤ 1` and four samples at most `M` in size, the formula of `lagrange4_f64` (`delay.lagrange4_real`) is at most `(1 + t - t²)·M ≤ (5/4)·M` in size. A bound on the rounded result is not proved. |
| `delay::read_interp_f32` | `delay.read_interp_f32_short_buffer`, `delay.read_interp_f32_ok`, `delay.read_interp_f32_spec`, `delay.interpPoint_f32_fst_le`, `delay.read_interp_f32_frac`, `delay.read_interp_f32_whole`, `delay.read_interp_f32_whole_eq_read` | `Delay/InterpF32.lean` | The same facts for `f32` samples (`interpPoint_f32`, `lagrange4_f32`), with `L ≤ 2^24` in place of `L ≤ 2^53`. |

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
(`block_error_real`), shared by both precisions; the smoother's in `Smoother/Block.lean`
(`smoother.block_error_real`); the biquad's is in `Biquad/Block.lean` and the SVF's in
`Svf/Block.lean`, both using the facts about a `Contraction` in `TwoState.lean`.

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

For the first-order all-pass, the whole-block theorems likewise compare the Rust outputs with
the exact filter run on the exact values of the stored floats: `C` is the value of `c`, `X1` and
`S` those of the starting state's `x1` and `y1`, and the inputs are the values of the stored
samples. (So the rounding of a decimal coefficient to a float, or inside `coeff_*`, is not
covered.) The previous input `x1` is a stored input, never rounded, so only the previous output
carries an error from step to step, multiplied by `C` each step. The conditions:

- `c` and the starting state are finite, and no step overflows (`allpass1.NoOverflow_f64` /
  `NoOverflow_f32`: every input, every difference `x - y1`, every product `c * (x - y1)` and every
  output is finite). The `_of_inputs` theorems need no no-overflow condition: they prove it,
  given the other conditions here, every input finite, and the size condition in the table;
- `X1` and every input are at most `M` in size, with `M ≥ 0`;
- `|C| + κ < 1`, where `κ = errGrowth C u = |C|·u·(1 + (1 + u)·(2 + u))`
  (`allpass1.errGrowth`): stable, with a little room for rounding.

Then, with `B = |S| + (1 + |C|)·M / (1 - |C|)` (`allpass1.outBound`, a bound on the exact
filter's outputs):

`E = (κ·(M + B) + u·M + ((1 + u)·(1 + |C|·(1 + u)) + 1)·η) / (1 - |C| - κ)`
(`allpass1.errBound`, with `allpass1.errBase` the part `u·M + ((1 + u)·(1 + |C|·(1 + u)) + 1)·η`).

For the smoother, `process_f64` / `process_f32` compute the coefficient `c = 1 - a` once per
block, rounded, so every step uses the same stored `c`. The whole-block theorems compare the Rust
outputs with the exact smoother `smoother.filt_real A` with that stored coefficient: `A = 1 - C`,
where `C` is the value of `c`, run on the values of the stored samples from the value `S` of the
stored starting state. The coefficient's own rounding is therefore not in `E`. It is bounded
separately: `A` is within `u·|1 - a| + η` of the value of `a` (`coeff_f64_error`,
`coeff_f32_error`), and when the value of `a` is between 1/2 and 2, as for a slow smoother, `c` is
exact and `A` is the value of `a` (`coeff_f64_exact`, `coeff_f32_exact`). The conditions:

- `1 - a`, the starting state and every input are finite, and no step overflows
  (`smoother.NoOverflow_f64` / `NoOverflow_f32`: every difference `x - state`, every product
  `c * (x - state)` and every output is finite). The `_of_inputs` theorems need no no-overflow
  condition: they prove it, given the other conditions here, that `a` is finite with value at
  most 1 in size, and that `G + W + (1 + u)·|C|·G + η` is at most the largest finite value, where
  `W = B + E` and `G = (1 + u)·(M + W) + η`, with `B` and `E` below;
- every input is at most `M` in size, with `M ≥ 0`;
- `|A| + errGrowth A u < 1`, where `errGrowth A u = u·|A| + (1 + u)·|1 - A|·u·(2 + u)`
  (`smoother.errGrowth`): stable, with a little room for rounding.

Then, with `B = |S| + |1 - A|·M / (1 - |A|)` (`smoother.outBound`, a bound on the exact smoother's
outputs; it is `|S| + M` when `0 ≤ A < 1`, `smoother.outBound_eq_of_nonneg`):

`E = stepBound A u η M B / (1 - |A| - errGrowth A u)` (`smoother.errBound`)

where `stepBound A u η M W = u·(|A|·W + |1 - A|·M) + (1 + u)·(|1 - A|·u·(2 + u)·(M + W) +
|1 - A|·(1 + u)·η + η) + η` bounds one step's rounding error when the input is at most `M` and
the state at most `W` in size (`smoother.stepErr_le`).

For a steady input `x` of value `X` (every sample equal to `x`) and any `M ≥ |X|`,
`process_f64_settle_of_inputs` / `process_f32_settle_of_inputs` prove that after a block of `n`
samples the state is within `|A|^n·|S - X| + E` of `X`. The first term is how far the exact
smoother still is from `X` (`filt_real_replicate`), and shrinks to 0 as `n` grows when `|A| < 1`;
the rounding term `E` does not.

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

For the smoother, with inputs at most `M = 1` in size and a starting state of value `S = 0`, the
theorems below prove, for every real `A` with `0 ≤ A` and `A` at most the bound in the third
column: the stability condition holds, `B = 1` exactly, and `E` and `20·log₁₀ E` (`E` relative to
the input bound 1, in decibels) are at most the values shown. Here `A = 1 - C`, with `C` the value
of the stored coefficient, and `E` is `smoother.errBound A u η 1 0`, with `u` and `η` the
precision's rounding constants. The values shown were chosen a little above the values of the
formula at that bound (worked out outside Lean, not proved), so each proved bound can be slightly
weaker than the formula's value.

| Precision | `a` | `A` at most | `E` | `E` relative to 1 | Theorem |
|---|---|---|---|---|---|
| f32 | 0.99 | 0.990001 | ≤ 6.2 × 10⁻⁶ | ≤ −104.1 dB | `smoother.table_row_le_of_le_099_f32` |
| f32 | 0.999 | 0.999001 | ≤ 6 × 10⁻⁵ | ≤ −84.4 dB | `smoother.table_row_le_of_le_0999_f32` |
| f64 | 0.99 | 0.99 | ≤ 1.16 × 10⁻¹⁴ | ≤ −278.7 dB | `smoother.table_row_le_of_le_099_f64` |
| f64 | 0.999 | 0.999 | ≤ 1.12 × 10⁻¹³ | ≤ −259.0 dB | `smoother.table_row_le_of_le_0999_f64` |

Each bound in the third column covers the `A` the smoother uses for that `a`. The precision stores
`a` as for the one-pole (f32: 0.99 as 0.9900000095 and 0.999 as 0.9990000129; f64: 0.99 as
0.98999999999999999112 and 0.999 as 0.99899999999999999911; these stored values are worked out
outside Lean, not proved). Each stored value is between 1/2 and 2, so `c = 1 - a` is computed
exactly (`coeff_f64_exact`, `coeff_f32_exact`) and `A` is the stored value of `a`. The rows rest on
`smoother.table_row_le_of_le` in `Smoother/Block.lean`, which uses `smoother.errBound_le_of_le`:
when `0 ≤ u ≤ 1/4`, `0 ≤ η`, `0 ≤ A ≤ a` and `a + errGrowth a u < 1`, the stability condition
holds at `A`, `B = 1` and `E` is at most its value at `A = a`. At these bounds the smoother's `E`
is close to `u / (1 - a)` (worked out outside Lean, not proved).

For each row, the size condition of the smoother's `_of_inputs` and settling theorems is also
proved, with `M = 1`, `S = 0` and every real `A` with `0 ≤ A` at most the row's bound: with
`W = B + E` and `G = (1 + u)·(1 + W) + η`, `G + W + (1 + u)·|1 - A|·G + η` is at most the largest
finite value of the precision (`smoother.sizeCondition_of_le_099_f32`, `_0999_f32`, `_099_f64`,
`_0999_f64`; in those theorems `|1 - A|` is `|C|`). They rest on `smoother.sizeCondition_le_24`
in `Smoother/Block.lean`: the left-hand side, with `B = 1`, is at most 24 when `0 ≤ u ≤ 1`,
`0 ≤ η ≤ 1`, `0 ≤ A ≤ 1` and `0 ≤ E ≤ 1`.

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
last two items (four theorems) are about RBJ low-pass filters with `Q = 0.4` and `Q = 0.5` at
1 kHz instead, whose poles are real. Each one that bounds `cInf·Ê + L` also proves that the
condition `cInf·K·κ·β < 1 − ρ` holds for the `Contraction` it uses, and that the coefficients meet
that `Contraction`'s conditions: poles inside the unit circle (complex, or real where that is
said), or, for `closePolesContraction`, `ρ < 1`.

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
  (`lowPass1kHzQ05_bound_f32`). With `closePolesContraction` and `ε = 0.06` instead, `ρ < 1`,
  `cInf = 1/ε` is below 17, the condition holds, and `cInf·Ê + L` is at most 0.0122 and at most
  −38 dB, `Sb ≤ 4.01` and `V ≤ 85` (`lowPass1kHzQ05_bounds_f32`). `ε = 0.06` is close to the `ε`
  that makes this bound smallest (worked out outside Lean, not proved).

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
`svf.complexPolesContraction`, `cInf` and `K` are about 3.41 and 2.41 at every cutoff (worked out
outside Lean, not proved), while the biquad's `cInf` grows like `1/ω` as the cutoff falls (worked
out outside Lean, not proved). There is no biquad row at 20 Hz (see "Observations").

## Fused multiply-add functions (the `std` feature)

With the cargo feature `std`, the crate also has `one_pole::step_fma_f64` / `process_fma_f64`,
`smoother::step_fma_f64` / `process_fma_f64` and `step_coeff_fma_f64` / `process_coeff_fma_f64`,
`allpass1::step_fma_f64` / `process_fma_f64`,
`biquad::step_fma_f64` / `process_fma_f64`, `svf::step_fma_f64` / `process_fma_f64` and their
`_f32` versions. They call Rust's `mul_add`, which Aeneas translates to Lean's `Float.fma` /
`Float32.fma`: `x·y + z` computed exactly and rounded once (Lean core's model
`Float.Model.UnpackedFloat.fma`). Which products are fused is fixed by the code, on every
processor:

| Rust function | Computes (each `fma(a, b, z)` is `a·b + z` rounded once; every other operation rounded on its own) |
|---|---|
| `one_pole::step_fma_*` | `y = fma(a, state, x)` |
| `smoother::step_coeff_fma_*`, `step_fma_*` | `y = fma(c, x - state, state)`, with `c` as given, or `c = 1 - a` (computed once per block by `process_fma_*`) |
| `allpass1::step_fma_*` | `y = fma(c, x - y1, x1)`, with the new state `(x1, y1) = (x, y)` |
| `biquad::step_fma_*` | `y = fma(b0, x, s1)`, `s1' = fma(b1, x, -(a1·y)) + s2`, `s2' = fma(b2, x, -(a2·y))` |
| `svf::step_fma_*` | `hp = (fma(-(k + g), s1, x) - s2)·d`, `bp = fma(g, hp, s1)`, `lp = fma(g, bp, s2)`, `s1' = fma(g, hp, bp)`, `s2' = fma(g, bp, lp)`, `y = fma(m_lp, lp, fma(m_hp, hp, m_bp·bp))` |

This is the grouping clang gives the unfused expressions under its default `-ffp-contract=on`,
which fuses a product into the addition or subtraction that uses it, within one expression,
trying the left operand first; on Apple silicon each `fma` is then one instruction (worked out
outside Lean, not proved). So each fused
step computes the same as the same step written that way in C or C++ and compiled by clang there
(worked out outside Lean, not proved: checked against Apple clang 17, arm64, -O2). For the SVF
this is the step only. Its coefficients, `d` included, come from `CoeffsF64::new` and the design
functions, which do not fuse, while clang also fuses `1 + g·(g + k)` in `d = 1/(1 + g·(g + k))`;
so a C or C++ SVF built that way can get a different `d`, and the whole filter matches only if
`d` is computed unfused there too (worked out outside Lean, not proved).

| Rust function | Theorem | File | Says |
|---|---|---|---|
| (Lean's `Float.fma`, `Float32.fma`) | `real_fma_f64`, `real_fma_f32` | `FmaFacts.lean` | **One rounding.** When `x`, `y`, `z` and `x.fma y z` are finite: the real value of `x.fma y z` is `x·y + z` rounded to nearest, ties to even (FloatLib's `roundAt`). |
| (the same) | `abs_real_fma_sub_le_f64`, `abs_real_fma_sub_le_f32` | `FmaFacts.lean` | Under the same conditions, `x.fma y z` is within `u·\|x·y + z\| + η` of `x·y + z`: the bound of one `+`, `-`, `*` or `/` (`abs_real_add_sub_le_f64` and the others). |
| (the same) | `isFinite_fma_f64`, `isFinite_fma_f32` | `FmaFacts.lean` | When `x`, `y` and `z` are finite and `\|x·y + z\|` is at most the largest finite value, `x.fma y z` is finite. |
| (the same) | `real_fma_eq_floatLib_fma_f64`, `real_fma_eq_floatLib_fma_f32` | `FmaFacts.lean` | When `x`, `y`, `z`, `x.fma y z` and FloatLib's own `Model.fma` of the three are finite, the two have the same real value. |
| (Lean's negation) | `real_neg_f64`, `real_neg_f32`, `isFinite_neg_f64`, `isFinite_neg_f32` | `FmaFacts.lean` | Negating a finite float is exact: the result is finite, with the negated real value. |
| `one_pole::step_fma_f64`, `process_fma_f64` | `one_pole.step_fma_f64_eq`, `one_pole.process_fma_f64_spec` | `OnePole/FmaF64.lean` | Exactly `a.fma state x` in binary64; never fails; the block's outputs and final state are those of applying it to each sample in turn (`filt_fma_f64`). |
| `one_pole::step_fma_f64` | `one_pole.step_fma_f64_error` | `OnePole/FmaF64.lean` | When `a`, `state`, `x` and the result are finite, one fused step is within `u·\|x + a·state\| + η` (`abs_real_fma_sub_le_f64`), and so within the unfused step's bound `stepErr` (`one_pole.step_fma_f64_error`), of exact real arithmetic. |
| `one_pole::process_fma_f64` | `one_pole.process_fma_f64_block_error`, `one_pole.process_fma_f64_block_error_of_inputs` | `OnePole/FmaF64.lean` | **Whole-block error.** The conditions and the bound `E` of `process_f64_block_error` and `process_f64_block_error_of_inputs`, with no fused step overflowing (`NoOverflowFma_f64`: every input and output finite) in place of `NoOverflow_f64`, or proved from the inputs under the same cap. The one-pole table rows above are about `E` and `B` alone, so they hold for the fused filter too. |
| `one_pole::*_fma_f32` | the `_f32` versions of the four theorems above | `OnePole/FmaF32.lean` | The same in binary32. |
| `smoother::step_fma_f64`, `process_fma_f64`, `step_coeff_fma_f64`, `process_coeff_fma_f64` | `smoother.step_fma_f64_eq`, `smoother.step_coeff_fma_f64_eq`, `smoother.process_fma_f64_spec`, `smoother.process_coeff_fma_f64_spec` | `Smoother/FmaF64.lean` | Exactly `(1 - a).fma (target - state) state` and `c.fma (target - state) state` in binary64; never fail; the blocks give exactly `filt_fma_f64 (1 - a)` (with `1 - a` computed once) and `filt_fma_f64 c`. |
| `smoother::step_fma_f64` | `smoother.step_fma_f64_error` | `Smoother/FmaF64.lean` | When `c`, `state`, `x`, the rounded difference `x - state` and the result are finite, one fused step is within the unfused step's bound `stepErr (1 - C) u η S X` of the exact step `S + C·(X - S)`. |
| `smoother::process_fma_f64`, `process_coeff_fma_f64` | `smoother.process_fma_f64_block_error`, `process_fma_f64_block_error_of_inputs`, `process_fma_f64_settle_of_inputs`, and the `process_coeff_fma_f64` versions | `Smoother/FmaF64.lean` | **Whole-block error and settling.** The statements of the unfused `process_f64` and `process_coeff_f64` theorems, with the same `E` and conditions (`NoOverflowFma_f64`: every input, difference and output finite, in place of `NoOverflow_f64` where no-overflow is assumed; the `_of_inputs` and `_settle_` forms have exactly the unfused conditions). The smoother table rows above are about `E`, `outBound` and the stability condition alone, so they hold for the fused functions too. |
| `smoother::*_fma_f32` | the `_f32` versions of the theorems above | `Smoother/FmaF32.lean` | The same in binary32. |
| `allpass1::step_fma_f64`, `process_fma_f64` | `allpass1.step_fma_f64_eq`, `allpass1.process_fma_f64_spec` | `Allpass1/SpecF64.lean` | Exactly `c.fma (x - y1) x1` in binary64, with the new state `(x, y)` (`apStep_fma_f64`); never fails; the block gives exactly `filt_fma_f64`. |
| `allpass1::step_fma_f64` | `allpass1.apStep_fma_f64_error`; `allpass1.stepErr_of_roundings_fma` (`Allpass1/Block.lean`, real numbers) | `Allpass1/BlockF64.lean` | When `c`, the state, `x`, the rounded difference `x - y1` and the result are finite, one fused step is within the unfused step's bound `stepErr C u η X1 Y1 X` of the exact step. |
| `allpass1::process_fma_f64` | `allpass1.process_fma_f64_block_error`, `allpass1.process_fma_f64_block_error_of_inputs` (and `noOverflowFma_f64_of_inputs`) | `Allpass1/BlockF64.lean` | **Whole-block error.** The statements of `process_f64_block_error` and `process_f64_block_error_of_inputs`, with the same `E` and conditions (`NoOverflowFma_f64`: every input, difference and output finite, in place of `NoOverflow_f64` where no-overflow is assumed; the `_of_inputs` form has exactly the unfused conditions). |
| `allpass1::*_fma_f32` | the `_f32` versions of the theorems above | `Allpass1/SpecF32.lean`, `Allpass1/BlockF32.lean` | The same in binary32. |
| `biquad::step_fma_f64`, `process_fma_f64` | `biquad.step_fma_f64_eq`, `biquad.process_fma_f64_spec` | `Biquad/FmaF64.lean` | Exactly `tdf2_fma_f64` (the grouping above) in binary64; never fails; the block gives exactly `filt_fma_f64`. |
| `biquad::step_fma_f64` | `biquad.tdf2_fma_f64_localErr`; `biquad.step_localErr_fma` (`Biquad/Fma.lean`, real numbers) | `Biquad/FmaF64.lean` | Under the conditions of `tdf2_f64_localErr`, with `StepFiniteFma_f64` (the six rounded results finite) in place of `StepFinite_f64`: the output and both new state values are within the same `α + β·Sb`. |
| `biquad::process_fma_f64` | `biquad.process_fma_f64_block_error`, `biquad.process_fma_f64_block_error_of_inputs` | `Biquad/FmaF64.lean` | **Whole-block error.** The statements of `process_f64_block_error` and `process_f64_block_error_of_inputs`, with the same constants and conditions (`NoOverflowFma_f64` in place of `NoOverflow_f64`), for the fused function. Every bound on those constants proved for particular coefficients (the biquad table above) therefore holds for the fused filter too. |
| `biquad::*_fma_f32` | the `_f32` versions of the theorems above | `Biquad/FmaF32.lean` | The same in binary32. |
| `svf::step_fma_f64`, `process_fma_f64` | `svf.step_fma_f64_eq`, `svf.process_fma_f64_spec` | `Svf/FmaF64.lean` | Exactly `svfStep_fma_f64` (the grouping above) in binary64; never fails; the block gives exactly `filt_fma_f64`. |
| `svf::step_fma_f64` | `svf.svfStep_fma_f64_localErr`; `svf.step_localErr_fma` (`Svf/Fma.lean`, real numbers) | `Svf/FmaF64.lean` | Under the conditions of `svfStep_f64_localErr`, with `StepFiniteFma_f64` (the eleven rounded results finite) in place of `StepFinite_f64`: the output is within the same `Ly` and the new state within the same `Ls`. |
| `svf::process_fma_f64` | `svf.process_fma_f64_block_error`, `svf.process_fma_f64_block_error_of_inputs` | `Svf/FmaF64.lean` | **Whole-block error.** The statements of `process_f64_block_error` and `process_f64_block_error_of_inputs`, with the same constants and conditions (`NoOverflowFma_f64` in place of `NoOverflow_f64`), for the fused function; so the SVF table's bounds hold for it too. |
| `svf::*_fma_f32` | the `_f32` versions of the theorems above | `Svf/FmaF32.lean` | The same in binary32. |

The fused functions round less often (one, two, two, six and eleven distinct rounded results per
step for the one-pole, the smoother, the first-order all-pass, the biquad and the SVF, against
two, three, three, nine and sixteen; a property of the code, not proved), but the bounds proved
for them are the unfused ones: correct, and no tighter. Tighter bounds for the fused functions
are not proved.

## Observations (not proofs)

What is listed here is observed or expected behaviour, not proved.

- The whole-block bounds are worst cases, and the errors seen in the measurements below are
  smaller: by a factor of about 2 to 4 for the one-pole and the smoother, about 200 to 1,100 for
  the SVF, and about 1,000 to 100,000 for the biquad, more with `realPolesContraction` for poles
  close together. The gain ramp's largest errors are 3.2 (f32) and 5.5 (f64) times below their
  bounds, and no gain came closer than 1.7 times (measured, not proved).
- At low cutoffs in f32 the SVF's whole-block theorem gives a bound where the biquad's, used with
  `biquad.complexPolesContraction`, gives none. At 20 Hz the SVF's bound is at most 0.0126
  (`svf.lowPass20Hz_bounds_f32`, proved), while for the RBJ-cookbook biquad the condition
  `cInf·K·κ·β < 1 − ρ` fails at every cutoff below about 82.4 Hz where the stored poles are complex
  (worked out outside Lean, not proved; it is proved to fail at 82 Hz,
  `biquad.lowPass82Hz_smallness_fails_f32`). That the SVF's actual errors are smaller than the
  biquad's at low cutoffs is expected, not proved.
- For RBJ-cookbook low-pass and high-pass biquads (which have the same poles), binary32 coefficients
  can put a pole on or outside the unit circle at very low cutoffs (worked out outside Lean, in
  Python, not proved; `Q` = 0.5, 0.7071, 2 and 10, cutoffs in 0.01 Hz steps up to 200 Hz and 1 Hz
  steps up to half the sample rate, testing `a2 < 1` and `|a1| < 1 + a2`). With the coefficients
  computed in binary64 and then rounded to binary32, this happens at some cutoffs below about 2.1 Hz
  at 44.1 kHz, 2.2 Hz at 48 kHz and 4.4 Hz at 96 kHz. With them computed in binary32 throughout, it
  happens at some cutoffs up to about 2.8 Hz at 44.1 kHz, 3 Hz at 48 kHz and 6 Hz at 96 kHz, the
  worst case being `Q = 0.5`. It also happens at some cutoffs within 6 Hz of half the sample rate.
  One case is proved for specific stored values: the binary32 coefficients in `lowPass1Hz_f32`,
  which are those of a 1 Hz Butterworth low-pass at 48 kHz (worked out outside Lean, not proved),
  have a pole at exactly 1 (`biquad.lowPass1Hz_pole_one_f32`).

### How close the bounds are to the errors seen (measured, not proved)

The tables compare each proved bound in the worked examples above, and the gain ramp's bound,
with the largest error seen when running the Rust code. Every "observed" figure and every ratio
is measured, not proved, and says nothing about inputs that were not tried: the largest error
over all inputs can be larger than the one observed, so each ratio may overstate how loose the
bound is.

How it was measured:

- The ignored test `tests/looseness.rs`, run with
  `cargo test --release --features std --test looseness -- --ignored --nocapture`
  (Rust 1.93.1, Apple silicon).
- Each filter starts from zero and filters blocks of 2²⁰ (1,048,576) samples, one call to
  `process_f32` / `process_f64` per block, with the stored coefficients of the theorems (for the
  SVF, the run checks that the design functions store them).
- Inputs, each at most 1 in size (so `M = 1`, as in the examples): uniform random in [−1, 1) and
  random ±1, 8 seeds each; alternating ±1; a constant 1 (a step); a sine and a square wave at the
  cutoff (for the one-pole and the smoother, at `(1 − |a|)/2π` cycles per sample); and ±1 with the
  signs of the filter's impulse response read backwards, repeated. That last input makes the
  exact output nearly as large as any input at most 1 in size can, once per period (worked out
  outside Lean, not proved).
- Every output is compared with the same filter run on the same stored coefficients, starting
  state and inputs in double-double arithmetic (about 106 bits), standing in for the exact
  arithmetic the theorems compare against. That reference's own error is estimated to be below
  about 10⁻²⁰ (worked out outside Lean, not proved): each double-double operation is within a few
  units of 2⁻¹⁰⁴ (about 10⁻³¹) of its exact result, relative to its size; there are at most 16
  operations per sample; the values are at most about 10³ in size; and the largest error gain of
  these filters, from an error in the state to the output, is below about 10⁶ (about 6.4 × 10⁵
  for the f64 biquad at 10 Hz, the largest here).
- The gain ramp's gains are read by ramping a block of ones and compared with the exact line
  `S + (E - S)·i/n`, for 14 pairs of `start` and `end` (6 chosen, 8 random in [−2, 2)) and
  block lengths 3, 64, 1,000, 4,096, 48,000 and 2²⁰.

For the filters, the proved bound is the value shown in the tables above (each theorem proves
the bound is at most that value), and the ratio is that bound divided by the largest observed
error. The last column names the input that gave the largest error.

| Filter | Case | Proved bound | Largest observed error | Ratio | Input |
|---|---|---|---|---|---|
| one-pole | f32, `a` = 0.5 | 3.6 × 10⁻⁷ | 1.2 × 10⁻⁷ | 3.1 | uniform random |
| one-pole | f32, `a` = −0.5 (same theorem) | 3.6 × 10⁻⁷ | 1.2 × 10⁻⁷ | 3.1 | uniform random |
| one-pole | f32, `a` = 0.99 | 1.19 × 10⁻³ | 3.8 × 10⁻⁴ | 3.1 | step |
| one-pole | f32, `a` = −0.99 (same theorem) | 1.19 × 10⁻³ | 3.8 × 10⁻⁴ | 3.1 | alternating ±1 |
| one-pole | f32, `a` = 0.999 | 0.12 | 0.031 | 3.9 | step |
| one-pole | f64, `a` = 0.99 | 2.21 × 10⁻¹² | 7.1 × 10⁻¹³ | 3.1 | step |
| one-pole | f64, `a` = −0.99 (same theorem) | 2.21 × 10⁻¹² | 7.1 × 10⁻¹³ | 3.1 | alternating ±1 |
| one-pole | f64, `a` = 0.999 | 2.22 × 10⁻¹⁰ | 5.7 × 10⁻¹¹ | 3.9 | step |
| smoother | f32, `a` = 0.99 | 6.2 × 10⁻⁶ | 3.0 × 10⁻⁶ | 2.1 | step |
| smoother | f32, `a` = 0.999 | 6 × 10⁻⁵ | 3.0 × 10⁻⁵ | 2.0 | step |
| smoother | f64, `a` = 0.99 | 1.16 × 10⁻¹⁴ | 5.4 × 10⁻¹⁵ | 2.1 | step |
| smoother | f64, `a` = 0.999 | 1.12 × 10⁻¹³ | 5.5 × 10⁻¹⁴ | 2.0 | step |
| biquad | f32, 100 Hz | 17.1 | 1.8 × 10⁻⁴ | 97,000 | impulse-response signs |
| biquad | f32, 250 Hz | 0.979 | 6.1 × 10⁻⁵ | 16,000 | impulse-response signs |
| biquad | f32, 1 kHz | 0.0542 | 7.1 × 10⁻⁶ | 7,600 | step |
| biquad | f32, 10 kHz | 1.81 × 10⁻⁴ | 1.5 × 10⁻⁷ | 1,200 | uniform random |
| biquad | f32, 20 kHz | 0.0128 | 5.1 × 10⁻⁷ | 25,000 | random ±1 |
| biquad | f32, 1 kHz, `Q` = 0.4 | 0.00559 | 1.6 × 10⁻⁶ | 3,600 | step |
| biquad | f32, 1 kHz, `Q` = 0.5, `closePolesContraction` | 0.0122 | 2.1 × 10⁻⁶ | 5,900 | random ±1 |
| biquad | f32, 1 kHz, `Q` = 0.5, `realPolesContraction` | 734 | 2.1 × 10⁻⁶ | 3.5 × 10⁸ | random ±1 |
| biquad | f64, 10 Hz | 1.02 × 10⁻⁶ | 1.9 × 10⁻¹⁰ | 5,200 | step |
| biquad | f64, 100 Hz | 1.02 × 10⁻⁸ | 1.3 × 10⁻¹² | 7,600 | step |
| biquad | f64, 1 kHz | 1.01 × 10⁻¹⁰ | 7.4 × 10⁻¹⁵ | 14,000 | step |
| biquad | f64, 10 kHz | 3.37 × 10⁻¹³ | 3.1 × 10⁻¹⁶ | 1,100 | random ±1 |
| biquad | f64, 1 kHz, `Q` = 0.4 | 1.04 × 10⁻¹¹ | 3.0 × 10⁻¹⁵ | 3,500 | step |
| SVF | f32, 20 Hz | 0.0126 | 5.6 × 10⁻⁵ | 220 | step |
| SVF | f32, 100 Hz | 0.00267 | 4.2 × 10⁻⁶ | 640 | step |
| SVF | f32, 1 kHz | 0.000459 | 5.7 × 10⁻⁷ | 800 | impulse-response signs |
| SVF | f32, 10 kHz | 0.000475 | 4.9 × 10⁻⁷ | 980 | random ±1 |
| SVF | f64, 20 Hz | 2.35 × 10⁻¹¹ | 7.0 × 10⁻¹⁴ | 340 | step |
| SVF | f64, 100 Hz | 4.98 × 10⁻¹² | 6.3 × 10⁻¹⁵ | 790 | step |
| SVF | f64, 1 kHz | 8.55 × 10⁻¹³ | 1.0 × 10⁻¹⁵ | 840 | impulse-response signs |
| SVF | f64, 10 kHz | 8.84 × 10⁻¹³ | 7.9 × 10⁻¹⁶ | 1,100 | uniform random |

For the gain ramp the bound `u·\|S\| + 5u·\|E - S\| + (2n + 4)·η` depends on `start`, `end`
and the block length, so the table gives the largest error seen over all cases, the bound for
the case where it was seen, and their ratio; and, separately, the smallest ratio of bound to
error over every gain of every case.

| Precision | Largest observed error | Bound there | Ratio there | Smallest ratio over all gains |
|---|---|---|---|---|
| f32 | 2.8 × 10⁻⁷ | 8.9 × 10⁻⁷ | 3.2 | 1.7 |
| f64 | 3.0 × 10⁻¹⁶ | 1.7 × 10⁻¹⁵ | 5.5 | 1.7 |

Also measured, not proved:

- The fused functions (`process_fma_*`), which have the same proved bounds, gave the same or
  smaller largest errors in every row, each below its bound. With inputs of ±1 the fused and
  unfused biquads give the same outputs, since every product with the input is then exact
  (worked out outside Lean, not proved).
- The biquad bounds are the loosest, as the paragraph after the biquad examples above expects.

## What is assumed, not proved

- Charon and Aeneas translate the Rust code into Lean faithfully.
- Aeneas's float model (from the pinned `conjure` commit) has a single NaN, like Lean's own float
  model. Reading a NaN's sign or bits (`to_bits`, `is_sign_negative`, `is_sign_positive`, and
  `copysign` with a NaN sign) fails in the model (as a panic would), so a proof that code returns
  a value also proves that it never reads a NaN's sign or bits. Theorems here still compare
  floats with Lean's `=`, which counts all NaNs as equal; no theorem here states anything about
  NaN bit patterns or NaN signs, and the axiom check rejects any public theorem statement that
  names a NaN constant or one of the model's NaN-bits helpers (it sees only names written in the
  statement).
  `min`/`max` of +0 and −0 may return either; Rust leaves this open too, and the model does not
  let a proof depend on which. No proof here relies on which zero `min`/`max` returns.
- Not modelled: `sin`, `exp` and other transcendental functions from Rust's standard library,
  and the `NAN` constant. This crate uses none of them.
- The crate's one dependency, `libm` 0.2.16 (a pure-Rust port of the musl and FreeBSD maths
  libraries, pinned exactly, default features off), is not translated. Its `tan`, `pow` and
  `sqrt` (and the binary32 `tanf`, `powf` and `sqrtf`) are modelled in the hand-written
  `Code/FunsExternal.lean` as unknown functions that always return a float and return the same
  float for the same arguments: `libm.tanModel_f64` and the others are Lean `opaque` constants,
  which no proof can look inside (they are not axioms). So the proofs assume that these functions
  never panic, always return, and return the same float for the same arguments. The proofs hold
  whatever float they return, so they don't depend on their accuracy, which is not proved here
  either. Nothing about the frequency
  responses of the coefficients the SVF design functions compute is proved.
- The processor does `f32`/`f64` arithmetic in its default mode: round to nearest, with subnormal
  results kept (no flush-to-zero) and subnormal inputs read as they are (no denormals-are-zero),
  and in IEEE single and double precision (not x87 extended precision, as 32-bit x86 without SSE2
  can). Hosts and plug-ins often turn on flush-to-zero; with it on, results near zero can differ
  from the model by more than `η`, and the error bounds are not proved for that mode. Which
  theorems would still describe the processor in that mode, and what proving bounds for it would
  take, is in the design note [`notes/flush-to-zero.md`](notes/flush-to-zero.md) (worked out
  outside Lean, not proved).
- Rust's `f32`/`f64` operations and Lean's `Float32`/`Float` operations are the same IEEE 754
  round-to-nearest operations. FloatLib relates Lean's floats to real numbers; nothing here
  verifies machine instructions or compiler optimizations. In particular, the proofs assume a
  separate multiply and add: Rust does not fuse `x + a * y` (or the smoother's
  `state + c * (x - state)`, or the biquad's `b0 * x + s1` and `b1 * x - a1 * y + s2`, or the
  SVF's `x - (k + g) * s1`, `1 + g * (g + k)`, `g * hp + s1`, `g * bp + s2`, `g * hp + bp`,
  `g * bp + lp` and its output mix, or the first-order all-pass's `c * (x - y1) + x1`, or the
  linear smoother's `target - step * (remaining as f64)`, or the interpolated delay read's
  weighted sum `((wm1 * xm1 + w0 * x0) + w1 * x1) + w2 * x2`) into one multiply-add instruction
  unless the code asks for `mul_add`, and the unfused functions do not.
- Aeneas translates Rust's `as usize` on a float to `Float.toUScalar .Usize` /
  `Float32.toUScalar .Usize`, Lean's conversion with Rust's rules: round toward zero, NaN to 0,
  and saturate at the largest `usize`. This is trusted, as the rest of the translation is; it is
  the crate's first conversion from a float to an integer (in `delay::read_interp_*`).
  `toUScalar_usize_val_f64` / `_f32` prove what Lean's conversion gives for finite floats.
- The fused functions (`*_fma_*`, the `std` feature) do ask for it. For them the proofs assume
  that Rust's `f64::mul_add` / `f32::mul_add` computes IEEE 754's fused multiply-add, `a·b + c`
  rounded once to nearest, the operation of Lean's `Float.fma` / `Float32.fma` that Aeneas
  translates it to; done by the processor's instruction, or by the platform's software `fma`
  routine where there is none. That this grouping is the one clang chooses is worked out outside
  Lean, not proved.
- For the smoother (`smoother::*`), the floating-point error bound is proved, under the
  conditions above, against the exact smoother with the stored coefficient `c = 1 - a`
  (`process_f64_block_error`, `process_f32_block_error` and their `_of_inputs` forms). In
  floating point the smoother need not land exactly on a steady input `X`; what is proved is how
  far off it can be: after `n` samples, within `|A|^n·|S - X| + E` of `X`
  (`process_f64_settle_of_inputs`, `process_f32_settle_of_inputs`), with `E` at most the bounds
  shown for the values of `a` in the smoother table above, inputs at most 1 and a start from 0.
  The theorems in `Smoother/Exact.lean` are in exact arithmetic only.
- Not proved for the smoother: how much the exact smoother's outputs change when its coefficient
  is the rounded `c` rather than `1 - a` (this matters only when the value of `a` is outside 1/2
  to 2, where `c` can be rounded; `coeff_f64_error` / `coeff_f32_error` bound only the
  coefficient itself), how close to `X` the state actually comes to rest (only the upper bound
  is proved), and how `E` grows as `A` approaches 1.
- For the first-order all-pass (`allpass1::*`), the floating-point error bound is proved, under
  the conditions above, against the exact filter with the stored coefficient. Not proved: its
  frequency response (the same level at every frequency; measured at five frequencies by the
  crate's tests, not proved), that `coeff_*` gives a phase shift of 90° at the corner
  frequency, and that it gives `|c| < 1` for corner frequencies between 0 and half the sample
  rate (standard results, not proved in Lean; `coeff_*` depends on libm's `tan`, outside the
  model).
- For the interpolated delay read (`delay::read_interp_*`), what the code computes is proved
  exactly, and the size of the exact formula (`delay.lagrange4_real_abs_le`). Not proved: a bound
  on the rounded result's size or on its distance from the exact formula, and that the formula is
  the cubic through the four samples (worked out outside Lean, not proved). In `f32` the theorems
  about the fraction and whole-number delays need a buffer of at most `2^24` samples.
- For the state-variable filter (`svf::*`), the floating-point error bound is proved, under the
  conditions in the table above, for any stored coefficients for which an `svf.Contraction` of the
  state-update map is given (`svf.process_f64_block_error`, `svf.process_f32_block_error` and their
  `_of_inputs` forms), provided a number `Sb` with `cInf·(R + Ê) ≤ Sb` exists. One is supplied for
  complex poles (`svf.complexPolesContraction`: `d > 0`, `g·k > 0` and `k² < 4·(1/d − g·(g + k))`),
  and any biquad `Contraction` of `svf.poleBiquad` gives one (`svf.ofBiquad`, when `g·d ≠ 0`), whose
  `cInf` is the biquad's `cInf` times `1 + (1 + |A₂₂|)/|A₁₂|`, a factor that grows like `1/(g·d)`
  as `g` shrinks (the growth worked out outside Lean, not proved). Worked examples are proved only
  for the low-pass values in the SVF table above, whose stored coefficients are worked out outside
  Lean, not proved.
- Not proved for the state-variable filter: its frequency response, or that it equals any biquad's;
  stability for all coefficients, including that the coefficients the design functions compute meet
  the conditions above at every cutoff (they depend on libm's `tan`, outside the model); and that
  the code matches Zavalishin's filter. Nor, for the design functions (`low_pass` to `high_shelf`),
  whose names and formulas follow A. Simper (Cytomic), that the coefficients give the named
  responses.
- The biquad's whole-block error bound is proved for any given `Contraction` of its state-update
  map. One is supplied for complex poles inside the unit circle (`complexPolesContraction`), for
  distinct real poles inside it (`realPolesContraction`, for example an RBJ low-pass with
  `Q < 1/2`, worked out outside Lean, not proved), for a repeated real pole inside it
  (`repeatedPoleContraction`), and for poles close together, real or complex, when
  `|a1|/2 + max(ε, |a1²/4 − a2|/ε) < 1` for a chosen `ε > 0` (`closePolesContraction`). None is
  supplied when a pole is on or outside the unit circle, and when 1 is a pole none exists
  (`isEmpty_contraction_of_pole_one`; one case is proved for specific stored values: the binary32
  coefficients in `lowPass1Hz_f32`, which are those of a 1 Hz Butterworth low-pass at 48 kHz
  (worked out outside Lean, not proved), have a pole at exactly 1, `lowPass1Hz_pole_one_f32`).
- Real poles that are distinct but close together have a large `cInf = 1/(p − q)` in
  `realPolesContraction` (above 2700 for an RBJ low-pass with `Q = 1/2` in f32 at 1 kHz,
  `lowPass1kHzQ05_bound_f32`), and `repeatedPoleContraction` needs exactly equal poles.
  `closePolesContraction` has `cInf = 1/ε` for the chosen `ε`, whatever the distance between the
  poles (worked out outside Lean, not proved: its condition `ρ < 1` needs `|p| + √|δ| < 1`, with
  `p = −a1/2` and `δ = a1²/4 − a2`, which for complex poles is stricter than both poles being
  inside the unit circle, and `cInf = 1/ε` is always above `1/(1 − |p|)`); for that filter,
  with `ε = 0.06`, `M = 1` (inputs at most 1 in size) and a start from zero, it gives a bound on
  each output's error of at most 0.0122, against at most 734 (`lowPass1kHzQ05_bounds_f32`,
  `lowPass1kHzQ05_bound_f32`). Not proved: which `ε` gives the
  smallest bound, or how close the bound is to the filter's actual largest error.
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
- One file per Rust module while it has one proof file; a folder once it has more (`OnePole/`,
  `Gain/`). Inside a folder: `SpecF64.lean`/`SpecF32.lean` say what the translated code
  computes; `BridgeF64.lean`/`BridgeF32.lean` relate one step to real numbers; `Block.lean` holds
  the whole-block argument on real numbers only, shared by both precisions, and
  `BlockF64.lean`/`BlockF32.lean` apply it to the Rust functions; `Exact.lean` (real numbers
  only, `OnePole/`, `Smoother/`) proves what the filter does in exact arithmetic;
  `Textbook.lean` (real numbers only) shows the code's form of a filter equals the textbook formula;
  `Contraction.lean` (real numbers only) builds a `Contraction` for biquads with complex poles,
  distinct real poles or a repeated real pole inside the unit circle, or with poles close together
  when its `ρ < 1`
  (`Biquad/`), or for the SVF with complex poles or from a biquad one (`Svf/`); `Basic.lean`
  (`Delay/`) holds facts about lists, natural numbers and Aeneas's `Result` that both precisions'
  files use; `Line.lean` (real numbers only, `Gain/`) holds the gain ramp's straight line and the
  error of one ramp gain and of the step, shared by both precisions' `Bridge` files.
- Names: Lean names about one precision end in `_f64` or `_f32`, like the Rust names
  (`filt_f64`, `real_f32`, `NoOverflow_f64`), and the filter functions keep the `filt_` prefix
  (`filt_real`). Otherwise Lean names follow Mathlib: definitions that are statements start with
  a capital (`WithinStepErr`), other definitions are lowerCamelCase (`stepErr`), and theorems are
  snake case, keeping the casing of any definition they mention, except that a capitalized one
  starts lowercase (`filt_f64_withinStepErr`, `noOverflow_f64_of_inputs`).
- `FmaFacts.lean` relates Lean's `Float.fma` / `Float32.fma` to FloatLib's rounding (one
  rounding of `x·y + z`), with its error bound and finiteness, and holds the facts about exact
  negation the fused filters use. `OnePole/FmaF64.lean`, `Smoother/FmaF64.lean`,
  `Biquad/FmaF64.lean`, `Svf/FmaF64.lean` and their `F32` versions prove the fused functions'
  spec, whole-block bounds and the smoother's settling bounds; `Biquad/Fma.lean` and
  `Svf/Fma.lean` (real numbers only) give a fused step the unfused step's bounds.
- `Allpass1/` (the first-order all-pass) has `SpecF64.lean`/`SpecF32.lean`, `Block.lean` (real
  numbers only) and `BlockF64.lean`/`BlockF32.lean`. Unlike the other filters, it has no
  separate `Fma` files: the fused functions' spec theorems are in the `Spec` files, the real-number
  fact that a fused step meets the unfused step's bound (`stepErr_of_roundings_fma`) is in
  `Block.lean`, and their per-step and whole-block bounds are in the `Block` files.
- `LinearSmoother/` has `SpecF64.lean`/`SpecF32.lean` (what the translated code computes,
  landing included) and `BridgeF64.lean`/`BridgeF32.lean` (the distance of each value from the
  straight line, reusing `gain.ramp_error_real` from `Gain/Line.lean`). It also reuses
  `delay.exists_ok_of_spec` from `Delay/Basic.lean`.
- `Delay/Interp.lean` holds the index facts of the interpolated read shared by both precisions
  and the exact-arithmetic size of its formula (`delay.lagrange4_real_abs_le`);
  `Delay/InterpF64.lean`/`InterpF32.lean` prove what `read_interp_f64`/`_f32` compute.
- `Cast.lean` relates Lean's conversion of a float to `usize` (Rust's `as usize`) to the float's
  real value (`toUScalar_usize_val_f64` / `_f32`).
- `FloatFacts.lean` holds facts about floats shared by every module's proofs, including
  `real_f64` / `real_f32` (the exact real value of a float), the size of one rounding, and how
  infinity, NaN and signed zeros pass through one operation.
- `TwoState.lean` (real numbers only) holds what the biquad's and the SVF's whole-block arguments
  share: `two_state.Contraction`, the `Contraction` structure for a filter with two state values
  and any 2 × 2 state-update matrix (`biquad.Contraction` is it at the companion matrix
  `(−a1, 1; −a2, 0)`, `svf.Contraction` at the SVF's `A`), and the facts about it that both
  use.
- `notes/` (in `proofs/`, outside the Lean library) holds design notes, which prove nothing:
  `notes/flush-to-zero.md`, on the flush-to-zero and denormals-are-zero modes.
