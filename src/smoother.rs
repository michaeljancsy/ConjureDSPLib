//! One-pole smoother: `y[n] = y[n-1] + (1 - a) * (x[n] - y[n-1])`.
//!
//! Each step moves the state (the previous output `y[n-1]`, kept by the caller and carried from
//! block to block) the fraction `1 - a` of the way toward the input. `a` near 1 is a slow glide;
//! a common choice is `a = exp(-1 / (time_constant_seconds * sample_rate))` (computed by the
//! caller).
//!
//! **Settling.** In exact arithmetic, with `|a| < 1`, a steady input settles on itself, unlike
//! `one_pole::process_*`, which settles at `x / (1 - a)` (`smoother.tendsto_filt_real_replicate`,
//! `one_pole.tendsto_filt_real_replicate`).
//! In floating point the state comes to rest close to the input but not always exactly on it,
//! because with `a` near 1 the last steps round away (worked out outside Lean, not proved; only an
//! upper bound on how far off it can be is proved), so do not test `state == target`.
//!
//! How far off it can be is proved in Lean (`smoother.process_f64_settle_of_inputs`,
//! `smoother.process_f32_settle_of_inputs`), under the assumptions in `proofs/README.md`. Let
//! `c = 1.0 - a` as computed (exactly `1 - a` when `0.5 <= a <= 2`, `smoother.coeff_f64_exact`,
//! `smoother.coeff_f32_exact`) and `A = 1 - c`. If `a`, the starting state `start` and `x` are
//! finite, `|a| <= 1`, `A` passes the stability condition `|A| + errGrowth A u < 1` (in
//! `proofs/README.md`), which implies `|A| < 1`, and, for a bound
//! `M >= |x|`, an explicit size condition on `M`, the start and `E` (given in `proofs/README.md`)
//! holds, then after `n` samples of `x` the state is within `|A|^n * |start - x| + E` of `x`,
//! where `E` is a rounding bound given there. For example, with `a = 0.999`, `|x| <= 1` and
//! `start = 0`, `E <= 1.12e-13` in `f64` and `E <= 6e-5` in `f32`, and the stability and size
//! conditions hold (`smoother.table_row_le_of_le_0999_f64`, `sizeCondition_of_le_0999_f64` and
//! their `f32` versions; this uses the value each precision stores for 0.999, worked out outside
//! Lean, not proved).
//!
//! **Stability.** In exact arithmetic it is stable for `|a| < 1`: with every input at most `M` in
//! size, every output is at most `|state| + |1 - a| * M / (1 - |a|)` in size, where `state` is the
//! starting state (`smoother.filt_real_abs_le_outBound`). For a steady target `X` from state `r`,
//! output `k` is `X + a^(k+1) * (r - X)` (`smoother.filt_real_replicate`). So, in exact
//! arithmetic, `0 <= a < 1` gives a glide with no overshoot: each output lies between `X` and `r`
//! and is no farther from `X` than the one before (`smoother.replicate_output_between`,
//! `smoother.replicate_output_closer`).
//! And `a < 0` makes it alternate around the target, unless the state is already on it:
//! consecutive outputs are on opposite sides of `X` (`smoother.replicate_output_alternates`).
//!
//! **Subnormals.** A state decaying toward 0 drifts into subnormal numbers, which are slow on
//! some processors (the drift worked out outside Lean, not proved; the slowness a hardware fact).
//! This module does nothing about that: flushing subnormals to zero is the caller's job (if the
//! caller turns on the processor's flush-to-zero mode, the error bounds are not proved for that
//! mode; see `proofs/README.md`).
//!
//! **Relation to the one-pole filter.** In exact arithmetic it is the same filter as
//! `one_pole::step_*` fed `(1 - a) * target` (`smoother.filt_real_eq_one_pole_filt_real`); in
//! floating point the results can differ (different operation order; worked out outside Lean,
//! not proved).
//!
//! **With the coefficient given directly.** `step_coeff_*` and `process_coeff_*` take the
//! fraction `c` itself instead of `a`, and compute `state + c * (target - state)` with `c` as
//! given, so no `1 - a` is rounded inside (`smoother.step_coeff_f64_eq`,
//! `smoother.process_coeff_f64_spec`). With `c = 1.0 - a` they give exactly the results of
//! `step_*` and `process_*` (`smoother.step_f64_eq_step_coeff`,
//! `smoother.process_f64_eq_process_coeff`). The whole-block error and settling bounds above hold
//! for `process_coeff_*` with `C` the value of the given `c` and `A = 1 - C`
//! (`smoother.process_coeff_f64_block_error`, `smoother.process_coeff_f64_block_error_of_inputs`,
//! `smoother.process_coeff_f64_settle_of_inputs`, and their `f32` versions).
//!
//! Call these through the module, as `smoother::process_f32` or `smoother::process_coeff_f64`.

/// One sample of the smoother, in `f64`: moves `state` (the previous output) the fraction
/// `1 - a` of the way toward `target`, returning `state + (1.0 - a) * (target - state)`, computed
/// in that order.
#[inline]
pub fn step_f64(a: f64, state: f64, target: f64) -> f64 {
    state + (1.0 - a) * (target - state)
}

/// Smooths `buf` in place, in `f64`, starting from `state` (the previous output) and leaving the
/// last output in `state`. Each sample is the target for that sample: with `c = 1.0 - a`
/// computed once per block, `y = state + c * (x - state)`. An empty block leaves `state`
/// unchanged (`smoother.process_f64_spec`).
pub fn process_f64(a: f64, state: &mut f64, buf: &mut [f64]) {
    let c = 1.0 - a;
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = *state + c * (buf[i] - *state);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

/// One sample of the smoother, in `f32`: moves `state` (the previous output) the fraction
/// `1 - a` of the way toward `target`, returning `state + (1.0 - a) * (target - state)`, computed
/// in that order.
#[inline]
pub fn step_f32(a: f32, state: f32, target: f32) -> f32 {
    state + (1.0 - a) * (target - state)
}

/// Smooths `buf` in place, in `f32`, starting from `state` (the previous output) and leaving the
/// last output in `state`. Each sample is the target for that sample: with `c = 1.0 - a`
/// computed once per block, `y = state + c * (x - state)`. An empty block leaves `state`
/// unchanged (`smoother.process_f32_spec`).
pub fn process_f32(a: f32, state: &mut f32, buf: &mut [f32]) {
    let c = 1.0 - a;
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = *state + c * (buf[i] - *state);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

/// One sample of the smoother with the coefficient given directly, in `f64`: moves `state` (the
/// previous output) the fraction `c` of the way toward `target`, returning
/// `state + c * (target - state)`, computed in that order: the difference `target - state`, then
/// the product with `c`, then the sum, each rounded once (`smoother.step_coeff_f64_eq`). With
/// `c = 1.0 - a` it is exactly `step_f64(a, state, target)` (`smoother.step_f64_eq_step_coeff`).
#[inline]
pub fn step_coeff_f64(c: f64, state: f64, target: f64) -> f64 {
    state + c * (target - state)
}

/// Smooths `buf` in place, in `f64`, with the coefficient `c` given directly, starting from
/// `state` (the previous output) and leaving the last output in `state`. Each sample `x` is the
/// target for that sample: `y = state + c * (x - state)`, as in `step_coeff_f64`. An empty block
/// leaves `state` unchanged (`smoother.process_coeff_f64_spec`). With `c = 1.0 - a` it gives
/// exactly the outputs and state of `process_f64(a, ..)`
/// (`smoother.process_f64_eq_process_coeff`).
pub fn process_coeff_f64(c: f64, state: &mut f64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = *state + c * (buf[i] - *state);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

/// One sample of the smoother with the coefficient given directly, in `f32`: returns
/// `state + c * (target - state)`, computed in that order (`smoother.step_coeff_f32_eq`). With
/// `c = 1.0 - a` it is exactly `step_f32(a, state, target)` (`smoother.step_f32_eq_step_coeff`).
#[inline]
pub fn step_coeff_f32(c: f32, state: f32, target: f32) -> f32 {
    state + c * (target - state)
}

/// Smooths `buf` in place, in `f32`, with the coefficient `c` given directly, starting from
/// `state` and leaving the last output in `state`: `y = state + c * (x - state)` for each sample
/// `x`, as in `step_coeff_f32`. An empty block leaves `state` unchanged
/// (`smoother.process_coeff_f32_spec`). With `c = 1.0 - a` it gives exactly the outputs and state
/// of `process_f32(a, ..)` (`smoother.process_f32_eq_process_coeff`).
pub fn process_coeff_f32(c: f32, state: &mut f32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = *state + c * (buf[i] - *state);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! smoother_tests {
        (
            $name:ident,
            $t:ty,
            $step:ident,
            $process:ident,
            $step_coeff:ident,
            $process_coeff:ident
        ) => {
            mod $name {
                use super::*;

                #[test]
                fn settles_on_a_steady_input_with_a_half() {
                    // Exact in binary with a = 0.5: each step halves the distance to 1.
                    let mut state: $t = 0.0;
                    let mut buf: [$t; 4] = [1.0; 4];
                    $process(0.5, &mut state, &mut buf);
                    assert_eq!(buf, [0.5, 0.75, 0.875, 0.9375]);
                    assert_eq!(state, 0.9375);

                    // Long enough, it lands exactly on 1.0: with a = 0.5 the last step adds half
                    // the gap between 1.0 and the float just below it, a tie that rounds to the
                    // even neighbor, 1.0.
                    let mut buf: [$t; 200] = [1.0; 200];
                    $process(0.5, &mut state, &mut buf);
                    assert_eq!(state, 1.0);
                }

                #[test]
                fn slow_glide_comes_to_rest_just_below_the_target() {
                    // With a near 1, once the remaining gap times (1 - a) is less than half a
                    // float gap, each step rounds back to the same state: it stops short.
                    let a: $t = 0.9999;
                    let mut state: $t = 0.0;
                    for _ in 0..1000 {
                        let mut buf: [$t; 1000] = [1.0; 1000];
                        $process(a, &mut state, &mut buf);
                    }
                    assert!(state < 1.0);
                    assert!(1.0 - state <= <$t>::EPSILON / (1.0 - a));

                    // It has come to rest: more of the same input changes nothing.
                    let rest = state;
                    let mut buf: [$t; 1000] = [1.0; 1000];
                    $process(a, &mut state, &mut buf);
                    assert_eq!(state, rest);
                    assert!(buf.iter().all(|&y| y == rest));
                }

                #[test]
                fn state_carries_across_blocks() {
                    let input: [$t; 5] = [1.0, 2.0, 3.0, 4.0, 5.0];
                    let mut whole = input;
                    let mut s1: $t = 0.25;
                    $process(0.9, &mut s1, &mut whole);

                    let mut split = input;
                    let mut s2: $t = 0.25;
                    let (first, second) = split.split_at_mut(2);
                    $process(0.9, &mut s2, first);
                    $process(0.9, &mut s2, second);

                    assert_eq!(whole, split);
                    assert_eq!(s1, s2);
                }

                #[test]
                fn empty_block_leaves_state_alone() {
                    let mut state: $t = 0.3;
                    $process(0.9, &mut state, &mut []);
                    assert_eq!(state, 0.3);
                }

                #[test]
                fn process_matches_step() {
                    let a: $t = 0.99;
                    let input: [$t; 5] = [0.1, -0.2, 0.3, 1.0, -1.0];
                    let mut buf = input;
                    let mut state: $t = -0.5;
                    $process(a, &mut state, &mut buf);
                    let mut y: $t = -0.5;
                    for (out, x) in buf.iter().zip(input) {
                        y = $step(a, y, x);
                        assert_eq!(out.to_bits(), y.to_bits());
                    }
                    assert_eq!(state.to_bits(), y.to_bits());
                }

                #[test]
                fn process_matches_reference_bit_for_bit() {
                    // Inexact values: compare with the formula written out, one rounding at a
                    // time in the stated order.
                    let a: $t = 0.7;
                    let input: [$t; 6] = [0.1, 0.2, -0.3, 1.0 / 3.0, 2.5, -7.1];
                    let mut buf = input;
                    let mut state: $t = 0.05;
                    $process(a, &mut state, &mut buf);
                    let c: $t = 1.0 - a;
                    let mut y: $t = 0.05;
                    for (out, x) in buf.iter().zip(input) {
                        let d: $t = x - y;
                        let p: $t = c * d;
                        y += p;
                        assert_eq!(out.to_bits(), y.to_bits());
                    }
                    assert_eq!(state.to_bits(), y.to_bits());
                }

                #[test]
                fn coeff_versions_match_when_one_minus_a_is_exact() {
                    // For a between 1/2 and 2, `1.0 - a` is exactly 1 - a (Sterbenz's lemma), so
                    // passing c = 1 - a gives the same bits as passing a.
                    let input: [$t; 6] = [0.1, 0.2, -0.3, 1.0 / 3.0, 2.5, -7.1];
                    for a in [0.5 as $t, 0.75, 0.9, 0.99, 0.999, 1.0, 1.5] {
                        let c: $t = 1.0 - a;
                        let mut y: $t = 0.05;
                        for x in input {
                            let want = $step(a, y, x);
                            let got = $step_coeff(c, y, x);
                            assert_eq!(got.to_bits(), want.to_bits());
                            y = got;
                        }

                        let mut want = input;
                        let mut want_state: $t = 0.05;
                        $process(a, &mut want_state, &mut want);
                        let mut got = input;
                        let mut got_state: $t = 0.05;
                        $process_coeff(c, &mut got_state, &mut got);
                        for (g, w) in got.iter().zip(want) {
                            assert_eq!(g.to_bits(), w.to_bits());
                        }
                        assert_eq!(got_state.to_bits(), want_state.to_bits());
                    }
                }

                #[test]
                fn process_coeff_matches_reference_bit_for_bit() {
                    // The coefficient is used as given: no `1 - a` is computed.
                    let c: $t = 0.3;
                    let input: [$t; 6] = [0.1, 0.2, -0.3, 1.0 / 3.0, 2.5, -7.1];
                    let mut buf = input;
                    let mut state: $t = 0.05;
                    $process_coeff(c, &mut state, &mut buf);
                    let mut y: $t = 0.05;
                    for (out, x) in buf.iter().zip(input) {
                        let step = $step_coeff(c, y, x);
                        let d: $t = x - y;
                        let p: $t = c * d;
                        y += p;
                        assert_eq!(out.to_bits(), y.to_bits());
                        assert_eq!(step.to_bits(), y.to_bits());
                    }
                    assert_eq!(state.to_bits(), y.to_bits());
                }

                #[test]
                fn process_coeff_empty_block_leaves_state_alone() {
                    let mut state: $t = 0.3;
                    $process_coeff(0.1, &mut state, &mut []);
                    assert_eq!(state, 0.3);
                }
            }
        };
    }

    smoother_tests!(
        f64_tests,
        f64,
        step_f64,
        process_f64,
        step_coeff_f64,
        process_coeff_f64
    );
    smoother_tests!(
        f32_tests,
        f32,
        step_f32,
        process_f32,
        step_coeff_f32,
        process_coeff_f32
    );
}
