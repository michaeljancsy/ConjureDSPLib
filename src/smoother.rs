//! One-pole smoother: `y[n] = y[n-1] + (1 - a) * (x[n] - y[n-1])`.
//!
//! Each step moves the state (the previous output `y[n-1]`, kept by the caller and carried from
//! block to block) the fraction `1 - a` of the way toward the input. `a` near 1 is a slow glide;
//! a common choice is `a = exp(-1 / (time_constant_seconds * sample_rate))` (computed by the
//! caller).
//!
//! **Settling.** In exact arithmetic a steady input settles on itself (unlike
//! `one_pole::process_*`, which settles at `x / (1 - a)`). In floating point the state comes to
//! rest close to the input but not always exactly on it, because with `a` near 1 the last steps
//! round away, so do not test `state == target`. How far off it can be is proved in Lean
//! (`smoother.process_f64_settle_of_inputs` and `process_f32_settle_of_inputs`, in
//! `proofs/ConjureDSPLib/Smoother/`): if `a`, the starting state and the input `x` are finite,
//! `a` is at most 1 in size, `A = 1 - c` (with `c = 1.0 - a` as computed, which is exactly
//! `1 - a` when `0.5 <= a <= 2`) passes a stability condition slightly stricter than `|A| < 1`,
//! and an explicit size condition, far below the largest finite float, holds, then after `n`
//! samples of `x` the state is within `|A|^n * |start - x| + E` of `x`, where `start` is the
//! starting state and `E` is an explicit bound on the rounding given in `proofs/README.md`. For
//! example, for `a = 0.999`, `x` at most 1 in size and a start from 0, `E` is at most `1.12e-13`
//! in `f64` and `6e-5` in `f32`.
//!
//! **Stability.** In exact arithmetic it is stable for `|a| < 1`, and `0 <= a < 1` gives a glide
//! with no overshoot (`a < 0` makes it alternate around the target).
//!
//! **Subnormals.** A state decaying toward 0 drifts into subnormal numbers, which are slow on
//! some processors. This module does nothing about that: flushing subnormals to zero is the
//! caller's job.
//!
//! **Relation to the one-pole filter.** In exact arithmetic it is the same filter as
//! `one_pole::step_*` fed `(1 - a) * target`; in floating point the results can differ
//! (different operation order).
//!
//! Call these through the module, as `smoother::process_f32`.

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
/// unchanged.
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
/// unchanged.
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! smoother_tests {
        ($name:ident, $t:ty, $step:ident, $process:ident) => {
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
            }
        };
    }

    smoother_tests!(f64_tests, f64, step_f64, process_f64);
    smoother_tests!(f32_tests, f32, step_f32, process_f32);
}
