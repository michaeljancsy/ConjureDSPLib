//! One-pole feedback filter: `y[n] = x[n] + a * y[n-1]`.
//!
//! The previous output `y[n-1]` is the filter's state, kept by the caller and carried from block
//! to block. The filter is stable when `|a| < 1`.
//!
//! **Gain.** This is the unnormalized form: a constant input `x` settles at `x / (1 - a)`, not at
//! `x`. With `a = 0.99` a constant 1.0 settles at 100. To smooth towards a target value, use
//! `smooth_f64` / `smooth_f32` (one sample: `smooth_step_f64` / `smooth_step_f32`), which settle
//! on the target itself.
//!
//! **Subnormals.** A decaying output drifts into subnormal numbers, which are slow on some
//! processors. This module does nothing about that: flushing subnormals to zero is the caller's
//! job.
//!
//! Call these through the module, as `one_pole::process_f32` or `one_pole::smooth_f32`.

/// One sample of the filter, in `f64`: the new output from the input `x` and the previous
/// output `state`.
#[inline]
pub fn step_f64(a: f64, state: f64, x: f64) -> f64 {
    x + a * state
}

/// Filters `buf` in place, in `f64`, starting from `state` (the previous output) and leaving the
/// last output in `state`. An empty block leaves `state` unchanged.
pub fn process_f64(a: f64, state: &mut f64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = step_f64(a, *state, buf[i]);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

/// One sample of the smoother, in `f64`: moves `state` (the previous output) the fraction
/// `1 - a` of the way towards `target`, returning `state + (1 - a) * (target - state)`.
///
/// A steady target settles on itself, unlike `process_f64`, which settles at `x / (1 - a)`. `a`
/// near 1 is a slow glide; `a = 0` jumps straight to the target. It is stable for `0 <= a < 1`.
/// In exact arithmetic it is the same filter as `step_f64` fed `(1 - a) * target`; in floating
/// point the results can differ, because the operations are done in a different order.
#[inline]
pub fn smooth_step_f64(a: f64, state: f64, target: f64) -> f64 {
    state + (1.0 - a) * (target - state)
}

/// Smooths `buf` in place, in `f64`, starting from `state` (the previous output) and leaving the
/// last output in `state`. Each sample is the target for that sample:
/// `y = state + (1 - a) * (x - state)`, with `1 - a` computed once per block. An empty block
/// leaves `state` unchanged.
///
/// A steady input settles on itself, unlike `process_f64`, which settles at `x / (1 - a)`. `a`
/// near 1 is a slow glide. It is stable for `0 <= a < 1`. In exact arithmetic it is the same
/// filter as `process_f64` with each input first multiplied by `1 - a`; in floating point the
/// results can differ.
pub fn smooth_f64(a: f64, state: &mut f64, buf: &mut [f64]) {
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

/// One sample of the filter, in `f32`: the new output from the input `x` and the previous
/// output `state`.
#[inline]
pub fn step_f32(a: f32, state: f32, x: f32) -> f32 {
    x + a * state
}

/// Filters `buf` in place, in `f32`, starting from `state` (the previous output) and leaving the
/// last output in `state`. An empty block leaves `state` unchanged.
pub fn process_f32(a: f32, state: &mut f32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = step_f32(a, *state, buf[i]);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

/// One sample of the smoother, in `f32`: moves `state` (the previous output) the fraction
/// `1 - a` of the way towards `target`, returning `state + (1 - a) * (target - state)`.
///
/// A steady target settles on itself, unlike `process_f32`, which settles at `x / (1 - a)`. `a`
/// near 1 is a slow glide; `a = 0` jumps straight to the target. It is stable for `0 <= a < 1`.
/// In exact arithmetic it is the same filter as `step_f32` fed `(1 - a) * target`; in floating
/// point the results can differ, because the operations are done in a different order.
#[inline]
pub fn smooth_step_f32(a: f32, state: f32, target: f32) -> f32 {
    state + (1.0 - a) * (target - state)
}

/// Smooths `buf` in place, in `f32`, starting from `state` (the previous output) and leaving the
/// last output in `state`. Each sample is the target for that sample:
/// `y = state + (1 - a) * (x - state)`, with `1 - a` computed once per block. An empty block
/// leaves `state` unchanged.
///
/// A steady input settles on itself, unlike `process_f32`, which settles at `x / (1 - a)`. `a`
/// near 1 is a slow glide. It is stable for `0 <= a < 1`. In exact arithmetic it is the same
/// filter as `process_f32` with each input first multiplied by `1 - a`; in floating point the
/// results can differ.
pub fn smooth_f32(a: f32, state: &mut f32, buf: &mut [f32]) {
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
    macro_rules! one_pole_tests {
        ($name:ident, $t:ty, $step:ident, $process:ident, $smooth_step:ident, $smooth:ident) => {
            mod $name {
                use super::*;

                #[test]
                fn impulse_response_is_powers_of_a() {
                    let mut state: $t = 0.0;
                    let mut buf: [$t; 4] = [1.0, 0.0, 0.0, 0.0];
                    $process(0.5, &mut state, &mut buf);
                    assert_eq!(buf, [1.0, 0.5, 0.25, 0.125]);
                    assert_eq!(state, 0.125);
                }

                #[test]
                fn starting_state_and_negative_coefficient() {
                    // Exact in binary: 1 + (-0.5)(2) = 0, 0.5 + (-0.5)(0) = 0.5, ...
                    let mut state: $t = 2.0;
                    let mut buf: [$t; 3] = [1.0, 0.5, 0.25];
                    $process(-0.5, &mut state, &mut buf);
                    assert_eq!(buf, [0.0, 0.5, 0.0]);
                    assert_eq!(state, 0.0);
                }

                #[test]
                fn state_carries_across_blocks() {
                    let input: [$t; 5] = [1.0, 2.0, 3.0, 4.0, 5.0];
                    let mut whole = input;
                    let mut s1: $t = 0.25;
                    $process(0.75, &mut s1, &mut whole);

                    let mut split = input;
                    let mut s2: $t = 0.25;
                    let (first, second) = split.split_at_mut(2);
                    $process(0.75, &mut s2, first);
                    $process(0.75, &mut s2, second);

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
                    let a: $t = 0.9;
                    let input: [$t; 5] = [0.1, -0.2, 0.3, 1.0, -1.0];
                    let mut buf = input;
                    let mut state: $t = -0.5;
                    $process(a, &mut state, &mut buf);
                    let mut y: $t = -0.5;
                    for (out, x) in buf.iter().zip(input) {
                        y = $step(a, y, x);
                        assert_eq!(*out, y);
                    }
                    assert_eq!(state, y);
                }

                #[test]
                fn smooth_settles_on_a_steady_input() {
                    // Exact in binary with a = 0.5: each step halves the distance to 1.
                    let mut state: $t = 0.0;
                    let mut buf: [$t; 4] = [1.0; 4];
                    $smooth(0.5, &mut state, &mut buf);
                    assert_eq!(buf, [0.5, 0.75, 0.875, 0.9375]);
                    assert_eq!(state, 0.9375);

                    // Long enough, it lands exactly on the input.
                    let mut buf: [$t; 200] = [1.0; 200];
                    $smooth(0.5, &mut state, &mut buf);
                    assert_eq!(state, 1.0);
                }

                #[test]
                fn smooth_state_carries_across_blocks() {
                    let input: [$t; 5] = [1.0, 2.0, 3.0, 4.0, 5.0];
                    let mut whole = input;
                    let mut s1: $t = 0.25;
                    $smooth(0.9, &mut s1, &mut whole);

                    let mut split = input;
                    let mut s2: $t = 0.25;
                    let (first, second) = split.split_at_mut(2);
                    $smooth(0.9, &mut s2, first);
                    $smooth(0.9, &mut s2, second);

                    assert_eq!(whole, split);
                    assert_eq!(s1, s2);
                }

                #[test]
                fn smooth_empty_block_leaves_state_alone() {
                    let mut state: $t = 0.3;
                    $smooth(0.9, &mut state, &mut []);
                    assert_eq!(state, 0.3);
                }

                #[test]
                fn smooth_matches_smooth_step() {
                    let a: $t = 0.99;
                    let input: [$t; 5] = [0.1, -0.2, 0.3, 1.0, -1.0];
                    let mut buf = input;
                    let mut state: $t = -0.5;
                    $smooth(a, &mut state, &mut buf);
                    let mut y: $t = -0.5;
                    for (out, x) in buf.iter().zip(input) {
                        y = $smooth_step(a, y, x);
                        assert_eq!(out.to_bits(), y.to_bits());
                    }
                    assert_eq!(state.to_bits(), y.to_bits());
                }

                #[test]
                fn smooth_matches_reference_bit_for_bit() {
                    // Inexact values: compare with the formula written out, one rounding at a
                    // time in the stated order.
                    let a: $t = 0.7;
                    let input: [$t; 6] = [0.1, 0.2, -0.3, 1.0 / 3.0, 2.5, -7.1];
                    let mut buf = input;
                    let mut state: $t = 0.05;
                    $smooth(a, &mut state, &mut buf);
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

    one_pole_tests!(
        f64_tests,
        f64,
        step_f64,
        process_f64,
        smooth_step_f64,
        smooth_f64
    );
    one_pole_tests!(
        f32_tests,
        f32,
        step_f32,
        process_f32,
        smooth_step_f32,
        smooth_f32
    );
}
