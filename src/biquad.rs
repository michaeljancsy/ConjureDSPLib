//! Biquad (second-order) filter, in transposed direct form II.
//!
//! With the coefficients normalized so that `a0 = 1`, the filter is the textbook recurrence
//!
//! `y[n] = b0·x[n] + b1·x[n-1] + b2·x[n-2] - a1·y[n-1] - a2·y[n-2]`.
//!
//! Transposed direct form II computes it with two state values per channel:
//!
//! ```text
//! y  = b0·x + s1
//! s1 = b1·x - a1·y + s2
//! s2 = b2·x - a2·y
//! ```
//!
//! In exact arithmetic the two forms give the same output; in floating point they round
//! differently. This module computes exactly the steps above, in that order (the same order as
//! a reference transposed-form biquad, so code can move onto it with bit-identical output).
//!
//! Designing coefficients (low-pass, shelf, ...) is not part of this module. The filter is stable
//! when both poles are inside the unit circle: `|a2| < 1` and `|a1| < 1 + a2`. Flushing
//! subnormal numbers to zero is the caller's job.
//!
//! Call these through the module, as `biquad::process_f32`.

/// Biquad coefficients in `f64`, normalized so that `a0 = 1`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CoeffsF64 {
    /// Feed-forward coefficient of `x[n]`.
    pub b0: f64,
    /// Feed-forward coefficient of `x[n-1]`.
    pub b1: f64,
    /// Feed-forward coefficient of `x[n-2]`.
    pub b2: f64,
    /// Feedback coefficient of `y[n-1]` (subtracted).
    pub a1: f64,
    /// Feedback coefficient of `y[n-2]` (subtracted).
    pub a2: f64,
}

/// The two state values of one biquad channel, in `f64`. Start from zero.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF64 {
    /// First state value.
    pub s1: f64,
    /// Second state value.
    pub s2: f64,
}

/// One sample of the filter, in `f64`: returns the output and updates `state`.
#[inline]
pub fn step_f64(c: &CoeffsF64, state: &mut StateF64, x: f64) -> f64 {
    let y = c.b0 * x + state.s1;
    state.s1 = c.b1 * x - c.a1 * y + state.s2;
    state.s2 = c.b2 * x - c.a2 * y;
    y
}

/// Filters `buf` in place, in `f64`, carrying `state` from block to block. An empty block leaves
/// `state` unchanged.
pub fn process_f64(c: &CoeffsF64, state: &mut StateF64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_f64(c, state, buf[i]);
        i += 1;
    }
}

/// Biquad coefficients in `f32`, normalized so that `a0 = 1`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CoeffsF32 {
    /// Feed-forward coefficient of `x[n]`.
    pub b0: f32,
    /// Feed-forward coefficient of `x[n-1]`.
    pub b1: f32,
    /// Feed-forward coefficient of `x[n-2]`.
    pub b2: f32,
    /// Feedback coefficient of `y[n-1]` (subtracted).
    pub a1: f32,
    /// Feedback coefficient of `y[n-2]` (subtracted).
    pub a2: f32,
}

/// The two state values of one biquad channel, in `f32`. Start from zero.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF32 {
    /// First state value.
    pub s1: f32,
    /// Second state value.
    pub s2: f32,
}

/// One sample of the filter, in `f32`: returns the output and updates `state`.
#[inline]
pub fn step_f32(c: &CoeffsF32, state: &mut StateF32, x: f32) -> f32 {
    let y = c.b0 * x + state.s1;
    state.s1 = c.b1 * x - c.a1 * y + state.s2;
    state.s2 = c.b2 * x - c.a2 * y;
    y
}

/// Filters `buf` in place, in `f32`, carrying `state` from block to block. An empty block leaves
/// `state` unchanged.
pub fn process_f32(c: &CoeffsF32, state: &mut StateF32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_f32(c, state, buf[i]);
        i += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! biquad_tests {
        ($name:ident, $t:ty, $coeffs:ident, $state:ident, $step:ident, $process:ident) => {
            mod $name {
                use super::*;

                // b = [0.5, 0.25, 0.125], a1 = -0.5, a2 = 0.25: exact in binary for short runs.
                const C: $coeffs = $coeffs {
                    b0: 0.5,
                    b1: 0.25,
                    b2: 0.125,
                    a1: -0.5,
                    a2: 0.25,
                };

                /// The textbook direct form I recurrence, for comparison.
                fn direct_form_1(c: &$coeffs, xs: &[$t]) -> [$t; 6] {
                    let mut out = [0.0; 6];
                    let (mut x1, mut x2, mut y1, mut y2): ($t, $t, $t, $t) = (0.0, 0.0, 0.0, 0.0);
                    for (o, &x) in out.iter_mut().zip(xs) {
                        let y = c.b0 * x + c.b1 * x1 + c.b2 * x2 - c.a1 * y1 - c.a2 * y2;
                        (x2, x1, y2, y1) = (x1, x, y1, y);
                        *o = y;
                    }
                    out
                }

                #[test]
                fn impulse_response_matches_textbook_recurrence() {
                    let mut buf: [$t; 6] = [1.0, 0.0, 0.0, 0.0, 0.0, 0.0];
                    let expected = direct_form_1(&C, &buf);
                    let mut state = $state::default();
                    $process(&C, &mut state, &mut buf);
                    assert_eq!(buf, expected);
                    // By hand: 0.5, 0.5, 0.25, 0, -0.0625, -0.03125.
                    assert_eq!(buf, [0.5, 0.5, 0.25, 0.0, -0.0625, -0.03125]);
                }

                #[test]
                fn identity_coefficients_pass_input_through() {
                    let id = $coeffs {
                        b0: 1.0,
                        b1: 0.0,
                        b2: 0.0,
                        a1: 0.0,
                        a2: 0.0,
                    };
                    let input: [$t; 4] = [0.3, -1.0, 2.5, 0.0];
                    let mut buf = input;
                    let mut state = $state::default();
                    $process(&id, &mut state, &mut buf);
                    assert_eq!(buf, input);
                }

                #[test]
                fn state_carries_across_blocks() {
                    let input: [$t; 7] = [1.0, -2.0, 0.5, 3.0, 0.0, -1.0, 0.25];
                    let mut whole = input;
                    let mut s1 = $state {
                        s1: 0.125,
                        s2: -0.25,
                    };
                    $process(&C, &mut s1, &mut whole);

                    let mut split = input;
                    let mut s2 = $state {
                        s1: 0.125,
                        s2: -0.25,
                    };
                    let (first, second) = split.split_at_mut(3);
                    $process(&C, &mut s2, first);
                    $process(&C, &mut s2, second);

                    assert_eq!(whole, split);
                    assert_eq!(s1, s2);
                }

                #[test]
                fn empty_block_leaves_state_alone() {
                    let mut state = $state { s1: 0.3, s2: -0.7 };
                    $process(&C, &mut state, &mut []);
                    assert_eq!(state, $state { s1: 0.3, s2: -0.7 });
                }

                #[test]
                fn process_matches_step() {
                    let input: [$t; 5] = [0.1, -0.2, 0.3, 1.0, -1.0];
                    let mut buf = input;
                    let mut state = $state { s1: -0.5, s2: 0.25 };
                    $process(&C, &mut state, &mut buf);
                    let mut s = $state { s1: -0.5, s2: 0.25 };
                    for (out, x) in buf.iter().zip(input) {
                        assert_eq!(*out, $step(&C, &mut s, x));
                    }
                    assert_eq!(state, s);
                }
            }
        };
    }

    biquad_tests!(f64_tests, f64, CoeffsF64, StateF64, step_f64, process_f64);
    biquad_tests!(f32_tests, f32, CoeffsF32, StateF32, step_f32, process_f32);
}
