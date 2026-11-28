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
//! In exact arithmetic the two forms give the same output when the starting state matches the
//! textbook form's history, in particular from zero state and zero history
//! (`biquad.filt_real_eq_df1_real`, `biquad.filt_real_eq_df1_real_zero`). In floating point they
//! can round differently (worked out outside Lean, not proved). This module computes exactly the
//! steps above, in that order and grouping (`s1 = (b1·x - a1·y) + s2`), with no fused
//! multiply-add (`biquad.step_f64_eq`, `biquad.step_f32_eq`, under the assumptions in
//! `proofs/README.md`). Other code doing the same operations in the same order, also without
//! fused multiply-add, given the same rounding mode and subnormal handling, gets the same output,
//! NaN bit patterns aside (follows from IEEE 754 rounding, not proved).
//!
//! With the `std` feature, `step_fma_f64` / `process_fma_f64` (and the `f32` ones) compute
//! the same steps with fused multiply-adds, in the grouping their documentation gives
//! (`biquad.step_fma_f64_eq`), with the same whole-block error bounds
//! (`biquad.process_fma_f64_block_error`).
//! Where the build cannot assume a fused multiply-add instruction, `mul_add` is expected to be a
//! call to the C library's `fma`, which can be much slower (expected, not measured).
//!
//! One set of coefficients can be shared by several channels, each with its own state. The
//! coefficients can change between calls; the state is kept.
//!
//! Designing coefficients (low-pass, shelf, ...) is not part of this module. The filter is stable
//! when both poles are inside the unit circle, that is when `|a2| < 1` and `|a1| < 1 + a2` (a
//! standard result, not proved in Lean). Proved in Lean: for distinct real poles, these two
//! inequalities hold exactly when both poles are inside the unit circle
//! (`biquad.realPoles_lt_one_iff`); and for poles inside the unit circle, the proofs supply the
//! `Contraction` the error-bound theorems need (`biquad.complexPolesContraction`,
//! `biquad.realPolesContraction`, `biquad.repeatedPoleContraction`,
//! `biquad.closePolesContraction`, in `Biquad/Contraction.lean`).
//!
//! For RBJ-cookbook low-pass and high-pass coefficients at very low cutoffs (a few hertz), `f32`
//! coefficients can put a pole on or outside the unit circle (worked out outside Lean, not proved;
//! see "Observations" in `proofs/README.md`). One case is proved for specific stored values: the
//! binary32 coefficients in `lowPass1Hz_f32`, which are those of a 1 Hz Butterworth low-pass at
//! 48 kHz (worked out outside Lean, not proved), have a pole at exactly 1
//! (`biquad.lowPass1Hz_pole_one_f32`). Consider the `f64` filter there; that its coefficients
//! avoid the problem is not proved.
//!
//! Flushing subnormal numbers to zero is the caller's job (if the caller turns on the processor's
//! flush-to-zero mode, the error bounds are not proved for that mode; see `proofs/README.md`).
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

impl CoeffsF64 {
    /// Coefficients `b0 = 1`, all others 0. From the zero state, every finite nonzero input and
    /// `+0.0` pass through unchanged, bit for bit. `-0.0` comes out as `+0.0` or `-0.0`,
    /// depending on the inputs before it. An infinite or NaN input makes the state NaN from then
    /// on (worked out outside Lean, not proved).
    pub const IDENTITY: Self = Self {
        b0: 1.0,
        b1: 0.0,
        b2: 0.0,
        a1: 0.0,
        a2: 0.0,
    };
}

/// The two state values of one biquad channel, in `f64`. `StateF64::default()` is the zero
/// state, for a filter that has seen only silence.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF64 {
    /// Carried into the next output: `y = b0·x + s1`.
    pub s1: f64,
    /// Carried into the next `s1`: `s1 = b1·x - a1·y + s2`.
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
/// `state` unchanged (`biquad.process_f64_spec`).
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

impl CoeffsF32 {
    /// Coefficients `b0 = 1`, all others 0. From the zero state, every finite nonzero input and
    /// `+0.0` pass through unchanged, bit for bit. `-0.0` comes out as `+0.0` or `-0.0`,
    /// depending on the inputs before it. An infinite or NaN input makes the state NaN from then
    /// on (worked out outside Lean, not proved).
    pub const IDENTITY: Self = Self {
        b0: 1.0,
        b1: 0.0,
        b2: 0.0,
        a1: 0.0,
        a2: 0.0,
    };
}

/// The two state values of one biquad channel, in `f32`. `StateF32::default()` is the zero
/// state, for a filter that has seen only silence.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF32 {
    /// Carried into the next output: `y = b0·x + s1`.
    pub s1: f32,
    /// Carried into the next `s1`: `s1 = b1·x - a1·y + s2`.
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
/// `state` unchanged (`biquad.process_f32_spec`).
pub fn process_f32(c: &CoeffsF32, state: &mut StateF32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_f32(c, state, buf[i]);
        i += 1;
    }
}

/// One sample of the filter, in `f64`, with fused multiply-adds: returns the output and updates
/// `state`. The grouping is how clang contracts the expressions of [`step_f64`] on Apple silicon
/// (its default `-ffp-contract=on`, which fuses a product into the addition or subtraction it
/// feeds, within one expression; worked out outside Lean, not proved: checked against Apple
/// clang 17, arm64, -O2):
///
/// ```text
/// y  = b0.mul_add(x, s1)
/// s1 = b1.mul_add(x, -(a1·y)) + s2
/// s2 = b2.mul_add(x, -(a2·y))
/// ```
///
/// Six roundings instead of nine (a property of the code, not proved). Needs the `std` feature.
#[cfg(feature = "std")]
#[inline]
pub fn step_fma_f64(c: &CoeffsF64, state: &mut StateF64, x: f64) -> f64 {
    let y = c.b0.mul_add(x, state.s1);
    state.s1 = c.b1.mul_add(x, -(c.a1 * y)) + state.s2;
    state.s2 = c.b2.mul_add(x, -(c.a2 * y));
    y
}

/// [`process_f64`] with [`step_fma_f64`] for each sample. Needs the `std` feature. An empty block
/// leaves `state` unchanged (`biquad.process_fma_f64_spec`).
#[cfg(feature = "std")]
pub fn process_fma_f64(c: &CoeffsF64, state: &mut StateF64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_fma_f64(c, state, buf[i]);
        i += 1;
    }
}

/// One sample of the filter, in `f32`, with fused multiply-adds: returns the output and updates
/// `state`. The grouping is how clang contracts the expressions of [`step_f32`] on Apple silicon
/// (its default `-ffp-contract=on`, which fuses a product into the addition or subtraction it
/// feeds, within one expression; worked out outside Lean, not proved: checked against Apple
/// clang 17, arm64, -O2):
///
/// ```text
/// y  = b0.mul_add(x, s1)
/// s1 = b1.mul_add(x, -(a1·y)) + s2
/// s2 = b2.mul_add(x, -(a2·y))
/// ```
///
/// Six roundings instead of nine (a property of the code, not proved). Needs the `std` feature.
#[cfg(feature = "std")]
#[inline]
pub fn step_fma_f32(c: &CoeffsF32, state: &mut StateF32, x: f32) -> f32 {
    let y = c.b0.mul_add(x, state.s1);
    state.s1 = c.b1.mul_add(x, -(c.a1 * y)) + state.s2;
    state.s2 = c.b2.mul_add(x, -(c.a2 * y));
    y
}

/// [`process_f32`] with [`step_fma_f32`] for each sample. Needs the `std` feature. An empty block
/// leaves `state` unchanged (`biquad.process_fma_f32_spec`).
#[cfg(feature = "std")]
pub fn process_fma_f32(c: &CoeffsF32, state: &mut StateF32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_fma_f32(c, state, buf[i]);
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
                fn direct_form_1(c: &$coeffs, xs: &[$t; 6]) -> [$t; 6] {
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
                    let id = $coeffs::IDENTITY;
                    assert_eq!(id.b0, 1.0);
                    assert_eq!((id.b1, id.b2, id.a1, id.a2), (0.0, 0.0, 0.0, 0.0));
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
                    let mut whole_state = $state {
                        s1: 0.125,
                        s2: -0.25,
                    };
                    $process(&C, &mut whole_state, &mut whole);

                    let mut split = input;
                    let mut split_state = $state {
                        s1: 0.125,
                        s2: -0.25,
                    };
                    let (first, second) = split.split_at_mut(3);
                    $process(&C, &mut split_state, first);
                    $process(&C, &mut split_state, second);

                    assert_eq!(whole, split);
                    assert_eq!(whole_state, split_state);
                }

                /// The step written out the usual way: `z` holds `[s1, s2]`, `y = b0·x + z0`,
                /// `z0 = b1·x - a1·y + z1`, `z1 = b2·x - a2·y`.
                fn reference_step(c: &$coeffs, z: &mut [$t; 2], x: $t) -> $t {
                    let y = c.b0 * x + z[0];
                    z[0] = c.b1 * x - c.a1 * y + z[1];
                    z[1] = c.b2 * x - c.a2 * y;
                    y
                }

                #[test]
                fn same_bits_as_the_reference_order() {
                    // Coefficients and inputs that are not exact in binary, so a different
                    // operation order would round differently (checked below).
                    let c = $coeffs {
                        b0: 0.3,
                        b1: -0.7,
                        b2: 0.11,
                        a1: -1.3,
                        a2: 0.47,
                    };
                    // 64 varied inputs in [-0.5, 0.5).
                    let mut input: [$t; 64] = [0.0; 64];
                    for (k, x) in input.iter_mut().enumerate() {
                        *x = ((k * 37 % 101) as $t) / 101.0 - 0.5;
                    }
                    let mut buf = input;
                    let mut state = $state::default();
                    $process(&c, &mut state, &mut buf);

                    let mut z: [$t; 2] = [0.0, 0.0];
                    let mut reordered: [$t; 2] = [0.0, 0.0];
                    let mut differs = false;
                    for (out, x) in buf.iter().zip(input) {
                        let y = reference_step(&c, &mut z, x);
                        assert_eq!(out.to_bits(), y.to_bits());
                        // The same maths in another order: s1 = (b1·x + s2) - a1·y.
                        let y2 = c.b0 * x + reordered[0];
                        reordered[0] = c.b1 * x + reordered[1] - c.a1 * y2;
                        reordered[1] = c.b2 * x - c.a2 * y2;
                        differs |= y2.to_bits() != y.to_bits();
                    }
                    assert_eq!(state, $state { s1: z[0], s2: z[1] });
                    // This test can tell the orders apart.
                    assert!(differs);
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

#[cfg(all(test, feature = "std"))]
mod fma_tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! biquad_fma_tests {
        ($name:ident, $t:ty, $coeffs:ident, $state:ident, $process:ident, $process_fma:ident,
         $tol:expr) => {
            mod $name {
                use super::*;

                // A low-pass near 1 kHz at 48 kHz (rounded coefficients; any stable set will do).
                const C: $coeffs = $coeffs {
                    b0: 0.003916,
                    b1: 0.007832,
                    b2: 0.003916,
                    a1: -1.815341,
                    a2: 0.831006,
                };
                const INPUT: [$t; 8] = [1.0, -0.5, 0.25, 0.0, 0.75, -1.0, 0.3, 0.1];

                #[test]
                fn process_is_the_documented_grouping() {
                    let mut buf = INPUT;
                    let mut state = $state {
                        s1: 0.01,
                        s2: -0.02,
                    };
                    $process_fma(&C, &mut state, &mut buf);
                    let (mut s1, mut s2): ($t, $t) = (0.01, -0.02);
                    for (out, x) in buf.iter().zip(INPUT) {
                        let y = C.b0.mul_add(x, s1);
                        s1 = C.b1.mul_add(x, -(C.a1 * y)) + s2;
                        s2 = C.b2.mul_add(x, -(C.a2 * y));
                        assert_eq!(out.to_bits(), y.to_bits());
                    }
                    assert_eq!(state.s1.to_bits(), s1.to_bits());
                    assert_eq!(state.s2.to_bits(), s2.to_bits());
                }

                #[test]
                fn close_to_unfused() {
                    let mut fused = INPUT;
                    let mut plain = INPUT;
                    let mut st1 = $state::default();
                    let mut st2 = $state::default();
                    $process_fma(&C, &mut st1, &mut fused);
                    $process(&C, &mut st2, &mut plain);
                    for (f, p) in fused.iter().zip(plain) {
                        assert!((f - p).abs() <= $tol, "{f} vs {p}");
                    }
                    assert!((st1.s1 - st2.s1).abs() <= $tol);
                    assert!((st1.s2 - st2.s2).abs() <= $tol);
                }

                #[test]
                fn empty_block_leaves_state_alone() {
                    let mut state = $state { s1: 0.3, s2: -0.1 };
                    $process_fma(&C, &mut state, &mut []);
                    assert_eq!(state, $state { s1: 0.3, s2: -0.1 });
                }
            }
        };
    }

    biquad_fma_tests!(
        f64_tests,
        f64,
        CoeffsF64,
        StateF64,
        process_f64,
        process_fma_f64,
        1e-13
    );
    biquad_fma_tests!(
        f32_tests,
        f32,
        CoeffsF32,
        StateF32,
        process_f32,
        process_fma_f32,
        1e-5
    );
}
