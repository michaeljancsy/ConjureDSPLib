//! First-order all-pass filter: `H(z) = (c + z⁻¹) / (1 + c·z⁻¹)`.
//!
//! Each sample is computed in direct form I as
//!
//! ```text
//! y  = c·(x - y1) + x1
//! x1 = x
//! y1 = y
//! ```
//!
//! where `x1` and `y1`, the previous input and output, are the filter's state ([`StateF64`],
//! [`StateF32`]), kept by the caller and carried from block to block. The code computes exactly
//! these operations, in this order (`allpass1.step_f64_eq`, `allpass1.process_f64_spec`), under
//! the assumptions in `proofs/README.md`.
//!
//! **Stability.** In exact arithmetic, for `|c| < 1`, with the starting `x1` and every input at
//! most `M` in size, every output is at most `|y1| + (1 + |c|)·M / (1 - |c|)` in size, where `y1`
//! is the starting state's (`allpass1.filt_real_abs_le_outBound`). That the filter then passes
//! every frequency at the same level, changing only its phase, is a standard result, not proved
//! in Lean (the tests measure it at a few frequencies). [`coeff_f64`] and [`coeff_f32`] give the
//! `c` whose phase shift is 90° at a chosen corner frequency (a standard result, not proved in
//! Lean).
//!
//! **Error bound.** For `|c|` below 1 with a little room for rounding, every output of a block of
//! any length is within a stated distance of the same filter run in exact arithmetic on the
//! stored coefficient, starting state and inputs (`allpass1.process_f64_block_error`,
//! `allpass1.process_f64_block_error_of_inputs` and their `f32` versions; the conditions and the
//! bound are in `proofs/README.md`).
//!
//! **Cascades.** A chain of all-pass stages is the caller's job: one state per stage, each stage
//! filtering the output of the one before.
//!
//! With the `std` feature, `step_fma_f64` / `process_fma_f64` (and the `f32` ones) compute
//! `y = c.mul_add(x - y1, x1)`, one fused multiply-add per sample (`allpass1.step_fma_f64_eq`),
//! with the same whole-block error bound (`allpass1.process_fma_f64_block_error`).
//! Where the build cannot assume a fused multiply-add instruction, `mul_add` is expected to be a
//! call to the C library's `fma`, which can be much slower (expected, not measured).
//!
//! Flushing subnormal numbers to zero is the caller's job (if the caller turns on the processor's
//! flush-to-zero mode, the error bounds are not proved for that mode; see `proofs/README.md`).
//!
//! Call these through the module, as `allpass1::process_f32`.

use core::f32::consts::PI as PI_F32;
use core::f64::consts::PI as PI_F64;

/// The state of one all-pass channel, in `f64`: the previous input and output.
/// `StateF64::default()` is the zero state, for a filter that has seen only silence.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF64 {
    /// The previous input, `x[n-1]`.
    pub x1: f64,
    /// The previous output, `y[n-1]`.
    pub y1: f64,
}

/// The state of one all-pass channel, in `f32`: the previous input and output.
/// `StateF32::default()` is the zero state, for a filter that has seen only silence.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF32 {
    /// The previous input, `x[n-1]`.
    pub x1: f32,
    /// The previous output, `y[n-1]`.
    pub y1: f32,
}

/// The coefficient `c` for a phase shift of 90° at `corner_hz`, in `f64`:
/// `c = (t - 1) / (t + 1)` with `t = tan(π·corner_hz / sample_rate_hz)`.
///
/// Computed as `t = libm::tan(PI * corner_hz / sample_rate_hz)` (`PI` is
/// `core::f64::consts::PI`; the multiplication first, then the division), then
/// `(t - 1.0) / (t + 1.0)` (`allpass1.coeff_f64_eq`). That the phase shift is 90° at
/// `corner_hz` is a standard result, not proved in Lean. Meant for
/// `0 < corner_hz < sample_rate_hz / 2`, which gives `|c| < 1` in exact arithmetic (a standard
/// result, not proved in Lean); nothing is checked. It never panics, assuming libm's `tan` never
/// panics.
pub fn coeff_f64(corner_hz: f64, sample_rate_hz: f64) -> f64 {
    let t = libm::tan(PI_F64 * corner_hz / sample_rate_hz);
    (t - 1.0) / (t + 1.0)
}

/// The coefficient `c` for a phase shift of 90° at `corner_hz`, in `f32`: the same as
/// [`coeff_f64`], with `libm::tanf` and `core::f32::consts::PI` (`allpass1.coeff_f32_eq`).
pub fn coeff_f32(corner_hz: f32, sample_rate_hz: f32) -> f32 {
    let t = libm::tanf(PI_F32 * corner_hz / sample_rate_hz);
    (t - 1.0) / (t + 1.0)
}

/// One sample of the filter, in `f64`: returns `y = c * (x - state.y1) + state.x1`, computed in
/// that order, and sets `state.x1 = x`, `state.y1 = y`.
#[inline]
pub fn step_f64(c: f64, state: &mut StateF64, x: f64) -> f64 {
    let y = c * (x - state.y1) + state.x1;
    state.x1 = x;
    state.y1 = y;
    y
}

/// Filters `buf` in place, in `f64`, carrying `state` from block to block. An empty block leaves
/// `state` unchanged (`allpass1.process_f64_spec`).
pub fn process_f64(c: f64, state: &mut StateF64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_f64(c, state, buf[i]);
        i += 1;
    }
}

/// One sample of the filter, in `f32`: returns `y = c * (x - state.y1) + state.x1`, computed in
/// that order, and sets `state.x1 = x`, `state.y1 = y`.
#[inline]
pub fn step_f32(c: f32, state: &mut StateF32, x: f32) -> f32 {
    let y = c * (x - state.y1) + state.x1;
    state.x1 = x;
    state.y1 = y;
    y
}

/// Filters `buf` in place, in `f32`, carrying `state` from block to block. An empty block leaves
/// `state` unchanged (`allpass1.process_f32_spec`).
pub fn process_f32(c: f32, state: &mut StateF32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_f32(c, state, buf[i]);
        i += 1;
    }
}

/// One sample of the filter, in `f64`, with one fused multiply-add:
/// `y = c.mul_add(x - state.y1, state.x1)`, which is `c * (x - state.y1) + state.x1` with the
/// multiply and add rounded once. This is how clang compiles `c * (x - y1) + x1` on Apple silicon
/// (its default `-ffp-contract=on`; worked out outside Lean, not proved: checked against Apple
/// clang 17, arm64, -O2). Needs the `std` feature.
#[cfg(feature = "std")]
#[inline]
pub fn step_fma_f64(c: f64, state: &mut StateF64, x: f64) -> f64 {
    let y = c.mul_add(x - state.y1, state.x1);
    state.x1 = x;
    state.y1 = y;
    y
}

/// [`process_f64`] with [`step_fma_f64`] for each sample. Needs the `std` feature. An empty block
/// leaves `state` unchanged (`allpass1.process_fma_f64_spec`).
#[cfg(feature = "std")]
pub fn process_fma_f64(c: f64, state: &mut StateF64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        buf[i] = step_fma_f64(c, state, buf[i]);
        i += 1;
    }
}

/// One sample of the filter, in `f32`, with one fused multiply-add:
/// `y = c.mul_add(x - state.y1, state.x1)`, which is `c * (x - state.y1) + state.x1` with the
/// multiply and add rounded once. This is how clang compiles `c * (x - y1) + x1` on Apple silicon
/// (its default `-ffp-contract=on`; worked out outside Lean, not proved: checked against Apple
/// clang 17, arm64, -O2). Needs the `std` feature.
#[cfg(feature = "std")]
#[inline]
pub fn step_fma_f32(c: f32, state: &mut StateF32, x: f32) -> f32 {
    let y = c.mul_add(x - state.y1, state.x1);
    state.x1 = x;
    state.y1 = y;
    y
}

/// [`process_f32`] with [`step_fma_f32`] for each sample. Needs the `std` feature. An empty block
/// leaves `state` unchanged (`allpass1.process_fma_f32_spec`).
#[cfg(feature = "std")]
pub fn process_fma_f32(c: f32, state: &mut StateF32, buf: &mut [f32]) {
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

    /// Steady-state gain and phase (radians) of the filter at `f` cycles per sample, measured
    /// from a long sine run in `f64` arithmetic on the outputs.
    fn measure<T: Copy>(
        f: f64,
        from: fn(f64) -> T,
        to: fn(T) -> f64,
        run: &dyn Fn(&mut [T]),
    ) -> (f64, f64) {
        const N: usize = 20_000;
        let w = 2.0 * PI_F64 * f;
        let mut buf = [from(0.0); N];
        for (k, x) in buf.iter_mut().enumerate() {
            *x = from(libm::sin(w * k as f64));
        }
        let input = buf;
        run(&mut buf);
        // Correlate the second half (a whole number of cycles) with sine and cosine at f.
        let (mut ys, mut yc, mut xs, mut xc) = (0.0, 0.0, 0.0, 0.0);
        for k in N / 2..N {
            let (s, c) = (libm::sin(w * k as f64), libm::cos(w * k as f64));
            ys += to(buf[k]) * s;
            yc += to(buf[k]) * c;
            xs += to(input[k]) * s;
            xc += to(input[k]) * c;
        }
        let gain = libm::sqrt(ys * ys + yc * yc) / libm::sqrt(xs * xs + xc * xc);
        let mut phase = libm::atan2(yc, ys) - libm::atan2(xc, xs);
        while phase > PI_F64 {
            phase -= 2.0 * PI_F64;
        }
        while phase < -PI_F64 {
            phase += 2.0 * PI_F64;
        }
        (gain, phase)
    }

    /// The same tests for both precisions.
    macro_rules! allpass_tests {
        ($name:ident, $t:ty, $state:ident, $coeff:ident, $step:ident, $process:ident,
         $tan:path, $pi:expr, $tol:expr) => {
            mod $name {
                use super::*;

                fn gain_phase(c: $t, f: f64) -> (f64, f64) {
                    measure(f, |x| x as $t, |x| x as f64, &|buf: &mut [$t]| {
                        let mut state = $state::default();
                        $process(c, &mut state, buf);
                    })
                }

                #[test]
                fn magnitude_is_one_at_several_frequencies() {
                    // Measured, not proved: the gain at each frequency is 1 within the tolerance.
                    let c = $coeff(1_000.0, 48_000.0);
                    for f in [0.0125, 0.05, 0.1, 0.25, 0.4] {
                        let (gain, _) = gain_phase(c, f);
                        assert!((gain - 1.0).abs() < $tol, "gain {gain} at {f}");
                    }
                }

                #[test]
                fn phase_is_minus_90_degrees_at_the_corner() {
                    // 1.2 kHz at 48 kHz is 0.025 cycles per sample.
                    let c = $coeff(1_200.0, 48_000.0);
                    let (_, phase) = gain_phase(c, 0.025);
                    assert!(
                        (phase + core::f64::consts::FRAC_PI_2).abs() < 1e-3,
                        "phase {phase}"
                    );
                }

                #[test]
                fn coefficient_formula() {
                    let t = $tan($pi * 1_000.0 / 48_000.0);
                    assert_eq!($coeff(1_000.0, 48_000.0), (t - 1.0) / (t + 1.0));
                    // A quarter of the sample rate: tan(π/4) is about 1, so c is about 0.
                    assert!($coeff(12_000.0, 48_000.0).abs() < 1e-6);
                }

                #[test]
                fn impulse_response_starts_c_then_one_minus_c_squared() {
                    let c: $t = 0.5;
                    let mut state = $state::default();
                    let mut buf: [$t; 3] = [1.0, 0.0, 0.0];
                    $process(c, &mut state, &mut buf);
                    // y0 = c, y1 = 1 - c^2, y2 = -c (1 - c^2): exact in binary for c = 0.5.
                    assert_eq!(buf, [0.5, 0.75, -0.375]);
                    assert_eq!(state.x1, 0.0);
                    assert_eq!(state.y1, -0.375);
                }

                #[test]
                fn state_carries_across_blocks() {
                    let input: [$t; 7] = [1.0, -0.5, 0.25, 2.0, 0.0, -1.0, 0.3];
                    let c: $t = -0.3;
                    let mut whole = input;
                    let mut s1 = $state { x1: 0.2, y1: -0.1 };
                    $process(c, &mut s1, &mut whole);
                    let mut split = input;
                    let mut s2 = $state { x1: 0.2, y1: -0.1 };
                    let (a, b) = split.split_at_mut(3);
                    $process(c, &mut s2, a);
                    $process(c, &mut s2, b);
                    assert_eq!(whole, split);
                    assert_eq!(s1, s2);
                }

                #[test]
                fn process_matches_step_and_empty_block() {
                    let input: [$t; 5] = [0.1, -0.2, 0.3, 1.0, -1.0];
                    let c: $t = 0.7;
                    let mut buf = input;
                    let mut state = $state { x1: 0.5, y1: 0.25 };
                    $process(c, &mut state, &mut buf);
                    let mut s = $state { x1: 0.5, y1: 0.25 };
                    for (out, x) in buf.iter().zip(input) {
                        let y = c * (x - s.y1) + s.x1;
                        assert_eq!($step(c, &mut s, x), y);
                        assert_eq!(*out, y);
                    }
                    assert_eq!(state, s);
                    $process(c, &mut state, &mut []);
                    assert_eq!(state, s);
                }
            }
        };
    }

    allpass_tests!(
        f64_tests,
        f64,
        StateF64,
        coeff_f64,
        step_f64,
        process_f64,
        libm::tan,
        PI_F64,
        1e-9
    );
    allpass_tests!(
        f32_tests,
        f32,
        StateF32,
        coeff_f32,
        step_f32,
        process_f32,
        libm::tanf,
        PI_F32,
        1e-4
    );
}

#[cfg(all(test, feature = "std"))]
mod fma_tests {
    use super::*;

    macro_rules! allpass_fma_tests {
        ($name:ident, $t:ty, $state:ident, $process:ident, $step_fma:ident, $process_fma:ident,
         $tol:expr) => {
            mod $name {
                use super::*;

                const INPUT: [$t; 8] = [0.1, -0.2, 0.3, 1.0, -1.0, 0.7, 0.0, -0.4];

                #[test]
                fn step_is_one_mul_add() {
                    let c: $t = 0.37;
                    let mut s = $state { x1: 0.5, y1: -0.25 };
                    let want = c.mul_add(0.9 - s.y1, s.x1);
                    assert_eq!($step_fma(c, &mut s, 0.9).to_bits(), want.to_bits());
                    assert_eq!(s.x1, 0.9);
                    assert_eq!(s.y1.to_bits(), want.to_bits());
                }

                #[test]
                fn process_matches_step_and_close_to_unfused() {
                    let c: $t = -0.6;
                    let mut fused = INPUT;
                    let mut plain = INPUT;
                    let (mut s1, mut s2) = ($state::default(), $state::default());
                    $process_fma(c, &mut s1, &mut fused);
                    $process(c, &mut s2, &mut plain);
                    let mut s = $state::default();
                    for (k, x) in INPUT.iter().enumerate() {
                        assert_eq!(fused[k].to_bits(), $step_fma(c, &mut s, *x).to_bits());
                        assert!((fused[k] - plain[k]).abs() <= $tol);
                    }
                    assert_eq!(s1, s);
                    $process_fma(c, &mut s1, &mut []);
                    assert_eq!(s1, s);
                }
            }
        };
    }

    allpass_fma_tests!(
        f64_tests,
        f64,
        StateF64,
        process_f64,
        step_fma_f64,
        process_fma_f64,
        1e-13
    );
    allpass_fma_tests!(
        f32_tests,
        f32,
        StateF32,
        process_f32,
        step_fma_f32,
        process_fma_f32,
        1e-5
    );
}
