//! One-pole feedback filter: `y[n] = x[n] + a * y[n-1]`.
//!
//! The previous output `y[n-1]` is the filter's state, kept by the caller and carried from block
//! to block.
//!
//! **Stability.** In exact arithmetic the filter is stable when `|a| < 1`: with every input at
//! most `M` in size, every output is at most `|state| + M / (1 - |a|)` in size, where `state` is
//! the starting state (`one_pole.filt_real_abs_le_outBound`). The whole-block floating-point
//! error theorems assume the stronger `|a| + |a| * u * (2 + u) < 1`, where `u` is the unit
//! roundoff; see `proofs/README.md`.
//!
//! **Gain.** This is the unnormalized form: in exact arithmetic, with `|a| < 1`, a constant input
//! `x` settles at `x / (1 - a)`, not at `x` (`one_pole.filt_real_replicate`,
//! `one_pole.tendsto_filt_real_replicate`). With `a = 0.99` a constant 1.0 settles at about 100.
//! To smooth toward a target value, use `smoother::process_f32` / `smoother::process_f64`, which
//! in exact arithmetic, with `|a| < 1`, settle on the target itself
//! (`smoother.tendsto_filt_real_replicate`).
//!
//! **Subnormals.** A decaying output drifts into subnormal numbers, which are slow on some
//! processors (the drift worked out outside Lean, not proved; the slowness a hardware fact). This
//! module does nothing about that: flushing subnormals to zero is the caller's job (if the caller
//! turns on the processor's flush-to-zero mode, the error bounds are not proved for that mode; see
//! `proofs/README.md`).
//!
//! Call these through the module, as `one_pole::process_f32`.

/// One sample of the filter, in `f64`: the new output from the input `x` and the previous
/// output `state`.
#[inline]
pub fn step_f64(a: f64, state: f64, x: f64) -> f64 {
    x + a * state
}

/// Filters `buf` in place, in `f64`, starting from `state` (the previous output) and leaving the
/// last output in `state`. An empty block leaves `state` unchanged (`one_pole.process_f64_spec`).
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

/// One sample of the filter, in `f32`: the new output from the input `x` and the previous
/// output `state`.
#[inline]
pub fn step_f32(a: f32, state: f32, x: f32) -> f32 {
    x + a * state
}

/// Filters `buf` in place, in `f32`, starting from `state` (the previous output) and leaving the
/// last output in `state`. An empty block leaves `state` unchanged (`one_pole.process_f32_spec`).
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

/// One sample of the filter, in `f64`, with one fused multiply-add: `a.mul_add(state, x)`, which
/// is `a * state + x` rounded once. This is how clang compiles `x + a * state` on Apple silicon
/// (its default `-ffp-contract=on`). Needs the `std` feature.
#[cfg(feature = "std")]
#[inline]
pub fn step_fma_f64(a: f64, state: f64, x: f64) -> f64 {
    a.mul_add(state, x)
}

/// [`process_f64`] with [`step_fma_f64`] for each sample. Needs the `std` feature. An empty block
/// leaves `state` unchanged (`one_pole.process_fma_f64_spec`).
#[cfg(feature = "std")]
pub fn process_fma_f64(a: f64, state: &mut f64, buf: &mut [f64]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = step_fma_f64(a, *state, buf[i]);
        buf[i] = y;
        *state = y;
        i += 1;
    }
}

/// One sample of the filter, in `f32`, with one fused multiply-add: `a.mul_add(state, x)`, which
/// is `a * state + x` rounded once. Needs the `std` feature.
#[cfg(feature = "std")]
#[inline]
pub fn step_fma_f32(a: f32, state: f32, x: f32) -> f32 {
    a.mul_add(state, x)
}

/// [`process_f32`] with [`step_fma_f32`] for each sample. Needs the `std` feature. An empty block
/// leaves `state` unchanged (`one_pole.process_fma_f32_spec`).
#[cfg(feature = "std")]
pub fn process_fma_f32(a: f32, state: &mut f32, buf: &mut [f32]) {
    // An index loop rather than an iterator, so that Aeneas can translate it.
    let mut i = 0;
    while i < buf.len() {
        let y = step_fma_f32(a, *state, buf[i]);
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
        ($name:ident, $t:ty, $step:ident, $process:ident) => {
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
            }
        };
    }

    one_pole_tests!(f64_tests, f64, step_f64, process_f64);
    one_pole_tests!(f32_tests, f32, step_f32, process_f32);
}

#[cfg(all(test, feature = "std"))]
mod fma_tests {
    use super::*;

    /// The same tests for both precisions.
    macro_rules! one_pole_fma_tests {
        ($name:ident, $t:ty, $step:ident, $process:ident, $step_fma:ident, $process_fma:ident,
         $tol:expr) => {
            mod $name {
                use super::*;

                const INPUT: [$t; 8] = [0.1, -0.2, 0.3, 1.0, -1.0, 0.7, 0.0, -0.4];

                #[test]
                fn step_is_one_mul_add() {
                    // The documented grouping, written out by hand.
                    for &(a, s, x) in &[(0.9, -0.5, 0.1), (0.3, 1.0e-3, 0.7), (-0.99, 2.0, -1.0)] {
                        let (a, s, x): ($t, $t, $t) = (a, s, x);
                        assert_eq!($step_fma(a, s, x).to_bits(), a.mul_add(s, x).to_bits());
                    }
                }

                #[test]
                fn process_matches_step() {
                    let a: $t = 0.9;
                    let mut buf = INPUT;
                    let mut state: $t = -0.5;
                    $process_fma(a, &mut state, &mut buf);
                    let mut y: $t = -0.5;
                    for (out, x) in buf.iter().zip(INPUT) {
                        y = a.mul_add(y, x);
                        assert_eq!(out.to_bits(), y.to_bits());
                    }
                    assert_eq!(state.to_bits(), y.to_bits());
                }

                #[test]
                fn close_to_unfused() {
                    let a: $t = 0.95;
                    let mut fused = INPUT;
                    let mut plain = INPUT;
                    let (mut s1, mut s2): ($t, $t) = (0.25, 0.25);
                    $process_fma(a, &mut s1, &mut fused);
                    $process(a, &mut s2, &mut plain);
                    for (f, p) in fused.iter().zip(plain) {
                        assert!((f - p).abs() <= $tol, "{f} vs {p}");
                    }
                    assert!((s1 - s2).abs() <= $tol);
                }

                #[test]
                fn empty_block_leaves_state_alone() {
                    let mut state: $t = 0.3;
                    $process_fma(0.9, &mut state, &mut []);
                    assert_eq!(state, 0.3);
                }
            }
        };
    }

    one_pole_fma_tests!(
        f64_tests,
        f64,
        step_f64,
        process_f64,
        step_fma_f64,
        process_fma_f64,
        1e-13
    );
    one_pole_fma_tests!(
        f32_tests,
        f32,
        step_f32,
        process_f32,
        step_fma_f32,
        process_fma_f32,
        1e-4
    );
}
