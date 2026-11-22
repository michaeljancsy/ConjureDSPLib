//! State-variable filter (SVF), trapezoidal, solving for the high-pass signal first.
//!
//! Each sample computes three signals, `hp`, `bp` and `lp`, from the input `x` and two state
//! values `s1`, `s2`, then mixes them into the output:
//!
//! ```text
//! hp  = ((x - (k + g)·s1) - s2)·d
//! bp  = g·hp + s1
//! lp  = g·bp + s2
//! s1' = g·hp + bp
//! s2' = g·bp + lp
//! y   = (m_hp·hp + m_bp·bp) + m_lp·lp
//! ```
//!
//! where `d = 1 / (1 + g·(g + k))` is computed once, by `CoeffsF64::new` / `CoeffsF32::new`.
//! This module computes exactly these steps, in this order and grouping (the brackets above),
//! with no fused multiply-add, so code that uses the same order gets bit-identical output. In
//! exact arithmetic these are the equations of the trapezoidal ("topology-preserving") SVF in
//! V. Zavalishin, *The Art of VA Filter Design* (with `k = 2R`); that correspondence is not proved
//! in `proofs/`.
//!
//! One set of coefficients can be shared by several channels, each with its own state. The
//! coefficients can change between calls; the state is kept.
//!
//! Designing coefficients from a cutoff in hertz is not part of this module: the caller computes
//! `g`. Flushing subnormal numbers to zero is the caller's job.
//!
//! Call these through the module, as `svf::process_f32`.

/// SVF coefficients in `f64`. Build them with [`CoeffsF64::new`], which computes `d`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CoeffsF64 {
    /// The integrators' gain, usually `tan(π·cutoff / sample_rate)`, computed by the caller.
    pub g: f64,
    /// The damping, usually `1 / Q`.
    pub k: f64,
    /// `1 / (1 + g·(g + k))`, computed in that order by [`CoeffsF64::new`].
    pub d: f64,
    /// Weight of the high-pass signal `hp` in the output.
    pub m_hp: f64,
    /// Weight of the band-pass signal `bp` in the output.
    pub m_bp: f64,
    /// Weight of the low-pass signal `lp` in the output.
    pub m_lp: f64,
}

impl CoeffsF64 {
    /// Coefficients with integrator gain `g`, damping `k` and output mix `m_hp`, `m_bp`, `m_lp`:
    /// the output is `m_hp·hp + m_bp·bp + m_lp·lp`. As the names say, the mix `(0, 0, 1)` gives the
    /// low-pass output, `(1, 0, 0)` the high-pass output and `(0, 1, 0)` the band-pass output. Computes
    /// `d = 1.0 / (1.0 + g * (g + k))`, in that order.
    pub fn new(g: f64, k: f64, m_hp: f64, m_bp: f64, m_lp: f64) -> Self {
        Self {
            g,
            k,
            d: 1.0 / (1.0 + g * (g + k)),
            m_hp,
            m_bp,
            m_lp,
        }
    }
}

/// The two state values of one SVF channel, in `f64`. `StateF64::default()` is the zero state,
/// for a filter that has seen only silence.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF64 {
    /// The first integrator's state: `bp = g·hp + s1`.
    pub s1: f64,
    /// The second integrator's state: `lp = g·bp + s2`.
    pub s2: f64,
}

/// One sample of the filter, in `f64`: returns the output and updates `state`, as in the module
/// documentation.
#[inline]
pub fn step_f64(c: &CoeffsF64, state: &mut StateF64, x: f64) -> f64 {
    let hp = (x - (c.k + c.g) * state.s1 - state.s2) * c.d;
    let bp = c.g * hp + state.s1;
    let lp = c.g * bp + state.s2;
    state.s1 = c.g * hp + bp;
    state.s2 = c.g * bp + lp;
    c.m_hp * hp + c.m_bp * bp + c.m_lp * lp
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

/// SVF coefficients in `f32`. Build them with [`CoeffsF32::new`], which computes `d`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CoeffsF32 {
    /// The integrators' gain, usually `tan(π·cutoff / sample_rate)`, computed by the caller.
    pub g: f32,
    /// The damping, usually `1 / Q`.
    pub k: f32,
    /// `1 / (1 + g·(g + k))`, computed in that order by [`CoeffsF32::new`].
    pub d: f32,
    /// Weight of the high-pass signal `hp` in the output.
    pub m_hp: f32,
    /// Weight of the band-pass signal `bp` in the output.
    pub m_bp: f32,
    /// Weight of the low-pass signal `lp` in the output.
    pub m_lp: f32,
}

impl CoeffsF32 {
    /// Coefficients with integrator gain `g`, damping `k` and output mix `m_hp`, `m_bp`, `m_lp`:
    /// the output is `m_hp·hp + m_bp·bp + m_lp·lp`. As the names say, the mix `(0, 0, 1)` gives the
    /// low-pass output, `(1, 0, 0)` the high-pass output and `(0, 1, 0)` the band-pass output. Computes
    /// `d = 1.0 / (1.0 + g * (g + k))`, in that order.
    pub fn new(g: f32, k: f32, m_hp: f32, m_bp: f32, m_lp: f32) -> Self {
        Self {
            g,
            k,
            d: 1.0 / (1.0 + g * (g + k)),
            m_hp,
            m_bp,
            m_lp,
        }
    }
}

/// The two state values of one SVF channel, in `f32`. `StateF32::default()` is the zero state,
/// for a filter that has seen only silence.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct StateF32 {
    /// The first integrator's state: `bp = g·hp + s1`.
    pub s1: f32,
    /// The second integrator's state: `lp = g·bp + s2`.
    pub s2: f32,
}

/// One sample of the filter, in `f32`: returns the output and updates `state`, as in the module
/// documentation.
#[inline]
pub fn step_f32(c: &CoeffsF32, state: &mut StateF32, x: f32) -> f32 {
    let hp = (x - (c.k + c.g) * state.s1 - state.s2) * c.d;
    let bp = c.g * hp + state.s1;
    let lp = c.g * bp + state.s2;
    state.s1 = c.g * hp + bp;
    state.s2 = c.g * bp + lp;
    c.m_hp * hp + c.m_bp * bp + c.m_lp * lp
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
    macro_rules! svf_tests {
        ($name:ident, $t:ty, $coeffs:ident, $state:ident, $step:ident, $process:ident) => {
            mod $name {
                use super::*;

                // g = 0.5, k = 1.5: 1 + g·(g + k) = 2, so d = 0.5 exactly, and short runs with
                // simple inputs stay exact in binary.
                const G: $t = 0.5;
                const K: $t = 1.5;

                #[test]
                fn new_computes_d() {
                    let c = $coeffs::new(G, K, 0.0, 0.0, 1.0);
                    assert_eq!(c.d, 0.5);
                    assert_eq!((c.g, c.k), (G, K));
                    assert_eq!((c.m_hp, c.m_bp, c.m_lp), (0.0, 0.0, 1.0));
                    // Not exact in binary: the same bits as the documented order.
                    let (g, k): ($t, $t) = (0.3, 0.7);
                    let c = $coeffs::new(g, k, 1.0, 0.0, 0.0);
                    assert_eq!(c.d.to_bits(), (1.0 / (1.0 + g * (g + k))).to_bits());
                }

                #[test]
                fn zero_gain_high_pass_passes_input_through() {
                    // With g = 0, d = 1, bp and lp stay at 0 from a zero state, and hp = x.
                    let c = $coeffs::new(0.0, 1.5, 1.0, 0.0, 0.0);
                    assert_eq!(c.d, 1.0);
                    let input: [$t; 4] = [0.3, -1.0, 2.5, 0.0];
                    let mut buf = input;
                    let mut state = $state::default();
                    $process(&c, &mut state, &mut buf);
                    assert_eq!(buf, input);
                    assert_eq!(state, $state::default());
                }

                #[test]
                fn mix_one_k_one_gives_input_back_for_exact_values() {
                    // With the mix (1, k, 1), the output hp + k·bp + lp equals x in exact
                    // arithmetic; with these values every operation is exact in binary, so the
                    // filter returns its input, from a nonzero state too.
                    let c = $coeffs::new(G, K, 1.0, K, 1.0);
                    let input: [$t; 6] = [1.0, 0.0, -0.5, 0.25, 2.0, 0.0];
                    let mut buf = input;
                    let mut state = $state { s1: 0.5, s2: -0.25 };
                    $process(&c, &mut state, &mut buf);
                    assert_eq!(buf, input);
                }

                #[test]
                fn impulse_response_by_hand() {
                    // Low-pass mix, g = 0.5, k = 1.5, d = 0.5, from zero.
                    // n = 0: hp = 0.5, bp = 0.25, lp = 0.125, s1 = 0.5, s2 = 0.25.
                    // n = 1: hp = (0 - 2·0.5 - 0.25)·0.5 = -0.625, bp = 0.1875,
                    //        lp = 0.34375, s1 = -0.125, s2 = 0.4375.
                    // n = 2: hp = (0 + 0.25 - 0.4375)·0.5 = -0.09375, bp = -0.171875,
                    //        lp = 0.3515625.
                    let c = $coeffs::new(G, K, 0.0, 0.0, 1.0);
                    let mut buf: [$t; 3] = [1.0, 0.0, 0.0];
                    let mut state = $state::default();
                    $process(&c, &mut state, &mut buf);
                    assert_eq!(buf, [0.125, 0.34375, 0.3515625]);
                    // s1 = g·hp + bp = -0.21875, s2 = g·bp + lp = 0.265625.
                    assert_eq!(
                        state,
                        $state {
                            s1: -0.21875,
                            s2: 0.265625
                        }
                    );
                }

                #[test]
                fn state_carries_across_blocks() {
                    let c = $coeffs::new(0.3, 0.7, 0.2, -0.4, 1.1);
                    let input: [$t; 7] = [1.0, -2.0, 0.5, 3.0, 0.0, -1.0, 0.25];
                    let mut whole = input;
                    let mut whole_state = $state {
                        s1: 0.125,
                        s2: -0.25,
                    };
                    $process(&c, &mut whole_state, &mut whole);

                    let mut split = input;
                    let mut split_state = $state {
                        s1: 0.125,
                        s2: -0.25,
                    };
                    let (first, second) = split.split_at_mut(3);
                    $process(&c, &mut split_state, first);
                    $process(&c, &mut split_state, second);

                    assert_eq!(whole, split);
                    assert_eq!(whole_state, split_state);
                }

                /// The step written out separately: `z` holds `[s1, s2]`.
                fn reference_step(c: &$coeffs, z: &mut [$t; 2], x: $t) -> $t {
                    let hp = ((x - (c.k + c.g) * z[0]) - z[1]) * c.d;
                    let bp = c.g * hp + z[0];
                    let lp = c.g * bp + z[1];
                    z[0] = c.g * hp + bp;
                    z[1] = c.g * bp + lp;
                    (c.m_hp * hp + c.m_bp * bp) + c.m_lp * lp
                }

                #[test]
                fn same_bits_as_the_reference_order() {
                    // Coefficients and inputs that are not exact in binary, so a different
                    // operation order would round differently (checked below).
                    let c = $coeffs::new(0.13, 0.9, 0.3, -0.7, 1.1);
                    // 64 varied inputs in [-0.5, 0.5).
                    let mut input: [$t; 64] = [0.0; 64];
                    for (n, x) in input.iter_mut().enumerate() {
                        *x = ((n * 37 % 101) as $t) / 101.0 - 0.5;
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
                        // The same maths in another order: hp = (x - (k·s1 + g·s1 + s2))·d.
                        let hp =
                            (x - (c.k * reordered[0] + c.g * reordered[0] + reordered[1])) * c.d;
                        let bp = c.g * hp + reordered[0];
                        let lp = c.g * bp + reordered[1];
                        reordered = [c.g * hp + bp, c.g * bp + lp];
                        let y2 = c.m_hp * hp + c.m_bp * bp + c.m_lp * lp;
                        differs |= y2.to_bits() != y.to_bits();
                    }
                    assert_eq!(state, $state { s1: z[0], s2: z[1] });
                    // This test can tell the orders apart.
                    assert!(differs);
                }

                #[test]
                fn empty_block_leaves_state_alone() {
                    let c = $coeffs::new(G, K, 0.0, 0.0, 1.0);
                    let mut state = $state { s1: 0.3, s2: -0.7 };
                    $process(&c, &mut state, &mut []);
                    assert_eq!(state, $state { s1: 0.3, s2: -0.7 });
                }

                #[test]
                fn process_matches_step() {
                    let c = $coeffs::new(0.3, 0.7, 0.2, -0.4, 1.1);
                    let input: [$t; 5] = [0.1, -0.2, 0.3, 1.0, -1.0];
                    let mut buf = input;
                    let mut state = $state { s1: -0.5, s2: 0.25 };
                    $process(&c, &mut state, &mut buf);
                    let mut s = $state { s1: -0.5, s2: 0.25 };
                    for (out, x) in buf.iter().zip(input) {
                        assert_eq!(*out, $step(&c, &mut s, x));
                    }
                    assert_eq!(state, s);
                }
            }
        };
    }

    svf_tests!(f64_tests, f64, CoeffsF64, StateF64, step_f64, process_f64);
    svf_tests!(f32_tests, f32, CoeffsF32, StateF32, step_f32, process_f32);

    /// The low-pass mix against the biquad with the bilinear-transform low-pass coefficients for
    /// the same `g` and `k`: `H(s) = 1 / (s² + k·s + 1)` with `s = (1/g)·(z - 1)/(z + 1)` gives
    /// `b = [g², 2g², g²] / a0`, `a1 = 2(g² - 1) / a0`, `a2 = (1 - k·g + g²) / a0`, with
    /// `a0 = 1 + k·g + g²`.
    #[test]
    fn low_pass_matches_bilinear_biquad_f64() {
        extern crate std;
        use crate::biquad;
        use core::f64::consts::PI;

        for &(cutoff, q) in &[(1000.0, 0.75), (100.0, 2.0), (8000.0, 0.5)] {
            let g = (PI * cutoff / 48000.0_f64).tan();
            let k = 1.0 / q;
            let a0 = 1.0 + k * g + g * g;
            let bq = biquad::CoeffsF64 {
                b0: g * g / a0,
                b1: 2.0 * g * g / a0,
                b2: g * g / a0,
                a1: 2.0 * (g * g - 1.0) / a0,
                a2: (1.0 - k * g + g * g) / a0,
            };
            let c = CoeffsF64::new(g, k, 0.0, 0.0, 1.0);

            let mut svf_buf = [0.0_f64; 32];
            svf_buf[0] = 1.0;
            let mut bq_buf = svf_buf;
            process_f64(&c, &mut StateF64::default(), &mut svf_buf);
            biquad::process_f64(&bq, &mut biquad::StateF64::default(), &mut bq_buf);
            for (a, b) in svf_buf.iter().zip(bq_buf.iter()) {
                assert!((a - b).abs() <= 1e-12, "cutoff {cutoff}: {a} vs {b}");
            }
        }
    }
}
