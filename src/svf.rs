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
//! with no fused multiply-add (proved of the translated code as `svf.step_f64_eq` /
//! `svf.step_f32_eq`, under the assumptions in `proofs/README.md`). In exact arithmetic these are
//! the equations of the trapezoidal ("topology-preserving") SVF in V. Zavalishin, *The Art of VA
//! Filter Design* (with `k = 2R`); that correspondence is not proved in `proofs/`.
//!
//! The Lean proofs bound the floating-point error of each output and of the final state of a
//! block, of any length, against the same filter in exact arithmetic
//! (`svf.process_f64_block_error`, `svf.process_f32_block_error`), under the assumptions in
//! `proofs/README.md`. Their conditions are on the stored coefficients, the starting state, the
//! inputs and a chosen state bound `Sb ≥ 0`: a `Contraction` for the coefficients (for example
//! `svf.complexPolesContraction`, when they have complex poles), finite coefficients and starting
//! state, every input at most `M` in size (with `M ≥ 0`), no overflow in any step (or, in the
//! `_of_inputs` versions, finite inputs and a cap on `V`), and `cInf·(R + Ê) ≤ Sb`. For the
//! low-pass examples in `proofs/README.md`, the proofs check the `Contraction`, the `Sb` condition
//! and the cap on `V`, for inputs at most 1 in size and a start from zero.
//!
//! One set of coefficients can be shared by several channels, each with its own state. The
//! coefficients can change between calls; the state is kept.
//!
//! # Designing coefficients from a cutoff in hertz
//!
//! `CoeffsF64` and `CoeffsF32` have design functions for eight shapes: [`CoeffsF64::low_pass`],
//! `high_pass`, `band_pass`, `notch`, `all_pass`, `bell`, `low_shelf` and `high_shelf`. Each
//! computes `g`, `k` and the output mix from `cutoff_hz`, `sample_rate_hz`, `q` (and `gain_db`
//! for the bell and shelves) with `libm`'s `tan`, `pow` and `sqrt` (`tanf`, `powf`, `sqrtf` in
//! `f32`), in the fixed order its documentation gives, then calls `new`. The Lean proofs pin that
//! order (`svf.CoeffsF64.low_pass_eq` and the others).
//!
//! The formulas follow A. Simper (Cytomic), *Solving the continuous SVF equations using
//! trapezoidal integration and equivalent currents*, rewritten in this module's `hp`/`bp`/`lp`
//! mix basis using `x = hp + k·bp + lp` (true in exact arithmetic; worked out outside Lean, not
//! proved). For example Simper's bell output `x + k·(A² - 1)·bp` is `hp + k·A²·bp + lp` (worked
//! out outside Lean, not proved). The names describe the responses Simper intends; that
//! the coefficients give those responses (or any frequency response), and that they are stable
//! and meet the conditions of the error bound for every shape and argument, are **not proved**
//! (only the low-pass examples in `proofs/README.md` are checked).
//!
//! Intended arguments: `0 < cutoff_hz < sample_rate_hz / 2`, `q > 0` and a finite `gain_db`.
//! Nothing is checked, and nothing is claimed outside these ranges (the results may be infinite
//! or NaN there). The design functions never panic, for any arguments, assuming libm's `tan`,
//! `pow` and `sqrt` never panic (proved of the translated code as `svf.CoeffsF64.low_pass_eq` and
//! the others, under that assumption; see `proofs/README.md`).
//!
//! Flushing subnormal numbers to zero is the caller's job (if the caller turns on the processor's
//! flush-to-zero mode, the error bounds no longer apply near zero; see `proofs/README.md`).
//!
//! Call these through the module, as `svf::process_f32`.

use core::f32::consts::PI as PI_F32;
use core::f64::consts::PI as PI_F64;

/// SVF coefficients in `f64`. Build them with [`CoeffsF64::new`], which computes `d`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct CoeffsF64 {
    /// The integrators' gain, usually `tan(π·cutoff / sample_rate)`, from a design function or the
    /// caller.
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
    /// the output is `m_hp·hp + m_bp·bp + m_lp·lp`. The mix `(0, 0, 1)` outputs the signal `lp`,
    /// `(1, 0, 0)` the signal `hp` and `(0, 1, 0)` the signal `bp`; that these are low-, high- and
    /// band-pass responses is not proved. Computes
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

    /// Low-pass design: `g = tan(π·cutoff_hz / sample_rate_hz)`, `k = 1 / q`, mix `(0, 0, 1)`.
    ///
    /// Computed as `g = libm::tan(PI * cutoff_hz / sample_rate_hz)` (`PI` is
    /// `core::f64::consts::PI`; the multiplication first, then the division) and
    /// `k = 1.0 / q`, then [`Self::new`]. The same `g` and `k` are used by every design function
    /// below; the bell changes `k` and the shelves change `g`, as stated there. See the module
    /// documentation for the intended argument ranges and what is not proved.
    pub fn low_pass(cutoff_hz: f64, sample_rate_hz: f64, q: f64) -> Self {
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 0.0, 0.0, 1.0)
    }

    /// High-pass design: `g` and `k` as in [`Self::low_pass`], mix `(1, 0, 0)`.
    pub fn high_pass(cutoff_hz: f64, sample_rate_hz: f64, q: f64) -> Self {
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, 0.0, 0.0)
    }

    /// Band-pass design: `g` and `k` as in [`Self::low_pass`], mix `(0, k, 0)`: the band signal
    /// scaled by `k`.
    pub fn band_pass(cutoff_hz: f64, sample_rate_hz: f64, q: f64) -> Self {
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 0.0, k, 0.0)
    }

    /// Notch design: `g` and `k` as in [`Self::low_pass`], mix `(1, 0, 1)`: `hp + lp`.
    pub fn notch(cutoff_hz: f64, sample_rate_hz: f64, q: f64) -> Self {
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, 0.0, 1.0)
    }

    /// All-pass design: `g` and `k` as in [`Self::low_pass`], mix `(1, -k, 1)`: `hp - k·bp + lp`.
    pub fn all_pass(cutoff_hz: f64, sample_rate_hz: f64, q: f64) -> Self {
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, -k, 1.0)
    }

    /// Bell (peak) design, with `gain_db` the intended gain at the cutoff:
    /// `A = libm::pow(10.0, gain_db / 40.0)`, `g` as in [`Self::low_pass`],
    /// `k = 1.0 / (q * A)`, mix `(1, k * A * A, 1)` (that is, `(k·A)·A`).
    pub fn bell(cutoff_hz: f64, sample_rate_hz: f64, q: f64, gain_db: f64) -> Self {
        let a = libm::pow(10.0, gain_db / 40.0);
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / (q * a);
        Self::new(g, k, 1.0, k * a * a, 1.0)
    }

    /// Low-shelf design, with `gain_db` the intended gain below the cutoff:
    /// `A = libm::pow(10.0, gain_db / 40.0)`,
    /// `g = libm::tan(PI * cutoff_hz / sample_rate_hz) / libm::sqrt(A)`, `k = 1.0 / q`, mix
    /// `(1, k * A, A * A)`.
    pub fn low_shelf(cutoff_hz: f64, sample_rate_hz: f64, q: f64, gain_db: f64) -> Self {
        let a = libm::pow(10.0, gain_db / 40.0);
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz) / libm::sqrt(a);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, k * a, a * a)
    }

    /// High-shelf design, with `gain_db` the intended gain above the cutoff:
    /// `A = libm::pow(10.0, gain_db / 40.0)`,
    /// `g = libm::tan(PI * cutoff_hz / sample_rate_hz) * libm::sqrt(A)`, `k = 1.0 / q`, mix
    /// `(A * A, k * A, 1)`.
    pub fn high_shelf(cutoff_hz: f64, sample_rate_hz: f64, q: f64, gain_db: f64) -> Self {
        let a = libm::pow(10.0, gain_db / 40.0);
        let g = libm::tan(PI_F64 * cutoff_hz / sample_rate_hz) * libm::sqrt(a);
        let k = 1.0 / q;
        Self::new(g, k, a * a, k * a, 1.0)
    }
}

/// The two state values of one SVF channel, in `f64`. `StateF64::default()` is the zero state
/// (`s1 = s2 = 0`).
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
/// `state` unchanged (`svf.process_f64_spec`).
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
    /// The integrators' gain, usually `tan(π·cutoff / sample_rate)`, from a design function or the
    /// caller.
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
    /// the output is `m_hp·hp + m_bp·bp + m_lp·lp`. The mix `(0, 0, 1)` outputs the signal `lp`,
    /// `(1, 0, 0)` the signal `hp` and `(0, 1, 0)` the signal `bp`; that these are low-, high- and
    /// band-pass responses is not proved. Computes
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

    /// Low-pass design: `g = tan(π·cutoff_hz / sample_rate_hz)`, `k = 1 / q`, mix `(0, 0, 1)`.
    ///
    /// Computed as `g = libm::tanf(PI * cutoff_hz / sample_rate_hz)` (`PI` is
    /// `core::f32::consts::PI`; the multiplication first, then the division) and
    /// `k = 1.0 / q`, then [`Self::new`]. The same `g` and `k` are used by every design function
    /// below; the bell changes `k` and the shelves change `g`, as stated there. See the module
    /// documentation for the intended argument ranges and what is not proved.
    pub fn low_pass(cutoff_hz: f32, sample_rate_hz: f32, q: f32) -> Self {
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 0.0, 0.0, 1.0)
    }

    /// High-pass design: `g` and `k` as in [`Self::low_pass`], mix `(1, 0, 0)`.
    pub fn high_pass(cutoff_hz: f32, sample_rate_hz: f32, q: f32) -> Self {
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, 0.0, 0.0)
    }

    /// Band-pass design: `g` and `k` as in [`Self::low_pass`], mix `(0, k, 0)`: the band signal
    /// scaled by `k`.
    pub fn band_pass(cutoff_hz: f32, sample_rate_hz: f32, q: f32) -> Self {
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 0.0, k, 0.0)
    }

    /// Notch design: `g` and `k` as in [`Self::low_pass`], mix `(1, 0, 1)`: `hp + lp`.
    pub fn notch(cutoff_hz: f32, sample_rate_hz: f32, q: f32) -> Self {
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, 0.0, 1.0)
    }

    /// All-pass design: `g` and `k` as in [`Self::low_pass`], mix `(1, -k, 1)`: `hp - k·bp + lp`.
    pub fn all_pass(cutoff_hz: f32, sample_rate_hz: f32, q: f32) -> Self {
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, -k, 1.0)
    }

    /// Bell (peak) design, with `gain_db` the intended gain at the cutoff:
    /// `A = libm::powf(10.0, gain_db / 40.0)`, `g` as in [`Self::low_pass`],
    /// `k = 1.0 / (q * A)`, mix `(1, k * A * A, 1)` (that is, `(k·A)·A`).
    pub fn bell(cutoff_hz: f32, sample_rate_hz: f32, q: f32, gain_db: f32) -> Self {
        let a = libm::powf(10.0, gain_db / 40.0);
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz);
        let k = 1.0 / (q * a);
        Self::new(g, k, 1.0, k * a * a, 1.0)
    }

    /// Low-shelf design, with `gain_db` the intended gain below the cutoff:
    /// `A = libm::powf(10.0, gain_db / 40.0)`,
    /// `g = libm::tanf(PI * cutoff_hz / sample_rate_hz) / libm::sqrtf(A)`, `k = 1.0 / q`, mix
    /// `(1, k * A, A * A)`.
    pub fn low_shelf(cutoff_hz: f32, sample_rate_hz: f32, q: f32, gain_db: f32) -> Self {
        let a = libm::powf(10.0, gain_db / 40.0);
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz) / libm::sqrtf(a);
        let k = 1.0 / q;
        Self::new(g, k, 1.0, k * a, a * a)
    }

    /// High-shelf design, with `gain_db` the intended gain above the cutoff:
    /// `A = libm::powf(10.0, gain_db / 40.0)`,
    /// `g = libm::tanf(PI * cutoff_hz / sample_rate_hz) * libm::sqrtf(A)`, `k = 1.0 / q`, mix
    /// `(A * A, k * A, 1)`.
    pub fn high_shelf(cutoff_hz: f32, sample_rate_hz: f32, q: f32, gain_db: f32) -> Self {
        let a = libm::powf(10.0, gain_db / 40.0);
        let g = libm::tanf(PI_F32 * cutoff_hz / sample_rate_hz) * libm::sqrtf(a);
        let k = 1.0 / q;
        Self::new(g, k, a * a, k * a, 1.0)
    }
}

/// The two state values of one SVF channel, in `f32`. `StateF32::default()` is the zero state
/// (`s1 = s2 = 0`).
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
/// `state` unchanged (`svf.process_f32_spec`).
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

    /// The design functions compute exactly their documented formulas, in both precisions.
    macro_rules! design_formula_tests {
        ($name:ident, $t:ty, $coeffs:ident, $tan:path, $pow:path, $sqrt:path, $pi:expr) => {
            mod $name {
                use super::*;

                // Arguments that are not exact in binary, so any other order would likely differ.
                const FC: $t = 1234.56;
                const FS: $t = 48000.0;
                const Q: $t = 0.707;
                const DB: $t = -4.3;

                fn bits(c: &$coeffs) -> [u64; 6] {
                    [c.g, c.k, c.d, c.m_hp, c.m_bp, c.m_lp].map(|v| v.to_bits() as u64)
                }

                #[test]
                fn designs_match_their_formulas() {
                    let g = $tan($pi * FC / FS);
                    let k = 1.0 / Q;
                    let n = |m_hp, m_bp, m_lp| bits(&$coeffs::new(g, k, m_hp, m_bp, m_lp));
                    assert_eq!(bits(&$coeffs::low_pass(FC, FS, Q)), n(0.0, 0.0, 1.0));
                    assert_eq!(bits(&$coeffs::high_pass(FC, FS, Q)), n(1.0, 0.0, 0.0));
                    assert_eq!(bits(&$coeffs::band_pass(FC, FS, Q)), n(0.0, k, 0.0));
                    assert_eq!(bits(&$coeffs::notch(FC, FS, Q)), n(1.0, 0.0, 1.0));
                    assert_eq!(bits(&$coeffs::all_pass(FC, FS, Q)), n(1.0, -k, 1.0));

                    let a = $pow(10.0, DB / 40.0);
                    let kb = 1.0 / (Q * a);
                    assert_eq!(
                        bits(&$coeffs::bell(FC, FS, Q, DB)),
                        bits(&$coeffs::new(g, kb, 1.0, kb * a * a, 1.0))
                    );
                    let gl = $tan($pi * FC / FS) / $sqrt(a);
                    assert_eq!(
                        bits(&$coeffs::low_shelf(FC, FS, Q, DB)),
                        bits(&$coeffs::new(gl, k, 1.0, k * a, a * a))
                    );
                    let gh = $tan($pi * FC / FS) * $sqrt(a);
                    assert_eq!(
                        bits(&$coeffs::high_shelf(FC, FS, Q, DB)),
                        bits(&$coeffs::new(gh, k, a * a, k * a, 1.0))
                    );
                }

                #[test]
                fn designs_do_not_panic_outside_the_intended_ranges() {
                    let odd: [$t; 7] = [0.0, -1.0, 1e30, -1e30, <$t>::INFINITY, <$t>::NAN, 24000.0];
                    for &a in &odd {
                        for &b in &odd {
                            let _ = $coeffs::low_pass(a, b, a);
                            let _ = $coeffs::all_pass(a, FS, b);
                            let _ = $coeffs::bell(a, b, a, b);
                            let _ = $coeffs::low_shelf(FC, a, b, a);
                            let _ = $coeffs::high_shelf(b, FS, a, b);
                        }
                    }
                }
            }
        };
    }

    design_formula_tests!(
        f64_design,
        f64,
        CoeffsF64,
        libm::tan,
        libm::pow,
        libm::sqrt,
        PI_F64
    );
    design_formula_tests!(
        f32_design,
        f32,
        CoeffsF32,
        libm::tanf,
        libm::powf,
        libm::sqrtf,
        PI_F32
    );

    const FS: f64 = 48000.0;
    const FC: f64 = 1000.0;
    const Q: f64 = 0.75;
    const DB: f64 = 4.0;
    const NYQUIST: f64 = 24000.0;

    /// The magnitude of the filter's response at `freq_hz` (sample rate `FS`), from a long run
    /// on a cosine and a sine from the zero state: once the start-up has died away the outputs
    /// are `|H|·cos(ωn + φ)` and `|H|·sin(ωn + φ)`.
    fn magnitude_f64(c: &CoeffsF64, freq_hz: f64) -> f64 {
        let w = 2.0 * PI_F64 * freq_hz / FS;
        let (mut sc, mut ss) = (StateF64::default(), StateF64::default());
        let (mut yc, mut ys) = (0.0, 0.0);
        for n in 0..20000 {
            let t = w * n as f64;
            yc = step_f64(c, &mut sc, libm::cos(t));
            ys = step_f64(c, &mut ss, libm::sin(t));
        }
        libm::sqrt(yc * yc + ys * ys)
    }

    fn assert_near(got: f64, want: f64, what: &str) {
        assert!((got - want).abs() <= 1e-9, "{what}: {got} vs {want}");
    }

    #[test]
    fn simple_shapes_dc_cutoff_and_nyquist_magnitudes_f64() {
        let lp = CoeffsF64::low_pass(FC, FS, Q);
        assert_near(magnitude_f64(&lp, 0.0), 1.0, "low-pass DC");
        assert_near(magnitude_f64(&lp, FC), Q, "low-pass cutoff");
        assert_near(magnitude_f64(&lp, NYQUIST), 0.0, "low-pass Nyquist");

        let hp = CoeffsF64::high_pass(FC, FS, Q);
        assert_near(magnitude_f64(&hp, 0.0), 0.0, "high-pass DC");
        assert_near(magnitude_f64(&hp, FC), Q, "high-pass cutoff");
        assert_near(magnitude_f64(&hp, NYQUIST), 1.0, "high-pass Nyquist");

        let bp = CoeffsF64::band_pass(FC, FS, Q);
        assert_near(magnitude_f64(&bp, 0.0), 0.0, "band-pass DC");
        assert_near(magnitude_f64(&bp, FC), 1.0, "band-pass cutoff");
        assert_near(magnitude_f64(&bp, NYQUIST), 0.0, "band-pass Nyquist");

        let notch = CoeffsF64::notch(FC, FS, Q);
        assert_near(magnitude_f64(&notch, 0.0), 1.0, "notch DC");
        assert_near(magnitude_f64(&notch, FC), 0.0, "notch cutoff");
        assert_near(magnitude_f64(&notch, NYQUIST), 1.0, "notch Nyquist");

        let ap = CoeffsF64::all_pass(FC, FS, Q);
        for f in [0.0, 100.0, FC, 5000.0, NYQUIST] {
            assert_near(magnitude_f64(&ap, f), 1.0, "all-pass");
        }
    }

    #[test]
    fn bell_and_shelves_magnitudes_f64() {
        let db = 6.0;
        let a = libm::pow(10.0, db / 40.0);
        let bell = CoeffsF64::bell(FC, FS, Q, db);
        assert_near(magnitude_f64(&bell, 0.0), 1.0, "bell DC");
        assert_near(magnitude_f64(&bell, FC), a * a, "bell cutoff");
        assert_near(magnitude_f64(&bell, NYQUIST), 1.0, "bell Nyquist");

        let ls = CoeffsF64::low_shelf(FC, FS, Q, db);
        assert_near(magnitude_f64(&ls, 0.0), a * a, "low shelf DC");
        assert_near(magnitude_f64(&ls, FC), a, "low shelf cutoff");
        assert_near(magnitude_f64(&ls, NYQUIST), 1.0, "low shelf Nyquist");

        let hs = CoeffsF64::high_shelf(FC, FS, Q, db);
        assert_near(magnitude_f64(&hs, 0.0), 1.0, "high shelf DC");
        assert_near(magnitude_f64(&hs, FC), a, "high shelf cutoff");
        assert_near(magnitude_f64(&hs, NYQUIST), a * a, "high shelf Nyquist");
    }

    #[test]
    fn zero_db_bell_and_shelves_give_the_identity_mix_and_return_the_input_f64() {
        // pow(10, 0) is exactly 1, so A = 1, the mix is exactly (1, k, 1) with k = 1 / q, and
        // the output hp + k·bp + lp equals the input in exact arithmetic.
        let k = 1.0 / Q;
        for c in [
            CoeffsF64::bell(FC, FS, Q, 0.0),
            CoeffsF64::low_shelf(FC, FS, Q, 0.0),
            CoeffsF64::high_shelf(FC, FS, Q, 0.0),
        ] {
            assert_eq!((c.k, c.m_hp, c.m_bp, c.m_lp), (k, 1.0, k, 1.0));
            assert_eq!(c.g, libm::tan(PI_F64 * FC / FS));
            let mut buf = [0.0_f64; 256];
            for (n, x) in buf.iter_mut().enumerate() {
                *x = ((n * 37 % 101) as f64) / 101.0 - 0.5;
            }
            let input = buf;
            process_f64(&c, &mut StateF64::default(), &mut buf);
            for (y, x) in buf.iter().zip(input) {
                assert!((y - x).abs() <= 1e-12, "{y} vs {x}");
            }
        }
    }

    #[test]
    fn f32_designs_are_close_to_f64_designs() {
        let (fc, fs, q, db) = (FC as f32, FS as f32, Q as f32, DB as f32);
        let pairs = [
            (
                CoeffsF32::low_pass(fc, fs, q),
                CoeffsF64::low_pass(FC, FS, Q),
            ),
            (
                CoeffsF32::high_pass(fc, fs, q),
                CoeffsF64::high_pass(FC, FS, Q),
            ),
            (
                CoeffsF32::band_pass(fc, fs, q),
                CoeffsF64::band_pass(FC, FS, Q),
            ),
            (CoeffsF32::notch(fc, fs, q), CoeffsF64::notch(FC, FS, Q)),
            (
                CoeffsF32::all_pass(fc, fs, q),
                CoeffsF64::all_pass(FC, FS, Q),
            ),
            (
                CoeffsF32::bell(fc, fs, q, db),
                CoeffsF64::bell(FC, FS, Q, DB),
            ),
            (
                CoeffsF32::low_shelf(fc, fs, q, db),
                CoeffsF64::low_shelf(FC, FS, Q, DB),
            ),
            (
                CoeffsF32::high_shelf(fc, fs, q, db),
                CoeffsF64::high_shelf(FC, FS, Q, DB),
            ),
        ];
        for (c32, c64) in pairs {
            let a = [c32.g, c32.k, c32.d, c32.m_hp, c32.m_bp, c32.m_lp];
            let b = [c64.g, c64.k, c64.d, c64.m_hp, c64.m_bp, c64.m_lp];
            for (x, y) in a.iter().zip(b) {
                assert!(
                    (f64::from(*x) - y).abs() <= 1e-5 * (1.0 + y.abs()),
                    "{x} vs {y}"
                );
            }
        }
    }

    /// The low-pass mix against the biquad with the bilinear-transform low-pass coefficients for
    /// the same `g` and `k`: `H(s) = 1 / (s² + k·s + 1)` with `s = (1/g)·(z - 1)/(z + 1)` gives
    /// `b = [g², 2g², g²] / a0`, `a1 = 2(g² - 1) / a0`, `a2 = (1 - k·g + g²) / a0`, with
    /// `a0 = 1 + k·g + g²`.
    #[test]
    fn low_pass_matches_bilinear_biquad_f64() {
        use crate::biquad;

        for &(cutoff, q) in &[(1000.0, 0.75), (100.0, 2.0), (8000.0, 0.5)] {
            let g = libm::tan(PI_F64 * cutoff / FS);
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
