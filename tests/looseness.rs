//! How loose are the proved whole-block error bounds? A measurement, not a proof.
//!
//! For each filter case with a proved bound in `proofs/README.md` (inputs at most 1 in size and a
//! start from zero), this runs the crate's `process_*` functions on long blocks of test signals and
//! compares every output with the same filter run on the same stored coefficients and inputs in
//! double-double arithmetic (about 106 bits), which stands in for the exact arithmetic the proofs
//! compare against. It prints a Markdown table: the proved bound, the largest error seen and their
//! ratio. The gain ramp's gains are compared with the exact straight line in the same way.
//!
//! Everything it prints is measured, not proved. The test is ignored by default; run it with
//!
//! ```sh
//! cargo test --release --features std --test looseness -- --ignored --nocapture
//! ```
//!
//! With the defaults a run takes about 65 seconds in release mode on Apple silicon (measured once).
//!
//! `LOOSENESS_LEN` sets the block length (default 2^20 samples) and `LOOSENESS_SEEDS` the number
//! of seeds for each random signal (default 8). Without `--features std` the fused functions are
//! skipped.

use conjure_dsp_lib::{biquad, gain, one_pole, smoother, svf};
use core::f64::consts::PI;

// ---------------------------------------------------------------------------------------------
// Double-double arithmetic: a value is hi + lo with |lo| <= ulp(hi)/2. Each operation below is
// accurate to a relative error of a few units in 2^-104 (standard algorithms, Dekker and Knuth;
// not proved here), far below the errors being measured.

#[derive(Clone, Copy, Debug, Default)]
struct Dd {
    hi: f64,
    lo: f64,
}

fn two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    let bb = s - a;
    (s, (a - (s - bb)) + (b - bb))
}

fn quick_two_sum(a: f64, b: f64) -> (f64, f64) {
    let s = a + b;
    (s, b - (s - a))
}

impl Dd {
    fn new(x: f64) -> Dd {
        Dd { hi: x, lo: 0.0 }
    }

    fn add(self, o: Dd) -> Dd {
        let (s, e) = two_sum(self.hi, o.hi);
        let (t, f) = two_sum(self.lo, o.lo);
        let (s, e) = quick_two_sum(s, e + t);
        let (hi, lo) = quick_two_sum(s, e + f);
        Dd { hi, lo }
    }

    fn neg(self) -> Dd {
        Dd {
            hi: -self.hi,
            lo: -self.lo,
        }
    }

    fn sub(self, o: Dd) -> Dd {
        self.add(o.neg())
    }

    fn mul(self, o: Dd) -> Dd {
        let p = self.hi * o.hi;
        let e = self.hi.mul_add(o.hi, -p);
        let e = e + (self.hi * o.lo + self.lo * o.hi);
        let (hi, lo) = quick_two_sum(p, e);
        Dd { hi, lo }
    }

    /// |x - self|, rounded to f64.
    fn dist(self, x: f64) -> f64 {
        let d = Dd::new(x).sub(self);
        (d.hi + d.lo).abs()
    }
}

// ---------------------------------------------------------------------------------------------
// Reference filters, in double-double, on the stored coefficients and inputs (as f64 values).

fn ref_one_pole(a: f64, xs: &[f64]) -> Vec<Dd> {
    let a = Dd::new(a);
    let mut y = Dd::default();
    xs.iter()
        .map(|&x| {
            y = Dd::new(x).add(a.mul(y));
            y
        })
        .collect()
}

fn ref_smoother(c: f64, xs: &[f64]) -> Vec<Dd> {
    let c = Dd::new(c);
    let mut y = Dd::default();
    xs.iter()
        .map(|&x| {
            y = y.add(c.mul(Dd::new(x).sub(y)));
            y
        })
        .collect()
}

#[derive(Clone, Copy)]
struct Bq {
    b0: f64,
    b1: f64,
    b2: f64,
    a1: f64,
    a2: f64,
}

fn ref_biquad(c: Bq, xs: &[f64]) -> Vec<Dd> {
    let (b0, b1, b2, a1, a2) = (
        Dd::new(c.b0),
        Dd::new(c.b1),
        Dd::new(c.b2),
        Dd::new(c.a1),
        Dd::new(c.a2),
    );
    let (mut s1, mut s2) = (Dd::default(), Dd::default());
    xs.iter()
        .map(|&x| {
            let x = Dd::new(x);
            let y = b0.mul(x).add(s1);
            s1 = b1.mul(x).sub(a1.mul(y)).add(s2);
            s2 = b2.mul(x).sub(a2.mul(y));
            y
        })
        .collect()
}

#[derive(Clone, Copy)]
struct Sv {
    g: f64,
    k: f64,
    d: f64,
}

/// The low-pass SVF (mix (0, 0, 1)); `k + g` is exact here, as in `svf.svfStep_real`.
fn ref_svf_lp(c: Sv, xs: &[f64]) -> Vec<Dd> {
    let (g, d) = (Dd::new(c.g), Dd::new(c.d));
    let kg = Dd::new(c.k).add(g);
    let (mut s1, mut s2) = (Dd::default(), Dd::default());
    xs.iter()
        .map(|&x| {
            let hp = Dd::new(x).sub(kg.mul(s1)).sub(s2).mul(d);
            let bp = g.mul(hp).add(s1);
            let lp = g.mul(bp).add(s2);
            s1 = g.mul(hp).add(bp);
            s2 = g.mul(bp).add(lp);
            lp
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------
// Test signals, all at most 1 in size.

struct Rng(u64);

impl Rng {
    /// xorshift64*: a small, fixed pseudo-random generator, so runs are repeatable.
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// Uniform in [-1, 1).
    fn uniform(&mut self) -> f64 {
        ((self.next() >> 11) as f64) * 2f64.powi(-52) - 1.0
    }
}

/// The signals, each with a name. `freq` is a frequency in cycles per sample (the filter's cutoff,
/// or for the one-pole and smoother `(1 - |a|) / 2π`); `h` is the filter's impulse response, used
/// for the "matched signs" signal: the input whose signs are those of the impulse response read
/// backwards, which makes the exact output as large as it can be once per period.
fn signals(n: usize, seeds: u64, freq: f64, h: &[f64]) -> Vec<(String, Vec<f64>)> {
    let mut out = Vec::new();
    for s in 1..=seeds {
        let mut r = Rng(0x9E37_79B9_7F4A_7C15 ^ s.wrapping_mul(0xD1B5_4A32_D192_ED03));
        out.push((
            format!("uniform random, seed {s}"),
            (0..n).map(|_| r.uniform()).collect(),
        ));
        out.push((
            format!("random ±1, seed {s}"),
            (0..n)
                .map(|_| if r.next() >> 63 == 0 { 1.0 } else { -1.0 })
                .collect(),
        ));
    }
    out.push((
        "alternating ±1".into(),
        (0..n)
            .map(|i| if i % 2 == 0 { 1.0 } else { -1.0 })
            .collect(),
    ));
    out.push(("step +1".into(), vec![1.0; n]));
    out.push((
        "sine at cutoff".into(),
        (0..n).map(|i| (2.0 * PI * freq * i as f64).sin()).collect(),
    ));
    out.push((
        "square at cutoff".into(),
        (0..n)
            .map(|i| {
                if (2.0 * PI * freq * i as f64).sin() >= 0.0 {
                    1.0
                } else {
                    -1.0
                }
            })
            .collect(),
    ));
    let p = h.len();
    out.push((
        format!("matched signs, period {p}"),
        (0..n)
            .map(|i| if h[p - 1 - i % p] >= 0.0 { 1.0 } else { -1.0 })
            .collect(),
    ));
    out
}

/// The impulse response of a reference filter, cut where it has decayed below 1e-13 of its peak
/// (at most `max` samples).
fn impulse(reference: &dyn Fn(&[f64]) -> Vec<Dd>, max: usize) -> Vec<f64> {
    let mut x = vec![0.0; max];
    x[0] = 1.0;
    let h: Vec<f64> = reference(&x).iter().map(|d| d.hi).collect();
    let peak = h.iter().fold(0.0_f64, |m, v| m.max(v.abs()));
    let last = h.iter().rposition(|v| v.abs() > 1e-13 * peak).unwrap_or(0);
    h[..=last.max(1)].to_vec()
}

// ---------------------------------------------------------------------------------------------
// Measuring one case.

struct Worst {
    err: f64,
    signal: String,
}

/// Runs `run` (the crate's function, on the whole block at once) on each signal rounded to `T`,
/// and returns the largest distance of any output from `reference` run on the same stored inputs.
fn measure<T: Copy + Into<f64>>(
    sigs: &[(String, Vec<f64>)],
    round: fn(f64) -> T,
    run: &dyn Fn(&mut [T]),
    reference: &dyn Fn(&[f64]) -> Vec<Dd>,
) -> Worst {
    let mut worst = Worst {
        err: 0.0,
        signal: String::new(),
    };
    for (name, xs) in sigs {
        let mut buf: Vec<T> = xs.iter().map(|&x| round(x)).collect();
        let stored: Vec<f64> = buf.iter().map(|&x| x.into()).collect();
        run(&mut buf);
        let exact = reference(&stored);
        let err = buf
            .iter()
            .zip(&exact)
            .fold(0.0_f64, |m, (&y, e)| m.max(e.dist(y.into())));
        if err > worst.err {
            worst = Worst {
                err,
                signal: name.clone(),
            };
        }
    }
    worst
}

/// Measures the unfused function (`$plain`) and, with the `std` feature, the fused one
/// (`$fused`), on the same signals against the same reference. `$b` is the block.
macro_rules! both {
    ($sigs:expr, $round:expr, $reference:expr, |$b:ident: $t:ty| $plain:expr, $fused:expr) => {{
        let plain = measure($sigs, $round, &|$b: $t| $plain, $reference);
        #[cfg(feature = "std")]
        let fused = Some(measure($sigs, $round, &|$b: $t| $fused, $reference));
        #[cfg(not(feature = "std"))]
        let fused = None;
        (plain, fused)
    }};
}

/// The `Q` of the worked SVF examples, as written there (not exactly 1/√2).
#[allow(clippy::approx_constant)]
const Q_WORKED: f64 = 0.7071;

fn r32(x: f64) -> f32 {
    x as f32
}

fn r64(x: f64) -> f64 {
    x
}

/// `m / 2^e`, exactly (every value used here is representable).
fn q(m: i64, e: i32) -> f64 {
    m as f64 * 2f64.powi(-e)
}

struct Row {
    filter: &'static str,
    case: String,
    bound: f64,
    bound_text: &'static str,
    plain: Worst,
    fused: Option<Worst>,
}

fn print_rows(rows: &[Row], n: usize, seeds: u64) {
    println!();
    println!(
        "Block length {n}, {seeds} seeds per random signal, start from zero, reference in double-double."
    );
    println!();
    println!(
        "| Filter | Case | Proved bound | Largest observed error | Bound ÷ observed | Fused: largest observed | Worst signal |"
    );
    println!("|---|---|---|---|---|---|---|");
    for r in rows {
        let fused = match &r.fused {
            Some(w) => format!("{:.2e}", w.err),
            None => "(not run)".into(),
        };
        println!(
            "| {} | {} | {} | {:.2e} | {:.2e} | {} | {} |",
            r.filter,
            r.case,
            r.bound_text,
            r.plain.err,
            r.bound / r.plain.err,
            fused,
            r.plain.signal
        );
    }
}

fn env_or(name: &str, default: u64) -> u64 {
    std::env::var(name)
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(default)
}

// ---------------------------------------------------------------------------------------------

#[test]
#[ignore = "a measurement, run by hand (see the top of this file)"]
fn looseness_of_block_error_bounds() {
    let n = env_or("LOOSENESS_LEN", 1 << 20) as usize;
    let seeds = env_or("LOOSENESS_SEEDS", 8);
    let mut rows = Vec::new();

    // One-pole: the rows of the one-pole table (each theorem covers every real A with |A| at most
    // the row's bound, so also the negative a).
    for &(prec, a, bound, text) in &[
        ("f32", 0.5, 3.6e-7, "3.6 × 10⁻⁷"),
        ("f32", -0.5, 3.6e-7, "3.6 × 10⁻⁷"),
        ("f32", 0.99, 1.19e-3, "1.19 × 10⁻³"),
        ("f32", -0.99, 1.19e-3, "1.19 × 10⁻³"),
        ("f32", 0.999, 0.12, "0.12"),
        ("f64", 0.99, 2.21e-12, "2.21 × 10⁻¹²"),
        ("f64", -0.99, 2.21e-12, "2.21 × 10⁻¹²"),
        ("f64", 0.999, 2.22e-10, "2.22 × 10⁻¹⁰"),
    ] {
        let a_stored = if prec == "f32" {
            f64::from(a as f32)
        } else {
            a
        };
        let reference = move |xs: &[f64]| ref_one_pole(a_stored, xs);
        let h = impulse(&reference, 1 << 16);
        let sigs = signals(n, seeds, (1.0 - f64::abs(a)) / (2.0 * PI), &h);
        let (plain, fused) = if prec == "f32" {
            let a32 = a as f32;
            both!(
                &sigs,
                r32,
                &reference,
                |b: &mut [f32]| one_pole::process_f32(a32, &mut 0.0, b),
                one_pole::process_fma_f32(a32, &mut 0.0, b)
            )
        } else {
            both!(
                &sigs,
                r64,
                &reference,
                |b: &mut [f64]| one_pole::process_f64(a, &mut 0.0, b),
                one_pole::process_fma_f64(a, &mut 0.0, b)
            )
        };
        rows.push(Row {
            filter: "one_pole",
            case: format!("{prec}, a = {a}"),
            bound,
            bound_text: text,
            plain,
            fused,
        });
    }

    // Smoother: the rows of the smoother table. The reference uses the stored c = 1 - a.
    for &(prec, a, bound, text) in &[
        ("f32", 0.99, 6.2e-6, "6.2 × 10⁻⁶"),
        ("f32", 0.999, 6e-5, "6 × 10⁻⁵"),
        ("f64", 0.99, 1.16e-14, "1.16 × 10⁻¹⁴"),
        ("f64", 0.999, 1.12e-13, "1.12 × 10⁻¹³"),
    ] {
        let c_stored = if prec == "f32" {
            f64::from(1.0 - a as f32)
        } else {
            1.0 - a
        };
        let reference = move |xs: &[f64]| ref_smoother(c_stored, xs);
        let h = impulse(&reference, 1 << 16);
        let sigs = signals(n, seeds, (1.0 - a) / (2.0 * PI), &h);
        let (plain, fused) = if prec == "f32" {
            let a32 = a as f32;
            both!(
                &sigs,
                r32,
                &reference,
                |b: &mut [f32]| smoother::process_f32(a32, &mut 0.0, b),
                smoother::process_fma_f32(a32, &mut 0.0, b)
            )
        } else {
            both!(
                &sigs,
                r64,
                &reference,
                |b: &mut [f64]| smoother::process_f64(a, &mut 0.0, b),
                smoother::process_fma_f64(a, &mut 0.0, b)
            )
        };
        rows.push(Row {
            filter: "smoother",
            case: format!("{prec}, a = {a}"),
            bound,
            bound_text: text,
            plain,
            fused,
        });
    }

    // Biquad: the stored coefficients of the worked examples (Biquad/BlockF32.lean and
    // Biquad/BlockF64.lean), RBJ low-pass at 48 kHz, Q = 0.7071 unless said.
    let bq = |b: i64, eb: i32, a1: i64, ea1: i32, a2: i64, ea2: i32| Bq {
        b0: q(b, eb),
        b1: q(b, eb - 1),
        b2: q(b, eb),
        a1: q(a1, ea1),
        a2: q(a2, ea2),
    };
    let biquads: Vec<(&str, &str, Bq, f64, f64, &str)> = vec![
        (
            "f32",
            "100 Hz",
            bq(11666743, 38, -16621929, 23, 8234745, 23),
            100.0 / 48e3,
            17.1,
            "17.1",
        ),
        (
            "f32",
            "250 Hz",
            bq(2247579, 33, -8194527, 22, 4004613, 22),
            250.0 / 48e3,
            0.979,
            "0.979",
        ),
        (
            "f32",
            "1 kHz",
            bq(8409811, 31, -3807043, 21, 13941935, 24),
            1e3 / 48e3,
            0.0542,
            "0.0542",
        ),
        (
            "f32",
            "10 kHz",
            bq(14776959, 26, -5160087, 24, 12639319, 26),
            10e3 / 48e3,
            1.81e-4,
            "1.81 × 10⁻⁴",
        ),
        (
            "f32",
            "20 kHz",
            bq(5782305, 23, 2683577, 21, 4006303, 23),
            20e3 / 48e3,
            0.0128,
            "0.0128",
        ),
        (
            "f32",
            "1 kHz, Q = 0.4",
            bq(1974369, 29, -14300455, 23, 6035245, 23),
            1e3 / 48e3,
            0.00559,
            "0.00559",
        ),
        (
            "f32",
            "1 kHz, Q = 0.5 (closePoles, ε = 0.06)",
            bq(8125429, 31, -1839153, 20, 12903151, 24),
            1e3 / 48e3,
            0.0122,
            "0.0122",
        ),
        (
            "f32",
            "1 kHz, Q = 0.5 (realPoles)",
            bq(8125429, 31, -1839153, 20, 12903151, 24),
            1e3 / 48e3,
            734.0,
            "734",
        ),
        (
            "f64",
            "10 Hz",
            bq(
                8084163468405705,
                74,
                -8998862108169191,
                52,
                8990540380915529,
                53,
            ),
            10.0 / 48e3,
            1.02e-6,
            "1.02 × 10⁻⁶",
        ),
        (
            "f64",
            "100 Hz",
            bq(
                3131767523398125,
                66,
                -8923830126573345,
                52,
                2210497545441683,
                51,
            ),
            100.0 / 48e3,
            1.02e-8,
            "1.02 × 10⁻⁸",
        ),
        (
            "f64",
            "1 kHz",
            bq(
                564372872879827,
                57,
                -4087781399317133,
                51,
                7485019560747497,
                53,
            ),
            1e3 / 48e3,
            1.01e-10,
            "1.01 × 10⁻¹⁰",
        ),
        (
            "f64",
            "10 kHz",
            bq(
                7933319284775931,
                55,
                -2770300704857065,
                53,
                6785682939568013,
                55,
            ),
            10e3 / 48e3,
            3.37e-13,
            "3.37 × 10⁻¹³",
        ),
        (
            "f64",
            "1 kHz, Q = 0.4",
            bq(
                4239925057238661,
                60,
                -3838749082463727,
                51,
                405018420822039,
                49,
            ),
            1e3 / 48e3,
            1.04e-11,
            "1.04 × 10⁻¹¹",
        ),
    ];
    for (prec, case, c, freq, bound, text) in biquads {
        let reference = move |xs: &[f64]| ref_biquad(c, xs);
        let h = impulse(&reference, 1 << 17);
        let sigs = signals(n, seeds, freq, &h);
        let (plain, fused) = if prec == "f32" {
            let c32 = biquad::CoeffsF32 {
                b0: c.b0 as f32,
                b1: c.b1 as f32,
                b2: c.b2 as f32,
                a1: c.a1 as f32,
                a2: c.a2 as f32,
            };
            // Every stored value converts exactly.
            assert_eq!(
                [c32.b0, c32.b1, c32.b2, c32.a1, c32.a2].map(f64::from),
                [c.b0, c.b1, c.b2, c.a1, c.a2],
                "biquad f32 {case}: a stored coefficient is not a binary32 value"
            );
            both!(
                &sigs,
                r32,
                &reference,
                |b: &mut [f32]| biquad::process_f32(&c32, &mut biquad::StateF32::default(), b),
                biquad::process_fma_f32(&c32, &mut biquad::StateF32::default(), b)
            )
        } else {
            let c64 = biquad::CoeffsF64 {
                b0: c.b0,
                b1: c.b1,
                b2: c.b2,
                a1: c.a1,
                a2: c.a2,
            };
            both!(
                &sigs,
                r64,
                &reference,
                |b: &mut [f64]| biquad::process_f64(&c64, &mut biquad::StateF64::default(), b),
                biquad::process_fma_f64(&c64, &mut biquad::StateF64::default(), b)
            )
        };
        rows.push(Row {
            filter: "biquad",
            case: format!("{prec}, {case}"),
            bound,
            bound_text: text,
            plain,
            fused,
        });
    }

    // SVF: the low-pass rows of the SVF table (Q = 0.7071, 48 kHz), from the design functions,
    // checked against the stored values in Svf/BlockF32.lean and Svf/BlockF64.lean.
    let svfs: Vec<(&str, f64, Sv, f64, &str)> = vec![
        (
            "f32",
            20.0,
            Sv {
                g: q(11244205, 33),
                k: q(11863397, 23),
                d: q(16746185, 24),
            },
            0.0126,
            "0.0126",
        ),
        (
            "f32",
            100.0,
            Sv {
                g: q(14055449, 31),
                k: q(11863397, 23),
                d: q(16622641, 24),
            },
            0.00267,
            "0.00267",
        ),
        (
            "f32",
            1e3,
            Sv {
                g: q(8797095, 27),
                k: q(11863397, 23),
                d: q(7646937, 23),
            },
            0.000459,
            "0.000459",
        ),
        (
            "f32",
            10e3,
            Sv {
                g: q(3218403, 22),
                k: q(11863397, 23),
                d: q(12548565, 25),
            },
            0.000475,
            "0.000475",
        ),
        (
            "f64",
            20.0,
            Sv {
                g: q(1509171582407745, 60),
                k: q(6369112752609951, 52),
                d: q(4495270190598775, 52),
            },
            2.35e-11,
            "2.35 × 10⁻¹¹",
        ),
        (
            "f64",
            100.0,
            Sv {
                g: q(7545961350812463, 60),
                k: q(6369112752609951, 52),
                d: q(8924212422413603, 53),
            },
            4.98e-12,
            "4.98 × 10⁻¹²",
        ),
        (
            "f64",
            1e3,
            Sv {
                g: q(4722904235380461, 56),
                k: q(6369112752609951, 52),
                d: q(8210836103189255, 53),
            },
            8.55e-13,
            "8.55 × 10⁻¹³",
        ),
        (
            "f64",
            10e3,
            Sv {
                g: q(3455733537133371, 52),
                k: q(6369112752609951, 52),
                d: q(3368480173622515, 53),
            },
            8.84e-13,
            "8.84 × 10⁻¹³",
        ),
    ];
    for (prec, fc, c, bound, text) in svfs {
        let reference = move |xs: &[f64]| ref_svf_lp(c, xs);
        let h = impulse(&reference, 1 << 17);
        let sigs = signals(n, seeds, fc / 48e3, &h);
        let (plain, fused) = if prec == "f32" {
            let c32 = svf::CoeffsF32::low_pass(fc as f32, 48_000.0, Q_WORKED as f32);
            assert_eq!(
                (f64::from(c32.g), f64::from(c32.k), f64::from(c32.d)),
                (c.g, c.k, c.d),
                "f32 SVF design at {fc} Hz differs from the stored values"
            );
            both!(
                &sigs,
                r32,
                &reference,
                |b: &mut [f32]| svf::process_f32(&c32, &mut svf::StateF32::default(), b),
                svf::process_fma_f32(&c32, &mut svf::StateF32::default(), b)
            )
        } else {
            let c64 = svf::CoeffsF64::low_pass(fc, 48_000.0, Q_WORKED);
            assert_eq!(
                (c64.g, c64.k, c64.d),
                (c.g, c.k, c.d),
                "f64 SVF design at {fc} Hz differs from the stored values"
            );
            both!(
                &sigs,
                r64,
                &reference,
                |b: &mut [f64]| svf::process_f64(&c64, &mut svf::StateF64::default(), b),
                svf::process_fma_f64(&c64, &mut svf::StateF64::default(), b)
            )
        };
        rows.push(Row {
            filter: "svf",
            case: format!("{prec}, {fc} Hz"),
            bound,
            bound_text: text,
            plain,
            fused,
        });
    }

    print_rows(&rows, n, seeds);
    for r in &rows {
        for (kind, w) in [("unfused", Some(&r.plain)), ("fused", r.fused.as_ref())] {
            if let Some(w) = w {
                assert!(
                    w.err <= r.bound,
                    "{} {} ({kind}): observed error {:.3e} above the proved bound {:.3e}",
                    r.filter,
                    r.case,
                    w.err,
                    r.bound
                );
            }
        }
    }
}

/// The gain ramp: each gain against the exact line `S + (E - S)·i/n`, with the proved bound
/// `u·|S| + 5u·|E - S| + (2n + 4)·η` (`gain.rampGain_f64_error`, `gain.rampGain_f32_error`).
/// The gains are read by ramping a block of ones (`1·g` is exact).
#[test]
#[ignore = "a measurement, run by hand (see the top of this file)"]
fn looseness_of_ramp_bounds() {
    let seeds = env_or("LOOSENESS_SEEDS", 8);
    let mut pairs: Vec<(f64, f64)> = vec![
        (0.0, 1.0),
        (1.0, 0.0),
        (0.3, -1.7),
        (-1.0, 1.0),
        (0.001, 1.0),
        (0.9, 0.95),
    ];
    let mut r = Rng(12345);
    for _ in 0..seeds {
        pairs.push((r.uniform() * 2.0, r.uniform() * 2.0));
    }
    let lengths = [3_usize, 64, 1000, 4096, 48_000, 1 << 20];
    println!();
    println!(
        "| Precision | Block lengths | Start, end pairs | Largest observed error | Its bound | \
         Bound ÷ observed there | Bound ÷ observed, smallest over all gains |"
    );
    println!("|---|---|---|---|---|---|---|");
    for prec in ["f32", "f64"] {
        let (u, eta) = if prec == "f32" {
            (2f64.powi(-24), 2f64.powi(-150))
        } else {
            (2f64.powi(-53), 2f64.powi(-1075))
        };
        let mut worst_err = 0.0_f64;
        let mut worst_bound = 0.0_f64;
        let mut min_ratio = f64::INFINITY;
        for &(s0, e0) in &pairs {
            for &n in &lengths {
                let (s, e, gains): (f64, f64, Vec<f64>) = if prec == "f32" {
                    let (s, e) = (s0 as f32, e0 as f32);
                    let mut b = vec![1.0_f32; n];
                    gain::ramp_f32(s, e, &mut b);
                    (
                        f64::from(s),
                        f64::from(e),
                        b.iter().map(|&g| f64::from(g)).collect(),
                    )
                } else {
                    let mut b = vec![1.0_f64; n];
                    gain::ramp_f64(s0, e0, &mut b);
                    (s0, e0, b)
                };
                let bound = u * s.abs() + 5.0 * u * (e - s).abs() + (2.0 * n as f64 + 4.0) * eta;
                let diff = Dd::new(e).sub(Dd::new(s));
                for (i, &g) in gains.iter().enumerate() {
                    // The exact line, in double-double: S + (E - S)·i/n, with the division done
                    // as a multiplication by i and a correction (error far below u).
                    let num = diff.mul(Dd::new(i as f64));
                    let qhi = num.hi / n as f64;
                    let rem = num.sub(Dd::new(qhi).mul(Dd::new(n as f64)));
                    let line = Dd::new(s).add(Dd::new(qhi)).add(Dd::new(rem.hi / n as f64));
                    let err = line.dist(g);
                    if err > 0.0 {
                        min_ratio = min_ratio.min(bound / err);
                    }
                    if err > worst_err {
                        worst_err = err;
                        worst_bound = bound;
                    }
                    assert!(
                        err <= bound,
                        "gain ramp {prec}, start {s}, end {e}, n = {n}, gain {i}: observed error \
                         {err:.3e} above the proved bound {bound:.3e}"
                    );
                }
            }
        }
        println!(
            "| {prec} | {lengths:?} | {} | {worst_err:.2e} | {worst_bound:.2e} | {:.2} | \
             {min_ratio:.2} |",
            pairs.len(),
            worst_bound / worst_err
        );
    }
}
