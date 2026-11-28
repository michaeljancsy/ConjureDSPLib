# ConjureDSPLib

A Rust library of audio DSP building blocks, with all implementations verified in Lean.

What sets it apart is a set of machine-checked [Lean 4](https://lean-lang.org) proofs about the
code. For each function they state exactly which floating-point operations it performs and that it
never fails (no panic, no out-of-bounds index). They also bound how far the filters' outputs can be
from exact arithmetic, and the gain ramp's gains from the exact straight line, under stated
conditions and assumptions.

The proofs are about a translation of the Rust into Lean by
[Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas),
and hold under stated conditions and the assumptions listed [below](#what-is-assumed-not-proved).

## What's in it

Every module has `f32` and `f64` versions (functions end in `_f32` / `_f64`, types in `F32` /
`F64`).

- `gain`: multiply by a fixed gain (`apply`), or by a gain that moves in a straight line across a
  block (`ramp`).
- `one_pole`: one-pole feedback filter, `y[n] = x[n] + a·y[n-1]`.
- `smoother`: one-pole smoother, `y[n] = y[n-1] + (1 - a)·(x[n] - y[n-1])`, for gliding toward a
  target; `step_coeff` and `process_coeff` take the fraction `c = 1 - a` directly.
- `biquad`: second-order filter in transposed direct form II, with coefficients you supply.
- `svf`: trapezoidal state-variable filter, with design functions for eight shapes (low-pass,
  high-pass, band-pass, notch, all-pass, bell, low shelf, high shelf), whose formulas follow
  A. Simper (Cytomic).
- `delay`: delay line of a whole number of samples (no interpolation), in a buffer the caller owns;
  a block at a time (`process`), or one sample at a time, reading before writing, for feedback
  (`read`, `write`).

With the optional cargo feature `std`, `one_pole`, `smoother`, `biquad` and `svf` also have fused
multiply-add versions (`step_fma_f64`, `process_fma_f64` and the `_f32` ones, and for the smoother
also `step_coeff_fma_f64` and `process_coeff_fma_f64`); see
[Fused multiply-add](#fused-multiply-add-the-std-feature).

## How to use it

Add it from crates.io:

```toml
[dependencies]
conjure-dsp-lib = "0.1"
```

For example, a low-pass filter on one channel:

```rust
use conjure_dsp_lib::svf;

// A 1 kHz low-pass at 48 kHz, Q = 0.7071, in f32.
let coeffs = svf::CoeffsF32::low_pass(1_000.0, 48_000.0, 0.7071);
let mut state = svf::StateF32::default(); // one per channel, kept between blocks

let mut block = [0.0_f32; 64]; // your audio
svf::process_f32(&coeffs, &mut state, &mut block); // filters in place
```

The crate declares a minimum Rust version of 1.93 (`rust-version` in `Cargo.toml`); this
repository's own checks use exactly Rust 1.93.1 (`rust-toolchain.toml`). Its one dependency is
`libm`, pinned exactly to 0.2.16 with default features off.

For the fused multiply-add functions, turn on the `std` feature:

```toml
[dependencies]
conjure-dsp-lib = { version = "0.1", features = ["std"] }
```

The documentation of each module (`cargo doc --open`) gives exact behaviour, including edge cases
such as empty blocks, an empty delay buffer and changing the delay between calls.

## Real-time use

Per-sample code does no memory allocation, takes no locks and makes no system calls.

- **Allocation and system calls** are ruled out by the build together with one property of the
  code: the crate is `no_std` and has no `extern crate alloc` or `extern crate std` (the compiler
  does not forbid adding them), and it forbids `unsafe` code when the crate itself is built (as
  `scripts/check.sh` does). `libm` is relied on to do the same.
- **Locks:** that it takes none is a property of the code (it uses no atomics or other
  synchronization), not enforced by the compiler.
- **Panics:** a panic would run the program's panic handler, which can allocate, lock and make
  system calls. That the functions never panic is proved of the translated code.
- None of this is otherwise proved in Lean.

With the `std` feature on, the crate is no longer `no_std`: it links Rust's standard library, so
the build no longer rules out allocation and system calls. The feature only adds the fused
functions, which call `f64::mul_add` and `f32::mul_add`; the source of every other function is
the same in both builds, since nothing else in the code depends on the feature (a property of the
code, not proved). With the feature off, the build is the `no_std` one described above. The
proofs are about the build with the feature on (Charon translates it with `--features std`),
which contains every function of the other build too.

On processors with a fused multiply-add instruction (64-bit Arm, Apple silicon included, and
x86-64 built with the `fma` target feature), each `mul_add` is expected to compile to that one
instruction; otherwise it is expected to be a call to the platform C library's `fma` routine
(expected, not measured).

## Fused multiply-add (the `std` feature)

The fused functions use `mul_add`, one rounding of `a·b + c`, in a fixed grouping, on every
processor:

- `one_pole::step_fma_*`: `y = a.mul_add(state, x)`.
- `smoother::step_coeff_fma_*`: `y = c.mul_add(x - state, state)`; `smoother::step_fma_*` the
  same with `c = 1.0 - a` (computed once per block by `process_fma_*`).
- `biquad::step_fma_*`: `y = b0.mul_add(x, s1)`, `s1 = b1.mul_add(x, -(a1·y)) + s2`,
  `s2 = b2.mul_add(x, -(a2·y))`.
- `svf::step_fma_*`: `hp = ((-(k + g)).mul_add(s1, x) - s2)·d`, `bp = g.mul_add(hp, s1)`,
  `lp = g.mul_add(bp, s2)`, `s1 = g.mul_add(hp, bp)`, `s2 = g.mul_add(bp, lp)`,
  `y = m_lp.mul_add(lp, m_hp.mul_add(hp, m_bp·bp))`. The coefficients come from the same
  (unfused) `CoeffsF64::new` and design functions.

This is how clang contracts the unfused expressions with its default `-ffp-contract=on`, so on
Apple silicon each fused step computes the same as the same step written in C or C++ and built
with clang (worked out outside Lean, not proved: checked against Apple clang 17, arm64, -O2). For
the SVF that is the step only: clang also fuses `1 + g·(g + k)` in the coefficient calculation,
so a C or C++ SVF can get a different `d` from this crate's unfused `CoeffsF64::new`, and the
whole filter matches only if `d` is computed unfused there too (worked out outside Lean, not
proved).

The proofs show that each fused function computes exactly this grouping, never fails, and meets
the same whole-block error bounds (and, for the smoother, the same settling bounds) as its unfused
version, with the same constants. The `_of_inputs` and settling theorems have exactly the unfused
ones' conditions; the others replace the
no-overflow condition `NoOverflow_*` by `NoOverflowFma_*`, which is about the fused function's
own intermediate results. Tighter bounds for the fused versions are not proved.

Advice on speed (expected, not measured): where the build cannot assume a fused multiply-add
instruction (x86-64 without the `fma` target feature, which is Rust's default for x86-64), each
`mul_add` is expected to be a call to the C library's `fma`. Some C libraries (glibc on x86-64,
for example) use the hardware instruction at run time when the processor has it, so the cost may
be only the call; on a processor without the instruction, or with a C library that computes it in
software, it can be many times slower than a multiply and an add. Use the unfused functions there,
or build with `-C target-feature=+fma` for processors that have the instruction.

## What is proved, in brief

The theorems are about the Lean translation of the Rust code, under the assumptions in the next
section. "Never fails" means the translated function always returns normally: no panic, no
out-of-bounds index, no arithmetic overflow on indices, and it terminates. The exact statement and
every condition of each theorem are in [proofs/README.md](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/proofs/README.md); this summary is no
substitute for them.

| Module | What is proved, under the conditions in proofs/README.md |
|---|---|
| every module (†) | Never fails; computes exactly the stated operations, in the code's order |
| `gain` | Ramp: each gain within a stated bound of the ideal line; finite gains never move the wrong way |
| `one_pole` | Error bound for every output of a block of any length, against exact arithmetic |
| `smoother` | The same; and, for a steady input, how far from it the state can be after `n` steps |
| `biquad` | From a zero state (or one matching a given history), equals the textbook recurrence in exact arithmetic; whole-block error bound (*) |
| `svf` | Design functions compute exactly the stated operations (libm modelled, see below); whole-block error bound (*) |
| `delay` | Exact outputs for any buffer, position and delay; splitting a block changes nothing; reading then writing one sample matches a one-sample block when the delay used is at least 1 (a delay of at least 1 and a buffer of at least 2 samples) |
| fused `one_pole`, `smoother`, `biquad`, `svf` (`std` feature) | Never fail; compute exactly the stated fused operations; the same whole-block error bounds (and, for the smoother, settling bounds) as the unfused version, with the same constants ((*) for the biquad and the SVF) |

(†) Every public DSP function. For the SVF design functions, "never fails" assumes libm's
functions never panic.

(*) Given a contraction for the stored coefficients: a way of measuring the filter's two state
values under which each step, without input, multiplies the measure by at most a fixed factor
below 1, with constants linking the measure to the two values (`biquad.Contraction` and
`svf.Contraction`, both the structure `two_state.Contraction` in
`proofs/ConjureDSPLib/TwoState.lean`), and further conditions.
One is supplied for biquads whose poles are inside the unit circle (complex, distinct real or
repeated real), and for the SVF with complex poles.

Things to know before relying on the error bounds:

- They compare the code with the same filter run in exact arithmetic on the stored floats:
  coefficients, starting state and inputs as already rounded. Rounding a decimal coefficient to a
  float is not covered.
- For the smoother, the coefficient compared against is `1 - a` as computed in floating point. It
  is exactly `1 - a` when `a` is between 1/2 and 2 (`smoother.coeff_f64_exact`); outside that
  range, the effect of its rounding is not proved. `process_coeff` uses the coefficient as given,
  and its bounds are against that coefficient (`smoother.process_coeff_f64_block_error`).
- They are worst cases, and can be too large to be useful, or prove nothing. Take the stored `f32`
  coefficients of an RBJ-cookbook Butterworth low-pass at 48 kHz, finite inputs at most 1 in size,
  a start from zero, and `biquad.complexPolesContraction`. At 1 kHz each output is within 0.0542
  (−25.3 dB) of exact arithmetic (`biquad.lowPass1kHz_bounds_f32` with
  `biquad.process_f32_block_error_of_inputs`). At 100 Hz the bound is at
  least 17, larger than the inputs themselves, so of no practical use
  (`biquad.lowPass100Hz_bounds_f32`). At 82 Hz the bound's condition is false, so it says nothing
  (`biquad.lowPass82Hz_smallness_fails_f32`). That these stored values are the cookbook's
  coefficients is worked out outside Lean, not proved.
- Worked examples with numbers, for the one-pole, the smoother, the biquad and the SVF, are in
  [proofs/README.md](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/proofs/README.md).

<details>
<summary>Key theorems and definitions</summary>

In the namespace `conjure_dsp_lib`; each `_f64` theorem here has an `_f32` counterpart.

- `gain`: `gain.apply_f64_eq`, `gain.ramp_f64_spec`, `gain.rampGain_f64_error`,
  `gain.rampGain_f64_mono`.
- `one_pole`: `one_pole.process_f64_spec`, `one_pole.process_f64_block_error`,
  `one_pole.process_f64_block_error_of_inputs`.
- `smoother`: `smoother.process_f64_spec`, `smoother.process_f64_block_error`,
  `smoother.process_f64_settle_of_inputs`; with the coefficient given directly,
  `smoother.process_coeff_f64_spec`, `smoother.process_coeff_f64_block_error`,
  `smoother.process_f64_eq_process_coeff`.
- `biquad`: `biquad.process_f64_spec`, `biquad.process_f64_block_error`; in exact arithmetic,
  `biquad.filt_real_eq_df1_real_zero` (the textbook recurrence) and
  `biquad.complexPolesContraction`.
- `svf`: `svf.process_f64_spec`, `svf.CoeffsF64.low_pass_eq` (and one for each other shape),
  `svf.process_f64_block_error`; in exact arithmetic, `svf.complexPolesContraction`.
- `delay`: `delay.process_f64_ok`, `delay.process_f64_spec`, `delay.process_f64_append`;
  one sample at a time, `delay.read_f64_spec`, `delay.write_f64_spec`,
  `delay.read_write_f64_eq_process`.
- Fused functions: `real_fma_f64` and `abs_real_fma_sub_le_f64` (one fused multiply-add rounds
  once), `one_pole.process_fma_f64_spec`, `one_pole.process_fma_f64_block_error_of_inputs`,
  `smoother.process_fma_f64_spec`, `smoother.process_coeff_fma_f64_spec`,
  `smoother.process_fma_f64_settle_of_inputs`, `smoother.process_coeff_fma_f64_settle_of_inputs`,
  `biquad.process_fma_f64_spec`, `biquad.process_fma_f64_block_error_of_inputs`,
  `svf.process_fma_f64_spec`, `svf.process_fma_f64_block_error_of_inputs`.

</details>

## What is assumed, not proved

In brief; the full list is in
["What is assumed, not proved"](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/proofs/README.md#what-is-assumed-not-proved).

- **Translation.** Charon and Aeneas translate the Rust code into Lean faithfully. The Aeneas used
  is a fork: the `conjure` branch of
  [michaeljancsy/aeneas](https://github.com/michaeljancsy/aeneas), at the commit pinned in
  `proofs/PINS`. Its float model has a single NaN; no theorem here states anything about NaN bit
  patterns or NaN signs.
- **Rounding.** Rust's `f32`/`f64` operations are the same IEEE 754 round-to-nearest operations
  as Lean's `Float32`/`Float`. The processor runs in its default mode: round to nearest, subnormal
  results kept (no flush-to-zero) and subnormal inputs read as they are (no denormals-are-zero), in
  IEEE single and double precision (not x87 extended precision). Hosts and plug-ins often turn on
  flush-to-zero; the error bounds are not proved for that mode.
- **Fused multiply-add only where the code asks for it.** In the unfused functions every multiply
  and add is rounded separately: Rust does not fuse them unless the code asks for `mul_add`, and
  those functions do not. The fused functions (`*_fma_*`, the `std` feature) ask for it, and the
  proofs assume that Rust's `mul_add` rounds `a·b + c` once, as IEEE 754's fused multiply-add,
  like Lean's `Float.fma` / `Float32.fma`: done by the processor's instruction or by the
  platform's software routine.
- **libm.** The one dependency, `libm` 0.2.16, is not translated. Its `tan`, `pow` and `sqrt`
  (and `tanf`, `powf`, `sqrtf`) are modelled as unknown functions that always return, and return
  the same float for the same arguments. The proofs hold whatever values these functions return,
  so they don't depend on `libm`'s accuracy; that accuracy is not proved here either. That libm
  gives the same results on every platform is not proved.
- **Filter design.** The frequency responses of the SVF design functions' coefficients are not
  proved, nor that those coefficients are stable or meet the error bounds' conditions at every
  cutoff (the low-pass examples in `proofs/README.md` are proved for stated coefficient values;
  that the design functions store those values is worked out outside Lean, not proved).
- **Trusted base.** Lean's kernel, Mathlib, FloatLib (which relates Lean's floats to real numbers)
  and Aeneas's Lean library. Every theorem depends only on the axioms `propext`,
  `Classical.choice` and `Quot.sound`, with no `sorry`. Every declaration in the `ConjureDSPLib`
  modules is replayed through Lean's kernel by `leanchecker`; Mathlib, FloatLib and Aeneas's
  library are trusted as compiled, not replayed.

## Scope

- Not a plug-in framework: nothing about plug-in formats, hosts, threads, parameters, saved state
  or user interfaces.
- Not a complete DSP library: no FFT, no resampling, no interpolating delay, no SIMD.
- No performance claims.
- Not checked for every input: nothing is validated at run time. For example, the SVF design
  functions are meant for `0 < cutoff_hz < sample_rate_hz / 2`, `q > 0` and a finite `gain_db`,
  and outside those ranges their results may be infinite or NaN.
- The proofs cover the translated code under the assumptions above. They say nothing about the
  machine code a compiler produces.

## Checking the proofs yourself

`scripts/check.sh` runs everything: a check of the Rust version, `cargo fmt --check`,
`cargo clippy`, `cargo test`, `cargo doc`, then `scripts/prove.sh`. That script runs Charon and
Aeneas, checks that the generated Lean matches the committed copy, runs `lake build` in `proofs/`,
an axiom check (only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`; no public theorem
statement outside the generated code names Lean's NaN constants or Aeneas's NaN-bits helpers
directly) and a `leanchecker` kernel replay. It needs `bash`, `git` (run it from a git checkout)
and `python3`.

GitHub Actions also runs the whole of `scripts/check.sh` weekly and on demand (`proofs.yml`), and
the Rust checks on every pull request (`rust.yml`).

`scripts/check.sh` and `scripts/prove.sh` refuse to run with tool versions other than those in
`proofs/PINS` (Rust is checked by `check.sh`, the rest by `prove.sh`):

| Tool | Version |
|---|---|
| Aeneas | `conjure` branch of [michaeljancsy/aeneas](https://github.com/michaeljancsy/aeneas), commit `5433b097…` |
| Charon | commit `de8736f7…` (the commit Aeneas's `charon-pin` names) |
| Lean | v4.35.0 (`proofs/lean-toolchain`) |
| Mathlib | v4.35.0 |
| FloatLib | [lean-dojo/FloatLib](https://github.com/lean-dojo/FloatLib), commit `acba2057…` |
| Rust | 1.93.1 |

`proofs/PINS` has the full commit hashes. To set up:

1. Install Rust with `rustup` (it picks up `rust-toolchain.toml`) and Lean with `elan` (it picks up
   `proofs/lean-toolchain`).
2. Clone the Aeneas fork, check out the commit in `proofs/PINS`, and build Aeneas (which needs
   OCaml and opam) with Charon in its `charon/` folder at the pinned Charon commit, as the Aeneas
   repository's own instructions describe. The script checks that the Aeneas checkout has no
   changes to tracked files, that the Aeneas binary reports the pinned commit and was not built
   from a modified tree, and that Charon reports the pinned commit named in Aeneas's `charon-pin`.
3. Set `AENEAS_DIR` to that checkout; it is required, because the script's built-in default will
   not exist on your machine. `CHARON_BIN` defaults to `$AENEAS_DIR/charon/bin/charon`.
4. Optionally set `LAKE_PACKAGES` to a folder of already-built Lake packages (Mathlib, FloatLib
   and their dependencies) at the revisions in `proofs/lake-manifest.json`, so nothing is
   downloaded or rebuilt; the script refuses a folder at other revisions. Without it, Lake fetches
   and builds them.
5. Run:

```sh
AENEAS_DIR=/path/to/aeneas scripts/check.sh
```

Run `scripts/prove.sh` once before running `lake build` by hand in `proofs/`: it makes the link to
Aeneas that the Lean project needs.

The Lean translation of the crate, `proofs/ConjureDSPLib/Code/`, is generated and committed, and
the script fails if it no longer matches. Its comments include source positions, so any edit to
the Rust that moves source lines or columns, even in a comment, means regenerating it
(`ALLOW_REGENERATED=1 scripts/prove.sh`) and committing it. One file there,
`Code/FunsExternal.lean`, is written by hand: the models of the `libm` functions.

## Licence

Licensed under the [Apache License, Version 2.0](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/LICENSE-APACHE). The
[NOTICE](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/NOTICE) file holds the attribution notices that section 4(d) of
the licence says must be passed on with works you distribute, in one of the places that section
lists.

## Status

Version 0.1.0, the first public release. The API may change.
