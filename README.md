# ConjureDSPLib

A small `no_std` Rust library of audio DSP building blocks: gain, two one-pole filters, a biquad, a
state-variable filter and a delay line. The Rust code is translated to Lean 4 by Charon and Aeneas,
and Lean proofs about that translation state exactly which floating-point operations each function
performs, that it never fails, and, for the filters and the gain ramp, how far its results can be
from exact arithmetic, under stated conditions and assumptions.

Per-sample code does no memory allocation, takes no locks and makes no system calls. Allocation
and system calls are ruled out by the build together with one property of the code: the crate is
`no_std` and has no `extern crate alloc` or `extern crate std` (the compiler does not forbid adding
them), and it forbids `unsafe` code; `libm` is relied on to do the same. That it takes no locks is
a property of the code (it uses no atomics or other synchronization), not enforced by the
compiler. A panic would run the program's panic handler, which can allocate, lock and make system
calls; that the functions never panic is proved of the translated code. None of this is otherwise
proved in Lean.

## What's in it

Every module has `f32` and `f64` versions (functions end in `_f32` / `_f64`, types in `F32` /
`F64`).

- `gain`: multiply by a fixed gain (`apply`), or by a gain that moves in a straight line across a
  block (`ramp`).
- `one_pole`: one-pole feedback filter, `y[n] = x[n] + a·y[n-1]`.
- `smoother`: one-pole smoother, `y[n] = y[n-1] + (1 - a)·(x[n] - y[n-1])`, for gliding toward a
  target.
- `biquad`: second-order filter in transposed direct form II, with coefficients you supply.
- `svf`: trapezoidal state-variable filter, with design functions for eight shapes (low-pass,
  high-pass, band-pass, notch, all-pass, bell, low shelf, high shelf), whose formulas follow
  A. Simper (Cytomic).
- `delay`: delay line of a whole number of samples (no interpolation), in a buffer the caller owns.

## What is proved, in brief

The theorems are about the Lean translation of the Rust code, under the assumptions in the next
section. "Never fails" means the translated function always returns normally: no panic, no
out-of-bounds index, no arithmetic overflow on indices, and it terminates. The exact statement and
every condition of each theorem are in [proofs/README.md](proofs/README.md); this summary is no
substitute for them.

| Module | What is proved, under the conditions in proofs/README.md |
|---|---|
| every module | Never fails; computes exactly the stated operations, in the code's order |
| `gain` | Ramp: each gain within a stated bound of the ideal line; never moves the wrong way |
| `one_pole` | Error bound for every output of a block of any length, against exact arithmetic |
| `smoother` | The same; and, for a steady input, how far from it the state can be after `n` steps |
| `biquad` | Equals the textbook recurrence in exact arithmetic; whole-block error bound (*) |
| `svf` | Design functions' exact operations (libm modelled); whole-block error bound (*) |
| `delay` | Exact outputs for any buffer, position and delay; splitting a block changes nothing |

(*) Given a `Contraction` for the stored coefficients and further conditions. One is supplied for
biquads whose poles are inside the unit circle (complex, distinct real or repeated real), and for
the SVF with complex poles. For the SVF design functions, "never fails" assumes libm's functions
never panic.

Key theorems (in the namespace `conjure_dsp_lib`; each `_f64` theorem here has an `_f32`
counterpart):

- `gain`: `gain.apply_f64_eq`, `gain.ramp_f64_spec`, `gain.rampGain_f64_error`,
  `gain.rampGain_f64_mono`.
- `one_pole`: `one_pole.process_f64_spec`, `one_pole.process_f64_block_error`,
  `one_pole.process_f64_block_error_of_inputs`.
- `smoother`: `smoother.process_f64_spec`, `smoother.process_f64_block_error`,
  `smoother.process_f64_settle_of_inputs`.
- `biquad`: `biquad.process_f64_spec`, `biquad.process_f64_block_error`; in exact arithmetic,
  `biquad.filt_real_eq_df1_real_zero` (the textbook recurrence) and
  `biquad.complexPolesContraction`.
- `svf`: `svf.process_f64_spec`, `svf.CoeffsF64.low_pass_eq` (and one for each other shape),
  `svf.process_f64_block_error`; in exact arithmetic, `svf.complexPolesContraction`.
- `delay`: `delay.process_f64_ok`, `delay.process_f64_spec`, `delay.process_f64_append`.

Things to know before relying on the error bounds:

- They compare the code with the same filter run in exact arithmetic on the stored floats:
  coefficients, starting state and inputs as already rounded. Rounding a decimal coefficient to a
  float is not covered.
- They are worst cases, and can be too large to be useful, or prove nothing. For example, for the
  stored `f32` coefficients of an RBJ-cookbook Butterworth low-pass at 48 kHz (that they are those
  coefficients is worked out outside Lean, not proved), the biquad's condition with
  `biquad.complexPolesContraction` is false at 82 Hz (`biquad.lowPass82Hz_smallness_fails_f32`),
  so the bound says nothing there, and at 100 Hz the bound is at least 17
  (`biquad.lowPass100Hz_bounds_f32`).
- Worked examples with numbers, for the one-pole, the smoother, the biquad and the SVF, are in
  [proofs/README.md](proofs/README.md).

## What is assumed, not proved

In brief; the full list is in
["What is assumed, not proved"](proofs/README.md#what-is-assumed-not-proved).

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
- **No fused multiply-add.** Every multiply and add is rounded separately. Rust does not fuse them
  unless the code asks for `mul_add`, and this code does not.
- **libm.** The one dependency, `libm` 0.2.16, is not translated. Its `tan`, `pow` and `sqrt`
  (and `tanf`, `powf`, `sqrtf`) are modelled as unknown functions that always return, and return
  the same float for the same arguments. Their accuracy is not assumed or proved. That libm gives
  the same results on every platform is not proved.
- **Filter design.** The frequency responses of the SVF design functions' coefficients are not
  proved, nor that those coefficients are stable or meet the error bounds' conditions at every
  cutoff (only the low-pass examples in `proofs/README.md` are checked).
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
- This is a first release (0.x). The API may change.

## How to use it

The crate is not published on crates.io (`publish = false` in `Cargo.toml`). Once v0.1.0 is
released, add it as a git dependency:

```toml
[dependencies]
conjure-dsp-lib = { git = "https://github.com/michaeljancsy/ConjureDSPLib", tag = "v0.1.0" }
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

The documentation of each module (`cargo doc --open`) gives exact behaviour, including edge cases
such as empty blocks, an empty delay buffer and changing the delay between calls.

## Checking the proofs yourself

`scripts/check.sh` runs everything: a check of the Rust version, `cargo fmt --check`,
`cargo clippy`, `cargo test`, `cargo doc`, then `scripts/prove.sh`. That script runs Charon and
Aeneas, checks that the generated Lean matches the committed copy, runs `lake build` in `proofs/`,
an axiom check (only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`; no public theorem
statement that names Lean's NaN constants or Aeneas's NaN-bits helpers) and a `leanchecker`
kernel replay. It needs `bash`, `git` (run it from a git checkout) and `python3`.

`scripts/prove.sh` refuses to run with tool versions other than those in `proofs/PINS`:

| Tool | Version |
|---|---|
| Aeneas | `conjure` branch of https://github.com/michaeljancsy/aeneas, commit `5433b097…` |
| Charon | commit `de8736f7…` (the commit Aeneas's `charon-pin` names) |
| Lean | v4.35.0 (`proofs/lean-toolchain`) |
| Mathlib | v4.35.0 |
| FloatLib | https://github.com/lean-dojo/FloatLib, commit `acba2057…` |
| Rust | 1.93.1 |

`proofs/PINS` has the full commit hashes. To set up:

1. Install Rust with `rustup` (it picks up `rust-toolchain.toml`) and Lean with `elan` (it picks up
   `proofs/lean-toolchain`).
2. Clone the Aeneas fork, check out the commit in `proofs/PINS`, and build Aeneas with Charon in
   its `charon/` folder at the pinned Charon commit, as the Aeneas repository's own instructions
   describe. The script checks that neither checkout has local changes and that both binaries
   report the pinned commits.
3. Set `AENEAS_DIR` to that checkout. The script's default is a folder in the author's own layout,
   so set it explicitly. `CHARON_BIN` defaults to `$AENEAS_DIR/charon/bin/charon`.
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
the script fails if it no longer matches. Its comments include source line numbers, so any edit to
the Rust, even to a comment, means regenerating it (`ALLOW_REGENERATED=1 scripts/prove.sh`) and
committing it. One file there, `Code/FunsExternal.lean`, is written by hand: the models of the
`libm` functions.

## Licence

Dual-licensed under either of [MIT](LICENSE-MIT) or [Apache-2.0](LICENSE-APACHE), at your option.

## Contributing and status

Version 0.1.0, the first public release. Contribution policy: to be decided.
