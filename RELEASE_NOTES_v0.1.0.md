# ConjureDSPLib v0.1.0

First public release: a small `no_std` Rust library of audio DSP building blocks, with Lean 4
proofs about the Rust code as translated by Charon and Aeneas. This is a 0.x release; the API may
change.

## Modules

Each in `f32` and `f64`:

- `gain`: fixed gain (`apply`) and a straight-line gain ramp across a block (`ramp`).
- `one_pole`: one-pole feedback filter, `y[n] = x[n] + a·y[n-1]`.
- `smoother`: one-pole smoother, `y[n] = y[n-1] + (1 - a)·(x[n] - y[n-1])`.
- `biquad`: second-order filter in transposed direct form II.
- `svf`: trapezoidal state-variable filter, with design functions for low-pass, high-pass,
  band-pass, notch, all-pass, bell, low shelf and high shelf.
- `delay`: whole-sample delay line in a caller-owned buffer.

The only dependency is `libm` 0.2.16, pinned exactly. Minimum Rust version: 1.93.

## What is proved

About the Lean translation of the code, under the assumptions below. Exact statements and
conditions are in `proofs/README.md`; theorem names are in the namespace `conjure_dsp_lib`.

- Every function never fails (no panic, no out-of-bounds index, no index overflow, and it
  terminates) and computes exactly a stated sequence of floating-point operations in the code's
  order (for example `one_pole.process_f64_spec`, `biquad.process_f64_spec`,
  `svf.CoeffsF64.low_pass_eq`; for the SVF design functions, given that libm's functions never
  panic).
- Gain ramp: under stated conditions on the ends and the block length, each gain is within a
  stated bound of the straight line from `start` toward `end` (`gain.rampGain_f64_error`), and
  finite gains never move the wrong way (`gain.rampGain_f64_mono`).
- One-pole and smoother: a floating-point error bound for every output and the final state of a
  block of any length, against the same filter in exact arithmetic on the stored floats, under
  stability, input-size and no-overflow conditions (`one_pole.process_f64_block_error`,
  `smoother.process_f64_block_error`, and `_of_inputs` forms with conditions on the inputs only).
  For the smoother on a steady input, a bound on how far from it the state can be after `n`
  samples (`smoother.process_f64_settle_of_inputs`).
- Biquad: in exact arithmetic, from a zero state, the transposed form gives exactly the textbook
  recurrence (`biquad.filt_real_eq_df1_real_zero`). A whole-block error bound given a
  `Contraction` for the stored coefficients and a smallness condition
  (`biquad.process_f64_block_error`); a `Contraction` is supplied for poles inside the unit circle
  (complex, distinct real or repeated real), and none exists when 1 is a pole.
- SVF: a whole-block error bound given an `svf.Contraction` and a state-bound condition
  (`svf.process_f64_block_error`); one is supplied for complex poles
  (`svf.complexPolesContraction`).
- Delay: exact outputs for any buffer, position and delay (`delay.process_f64_spec`), never fails
  for any arguments (`delay.process_f64_ok`), and two calls on consecutive blocks give the same
  result as one call on both (`delay.process_f64_append`).

Each `_f64` theorem named here has an `_f32` counterpart. Worked numerical examples are in
`proofs/README.md`.

## Known limitations

Assumed, not proved (full list in `proofs/README.md`, "What is assumed, not proved"):

- Charon and Aeneas translate the Rust faithfully. The Aeneas used is a fork (`conjure` branch of
  `michaeljancsy/aeneas`, pinned commit), whose float model has a single NaN.
- IEEE 754 round-to-nearest arithmetic in the processor's default mode: no flush-to-zero, no
  denormals-are-zero, no x87 extended precision. The error bounds are not proved with
  flush-to-zero on.
- No fused multiply-add.
- libm's `tan`, `pow` and `sqrt` (and `f32` versions) are modelled as unknown functions that always
  return; their accuracy is not assumed or proved.
- The SVF design functions' frequency responses, and that their coefficients are stable at every
  cutoff, are not proved.
- Trusted: Lean's kernel, Mathlib, FloatLib and Aeneas's Lean library. Nothing is proved about the
  compiled machine code.

Observed, not proved (`proofs/README.md`, "Observations (not proofs)"):

- The error bounds are worst cases; typical rounding errors are expected to be much smaller.
- For RBJ-cookbook low-pass and high-pass biquads, `f32` coefficients can put a pole on or outside
  the unit circle at some cutoffs below about 6 Hz and within 6 Hz of half the sample rate
  (worked out outside Lean, not proved). One case is proved for specific stored values: the `f32`
  coefficients in `lowPass1Hz_f32` have a pole at exactly 1 (`biquad.lowPass1Hz_pole_one_f32`).
- At low cutoffs in `f32`, the SVF's error bound applies where the biquad's, with
  `biquad.complexPolesContraction`, does not. The SVF's bound at 20 Hz is proved
  (`svf.lowPass20Hz_bounds_f32`); that the biquad's condition fails below about 82.4 Hz is worked
  out outside Lean, not proved (it is proved to fail at 82 Hz). That the SVF's actual errors are
  smaller there is expected, not proved.

Also: no FFT, no SIMD, no performance claims; the crate is not on crates.io.

## Checking the proofs

Pinned tools are in `proofs/PINS`: the Aeneas fork's commit and the matching Charon commit,
Lean v4.35.0, Mathlib v4.35.0, FloatLib and Rust 1.93.1. Check out and build the Aeneas fork at the
pinned commit (with Charon in its `charon/` folder), then run:

```sh
AENEAS_DIR=/path/to/aeneas scripts/check.sh
```

`LAKE_PACKAGES` can point at already-built Mathlib and FloatLib packages. The README's "Checking
the proofs yourself" section has the details.
