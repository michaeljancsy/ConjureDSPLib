First public release of ConjureDSPLib: a small `no_std` Rust library of audio DSP building blocks
(gain and gain ramp, one-pole filter, smoother, biquad, state-variable filter with eight design
functions, delay line), each in `f32` and `f64`, with machine-checked Lean 4 proofs about the code
as translated by Charon and Aeneas. The API may change in 0.x releases.

```toml
[dependencies]
conjure-dsp-lib = { git = "https://github.com/michaeljancsy/ConjureDSPLib", tag = "v0.1.0" }
```

**Proved** (exact statements and conditions in
[proofs/README.md](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/proofs/README.md)):

- Every public DSP function never fails and computes exactly the stated floating-point operations
  in the code's order (for the SVF design functions, assuming libm's functions never panic).
- Gain ramp: each gain within a stated bound of the exact straight line
  (`gain.rampGain_f64_error`); finite gains never move the wrong way (`gain.rampGain_f64_mono`).
- One-pole and smoother: a whole-block error bound against exact arithmetic, under stability,
  finiteness, input-size and no-overflow conditions (`one_pole.process_f64_block_error`,
  `smoother.process_f64_block_error`).
- Biquad and SVF: a whole-block error bound given a contraction for the stored coefficients, under
  finiteness, input-size and no-overflow conditions (`biquad.process_f64_block_error`,
  `svf.process_f64_block_error`). For the stored `f32` coefficients of a 20 Hz SVF low-pass with
  Q = 0.7071 at 48 kHz (that `CoeffsF32::low_pass` stores them is worked out outside Lean, not
  proved), with inputs at most 1 and a start from zero, the SVF's bound is proved to be at most 0.0126
  (`svf.lowPass20Hz_bounds_f32`). For the stored `f32` coefficients of an RBJ-cookbook
  Butterworth biquad low-pass at 48 kHz (that they are the cookbook's is worked out outside Lean,
  not proved), the biquad bound's condition with `biquad.complexPolesContraction` is proved to fail
  at 82 Hz (`biquad.lowPass82Hz_smallness_fails_f32`); that it fails at every cutoff below about
  82.4 Hz where the stored poles are complex is worked out outside Lean, not proved.
- Delay: exact outputs for any buffer, position and delay (`delay.process_f64_spec`,
  `delay.process_f64_empty_buffer`).

Each `_f64` theorem named here has an `_f32` counterpart.

**Assumed, not proved** (full list in
[What is assumed, not proved](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/proofs/README.md#what-is-assumed-not-proved)):
faithful translation by Charon and a fork of Aeneas (`conjure` branch, pinned commit); IEEE
round-to-nearest in the processor's default mode (no flush-to-zero, no x87), with flush-to-zero not
covered; no fused multiply-add; libm's `tan`, `pow` and `sqrt` modelled as unknown functions that
always return, their accuracy not assumed or proved; the design functions' frequency responses; the
trusted base (Lean's kernel, Mathlib, FloatLib, Aeneas's Lean library). Nothing is proved about
compiled machine code.

**Observed, not proved:** the error bounds are worst cases, and typical errors are expected to be
much smaller; RBJ-cookbook low-pass and high-pass biquads with `f32` coefficients can put a pole on
or outside the unit circle at some cutoffs below about 6 Hz and within 6 Hz of half the sample rate
(worked out outside Lean at 44.1, 48 and 96 kHz and Q = 0.5, 0.7071, 2 and 10); one such case is
proved for specific stored values (`biquad.lowPass1Hz_pole_one_f32`; that they are a 1 Hz
Butterworth low-pass's at 48 kHz is worked out outside Lean, not proved).

**Checking the proofs:** pinned versions are in
[proofs/PINS](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/proofs/PINS). Build the
Aeneas fork at the pinned commit, then run `AENEAS_DIR=/path/to/aeneas scripts/check.sh`; see
[the README](https://github.com/michaeljancsy/ConjureDSPLib/blob/v0.1.0/README.md#checking-the-proofs-yourself).
