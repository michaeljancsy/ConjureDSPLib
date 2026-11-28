# Flush-to-zero and denormals-are-zero: a design note

The proofs assume the processor's default floating-point mode: subnormal results are kept and
subnormal inputs are read as they are (see "What is assumed, not proved" in
[`proofs/README.md`](../README.md#what-is-assumed-not-proved)). Audio hosts and plug-ins often
turn on flush-to-zero (FTZ) and denormals-are-zero (DAZ). This note says what changes in that
mode, which theorems would still describe what the processor does, and what proving error bounds
for that mode would take. Nothing in this note is proved; every conclusion in it is worked out
outside Lean, not proved.

## What changes

A subnormal number is a nonzero float smaller in size than the smallest normal number `N`:
`N = 2⁻¹²⁶` (about 1.2 × 10⁻³⁸) in f32 and `2⁻¹⁰²²` (about 2.2 × 10⁻³⁰⁸) in f64.

- **FTZ:** an operation whose result would be subnormal returns zero, with the result's sign.
- **DAZ:** an operation reads a subnormal operand as zero, with its sign.
- On x86-64 (SSE and AVX) these are two separate bits of the `MXCSR` register. On 64-bit Arm,
  Apple silicon included, one bit (`FPCR.FZ`) does both. Processors differ in whether "would be
  subnormal" is decided before or after rounding; that matters only for results within one
  rounding of `N`.
- Loads, stores and moves copy floats bit for bit in either mode; only arithmetic changes.
- Rust defines its float operations only in the default mode, and the compiler may evaluate an
  operation with constant operands at build time, in the default mode. So with FTZ on, whether a
  given operation is flushed can depend on inlining and constant folding, which the Rust source
  does not fix.

For one operation with exact result `e`, the proofs use FloatLib's bound in the default mode: the
rounded result is within `u·|e| + η` of `e`, with `u = 2⁻²⁴`, `η = 2⁻¹⁵⁰` in f32 and
`u = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵` in f64. Under FTZ the bound becomes `u·|e| + N`, whichever way
tininess is decided: a flushed result is off by less than `N`. The absolute term is `2²⁴` times
larger in f32 and `2⁵³` times larger in f64.

Under FTZ every computed result is normal or zero, so a subnormal operand can only be a value the
caller supplies: a coefficient, the starting state or an input sample. When none of those is
subnormal, DAZ changes nothing. When an input sample is subnormal, DAZ is the same as replacing
it by zero before filtering, a change of less than `N` in that sample.

## Which theorems would still describe the processor

Every theorem is a statement about the Lean model, and stays true as such. The question is
whether it still describes what the processor computes, which the assumption in
`proofs/README.md` ties to the default mode. Worked out outside Lean, not proved:

**Unaffected by the mode.**

- The theorems in exact arithmetic: `Exact.lean`, `Textbook.lean`, `Contraction.lean`,
  `TwoState.lean`, `gain.ramp_line_*`, `svf.svfStep_real_linear` and the others on real numbers
  only.
- "Never fails", for every function: no loop or `if` in the crate tests a float value (each tests
  an integer; a property of the code), so FTZ and DAZ cannot change which path is taken or
  whether an index is in range. For the SVF design functions this still assumes that libm never
  panics, now in that mode.
- Every delay theorem: the delay line only copies samples, and copies are bit for bit.
- `gain.real_castNat_f64` and the other index-conversion facts: whole numbers are never
  subnormal.
- `smoother.coeff_f64_exact` and `coeff_f32_exact`: for a stored `a` between 1/2 and 2, `1 - a`
  is zero or at least `2⁻⁵³` (f64) or `2⁻²⁴` (f32) in size, so never subnormal, and still exact.
- `gain.rampGain_f64_not_finite` and `_f32`: infinities and NaN are not affected.
- `gain.rampGain_f64_mono` and `_f32`: flushing to zero is monotonic, so finite gains still never
  move the wrong way.

**Still true for most blocks, but not for all.**

- The `_eq` and `_spec` theorems (which operations, in which order): the operations and their
  order are the same, and each result is the model's whenever the exact result does not round to
  a subnormal and no operand is subnormal. A block in which no operation meets a subnormal gives
  bit-identical outputs in both modes. `gain.apply_f64_eq` fails exactly when the product would
  be subnormal or an operand is.
- `gain.rampGain_f64_zero` (the first gain is `start`, bit for bit) and
  `gain.rampGain_f64_next_block`: they fail when `start` (or, for the following block, `end`) is
  subnormal, since `start + step·0` is then flushed to zero (FTZ) or `start` is read as zero
  (DAZ); otherwise they still hold.

**Not true as stated.**

- Every one-step error bound (`one_pole.step_f64_error`, `smoother.step_f64_error`,
  `biquad.tdf2_f64_localErr`, `svf.svfStep_f64_localErr`, the fused ones, and the gain ramp's
  accuracy and step bounds), and every whole-block and settling bound for general `M` and
  starting state: their `η` terms are too small for FTZ. For example, `one_pole::process_f32`
  with `a = 0.5`, a starting state of `2⁻¹²⁶` and one input sample `0.0` gives `2⁻¹²⁷` in the
  default mode and `0` under FTZ. The error under FTZ is `2⁻¹²⁷` (about 5.9 × 10⁻³⁹), while the
  proved bound `E`, with `M = 0` and that starting state, is about 4.2 × 10⁻⁴⁵, some 1.4 million
  times smaller.
- The worked examples (inputs at most 1 in size, a start from zero): their bounds are of the
  order of `u` or more, against `N` about 10⁻³⁸ or smaller. If each operation is within
  `u·|e| + N`, the same arguments with `η` replaced by `N` give bounds larger by a multiple of
  `N - η`, with the same factors that multiply `η` now, and for these examples that would change
  none of the digits shown. So every value in the tables is expected to hold under FTZ too (with
  no subnormal coefficient, starting state or input), but this is not proved. Under DAZ with
  subnormal inputs, add the exact filter's response to a change of less than `N` in each input:
  for the one-pole at most `N/(1 - |A|)`, from `one_pole.filt_real_abs_le_outBound`.

## What a proof under FTZ would take

Three layers change. The real-number arguments in the `Block.lean` files would not.

1. **The float model (Aeneas).** Aeneas translates each Rust float operation to Lean's own IEEE
   operation (`Float.add`, `Float32.mul`, `Float.fma` and so on), so the generated code cannot
   say "flushed". Two ways round it:
   - Without changing Aeneas: write each step once over an abstract set of operations (`+`, `-`,
     `*`, `/`, `fma`), prove that the generated step is that step at Lean's operations (a small
     addition to the existing `_eq` theorems), and define the step under FTZ as the same step at
     flushing operations, `x ⊕ y = flush(daz(x) + daz(y))`. The new assumption: with FTZ (and
     DAZ) on, the processor computes the generated operations with each replaced by its flushing
     version. This keeps the generated code and the Aeneas pin unchanged.
   - Or add an option to the Aeneas fork that translates float operations to flushing ones. This
     is more work, and changes a trusted tool.
2. **Rounding with a flush step (FloatLib).** Define `flush` and `daz` on Lean's floats (a
   subnormal becomes a zero of the same sign) and on real numbers (FloatLib's `roundAt`, then
   zero if the result is smaller than `N` in size, with both ways of deciding tininess), and
   prove for each operation in both precisions: its real value is the flushed rounding of the
   exact result, it is within `u·|e| + N` of it, flushing never creates an infinity, a flushed
   result is never subnormal, and `daz` leaves every other value unchanged. These are the
   counterparts of the per-operation facts in `FloatFacts.lean` and `FmaFacts.lean`.
3. **An extra absolute error term η per operation.** The real-number arguments are already
   written for any `u` and `η` (`one_pole.stepErr A u η`, `one_pole.errBound`,
   `smoother.errBound`, the biquad's `α` and `β`, the SVF's per-operation terms), so the FTZ
   bounds are the same formulas with `η` replaced by `N`. What has to be redone is the layer
   that feeds them: each filter's one-step and no-overflow theorems, from the new per-operation
   facts, then the whole-block theorems, for both precisions and the fused functions, and the
   gain ramp's bounds. Facts that use gradual underflow need checking one by one; of those found
   here, the smoother's exact coefficient still holds, and the ramp's exact first gain needs
   `start` not subnormal. The worked examples would be re-checked with `N` in place of `η`. The
   simplest hypothesis is that no coefficient, starting state or input is subnormal (then DAZ
   changes nothing); a version allowing subnormal inputs adds the input-change term above.

**Estimate** (not measured). The fused multiply-add proofs are the closest earlier piece of work:
a new per-operation model fed into the same real-number arguments, about 5,000 lines for four
filters in two precisions. FTZ is about the same size, plus layer 1, which the fused functions
did not need, and plus the flush facts, which FloatLib does not provide. Roughly:

| Part | Hours |
|---|---|
| Layer 2: `flush`, `daz` and the per-operation facts, both precisions, `fma` included | 4–8 |
| Layer 1: steps over abstract operations, equal to the generated code | 3–5 |
| Layer 3: one-step, no-overflow and whole-block theorems for the one-pole, smoother, biquad, SVF (unfused and fused) and the gain ramp | 6–10 |
| Worked examples with `N` in place of `η`, and documentation | 2–4 |
| Total | 15–27 |

Layer 3 splits by filter, so with the filters done in parallel the total time is about 10–15
hours. Each check of the proofs on GitHub takes about 15 minutes, which limits how fast mistakes
are found. Allowing subnormal inputs under DAZ adds about 4–6 hours. The main risk is layer 2:
how much of Lean's float model and FloatLib's rounding can be reused for the flush step.
