module

public import ConjureDSPLib.Smoother.BridgeF32
public import ConjureDSPLib.Smoother.Block

/-!
# The smoother in f32 over a whole block

`process_f32` computes `c = 1 - a` once, rounded, and then runs `s + c * (x - s)` over the
block. Write `C` for the value of that stored `c` and `A = 1 - C`. The theorems here compare the
Rust outputs with the exact smoother `filt_real A`, whose coefficient `1 - A` is exactly `C`: the
same stored coefficient, so the coefficient's own rounding is not in `E`. How far `A` is from
the value of `a` is `coeff_f32_error` (at most `u·|1 - a| + η`), and when the value of `a` is
between 1/2 and 2 they are equal (`coeff_f32_exact`).

`process_f32_block_error`: with `|A| + errGrowth A u < 1` (stable, with a little room for
rounding) and no step overflowing, every output sample and the final state are within `E` of the
exact smoother, for a block of any length. `process_f32_block_error_of_inputs` proves the
no-overflow condition from the inputs instead. `process_f32_settle_of_inputs`: with a steady
input `x`, the final state is within `|A|^n·|S - X| + E` of `X`.

The last theorems are the f32 rows of the smoother table in `proofs/README.md`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.smoother

/-- No step overflows: running the smoother with coefficient `c` from state `s` over the inputs,
every input, every difference `x - state`, every product `c * (x - state)` and every new output
is finite. -/
def NoOverflow_f32 (c : Float32) : Float32 → List Float32 → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (x - s).isFinite = true ∧ (c * (x - s)).isFinite = true ∧
      (s + c * (x - s)).isFinite = true ∧ NoOverflow_f32 c (s + c * (x - s)) xs

/-- Without overflow, each step of `filt_f32` is within the per-step error `step_f32_error`. -/
theorem filt_f32_withinStepErr (c : Float32) (hc : c.isFinite = true) :
    ∀ (xs : List Float32) (s : Float32), s.isFinite = true → NoOverflow_f32 c s xs →
      WithinStepErr (1 - real_f32 c) unitRoundoff_f32 underflowErr_f32 (real_f32 s)
        (xs.map real_f32) (real_f32 (filt_f32 c s xs).1) ((filt_f32 c s xs).2.map real_f32) := by
  intro xs
  induction xs with
  | nil => intro s _ _; simp [filt_f32, WithinStepErr]
  | cons x xs ih =>
    intro s hs hno
    obtain ⟨hx, hd, hp, hr, hrest⟩ := hno
    simp only [filt_f32, List.map_cons, WithinStepErr]
    refine ⟨?_, ih _ hr hrest⟩
    rw [sub_sub_cancel]
    exact step_f32_error c s x hc hs hx hd hp hr

/-- **Whole-block error of the f32 smoother.** Let `C`, `S` and the inputs be the values of the
coefficient `c`, the starting state and the samples, with every input at most `M` in size, and
`A = 1 - C`. If `c` and the start are finite, no step overflows, and
`|A| + errGrowth A u < 1` (`u = 2⁻²⁴`), then every output of `filt_f32 c` and its final state
are within `E = errBound A u η M S` of the exact smoother `filt_real A`. -/
theorem filt_f32_block_error (c s : Float32) (xs : List Float32) (M : ℝ)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hno : NoOverflow_f32 c s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f32 x| ≤ M)
    (hstab : |1 - real_f32 c| + errGrowth (1 - real_f32 c) unitRoundoff_f32 < 1) :
    let A := 1 - real_f32 c
    let E := errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 s)
    List.Forall₂ (fun y e => |real_f32 y - e| ≤ E) (filt_f32 c s xs).2
        (filt_real A (real_f32 s) (xs.map real_f32)).2 ∧
      |real_f32 (filt_f32 c s xs).1 - (filt_real A (real_f32 s) (xs.map real_f32)).1| ≤ E := by
  intro A E
  have h := block_error_real A unitRoundoff_f32 underflowErr_f32 M (real_f32 s)
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab (xs.map real_f32)
    _ _ (by simpa using hM) (filt_f32_withinStepErr c hc xs s hs hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust `process_f32`.** Let `A = 1 - C`, where `C` is the value of
`1 - a` computed in binary32 (the stored coefficient), and `S` the value of the starting state.
If `1 - a` and the starting state are finite, no step overflows, every sample is at most `M` in
size and `|A| + errGrowth A u < 1`, then `process_f32` never fails, and every sample it writes and
the state it leaves are within `E = errBound A u η M S` of the exact smoother `filt_real A`, run
from `S` on the samples' values. See `process_f32_block_error_of_inputs` for a version whose
conditions are on the inputs only. -/
theorem process_f32_block_error (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (hc : (1 - a).isFinite = true) (hs : state.isFinite = true)
    (hno : NoOverflow_f32 (1 - a) state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f32 x| ≤ M)
    (hstab : |1 - real_f32 (1 - a)| + errGrowth (1 - real_f32 (1 - a)) unitRoundoff_f32 < 1) :
    let A := 1 - real_f32 (1 - a)
    let E := errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    process_f32 a state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f32 y - e| ≤ E) r.2.val
          (filt_real A (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real A (real_f32 state) (buf.val.map real_f32)).1| ≤ E ⦄ := by
  intro A E
  have hblock := filt_f32_block_error (1 - a) state buf.val M hc hs hno hM0 hM hstab
  apply WP.spec_mono (process_f32_spec a state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **No overflow, from the inputs alone.** Let `C` be the value of the stored `c`, `A = 1 - C`,
and `u`, `η` binary32's rounding constants. Suppose `c` and every input are finite, every input is
at most `M` in size, and the bounds `B` and `E` satisfy the two inequalities of `block_step`.
Start from any finite state `s` within `E` of a real state `r` with `|r| ≤ B` (for the smoother's
own start, `r` is the state's value). If, with `W = B + E` and `G = (1 + u)·(M + W) + η`,
`G + W + (1 + u)·|C|·G + η` is at most the largest finite binary32 value, then no step of the
smoother overflows. -/
theorem noOverflow_f32_of_inputs (c : Float32) (hc : c.isFinite = true) (M B E : ℝ)
    (hB : |real_f32 c| * M + |1 - real_f32 c| * B ≤ B)
    (hE : stepBound (1 - real_f32 c) unitRoundoff_f32 underflowErr_f32 M (B + E) +
        |1 - real_f32 c| * E ≤ E)
    (hcap : (1 + unitRoundoff_f32) * (M + (B + E)) + underflowErr_f32 + (B + E) +
        (1 + unitRoundoff_f32) * |real_f32 c| *
          ((1 + unitRoundoff_f32) * (M + (B + E)) + underflowErr_f32) + underflowErr_f32 ≤
      maxFinite_f32) :
    ∀ (xs : List Float32) (s : Float32) (r : ℝ), s.isFinite = true →
      (∀ x ∈ xs, x.isFinite = true ∧ |real_f32 x| ≤ M) →
      |real_f32 s - r| ≤ E → |r| ≤ B → NoOverflow_f32 c s xs := by
  have hu : 0 ≤ unitRoundoff_f32 := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ underflowErr_f32 := (Model.underflowErrorAt_pos _).le
  have hB' : |1 - (1 - real_f32 c)| * M + |1 - real_f32 c| * B ≤ B := by rwa [sub_sub_cancel]
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs hin hsr hr
    obtain ⟨hx, hxM⟩ := hin x (by simp)
    set u := unitRoundoff_f32
    set η := underflowErr_f32
    set C := real_f32 c
    set W := B + E
    have hE0 : 0 ≤ E := (abs_nonneg _).trans hsr
    have hB0 : 0 ≤ B := (abs_nonneg _).trans hr
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hxM
    have hS : |real_f32 s| ≤ W := by
      calc |real_f32 s| = |(real_f32 s - r) + r| := by ring_nf
        _ ≤ |real_f32 s - r| + |r| := abs_add_le _ _
        _ ≤ W := by linarith
    have hC := abs_nonneg C
    set G := (1 + u) * (M + W) + η
    have hG : M + W ≤ G := by
      have : 0 ≤ u * (M + W) := by positivity
      linarith
    have hCG : 0 ≤ (1 + u) * |C| * G := by positivity
    -- The difference: finite, and within `G` in size.
    have hXS : |real_f32 x - real_f32 s| ≤ M + W := (abs_sub _ _).trans (add_le_add hxM hS)
    have hd : (x - s).isFinite = true := isFinite_sub_f32 x s hx hs (by linarith)
    have hD : |real_f32 (x - s)| ≤ G := by
      have h1 := abs_real_sub_sub_le_f32 x s hx hs hd
      calc |real_f32 (x - s)|
          = |(real_f32 x - real_f32 s) + (real_f32 (x - s) - (real_f32 x - real_f32 s))| := by
            ring_nf
        _ ≤ |real_f32 x - real_f32 s| + |real_f32 (x - s) - (real_f32 x - real_f32 s)| :=
            abs_add_le _ _
        _ ≤ (M + W) + (u * (M + W) + η) := by
            have := mul_le_mul_of_nonneg_left hXS hu
            linarith
        _ = G := by ring
    -- The product: finite, and within `(1 + u)·|C|·G + η` in size.
    have hCD : |C * real_f32 (x - s)| ≤ |C| * G := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hD hC
    have hp : (c * (x - s)).isFinite = true := by
      refine isFinite_mul_f32 c (x - s) hc hd ?_
      have : |C| * G ≤ (1 + u) * |C| * G := by nlinarith
      linarith
    have hP : |real_f32 (c * (x - s))| ≤ (1 + u) * |C| * G + η := by
      have h2 := abs_real_mul_sub_le_f32 c (x - s) hc hd hp
      calc |real_f32 (c * (x - s))|
          = |C * real_f32 (x - s) + (real_f32 (c * (x - s)) - C * real_f32 (x - s))| := by
            ring_nf
        _ ≤ |C * real_f32 (x - s)| + |real_f32 (c * (x - s)) - C * real_f32 (x - s)| :=
            abs_add_le _ _
        _ ≤ |C| * G + (u * (|C| * G) + η) := by
            have := mul_le_mul_of_nonneg_left hCD hu
            linarith
        _ = (1 + u) * |C| * G + η := by ring
    -- So the sum is finite too.
    have hsum : (s + c * (x - s)).isFinite = true := by
      refine isFinite_add_f32 s (c * (x - s)) hs hp ?_
      calc |real_f32 s + real_f32 (c * (x - s))|
          ≤ |real_f32 s| + |real_f32 (c * (x - s))| := abs_add_le _ _
        _ ≤ W + ((1 + u) * |C| * G + η) := add_le_add hS hP
        _ ≤ maxFinite_f32 := by linarith
    -- The step is within its error bound, so both bounds carry on to the next step.
    have hstep : |real_f32 (s + c * (x - s)) -
        (real_f32 s + (1 - (1 - C)) * (real_f32 x - real_f32 s))| ≤
        stepErr (1 - C) u η (real_f32 s) (real_f32 x) := by
      rw [sub_sub_cancel]; exact step_f32_error c s x hc hs hx hd hp hsum
    obtain ⟨herr, hr'⟩ := block_step (1 - C) u η M B E (real_f32 x) (real_f32 s) r
      (real_f32 (s + c * (x - s))) hu hη hB' hE hxM hsr hr hstep
    exact ⟨hx, hd, hp, hsum, ih (s + c * (x - s)) _ hsum
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) herr hr'⟩

/-- **Whole-block error of `process_f32`, with conditions on the inputs only.** Let `A = 1 - C`,
where `C` is the value of `1 - a` computed in binary32, `S` the value of the starting state, and
`u`, `η` binary32's rounding constants. If `a`, the starting state and every sample are finite,
the value of `a` is at most 1 in size, every sample is at most `M` in size,
`|A| + errGrowth A u < 1`, and, with `B = outBound A M S`, `E = errBound A u η M S`, `W = B + E`
and `G = (1 + u)·(M + W) + η`, `G + W + (1 + u)·|C|·G + η` is at most the largest finite binary32
value (about 3.4 × 10³⁸), then no step overflows, `process_f32` never fails, and every sample it
writes and the state it leaves are within `E` of the exact smoother `filt_real A`. -/
theorem process_f32_block_error_of_inputs (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (ha : a.isFinite = true) (ha1 : |real_f32 a| ≤ 1) (hs : state.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f32 x| ≤ M) (hM0 : 0 ≤ M)
    (hstab : |1 - real_f32 (1 - a)| + errGrowth (1 - real_f32 (1 - a)) unitRoundoff_f32 < 1)
    (hcap :
      let A := 1 - real_f32 (1 - a)
      let W := outBound A M (real_f32 state) +
        errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
      let G := (1 + unitRoundoff_f32) * (M + W) + underflowErr_f32
      G + W + (1 + unitRoundoff_f32) * |real_f32 (1 - a)| * G + underflowErr_f32 ≤
        maxFinite_f32) :
    let A := 1 - real_f32 (1 - a)
    let E := errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    NoOverflow_f32 (1 - a) state buf.val ∧
      process_f32 a state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f32 y - e| ≤ E) r.2.val
          (filt_real A (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real A (real_f32 state) (buf.val.map real_f32)).1| ≤ E ⦄ := by
  intro A E
  have hc : (1 - a).isFinite = true := isFinite_one_sub_f32_of_abs_le_one a ha ha1
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants A unitRoundoff_f32 underflowErr_f32 M
    (real_f32 state) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab
  have hB' : |real_f32 (1 - a)| * M + |1 - real_f32 (1 - a)| * outBound A M (real_f32 state) ≤
      outBound A M (real_f32 state) := by
    have := hB; simp only [A, sub_sub_cancel] at this; exact this
  have hno := noOverflow_f32_of_inputs (1 - a) hc M _ _ hB' hE hcap buf.val state (real_f32 state)
    hs hin (by simpa using hE0) hSB
  exact ⟨hno, process_f32_block_error a state buf M hc hs hno hM0
    (fun x hx => (hin x hx).2) hstab⟩

/-- **Settling on a steady input, f32.** Let `A = 1 - C`, where `C` is the value of `1 - a`
computed in binary32, `S` the value of the starting state, `X` the value of the input `x`, and
`n` the length of the block. If every sample in the buffer is `x`, `|X| ≤ M`, and the
conditions of `process_f32_block_error_of_inputs` hold, then `process_f32` never fails, and the
state it leaves is within `|A|^n·|S - X| + E` of `X`, where `E = errBound A u η M S`. The first
term is how far the exact smoother still is from `X` after `n` samples; the second is rounding.
So the state need not land exactly on `X`, but stays within that distance of it. -/
theorem process_f32_settle_of_inputs (a state x : Float32) (buf : Slice Float32) (M : ℝ)
    (ha : a.isFinite = true) (ha1 : |real_f32 a| ≤ 1) (hs : state.isFinite = true)
    (hx : x.isFinite = true) (hbuf : ∀ y ∈ buf.val, y = x) (hXM : |real_f32 x| ≤ M)
    (hstab : |1 - real_f32 (1 - a)| + errGrowth (1 - real_f32 (1 - a)) unitRoundoff_f32 < 1)
    (hcap :
      let A := 1 - real_f32 (1 - a)
      let W := outBound A M (real_f32 state) +
        errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
      let G := (1 + unitRoundoff_f32) * (M + W) + underflowErr_f32
      G + W + (1 + unitRoundoff_f32) * |real_f32 (1 - a)| * G + underflowErr_f32 ≤
        maxFinite_f32) :
    let A := 1 - real_f32 (1 - a)
    process_f32 a state buf ⦃ fun r =>
      |real_f32 r.1 - real_f32 x| ≤ |A| ^ buf.val.length * |real_f32 state - real_f32 x| +
        errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state) ⦄ := by
  intro A
  have hin : ∀ y ∈ buf.val, y.isFinite = true ∧ |real_f32 y| ≤ M := by
    intro y hy; rw [hbuf y hy]; exact ⟨hx, hXM⟩
  obtain ⟨hno, -⟩ := process_f32_block_error_of_inputs a state buf M ha ha1 hs hin
    ((abs_nonneg _).trans hXM) hstab hcap
  have hc : (1 - a).isFinite = true := isFinite_one_sub_f32_of_abs_le_one a ha ha1
  have hrep : buf.val = List.replicate buf.val.length x := List.eq_replicate_iff.mpr ⟨rfl, hbuf⟩
  have hw := filt_f32_withinStepErr (1 - a) hc buf.val state hs hno
  rw [hrep, List.map_replicate] at hw
  have h := settle_real A unitRoundoff_f32 underflowErr_f32 M (real_f32 x) (real_f32 state)
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hXM hstab _ _ _ hw
  apply WP.spec_mono (process_f32_spec a state buf)
  rintro r ⟨-, hst⟩
  rw [hst]
  rw [← hrep] at h
  exact h

/-! ## The f32 rows of the smoother table -/

-- The dB step checks a power of 10 with up to 1400 digits; norm_num needs a higher limit for that.
set_option exponentiation.threshold 4000 in
/-- **Row `a = 0.99` of the smoother table in `proofs/README.md`, f32.** For every real `A` with
`0 ≤ A ≤ 0.990001` (`A = 1 - C`, `C` the value of the stored coefficient), inputs at most `M = 1`
in size and a starting state of value `S = 0`, in binary32: the stability condition holds,
`B = outBound A 1 0 = 1`, `E = errBound A u η 1 0 ≤ 6.2 × 10⁻⁶` and `20·log₁₀ E ≤ −104.1`.
f32 stores 0.99 as 0.9900000095 (worked out outside Lean, not proved); since that is between 1/2
and 2, `1 - a` is computed exactly (`coeff_f32_exact`), so `A` is that stored value, and the
bound 0.990001 leaves room for it. -/
theorem table_row_le_of_le_099_f32 (A : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 0.990001) :
    |A| + errGrowth A unitRoundoff_f32 < 1 ∧ outBound A 1 0 = 1 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 ≤ 6.2 * 10 ^ (-6 : ℤ) ∧
      20 * Real.logb 10 (errBound A unitRoundoff_f32 underflowErr_f32 1 0) ≤ -104.1 := by
  have hu : 0 < unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; positivity
  have hη : 0 ≤ underflowErr_f32 := by rw [underflowErr_f32_eq]; positivity
  obtain ⟨h1, h2, h3, h4⟩ := table_row_le_of_le A 0.990001 _ _ (2 ^ (-150 : ℤ)) 62 7 200 1041
    hu (by rw [unitRoundoff_f32_eq]; norm_num) hη underflowErr_f32_eq.le hA0 hA
    (by
      unfold errGrowth
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.990001),
        abs_of_pos (by norm_num : (0 : ℝ) < 1 - 0.990001), unitRoundoff_f32_eq]
      norm_num)
    (by norm_num) (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num)
  exact ⟨h1, h2, h3.trans (by norm_num), h4.trans (by norm_num)⟩

set_option exponentiation.threshold 4000 in
/-- **Row `a = 0.999` of the smoother table in `proofs/README.md`, f32.** For every real `A` with
`0 ≤ A ≤ 0.999001` (`A = 1 - C`, `C` the value of the stored coefficient), inputs at most `M = 1`
in size and a starting state of value `S = 0`, in binary32: the stability condition holds,
`B = outBound A 1 0 = 1`, `E = errBound A u η 1 0 ≤ 6 × 10⁻⁵` and `20·log₁₀ E ≤ −84.4`.
f32 stores 0.999 as 0.9990000129 (worked out outside Lean, not proved); since that is between 1/2
and 2, `1 - a` is computed exactly (`coeff_f32_exact`), so `A` is that stored value, and the
bound 0.999001 leaves room for it. -/
theorem table_row_le_of_le_0999_f32 (A : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 0.999001) :
    |A| + errGrowth A unitRoundoff_f32 < 1 ∧ outBound A 1 0 = 1 ∧
      errBound A unitRoundoff_f32 underflowErr_f32 1 0 ≤ 6 * 10 ^ (-5 : ℤ) ∧
      20 * Real.logb 10 (errBound A unitRoundoff_f32 underflowErr_f32 1 0) ≤ -84.4 := by
  have hu : 0 < unitRoundoff_f32 := by rw [unitRoundoff_f32_eq]; positivity
  have hη : 0 ≤ underflowErr_f32 := by rw [underflowErr_f32_eq]; positivity
  obtain ⟨h1, h2, h3, h4⟩ := table_row_le_of_le A 0.999001 _ _ (2 ^ (-150 : ℤ)) 6 5 50 211
    hu (by rw [unitRoundoff_f32_eq]; norm_num) hη underflowErr_f32_eq.le hA0 hA
    (by
      unfold errGrowth
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 0.999001),
        abs_of_pos (by norm_num : (0 : ℝ) < 1 - 0.999001), unitRoundoff_f32_eq]
      norm_num)
    (by norm_num) (by rw [unitRoundoff_f32_eq]; norm_num) (by norm_num)
  exact ⟨h1, h2, h3.trans (by norm_num), h4.trans (by norm_num)⟩

/-- **The size condition of `process_f32_block_error_of_inputs` and
`process_f32_settle_of_inputs` holds for row `0.99` of the smoother table, f32.** For every
real `A` with `0 ≤ A ≤ 0.990001`, `M = 1` and a starting state of value `S = 0`, in binary32: with
`W = B + E` (`B = outBound A 1 0`, `E = errBound A u η 1 0`) and `G = (1 + u)·(M + W) + η`,
`G + W + (1 + u)·|1 - A|·G + η` is at most the largest finite binary32 value. In those theorems
`A = 1 - C` with `C` the value of the stored coefficient, so `|1 - A|` is `|C|`. -/
theorem sizeCondition_of_le_099_f32 (A : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 0.990001) :
    let W := outBound A 1 0 + errBound A unitRoundoff_f32 underflowErr_f32 1 0
    let G := (1 + unitRoundoff_f32) * (1 + W) + underflowErr_f32
    G + W + (1 + unitRoundoff_f32) * |1 - A| * G + underflowErr_f32 ≤ maxFinite_f32 := by
  intro W G
  obtain ⟨hstab, hB, hE, -⟩ := table_row_le_of_le_099_f32 A hA0 hA
  have hu0 : 0 ≤ unitRoundoff_f32 := (Model.unitRoundoffAt_pos _).le
  have hη0 : 0 ≤ underflowErr_f32 := (Model.underflowErrorAt_pos _).le
  obtain ⟨hE0, -, -, -⟩ := block_constants A _ _ 1 0 hu0 hη0 zero_le_one hstab
  have h24 := sizeCondition_le_24 A unitRoundoff_f32 underflowErr_f32
    (errBound A unitRoundoff_f32 underflowErr_f32 1 0) hu0
    (by rw [unitRoundoff_f32_eq]; norm_num) hη0 (by rw [underflowErr_f32_eq]; norm_num) hA0
    (by linarith) hE0 (hE.trans (by norm_num))
  have hmax : (24 : ℝ) ≤ maxFinite_f32 := by
    rw [maxFinite_f32_eq]
    have : (1 : ℝ) ≤ 2 ^ 104 := one_le_pow₀ (by norm_num)
    calc (24 : ℝ) ≤ ((2 ^ 24 - 1)) * 1 := by norm_num
      _ ≤ (2 ^ 24 - 1) * 2 ^ 104 := mul_le_mul_of_nonneg_left this (by norm_num)
  simp only [W, G, hB]
  linarith

/-- **The size condition of `process_f32_block_error_of_inputs` and
`process_f32_settle_of_inputs` holds for row `0.999` of the smoother table, f32.** For every
real `A` with `0 ≤ A ≤ 0.999001`, `M = 1` and a starting state of value `S = 0`, in binary32: with
`W = B + E` (`B = outBound A 1 0`, `E = errBound A u η 1 0`) and `G = (1 + u)·(M + W) + η`,
`G + W + (1 + u)·|1 - A|·G + η` is at most the largest finite binary32 value. In those theorems
`A = 1 - C` with `C` the value of the stored coefficient, so `|1 - A|` is `|C|`. -/
theorem sizeCondition_of_le_0999_f32 (A : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 0.999001) :
    let W := outBound A 1 0 + errBound A unitRoundoff_f32 underflowErr_f32 1 0
    let G := (1 + unitRoundoff_f32) * (1 + W) + underflowErr_f32
    G + W + (1 + unitRoundoff_f32) * |1 - A| * G + underflowErr_f32 ≤ maxFinite_f32 := by
  intro W G
  obtain ⟨hstab, hB, hE, -⟩ := table_row_le_of_le_0999_f32 A hA0 hA
  have hu0 : 0 ≤ unitRoundoff_f32 := (Model.unitRoundoffAt_pos _).le
  have hη0 : 0 ≤ underflowErr_f32 := (Model.underflowErrorAt_pos _).le
  obtain ⟨hE0, -, -, -⟩ := block_constants A _ _ 1 0 hu0 hη0 zero_le_one hstab
  have h24 := sizeCondition_le_24 A unitRoundoff_f32 underflowErr_f32
    (errBound A unitRoundoff_f32 underflowErr_f32 1 0) hu0
    (by rw [unitRoundoff_f32_eq]; norm_num) hη0 (by rw [underflowErr_f32_eq]; norm_num) hA0
    (by linarith) hE0 (hE.trans (by norm_num))
  have hmax : (24 : ℝ) ≤ maxFinite_f32 := by
    rw [maxFinite_f32_eq]
    have : (1 : ℝ) ≤ 2 ^ 104 := one_le_pow₀ (by norm_num)
    calc (24 : ℝ) ≤ ((2 ^ 24 - 1)) * 1 := by norm_num
      _ ≤ (2 ^ 24 - 1) * 2 ^ 104 := mul_le_mul_of_nonneg_left this (by norm_num)
  simp only [W, G, hB]
  linarith

end conjure_dsp_lib.smoother

end
