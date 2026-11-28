module

public import ConjureDSPLib.Biquad.BlockF64
public import ConjureDSPLib.Biquad.Fma
public import ConjureDSPLib.FmaFacts

/-!
# The fused biquad filter in f64

About `step_fma_f64` and `process_fma_f64` from `src/biquad.rs` (the `std` feature), as Aeneas
translated them. Rust's `b.mul_add(x, z)` becomes Lean's `b.fma x z`: `b·x + z` rounded once.
This file proves:

1. `step_fma_f64_eq`: one Rust step is exactly `tdf2_fma_f64`, and never fails;
   `process_fma_f64_spec`: the block loop never fails and gives exactly `filt_fma_f64`.
2. `tdf2_fma_f64_localErr`: one fused step is within `α + β·Sb`, the per-step bound of the unfused
   step (`tdf2_f64_localErr`), with the same `α = localErrBase_f64` and `β = localErrSlope_f64`.
3. `process_fma_f64_block_error` and `process_fma_f64_block_error_of_inputs`: the whole-block
   bounds of `process_f64_block_error` and `process_f64_block_error_of_inputs`, with the same
   constants (`stateErrBound_f64`, `localErrBound_f64`, `stepValueBound_f64`) and the same
   conditions, for the fused Rust function. So every bound proved for particular coefficients in
   `BlockF64.lean` (they are bounds on those constants) holds for the fused filter too.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.biquad

/-- One fused transposed-direct-form-II step in binary64: the output and the new state, computed
as the Rust code does: `y = b0.fma x s1`, `s1' = b1.fma x (-(a1 * y)) + s2`,
`s2' = b2.fma x (-(a2 * y))`. -/
def tdf2_fma_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Float × StateF64 :=
  let y := c.b0.fma x s.s1
  (y, { s1 := c.b1.fma x (-(c.a1 * y)) + s.s2, s2 := c.b2.fma x (-(c.a2 * y)) })

/-- One fused Rust step is exactly `tdf2_fma_f64`, and cannot fail. -/
theorem step_fma_f64_eq (c : CoeffsF64) (s : StateF64) (x : Float) :
    step_fma_f64 c s x = ok (tdf2_fma_f64 c s x) := by
  simp only [step_fma_f64, lift, bind_ok]
  rfl

/-- The fused filter on binary64 numbers: run `tdf2_fma_f64` over a list of input samples from
state `s`, returning the final state and the list of outputs. -/
def filt_fma_f64 (c : CoeffsF64) : StateF64 → List Float → StateF64 × List Float
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_fma_f64 c (tdf2_fma_f64 c s x).2 xs
    (r.1, (tdf2_fma_f64 c s x).1 :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_fma_f64_set_step (c : CoeffsF64) (s : StateF64) (l : List Float) (j : ℕ)
    (hj : j < l.length) :
    (l.set j (tdf2_fma_f64 c s l[j]).1).take (j + 1) ++
        (filt_fma_f64 c (tdf2_fma_f64 c s l[j]).2
          ((l.set j (tdf2_fma_f64 c s l[j]).1).drop (j + 1))).2 =
      l.take j ++ (filt_fma_f64 c s (l.drop j)).2 ∧
    (filt_fma_f64 c (tdf2_fma_f64 c s l[j]).2
        ((l.set j (tdf2_fma_f64 c s l[j]).1).drop (j + 1))).1 =
      (filt_fma_f64 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (tdf2_fma_f64 c s l[j]).1).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (tdf2_fma_f64 c s l[j]).1).take (j + 1) =
      l.take j ++ [(tdf2_fma_f64 c s l[j]).1] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_fma_f64]

/-- The loop, started at position `i`, leaves the first `i` samples alone and filters the rest. -/
theorem process_fma_f64_loop_spec (c : CoeffsF64) (state : StateF64) (buf : Slice Float)
    (i : Std.Usize) (hi : i.val ≤ buf.length) :
    process_fma_f64_loop c state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_fma_f64 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_fma_f64 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_fma_f64_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_fma_f64 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_fma_f64 c state (buf.val.drop i.val)).2 ∧
      (filt_fma_f64 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_fma_f64 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_fma_f64_loop.body, step_fma_f64_eq]
    step*
    · subst fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_fma_f64_set_step c st b.val j.val hjl
      generalize hT : tdf2_fma_f64 c st (↑b)[↑j] = T at h1 h2
      obtain ⟨y, s'⟩ := T
      step*
      subst s_post
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_fma_f64] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The fused Rust block-processing function never fails, and its output samples and final state
are exactly those of `filt_fma_f64`, sample by sample. -/
theorem process_fma_f64_spec (c : CoeffsF64) (state : StateF64) (buf : Slice Float) :
    process_fma_f64 c state buf ⦃ fun r =>
      r.2.val = (filt_fma_f64 c state buf.val).2 ∧ r.1 = (filt_fma_f64 c state buf.val).1 ⦄ := by
  simpa using process_fma_f64_loop_spec c state buf 0#usize (by simp)

/-- One fused step from state `s` on input `x` does not overflow: `x` and the six rounded results
are finite. With `y = b0.fma x s1` the output, these are `y`, `a1 * y`,
`b1.fma x (-(a1 * y))`, the new `s1` (that plus `s2`), `a2 * y` and the new
`s2 = b2.fma x (-(a2 * y))`. -/
def StepFiniteFma_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Prop :=
  let y := c.b0.fma x s.s1
  x.isFinite = true ∧ y.isFinite = true ∧ (c.a1 * y).isFinite = true ∧
    (c.b1.fma x (-(c.a1 * y))).isFinite = true ∧
    (c.b1.fma x (-(c.a1 * y)) + s.s2).isFinite = true ∧
    (c.a2 * y).isFinite = true ∧ (c.b2.fma x (-(c.a2 * y))).isFinite = true

/-- No fused step overflows: running the fused filter from state `s` over the inputs, every step
is `StepFiniteFma_f64`. -/
def NoOverflowFma_f64 (c : CoeffsF64) : StateF64 → List Float → Prop
  | _, [] => True
  | s, x :: xs => StepFiniteFma_f64 c s x ∧ NoOverflowFma_f64 c (tdf2_fma_f64 c s x).2 xs

/-- **One fused step's roundings in binary64.** If the coefficients and state are finite, the
fused step does not overflow, both state values are at most `Sb` in size and the input at most
`M`, then the output and the two new state values of `tdf2_fma_f64` are each within `α + β·Sb`
(`localErrBase_f64`, `localErrSlope_f64`: the constants of the unfused `tdf2_f64_localErr`) of
the exact step from the same state and the computed output. -/
theorem tdf2_fma_f64_localErr (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hstep : StepFiniteFma_f64 c s x) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M) :
    let cr := realCoeffs_f64 c
    let L := localErrBase_f64 c M + localErrSlope_f64 c * Sb
    let Y := real_f64 (tdf2_fma_f64 c s x).1
    |Y - (cr.b0 * real_f64 x + real_f64 s.s1)| ≤ L ∧
      |real_f64 (tdf2_fma_f64 c s x).2.s1 - (cr.b1 * real_f64 x - cr.a1 * Y + real_f64 s.s2)|
        ≤ L ∧
      |real_f64 (tdf2_fma_f64 c s x).2.s2 - (cr.b2 * real_f64 x - cr.a2 * Y)| ≤ L := by
  obtain ⟨hb0, hb1, hb2, ha1, ha2⟩ := hc
  obtain ⟨hx, hy, hq1, hd1, ht1, hq2, ht2⟩ := hstep
  exact step_localErr_fma (realCoeffs_f64 c) (Model.unitRoundoffAt_pos _).le
    (Model.unitRoundoffAt_lt_one _).le (Model.underflowErrorAt_pos _).le hX hS1 hS2
    (abs_real_fma_sub_le_f64 _ _ _ hb0 hx hs1 hy)
    (abs_real_mul_sub_le_f64 _ _ ha1 hy hq1)
    (abs_real_fma_neg_sub_le_f64 _ _ _ hb1 hx hq1 hd1)
    (abs_real_add_sub_le_f64 _ _ hd1 hs2 ht1)
    (abs_real_mul_sub_le_f64 _ _ ha2 hy hq2)
    (abs_real_fma_neg_sub_le_f64 _ _ _ hb2 hx hq2 ht2)

/-- Without overflow, the run of `filt_fma_f64` satisfies `WithinLocalErr` with
`L = α + β·Sb`, as the unfused `filt_f64_withinLocalErr`. -/
theorem filt_fma_f64_withinLocalErr (c : CoeffsF64) (hc : CoeffsFinite_f64 c) (Sb M : ℝ) :
    ∀ (xs : List Float) (s : StateF64), s.s1.isFinite = true → s.s2.isFinite = true →
      NoOverflowFma_f64 c s xs →
      WithinLocalErr (realCoeffs_f64 c) Sb M (localErrBase_f64 c M + localErrSlope_f64 c * Sb)
        (realState_f64 s) (xs.map real_f64) (realState_f64 (filt_fma_f64 c s xs).1)
        ((filt_fma_f64 c s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_fma_f64, WithinLocalErr, realState_f64]
  | cons x xs ih =>
    intro s hs1 hs2 hno
    obtain ⟨hstep, hrest⟩ := hno
    have ht1 : (tdf2_fma_f64 c s x).2.s1.isFinite = true := hstep.2.2.2.2.1
    have ht2 : (tdf2_fma_f64 c s x).2.s2.isFinite = true := hstep.2.2.2.2.2.2
    simp only [filt_fma_f64, List.map_cons, realState_f64, WithinLocalErr]
    exact ⟨_, _, fun h1 h2 hX => tdf2_fma_f64_localErr c s x Sb M hc hs1 hs2 hstep h1 h2 hX,
      ih _ ht1 ht2 hrest⟩

/-- **Whole-block error of the fused Rust biquad `process_fma_f64`.** The statement of
`process_f64_block_error`, word for word, for the fused function: under its conditions (a
`Contraction` `C` for `realCoeffs_f64 c`, finite coefficients and starting state, inputs at most
`M ≥ 0`, no fused step overflows, `cInf·K·κ·β < 1 − ρ`), `process_fma_f64` never fails, each
sample it writes is within `cInf·Ê + L` of the exact filter's output and each value of the state
it leaves within `cInf·Ê` of the exact final state's, with `Ê = stateErrBound_f64 c C M state` and
`L = localErrBound_f64 c C M state`. -/
theorem process_fma_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hno : NoOverflowFma_f64 c state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ) :
    let Ê := stateErrBound_f64 c C M state
    let L := localErrBound_f64 c C M state
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    process_fma_f64 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f64 y - e| ≤ C.cInf * Ê + L) r.2.val F.2 ∧
        |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê L F
  have h := block_error_real (realCoeffs_f64 c) C M _ _ hM0
    (localErrBase_nonneg _ (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0)
    (localErrSlope_nonneg _ (Model.unitRoundoffAt_pos _).le) hsmall (buf.val.map real_f64)
    (realState_f64 state) _ _ (by simpa using hM)
    (filt_fma_f64_withinLocalErr c hc _ M buf.val state hs1 hs2 hno)
  apply WP.spec_mono (process_fma_f64_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **One fused step does not overflow**, under the conditions of the unfused `stepFinite_f64`:
finite coefficients, state and input, state values at most `Sb`, input at most `M`, and
`stepValueBound (realCoeffs_f64 c) η M Sb` at most the largest finite binary64 value. -/
theorem stepFiniteFma_f64 (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hx : x.isFinite = true) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M)
    (hcap : stepValueBound (realCoeffs_f64 c) underflowErr_f64 M Sb ≤ maxFinite_f64) :
    StepFiniteFma_f64 c s x := by
  obtain ⟨hb0, hb1, hb2, ha1, ha2⟩ := hc
  have hu := (Model.unitRoundoffAt_pos FloatFormat.binary64).le
  have hη := (Model.underflowErrorAt_pos FloatFormat.binary64).le
  -- The unfused chain of bounds, with the three products `b·x` taken as exact.
  obtain ⟨-, -, -, rest⟩ := step_values_le (realCoeffs_f64 c) (u := unitRoundoff_f64)
    (P0 := real_f64 c.b0 * real_f64 x) (Y := real_f64 (c.b0.fma x s.s1))
    (P1 := real_f64 c.b1 * real_f64 x) (Q1 := real_f64 (c.a1 * c.b0.fma x s.s1))
    (D1 := real_f64 (c.b1.fma x (-(c.a1 * c.b0.fma x s.s1))))
    (P2 := real_f64 c.b2 * real_f64 x) (Q2 := real_f64 (c.a2 * c.b0.fma x s.s1))
    hu (Model.unitRoundoffAt_lt_one _).le hη hX hS1 hS2
  obtain ⟨vy, rest⟩ := rest (exact_within hu hη)
  have hy := isFinite_fma_f64 _ _ _ hb0 hx hs1 (vy.trans hcap)
  obtain ⟨vq1, vq2, r1, r2⟩ := rest (abs_real_fma_sub_le_f64 _ _ _ hb0 hx hs1 hy)
  have hq1 := isFinite_mul_f64 _ _ ha1 hy (vq1.trans hcap)
  obtain ⟨vd1, r1⟩ := r1 (exact_within hu hη) (abs_real_mul_sub_le_f64 _ _ ha1 hy hq1)
  have hd1 := isFinite_fma_neg_f64 _ _ _ hb1 hx hq1 (vd1.trans hcap)
  have ht1 := isFinite_add_f64 _ _ hd1 hs2
    ((r1 (abs_real_fma_neg_sub_le_f64 _ _ _ hb1 hx hq1 hd1)).trans hcap)
  have hq2 := isFinite_mul_f64 _ _ ha2 hy (vq2.trans hcap)
  have ht2 := isFinite_fma_neg_f64 _ _ _ hb2 hx hq2
    ((r2 (exact_within hu hη) (abs_real_mul_sub_le_f64 _ _ ha2 hy hq2)).trans hcap)
  exact ⟨hx, hy, hq1, hd1, ht1, hq2, ht2⟩

/-- **No fused overflow, from the inputs alone**, under the conditions of the unfused
`noOverflow_f64_of_inputs`, word for word. -/
theorem noOverflowFma_f64_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (hc : CoeffsFinite_f64 c) (Sb M R Ê : ℝ)
    (hR : C.ρ * R + C.K * inputGain (realCoeffs_f64 c) * M ≤ R)
    (hE : C.ρ * Ê + C.K * ((localErrBase_f64 c M + localErrSlope_f64 c * Sb) *
        roundGain (realCoeffs_f64 c)) ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb)
    (hcap : stepValueBound (realCoeffs_f64 c) underflowErr_f64 M Sb ≤ maxFinite_f64) :
    ∀ (xs : List Float) (s : StateF64) (r : ℝ × ℝ), s.s1.isFinite = true →
      s.s2.isFinite = true → (∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) →
      C.N r.1 r.2 ≤ R → C.N (real_f64 s.s1 - r.1) (real_f64 s.s2 - r.2) ≤ Ê →
      NoOverflowFma_f64 c s xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs1 hs2 hin hr he
    obtain ⟨hx, hX⟩ := hin x (by simp)
    obtain ⟨hS1, hS2⟩ := C.state_le hS hr he
    have hstep := stepFiniteFma_f64 c s x Sb M hc hs1 hs2 hx hS1 hS2 hX hcap
    obtain ⟨hdy, hd₁, hd₂⟩ := tdf2_fma_f64_localErr c s x Sb M hc hs1 hs2 hstep hS1 hS2 hX
    obtain ⟨-, hr', he'⟩ := block_step _ C hR hE hX hr he hdy hd₁ hd₂
    let cr := realCoeffs_f64 c
    exact ⟨hstep, ih _ (cr.b1 * real_f64 x - cr.a1 * (cr.b0 * real_f64 x + r.1) + r.2,
      cr.b2 * real_f64 x - cr.a2 * (cr.b0 * real_f64 x + r.1)) hstep.2.2.2.2.1
      hstep.2.2.2.2.2.2 (fun z hz => hin z (List.mem_cons_of_mem _ hz)) hr' he'⟩

/-- **Whole-block error of the fused Rust biquad `process_fma_f64`, with conditions on the inputs
only.** The statement of `process_f64_block_error_of_inputs`, word for word, for the fused
function: if the coefficients, `state` and every sample are finite, every sample's real value is
at most `M ≥ 0` in size, `cInf·K·κ·β < 1 − ρ`, and `stepValueBound_f64 c C M state` is at most the
largest finite binary64 value, then no fused step overflows, `process_fma_f64` never fails, each
sample it writes is within `cInf·Ê + L` of the exact filter's output, and each value of the state
it leaves within `cInf·Ê` of the exact final state's. -/
theorem process_fma_f64_block_error_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M)
    (hsmall : C.cInf * C.K * roundGain (realCoeffs_f64 c) * localErrSlope_f64 c < 1 - C.ρ)
    (hcap : stepValueBound_f64 c C M state ≤ maxFinite_f64) :
    let Ê := stateErrBound_f64 c C M state
    let L := localErrBound_f64 c C M state
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    NoOverflowFma_f64 c state buf.val ∧
      process_fma_f64 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f64 y - e| ≤ C.cInf * Ê + L) r.2.val F.2 ∧
          |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê L F
  obtain ⟨hR, hE, hS, hr, he⟩ := block_constants (realCoeffs_f64 c) C M _ _ (realState_f64 state)
    hM0
    (localErrBase_nonneg _ (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0)
    (localErrSlope_nonneg _ (Model.unitRoundoffAt_pos _).le) hsmall
  have hno := noOverflowFma_f64_of_inputs c C hc _ M _ _ hR hE hS hcap buf.val state
    (realState_f64 state) hs1 hs2 hin hr he
  exact ⟨hno, process_fma_f64_block_error c C state buf M hc hs1 hs2 hno hM0
    (fun x hx => (hin x hx).2) hsmall⟩

end conjure_dsp_lib.biquad

end
