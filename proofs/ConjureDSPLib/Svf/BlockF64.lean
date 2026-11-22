module

public import ConjureDSPLib.Svf.SpecF64
public import ConjureDSPLib.Svf.Block
public import ConjureDSPLib.Svf.Contraction
public import ConjureDSPLib.FloatFacts

/-!
# The state-variable filter in f64 over a whole block

`process_f64_block_error`: when the Rust `process_f64` filters a block, given a `Contraction`
for the real values of the stored coefficients (see `Svf/Block.lean`), finite coefficients and
starting state, inputs at most `M`, no overflow, and a number `Sb` with `cInf·(R + Ê) ≤ Sb`,
every output and the final state are within distances of the exact real-number filter
`filt_real` that depend on the coefficients, the `Contraction`, `M`, `Sb` and the starting state
but not on the block length.

Each step rounds sixteen times (`svfStep_f64`); `svfStep_f64_localErr` bounds the effect of those
roundings on the step's output by `stepErrOut_f64` and on the new state (both values' errors
added) by `stepErrState_f64`, when the state is at most `Sb` in size, the input at most `M`, and
no intermediate result overflows. `block_error_real` in `Svf/Block.lean` turns that into the
whole-block bound.

`process_f64_block_error_of_inputs` replaces the no-overflow condition by finite inputs and
`stepValueBound_f64 c M Sb ≤ maxFinite_f64`: `stepFinite_f64` shows that a step whose state is
within `Sb` and input within `M` does not overflow when `stepValueBound` is at most the largest
finite value, and `noOverflow_f64_of_inputs` carries the state bound through the block with
`block_step`.

`block_bounds_of_rat_f64` turns rational bounds on `p` and `ρ` into bounds on the constants of
these theorems for `svf.complexPolesContraction`; the last section applies it to the stored
coefficients of `CoeffsF64::low_pass` at chosen cutoffs.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.svf

/-- The exact real values of the six binary64 coefficients. -/
noncomputable def realCoeffs_f64 (c : CoeffsF64) : CoeffsReal where
  g := real_f64 c.g
  k := real_f64 c.k
  d := real_f64 c.d
  m_hp := real_f64 c.m_hp
  m_bp := real_f64 c.m_bp
  m_lp := real_f64 c.m_lp

/-- The exact real values of the two binary64 state values. -/
noncomputable def realState_f64 (s : StateF64) : ℝ × ℝ := (real_f64 s.s1, real_f64 s.s2)

/-- All six coefficients are finite. -/
def CoeffsFinite_f64 (c : CoeffsF64) : Prop :=
  c.g.isFinite = true ∧ c.k.isFinite = true ∧ c.d.isFinite = true ∧
    c.m_hp.isFinite = true ∧ c.m_bp.isFinite = true ∧ c.m_lp.isFinite = true

/-- One step of `svfStep_f64` from state `s` on input `x` does not overflow: `x` and each of the
sixteen intermediate results are finite. These are `k + g`, `(k + g) * s1`, `x - (k + g) * s1`,
`x - (k + g) * s1 - s2`, `hp = (…) * d`, `g * hp`, `bp = g * hp + s1`, `g * bp`,
`lp = g * bp + s2`, `m_hp * hp`, `m_bp * bp`, their sum, `m_lp * lp`, the output, and the new
state values `g * hp + bp` and `g * bp + lp`. -/
def StepFinite_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Prop :=
  let K1 := c.k + c.g
  let P := K1 * s.s1
  let D1 := x - P
  let D2 := D1 - s.s2
  let H := D2 * c.d
  let Q := c.g * H
  let B := Q + s.s1
  let R := c.g * B
  let Lp := R + s.s2
  let Y1 := c.m_hp * H
  let Y2 := c.m_bp * B
  let Y3 := Y1 + Y2
  let Y4 := c.m_lp * Lp
  x.isFinite = true ∧ K1.isFinite = true ∧ P.isFinite = true ∧ D1.isFinite = true ∧
    D2.isFinite = true ∧ H.isFinite = true ∧ Q.isFinite = true ∧ B.isFinite = true ∧
    R.isFinite = true ∧ Lp.isFinite = true ∧ Y1.isFinite = true ∧ Y2.isFinite = true ∧
    Y3.isFinite = true ∧ Y4.isFinite = true ∧ (Y3 + Y4).isFinite = true ∧
    (Q + B).isFinite = true ∧ (R + Lp).isFinite = true

/-- If a step does not overflow, the new first state value is finite. -/
theorem StepFinite_f64.next_s1_isFinite {c : CoeffsF64} {s : StateF64} {x : Float}
    (h : StepFinite_f64 c s x) : (svfStep_f64 c s x).2.s1.isFinite = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h1, -⟩ := h
  exact h1

/-- If a step does not overflow, the new second state value is finite. -/
theorem StepFinite_f64.next_s2_isFinite {c : CoeffsF64} {s : StateF64} {x : Float}
    (h : StepFinite_f64 c s x) : (svfStep_f64 c s x).2.s2.isFinite = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h2⟩ := h
  exact h2

/-- No step overflows: running the filter from state `s` over the inputs, every step is
`StepFinite_f64`. -/
def NoOverflow_f64 (c : CoeffsF64) : StateF64 → List Float → Prop
  | _, [] => True
  | s, x :: xs => StepFinite_f64 c s x ∧ NoOverflow_f64 c (svfStep_f64 c s x).2 xs

/-- `Ly` for binary64: `stepErrOut` with binary64's `u` and `η`, the real values of the stored
coefficients, inputs at most `M` and state values at most `Sb`. -/
noncomputable abbrev stepErrOut_f64 (c : CoeffsF64) (M Sb : ℝ) : ℝ :=
  stepErrOut (realCoeffs_f64 c) unitRoundoff_f64 underflowErr_f64 M Sb

/-- `Ls` for binary64: `stepErrState` with binary64's `u` and `η`. -/
noncomputable abbrev stepErrState_f64 (c : CoeffsF64) (M Sb : ℝ) : ℝ :=
  stepErrState (realCoeffs_f64 c) unitRoundoff_f64 underflowErr_f64 M Sb

/-- `V` for binary64: `stepValueBound` with binary64's `u` and `η`. -/
noncomputable abbrev stepValueBound_f64 (c : CoeffsF64) (M Sb : ℝ) : ℝ :=
  stepValueBound (realCoeffs_f64 c) unitRoundoff_f64 underflowErr_f64 M Sb

/-- `Ê` for binary64: `stateErrBound` with `Ls = stepErrState_f64 c M Sb`. -/
noncomputable abbrev stateErrBound_f64 (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (M Sb : ℝ) : ℝ :=
  stateErrBound (realCoeffs_f64 c) C (stepErrState_f64 c M Sb)

/-- **One step's roundings in binary64.** If the coefficients and state are finite, the step does
not overflow, both state values are at most `Sb` in size and the input at most `M`, then the
output of `svfStep_f64` is within `stepErrOut_f64 c M Sb` of the exact step's from the same state
(`svfStep_real`, on the real values of the stored coefficients, state and input), and the distances
of its two new state values from the exact step's add up to at most `stepErrState_f64 c M Sb`. -/
theorem svfStep_f64_localErr (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hstep : StepFinite_f64 c s x) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M) :
    let e := svfStep_real (realCoeffs_f64 c) (realState_f64 s) (real_f64 x)
    |real_f64 (svfStep_f64 c s x).1 - e.1| ≤ stepErrOut_f64 c M Sb ∧
      |real_f64 (svfStep_f64 c s x).2.s1 - e.2.1| + |real_f64 (svfStep_f64 c s x).2.s2 - e.2.2| ≤
        stepErrState_f64 c M Sb := by
  obtain ⟨hg, hk, hd, hmh, hmb, hml⟩ := hc
  obtain ⟨hx, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩ := hstep
  exact step_localErr (realCoeffs_f64 c) (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hX hS1 hS2
    (abs_real_add_sub_le_f64 _ _ hk hg f1)
    (abs_real_mul_sub_le_f64 _ _ f1 hs1 f2)
    (abs_real_sub_sub_le_f64 _ _ hx f2 f3)
    (abs_real_sub_sub_le_f64 _ _ f3 hs2 f4)
    (abs_real_mul_sub_le_f64 _ _ f4 hd f5)
    (abs_real_mul_sub_le_f64 _ _ hg f5 f6)
    (abs_real_add_sub_le_f64 _ _ f6 hs1 f7)
    (abs_real_mul_sub_le_f64 _ _ hg f7 f8)
    (abs_real_add_sub_le_f64 _ _ f8 hs2 f9)
    (abs_real_mul_sub_le_f64 _ _ hmh f5 f10)
    (abs_real_mul_sub_le_f64 _ _ hmb f7 f11)
    (abs_real_add_sub_le_f64 _ _ f10 f11 f12)
    (abs_real_mul_sub_le_f64 _ _ hml f9 f13)
    (abs_real_add_sub_le_f64 _ _ f12 f13 f14)
    (abs_real_add_sub_le_f64 _ _ f6 f7 f15)
    (abs_real_add_sub_le_f64 _ _ f8 f9 f16)

/-- **One step does not overflow.** If the coefficients, both state values and the input are
finite, both state values are at most `Sb` in size, the input at most `M` in size, and
`V = stepValueBound_f64 c M Sb` is at most the largest finite binary64 value, then none of the
step's sixteen operations overflows (`StepFinite_f64`). -/
theorem stepFinite_f64 (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hx : x.isFinite = true) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M) (hcap : stepValueBound_f64 c M Sb ≤ maxFinite_f64) :
    StepFinite_f64 c s x := by
  obtain ⟨hg, hk, hd, hmh, hmb, hml⟩ := hc
  have h := step_chain (realCoeffs_f64 c) (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hX hS1 hS2 hcap
    (fun hb => let h := isFinite_add_f64 _ _ hk hg hb; ⟨h, abs_real_add_sub_le_f64 _ _ hk hg h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ f hs1 hb; ⟨h, abs_real_mul_sub_le_f64 _ _ f hs1 h⟩)
    (fun f hb => let h := isFinite_sub_f64 _ _ hx f hb; ⟨h, abs_real_sub_sub_le_f64 _ _ hx f h⟩)
    (fun f hb => let h := isFinite_sub_f64 _ _ f hs2 hb; ⟨h, abs_real_sub_sub_le_f64 _ _ f hs2 h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ f hd hb; ⟨h, abs_real_mul_sub_le_f64 _ _ f hd h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ hg f hb; ⟨h, abs_real_mul_sub_le_f64 _ _ hg f h⟩)
    (fun f hb => let h := isFinite_add_f64 _ _ f hs1 hb; ⟨h, abs_real_add_sub_le_f64 _ _ f hs1 h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ hg f hb; ⟨h, abs_real_mul_sub_le_f64 _ _ hg f h⟩)
    (fun f hb => let h := isFinite_add_f64 _ _ f hs2 hb; ⟨h, abs_real_add_sub_le_f64 _ _ f hs2 h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ hmh f hb; ⟨h, abs_real_mul_sub_le_f64 _ _ hmh f h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ hmb f hb; ⟨h, abs_real_mul_sub_le_f64 _ _ hmb f h⟩)
    (fun f f' hb => let h := isFinite_add_f64 _ _ f f' hb; ⟨h, abs_real_add_sub_le_f64 _ _ f f' h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ hml f hb; ⟨h, abs_real_mul_sub_le_f64 _ _ hml f h⟩)
    (fun f f' hb => let h := isFinite_add_f64 _ _ f f' hb; ⟨h, abs_real_add_sub_le_f64 _ _ f f' h⟩)
    (fun f f' hb => let h := isFinite_add_f64 _ _ f f' hb; ⟨h, abs_real_add_sub_le_f64 _ _ f f' h⟩)
    (fun f f' hb => let h := isFinite_add_f64 _ _ f f' hb; ⟨h, abs_real_add_sub_le_f64 _ _ f f' h⟩)
  exact ⟨hx, h.1⟩

/-- If the coefficients and starting state are finite and no step overflows (`NoOverflow_f64`),
then for every `Sb` and `M`, the run of `filt_f64` (as real values) satisfies `WithinLocalErr`
with `Ly = stepErrOut_f64 c M Sb` and `Ls = stepErrState_f64 c M Sb`. -/
theorem filt_f64_withinLocalErr (c : CoeffsF64) (hc : CoeffsFinite_f64 c) (Sb M : ℝ) :
    ∀ (xs : List Float) (s : StateF64), s.s1.isFinite = true → s.s2.isFinite = true →
      NoOverflow_f64 c s xs →
      WithinLocalErr (realCoeffs_f64 c) Sb M (stepErrOut_f64 c M Sb) (stepErrState_f64 c M Sb)
        (realState_f64 s) (xs.map real_f64) (realState_f64 (filt_f64 c s xs).1)
        ((filt_f64 c s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_f64, WithinLocalErr]
  | cons x xs ih =>
    intro s hs1 hs2 hno
    obtain ⟨hstep, hrest⟩ := hno
    have ht1 := hstep.next_s1_isFinite
    have ht2 := hstep.next_s2_isFinite
    simp only [filt_f64, List.map_cons, WithinLocalErr]
    exact ⟨realState_f64 (svfStep_f64 c s x).2,
      fun h1 h2 hX => svfStep_f64_localErr c s x Sb M hc hs1 hs2 hstep h1 h2 hX,
      ih _ ht1 ht2 hrest⟩

/-- **Whole-block error of the f64 SVF.** Let `C` be a `Contraction` for the real values of the
stored coefficients (`realCoeffs_f64 c`), `0 ≤ M`, every input's real value at most `M` in size,
and `Sb ≥ 0` a number with `cInf·(R + Ê) ≤ Sb`, where `R = exactStateBound` (from the real value
of the starting state) and `Ê = stateErrBound_f64 c C M Sb`. If the coefficients and the starting
state are finite and no step overflows (`NoOverflow_f64`), then the outputs of `filt_f64` and of
`filt_real` (run on the real values of the inputs from `realState_f64 s`) have the same length,
every output's real value is within `outGain·cInf·Ê + Ly` of the corresponding exact output
(`Ly = stepErrOut_f64 c M Sb`), and each final state value's real value within `cInf·Ê` of the
exact one. -/
theorem filt_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c)) (s : StateF64)
    (xs : List Float) (M Sb : ℝ) (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true)
    (hs2 : s.s2.isFinite = true) (hno : NoOverflow_f64 c s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f64 x| ≤ M) (hSb : 0 ≤ Sb)
    (hS : C.cInf * (exactStateBound (realCoeffs_f64 c) C M (realState_f64 s) +
      stateErrBound_f64 c C M Sb) ≤ Sb) :
    let Ê := stateErrBound_f64 c C M Sb
    let F := filt_real (realCoeffs_f64 c) (realState_f64 s) (xs.map real_f64)
    List.Forall₂
        (fun y e => |real_f64 y - e| ≤ outGain (realCoeffs_f64 c) * C.cInf * Ê +
          stepErrOut_f64 c M Sb) (filt_f64 c s xs).2 F.2 ∧
      |real_f64 (filt_f64 c s xs).1.s1 - F.1.1| ≤ C.cInf * Ê ∧
      |real_f64 (filt_f64 c s xs).1.s2 - F.1.2| ≤ C.cInf * Ê := by
  intro Ê F
  have hLs := stepErrState_nonneg (realCoeffs_f64 c) (u := unitRoundoff_f64)
    (η := underflowErr_f64) (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hM0 hSb
  have h := block_error_real (realCoeffs_f64 c) C M Sb _ _ hM0 hLs (realState_f64 s) hS
    (xs.map real_f64) _ _ (by simpa using hM)
    (filt_f64_withinLocalErr c hc Sb M xs s hs1 hs2 hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust SVF `process_f64`.** Under the conditions of
`filt_f64_block_error` (with `state` as the starting state and the buffer as the inputs),
`process_f64` never fails, the buffer it returns has one sample per exact output, each sample's
real value is within `outGain·cInf·Ê + Ly` of the corresponding output of `filt_real` (run on the
real values of the inputs from `realState_f64 state`), and each value of the state it leaves is
within `cInf·Ê` of the exact final state's, where `Ê = stateErrBound_f64 c C M Sb` and
`Ly = stepErrOut_f64 c M Sb`. -/
theorem process_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M Sb : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hno : NoOverflow_f64 c state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M) (hSb : 0 ≤ Sb)
    (hS : C.cInf * (exactStateBound (realCoeffs_f64 c) C M (realState_f64 state) +
      stateErrBound_f64 c C M Sb) ≤ Sb) :
    let Ê := stateErrBound_f64 c C M Sb
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    process_f64 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f64 y - e| ≤ outGain (realCoeffs_f64 c) * C.cInf * Ê +
          stepErrOut_f64 c M Sb) r.2.val F.2 ∧
        |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê F
  have hblock := filt_f64_block_error c C state buf.val M Sb hc hs1 hs2 hno hM0 hM hSb hS
  apply WP.spec_mono (process_f64_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **No overflow, from the inputs alone.** Let `C` be a `Contraction` for the real values of the
stored coefficients, with `G = inputGain` of those values. Suppose the coefficients are finite,
and the numbers `Sb`, `R`, `Ê` satisfy `ρ·R + K·G·M ≤ R`, `ρ·Ê + K·Ls ≤ Ê` (with
`Ls = stepErrState_f64 c M Sb`), `cInf·(R + Ê) ≤ Sb`, and `V = stepValueBound_f64 c M Sb` is at
most the largest finite binary64 value. Start from a state `s` with both values finite, and a real
state `r` that measures at most `R`, with `s`'s real value minus `r` measuring at most `Ê` (for
the filter's own start, `r` is `s`'s real value). If every input is finite and at most `M` in
size, then no step overflows (`NoOverflow_f64`). -/
theorem noOverflow_f64_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (hc : CoeffsFinite_f64 c) (Sb M R Ê : ℝ)
    (hR : C.ρ * R + C.K * inputGain (realCoeffs_f64 c) * M ≤ R)
    (hE : C.ρ * Ê + C.K * stepErrState_f64 c M Sb ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb) (hcap : stepValueBound_f64 c M Sb ≤ maxFinite_f64) :
    ∀ (xs : List Float) (s : StateF64) (r : ℝ × ℝ), s.s1.isFinite = true →
      s.s2.isFinite = true → (∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) →
      C.N r.1 r.2 ≤ R → C.N (real_f64 s.s1 - r.1) (real_f64 s.s2 - r.2) ≤ Ê →
      NoOverflow_f64 c s xs := by
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs1 hs2 hin hr he
    obtain ⟨hx, hX⟩ := hin x (by simp)
    -- The computed state is within `Sb`, so the step does not overflow.
    obtain ⟨hS1, hS2⟩ := C.state_le hS hr he
    have hstep := stepFinite_f64 c s x Sb M hc hs1 hs2 hx hS1 hS2 hX hcap
    -- Its roundings are within `Ly` and `Ls`, so both bounds carry on to the next step.
    obtain ⟨hdy, hdt⟩ := svfStep_f64_localErr c s x Sb M hc hs1 hs2 hstep hS1 hS2 hX
    obtain ⟨-, hr', he'⟩ := block_step _ C (t := realState_f64 (svfStep_f64 c s x).2) hR hE hX
      hr he hdy hdt
    exact ⟨hstep, ih _ _ hstep.next_s1_isFinite hstep.next_s2_isFinite
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) hr' he'⟩

/-- **Whole-block error of the f64 SVF, with conditions on the inputs only.** Let `C` be a
`Contraction` for the real values of the stored coefficients, `0 ≤ M`, `0 ≤ Sb` with
`cInf·(R + Ê) ≤ Sb` (`R = exactStateBound`, `Ê = stateErrBound_f64 c C M Sb`), and
`stepValueBound_f64 c M Sb` at most the largest finite binary64 value (about 1.8 × 10³⁰⁸). If the
coefficients, the starting state and every input are finite and every input's real value is at
most `M` in size, then no step overflows (`NoOverflow_f64`), and the conclusion of
`filt_f64_block_error` holds. -/
theorem filt_f64_block_error_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (s : StateF64) (xs : List Float) (M Sb : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hin : ∀ x ∈ xs, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M) (hSb : 0 ≤ Sb)
    (hS : C.cInf * (exactStateBound (realCoeffs_f64 c) C M (realState_f64 s) +
      stateErrBound_f64 c C M Sb) ≤ Sb)
    (hcap : stepValueBound_f64 c M Sb ≤ maxFinite_f64) :
    let Ê := stateErrBound_f64 c C M Sb
    let F := filt_real (realCoeffs_f64 c) (realState_f64 s) (xs.map real_f64)
    NoOverflow_f64 c s xs ∧
      List.Forall₂
          (fun y e => |real_f64 y - e| ≤ outGain (realCoeffs_f64 c) * C.cInf * Ê +
            stepErrOut_f64 c M Sb) (filt_f64 c s xs).2 F.2 ∧
        |real_f64 (filt_f64 c s xs).1.s1 - F.1.1| ≤ C.cInf * Ê ∧
        |real_f64 (filt_f64 c s xs).1.s2 - F.1.2| ≤ C.cInf * Ê := by
  intro Ê F
  have hLs := stepErrState_nonneg (realCoeffs_f64 c) (u := unitRoundoff_f64)
    (η := underflowErr_f64) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le
    hM0 hSb
  obtain ⟨hR, hE, hr, he⟩ := block_constants (realCoeffs_f64 c) C M _ (realState_f64 s) hM0 hLs
  have hno := noOverflow_f64_of_inputs c C hc Sb M _ _ hR hE hS hcap xs s (realState_f64 s)
    hs1 hs2 hin hr he
  exact ⟨hno, filt_f64_block_error c C s xs M Sb hc hs1 hs2 hno hM0 (fun x hx => (hin x hx).2)
    hSb hS⟩

/-- **Whole-block error of the Rust SVF `process_f64`, with conditions on the inputs only.**
Under the conditions of `filt_f64_block_error_of_inputs` (with `state` as the starting state and
the buffer as the inputs), no step overflows (`NoOverflow_f64`), `process_f64` never fails, and
the conclusion of `process_f64_block_error` holds. -/
theorem process_f64_block_error_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M Sb : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M) (hSb : 0 ≤ Sb)
    (hS : C.cInf * (exactStateBound (realCoeffs_f64 c) C M (realState_f64 state) +
      stateErrBound_f64 c C M Sb) ≤ Sb)
    (hcap : stepValueBound_f64 c M Sb ≤ maxFinite_f64) :
    let Ê := stateErrBound_f64 c C M Sb
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    NoOverflow_f64 c state buf.val ∧
      process_f64 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f64 y - e| ≤ outGain (realCoeffs_f64 c) * C.cInf * Ê +
            stepErrOut_f64 c M Sb) r.2.val F.2 ∧
          |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê F
  have hno := (filt_f64_block_error_of_inputs c C state buf.val M Sb hc hs1 hs2 hin hM0 hSb hS
    hcap).1
  exact ⟨hno, process_f64_block_error c C state buf M Sb hc hs1 hs2 hno hM0
    (fun x hx => (hin x hx).2) hSb hS⟩

/-- **The f64 whole-block constants with `svf.complexPolesContraction`, from rational numbers.**
For stored coefficients with real values `q`, a start of value `(0, 0)` and `M = 1` (inputs at
most 1 in size): suppose `0 < q.d`, `0 < q.g·q.k`, `q.k² < 4·(1/q.d − q.g·(q.g + q.k))`, and,
with `p² = 1/q.d − q.g·(q.g + q.k) − q.k²/4`, `0 < pl`, `0 ≤ pu`, `pl² ≤ p² ≤ pu²`, `0 ≤ ρu < 1`
and `1 − 2·q.g·q.d·q.k ≤ ρu²`. Let `ci = (1 + |q.k|/2)/pl + 1`, `k = pu + |q.k|/2 + 1`,
`u = 2⁻⁵³`, `η = 2⁻¹⁰⁷⁵`, `Ly = stepErrOut q u η 1 Sb` and `Ls = stepErrState q u η 1 Sb`. If
`0 ≤ Sb`, `stateBoundAt q 1 Ls 0 ci k ρu ≤ Sb`, `outErrBoundAt q Ly Ls ci k ρu ≤ X` and
`stepValueBound q u η 1 Sb ≤ Vb`, then for `svf.complexPolesContraction` the condition
`cInf·(R + Ê) ≤ Sb` of the whole-block theorems holds, the bound `outGain·cInf·Ê + Ly` on each
output's error is positive and at most `X`, and `V = stepValueBound_f64 c 1 Sb` is at most `Vb`.
The hypotheses are statements about rational numbers that `norm_num` checks. -/
theorem block_bounds_of_rat_f64 (c : CoeffsF64) (q : CoeffsReal) (hc : realCoeffs_f64 c = q)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) (Sb pl pu ρu X Vb : ℝ)
    (hd : 0 < q.d) (hgk : 0 < q.g * q.k) (h : (normCoeffs q).a1 ^ 2 < 4 * (normCoeffs q).a2)
    (hpl : 0 < pl) (hpu : 0 ≤ pu)
    (hpl2 : pl ^ 2 ≤ 1 / q.d - q.g * (q.g + q.k) - q.k ^ 2 / 4)
    (hpu2 : 1 / q.d - q.g * (q.g + q.k) - q.k ^ 2 / 4 ≤ pu ^ 2)
    (hρu : 0 ≤ ρu) (hρu2 : 1 - 2 * q.g * q.d * q.k ≤ ρu ^ 2) (hρ1 : ρu < 1) (hSb0 : 0 ≤ Sb)
    (hSb : stateBoundAt q 1 (stepErrState q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1 Sb) 0
      ((1 + |q.k| / 2) / pl + 1) (pu + |q.k| / 2 + 1) ρu ≤ Sb)
    (hX : outErrBoundAt q (stepErrOut q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1 Sb)
      (stepErrState q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1 Sb)
      ((1 + |q.k| / 2) / pl + 1) (pu + |q.k| / 2 + 1) ρu ≤ X)
    (hV : stepValueBound q (2 ^ (-53 : ℤ)) (2 ^ (-1075 : ℤ)) 1 Sb ≤ Vb) :
    ∃ (hd : 0 < (realCoeffs_f64 c).d)
      (hgk : 0 < (realCoeffs_f64 c).g * (realCoeffs_f64 c).k)
      (h : (normCoeffs (realCoeffs_f64 c)).a1 ^ 2 < 4 * (normCoeffs (realCoeffs_f64 c)).a2),
      let C := complexPolesContraction (realCoeffs_f64 c) hd hgk h
      C.cInf * (exactStateBound (realCoeffs_f64 c) C 1 (realState_f64 s) +
          stateErrBound_f64 c C 1 Sb) ≤ Sb ∧
        0 < outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 Sb +
          stepErrOut_f64 c 1 Sb ∧
        outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 Sb +
          stepErrOut_f64 c 1 Sb ≤ X ∧
        stepValueBound_f64 c 1 Sb ≤ Vb := by
  subst hc
  rw [← unitRoundoff_f64_eq, ← underflowErr_f64_eq] at hSb hX hV
  refine ⟨hd, hgk, h, ?_⟩
  intro C
  have hu := (Model.unitRoundoffAt_pos _ : 0 < unitRoundoff_f64)
  have hη := (Model.underflowErrorAt_pos _ : 0 < underflowErr_f64)
  have hLs := stepErrState_nonneg (realCoeffs_f64 c) hu.le hη.le zero_le_one hSb0
  have hLy := stepErrOut_pos (realCoeffs_f64 c) hu.le hη zero_le_one hSb0
  obtain ⟨hci, hk, hρ⟩ := complexPolesContraction_bounds (realCoeffs_f64 c) hd hgk h hpl hpu
    hpl2 hpu2 hρu hρu2
  have hs0 : C.N (realState_f64 s).1 (realState_f64 s).2 ≤ 0 := by
    rw [hs]; exact (complexPolesContraction_N_zero _ hd hgk h).le
  obtain ⟨h1, h2⟩ := block_bounds_le (realCoeffs_f64 c) C 1 (stepErrOut_f64 c 1 Sb)
    (stepErrState_f64 c 1 Sb) 0 _ _ ρu (realState_f64 s) zero_le_one hLs hs0 hci hk hρ hρ1
  have hE0 : 0 ≤ stateErrBound_f64 c C 1 Sb := by
    have := C.ρ_lt_one
    unfold stateErrBound_f64 stateErrBound
    exact div_nonneg (mul_nonneg C.K_nonneg hLs) (by linarith)
  have hO : 0 ≤ outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 Sb := by
    have := outGain_nonneg (realCoeffs_f64 c)
    have := C.cInf_nonneg
    positivity
  exact ⟨h1.trans hSb, by linarith, h2.trans hX, hV⟩

/-! ## Low-pass examples, f64

The theorems behind the SVF table in `proofs/README.md`, for `CoeffsF64::low_pass` with
`Q = 0.7071` at 48 kHz. Each `lowPass…_f64` below holds the exact real values of the stored
coefficients at one cutoff `f`, with the mix `(0, 0, 1)`. Worked out outside Lean, not proved:
they are what `CoeffsF64::low_pass(f, 48000.0, 0.7071)` stores, computed by running the Rust code
(with `libm` 0.2.16's `tan`, which is outside the model). -/

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at
a 20 Hz cutoff. Their bits: `g = 0x3F557255904C5104`, `k = 0x3FF6A0AC9F275A9F`,
`d = 0x3FEFF0D94DC294EE`, `m_hp = m_bp = 0`, `m_lp = 0x3FF0000000000000` (1). -/
noncomputable def lowPass20Hz_f64 : CoeffsReal where
  g := (1509171582407745 / 2 ^ 60)
  k := (6369112752609951 / 2 ^ 52)
  d := (4495270190598775 / 2 ^ 52)
  m_hp := 0
  m_bp := 0
  m_lp := 1

-- `norm_num` below evaluates powers such as `2 ^ 1075` and `10 ^ 2413`, above Lean's default
-- limit of 256 on exponents that it evaluates.
set_option exponentiation.threshold 4000 in
/-- **Row 20 Hz of the SVF table in `proofs/README.md`, f64.** For stored binary64 coefficients
whose real values are `lowPass20Hz_f64`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: with `svf.complexPolesContraction` and `Sb = 11.67`, the condition `cInf·(R + Ê) ≤ Sb` of
the whole-block theorems holds, the bound `outGain·cInf·Ê + Ly` on each output's error is at most
2.35 × 10⁻¹¹, `20·log₁₀` of it (the bound in decibels relative to 1.0) is at most −212.5,
`V = stepValueBound_f64` is at most 165, and `V·10³⁵` is at most the largest finite binary64 value.
-/
theorem lowPass20Hz_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass20Hz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (hd : 0 < (realCoeffs_f64 c).d)
      (hgk : 0 < (realCoeffs_f64 c).g * (realCoeffs_f64 c).k)
      (h : (normCoeffs (realCoeffs_f64 c)).a1 ^ 2 < 4 * (normCoeffs (realCoeffs_f64 c)).a2),
      let C := complexPolesContraction (realCoeffs_f64 c) hd hgk h
      C.cInf * (exactStateBound (realCoeffs_f64 c) C 1 (realState_f64 s) +
          stateErrBound_f64 c C 1 11.67) ≤ 11.67 ∧
        outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 11.67 +
          stepErrOut_f64 c 1 11.67 ≤ 2.35 * 10 ^ (-11 : ℤ) ∧
        20 * Real.logb 10
            (outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 11.67 +
              stepErrOut_f64 c 1 11.67) ≤ -212.5 ∧
        stepValueBound_f64 c 1 11.67 ≤ 165 ∧
        stepValueBound_f64 c 1 11.67 * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (block_bounds_of_rat_f64 c _ hc s hs 11.67 0.7070999998 0.7070999999
    0.998150493472 (2.35 * 10 ^ (-11 : ℤ)) 165 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨hd, hgk, h, hS, hpos, hX, hV⟩ := H
    refine ⟨hd, hgk, h, ?_⟩
    intro C
    refine ⟨hS, hX, ?_, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 200 2125 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals svf_bound_norm_num [lowPass20Hz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at
a 100 Hz cutoff. Their bits: `g = 0x3F7ACF0309CDD32F`, `k = 0x3FF6A0AC9F275A9F`,
`d = 0x3FEFB4861F568D23`, `m_hp = m_bp = 0`, `m_lp = 0x3FF0000000000000` (1). -/
noncomputable def lowPass100Hz_f64 : CoeffsReal where
  g := (7545961350812463 / 2 ^ 60)
  k := (6369112752609951 / 2 ^ 52)
  d := (8924212422413603 / 2 ^ 53)
  m_hp := 0
  m_bp := 0
  m_lp := 1

set_option exponentiation.threshold 4000 in
/-- **Row 100 Hz of the SVF table in `proofs/README.md`, f64.** For stored binary64 coefficients
whose real values are `lowPass100Hz_f64`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: with `svf.complexPolesContraction` and `Sb = 11.69`, the condition `cInf·(R + Ê) ≤ Sb` of
the whole-block theorems holds, the bound `outGain·cInf·Ê + Ly` on each output's error is at most
4.98 × 10⁻¹², `20·log₁₀` of it (the bound in decibels relative to 1.0) is at most −226.0,
`V = stepValueBound_f64` is at most 166, and `V·10³⁵` is at most the largest finite binary64 value.
-/
theorem lowPass100Hz_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass100Hz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (hd : 0 < (realCoeffs_f64 c).d)
      (hgk : 0 < (realCoeffs_f64 c).g * (realCoeffs_f64 c).k)
      (h : (normCoeffs (realCoeffs_f64 c)).a1 ^ 2 < 4 * (normCoeffs (realCoeffs_f64 c)).a2),
      let C := complexPolesContraction (realCoeffs_f64 c) hd hgk h
      C.cInf * (exactStateBound (realCoeffs_f64 c) C 1 (realState_f64 s) +
          stateErrBound_f64 c C 1 11.69) ≤ 11.69 ∧
        outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 11.69 +
          stepErrOut_f64 c 1 11.69 ≤ 4.98 * 10 ^ (-12 : ℤ) ∧
        20 * Real.logb 10
            (outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 11.69 +
              stepErrOut_f64 c 1 11.69) ≤ -226.0 ∧
        stepValueBound_f64 c 1 11.69 ≤ 166 ∧
        stepValueBound_f64 c 1 11.69 * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (block_bounds_of_rat_f64 c _ hc s hs 11.69 0.7070999998 0.7070999999
    0.990786610896 (4.98 * 10 ^ (-12 : ℤ)) 166 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨hd, hgk, h, hS, hpos, hX, hV⟩ := H
    refine ⟨hd, hgk, h, ?_⟩
    intro C
    refine ⟨hS, hX, ?_, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 200 2260 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals svf_bound_norm_num [lowPass100Hz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at
a 1 kHz cutoff. Their bits: `g = 0x3FB0C774D5420EED`, `k = 0x3FF6A0AC9F275A9F`,
`d = 0x3FED2BB6413D5307`, `m_hp = m_bp = 0`, `m_lp = 0x3FF0000000000000` (1). -/
noncomputable def lowPass1kHz_f64 : CoeffsReal where
  g := (4722904235380461 / 2 ^ 56)
  k := (6369112752609951 / 2 ^ 52)
  d := (8210836103189255 / 2 ^ 53)
  m_hp := 0
  m_bp := 0
  m_lp := 1

set_option exponentiation.threshold 4000 in
/-- **Row 1 kHz of the SVF table in `proofs/README.md`, f64.** For stored binary64 coefficients
whose real values are `lowPass1kHz_f64`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: with `svf.complexPolesContraction` and `Sb = 11.88`, the condition `cInf·(R + Ê) ≤ Sb` of
the whole-block theorems holds, the bound `outGain·cInf·Ê + Ly` on each output's error is at most
8.55 × 10⁻¹³, `20·log₁₀` of it (the bound in decibels relative to 1.0) is at most −241.3,
`V = stepValueBound_f64` is at most 180, and `V·10³⁵` is at most the largest finite binary64 value.
-/
theorem lowPass1kHz_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass1kHz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (hd : 0 < (realCoeffs_f64 c).d)
      (hgk : 0 < (realCoeffs_f64 c).g * (realCoeffs_f64 c).k)
      (h : (normCoeffs (realCoeffs_f64 c)).a1 ^ 2 < 4 * (normCoeffs (realCoeffs_f64 c)).a2),
      let C := complexPolesContraction (realCoeffs_f64 c) hd hgk h
      C.cInf * (exactStateBound (realCoeffs_f64 c) C 1 (realState_f64 s) +
          stateErrBound_f64 c C 1 11.88) ≤ 11.88 ∧
        outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 11.88 +
          stepErrOut_f64 c 1 11.88 ≤ 8.55 * 10 ^ (-13 : ℤ) ∧
        20 * Real.logb 10
            (outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 11.88 +
              stepErrOut_f64 c 1 11.88) ≤ -241.3 ∧
        stepValueBound_f64 c 1 11.88 ≤ 180 ∧
        stepValueBound_f64 c 1 11.88 * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (block_bounds_of_rat_f64 c _ hc s hs 11.88 0.7070999998 0.7070999999
    0.911594265895 (8.55 * 10 ^ (-13 : ℤ)) 180 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨hd, hgk, h, hS, hpos, hX, hV⟩ := H
    refine ⟨hd, hgk, h, ?_⟩
    intro C
    refine ⟨hS, hX, ?_, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 200 2413 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals svf_bound_norm_num [lowPass1kHz_f64]

/-- The exact real values of the binary64 coefficients stored for the low-pass of this section at
a 10 kHz cutoff. Their bits: `g = 0x3FE88DF153D6A676`, `k = 0x3FF6A0AC9F275A9F`,
`d = 0x3FD7EF3AD05D09E6`, `m_hp = m_bp = 0`, `m_lp = 0x3FF0000000000000` (1). -/
noncomputable def lowPass10kHz_f64 : CoeffsReal where
  g := (3455733537133371 / 2 ^ 52)
  k := (6369112752609951 / 2 ^ 52)
  d := (3368480173622515 / 2 ^ 53)
  m_hp := 0
  m_bp := 0
  m_lp := 1

set_option exponentiation.threshold 4000 in
/-- **Row 10 kHz of the SVF table in `proofs/README.md`, f64.** For stored binary64 coefficients
whose real values are `lowPass10kHz_f64`, `M = 1` (inputs at most 1 in size) and a start of value
`(0, 0)`: with `svf.complexPolesContraction` and `Sb = 14.78`, the condition `cInf·(R + Ê) ≤ Sb` of
the whole-block theorems holds, the bound `outGain·cInf·Ê + Ly` on each output's error is at most
8.84 × 10⁻¹³, `20·log₁₀` of it (the bound in decibels relative to 1.0) is at most −241.0,
`V = stepValueBound_f64` is at most 409, and `V·10³⁵` is at most the largest finite binary64 value.
-/
theorem lowPass10kHz_bounds_f64 (c : CoeffsF64) (hc : realCoeffs_f64 c = lowPass10kHz_f64)
    (s : StateF64) (hs : realState_f64 s = (0, 0)) :
    ∃ (hd : 0 < (realCoeffs_f64 c).d)
      (hgk : 0 < (realCoeffs_f64 c).g * (realCoeffs_f64 c).k)
      (h : (normCoeffs (realCoeffs_f64 c)).a1 ^ 2 < 4 * (normCoeffs (realCoeffs_f64 c)).a2),
      let C := complexPolesContraction (realCoeffs_f64 c) hd hgk h
      C.cInf * (exactStateBound (realCoeffs_f64 c) C 1 (realState_f64 s) +
          stateErrBound_f64 c C 1 14.78) ≤ 14.78 ∧
        outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 14.78 +
          stepErrOut_f64 c 1 14.78 ≤ 8.84 * 10 ^ (-13 : ℤ) ∧
        20 * Real.logb 10
            (outGain (realCoeffs_f64 c) * C.cInf * stateErrBound_f64 c C 1 14.78 +
              stepErrOut_f64 c 1 14.78) ≤ -241.0 ∧
        stepValueBound_f64 c 1 14.78 ≤ 409 ∧
        stepValueBound_f64 c 1 14.78 * 10 ^ 35 ≤ maxFinite_f64 := by
  refine (fun H => ?main) (block_bounds_of_rat_f64 c _ hc s hs 14.78 0.7070999998 0.7070999999
    0.433982183889 (8.84 * 10 ^ (-13 : ℤ)) 409 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case main =>
    obtain ⟨hd, hgk, h, hS, hpos, hX, hV⟩ := H
    refine ⟨hd, hgk, h, ?_⟩
    intro C
    refine ⟨hS, hX, ?_, hV, ?_⟩
    · exact (twenty_logb_le_of_pow_le _ _ 200 2410 hpos hX (by norm_num)
        (by norm_num)).trans (by norm_num)
    · exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans
        (by rw [maxFinite_f64_eq]; norm_num)
  all_goals svf_bound_norm_num [lowPass10kHz_f64]

end conjure_dsp_lib.svf

end
