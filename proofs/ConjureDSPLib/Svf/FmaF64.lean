module

public import ConjureDSPLib.Svf.BlockF64
public import ConjureDSPLib.Svf.Fma
public import ConjureDSPLib.FmaFacts

/-!
# The fused state-variable filter in f64

About `step_fma_f64` and `process_fma_f64` from `src/svf.rs` (the `std` feature), as Aeneas
translated them. Rust's `a.mul_add(b, z)` becomes Lean's `a.fma b z`: `a·b + z` rounded once.
This file proves:

1. `step_fma_f64_eq`: one Rust step is exactly `svfStep_fma_f64`, and never fails;
   `process_fma_f64_spec`: the block loop never fails and gives exactly `filt_fma_f64`.
2. `svfStep_fma_f64_localErr`: one fused step is within the per-step bounds of the unfused step
   (`svfStep_f64_localErr`), `stepErrOut_f64` and `stepErrState_f64`.
3. `process_fma_f64_block_error` and `process_fma_f64_block_error_of_inputs`: the whole-block
   bounds of `process_f64_block_error` and `process_f64_block_error_of_inputs`, with the same
   constants and conditions, for the fused Rust function. So every bound proved for particular
   coefficients in `BlockF64.lean` (they are bounds on those constants) holds for the fused
   filter too.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.svf

open conjure_dsp_lib.biquad (exact_within)

/-- One fused state-variable-filter step in binary64: the output and the new state, computed as
the Rust code does. -/
def svfStep_fma_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Float × StateF64 :=
  let hp := ((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d
  let bp := c.g.fma hp s.s1
  let lp := c.g.fma bp s.s2
  (c.m_lp.fma lp (c.m_hp.fma hp (c.m_bp * bp)), { s1 := c.g.fma hp bp, s2 := c.g.fma bp lp })

/-- One fused Rust step is exactly `svfStep_fma_f64`, and cannot fail. -/
theorem step_fma_f64_eq (c : CoeffsF64) (s : StateF64) (x : Float) :
    step_fma_f64 c s x = ok (svfStep_fma_f64 c s x) := by
  simp only [step_fma_f64, lift, bind_ok]
  rfl

/-- The fused filter on binary64 numbers: run `svfStep_fma_f64` over a list of input samples from
state `s`, returning the final state and the list of outputs. -/
def filt_fma_f64 (c : CoeffsF64) : StateF64 → List Float → StateF64 × List Float
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_fma_f64 c (svfStep_fma_f64 c s x).2 xs
    (r.1, (svfStep_fma_f64 c s x).1 :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_fma_f64_set_step (c : CoeffsF64) (s : StateF64) (l : List Float) (j : ℕ)
    (hj : j < l.length) :
    (l.set j (svfStep_fma_f64 c s l[j]).1).take (j + 1) ++
        (filt_fma_f64 c (svfStep_fma_f64 c s l[j]).2
          ((l.set j (svfStep_fma_f64 c s l[j]).1).drop (j + 1))).2 =
      l.take j ++ (filt_fma_f64 c s (l.drop j)).2 ∧
    (filt_fma_f64 c (svfStep_fma_f64 c s l[j]).2
        ((l.set j (svfStep_fma_f64 c s l[j]).1).drop (j + 1))).1 =
      (filt_fma_f64 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (svfStep_fma_f64 c s l[j]).1).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (svfStep_fma_f64 c s l[j]).1).take (j + 1) =
      l.take j ++ [(svfStep_fma_f64 c s l[j]).1] := by
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
      generalize hT : svfStep_fma_f64 c st (↑b)[↑j] = T at h1 h2
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

/-- One fused step from state `s` on input `x` does not overflow: `x` and each of the eleven
rounded results are finite. These are `K1 = k + g`, `D1 = (-K1).fma s1 x`, `D2 = D1 - s2`,
`hp = D2 * d`, `bp = g.fma hp s1`, `lp = g.fma bp s2`, `Y2 = m_bp * bp`, `Y3 = m_hp.fma hp Y2`, the
output `m_lp.fma lp Y3`, and the new state values `g.fma hp bp` and `g.fma bp lp`. -/
def StepFiniteFma_f64 (c : CoeffsF64) (s : StateF64) (x : Float) : Prop :=
  let K1 := c.k + c.g
  let D1 := (-K1).fma s.s1 x
  let D2 := D1 - s.s2
  let H := D2 * c.d
  let B := c.g.fma H s.s1
  let Lp := c.g.fma B s.s2
  let Y2 := c.m_bp * B
  let Y3 := c.m_hp.fma H Y2
  x.isFinite = true ∧ K1.isFinite = true ∧ D1.isFinite = true ∧ D2.isFinite = true ∧
    H.isFinite = true ∧ B.isFinite = true ∧ Lp.isFinite = true ∧ Y2.isFinite = true ∧
    Y3.isFinite = true ∧ (c.m_lp.fma Lp Y3).isFinite = true ∧
    (c.g.fma H B).isFinite = true ∧ (c.g.fma B Lp).isFinite = true

/-- If a fused step does not overflow, the new first state value is finite. -/
theorem StepFiniteFma_f64.next_s1_isFinite {c : CoeffsF64} {s : StateF64} {x : Float}
    (h : StepFiniteFma_f64 c s x) : (svfStep_fma_f64 c s x).2.s1.isFinite = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h1, -⟩ := h
  exact h1

/-- If a fused step does not overflow, the new second state value is finite. -/
theorem StepFiniteFma_f64.next_s2_isFinite {c : CoeffsF64} {s : StateF64} {x : Float}
    (h : StepFiniteFma_f64 c s x) : (svfStep_fma_f64 c s x).2.s2.isFinite = true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h2⟩ := h
  exact h2

/-- No fused step overflows: running the fused filter from state `s` over the inputs, every step
is `StepFiniteFma_f64`. -/
def NoOverflowFma_f64 (c : CoeffsF64) : StateF64 → List Float → Prop
  | _, [] => True
  | s, x :: xs => StepFiniteFma_f64 c s x ∧ NoOverflowFma_f64 c (svfStep_fma_f64 c s x).2 xs

/-- **One fused step's roundings in binary64.** Under the conditions of the unfused
`svfStep_f64_localErr` (finite coefficients and state, no overflow, state values at most `Sb`,
input at most `M`), the output of `svfStep_fma_f64` is within `stepErrOut_f64 c M Sb` of the
exact step's, and the distances of its two new state values from the exact step's add up to at
most `stepErrState_f64 c M Sb`: the bounds of the unfused step. -/
theorem svfStep_fma_f64_localErr (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hstep : StepFiniteFma_f64 c s x) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M) :
    let e := svfStep_real (realCoeffs_f64 c) (realState_f64 s) (real_f64 x)
    |real_f64 (svfStep_fma_f64 c s x).1 - e.1| ≤ stepErrOut_f64 c M Sb ∧
      |real_f64 (svfStep_fma_f64 c s x).2.s1 - e.2.1| +
          |real_f64 (svfStep_fma_f64 c s x).2.s2 - e.2.2| ≤
        stepErrState_f64 c M Sb := by
  obtain ⟨hg, hk, hd, hmh, hmb, hml⟩ := hc
  obtain ⟨hx, f1, f3, f4, f5, f7, f9, f11, f12, f14, f15, f16⟩ := hstep
  have h14 := abs_real_fma_sub_le_f64 _ _ _ hml f9 f12 f14
  rw [add_comm (real_f64 c.m_lp * _)] at h14
  exact step_localErr_fma (realCoeffs_f64 c) (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hX hS1 hS2
    (abs_real_add_sub_le_f64 _ _ hk hg f1)
    (abs_real_neg_fma_sub_le_f64 _ _ _ f1 hs1 hx f3)
    (abs_real_sub_sub_le_f64 _ _ f3 hs2 f4)
    (abs_real_mul_sub_le_f64 _ _ f4 hd f5)
    (abs_real_fma_sub_le_f64 _ _ _ hg f5 hs1 f7)
    (abs_real_fma_sub_le_f64 _ _ _ hg f7 hs2 f9)
    (abs_real_mul_sub_le_f64 _ _ hmb f7 f11)
    (abs_real_fma_sub_le_f64 _ _ _ hmh f5 f11 f12)
    h14
    (abs_real_fma_sub_le_f64 _ _ _ hg f5 f7 f15)
    (abs_real_fma_sub_le_f64 _ _ _ hg f7 f9 f16)

/-- **One fused step does not overflow**, under the conditions of the unfused `stepFinite_f64`:
finite coefficients, state and input, state values at most `Sb`, input at most `M`, and
`stepValueBound_f64 c M Sb` at most the largest finite binary64 value. -/
theorem stepFiniteFma_f64 (c : CoeffsF64) (s : StateF64) (x : Float) (Sb M : ℝ)
    (hc : CoeffsFinite_f64 c) (hs1 : s.s1.isFinite = true) (hs2 : s.s2.isFinite = true)
    (hx : x.isFinite = true) (hS1 : |real_f64 s.s1| ≤ Sb) (hS2 : |real_f64 s.s2| ≤ Sb)
    (hX : |real_f64 x| ≤ M) (hcap : stepValueBound_f64 c M Sb ≤ maxFinite_f64) :
    StepFiniteFma_f64 c s x := by
  obtain ⟨hg, hk, hd, hmh, hmb, hml⟩ := hc
  have hu := (Model.unitRoundoffAt_pos FloatFormat.binary64).le
  have hη := (Model.underflowErrorAt_pos FloatFormat.binary64).le
  -- The unfused chain of bounds, with the five fused products taken as exact.
  have h := step_chain (realCoeffs_f64 c) (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hX hS1 hS2 hcap
    (K1 := real_f64 (c.k + c.g)) (P := real_f64 (c.k + c.g) * real_f64 s.s1)
    (D1 := real_f64 ((-(c.k + c.g)).fma s.s1 x))
    (D2 := real_f64 ((-(c.k + c.g)).fma s.s1 x - s.s2))
    (H := real_f64 (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d))
    (Q := real_f64 c.g * real_f64 (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d))
    (B := real_f64 (c.g.fma (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d) s.s1))
    (R := real_f64 c.g * real_f64 (c.g.fma (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d) s.s1))
    (Y1 := real_f64 c.m_hp * real_f64 (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d))
    (F2 := (c.k + c.g).isFinite = true)
    (F6 := (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d).isFinite = true)
    (F8 := (c.g.fma (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d) s.s1).isFinite = true)
    (F10 := (((-(c.k + c.g)).fma s.s1 x - s.s2) * c.d).isFinite = true)
    (fun hb => let h := isFinite_add_f64 _ _ hk hg hb; ⟨h, abs_real_add_sub_le_f64 _ _ hk hg h⟩)
    (fun f _ => ⟨f, exact_within hu hη⟩)
    (fun f hb => let h := isFinite_neg_fma_f64 _ _ _ f hs1 hx hb;
      ⟨h, abs_real_neg_fma_sub_le_f64 _ _ _ f hs1 hx h⟩)
    (fun f hb => let h := isFinite_sub_f64 _ _ f hs2 hb; ⟨h, abs_real_sub_sub_le_f64 _ _ f hs2 h⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ f hd hb; ⟨h, abs_real_mul_sub_le_f64 _ _ f hd h⟩)
    (fun f _ => ⟨f, exact_within hu hη⟩)
    (fun f hb => let h := isFinite_fma_f64 _ _ _ hg f hs1 hb;
      ⟨h, abs_real_fma_sub_le_f64 _ _ _ hg f hs1 h⟩)
    (fun f _ => ⟨f, exact_within hu hη⟩)
    (fun f hb => let h := isFinite_fma_f64 _ _ _ hg f hs2 hb;
      ⟨h, abs_real_fma_sub_le_f64 _ _ _ hg f hs2 h⟩)
    (fun f _ => ⟨f, exact_within hu hη⟩)
    (fun f hb => let h := isFinite_mul_f64 _ _ hmb f hb; ⟨h, abs_real_mul_sub_le_f64 _ _ hmb f h⟩)
    (fun f f' hb => let h := isFinite_fma_f64 _ _ _ hmh f f' hb;
      ⟨h, abs_real_fma_sub_le_f64 _ _ _ hmh f f' h⟩)
    (fun f _ => ⟨f, exact_within hu hη⟩)
    (fun f f' hb => by
      rw [add_comm] at hb
      have h := isFinite_fma_f64 _ _ _ hml f' f hb
      refine ⟨h, ?_⟩
      have e := abs_real_fma_sub_le_f64 _ _ _ hml f' f h
      rwa [add_comm (real_f64 c.m_lp * _)] at e)
    (fun f f' hb => let h := isFinite_fma_f64 _ _ _ hg f f' hb;
      ⟨h, abs_real_fma_sub_le_f64 _ _ _ hg f f' h⟩)
    (fun f f' hb => let h := isFinite_fma_f64 _ _ _ hg f f' hb;
      ⟨h, abs_real_fma_sub_le_f64 _ _ _ hg f f' h⟩)
  obtain ⟨⟨f1, -, f3, f4, f5, -, f7, -, f9, -, f11, f12, -, f14, f15, f16⟩, -⟩ := h
  exact ⟨hx, f1, f3, f4, f5, f7, f9, f11, f12, f14, f15, f16⟩

/-- Without overflow, the run of `filt_fma_f64` satisfies `WithinLocalErr` with
`Ly = stepErrOut_f64 c M Sb` and `Ls = stepErrState_f64 c M Sb`, as the unfused
`filt_f64_withinLocalErr`. -/
theorem filt_fma_f64_withinLocalErr (c : CoeffsF64) (hc : CoeffsFinite_f64 c) (Sb M : ℝ) :
    ∀ (xs : List Float) (s : StateF64), s.s1.isFinite = true → s.s2.isFinite = true →
      NoOverflowFma_f64 c s xs →
      WithinLocalErr (realCoeffs_f64 c) Sb M (stepErrOut_f64 c M Sb) (stepErrState_f64 c M Sb)
        (realState_f64 s) (xs.map real_f64) (realState_f64 (filt_fma_f64 c s xs).1)
        ((filt_fma_f64 c s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _ _; simp [filt_fma_f64, WithinLocalErr]
  | cons x xs ih =>
    intro s hs1 hs2 hno
    obtain ⟨hstep, hrest⟩ := hno
    have ht1 := hstep.next_s1_isFinite
    have ht2 := hstep.next_s2_isFinite
    simp only [filt_fma_f64, List.map_cons, WithinLocalErr]
    exact ⟨realState_f64 (svfStep_fma_f64 c s x).2,
      fun h1 h2 hX => svfStep_fma_f64_localErr c s x Sb M hc hs1 hs2 hstep h1 h2 hX,
      ih _ ht1 ht2 hrest⟩

/-- **Whole-block error of the fused Rust SVF `process_fma_f64`.** The statement of
`process_f64_block_error`, word for word, for the fused function: under its conditions (a
`Contraction` `C` for `realCoeffs_f64 c`, finite coefficients and starting state, inputs at most
`M ≥ 0`, no fused step overflows, `Sb ≥ 0` with `cInf·(R + Ê) ≤ Sb`), `process_fma_f64` never
fails, each sample it writes is within `outGain·cInf·Ê + Ly` of the exact filter's output and
each value of the state it leaves within `cInf·Ê` of the exact final state's, with
`Ê = stateErrBound_f64 c C M Sb` and `Ly = stepErrOut_f64 c M Sb`. -/
theorem process_fma_f64_block_error (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M Sb : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hno : NoOverflowFma_f64 c state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M) (hSb : 0 ≤ Sb)
    (hS : C.cInf * (exactStateBound (realCoeffs_f64 c) C M (realState_f64 state) +
      stateErrBound_f64 c C M Sb) ≤ Sb) :
    let Ê := stateErrBound_f64 c C M Sb
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    process_fma_f64 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f64 y - e| ≤ outGain (realCoeffs_f64 c) * C.cInf * Ê +
          stepErrOut_f64 c M Sb) r.2.val F.2 ∧
        |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê F
  have hLs := stepErrState_nonneg (realCoeffs_f64 c) (u := unitRoundoff_f64)
    (η := underflowErr_f64) (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hM0 hSb
  have h := block_error_real (realCoeffs_f64 c) C M Sb _ _ hM0 hLs (realState_f64 state) hS
    (buf.val.map real_f64) _ _ (by simpa using hM)
    (filt_fma_f64_withinLocalErr c hc Sb M buf.val state hs1 hs2 hno)
  apply WP.spec_mono (process_fma_f64_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **No fused overflow, from the inputs alone**, under the conditions of the unfused
`noOverflow_f64_of_inputs`, word for word. -/
theorem noOverflowFma_f64_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (hc : CoeffsFinite_f64 c) (Sb M R Ê : ℝ)
    (hR : C.ρ * R + C.K * inputGain (realCoeffs_f64 c) * M ≤ R)
    (hE : C.ρ * Ê + C.K * stepErrState_f64 c M Sb ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb) (hcap : stepValueBound_f64 c M Sb ≤ maxFinite_f64) :
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
    obtain ⟨hdy, hdt⟩ := svfStep_fma_f64_localErr c s x Sb M hc hs1 hs2 hstep hS1 hS2 hX
    obtain ⟨-, hr', he'⟩ := block_step _ C (t := realState_f64 (svfStep_fma_f64 c s x).2) hR hE
      hX hr he hdy hdt
    exact ⟨hstep, ih _ _ hstep.next_s1_isFinite hstep.next_s2_isFinite
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) hr' he'⟩

/-- **Whole-block error of the fused Rust SVF `process_fma_f64`, with conditions on the inputs
only.** The statement of `process_f64_block_error_of_inputs`, word for word, for the fused
function: if the coefficients, `state` and every sample are finite, every sample's real value is
at most `M ≥ 0` in size, `0 ≤ Sb` with `cInf·(R + Ê) ≤ Sb`, and `stepValueBound_f64 c M Sb` is at
most the largest finite binary64 value, then no fused step overflows, `process_fma_f64` never
fails, and the conclusion of `process_fma_f64_block_error` holds. -/
theorem process_fma_f64_block_error_of_inputs (c : CoeffsF64) (C : Contraction (realCoeffs_f64 c))
    (state : StateF64) (buf : Slice Float) (M Sb : ℝ) (hc : CoeffsFinite_f64 c)
    (hs1 : state.s1.isFinite = true) (hs2 : state.s2.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f64 x| ≤ M) (hM0 : 0 ≤ M) (hSb : 0 ≤ Sb)
    (hS : C.cInf * (exactStateBound (realCoeffs_f64 c) C M (realState_f64 state) +
      stateErrBound_f64 c C M Sb) ≤ Sb)
    (hcap : stepValueBound_f64 c M Sb ≤ maxFinite_f64) :
    let Ê := stateErrBound_f64 c C M Sb
    let F := filt_real (realCoeffs_f64 c) (realState_f64 state) (buf.val.map real_f64)
    NoOverflowFma_f64 c state buf.val ∧
      process_fma_f64 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f64 y - e| ≤ outGain (realCoeffs_f64 c) * C.cInf * Ê +
            stepErrOut_f64 c M Sb) r.2.val F.2 ∧
          |real_f64 r.1.s1 - F.1.1| ≤ C.cInf * Ê ∧ |real_f64 r.1.s2 - F.1.2| ≤ C.cInf * Ê ⦄ := by
  intro Ê F
  have hLs := stepErrState_nonneg (realCoeffs_f64 c) (u := unitRoundoff_f64)
    (η := underflowErr_f64) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le
    hM0 hSb
  obtain ⟨hR, hE, hr, he⟩ := block_constants (realCoeffs_f64 c) C M _ (realState_f64 state) hM0
    hLs
  have hno := noOverflowFma_f64_of_inputs c C hc Sb M _ _ hR hE hS hcap buf.val state
    (realState_f64 state) hs1 hs2 hin hr he
  exact ⟨hno, process_fma_f64_block_error c C state buf M Sb hc hs1 hs2 hno hM0
    (fun x hx => (hin x hx).2) hSb hS⟩

end conjure_dsp_lib.svf

end
