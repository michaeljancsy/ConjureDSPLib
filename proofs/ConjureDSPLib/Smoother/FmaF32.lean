module

public import ConjureDSPLib.Smoother.BlockF32
public import ConjureDSPLib.FmaFacts

/-!
# The fused smoother in f32

About `step_fma_f32`, `process_fma_f32`, `step_coeff_fma_f32` and `process_coeff_fma_f32` from
`src/smoother.rs` (the `std` feature), as Aeneas translated them. Rust's
`c.mul_add(x - state, state)` becomes Lean's `c.fma (x - state) state`: the difference rounded
once, then `c·(x - state) + state` rounded once. This file proves:

1. `step_fma_f32_eq`, `step_coeff_fma_f32_eq`: one Rust step is exactly that, and never fails;
   `process_fma_f32_spec`, `process_coeff_fma_f32_spec`: the block loops never fail and give
   exactly `filt_fma_f32` (with `c = 1 - a` computed once in binary32 for `process_fma_f32`).
2. `step_fma_f32_error`: one fused step is within `stepErr`, the per-step bound of the unfused
   step (`step_f32_error`), so the whole-block theorems of `Block.lean` apply unchanged.
3. The whole-block and settling theorems of `BlockF32.lean` for the fused functions, with the
   same `E` (`errBound`) and the same conditions (`NoOverflowFma_f32` in place of
   `NoOverflow_f32` where no-overflow is assumed): `process_fma_f32_block_error`,
   `process_fma_f32_block_error_of_inputs`, `process_fma_f32_settle_of_inputs` and their
   `process_coeff_fma_f32` versions. The smoother table rows of `BlockF32.lean` are about `E`,
   `outBound` and the stability condition alone, so they hold for the fused functions too.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.smoother

/-- One fused Rust smoother step is `(1 - a).fma (target - state) state` in binary32, and cannot
fail. -/
theorem step_fma_f32_eq (a state target : Float32) :
    step_fma_f32 a state target = ok ((1 - a).fma (target - state) state) := rfl

/-- One fused Rust step of `step_coeff_fma_f32` is `c.fma (target - state) state` in binary32,
and cannot fail. -/
theorem step_coeff_fma_f32_eq (c state target : Float32) :
    step_coeff_fma_f32 c state target = ok (c.fma (target - state) state) := rfl

/-- `step_fma_f32 a` is `step_coeff_fma_f32` with the coefficient `1 - a` computed in
binary32. -/
theorem step_fma_f32_eq_step_coeff_fma (a state target : Float32) :
    step_fma_f32 a state target = step_coeff_fma_f32 (1 - a) state target := rfl

/-- The fused smoother on binary32 numbers with coefficient `c`: run it over a list of input
samples from state `s`, returning the final state and the list of outputs. -/
def filt_fma_f32 (c : Float32) : Float32 → List Float32 → Float32 × List Float32
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := c.fma (x - s) s
    let r := filt_fma_f32 c y xs
    (r.1, y :: r.2)

/-- One loop iteration on plain lists, as `filt_f32_set_step`. -/
theorem filt_fma_f32_set_step (c s : Float32) (l : List Float32) (j : ℕ) (hj : j < l.length) :
    (l.set j (c.fma (l[j] - s) s)).take (j + 1) ++
        (filt_fma_f32 c (c.fma (l[j] - s) s)
          ((l.set j (c.fma (l[j] - s) s)).drop (j + 1))).2 =
      l.take j ++ (filt_fma_f32 c s (l.drop j)).2 ∧
    (filt_fma_f32 c (c.fma (l[j] - s) s)
        ((l.set j (c.fma (l[j] - s) s)).drop (j + 1))).1 =
      (filt_fma_f32 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (c.fma (l[j] - s) s)).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (c.fma (l[j] - s) s)).take (j + 1) =
      l.take j ++ [c.fma (l[j] - s) s] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_fma_f32]

/-- The loop of `process_fma_f32`, started at position `i` with `c` already computed, leaves the
first `i` samples alone and smooths the rest. -/
theorem process_fma_f32_loop_spec (state : Float32) (buf : Slice Float32) (c : Float32)
    (i : Std.Usize) (hi : i.val ≤ buf.length) :
    process_fma_f32_loop state buf c i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_fma_f32 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_fma_f32 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_fma_f32_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_fma_f32 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_fma_f32 c state (buf.val.drop i.val)).2 ∧
      (filt_fma_f32 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_fma_f32 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_fma_f32_loop.body, lift, bind_ok]
    step*
    · subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_fma_f32_set_step c st b.val j.val hjl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_fma_f32] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The fused Rust smoother never fails, and its output samples and final state are exactly those
of `filt_fma_f32` with `c = 1 - a` computed once in binary32, sample by sample. -/
theorem process_fma_f32_spec (a state : Float32) (buf : Slice Float32) :
    process_fma_f32 a state buf ⦃ fun r =>
      r.2.val = (filt_fma_f32 (1 - a) state buf.val).2 ∧
      r.1 = (filt_fma_f32 (1 - a) state buf.val).1 ⦄ := by
  have h := process_fma_f32_loop_spec state buf (1 - a) 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.take_zero, List.drop_zero, List.nil_append] at h
  exact h

/-- The loop of `process_coeff_fma_f32`, started at position `i`, leaves the first `i` samples
alone and smooths the rest. -/
theorem process_coeff_fma_f32_loop_spec (c state : Float32) (buf : Slice Float32) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    process_coeff_fma_f32_loop c state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_fma_f32 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_fma_f32 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_coeff_fma_f32_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_fma_f32 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_fma_f32 c state (buf.val.drop i.val)).2 ∧
      (filt_fma_f32 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_fma_f32 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_coeff_fma_f32_loop.body, lift, bind_ok]
    step*
    · subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_fma_f32_set_step c st b.val j.val hjl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_fma_f32] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- `process_coeff_fma_f32` never fails, and its output samples and final state are exactly those
of `filt_fma_f32 c`, with `c` as given. -/
theorem process_coeff_fma_f32_spec (c state : Float32) (buf : Slice Float32) :
    process_coeff_fma_f32 c state buf ⦃ fun r =>
      r.2.val = (filt_fma_f32 c state buf.val).2 ∧ r.1 = (filt_fma_f32 c state buf.val).1 ⦄ := by
  have h := process_coeff_fma_f32_loop_spec c state buf 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.take_zero, List.drop_zero, List.nil_append] at h
  exact h

/-- **One fused step's error.** When `c`, `s`, `x`, the rounded difference `x - s` and the result
are finite, one fused step `c.fma (x - s) s` is within `stepErr (1 - C) u η S X` of the exact
step `S + C·(X - S)`: the bound of the unfused step (`step_f32_error`). -/
theorem step_fma_f32_error (c s x : Float32)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hx : x.isFinite = true)
    (hd : (x - s).isFinite = true) (hr : (c.fma (x - s) s).isFinite = true) :
    |real_f32 (c.fma (x - s) s) - (real_f32 s + real_f32 c * (real_f32 x - real_f32 s))| ≤
      stepErr (1 - real_f32 c) unitRoundoff_f32 underflowErr_f32 (real_f32 s) (real_f32 x) := by
  have h1 := abs_real_sub_sub_le_f32 x s hx hs hd
  have h2 := abs_real_fma_sub_le_f32 c (x - s) s hc hd hs hr
  unfold stepErr prodErr diffErr
  rw [sub_sub_cancel]
  set C := real_f32 c
  set S := real_f32 s
  set X := real_f32 x
  set D := real_f32 (x - s)
  set Y := real_f32 (c.fma (x - s) s)
  set u := unitRoundoff_f32
  set η := underflowErr_f32
  have hu : 0 ≤ u := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ η := (Model.underflowErrorAt_pos _).le
  -- The difference's rounding, carried through the exact product.
  have he : |C * D - C * (X - S)| ≤ |C| * (u * |X - S| + η) := by
    rw [← mul_sub, abs_mul]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have hCD : |C * D + S| ≤ |S + C * (X - S)| + |C| * (u * |X - S| + η) := by
    calc |C * D + S| = |(S + C * (X - S)) + (C * D - C * (X - S))| := by ring_nf
      _ ≤ |S + C * (X - S)| + |C * D - C * (X - S)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hD0 : 0 ≤ u * |C| * (|X - S| + (u * |X - S| + η)) + η := by positivity
  have hfused : |Y - (S + C * (X - S))| ≤
      u * (|S + C * (X - S)| + |C| * (u * |X - S| + η)) + η + |C| * (u * |X - S| + η) := by
    calc |Y - (S + C * (X - S))| = |(Y - (C * D + S)) + (C * D - C * (X - S))| := by ring_nf
      _ ≤ |Y - (C * D + S)| + |C * D - C * (X - S)| := abs_add_le _ _
      _ ≤ (u * |C * D + S| + η) + |C| * (u * |X - S| + η) := add_le_add h2 he
      _ ≤ _ := by have := mul_le_mul_of_nonneg_left hCD hu; linarith
  have hmono := mul_le_mul_of_nonneg_left (le_refl (|S + C * (X - S)|)) hu
  nlinarith [mul_nonneg hu hD0]

/-- No fused step overflows: running the fused smoother with coefficient `c` from state `s` over
the inputs, every input, every difference `x - state` and every new output is finite. -/
def NoOverflowFma_f32 (c : Float32) : Float32 → List Float32 → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (x - s).isFinite = true ∧ (c.fma (x - s) s).isFinite = true ∧
      NoOverflowFma_f32 c (c.fma (x - s) s) xs

/-- Without overflow, each step of `filt_fma_f32` is within `stepErr`. -/
theorem filt_fma_f32_withinStepErr (c : Float32) (hc : c.isFinite = true) :
    ∀ (xs : List Float32) (s : Float32), s.isFinite = true → NoOverflowFma_f32 c s xs →
      WithinStepErr (1 - real_f32 c) unitRoundoff_f32 underflowErr_f32 (real_f32 s)
        (xs.map real_f32) (real_f32 (filt_fma_f32 c s xs).1)
        ((filt_fma_f32 c s xs).2.map real_f32) := by
  intro xs
  induction xs with
  | nil => intro s _ _; simp [filt_fma_f32, WithinStepErr]
  | cons x xs ih =>
    intro s hs hno
    obtain ⟨hx, hd, hr, hrest⟩ := hno
    simp only [filt_fma_f32, List.map_cons, WithinStepErr]
    refine ⟨?_, ih _ hr hrest⟩
    rw [sub_sub_cancel]
    exact step_fma_f32_error c s x hc hs hx hd hr

/-- The fused smoother over a list, as `filt_f32_block_error`: with `C` the value of `c` and
`A = 1 - C`, if `c` and the start are finite, no fused step overflows, every input is at most
`M ≥ 0` in size and `|A| + errGrowth A u < 1`, then every output of `filt_fma_f32 c` and its final
state are within `E = errBound A u η M S` of the exact smoother `filt_real A`. -/
theorem filt_fma_f32_block_error (c s : Float32) (xs : List Float32) (M : ℝ)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hno : NoOverflowFma_f32 c s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f32 x| ≤ M)
    (hstab : |1 - real_f32 c| + errGrowth (1 - real_f32 c) unitRoundoff_f32 < 1) :
    let A := 1 - real_f32 c
    let E := errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 s)
    List.Forall₂ (fun y e => |real_f32 y - e| ≤ E) (filt_fma_f32 c s xs).2
        (filt_real A (real_f32 s) (xs.map real_f32)).2 ∧
      |real_f32 (filt_fma_f32 c s xs).1 - (filt_real A (real_f32 s) (xs.map real_f32)).1| ≤ E := by
  intro A E
  have h := block_error_real A unitRoundoff_f32 underflowErr_f32 M (real_f32 s)
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab (xs.map real_f32)
    _ _ (by simpa using hM) (filt_fma_f32_withinStepErr c hc xs s hs hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the fused Rust `process_fma_f32`.** The statement of
`process_f32_block_error`, word for word, for the fused function, with `NoOverflowFma_f32` in
place of `NoOverflow_f32`: with `A = 1 - C`, `C` the value of `1 - a` computed in binary32, it
never fails, and every sample it writes and the state it leaves are within
`E = errBound A u η M S` of the exact smoother `filt_real A`. -/
theorem process_fma_f32_block_error (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (hc : (1 - a).isFinite = true) (hs : state.isFinite = true)
    (hno : NoOverflowFma_f32 (1 - a) state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f32 x| ≤ M)
    (hstab : |1 - real_f32 (1 - a)| + errGrowth (1 - real_f32 (1 - a)) unitRoundoff_f32 < 1) :
    let A := 1 - real_f32 (1 - a)
    let E := errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    process_fma_f32 a state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f32 y - e| ≤ E) r.2.val
          (filt_real A (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real A (real_f32 state) (buf.val.map real_f32)).1| ≤ E ⦄ := by
  intro A E
  have hblock := filt_fma_f32_block_error (1 - a) state buf.val M hc hs hno hM0 hM hstab
  apply WP.spec_mono (process_fma_f32_spec a state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **Whole-block error of the fused Rust `process_coeff_fma_f32`.** The statement of
`process_coeff_f32_block_error`, word for word, for the fused function, with `NoOverflowFma_f32`
in place of `NoOverflow_f32`. -/
theorem process_coeff_fma_f32_block_error (c state : Float32) (buf : Slice Float32) (M : ℝ)
    (hc : c.isFinite = true) (hs : state.isFinite = true)
    (hno : NoOverflowFma_f32 c state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f32 x| ≤ M)
    (hstab : |1 - real_f32 c| + errGrowth (1 - real_f32 c) unitRoundoff_f32 < 1) :
    let A := 1 - real_f32 c
    let E := errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    process_coeff_fma_f32 c state buf ⦃ fun r =>
      List.Forall₂ (fun y e => |real_f32 y - e| ≤ E) r.2.val
          (filt_real A (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real A (real_f32 state) (buf.val.map real_f32)).1| ≤ E ⦄ := by
  intro A E
  have hblock := filt_fma_f32_block_error c state buf.val M hc hs hno hM0 hM hstab
  apply WP.spec_mono (process_coeff_fma_f32_spec c state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

/-- **No fused overflow, from the inputs alone**, under the conditions of the unfused
`noOverflow_f32_of_inputs`, word for word. -/
theorem noOverflowFma_f32_of_inputs (c : Float32) (hc : c.isFinite = true) (M B E : ℝ)
    (hB : |real_f32 c| * M + |1 - real_f32 c| * B ≤ B)
    (hE : stepBound (1 - real_f32 c) unitRoundoff_f32 underflowErr_f32 M (B + E) +
        |1 - real_f32 c| * E ≤ E)
    (hcap : (1 + unitRoundoff_f32) * (M + (B + E)) + underflowErr_f32 + (B + E) +
        (1 + unitRoundoff_f32) * |real_f32 c| *
          ((1 + unitRoundoff_f32) * (M + (B + E)) + underflowErr_f32) + underflowErr_f32 ≤
      maxFinite_f32) :
    ∀ (xs : List Float32) (s : Float32) (r : ℝ), s.isFinite = true →
      (∀ x ∈ xs, x.isFinite = true ∧ |real_f32 x| ≤ M) →
      |real_f32 s - r| ≤ E → |r| ≤ B → NoOverflowFma_f32 c s xs := by
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
    have hCD : |C * real_f32 (x - s)| ≤ |C| * G := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left hD hC
    -- The fused result: its exact value `C·D + S` is within the cap.
    have hr' : (c.fma (x - s) s).isFinite = true := by
      refine isFinite_fma_f32 c (x - s) s hc hd hs ?_
      have : |C| * G ≤ (1 + u) * |C| * G := by nlinarith
      calc |C * real_f32 (x - s) + real_f32 s|
          ≤ |C * real_f32 (x - s)| + |real_f32 s| := abs_add_le _ _
        _ ≤ |C| * G + W := add_le_add hCD hS
        _ ≤ maxFinite_f32 := by linarith
    have hstep : |real_f32 (c.fma (x - s) s) -
        (real_f32 s + (1 - (1 - C)) * (real_f32 x - real_f32 s))| ≤
        stepErr (1 - C) u η (real_f32 s) (real_f32 x) := by
      rw [sub_sub_cancel]; exact step_fma_f32_error c s x hc hs hx hd hr'
    obtain ⟨herr, hrB⟩ := block_step (1 - C) u η M B E (real_f32 x) (real_f32 s) r
      (real_f32 (c.fma (x - s) s)) hu hη hB' hE hxM hsr hr hstep
    exact ⟨hx, hd, hr', ih (c.fma (x - s) s) _ hr'
      (fun z hz => hin z (List.mem_cons_of_mem _ hz)) herr hrB⟩

/-- **Whole-block error of the fused `process_fma_f32`, with conditions on the inputs only.** The
statement of `process_f32_block_error_of_inputs`, word for word (the same conditions and the same
`E`), for the fused function. -/
theorem process_fma_f32_block_error_of_inputs (a state : Float32) (buf : Slice Float32) (M : ℝ)
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
    NoOverflowFma_f32 (1 - a) state buf.val ∧
      process_fma_f32 a state buf ⦃ fun r =>
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
  have hno := noOverflowFma_f32_of_inputs (1 - a) hc M _ _ hB' hE hcap buf.val state
    (real_f32 state) hs hin (by simpa using hE0) hSB
  exact ⟨hno, process_fma_f32_block_error a state buf M hc hs hno hM0
    (fun x hx => (hin x hx).2) hstab⟩

/-- **Whole-block error of the fused `process_coeff_fma_f32`, with conditions on the inputs
only.** The statement of `process_coeff_f32_block_error_of_inputs`, word for word, for the fused
function. -/
theorem process_coeff_fma_f32_block_error_of_inputs (c state : Float32) (buf : Slice Float32)
    (M : ℝ)
    (hc : c.isFinite = true) (hs : state.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f32 x| ≤ M) (hM0 : 0 ≤ M)
    (hstab : |1 - real_f32 c| + errGrowth (1 - real_f32 c) unitRoundoff_f32 < 1)
    (hcap :
      let A := 1 - real_f32 c
      let W := outBound A M (real_f32 state) +
        errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
      let G := (1 + unitRoundoff_f32) * (M + W) + underflowErr_f32
      G + W + (1 + unitRoundoff_f32) * |real_f32 c| * G + underflowErr_f32 ≤
        maxFinite_f32) :
    let A := 1 - real_f32 c
    let E := errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    NoOverflowFma_f32 c state buf.val ∧
      process_coeff_fma_f32 c state buf ⦃ fun r =>
        List.Forall₂ (fun y e => |real_f32 y - e| ≤ E) r.2.val
          (filt_real A (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real A (real_f32 state) (buf.val.map real_f32)).1| ≤ E ⦄ := by
  intro A E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants A unitRoundoff_f32 underflowErr_f32 M
    (real_f32 state) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab
  have hB' : |real_f32 c| * M + |1 - real_f32 c| * outBound A M (real_f32 state) ≤
      outBound A M (real_f32 state) := by
    have := hB; simp only [A, sub_sub_cancel] at this; exact this
  have hno := noOverflowFma_f32_of_inputs c hc M _ _ hB' hE hcap buf.val state (real_f32 state)
    hs hin (by simpa using hE0) hSB
  exact ⟨hno, process_coeff_fma_f32_block_error c state buf M hc hs hno hM0
    (fun x hx => (hin x hx).2) hstab⟩

/-- **Settling on a steady input, fused `process_fma_f32`.** The statement of
`process_f32_settle_of_inputs`, word for word, for the fused function: under its conditions, the
state left after a block of `n` copies of `x` is within `|A|^n·|S - X| + E` of `X`. -/
theorem process_fma_f32_settle_of_inputs (a state x : Float32) (buf : Slice Float32) (M : ℝ)
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
    process_fma_f32 a state buf ⦃ fun r =>
      |real_f32 r.1 - real_f32 x| ≤ |A| ^ buf.val.length * |real_f32 state - real_f32 x| +
        errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state) ⦄ := by
  intro A
  have hin : ∀ y ∈ buf.val, y.isFinite = true ∧ |real_f32 y| ≤ M := by
    intro y hy; rw [hbuf y hy]; exact ⟨hx, hXM⟩
  obtain ⟨hno, -⟩ := process_fma_f32_block_error_of_inputs a state buf M ha ha1 hs hin
    ((abs_nonneg _).trans hXM) hstab hcap
  have hc : (1 - a).isFinite = true := isFinite_one_sub_f32_of_abs_le_one a ha ha1
  have hrep : buf.val = List.replicate buf.val.length x := List.eq_replicate_iff.mpr ⟨rfl, hbuf⟩
  have hw := filt_fma_f32_withinStepErr (1 - a) hc buf.val state hs hno
  rw [hrep, List.map_replicate] at hw
  have h := settle_real A unitRoundoff_f32 underflowErr_f32 M (real_f32 x) (real_f32 state)
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hXM hstab _ _ _ hw
  apply WP.spec_mono (process_fma_f32_spec a state buf)
  rintro r ⟨-, hst⟩
  rw [hst]
  rw [← hrep] at h
  exact h

/-- **Settling on a steady input, fused `process_coeff_fma_f32`.** The statement of
`process_coeff_f32_settle_of_inputs`, word for word, for the fused function. -/
theorem process_coeff_fma_f32_settle_of_inputs (c state x : Float32) (buf : Slice Float32) (M : ℝ)
    (hc : c.isFinite = true) (hs : state.isFinite = true)
    (hx : x.isFinite = true) (hbuf : ∀ y ∈ buf.val, y = x) (hXM : |real_f32 x| ≤ M)
    (hstab : |1 - real_f32 c| + errGrowth (1 - real_f32 c) unitRoundoff_f32 < 1)
    (hcap :
      let A := 1 - real_f32 c
      let W := outBound A M (real_f32 state) +
        errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
      let G := (1 + unitRoundoff_f32) * (M + W) + underflowErr_f32
      G + W + (1 + unitRoundoff_f32) * |real_f32 c| * G + underflowErr_f32 ≤
        maxFinite_f32) :
    let A := 1 - real_f32 c
    process_coeff_fma_f32 c state buf ⦃ fun r =>
      |real_f32 r.1 - real_f32 x| ≤ |A| ^ buf.val.length * |real_f32 state - real_f32 x| +
        errBound A unitRoundoff_f32 underflowErr_f32 M (real_f32 state) ⦄ := by
  intro A
  have hin : ∀ y ∈ buf.val, y.isFinite = true ∧ |real_f32 y| ≤ M := by
    intro y hy; rw [hbuf y hy]; exact ⟨hx, hXM⟩
  obtain ⟨hno, -⟩ := process_coeff_fma_f32_block_error_of_inputs c state buf M hc hs hin
    ((abs_nonneg _).trans hXM) hstab hcap
  have hrep : buf.val = List.replicate buf.val.length x := List.eq_replicate_iff.mpr ⟨rfl, hbuf⟩
  have hw := filt_fma_f32_withinStepErr c hc buf.val state hs hno
  rw [hrep, List.map_replicate] at hw
  have h := settle_real A unitRoundoff_f32 underflowErr_f32 M (real_f32 x) (real_f32 state)
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hXM hstab _ _ _ hw
  apply WP.spec_mono (process_coeff_fma_f32_spec c state buf)
  rintro r ⟨-, hst⟩
  rw [hst]
  rw [← hrep] at h
  exact h

end conjure_dsp_lib.smoother

end
