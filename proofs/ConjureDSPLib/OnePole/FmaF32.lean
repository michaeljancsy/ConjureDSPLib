module

public import ConjureDSPLib.OnePole.BlockF32
public import ConjureDSPLib.FmaFacts

/-!
# The fused one-pole filter in f32

About `step_fma_f32` and `process_fma_f32` from `src/one_pole.rs` (the `std` feature), as Aeneas
translated them. Rust's `a.mul_add(state, x)` becomes Lean's `a.fma state x`: `a·state + x`
rounded once. This file proves:

1. `step_fma_f32_eq`: one Rust step is exactly `a.fma state x`, and never fails.
2. `process_fma_f32_spec`: the Rust block loop never fails and produces exactly the outputs and
   final state of `filt_fma_f32`, the fused filter computed one sample at a time.
3. `step_fma_f32_error`: one fused step is within `stepErr`, the per-step bound of the unfused step
   (`step_f32_error`), so every whole-block theorem of `Block.lean` applies unchanged.
4. `process_fma_f32_block_error_of_inputs`: the whole-block bound of
   `process_f32_block_error_of_inputs`, with the same `E` (`errBound`) and the same conditions, for
   the fused Rust function. The table rows of `BlockF32.lean` (`table_row_le_of_abs_le_*_f32`) are
   about `outBound` and `errBound` alone, so they hold for it too.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.one_pole

/-- One fused Rust step is `a.fma state x` (`a·state + x` rounded once), and cannot fail. -/
theorem step_fma_f32_eq (a state x : Float32) :
    step_fma_f32 a state x = ok (a.fma state x) := rfl

/-- The fused filter on binary32 numbers: run it over a list of input samples from state `s`,
returning the final state and the list of outputs. -/
def filt_fma_f32 (a : Float32) : Float32 → List Float32 → Float32 × List Float32
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := a.fma s x
    let r := filt_fma_f32 a y xs
    (r.1, y :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_fma_f32_set_step (a s : Float32) (l : List Float32) (j : ℕ) (hj : j < l.length) :
    (l.set j (a.fma s l[j])).take (j + 1) ++
        (filt_fma_f32 a (a.fma s l[j]) ((l.set j (a.fma s l[j])).drop (j + 1))).2 =
      l.take j ++ (filt_fma_f32 a s (l.drop j)).2 ∧
    (filt_fma_f32 a (a.fma s l[j]) ((l.set j (a.fma s l[j])).drop (j + 1))).1 =
      (filt_fma_f32 a s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (a.fma s l[j])).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (a.fma s l[j])).take (j + 1) = l.take j ++ [a.fma s l[j]] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_fma_f32]

/-- The loop, started at position `i`, leaves the first `i` samples alone and filters the rest. -/
theorem process_fma_f32_loop_spec (a state : Float32) (buf : Slice Float32) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    process_fma_f32_loop a state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_fma_f32 a state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_fma_f32 a state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_fma_f32_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_fma_f32 a x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_fma_f32 a state (buf.val.drop i.val)).2 ∧
      (filt_fma_f32 a x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_fma_f32 a state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_fma_f32_loop.body, step_fma_f32_eq]
    step*
    · subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_fma_f32_set_step a st b.val j.val hjl
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

/-- The fused Rust block-processing function never fails, and its output samples and final
state are exactly those of `filt_fma_f32`, sample by sample. -/
theorem process_fma_f32_spec (a state : Float32) (buf : Slice Float32) :
    process_fma_f32 a state buf ⦃ fun r =>
      r.2.val = (filt_fma_f32 a state buf.val).2 ∧ r.1 = (filt_fma_f32 a state buf.val).1 ⦄ := by
  simpa using process_fma_f32_loop_spec a state buf 0#usize (by simp)

/-- **One fused step's error.** When `a`, `y`, `x` and the result are finite, one fused step
differs from exact real arithmetic by at most `u·|x + a·y| + η`, which is at most `stepErr`, the
bound of the unfused step (`step_f32_error`). -/
theorem step_fma_f32_error (a y x : Float32)
    (ha : a.isFinite = true) (hy : y.isFinite = true) (hx : x.isFinite = true)
    (hr : (a.fma y x).isFinite = true) :
    |real_f32 (a.fma y x) - (real_f32 x + real_f32 a * real_f32 y)| ≤
      stepErr (real_f32 a) unitRoundoff_f32 underflowErr_f32 (real_f32 y) (real_f32 x) := by
  have h := abs_real_fma_sub_le_f32 a y x ha hy hx hr
  have hu : 0 ≤ unitRoundoff_f32 := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ underflowErr_f32 := (Model.underflowErrorAt_pos _).le
  have e : real_f32 x + real_f32 a * real_f32 y = real_f32 a * real_f32 y + real_f32 x := by ring
  rw [e]
  unfold stepErr
  rw [add_comm (real_f32 x)]
  have : 0 ≤ (|real_f32 a * real_f32 y| * unitRoundoff_f32 + underflowErr_f32) *
      (1 + unitRoundoff_f32) := by positivity
  nlinarith [abs_nonneg (real_f32 a * real_f32 y + real_f32 x)]

/-- No fused step overflows: running the fused filter from state `s` over the inputs, every
input and every new output is finite. -/
def NoOverflowFma_f32 (a : Float32) : Float32 → List Float32 → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (a.fma s x).isFinite = true ∧ NoOverflowFma_f32 a (a.fma s x) xs

/-- Without overflow, each step of `filt_fma_f32` is within `stepErr`. -/
theorem filt_fma_f32_withinStepErr (a : Float32) (ha : a.isFinite = true) :
    ∀ (xs : List Float32) (s : Float32), s.isFinite = true → NoOverflowFma_f32 a s xs →
      WithinStepErr (real_f32 a) unitRoundoff_f32 underflowErr_f32 (real_f32 s)
        (xs.map real_f32) (real_f32 (filt_fma_f32 a s xs).1)
        ((filt_fma_f32 a s xs).2.map real_f32) := by
  intro xs
  induction xs with
  | nil => intro s _ _; simp [filt_fma_f32, WithinStepErr]
  | cons x xs ih =>
    intro s hs hno
    obtain ⟨hx, hr, hrest⟩ := hno
    simp only [filt_fma_f32, List.map_cons, WithinStepErr]
    exact ⟨step_fma_f32_error a s x ha hs hx hr, ih (a.fma s x) hr hrest⟩

/-- **Whole-block error of the fused Rust `process_fma_f32`.** The bound of
`process_f32_block_error`, with the same `B` (`outBound`), `E` (`errBound`) and conditions: let
`A`, `S` and the inputs be the exact values of `a`, the starting state and the samples, with every
input at most `M` in size. If no fused step overflows and `|A| + |A|·u·(2 + u) < 1`, then
`process_fma_f32` never fails, and every sample it writes and the state it leaves are within `E`
of the exact real-number filter `filt_real`. -/
theorem process_fma_f32_block_error (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true)
    (hno : NoOverflowFma_f32 a state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f32 x| ≤ M)
    (hstab : |real_f32 a| + |real_f32 a| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1) :
    let E := errBound (real_f32 a) unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    process_fma_f32 a state buf ⦃ fun r =>
      List.Forall₂ (fun c e => |real_f32 c - e| ≤ E) r.2.val
          (filt_real (real_f32 a) (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real (real_f32 a) (real_f32 state) (buf.val.map real_f32)).1|
          ≤ E ⦄ := by
  intro E
  have h := block_error_real (real_f32 a) unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab
    (buf.val.map real_f32) _ _ (by simpa using hM)
    (filt_fma_f32_withinStepErr a ha buf.val state hs hno)
  apply WP.spec_mono (process_fma_f32_spec a state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **No fused overflow, from the inputs alone.** The conditions of `noOverflow_f32_of_inputs`
(the same `M`, `B`, `E` and cap) rule out overflow in the fused filter too. -/
theorem noOverflowFma_f32_of_inputs (a : Float32) (ha : a.isFinite = true) (M B E : ℝ)
    (hB : M + |real_f32 a| * B ≤ B)
    (hE : unitRoundoff_f32 * M + underflowErr_f32 * (2 + unitRoundoff_f32) +
        |real_f32 a| * unitRoundoff_f32 * (2 + unitRoundoff_f32) * (B + E) +
        |real_f32 a| * E ≤ E)
    (hA1 : |real_f32 a| ≤ 1)
    (hcap : M + (1 + unitRoundoff_f32) * (B + E) + underflowErr_f32 ≤ maxFinite_f32) :
    ∀ (xs : List Float32) (s : Float32) (r : ℝ), s.isFinite = true →
      (∀ x ∈ xs, x.isFinite = true ∧ |real_f32 x| ≤ M) →
      |real_f32 s - r| ≤ E → |r| ≤ B → NoOverflowFma_f32 a s xs := by
  have hu : 0 ≤ unitRoundoff_f32 := (Model.unitRoundoffAt_pos _).le
  have hη : 0 ≤ underflowErr_f32 := (Model.underflowErrorAt_pos _).le
  intro xs
  induction xs with
  | nil => intro _ _ _ _ _ _; trivial
  | cons x xs ih =>
    intro s r hs hin hsr hr
    obtain ⟨hx, hxM⟩ := hin x (by simp)
    have hE0 : 0 ≤ E := (abs_nonneg _).trans hsr
    have hS : |real_f32 s| ≤ B + E := by
      calc |real_f32 s| = |(real_f32 s - r) + r| := by ring_nf
        _ ≤ |real_f32 s - r| + |r| := abs_add_le _ _
        _ ≤ B + E := by linarith
    have hAS : |real_f32 a * real_f32 s| ≤ B + E := by
      rw [abs_mul]
      calc |real_f32 a| * |real_f32 s| ≤ 1 * (B + E) :=
            mul_le_mul hA1 hS (abs_nonneg _) zero_le_one
        _ = B + E := one_mul _
    have hr' : (a.fma s x).isFinite = true := by
      refine isFinite_fma_f32 a s x ha hs hx ?_
      have hB0 : 0 ≤ B := (abs_nonneg _).trans hr
      have : B + E ≤ (1 + unitRoundoff_f32) * (B + E) := by
        nlinarith [mul_nonneg hu (add_nonneg hB0 hE0)]
      calc |real_f32 a * real_f32 s + real_f32 x|
          ≤ |real_f32 a * real_f32 s| + |real_f32 x| := abs_add_le _ _
        _ ≤ (B + E) + M := add_le_add hAS hxM
        _ ≤ maxFinite_f32 := by linarith
    obtain ⟨herr, hrB⟩ := block_step (real_f32 a) _ _ M B E (real_f32 x) (real_f32 s) r
      (real_f32 (a.fma s x)) hu hB hE hxM hsr hr (step_fma_f32_error a s x ha hs hx hr')
    exact ⟨hx, hr', ih (a.fma s x) _ hr' (fun z hz => hin z (List.mem_cons_of_mem _ hz))
      herr hrB⟩

/-- **Whole-block error of the fused `process_fma_f32`, with conditions on the inputs only.**
Word for word the conditions and the bound `E` of `process_f32_block_error_of_inputs`: if `a`, the
starting state and every sample are finite, every sample is at most `M` in size,
`|A| + |A|·u·(2 + u) < 1`, and `M + (1 + u)·(B + E) + η` is at most the largest finite binary32
value, then no fused step overflows, `process_fma_f32` never fails, and every sample it writes and
the state it leaves are within `E` of the exact real-number filter. -/
theorem process_fma_f32_block_error_of_inputs (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true)
    (hin : ∀ x ∈ buf.val, x.isFinite = true ∧ |real_f32 x| ≤ M) (hM0 : 0 ≤ M)
    (hstab : |real_f32 a| + |real_f32 a| * unitRoundoff_f32 * (2 + unitRoundoff_f32) < 1)
    (hcap : M + (1 + unitRoundoff_f32) *
        (outBound (real_f32 a) M (real_f32 state) +
          errBound (real_f32 a) unitRoundoff_f32 underflowErr_f32 M (real_f32 state)) +
      underflowErr_f32 ≤ maxFinite_f32) :
    let E := errBound (real_f32 a) unitRoundoff_f32 underflowErr_f32 M (real_f32 state)
    NoOverflowFma_f32 a state buf.val ∧
      process_fma_f32 a state buf ⦃ fun r =>
        List.Forall₂ (fun c e => |real_f32 c - e| ≤ E) r.2.val
          (filt_real (real_f32 a) (real_f32 state) (buf.val.map real_f32)).2 ∧
        |real_f32 r.1 - (filt_real (real_f32 a) (real_f32 state) (buf.val.map real_f32)).1|
          ≤ E ⦄ := by
  intro E
  obtain ⟨hE0, hSB, hB, hE⟩ := block_constants (real_f32 a) unitRoundoff_f32 underflowErr_f32
    M (real_f32 state) (Model.unitRoundoffAt_pos _).le (Model.underflowErrorAt_pos _).le hM0 hstab
  have hA1 : |real_f32 a| ≤ 1 := by
    have : 0 ≤ |real_f32 a| * unitRoundoff_f32 * (2 + unitRoundoff_f32) := by
      have := (Model.unitRoundoffAt_pos FloatFormat.binary32).le
      positivity
    linarith
  have hno := noOverflowFma_f32_of_inputs a ha M _ _ hB hE hA1 hcap buf.val state
    (real_f32 state) hs hin (by simpa using hE0) hSB
  exact ⟨hno, process_fma_f32_block_error a state buf M ha hs hno hM0
    (fun x hx => (hin x hx).2) hstab⟩

end conjure_dsp_lib.one_pole

end
