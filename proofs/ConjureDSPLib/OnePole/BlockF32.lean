module

public import ConjureDSPLib.OnePole.BridgeF32
public import ConjureDSPLib.OnePole.Block

/-!
# The one-pole filter in f32 over a whole block

`process_f32_block_error`: when the Rust `process_f32` filters a block with a stable
coefficient and no step overflows, every output sample and the final state are within a fixed
distance `E` of the exact real-number filter, for a block of any length. `E` depends only on the
input bound `M`, the coefficient, the starting state and binary32's rounding constants.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.one_pole

/-- The exact real value of a finite binary32 number (through FloatLib's model). -/
noncomputable abbrev realF32 (v : Float32) : ℝ := toReal (ofFloat32 v : Binary32)

/-- No step overflows: running the filter from state `s` over the inputs, every input, every
product `a * state` and every new output is finite. -/
def NoOverflowF32 (a : Float32) : Float32 → List Float32 → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (a * s).isFinite = true ∧ (x + a * s).isFinite = true ∧
      NoOverflowF32 a (x + a * s) xs

/-- Without overflow, each step of `filt_f32` is within the per-step error `step_f32_error`. -/
theorem filt_f32_withinStepErr (a : Float32) (ha : a.isFinite = true) :
    ∀ (xs : List Float32) (s : Float32), s.isFinite = true → NoOverflowF32 a s xs →
      WithinStepErr (realF32 a) (Model.unitRoundoffAt FloatFormat.binary32)
        (Model.underflowErrorAt FloatFormat.binary32) (realF32 s) (xs.map realF32)
        (realF32 (filt_f32 a s xs).1) ((filt_f32 a s xs).2.map realF32) := by
  intro xs
  induction xs with
  | nil => intro s _ _; simp [filt_f32, WithinStepErr]
  | cons x xs ih =>
    intro s hs hno
    obtain ⟨hx, hp, hr, hrest⟩ := hno
    simp only [filt_f32, List.map_cons, WithinStepErr]
    exact ⟨step_f32_error a s x ha hs hx hp hr, ih (x + a * s) hr hrest⟩

/-- **Whole-block error of the f32 filter.** Let `A`, `S` and the inputs be the exact values of
`a`, the starting state and the samples, with every input at most `M` in size. If no step
overflows and `|A| + |A|·u·(2 + u) < 1` (`u = 2⁻²⁴`), then every output of `filt_f32` and its
final state are within `E` of the exact real-number filter `filt_real`, where
`B = |S| + M / (1 - |A|)` and
`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`. -/
theorem filt_f32_block_error (a s : Float32) (xs : List Float32) (M : ℝ)
    (ha : a.isFinite = true) (hs : s.isFinite = true) (hno : NoOverflowF32 a s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |realF32 x| ≤ M)
    (hstab : |realF32 a| + |realF32 a| * Model.unitRoundoffAt FloatFormat.binary32 *
      (2 + Model.unitRoundoffAt FloatFormat.binary32) < 1) :
    let A := realF32 a
    let S := realF32 s
    let u := Model.unitRoundoffAt FloatFormat.binary32
    let η := Model.underflowErrorAt FloatFormat.binary32
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    List.Forall₂ (fun c e => |realF32 c - e| ≤ E) (filt_f32 a s xs).2
        (filt_real A S (xs.map realF32)).2 ∧
      |realF32 (filt_f32 a s xs).1 - (filt_real A S (xs.map realF32)).1| ≤ E := by
  intro A S u η B E
  have h := block_error_real A u η M S (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hM0 hstab (xs.map realF32) _ _
    (by simpa using hM) (filt_f32_withinStepErr a ha xs s hs hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust `process_f32`.** Under the conditions of
`filt_f32_block_error`, `process_f32` never fails, and every sample it writes into the buffer,
and the state it leaves, are within `E` of the exact real-number filter. -/
theorem process_f32_block_error (a state : Float32) (buf : Slice Float32) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true) (hno : NoOverflowF32 a state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |realF32 x| ≤ M)
    (hstab : |realF32 a| + |realF32 a| * Model.unitRoundoffAt FloatFormat.binary32 *
      (2 + Model.unitRoundoffAt FloatFormat.binary32) < 1) :
    let A := realF32 a
    let S := realF32 state
    let u := Model.unitRoundoffAt FloatFormat.binary32
    let η := Model.underflowErrorAt FloatFormat.binary32
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    process_f32 a state buf ⦃ fun r =>
      List.Forall₂ (fun c e => |realF32 c - e| ≤ E) r.2.val
          (filt_real A S (buf.val.map realF32)).2 ∧
        |realF32 r.1 - (filt_real A S (buf.val.map realF32)).1| ≤ E ⦄ := by
  intro A S u η B E
  have hblock := filt_f32_block_error a state buf.val M ha hs hno hM0 hM hstab
  apply WP.spec_mono (process_f32_spec a state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

end conjure_dsp_lib.one_pole

end
