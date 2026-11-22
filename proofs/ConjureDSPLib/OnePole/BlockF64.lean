module

public import ConjureDSPLib.OnePole.BridgeF64
public import ConjureDSPLib.OnePole.Block

/-!
# The one-pole filter in f64 over a whole block

`process_f64_block_error`: when the Rust `process_f64` filters a block with a stable
coefficient (with a little room for rounding) and no step overflows, every output sample and the
final state are within a fixed distance `E` of the exact real-number filter, for a block of any
length. `E` depends only on the input bound `M`, the coefficient, the starting state and
binary64's rounding constants.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open FloatLib.Floats FloatLib.Floats.ExecFloat.Binary FloatLib.Floats.Formats.BinaryInterchange

namespace conjure_dsp_lib.one_pole

/-- No step overflows: running the filter from state `s` over the inputs, every input, every
product `a * state` and every new output is finite. -/
def NoOverflow_f64 (a : Float) : Float → List Float → Prop
  | _, [] => True
  | s, x :: xs =>
    x.isFinite = true ∧ (a * s).isFinite = true ∧ (x + a * s).isFinite = true ∧
      NoOverflow_f64 a (x + a * s) xs

/-- Without overflow, each step of `filt_f64` is within the per-step error `step_f64_error`. -/
theorem filt_f64_withinStepErr (a : Float) (ha : a.isFinite = true) :
    ∀ (xs : List Float) (s : Float), s.isFinite = true → NoOverflow_f64 a s xs →
      WithinStepErr (real_f64 a) (Model.unitRoundoffAt FloatFormat.binary64)
        (Model.underflowErrorAt FloatFormat.binary64) (real_f64 s) (xs.map real_f64)
        (real_f64 (filt_f64 a s xs).1) ((filt_f64 a s xs).2.map real_f64) := by
  intro xs
  induction xs with
  | nil => intro s _ _; simp [filt_f64, WithinStepErr]
  | cons x xs ih =>
    intro s hs hno
    obtain ⟨hx, hp, hr, hrest⟩ := hno
    simp only [filt_f64, List.map_cons, WithinStepErr]
    exact ⟨step_f64_error a s x ha hs hx hp hr, ih (x + a * s) hr hrest⟩

/-- **Whole-block error of the f64 filter.** Let `A`, `S` and the inputs be the exact values of
`a`, the starting state and the samples, with every input at most `M` in size. If no step
overflows and `|A| + |A|·u·(2 + u) < 1` (`u = 2⁻⁵³`; this is `|A|·(1 + u)² < 1`, which any
`|A| ≤ 1 - 2⁻⁵¹` satisfies), then every output of `filt_f64` and its
final state are within `E` of the exact real-number filter `filt_real`, where
`B = |S| + M / (1 - |A|)` and
`E = (u·M + η·(2 + u) + |A|·u·(2 + u)·B) / (1 - |A| - |A|·u·(2 + u))`. -/
theorem filt_f64_block_error (a s : Float) (xs : List Float) (M : ℝ)
    (ha : a.isFinite = true) (hs : s.isFinite = true) (hno : NoOverflow_f64 a s xs)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ xs, |real_f64 x| ≤ M)
    (hstab : |real_f64 a| + |real_f64 a| * Model.unitRoundoffAt FloatFormat.binary64 *
      (2 + Model.unitRoundoffAt FloatFormat.binary64) < 1) :
    let A := real_f64 a
    let S := real_f64 s
    let u := Model.unitRoundoffAt FloatFormat.binary64
    let η := Model.underflowErrorAt FloatFormat.binary64
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    List.Forall₂ (fun c e => |real_f64 c - e| ≤ E) (filt_f64 a s xs).2
        (filt_real A S (xs.map real_f64)).2 ∧
      |real_f64 (filt_f64 a s xs).1 - (filt_real A S (xs.map real_f64)).1| ≤ E := by
  intro A S u η B E
  have h := block_error_real A u η M S (Model.unitRoundoffAt_pos _).le
    (Model.underflowErrorAt_pos _).le hM0 hstab (xs.map real_f64) _ _
    (by simpa using hM) (filt_f64_withinStepErr a ha xs s hs hno)
  exact ⟨List.forall₂_map_left_iff.mp h.1, h.2⟩

/-- **Whole-block error of the Rust `process_f64`.** Under the conditions of
`filt_f64_block_error`, `process_f64` never fails, and every sample it writes into the buffer,
and the state it leaves, are within `E` of the exact real-number filter. -/
theorem process_f64_block_error (a state : Float) (buf : Slice Float) (M : ℝ)
    (ha : a.isFinite = true) (hs : state.isFinite = true) (hno : NoOverflow_f64 a state buf.val)
    (hM0 : 0 ≤ M) (hM : ∀ x ∈ buf.val, |real_f64 x| ≤ M)
    (hstab : |real_f64 a| + |real_f64 a| * Model.unitRoundoffAt FloatFormat.binary64 *
      (2 + Model.unitRoundoffAt FloatFormat.binary64) < 1) :
    let A := real_f64 a
    let S := real_f64 state
    let u := Model.unitRoundoffAt FloatFormat.binary64
    let η := Model.underflowErrorAt FloatFormat.binary64
    let B := |S| + M / (1 - |A|)
    let E := (u * M + η * (2 + u) + |A| * u * (2 + u) * B) / (1 - |A| - |A| * u * (2 + u))
    process_f64 a state buf ⦃ fun r =>
      List.Forall₂ (fun c e => |real_f64 c - e| ≤ E) r.2.val
          (filt_real A S (buf.val.map real_f64)).2 ∧
        |real_f64 r.1 - (filt_real A S (buf.val.map real_f64)).1| ≤ E ⦄ := by
  intro A S u η B E
  have hblock := filt_f64_block_error a state buf.val M ha hs hno hM0 hM hstab
  apply WP.spec_mono (process_f64_spec a state buf)
  rintro r ⟨hbuf, hst⟩
  rw [hbuf, hst]
  exact hblock

end conjure_dsp_lib.one_pole

end
