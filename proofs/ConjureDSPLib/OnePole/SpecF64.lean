module

public import ConjureDSPLib.Code.ConjureDspLib

/-!
# The one-pole filter in f64: what the translated Rust does

About `step_f64`, `process_f64`, `smooth_step_f64` and `smooth_f64` from `src/one_pole.rs`, as
Aeneas translated them (into `ConjureDSPLib/Code/ConjureDspLib.lean`). This file proves:

1. `step_f64_eq`: one Rust step is exactly `x + a * state` in Lean's `Float` (IEEE binary64),
   and never fails.
2. `process_f64_spec`: the Rust block loop never fails and produces exactly the outputs and
   final state of `filt_f64`, the filter computed in binary64 one sample at a time.
3. `smooth_step_f64_eq`: one Rust smoother step is exactly `state + (1 - a) * (target - state)`
   in Lean's `Float`, in that order, and never fails.
4. `smooth_f64_spec`: the Rust smoother's block loop never fails and produces exactly the outputs
   and final state of `filt_smooth_f64` with `c = 1 - a` computed once in binary64.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.one_pole

/-- One Rust step is `x + a * state` in binary64 arithmetic, and cannot fail. -/
theorem step_f64_eq (a state x : Float) :
    step_f64 a state x = ok (x + a * state) := rfl

/-- The filter as a mathematician writes it, on binary64 numbers: run it over a list of input
samples from state `s`, returning the final state and the list of outputs. -/
def filt_f64 (a : Float) : Float → List Float → Float × List Float
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := x + a * s
    let r := filt_f64 a y xs
    (r.1, y :: r.2)

/-- One loop iteration on plain lists: overwriting sample `j` with its filtered value and moving
on to `j + 1` doesn't change the final answer. -/
theorem filt_f64_set_step (a s : Float) (l : List Float) (j : ℕ) (hj : j < l.length) :
    (l.set j (l[j] + a * s)).take (j + 1) ++
        (filt_f64 a (l[j] + a * s) ((l.set j (l[j] + a * s)).drop (j + 1))).2 =
      l.take j ++ (filt_f64 a s (l.drop j)).2 ∧
    (filt_f64 a (l[j] + a * s) ((l.set j (l[j] + a * s)).drop (j + 1))).1 =
      (filt_f64 a s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (l[j] + a * s)).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (l[j] + a * s)).take (j + 1) = l.take j ++ [l[j] + a * s] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_f64]

/-- The loop, started at position `i`, leaves the first `i` samples alone and filters the rest.
`f ⦃ P ⦄` is Aeneas's notation for "running `f` never fails, and its result satisfies `P`". -/
theorem process_f64_loop_spec (a state : Float) (buf : Slice Float) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    process_f64_loop a state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_f64 a state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_f64 a state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_f64_loop
  -- Invariant on the loop state `(s, b, j)`: the buffer keeps its length, and finishing the job
  -- from here (keep `b`'s first `j` samples, filter the rest from state `s`) gives the same answer
  -- as filtering from the start.
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_f64 a x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_f64 a state (buf.val.drop i.val)).2 ∧
      (filt_f64 a x.1 (x.2.1.val.drop x.2.2.val)).1 = (filt_f64 a state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_f64_loop.body, step_f64_eq]
    step*
    · -- Still looping: rebuild the invariant one sample further on.
      subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_f64_set_step a st b.val j.val hjl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: the whole buffer is processed.
      have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_f64] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The Rust block-processing function never fails, and its output samples and final
state are exactly those of `filt_f64`, sample by sample. -/
theorem process_f64_spec (a state : Float) (buf : Slice Float) :
    process_f64 a state buf ⦃ fun r =>
      r.2.val = (filt_f64 a state buf.val).2 ∧ r.1 = (filt_f64 a state buf.val).1 ⦄ := by
  simpa using process_f64_loop_spec a state buf 0#usize (by simp)

/-! ## The smoother -/

/-- One Rust smoother step is `state + (1 - a) * (target - state)` in binary64 arithmetic, in
that order, and cannot fail. -/
theorem smooth_step_f64_eq (a state target : Float) :
    smooth_step_f64 a state target = ok (state + (1 - a) * (target - state)) := rfl

/-- The smoother on binary64 numbers, with `c` standing for the already computed `1 - a`: run it
over a list of input samples from state `s`, returning the final state and the list of outputs.
-/
def filt_smooth_f64 (c : Float) : Float → List Float → Float × List Float
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := s + c * (x - s)
    let r := filt_smooth_f64 c y xs
    (r.1, y :: r.2)

/-- One loop iteration on plain lists, as `filt_f64_set_step`. -/
theorem filt_smooth_f64_set_step (c s : Float) (l : List Float) (j : ℕ) (hj : j < l.length) :
    (l.set j (s + c * (l[j] - s))).take (j + 1) ++
        (filt_smooth_f64 c (s + c * (l[j] - s))
          ((l.set j (s + c * (l[j] - s))).drop (j + 1))).2 =
      l.take j ++ (filt_smooth_f64 c s (l.drop j)).2 ∧
    (filt_smooth_f64 c (s + c * (l[j] - s))
        ((l.set j (s + c * (l[j] - s))).drop (j + 1))).1 =
      (filt_smooth_f64 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (s + c * (l[j] - s))).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (s + c * (l[j] - s))).take (j + 1) = l.take j ++ [s + c * (l[j] - s)] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_smooth_f64]

/-- The smoother's loop, started at position `i` with `c` already computed, leaves the first `i`
samples alone and smooths the rest. -/
theorem smooth_f64_loop_spec (state : Float) (buf : Slice Float) (c : Float) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    smooth_f64_loop state buf c i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_smooth_f64 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_smooth_f64 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold smooth_f64_loop
  -- The same invariant as `process_f64_loop_spec`, with `filt_smooth_f64`.
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_smooth_f64 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_smooth_f64 c state (buf.val.drop i.val)).2 ∧
      (filt_smooth_f64 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_smooth_f64 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [smooth_f64_loop.body]
    step*
    · -- Still looping: rebuild the invariant one sample further on.
      subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_smooth_f64_set_step c st b.val j.val hjl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: the whole buffer is processed.
      have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_smooth_f64] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- The Rust smoother never fails, and its output samples and final state are exactly those of
`filt_smooth_f64` with `c = 1 - a` computed once in binary64, sample by sample. -/
theorem smooth_f64_spec (a state : Float) (buf : Slice Float) :
    smooth_f64 a state buf ⦃ fun r =>
      r.2.val = (filt_smooth_f64 (1 - a) state buf.val).2 ∧
      r.1 = (filt_smooth_f64 (1 - a) state buf.val).1 ⦄ := by
  -- `smooth_f64` computes `1 - a` with the literal `1` stored as its bit pattern; Lean sees
  -- that this is the same `1`.
  have h := smooth_f64_loop_spec state buf (1 - a) 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.take_zero, List.drop_zero, List.nil_append] at h
  exact h

end conjure_dsp_lib.one_pole

end
