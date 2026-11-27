module

public import ConjureDSPLib.Code.Funs
public import ConjureDSPLib.Delay.Basic

/-!
# The smoother in f64: what the translated Rust does

About `step_f64`, `process_f64`, `step_coeff_f64` and `process_coeff_f64` from
`src/smoother.rs`, as Aeneas translated them (into `ConjureDSPLib/Code/Funs.lean`). This file
proves:

1. `step_f64_eq`: one Rust step is exactly `state + (1 - a) * (target - state)` in Lean's `Float`
   (IEEE binary64), in that order, and never fails.
2. `process_f64_spec`: the Rust block loop never fails and produces exactly the outputs and final
   state of `filt_f64` with `c = 1 - a` computed once in binary64.
3. `step_coeff_f64_eq`, `process_coeff_f64_spec`: the same with the coefficient `c` given
   directly, `state + c * (target - state)`.
4. `step_f64_eq_step_coeff`, `process_f64_eq_process_coeff`: `step_f64 a` and `process_f64 a` are
   `step_coeff_f64` and `process_coeff_f64` with `c = 1 - a` computed in binary64.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.smoother

/-- One Rust smoother step is `state + (1 - a) * (target - state)` in binary64 arithmetic, in
that order, and cannot fail. -/
theorem step_f64_eq (a state target : Float) :
    step_f64 a state target = ok (state + (1 - a) * (target - state)) := rfl

/-- The smoother on binary64 numbers, with `c` standing for the already computed `1 - a`: run it
over a list of input samples from state `s`, returning the final state and the list of outputs.
-/
def filt_f64 (c : Float) : Float → List Float → Float × List Float
  | s, [] => (s, [])
  | s, x :: xs =>
    let y := s + c * (x - s)
    let r := filt_f64 c y xs
    (r.1, y :: r.2)

/-- One loop iteration on plain lists, as `one_pole.filt_f64_set_step`. -/
theorem filt_f64_set_step (c s : Float) (l : List Float) (j : ℕ) (hj : j < l.length) :
    (l.set j (s + c * (l[j] - s))).take (j + 1) ++
        (filt_f64 c (s + c * (l[j] - s))
          ((l.set j (s + c * (l[j] - s))).drop (j + 1))).2 =
      l.take j ++ (filt_f64 c s (l.drop j)).2 ∧
    (filt_f64 c (s + c * (l[j] - s))
        ((l.set j (s + c * (l[j] - s))).drop (j + 1))).1 =
      (filt_f64 c s (l.drop j)).1 := by
  rw [List.drop_eq_getElem_cons hj]
  have hd : (l.set j (s + c * (l[j] - s))).drop (j + 1) = l.drop (j + 1) := by
    simp [List.drop_set]
  have ht : (l.set j (s + c * (l[j] - s))).take (j + 1) = l.take j ++ [s + c * (l[j] - s)] := by
    rw [List.take_add_one]
    simp [List.take_set, List.set_eq_of_length_le, hj]
  rw [hd, ht]
  simp [filt_f64]

/-- The smoother's loop, started at position `i` with `c` already computed, leaves the first `i`
samples alone and smooths the rest. -/
theorem process_f64_loop_spec (state : Float) (buf : Slice Float) (c : Float) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    process_f64_loop state buf c i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_f64 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_f64_loop
  -- The same invariant as `one_pole.process_f64_loop_spec`, with this `filt_f64`.
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_f64 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_f64_loop.body]
    step*
    · -- Still looping: rebuild the invariant one sample further on.
      subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_f64_set_step c st b.val j.val hjl
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

/-- The Rust smoother never fails, and its output samples and final state are exactly those of
`filt_f64` with `c = 1 - a` computed once in binary64, sample by sample. -/
theorem process_f64_spec (a state : Float) (buf : Slice Float) :
    process_f64 a state buf ⦃ fun r =>
      r.2.val = (filt_f64 (1 - a) state buf.val).2 ∧
      r.1 = (filt_f64 (1 - a) state buf.val).1 ⦄ := by
  -- `process_f64` computes `1 - a` with the literal `1` stored as its bit pattern; Lean sees
  -- that this is the same `1`.
  have h := process_f64_loop_spec state buf (1 - a) 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.take_zero, List.drop_zero, List.nil_append] at h
  exact h

/-! ## The smoother with the coefficient given directly -/

/-- One Rust step of `step_coeff_f64` is `state + c * (target - state)` in binary64 arithmetic,
in that order, and cannot fail. -/
theorem step_coeff_f64_eq (c state target : Float) :
    step_coeff_f64 c state target = ok (state + c * (target - state)) := rfl

/-- `step_f64 a` is `step_coeff_f64` with the coefficient `1 - a` computed in binary64. -/
theorem step_f64_eq_step_coeff (a state target : Float) :
    step_f64 a state target = step_coeff_f64 (1 - a) state target := rfl

/-- The loop of `process_coeff_f64`, started at position `i`, leaves the first `i` samples alone
and smooths the rest, as `process_f64_loop_spec`. -/
theorem process_coeff_f64_loop_spec (c state : Float) (buf : Slice Float) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    process_coeff_f64_loop c state buf i ⦃ fun r =>
      r.2.val = buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      r.1 = (filt_f64 c state (buf.val.drop i.val)).1 ⦄ := by
  unfold process_coeff_f64_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.2.1.val.take x.2.2.val ++ (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).2 =
        buf.val.take i.val ++ (filt_f64 c state (buf.val.drop i.val)).2 ∧
      (filt_f64 c x.1 (x.2.1.val.drop x.2.2.val)).1 =
        (filt_f64 c state (buf.val.drop i.val)).1)
  · rintro ⟨st, b, j⟩ ⟨hlen, hj, hout, hst⟩
    simp only at hlen hj hout hst
    simp only [process_coeff_f64_loop.body]
    step*
    · subst s_post fl_post
      have hjl : j.val < b.length := by scalar_tac
      obtain ⟨h1, h2⟩ := filt_f64_set_step c st b.val j.val hjl
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]; exact h1.trans hout
      · simp only [Slice.set_val_eq, i2_post]; exact h2.trans hst
      · simp only [Slice.set_length, i2_post]; omega
    · have hjl : j.val = b.length := by scalar_tac
      simp [hjl, filt_f64] at hout hst
      exact ⟨hout, hst⟩
  · exact ⟨rfl, hi, rfl, rfl⟩

/-- `process_coeff_f64` never fails, and its output samples and final state are exactly those
of `filt_f64 c`: `state + c * (x - state)` in binary64 for each sample in turn, with `c` as
given. -/
theorem process_coeff_f64_spec (c state : Float) (buf : Slice Float) :
    process_coeff_f64 c state buf ⦃ fun r =>
      r.2.val = (filt_f64 c state buf.val).2 ∧ r.1 = (filt_f64 c state buf.val).1 ⦄ := by
  have h := process_coeff_f64_loop_spec c state buf 0#usize (by simp)
  simp only [UScalar.ofNatCore_val_eq, List.take_zero, List.drop_zero, List.nil_append] at h
  exact h

/-- `process_f64 a` is `process_coeff_f64` with the coefficient `1 - a` computed in binary64:
the same result (outputs and final state), for every `a`, state and block. -/
theorem process_f64_eq_process_coeff (a state : Float) (buf : Slice Float) :
    process_f64 a state buf = process_coeff_f64 (1 - a) state buf := by
  obtain ⟨⟨s1, b1⟩, e1, h1a, h1b⟩ := delay.exists_ok_of_spec (process_f64_spec a state buf)
  obtain ⟨⟨s2, b2⟩, e2, h2a, h2b⟩ :=
    delay.exists_ok_of_spec (process_coeff_f64_spec (1 - a) state buf)
  rw [e1, e2]
  have hs : s1 = s2 := h1b.trans h2b.symm
  have hb : b1 = b2 := (Slice.eq_iff _ _).mpr (h1a.trans h2a.symm)
  rw [hs, hb]

end conjure_dsp_lib.smoother

end
