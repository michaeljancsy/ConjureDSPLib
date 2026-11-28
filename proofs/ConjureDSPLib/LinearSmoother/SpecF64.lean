module

public import ConjureDSPLib.Code.Funs
public import ConjureDSPLib.Gain.SpecF64
public import ConjureDSPLib.Delay.Basic

/-!
# The linear smoother in f64: what the translated Rust does

About `set_target_f64`, `step_f64` and `process_f64` from `src/linear_smoother.rs`, as Aeneas
translated them. Write `r` for the state's `remaining`. This file proves:

1. `set_target_f64_spec`: `set_target_f64` never fails; with `steps = 0` it sets the value to the
   target, the step to `0` and `r` to 0, and otherwise it sets the step to
   `(target - value) / castNat_f64 steps` (`gain.rampStep_f64 value target steps`) and `r` to
   `steps`; it always sets the target.
2. `step_f64_spec`: `step_f64` never fails, returns `nextValue_f64` (the value itself when
   `r = 0`, the target when `r = 1`, and `target - step * castNat_f64 (r - 1)` otherwise), stores
   it as the new value, takes one off `r` (none when `r = 0`) and keeps the step and target.
3. `process_f64_spec`: `process_f64` never fails, and output sample `j` is
   `valueAfter_f64 s (j + 1)`: the value after `j + 1` steps, which is the value itself when
   `r = 0`, the target once `r ≤ j + 1`, and `target - step * castNat_f64 (r - (j + 1))` before.
4. `process_f64_lands`, `process_f64_at_rest`, `set_target_process_f64_lands`: after `set_target`
   with `steps` samples, the value returned by step number `steps` and every later one is the
   target, bit for bit; with `r = 0` a block changes nothing and every output is the value.
5. `valueAfter_set_target_f64`: before that, step number `k` (`1 ≤ k < steps`) returns
   `rampValue_f64 value target steps k`, `target - rampStep * castNat_f64 (steps - k)`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open conjure_dsp_lib.gain (castNat_f64 usize_toFloat_eq_castNat_f64 rampStep_f64)

namespace conjure_dsp_lib.linear_smoother

/-- **Starting a ramp.** `set_target_f64` never fails. It sets the target; with `steps = 0` it
also sets the value to the target, the step to `0` and `remaining` to 0, and otherwise it sets the
step to `(target - value) / castNat_f64 steps` and `remaining` to `steps`, keeping the value. -/
theorem set_target_f64_spec (s : StateF64) (target : Float) (steps : Std.Usize) :
    set_target_f64 s target steps ⦃ s' =>
      s'.target = target ∧
      (steps.val = 0 → s'.value = target ∧ s'.step = 0 ∧ s'.remaining.val = 0) ∧
      (steps.val ≠ 0 → s'.value = s.value ∧ s'.step = rampStep_f64 s.value target steps.val ∧
        s'.remaining.val = steps.val) ⦄ := by
  unfold set_target_f64
  split
  · rename_i h
    have h0 : steps.val = 0 := by rw [h]; rfl
    simp only [WP.spec_ok, h0, true_implies, ne_eq, not_true_eq_false, false_implies, and_true]
    and_intros <;> trivial
  · rename_i h
    have h0 : steps.val ≠ 0 := fun e => h (UScalar.eq_of_val_eq (by simpa using e))
    simp only [lift, bind_ok, WP.spec_ok, usize_toFloat_eq_castNat_f64, h0, false_implies,
      ne_eq, not_false_eq_true, true_implies, true_and]
    and_intros <;> trivial

/-- The value one step returns: the value itself when `remaining = 0`, the target when
`remaining = 1`, and `target - step * castNat_f64 (remaining - 1)` otherwise. -/
def nextValue_f64 (s : StateF64) : Float :=
  if s.remaining.val = 0 then s.value
  else if s.remaining.val = 1 then s.target
  else s.target - s.step * castNat_f64 (s.remaining.val - 1)

/-- **One step.** `step_f64` never fails; it returns `nextValue_f64 s`, stores it as the new
value, takes one off `remaining` (leaving 0 at 0) and keeps the step and the target. -/
theorem step_f64_spec (s : StateF64) :
    step_f64 s ⦃ y s' =>
      y = nextValue_f64 s ∧ s'.value = y ∧ s'.step = s.step ∧ s'.target = s.target ∧
        s'.remaining.val = s.remaining.val - 1 ⦄ := by
  unfold step_f64
  split
  · rename_i hpos
    have hpos' : 0 < s.remaining.val := by scalar_tac
    have h1 : s.remaining.val ≠ 0 := by omega
    step*
    · have hi : i.val = 0 := by simp_all
      have h2 : s.remaining.val = 1 := by omega
      simp [nextValue_f64, h2]
    · have hi : i.val ≠ 0 := fun e => by simp_all
      have h2 : s.remaining.val ≠ 1 := by omega
      refine ⟨?_, i_post⟩
      simp only [nextValue_f64, h1, h2, ite_false, fl_post, usize_toFloat_eq_castNat_f64, i_post]
      rfl
  · rename_i hpos
    have h0 : s.remaining.val = 0 := by scalar_tac
    simp only [WP.spec_ok]
    refine ⟨?_, rfl, rfl, rfl, by omega⟩
    simp [nextValue_f64, h0]

/-- The value after `k ≥ 1` steps from state `s`: the value itself when `remaining = 0`; the
target once `remaining ≤ k`; and `target - step * castNat_f64 (remaining - k)` before that. -/
def valueAfter_f64 (s : StateF64) (k : ℕ) : Float :=
  if s.remaining.val = 0 then s.value
  else if s.remaining.val ≤ k then s.target
  else s.target - s.step * castNat_f64 (s.remaining.val - k)

/-- One more step from the state reached after `i` steps (described by its fields) returns the
value after `i + 1` steps. -/
theorem nextValue_eq_valueAfter_f64 (s st : StateF64) (i : ℕ) (hstep : st.step = s.step)
    (htarget : st.target = s.target) (hrem : st.remaining.val = s.remaining.val - i)
    (hval : st.value = if i = 0 then s.value else valueAfter_f64 s i) :
    nextValue_f64 st = valueAfter_f64 s (i + 1) := by
  unfold nextValue_f64 valueAfter_f64
  rw [hstep, htarget, hrem]
  by_cases hr0 : s.remaining.val = 0
  · simp only [hr0, Nat.zero_sub, ite_true] at hval ⊢
    rw [hval]
    split_ifs <;> simp_all [valueAfter_f64]
  · simp only [hr0, ite_false]
    by_cases hri : s.remaining.val ≤ i
    · have h1 : s.remaining.val - i = 0 := by omega
      have hi0 : i ≠ 0 := by omega
      simp only [h1, ite_true, hval, hi0, ite_false, valueAfter_f64, hr0, hri]
      simp [show s.remaining.val ≤ i + 1 by omega]
    · have h1 : s.remaining.val - i ≠ 0 := by omega
      simp only [h1, ite_false]
      by_cases hr1 : s.remaining.val - i = 1
      · simp [hr1, show s.remaining.val ≤ i + 1 by omega]
      · simp only [hr1, ite_false, show ¬ s.remaining.val ≤ i + 1 by omega]
        congr 2

/-- The loop, started at position `i` from the state reached after `i` steps, never fails, and
fills every position `j` from `i` on with the value after `j + 1` steps. -/
theorem process_f64_loop_spec (s st : StateF64) (buf : Slice Float) (i : Std.Usize)
    (hi : i.val ≤ buf.length) (hstep : st.step = s.step) (htarget : st.target = s.target)
    (hrem : st.remaining.val = s.remaining.val - i.val)
    (hval : st.value = if i.val = 0 then s.value else valueAfter_f64 s i.val)
    (hdone : ∀ j < i.val, buf.val[j]? = some (valueAfter_f64 s (j + 1))) :
    process_f64_loop st buf i ⦃ fun r =>
      r.2.length = buf.length ∧
      (∀ j < buf.length, r.2.val[j]? = some (valueAfter_f64 s (j + 1))) ∧
      r.1.step = s.step ∧ r.1.target = s.target ∧
      r.1.remaining.val = s.remaining.val - buf.length ∧
      r.1.value = (if buf.length = 0 then s.value else valueAfter_f64 s buf.length) ⦄ := by
  unfold process_f64_loop
  apply loop.spec_decr_nat (fun x => x.2.1.length - x.2.2.val)
    (fun x => x.2.1.length = buf.length ∧ x.2.2.val ≤ x.2.1.length ∧
      x.1.step = s.step ∧ x.1.target = s.target ∧
      x.1.remaining.val = s.remaining.val - x.2.2.val ∧
      x.1.value = (if x.2.2.val = 0 then s.value else valueAfter_f64 s x.2.2.val) ∧
      ∀ j < x.2.2.val, x.2.1.val[j]? = some (valueAfter_f64 s (j + 1)))
  · rintro ⟨st', b, j⟩ ⟨hlen, hj, hs, ht, hr, hv, hd⟩
    simp only at hlen hj hs ht hr hv hd
    simp only [process_f64_loop.body]
    split
    · rename_i hjl
      have hjl' : j.val < b.length := by scalar_tac
      apply WP.spec_bind (step_f64_spec st')
      rintro ⟨y, st2⟩ ⟨hy, hv2, hs2, ht2, hr2⟩
      have hnext := nextValue_eq_valueAfter_f64 s st' j.val hs ht hr hv
      step*
      subst s_post
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [Slice.set_length, i2_post]; omega
      · exact hs2.trans hs
      · exact ht2.trans ht
      · rw [hr2, hr, i2_post]; omega
      · rw [i2_post, hv2, hy, hnext]; simp
      · intro k hk
        rw [i2_post] at hk
        simp only [Slice.set_val_eq]
        by_cases hkj : k = j.val
        · subst hkj
          rw [List.getElem?_set_self (by simpa using hjl'), hy, hnext]
        · rw [List.getElem?_set_ne (Ne.symm hkj)]
          exact hd k (by omega)
      · simp only [Slice.set_length, i2_post]; omega
    · rename_i hjl
      have hjb : j.val = b.length := by scalar_tac
      simp only [WP.spec_ok]
      refine ⟨hlen, fun k hk => hd k (by omega), hs, ht, by rw [hr, hjb, hlen], ?_⟩
      rw [hv, hjb, hlen]
  · exact ⟨rfl, hi, hstep, htarget, hrem, hval, hdone⟩

/-- **A block.** `process_f64` never fails; output sample `j` is `valueAfter_f64 s (j + 1)`, the
value after `j + 1` steps; and the state it leaves has the same step and target, `remaining`
reduced by the block's length (to no less than 0), and the last output as its value (the value
unchanged for an empty block). -/
theorem process_f64_spec (s : StateF64) (buf : Slice Float) :
    process_f64 s buf ⦃ fun r =>
      r.2.length = buf.length ∧
      (∀ j < buf.length, r.2.val[j]? = some (valueAfter_f64 s (j + 1))) ∧
      r.1.step = s.step ∧ r.1.target = s.target ∧
      r.1.remaining.val = s.remaining.val - buf.length ∧
      r.1.value = (if buf.length = 0 then s.value else valueAfter_f64 s buf.length) ⦄ := by
  unfold process_f64
  exact process_f64_loop_spec s s buf 0#usize (by simp) rfl rfl (by simp) (by simp)
    (fun j hj => absurd hj (by simp))

/-- `process_f64` never fails, for every state and block. -/
theorem process_f64_ok (s : StateF64) (buf : Slice Float) :
    ∃ r, process_f64 s buf = ok r := by
  obtain ⟨r, hr, -⟩ := conjure_dsp_lib.delay.exists_ok_of_spec (process_f64_spec s buf)
  exact ⟨r, hr⟩

/-- **Landing.** Once at least `remaining` steps have been taken (`remaining ≤ k`, `k ≥ 1`), the
value is the target, bit for bit, if a ramp was in progress (`remaining ≥ 1`), or the value
itself, unchanged, if not. -/
theorem process_f64_lands (s : StateF64) (k : ℕ) (hk : s.remaining.val ≤ k) :
    valueAfter_f64 s k = if s.remaining.val = 0 then s.value else s.target := by
  unfold valueAfter_f64
  split_ifs <;> simp_all

/-- **At rest.** With `remaining = 0`, a block of any length never fails, leaves the state
exactly as it was, and every output sample is the value. -/
theorem process_f64_at_rest (s : StateF64) (buf : Slice Float) (h0 : s.remaining.val = 0) :
    process_f64 s buf ⦃ fun r =>
      r.1.value = s.value ∧ r.1.step = s.step ∧ r.1.target = s.target ∧
        r.1.remaining.val = 0 ∧ ∀ j < buf.length, r.2.val[j]? = some s.value ⦄ := by
  apply WP.spec_mono (process_f64_spec s buf)
  rintro r ⟨-, hout, hs, ht, hr, hv⟩
  have hva : ∀ k, valueAfter_f64 s k = s.value := fun k => by simp [valueAfter_f64, h0]
  refine ⟨?_, hs, ht, by rw [hr, h0]; simp, fun j hj => by rw [hout j hj, hva]⟩
  split_ifs at hv <;> simp_all

/-- **Starting a ramp and running a block.** After `set_target_f64 s target steps`, a block of
any length never fails, and every output sample `j` with `steps ≤ j + 1` (step number `steps`
and after) is `target`, bit for bit. When the block has at least `steps` samples, the state it
leaves holds `target` as its value, with `remaining = 0`. -/
theorem set_target_process_f64_lands (s : StateF64) (target : Float) (steps : Std.Usize)
    (buf : Slice Float) :
    (do let s1 ← set_target_f64 s target steps; process_f64 s1 buf) ⦃ fun r =>
      (∀ j < buf.length, steps.val ≤ j + 1 → r.2.val[j]? = some target) ∧
      (steps.val ≤ buf.length → r.1.value = target ∧ r.1.remaining.val = 0) ⦄ := by
  apply WP.spec_bind (set_target_f64_spec s target steps)
  rintro s1 ⟨ht, h0, hn⟩
  apply WP.spec_mono (process_f64_spec s1 buf)
  rintro r ⟨-, hout, -, ht', hr, hv⟩
  have hland : ∀ k, steps.val ≤ k → valueAfter_f64 s1 k = target := by
    intro k hk
    by_cases hs0 : steps.val = 0
    · obtain ⟨hv1, -, hr1⟩ := h0 hs0
      simp [valueAfter_f64, hr1, hv1]
    · obtain ⟨-, -, hr1⟩ := hn hs0
      rw [process_f64_lands s1 k (by omega)]
      simp [hr1, hs0, ht]
  refine ⟨fun j hj hsj => by rw [hout j hj, hland (j + 1) hsj], fun hsb => ⟨?_, ?_⟩⟩
  · by_cases hb : buf.length = 0
    · have hs0 : steps.val = 0 := by omega
      obtain ⟨hv1, -, -⟩ := h0 hs0
      simp [hv, hb, hv1]
    · simp only [hv, hb, ite_false]
      exact hland _ hsb
  · rw [hr]
    by_cases hs0 : steps.val = 0
    · obtain ⟨-, -, hr1⟩ := h0 hs0
      simp [hr1]
    · obtain ⟨-, -, hr1⟩ := hn hs0
      omega

/-- The value of a ramp from `start` to `target` over `n` steps after `k` steps:
`target - rampStep_f64 start target n * castNat_f64 (n - k)`, in binary64, in that order. -/
def rampValue_f64 (start target : Float) (n k : ℕ) : Float :=
  target - rampStep_f64 start target n * castNat_f64 (n - k)

/-- **Before landing.** After `set_target_f64 s target steps` with `steps ≥ 1`, the value after
`k` steps, for `1 ≤ k < steps`, is `rampValue_f64 s.value target steps k`. -/
theorem valueAfter_set_target_f64 (s : StateF64) (target : Float) (steps : Std.Usize) (k : ℕ)
    (hk : k < steps.val) :
    set_target_f64 s target steps ⦃ s1 =>
      valueAfter_f64 s1 k = rampValue_f64 s.value target steps.val k ⦄ := by
  apply WP.spec_mono (set_target_f64_spec s target steps)
  rintro s1 ⟨ht, -, hn⟩
  obtain ⟨-, hst, hr1⟩ := hn (by omega)
  have h1 : steps.val ≠ 0 := by omega
  have h2 : ¬ steps.val ≤ k := by omega
  simp only [valueAfter_f64, hr1, h1, h2, ite_false, rampValue_f64, ht, hst]

end conjure_dsp_lib.linear_smoother

end
