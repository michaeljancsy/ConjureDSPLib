module

public import ConjureDSPLib.Code.ConjureDspLib
public import Mathlib.Data.List.Rotate

/-!
# The delay line in f32: what the translated Rust does

About `process_f32` from `src/delay.rs`, as Aeneas translated it.

Write `L` for the buffer's length, `p` for the write position and `n` for the number of audio
samples. The buffer read in time order, oldest first, is `buf.rotate p` (Mathlib's
`List.rotate`): `buf[p], buf[p+1], …, buf[L-1], buf[0], …, buf[p-1]` when `p < L`; for `p ≥ L`,
`List.rotate` uses `p mod L`, as the Rust code does. Following it with the block's input gives
the history `buf.rotate p ++ audio`, of length `L + n`, in which the sample written `d` samples
before input sample `j` is element `L + j - d`.

This file proves:

1. `process_f32_spec`: for `L > 0` and any position and delay, `process_f32` never fails; output
   sample `j` is element `L + j - d` of the history, with `d = min delay (L - 1)`; and the new
   buffer read in time order from the new position is the last `L` elements of the history.
   So the history after one block is the starting point of the next: blocks compose.
2. `process_f32_delay`: the same, for a delay less than `L`, with `d` the delay itself.
3. `process_f32_empty_buffer`: for `L = 0`, it returns the buffer, position and audio unchanged.
4. `process_f32_ok`: `process_f32` never fails, for every buffer, position, delay and audio.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.delay

/-- Moving on by one and wrapping at `L` is adding one mod `L`. -/
private theorem succ_mod_eq (x L : ℕ) (hL : 0 < L) :
    (x + 1) % L = if x % L + 1 = L then 0 else x % L + 1 := by
  have hx := Nat.mod_lt x hL
  rcases (by omega : L = 1 ∨ 2 ≤ L) with rfl | h2
  · simp [Nat.mod_one]
  · rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < L)]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)

/-- Choosing between two results that cannot fail is choosing between their values. -/
private theorem ite_ok {α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then (ok x : Result α) else ok y) = ok (if c then x else y) := by
  split <;> rfl

/-- The loop, started at sample `i` with write index `w` and read index `r`. `S` is the whole
history: the `L` samples in the buffer before the block, oldest first, then the block's input
samples. The hypotheses are the loop invariant: buffer index `k` holds history sample
`i + (k - w) mod L` (written without `mod`), the first `i` samples of `a` are done, and the
rest are still the input. `f ⦃ P ⦄` is Aeneas's notation for "running `f` never fails, and its
result satisfies `P`". -/
theorem process_f32_loop_spec (L d p n : ℕ) (S : List Float32) (len : Std.Usize)
    (hlen : len.val = L) (hd : d < L)
    (b a : Slice Float32) (w r i : Std.Usize)
    (hb : b.length = L) (ha : a.length = n) (hw : w.val < L) (hr : r.val < L)
    (hrw : r.val + d = w.val ∨ r.val + d = w.val + L) (hi : i.val ≤ n)
    (hwp : w.val = (p + i.val) % L)
    (hbS : ∀ k < L, b.val[k]? =
      S[if w.val ≤ k then i.val + k - w.val else i.val + k + L - w.val]?)
    (ha1 : ∀ j < i.val, a.val[j]? = S[L + j - d]?)
    (ha2 : ∀ j, i.val ≤ j → a.val[j]? = S[L + j]?) :
    process_f32_loop b a len w r i ⦃ fun res =>
      res.1.length = L ∧ res.2.1.val = (p + n) % L ∧
      (∀ k < L, res.1.val[k]? =
        S[if res.2.1.val ≤ k then n + k - res.2.1.val else n + k + L - res.2.1.val]?) ∧
      res.2.2.length = n ∧ ∀ j < n, res.2.2.val[j]? = S[L + j - d]? ⦄ := by
  unfold process_f32_loop
  apply loop.spec_decr_nat (fun x => n - x.2.2.2.2.val)
    (fun x => x.1.length = L ∧ x.2.1.length = n ∧ x.2.2.1.val < L ∧ x.2.2.2.1.val < L ∧
      (x.2.2.2.1.val + d = x.2.2.1.val ∨ x.2.2.2.1.val + d = x.2.2.1.val + L) ∧
      x.2.2.2.2.val ≤ n ∧ x.2.2.1.val = (p + x.2.2.2.2.val) % L ∧
      (∀ k < L, x.1.val[k]? = S[if x.2.2.1.val ≤ k then x.2.2.2.2.val + k - x.2.2.1.val
          else x.2.2.2.2.val + k + L - x.2.2.1.val]?) ∧
      (∀ j < x.2.2.2.2.val, x.2.1.val[j]? = S[L + j - d]?) ∧
      (∀ j, x.2.2.2.2.val ≤ j → x.2.1.val[j]? = S[L + j]?))
  · rintro ⟨b, a, w, r, i⟩ ⟨hb, ha, hw, hr, hrw, hi, hwp, hbS, ha1, ha2⟩
    simp only at hb ha hw hr hrw hi hwp hbS ha1 ha2
    simp only [process_f32_loop.body, ite_ok]
    step*
    · -- One more sample: the write and read indices move on by one, wrapping at `L`.
      have hiN : i.val < n := by scalar_tac
      have hL : 0 < L := by omega
      have hW : (if w1 = len then 0#usize else w1).val =
          if w.val + 1 = L then 0 else w.val + 1 := by
        by_cases h : w1 = len
        · have : w.val + 1 = L := by rw [← w1_post, h, hlen]
          simp [h, this]
        · have : w.val + 1 ≠ L := fun e => h (UScalar.eq_of_val_eq (by rw [w1_post, hlen, e]))
          simp [h, this, w1_post]
      have hR : (if r1 = len then 0#usize else r1).val =
          if r.val + 1 = L then 0 else r.val + 1 := by
        by_cases h : r1 = len
        · have : r.val + 1 = L := by rw [← r1_post, h, hlen]
          simp [h, this]
        · have : r.val + 1 ≠ L := fun e => h (UScalar.eq_of_val_eq (by rw [r1_post, hlen, e]))
          simp [h, this, r1_post]
      generalize (if w1 = len then 0#usize else w1) = W at hW ⊢
      generalize (if r1 = len then 0#usize else r1) = R at hR ⊢
      subst s_post fl1_post buffer1_post fl_post
      simp only [Slice.set_length, Slice.set_val_eq, i2_post]
      have hbl : b.val.length = L := hb
      have hal : a.val.length = n := ha
      refine ⟨hb, ha, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_, by omega⟩
      · split_ifs at hW <;> omega
      · split_ifs at hR <;> omega
      · split_ifs at hW hR <;> omega
      · rw [hW, ← Nat.add_assoc, succ_mod_eq _ _ hL, ← hwp]
      · -- The buffer: index `w` now holds input sample `i`, history sample `L + i`.
        intro k hk
        by_cases hkw : w.val = k
        · subst hkw
          rw [List.getElem?_set_self (by omega)]
          have : (if W.val ≤ w.val then i.val + 1 + w.val - W.val
              else i.val + 1 + w.val + L - W.val) = L + i.val := by
            split_ifs at hW ⊢ <;> omega
          rw [this, ← ha2 i.val le_rfl, List.getElem?_eq_getElem]
        · rw [List.getElem?_set_ne hkw, hbS k hk]
          congr 1
          split_ifs at hW ⊢ <;> omega
      · -- The output: sample `i` is read from index `r`, history sample `L + i - d`.
        intro j hj
        by_cases hji : i.val = j
        · subst hji
          rw [List.getElem?_set_self (by omega), ← List.getElem?_eq_getElem]
          by_cases hwr : w.val = r.val
          · have hd0 : d = 0 := by omega
            rw [hwr, List.getElem?_set_self (by omega), hd0, Nat.sub_zero, ← ha2 i.val le_rfl,
              List.getElem?_eq_getElem]
          · rw [List.getElem?_set_ne hwr, hbS r.val hr]
            congr 1
            split_ifs <;> omega
        · rw [List.getElem?_set_ne hji, ha1 j (by omega)]
      · intro j hj
        rw [List.getElem?_set_ne (by omega), ha2 j (by omega)]
    · -- Finished: every sample is done.
      have hiN : i.val = n := by scalar_tac
      rw [hiN] at hwp hbS ha1
      exact ⟨hb, hwp, hbS, ha, ha1⟩
  · exact ⟨hb, ha, hw, hr, hrw, hi, hwp, hbS, ha1, ha2⟩

/-- After the loop: buffer index `k` holds history sample `n + (k - w) mod L`, so reading the
buffer in time order from `w` gives the history from sample `n` on. -/
private theorem rotate_eq_drop_f32 (L n w : ℕ) (S b : List Float32) (hS : S.length = L + n)
    (hb : b.length = L) (hw : w < L)
    (hbS : ∀ k < L, b[k]? = S[if w ≤ k then n + k - w else n + k + L - w]?) :
    b.rotate w = S.drop n := by
  apply List.ext_getElem?
  intro m
  by_cases hm : m < L
  · rw [List.getElem?_rotate (by omega), List.getElem?_drop, hb]
    rw [hbS _ (Nat.mod_lt _ (by omega))]
    congr 1
    rcases Nat.lt_or_ge (m + w) L with h | h
    · rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]; split_ifs <;> omega
  · rw [List.getElem?_eq_none (by simp [List.length_rotate]; omega),
      List.getElem?_eq_none (by simp; omega)]

/-- The loop from its start: write index `position mod L`, read index `d` samples behind it. -/
private theorem process_f32_from_start (buffer audio : Slice Float32)
    (position delay d w r : Std.Usize) (hL : 0 < buffer.length)
    (hd : d.val = min delay.val (buffer.length - 1))
    (hw : w.val = position.val % buffer.length)
    (hrw : r.val + d.val = w.val ∨ r.val + d.val = w.val + buffer.length)
    (hr : r.val < buffer.length) :
    process_f32_loop buffer audio buffer.len w r 0#usize ⦃ buffer' position' audio' =>
      audio'.length = audio.length ∧
      (∀ j < audio.length, audio'.val[j]? =
        (buffer.val.rotate position.val ++ audio.val)[buffer.length + j -
          min delay.val (buffer.length - 1)]?) ∧
      buffer'.length = buffer.length ∧
      position'.val = (position.val + audio.length) % buffer.length ∧
      buffer'.val.rotate position'.val =
        (buffer.val.rotate position.val ++ audio.val).drop audio.length ⦄ := by
  have hlen : buffer.len.val = buffer.length := Slice.len_val buffer
  have hbl : buffer.val.length = buffer.length := rfl
  have hwL : w.val < buffer.length := by rw [hw]; exact Nat.mod_lt _ hL
  have hS : (buffer.val.rotate position.val ++ audio.val).length =
      buffer.length + audio.length := by simp [List.length_rotate]
  apply WP.spec_mono (process_f32_loop_spec buffer.length d.val position.val audio.length
    (buffer.val.rotate position.val ++ audio.val) buffer.len hlen (by omega) buffer audio w r
    0#usize rfl rfl hwL hr hrw (by simp) (by simp [hw]) ?_ (by simp) ?_)
  · rintro ⟨b', p', a'⟩ ⟨hb', hp', hbS', ha', ha1'⟩
    simp only [WP.uncurry'_pair]
    refine ⟨ha', fun j hj => by rw [ha1' j hj, hd], hb', hp', ?_⟩
    exact rotate_eq_drop_f32 _ _ _ _ _ hS hb' (by rw [hp']; exact Nat.mod_lt _ hL) hbS'
  · -- At the start, index `k` holds the history sample `(k - w) mod L` of the old buffer.
    intro k hk
    have h0 : (0#usize : Std.Usize).val = 0 := by simp
    simp only [h0, Nat.zero_add]
    rw [List.getElem?_append_left (by simp [List.length_rotate]; split_ifs <;> omega),
      List.getElem?_rotate (by split_ifs <;> omega), hbl]
    congr 1
    have hp : position.val = position.val % buffer.length +
        buffer.length * (position.val / buffer.length) := (Nat.mod_add_div _ _).symm
    split_ifs with h
    · rw [hp, ← Nat.add_assoc, Nat.add_mul_mod_self_left, ← hw, Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [hp, ← Nat.add_assoc, Nat.add_mul_mod_self_left, ← hw]
      rw [show k + buffer.length - w.val + w.val = k + buffer.length by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt hk]
  · intro j _
    rw [List.getElem?_append_right (by simp [List.length_rotate])]
    simp [List.length_rotate]

/-- **The delay line, for any position and delay.** Let `L = buffer.length > 0`,
`n = audio.length`, `d = min delay (L - 1)` (the delay, clamped to at most `L - 1`) and
`H = buffer.rotate position ++ audio` (the buffer read in time order from `position`, taken mod
`L`, then the input). Then `process_f32` never fails, and its result `(buffer', position', audio')`
satisfies:
- `audio'` has `n` samples, and for every `j < n`, `audio'[j]? = H[L + j - d]?`: output sample
  `j` is element `L + j - d` of `H` (both indices are in range, so the samples are equal);
- `buffer'` has length `L`, and `position' = (position + n) mod L`;
- `buffer'.rotate position' = H.drop n`: the new buffer read in time order from the new position
  is the last `L` elements of `H`. -/
theorem process_f32_spec (buffer : Slice Float32) (position delay : Std.Usize)
    (audio : Slice Float32) (hL : 0 < buffer.length) :
    process_f32 buffer position delay audio ⦃ buffer' position' audio' =>
      audio'.length = audio.length ∧
      (∀ j < audio.length, audio'.val[j]? =
        (buffer.val.rotate position.val ++ audio.val)[buffer.length + j -
          min delay.val (buffer.length - 1)]?) ∧
      buffer'.length = buffer.length ∧
      position'.val = (position.val + audio.length) % buffer.length ∧
      buffer'.val.rotate position'.val =
        (buffer.val.rotate position.val ++ audio.val).drop audio.length ⦄ := by
  unfold process_f32
  step*
  split <;> rename_i hdl <;> step* <;> split <;> rename_i hdw <;> step*
  all_goals first
    | (apply process_f32_from_start (d := delay) <;> scalar_tac)
    | (apply process_f32_from_start (d := d) <;> scalar_tac)

/-- **The delay property.** The same as `process_f32_spec` when `delay < L`, so that the delay is
used as given: for `L = buffer.length > 0`, `n = audio.length` and
`H = buffer.rotate position ++ audio`, `process_f32` never fails; `audio'` has `n` samples and
`audio'[j]? = H[L + j - delay]?` for every `j < n` (the sample written `delay` samples earlier);
`buffer'` has length `L`; `position' = (position + n) mod L`; and
`buffer'.rotate position' = H.drop n`, the last `L` elements of `H`. -/
theorem process_f32_delay (buffer : Slice Float32) (position delay : Std.Usize)
    (audio : Slice Float32) (hL : 0 < buffer.length) (hd : delay.val < buffer.length) :
    process_f32 buffer position delay audio ⦃ buffer' position' audio' =>
      audio'.length = audio.length ∧
      (∀ j < audio.length, audio'.val[j]? =
        (buffer.val.rotate position.val ++ audio.val)[buffer.length + j - delay.val]?) ∧
      buffer'.length = buffer.length ∧
      position'.val = (position.val + audio.length) % buffer.length ∧
      buffer'.val.rotate position'.val =
        (buffer.val.rotate position.val ++ audio.val).drop audio.length ⦄ := by
  have hmin : min delay.val (buffer.length - 1) = delay.val := by omega
  simpa only [hmin] using process_f32_spec buffer position delay audio hL

/-- With an empty buffer (`buffer.length = 0`), `process_f32` never fails and returns the buffer,
position and audio unchanged. -/
theorem process_f32_empty_buffer (buffer : Slice Float32) (position delay : Std.Usize)
    (audio : Slice Float32) (hL : buffer.length = 0) :
    process_f32 buffer position delay audio = ok (buffer, position, audio) := by
  have h : Slice.len buffer = 0#usize := UScalar.eq_of_val_eq (by simp [hL])
  simp [process_f32, h]

/-- `process_f32` never fails, for every buffer, position, delay and audio: it returns a result,
with no panic, out-of-bounds index or index overflow, and it terminates. -/
theorem process_f32_ok (buffer : Slice Float32) (position delay : Std.Usize)
    (audio : Slice Float32) : ∃ r, process_f32 buffer position delay audio = ok r := by
  rcases Nat.eq_zero_or_pos buffer.length with h | h
  · exact ⟨_, process_f32_empty_buffer buffer position delay audio h⟩
  · have hs := process_f32_spec buffer position delay audio h
    revert hs
    cases process_f32 buffer position delay audio <;> simp

end conjure_dsp_lib.delay

end
