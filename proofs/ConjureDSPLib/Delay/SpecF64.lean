module

public import ConjureDSPLib.Code.ConjureDspLib
public import ConjureDSPLib.Delay.Basic

/-!
# The delay line in f64: what the translated Rust does

About `process_f64` from `src/delay.rs`, as Aeneas translated it.

Write `L` for the buffer's length, `p` for the write position, `n` for the number of audio
samples and `d = min delay_samples (L - 1)` for the delay used (the delay asked for, clamped to at
most `L - 1`). The buffer read in time order, oldest first, is `buf.rotate p` (Mathlib's
`List.rotate`): `buf[p], buf[p+1], …, buf[L-1], buf[0], …, buf[p-1]` when `p < L`; for `p ≥ L`,
`List.rotate` uses `p mod L`, as the Rust code does. Following it with the block's input gives
the history `H = buf.rotate p ++ audio`, of length `L + n`, in which the sample written `d`
samples before input sample `j` is element `L + j - d`.

This file proves:

1. `process_f64_spec`: for `L > 0` and any position and delay, `process_f64` never fails; output
   sample `j` is element `L + j - d` of `H`; and the new buffer read in time order from the new
   position is the last `L` elements of `H`.
2. `process_f64_spec_of_lt`: the same, for `delay_samples < L`, with `d = delay_samples`.
3. `process_f64_getElem`: for `L > 0`, output sample `j` equals `H[L + j - d]`, with both
   indices proved in range.
4. `process_f64_zero_prefix`: for `L > 0` and a buffer of zeros, the first
   `min d n` output samples are 0.
5. `process_f64_append`: one call on `audio₁` followed by one on `audio₂`, with the buffer and
   position the first returns, gives the same buffer, position and output samples as one call on
   `audio₁ ++ audio₂`.
6. `process_f64_empty_buffer`: for `L = 0`, it returns the buffer, position and audio unchanged.
7. `process_f64_ok`: `process_f64` never fails, for every buffer, position, delay and audio.
8. `process_f64_state_indep`: two calls that differ only in the delay both never fail and return
   the same buffer and position.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.delay

/-- The loop, started at sample `i` with write index `w` and read index `r`. `S` is the whole
history: the `L` samples in the buffer before the block, oldest first, then the block's input
samples. The hypotheses are the loop invariant: buffer index `k` holds history sample
`i + (k - w) mod L` (written without `mod`), the first `i` samples of `a` are done, and the
rest are still the input. `f ⦃ P ⦄` is Aeneas's notation for "running `f` never fails, and its
result satisfies `P`". -/
theorem process_f64_loop_spec (L d p n : ℕ) (S : List Float) (len : Std.Usize)
    (hlen : len.val = L) (hd : d < L)
    (b a : Slice Float) (w r i : Std.Usize)
    (hb : b.length = L) (ha : a.length = n) (hw : w.val < L) (hr : r.val < L)
    (hrw : r.val + d = w.val ∨ r.val + d = w.val + L) (hi : i.val ≤ n)
    (hwp : w.val = (p + i.val) % L)
    (hbS : ∀ k < L, b.val[k]? =
      S[if w.val ≤ k then i.val + k - w.val else i.val + k + L - w.val]?)
    (ha1 : ∀ j < i.val, a.val[j]? = S[L + j - d]?)
    (ha2 : ∀ j, i.val ≤ j → a.val[j]? = S[L + j]?) :
    process_f64_loop b a len w r i ⦃ fun res =>
      res.1.length = L ∧ res.2.1.val = (p + n) % L ∧
      (∀ k < L, res.1.val[k]? =
        S[if res.2.1.val ≤ k then n + k - res.2.1.val else n + k + L - res.2.1.val]?) ∧
      res.2.2.length = n ∧ ∀ j < n, res.2.2.val[j]? = S[L + j - d]? ⦄ := by
  unfold process_f64_loop
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
    simp only [process_f64_loop.body, ite_ok]
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

/-- The loop from its start: write index `position mod L`, read index `d` samples behind it. -/
private theorem process_f64_from_start (buffer audio : Slice Float)
    (position delay_samples d w r : Std.Usize) (hL : 0 < buffer.length)
    (hd : d.val = min delay_samples.val (buffer.length - 1))
    (hw : w.val = position.val % buffer.length)
    (hrw : r.val + d.val = w.val ∨ r.val + d.val = w.val + buffer.length)
    (hr : r.val < buffer.length) :
    process_f64_loop buffer audio buffer.len w r 0#usize ⦃ buffer' position' audio' =>
      audio'.length = audio.length ∧
      (∀ j < audio.length, audio'.val[j]? =
        (buffer.val.rotate position.val ++ audio.val)[buffer.length + j -
          min delay_samples.val (buffer.length - 1)]?) ∧
      buffer'.length = buffer.length ∧
      position'.val = (position.val + audio.length) % buffer.length ∧
      buffer'.val.rotate position'.val =
        (buffer.val.rotate position.val ++ audio.val).drop audio.length ⦄ := by
  have hlen : buffer.len.val = buffer.length := Slice.len_val buffer
  have hbl : buffer.val.length = buffer.length := rfl
  have hwL : w.val < buffer.length := by rw [hw]; exact Nat.mod_lt _ hL
  have hS : (buffer.val.rotate position.val ++ audio.val).length =
      buffer.length + audio.length := by simp [List.length_rotate]
  apply WP.spec_mono (process_f64_loop_spec buffer.length d.val position.val audio.length
    (buffer.val.rotate position.val ++ audio.val) buffer.len hlen (by omega) buffer audio w r
    0#usize rfl rfl hwL hr hrw (by simp) (by simp [hw]) ?_ (by simp) ?_)
  · rintro ⟨b', p', a'⟩ ⟨hb', hp', hbS', ha', ha1'⟩
    simp only [WP.uncurry'_pair]
    refine ⟨ha', fun j hj => by rw [ha1' j hj, hd], hb', hp', ?_⟩
    exact rotate_eq_drop _ _ _ _ _ hS hb' (by rw [hp']; exact Nat.mod_lt _ hL) hbS'
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
`n = audio.length`, `d = min delay_samples (L - 1)` (the delay, clamped to at most `L - 1`) and
`H = buffer.rotate position ++ audio` (the buffer read in time order from `position`, taken mod
`L`, then the input). Then `process_f64` never fails, and its result `(buffer', position', audio')`
satisfies:
- `audio'` has `n` samples, and for every `j < n`, `audio'[j]? = H[L + j - d]?`: output sample
  `j` is element `L + j - d` of `H` (`process_f64_getElem` states this with `getElem`);
- `buffer'` has length `L`, and `position' = (position + n) mod L`;
- `buffer'.rotate position' = H.drop n`: the new buffer read in time order from the new position
  is the last `L` elements of `H`. -/
theorem process_f64_spec (buffer : Slice Float) (position delay_samples : Std.Usize)
    (audio : Slice Float) (hL : 0 < buffer.length) :
    process_f64 buffer position delay_samples audio ⦃ buffer' position' audio' =>
      audio'.length = audio.length ∧
      (∀ j < audio.length, audio'.val[j]? =
        (buffer.val.rotate position.val ++ audio.val)[buffer.length + j -
          min delay_samples.val (buffer.length - 1)]?) ∧
      buffer'.length = buffer.length ∧
      position'.val = (position.val + audio.length) % buffer.length ∧
      buffer'.val.rotate position'.val =
        (buffer.val.rotate position.val ++ audio.val).drop audio.length ⦄ := by
  unfold process_f64
  step*
  split <;> rename_i hdl <;> step* <;> split <;> rename_i hdw <;> step*
  all_goals first
    | (apply process_f64_from_start (d := delay_samples) <;> scalar_tac)
    | (apply process_f64_from_start (d := d) <;> scalar_tac)

/-- **The delay property.** The same as `process_f64_spec` when `delay_samples < L`, so that
`d = delay_samples`: for `L = buffer.length > 0`, `n = audio.length` and
`H = buffer.rotate position ++ audio`, `process_f64` never fails; `audio'` has `n` samples and
`audio'[j]? = H[L + j - delay_samples]?` for every `j < n` (the sample written `delay_samples`
samples earlier); `buffer'` has length `L`; `position' = (position + n) mod L`; and
`buffer'.rotate position' = H.drop n`, the last `L` elements of `H`. -/
theorem process_f64_spec_of_lt (buffer : Slice Float) (position delay_samples : Std.Usize)
    (audio : Slice Float) (hL : 0 < buffer.length) (hd : delay_samples.val < buffer.length) :
    process_f64 buffer position delay_samples audio ⦃ buffer' position' audio' =>
      audio'.length = audio.length ∧
      (∀ j < audio.length, audio'.val[j]? =
        (buffer.val.rotate position.val ++ audio.val)[buffer.length + j - delay_samples.val]?) ∧
      buffer'.length = buffer.length ∧
      position'.val = (position.val + audio.length) % buffer.length ∧
      buffer'.val.rotate position'.val =
        (buffer.val.rotate position.val ++ audio.val).drop audio.length ⦄ := by
  have hmin : min delay_samples.val (buffer.length - 1) = delay_samples.val := by omega
  simpa only [hmin] using process_f64_spec buffer position delay_samples audio hL

/-- **Output samples, with `getElem`.** For `L = buffer.length > 0`, `n = audio.length`,
`d = min delay_samples (L - 1)` and `H = buffer.rotate position ++ audio`: `process_f64` never
fails, `audio'` has `n` samples (`hn`), and for every `j < n`, `audio'[j] = H[L + j - d]`. Both
indices are in range, as the statement's index proofs show: `j < n`, the length of `audio'`, and
`L + j - d < L + n`, the length of `H`. -/
theorem process_f64_getElem (buffer : Slice Float) (position delay_samples : Std.Usize)
    (audio : Slice Float) (hL : 0 < buffer.length) :
    process_f64 buffer position delay_samples audio ⦃ _ _ audio' =>
      ∃ hn : audio'.length = audio.length, ∀ (j : ℕ) (hj : j < audio.length),
        audio'.val[j]'(by simp only [Slice.length] at hn hj ⊢; omega) =
          (buffer.val.rotate position.val ++ audio.val)[buffer.length + j -
            min delay_samples.val (buffer.length - 1)]'(by
              simp only [Slice.length] at hj ⊢; simp [List.length_rotate]; omega) ⦄ := by
  apply WP.spec_mono (process_f64_spec buffer position delay_samples audio hL)
  rintro ⟨buffer', position', audio'⟩ ⟨hn, hout, -⟩
  refine ⟨hn, fun j hj => ?_⟩
  have h := hout j hj
  simp only [Slice.length] at hn hj
  rw [List.getElem?_eq_getElem (by omega),
    List.getElem?_eq_getElem (by simp [List.length_rotate]; omega)] at h
  exact Option.some_inj.mp h

/-- **Silence first.** Let `L = buffer.length > 0`, `n = audio.length` and
`d = min delay_samples (L - 1)`. If every element of `buffer` is the float `0`, then
`process_f64` never fails and, for every `j < min d n`, output sample `j` is `0`
(`audio'[j]? = some 0`). -/
theorem process_f64_zero_prefix (buffer : Slice Float) (position delay_samples : Std.Usize)
    (audio : Slice Float) (hL : 0 < buffer.length) (hz : ∀ x ∈ buffer.val, x = 0) :
    process_f64 buffer position delay_samples audio ⦃ _ _ audio' =>
      ∀ j < min (min delay_samples.val (buffer.length - 1)) audio.length,
        audio'.val[j]? = some 0 ⦄ := by
  apply WP.spec_mono (process_f64_spec buffer position delay_samples audio hL)
  rintro ⟨buffer', position', audio'⟩ ⟨-, hout, -⟩ j hj
  have hR : (buffer.val.rotate position.val).length = buffer.length := by
    simp [List.length_rotate]
  rw [hout j (by omega), List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega),
    hz _ (List.mem_rotate.mp (List.getElem_mem _))]

/-- With an empty buffer (`buffer.length = 0`), `process_f64` never fails and returns the buffer,
position and audio unchanged. -/
theorem process_f64_empty_buffer (buffer : Slice Float) (position delay_samples : Std.Usize)
    (audio : Slice Float) (hL : buffer.length = 0) :
    process_f64 buffer position delay_samples audio = ok (buffer, position, audio) := by
  have h : Slice.len buffer = 0#usize := UScalar.eq_of_val_eq (by simp [hL])
  simp [process_f64, h]

/-- **Two blocks compose.** Let `audio` be `audio₁` followed by `audio₂`. Running `process_f64`
on `audio₁`, then on `audio₂` with the buffer and position the first call returned, never fails;
neither does one call on `audio` from the same starting buffer and position (every call with the
same `delay_samples`); and the two calls end with the same buffer and position as the one call,
and their output samples, joined, are its output samples. For any buffer, including an empty
one. -/
theorem process_f64_append (buffer : Slice Float) (position delay_samples : Std.Usize)
    (audio₁ audio₂ audio : Slice Float) (haudio : audio.val = audio₁.val ++ audio₂.val) :
    process_f64 buffer position delay_samples audio₁ ⦃ buffer₁ position₁ out₁ =>
      process_f64 buffer₁ position₁ delay_samples audio₂ ⦃ buffer₂ position₂ out₂ =>
        process_f64 buffer position delay_samples audio ⦃ buffer' position' out =>
          buffer₂ = buffer' ∧ position₂ = position' ∧ out₁.val ++ out₂.val = out.val ⦄ ⦄ ⦄ := by
  rcases Nat.eq_zero_or_pos buffer.length with hL | hL
  · simp [process_f64_empty_buffer _ _ _ _ hL, haudio]
  obtain ⟨⟨b₁, p₁, o₁⟩, e₁, hn₁, hout₁, hb₁, hp₁, hrot₁⟩ :=
    exists_ok_of_spec (process_f64_spec buffer position delay_samples audio₁ hL)
  obtain ⟨⟨b₂, p₂, o₂⟩, e₂, hn₂, hout₂, hb₂, hp₂, hrot₂⟩ :=
    exists_ok_of_spec (process_f64_spec b₁ p₁ delay_samples audio₂ (by omega))
  obtain ⟨⟨b, p, o⟩, e, hn, hout, hb, hp, hrot⟩ :=
    exists_ok_of_spec (process_f64_spec buffer position delay_samples audio hL)
  have hlen : audio.length = audio₁.length + audio₂.length := by
    simp only [Slice.length, haudio, List.length_append]
  rw [hb₁] at hout₂ hp₂
  rw [hlen] at hn hout hp hrot
  rw [hrot₁] at hout₂
  rw [hrot₁] at hrot₂
  rw [haudio, ← List.append_assoc] at hout hrot
  have hR : (buffer.val.rotate position.val).length = buffer.length := by
    simp [List.length_rotate]
  have hpos : p₂ = p := UScalar.eq_of_val_eq (by
    rw [hp₂, hp, hp₁, Nat.mod_add_mod, Nat.add_assoc])
  simp only [e₁, e₂, e, WP.spec_ok, WP.uncurry'_pair]
  refine ⟨(Slice.eq_iff _ _).mpr ?_, hpos, ?_⟩
  · rw [← List.rotate_eq_rotate (n := p₂.val), hrot₂, hpos, hrot,
      drop_append_drop _ _ _ _ (by simp)]
  · exact outputs_append _ _ _ _ _ _ _ _ hR (by omega) hn₁ hout₁ hn₂ hout₂ hn hout

/-- `process_f64` never fails, for every buffer, position, delay and audio: it returns a result,
with no panic, out-of-bounds index or index overflow, and it terminates. -/
theorem process_f64_ok (buffer : Slice Float) (position delay_samples : Std.Usize)
    (audio : Slice Float) : ∃ r, process_f64 buffer position delay_samples audio = ok r := by
  rcases Nat.eq_zero_or_pos buffer.length with h | h
  · exact ⟨_, process_f64_empty_buffer buffer position delay_samples audio h⟩
  · obtain ⟨r, hr, -⟩ := exists_ok_of_spec (process_f64_spec buffer position delay_samples audio h)
    exact ⟨r, hr⟩

/-- **The delay does not change the stored history.** For any buffer (empty or not), position and
audio, and any two delays `d₁` and `d₂`: `process_f64` with `d₁` and `process_f64` with `d₂`, from
the same buffer, position and audio, both never fail and return the same new buffer and the same
new position. Only their output samples may differ. -/
theorem process_f64_state_indep (buffer : Slice Float) (position d₁ d₂ : Std.Usize)
    (audio : Slice Float) :
    process_f64 buffer position d₁ audio ⦃ buffer₁ position₁ _ =>
      process_f64 buffer position d₂ audio ⦃ buffer₂ position₂ _ =>
        buffer₁ = buffer₂ ∧ position₁ = position₂ ⦄ ⦄ := by
  rcases Nat.eq_zero_or_pos buffer.length with hL | hL
  · simp [process_f64_empty_buffer _ _ _ _ hL]
  obtain ⟨⟨b₁, p₁, o₁⟩, e₁, -, -, -, hp₁, hrot₁⟩ :=
    exists_ok_of_spec (process_f64_spec buffer position d₁ audio hL)
  obtain ⟨⟨b₂, p₂, o₂⟩, e₂, -, -, -, hp₂, hrot₂⟩ :=
    exists_ok_of_spec (process_f64_spec buffer position d₂ audio hL)
  have hpos : p₁ = p₂ := UScalar.eq_of_val_eq (by rw [hp₁, hp₂])
  simp only [e₁, e₂, WP.spec_ok, WP.uncurry'_pair]
  refine ⟨(Slice.eq_iff _ _).mpr ?_, hpos⟩
  rw [← List.rotate_eq_rotate (n := p₁.val), hrot₁, hpos, hrot₂]

end conjure_dsp_lib.delay

end
