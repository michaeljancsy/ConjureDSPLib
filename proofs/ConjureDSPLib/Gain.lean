module

public import ConjureDSPLib.Code.ConjureDspLib

/-!
# Gain

About `src/gain.rs`, as Aeneas translated it (into `ConjureDSPLib/Code/ConjureDspLib.lean`):

1. `apply_f64` and `apply_f32` are exactly Lean's `Float.mul` / `Float32.mul`, and never fail.
2. `ramp_f64_spec` / `ramp_f32_spec`: `ramp_f64` and `ramp_f32` never fail, and multiply each
   sample `i` of a block of `n` samples by exactly `start + ((end - start) / n) * i`, computed in
   binary64 / binary32 in that order, with `n` and `i` converted by `castNat_f64` /
   `castNat_f32` (Lean's own `Float.Model.ofNat`; `usize_toFloat_eq_castNat_*` shows this is the
   translated `as`) (`rampGain_f64`, `rampGain_f32`). These are statements about float
   operations, not about real numbers.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.gain

/-- The Rust `apply_f64` is `gain * x` on Lean's binary64 `Float`, and cannot fail. -/
theorem apply_f64_eq (gain x : Float) : apply_f64 gain x = ok (gain * x) := rfl

/-- The Rust `apply_f32` is `gain * x` on Lean's binary32 `Float32`, and cannot fail. -/
theorem apply_f32_eq (gain x : Float32) : apply_f32 gain x = ok (gain * x) := rfl

/-! ## The ramp in f64 -/

/-- A natural number converted to a binary64 value by Lean's own conversion `Float.Model.ofNat`
(whose definition in Lean core's float model rounds to nearest, ties to even; not proved here).
`usize_toFloat_eq_castNat_f64` shows it is the translated Rust `i as f64`. -/
def castNat_f64 (n : ℕ) : Float := Float.ofModel (Float.Model.ofNat n)

/-- The translation of Rust's `i as f64` for a `usize` is `castNat_f64` of its value. -/
theorem usize_toFloat_eq_castNat_f64 (i : Std.Usize) : UScalar.toFloat i = castNat_f64 i.val := by
  simp only [UScalar.toFloat, USize.toFloat, castNat_f64, Float.Model.ofUSize,
    Float.Model.ofNat, Float.Model.UnpackedFloat.ofUSize, USize.toNat_ofBitVec]
  rfl

/-- The gain of sample `i` in a block of `n` samples: `start + ((end - start) / n) * i` in
binary64, in the Rust code's order, with `n` and `i` rounded as `castNat_f64`. -/
def rampGain_f64 (start «end» : Float) (n i : ℕ) : Float :=
  start + ((«end» - start) / castNat_f64 n) * castNat_f64 i

/-- The ramp on a list of samples: sample `i` multiplied by `rampGain_f64` for the list's length.
(An empty list gives an empty list.) -/
def rampList_f64 (start «end» : Float) (xs : List Float) : List Float :=
  xs.mapIdx (fun i x => x * rampGain_f64 start «end» xs.length i)

/-- When `i ≤ buf.length`, the loop started at position `i` never fails, leaves the first `i`
samples as they are, and multiplies every later sample `k` by `start + step * castNat_f64 k`. -/
theorem ramp_f64_loop_spec (start step : Float) (buf : Slice Float) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    ramp_f64_loop start buf step i ⦃ fun r =>
      r.val = buf.val.mapIdx (fun k x =>
        if k < i.val then x else x * (start + step * castNat_f64 k)) ⦄ := by
  unfold ramp_f64_loop
  -- Invariant on the loop state `(b, j)`: the buffer keeps its length, the samples from `i` up
  -- to `j` are done, and the others are as they were at the start of the loop.
  apply loop.spec_decr_nat (fun x => x.1.length - x.2.val)
    (fun x => x.1.length = buf.length ∧ i.val ≤ x.2.val ∧ x.2.val ≤ x.1.length ∧
      x.1.val = buf.val.mapIdx (fun k x' =>
        if k < i.val ∨ x.2.val ≤ k then x' else x' * (start + step * castNat_f64 k)))
  · rintro ⟨b, j⟩ ⟨hlen, hij, hj, hb⟩
    simp only at hlen hij hj hb
    simp only [ramp_f64_loop.body, lift, usize_toFloat_eq_castNat_f64]
    step*
    · -- Still looping: sample `j` is now done.
      subst s_post fl1_post
      have hjl : j.val < b.length := by scalar_tac
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [i2_post]; omega
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]
        apply List.ext_getElem
        · simp [hb]
        · intro k hk1 hk2
          by_cases hkj : j.val = k
          · subst hkj
            have h1 : ¬ (j.val < i.val ∨ j.val + 1 ≤ j.val) := by omega
            have h2 : j.val < i.val ∨ j.val ≤ j.val := by omega
            simp only [List.getElem_set_self, List.getElem_mapIdx, hb, h1, h2, ite_true,
              ite_false]
            rfl
          · have h1 : (k < i.val ∨ j.val ≤ k) ↔ (k < i.val ∨ j.val + 1 ≤ k) := by omega
            rw [List.getElem_set_ne hkj]
            simp only [hb, List.getElem_mapIdx, h1]
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: every sample from `i` on is done.
      have hjl : j.val = b.length := by scalar_tac
      rw [hb]
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [List.getElem_mapIdx]
        have : ¬ (j.val ≤ k) := by simp [Slice.length] at hk1 hk2 hjl hlen; omega
        simp [this]
  · refine ⟨rfl, le_refl _, hi, ?_⟩
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      simp only [List.getElem_mapIdx]
      grind

/-- **The Rust `ramp_f64` never fails, and its output is exactly `rampList_f64`:** each sample
`i` of the block multiplied by `rampGain_f64 start end n i`, where `n` is the block's length,
in binary64. An empty block is returned unchanged. -/
theorem ramp_f64_spec (start «end» : Float) (buf : Slice Float) :
    ramp_f64 start «end» buf ⦃ fun r => r.val = rampList_f64 start «end» buf.val ⦄ := by
  unfold ramp_f64
  dsimp only
  split
  · rename_i h
    have h0 : buf.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      have := congrArg UScalar.val h
      simpa using this
    simp [h0, rampList_f64]
  · simp only [lift, usize_toFloat_eq_castNat_f64, bind_ok]
    apply WP.spec_mono (ramp_f64_loop_spec start _ buf 0#usize (by simp))
    intro r hr
    rw [hr]
    simp [rampList_f64, rampGain_f64]
    rfl

/-! ## The ramp in f32 -/

/-- A natural number converted to a binary32 value by Lean's own conversion `Float32.Model.ofNat`
(whose definition in Lean core's float model rounds to nearest, ties to even; not proved here).
`usize_toFloat32_eq_castNat_f32` shows it is the translated Rust `i as f32`. -/
def castNat_f32 (n : ℕ) : Float32 := Float32.ofModel (Float32.Model.ofNat n)

/-- The translation of Rust's `i as f32` for a `usize` is `castNat_f32` of its value. -/
theorem usize_toFloat32_eq_castNat_f32 (i : Std.Usize) :
    UScalar.toFloat32 i = castNat_f32 i.val := by
  simp only [UScalar.toFloat32, USize.toFloat32, castNat_f32, Float32.Model.ofUSize,
    Float32.Model.ofNat, Float.Model.UnpackedFloat.ofUSize, USize.toNat_ofBitVec]
  rfl

/-- The gain of sample `i` in a block of `n` samples: `start + ((end - start) / n) * i` in
binary32, in the Rust code's order, with `n` and `i` rounded as `castNat_f32`. -/
def rampGain_f32 (start «end» : Float32) (n i : ℕ) : Float32 :=
  start + ((«end» - start) / castNat_f32 n) * castNat_f32 i

/-- The ramp on a list of samples: sample `i` multiplied by `rampGain_f32` for the list's length.
(An empty list gives an empty list.) -/
def rampList_f32 (start «end» : Float32) (xs : List Float32) : List Float32 :=
  xs.mapIdx (fun i x => x * rampGain_f32 start «end» xs.length i)

/-- When `i ≤ buf.length`, the loop started at position `i` never fails, leaves the first `i`
samples as they are, and multiplies every later sample `k` by `start + step * castNat_f32 k`. -/
theorem ramp_f32_loop_spec (start step : Float32) (buf : Slice Float32) (i : Std.Usize)
    (hi : i.val ≤ buf.length) :
    ramp_f32_loop start buf step i ⦃ fun r =>
      r.val = buf.val.mapIdx (fun k x =>
        if k < i.val then x else x * (start + step * castNat_f32 k)) ⦄ := by
  unfold ramp_f32_loop
  -- Invariant on the loop state `(b, j)`: the buffer keeps its length, the samples from `i` up
  -- to `j` are done, and the others are as they were at the start of the loop.
  apply loop.spec_decr_nat (fun x => x.1.length - x.2.val)
    (fun x => x.1.length = buf.length ∧ i.val ≤ x.2.val ∧ x.2.val ≤ x.1.length ∧
      x.1.val = buf.val.mapIdx (fun k x' =>
        if k < i.val ∨ x.2.val ≤ k then x' else x' * (start + step * castNat_f32 k)))
  · rintro ⟨b, j⟩ ⟨hlen, hij, hj, hb⟩
    simp only at hlen hij hj hb
    simp only [ramp_f32_loop.body, lift, usize_toFloat32_eq_castNat_f32]
    step*
    · -- Still looping: sample `j` is now done.
      subst s_post fl1_post
      have hjl : j.val < b.length := by scalar_tac
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [hlen]
      · simp only [i2_post]; omega
      · simp only [Slice.set_length, i2_post]; omega
      · simp only [Slice.set_val_eq, i2_post]
        apply List.ext_getElem
        · simp [hb]
        · intro k hk1 hk2
          by_cases hkj : j.val = k
          · subst hkj
            have h1 : ¬ (j.val < i.val ∨ j.val + 1 ≤ j.val) := by omega
            have h2 : j.val < i.val ∨ j.val ≤ j.val := by omega
            simp only [List.getElem_set_self, List.getElem_mapIdx, hb, h1, h2, ite_true,
              ite_false]
            rfl
          · have h1 : (k < i.val ∨ j.val ≤ k) ↔ (k < i.val ∨ j.val + 1 ≤ k) := by omega
            rw [List.getElem_set_ne hkj]
            simp only [hb, List.getElem_mapIdx, h1]
      · simp only [Slice.set_length, i2_post]; omega
    · -- Finished: every sample from `i` on is done.
      have hjl : j.val = b.length := by scalar_tac
      rw [hb]
      apply List.ext_getElem
      · simp
      · intro k hk1 hk2
        simp only [List.getElem_mapIdx]
        have : ¬ (j.val ≤ k) := by simp [Slice.length] at hk1 hk2 hjl hlen; omega
        simp [this]
  · refine ⟨rfl, le_refl _, hi, ?_⟩
    apply List.ext_getElem
    · simp
    · intro k hk1 hk2
      simp only [List.getElem_mapIdx]
      grind

/-- **The Rust `ramp_f32` never fails, and its output is exactly `rampList_f32`:** each sample
`i` of the block multiplied by `rampGain_f32 start end n i`, where `n` is the block's length,
in binary32. An empty block is returned unchanged. -/
theorem ramp_f32_spec (start «end» : Float32) (buf : Slice Float32) :
    ramp_f32 start «end» buf ⦃ fun r => r.val = rampList_f32 start «end» buf.val ⦄ := by
  unfold ramp_f32
  dsimp only
  split
  · rename_i h
    have h0 : buf.val = [] := by
      apply List.eq_nil_of_length_eq_zero
      have := congrArg UScalar.val h
      simpa using this
    simp [h0, rampList_f32]
  · simp only [lift, usize_toFloat32_eq_castNat_f32, bind_ok]
    apply WP.spec_mono (ramp_f32_loop_spec start _ buf 0#usize (by simp))
    intro r hr
    rw [hr]
    simp [rampList_f32, rampGain_f32]
    rfl

end conjure_dsp_lib.gain
