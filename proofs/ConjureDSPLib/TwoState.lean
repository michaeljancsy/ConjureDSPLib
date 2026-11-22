module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Filters with two state values: the shared real-number argument

The biquad (`Biquad/Block.lean`) and the state-variable filter (`Svf/Block.lean`) each keep two
state values, and one exact step updates them linearly: the new state is `A·s + b·x` for a 2 × 2
matrix `A` (the state-update map) and a pair `b`. If the computed state differs from the exact
one by `e`, one step changes that difference to `A·e + w`, where `w` comes from this step's
rounding. Whether such errors pile up depends on `A`.

`Contraction a₁₁ a₁₂ a₂₁ a₂₂` is a way `N` of measuring pairs under which the map
`v ↦ (a₁₁·v₁ + a₁₂·v₂, a₂₁·v₁ + a₂₂·v₂)` shrinks every pair by at least `ρ < 1`. The biquad's
`Contraction` is this structure at its companion matrix `(−a1, 1; −a2, 0)`, and the SVF's at its
matrix `(a11, a12; a21, a22)`.

This file holds the facts about a `Contraction` that both filters' whole-block arguments use:
- `Contraction.state_le`: if the exact state measures at most `R` and the error at most `Ê`,
  and `cInf·(R + Ê) ≤ Sb`, both computed state values are at most `Sb`;
- `Contraction.map_add_le`: if `N(v) ≤ B`, `|w₁| + |w₂| ≤ W` and `ρ·B + K·W ≤ B`, then
  `N(A·v + w) ≤ B`. It keeps both invariants of the induction: the exact state's bound `R` (with
  `w` the input's contribution) and the error's bound `Ê` (with `w` this step's rounding);
- `Contraction.exactBound_invariant`, `Contraction.errBound_invariant`: the closed forms
  `R = N(s) + K·G·M/(1 − ρ)` and `Ê = K·X/(1 − ρ)` satisfy `ρ·R + K·G·M ≤ R` and
  `ρ·Ê + K·X ≤ Ê`.
-/

@[expose] public section

namespace conjure_dsp_lib.two_state

/-- A way `N` of measuring pairs `(v₁, v₂)`, with `N` nonnegative and `N(u + v) ≤ N(u) + N(v)`,
under which the state-update map `(v₁, v₂) ↦ (a₁₁·v₁ + a₁₂·v₂, a₂₁·v₁ + a₂₂·v₂)` takes every pair
to one whose measure is at most `ρ` times the original's, with `0 ≤ ρ < 1`. `cInf ≥ 0` is the
constant comparing each entry with `N`: `|v₁| ≤ cInf·N(v₁, v₂)` and `|v₂| ≤ cInf·N(v₁, v₂)`.
`K ≥ 0` compares `N` with the entries' sizes: `N(v₁, v₂) ≤ K·(|v₁| + |v₂|)`. -/
structure Contraction (a₁₁ a₁₂ a₂₁ a₂₂ : ℝ) where
  /-- The measure of a pair. -/
  N : ℝ → ℝ → ℝ
  /-- How much the state-update map shrinks a pair. -/
  ρ : ℝ
  /-- Each entry is at most `cInf` times the measure. -/
  cInf : ℝ
  /-- The measure is at most `K` times the sum of the entries' sizes. -/
  K : ℝ
  nonneg : ∀ v₁ v₂, 0 ≤ N v₁ v₂
  add_le : ∀ u₁ u₂ v₁ v₂, N (u₁ + v₁) (u₂ + v₂) ≤ N u₁ u₂ + N v₁ v₂
  contract : ∀ v₁ v₂, N (a₁₁ * v₁ + a₁₂ * v₂) (a₂₁ * v₁ + a₂₂ * v₂) ≤ ρ * N v₁ v₂
  ρ_nonneg : 0 ≤ ρ
  cInf_nonneg : 0 ≤ cInf
  K_nonneg : 0 ≤ K
  ρ_lt_one : ρ < 1
  le_fst : ∀ v₁ v₂, |v₁| ≤ cInf * N v₁ v₂
  le_snd : ∀ v₁ v₂, |v₂| ≤ cInf * N v₁ v₂
  le_sum : ∀ v₁ v₂, N v₁ v₂ ≤ K * (|v₁| + |v₂|)

namespace Contraction

variable {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ} (C : Contraction a₁₁ a₁₂ a₂₁ a₂₂)

/-- If a pair measures at most `E`, its first entry is at most `cInf·E` in size. -/
theorem fst_le {E v₁ v₂ : ℝ} (h : C.N v₁ v₂ ≤ E) : |v₁| ≤ C.cInf * E :=
  (C.le_fst _ _).trans (mul_le_mul_of_nonneg_left h C.cInf_nonneg)

/-- If a pair measures at most `E`, its second entry is at most `cInf·E` in size. -/
theorem snd_le {E v₁ v₂ : ℝ} (h : C.N v₁ v₂ ≤ E) : |v₂| ≤ C.cInf * E :=
  (C.le_snd _ _).trans (mul_le_mul_of_nonneg_left h C.cInf_nonneg)

/-- The computed state is within `Sb`: if the exact state `(r₁, r₂)` measures at most `R`, the
error `(s₁ - r₁, s₂ - r₂)` (computed minus exact state) measures at most `Ê`, and
`cInf·(R + Ê) ≤ Sb`, then both computed state values `s₁`, `s₂` are at most `Sb` in size. -/
theorem state_le {Sb R Ê s₁ s₂ r₁ r₂ : ℝ}
    (hS : C.cInf * (R + Ê) ≤ Sb) (hr : C.N r₁ r₂ ≤ R) (he : C.N (s₁ - r₁) (s₂ - r₂) ≤ Ê) :
    |s₁| ≤ Sb ∧ |s₂| ≤ Sb := by
  constructor
  · calc |s₁| = |r₁ + (s₁ - r₁)| := by ring_nf
      _ ≤ |r₁| + |s₁ - r₁| := abs_add_le _ _
      _ ≤ C.cInf * R + C.cInf * Ê := add_le_add (C.fst_le hr) (C.fst_le he)
      _ ≤ Sb := by linarith
  · calc |s₂| = |r₂ + (s₂ - r₂)| := by ring_nf
      _ ≤ |r₂| + |s₂ - r₂| := abs_add_le _ _
      _ ≤ C.cInf * R + C.cInf * Ê := add_le_add (C.snd_le hr) (C.snd_le he)
      _ ≤ Sb := by linarith

/-- **One step keeps a bound on the measure.** If `v` measures at most `B`, `|w₁| + |w₂| ≤ W`
and `ρ·B + K·W ≤ B`, then `A·v + w` measures at most `B`. -/
theorem map_add_le {B W v₁ v₂ w₁ w₂ : ℝ} (hv : C.N v₁ v₂ ≤ B) (hw : |w₁| + |w₂| ≤ W)
    (hB : C.ρ * B + C.K * W ≤ B) :
    C.N (a₁₁ * v₁ + a₁₂ * v₂ + w₁) (a₂₁ * v₁ + a₂₂ * v₂ + w₂) ≤ B :=
  calc _ ≤ C.N (a₁₁ * v₁ + a₁₂ * v₂) (a₂₁ * v₁ + a₂₂ * v₂) + C.N w₁ w₂ := C.add_le _ _ _ _
    _ ≤ C.ρ * B + C.K * W := add_le_add
        ((C.contract _ _).trans (mul_le_mul_of_nonneg_left hv C.ρ_nonneg))
        ((C.le_sum _ _).trans (mul_le_mul_of_nonneg_left hw C.K_nonneg))
    _ ≤ B := hB

/-- The zero error `s − s` measures at most any `E ≥ 0`. -/
theorem sub_self_le {E s₁ s₂ : ℝ} (hE : 0 ≤ E) : C.N (s₁ - s₁) (s₂ - s₂) ≤ E := by
  have h0 := C.le_sum 0 0
  simp only [sub_self, abs_zero, add_zero, mul_zero] at h0 ⊢
  linarith

/-- `R = N(s) + K·G·M/(1 − ρ)` satisfies `ρ·R + K·G·M ≤ R`, for any `G` and `M`. -/
theorem exactBound_invariant (s₁ s₂ G M : ℝ) :
    C.ρ * (C.N s₁ s₂ + C.K * G * M / (1 - C.ρ)) + C.K * G * M ≤
      C.N s₁ s₂ + C.K * G * M / (1 - C.ρ) := by
  have h1ρ : 0 < 1 - C.ρ := by linarith [C.ρ_lt_one]
  have e : C.K * G * M = (1 - C.ρ) * (C.K * G * M / (1 - C.ρ)) := by field_simp
  nlinarith [C.ρ_nonneg, C.nonneg s₁ s₂]

/-- `Ê = K·X/(1 − ρ)` satisfies `ρ·Ê + K·X ≤ Ê`, for any `X`. -/
theorem errBound_invariant (X : ℝ) :
    C.ρ * (C.K * X / (1 - C.ρ)) + C.K * X ≤ C.K * X / (1 - C.ρ) := by
  have h1ρ : 0 < 1 - C.ρ := by linarith [C.ρ_lt_one]
  have e : C.K * X / (1 - C.ρ) * (1 - C.ρ) = C.K * X := by field_simp
  nlinarith

/-- The starting state `s` measures at most `R = N(s) + K·G·M/(1 − ρ)` when `0 ≤ G` and
`0 ≤ M`. -/
theorem le_exactBound (s₁ s₂ : ℝ) {G M : ℝ} (hG : 0 ≤ G) (hM : 0 ≤ M) :
    C.N s₁ s₂ ≤ C.N s₁ s₂ + C.K * G * M / (1 - C.ρ) := by
  have h1ρ : 0 < 1 - C.ρ := by linarith [C.ρ_lt_one]
  have := C.K_nonneg
  have : 0 ≤ C.K * G * M / (1 - C.ρ) := by positivity
  linarith

end Contraction

/-- The input's contribution `(b₁·x, b₂·x)` to the next state, for `|x| ≤ M`:
`|b₁·x| + |b₂·x| ≤ (|b₁| + |b₂|)·M`. -/
theorem abs_mul_add_abs_mul_le {b₁ b₂ x M : ℝ} (hx : |x| ≤ M) :
    |b₁ * x| + |b₂ * x| ≤ (|b₁| + |b₂|) * M := by
  rw [abs_mul, abs_mul, ← add_mul]
  exact mul_le_mul_of_nonneg_left hx (by positivity)

end conjure_dsp_lib.two_state

end
