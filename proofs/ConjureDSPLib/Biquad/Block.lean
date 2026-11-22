module

public import ConjureDSPLib.Biquad.Textbook
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# The biquad over a whole block: the real-number argument

The transposed-direct-form-II biquad keeps two state values. If the computed state differs from
the exact state by `e = (e₁, e₂)`, one step changes that difference to `T(e) + w`, where

`T(v₁, v₂) = (-a1·v₁ + v₂, -a2·v₁)`

is the state-update map (the filter's own, whose eigenvalues are its poles) and `w` comes from
this step's rounding. Whether such errors pile up depends on the state-update map. This file is
parametric in a `Contraction`: any way `N` of measuring a pair of numbers under which the
state-update map takes every pair to one whose measure is at most `ρ` times the original's, with
`0 ≤ ρ < 1`. `Biquad/Contraction.lean` gives one for biquads with complex poles, distinct real
poles or a repeated real pole, inside the unit circle.

With it, `block_error_real` shows that over a block of any length the computed outputs and state
stay within fixed distances of the exact filter's, provided the inputs are at most `M`, each
step's rounding is at most `α + β·Sb` while the state is within `Sb`, and `cInf·K·κ·β < 1 − ρ`
(κ = `roundGain` = `2 + |a1| + |a2|`). This file uses real numbers only; the floating-point and
Rust layers are in `BlockF64.lean` and `BlockF32.lean`.

`step_values_le` bounds the exact value of each of one step's nine operations by
`stepValueBound`; the floating-point files use it, with `block_step` and `block_state_le`, to
prove that no step overflows.

`block_bounds_le` and `block_bounds_ge` bound `computedStateBound` and the output error bound
`cInf·Ê + L` above and below from numbers on either side of `cInf`, `K` and `ρ`
(`stateBoundAt`, `outErrBoundAt`), and `smallness_fails` shows when `cInf·K·κ·β < 1 − ρ` is
false; with numbers checked by `norm_num` they give the worked examples in `BlockF64.lean` and
`BlockF32.lean`.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- A way `N` of measuring pairs `(v₁, v₂)`, with `N` nonnegative and `N(u + v) ≤ N(u) + N(v)`,
under which the biquad's state-update map `(v₁, v₂) ↦ (-a1·v₁ + v₂, -a2·v₁)` takes every pair to
one whose measure is at most `ρ` times the original's, with `0 ≤ ρ < 1`. `cInf ≥ 0` is the
constant comparing each entry with `N`: `|v₁| ≤ cInf·N(v₁, v₂)` and `|v₂| ≤ cInf·N(v₁, v₂)`.
`K ≥ 0` compares `N` with the entries' sizes: `N(v₁, v₂) ≤ K·(|v₁| + |v₂|)`. -/
structure Contraction (c : CoeffsReal) where
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
  contract : ∀ v₁ v₂, N (-c.a1 * v₁ + v₂) (-c.a2 * v₁) ≤ ρ * N v₁ v₂
  ρ_nonneg : 0 ≤ ρ
  cInf_nonneg : 0 ≤ cInf
  K_nonneg : 0 ≤ K
  ρ_lt_one : ρ < 1
  le_fst : ∀ v₁ v₂, |v₁| ≤ cInf * N v₁ v₂
  le_snd : ∀ v₁ v₂, |v₂| ≤ cInf * N v₁ v₂
  le_sum : ∀ v₁ v₂, N v₁ v₂ ≤ K * (|v₁| + |v₂|)

/-- `WithinLocalErr c Sb M L s xs f ys`: `ys` has one entry per input, and there are intermediate
states starting at `s` and ending at `f` such that, at every step where both state values are at
most `Sb` and the input at most `M`, the output and the two next state values each differ by at
most `L` from the exact step taken from that state and that output (`b0·x + s₁`,
`b1·x − a1·y + s₂`, `b2·x − a2·y`). -/
def WithinLocalErr (c : CoeffsReal) (Sb M L : ℝ) : ℝ × ℝ → List ℝ → ℝ × ℝ → List ℝ → Prop
  | s, [], f, [] => f = s
  | (s₁, s₂), x :: xs, f, y :: ys =>
    ∃ t₁ t₂ : ℝ,
      (|s₁| ≤ Sb → |s₂| ≤ Sb → |x| ≤ M →
        |y - (c.b0 * x + s₁)| ≤ L ∧ |t₁ - (c.b1 * x - c.a1 * y + s₂)| ≤ L ∧
          |t₂ - (c.b2 * x - c.a2 * y)| ≤ L) ∧
      WithinLocalErr c Sb M L (t₁, t₂) xs f ys
  | _, _, _, _ => False

/-- The size of one input's direct contribution to the next state, per unit of input:
`|b1 − a1·b0| + |b2 − a2·b0|`. -/
def inputGain (c : CoeffsReal) : ℝ := |c.b1 - c.a1 * c.b0| + |c.b2 - c.a2 * c.b0|

/-- `κ = 2 + |a1| + |a2|`: one step's roundings, each at most `L`, add at most `roundGain·L` to
`|w₁| + |w₂|`, where `w` is that step's contribution to the state error. -/
def roundGain (c : CoeffsReal) : ℝ := 2 + |c.a1| + |c.a2|

/-- The computed state is within `Sb`: if the exact state `(r₁, r₂)` measures at most `R`, the
error `(s₁ - r₁, s₂ - r₂)` (computed minus exact state) measures at most `Ê`, and
`cInf·(R + Ê) ≤ Sb`, then both computed state values `s₁`, `s₂` are at most `Sb` in size. -/
theorem block_state_le (c : CoeffsReal) (C : Contraction c) {Sb R Ê s₁ s₂ r₁ r₂ : ℝ}
    (hS : C.cInf * (R + Ê) ≤ Sb) (hr : C.N r₁ r₂ ≤ R) (he : C.N (s₁ - r₁) (s₂ - r₂) ≤ Ê) :
    |s₁| ≤ Sb ∧ |s₂| ≤ Sb := by
  have hci := C.cInf_nonneg
  constructor
  · have h1 := C.le_fst r₁ r₂
    have h2 := C.le_fst (s₁ - r₁) (s₂ - r₂)
    calc |s₁| = |r₁ + (s₁ - r₁)| := by ring_nf
      _ ≤ |r₁| + |s₁ - r₁| := abs_add_le _ _
      _ ≤ C.cInf * R + C.cInf * Ê := add_le_add
          (h1.trans (mul_le_mul_of_nonneg_left hr hci))
          (h2.trans (mul_le_mul_of_nonneg_left he hci))
      _ ≤ Sb := by linarith
  · have h1 := C.le_snd r₁ r₂
    have h2 := C.le_snd (s₁ - r₁) (s₂ - r₂)
    calc |s₂| = |r₂ + (s₂ - r₂)| := by ring_nf
      _ ≤ |r₂| + |s₂ - r₂| := abs_add_le _ _
      _ ≤ C.cInf * R + C.cInf * Ê := add_le_add
          (h1.trans (mul_le_mul_of_nonneg_left hr hci))
          (h2.trans (mul_le_mul_of_nonneg_left he hci))
      _ ≤ Sb := by linarith

/-- One step of the induction behind `block_error_real`. Suppose the exact state `(r₁, r₂)`
measures at most `R`, the error `(s₁ - r₁, s₂ - r₂)` (computed minus exact state) measures at
most `Ê`, the input `x` is at most `M`, and the computed output `y` and next state `(t₁, t₂)` are
each within `L` of the exact step from the computed state and the computed output
(`b0·x + s₁`, `b1·x − a1·y + s₂`, `b2·x − a2·y`). If `ρ·R + K·inputGain·M ≤ R` and
`ρ·Ê + K·L·κ ≤ Ê` (`κ = roundGain`), then, with `y' = b0·x + r₁` the exact output and
`(b1·x − a1·y' + r₂, b2·x − a2·y')` the exact next state, `y` is within `cInf·Ê + L` of `y'`,
the exact next state measures at most `R`, and the next error measures at most `Ê`. -/
theorem block_step (c : CoeffsReal) (C : Contraction c) {M L R Ê x s₁ s₂ r₁ r₂ y t₁ t₂ : ℝ}
    (hR : C.ρ * R + C.K * inputGain c * M ≤ R)
    (hE : C.ρ * Ê + C.K * (L * roundGain c) ≤ Ê)
    (hx : |x| ≤ M) (hr : C.N r₁ r₂ ≤ R) (he : C.N (s₁ - r₁) (s₂ - r₂) ≤ Ê)
    (hdy : |y - (c.b0 * x + s₁)| ≤ L) (hd₁ : |t₁ - (c.b1 * x - c.a1 * y + s₂)| ≤ L)
    (hd₂ : |t₂ - (c.b2 * x - c.a2 * y)| ≤ L) :
    |y - (c.b0 * x + r₁)| ≤ C.cInf * Ê + L ∧
      C.N (c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂) (c.b2 * x - c.a2 * (c.b0 * x + r₁)) ≤ R ∧
      C.N (t₁ - (c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂))
        (t₂ - (c.b2 * x - c.a2 * (c.b0 * x + r₁))) ≤ Ê := by
  have hci := C.cInf_nonneg
  set dy := y - (c.b0 * x + s₁) with hdy_def
  set d₁ := t₁ - (c.b1 * x - c.a1 * y + s₂) with hd₁_def
  set d₂ := t₂ - (c.b2 * x - c.a2 * y) with hd₂_def
  set e₁ := s₁ - r₁
  set e₂ := s₂ - r₂
  -- The new error is the state-update map applied to the old error, plus this step's
  -- rounding `w`.
  have hw₁ : |d₁ - c.a1 * dy| ≤ L + |c.a1| * L := by
    calc |d₁ - c.a1 * dy| ≤ |d₁| + |c.a1 * dy| := abs_sub _ _
      _ = |d₁| + |c.a1| * |dy| := by rw [abs_mul]
      _ ≤ L + |c.a1| * L := add_le_add hd₁ (mul_le_mul_of_nonneg_left hdy (abs_nonneg _))
  have hw₂ : |d₂ - c.a2 * dy| ≤ L + |c.a2| * L := by
    calc |d₂ - c.a2 * dy| ≤ |d₂| + |c.a2 * dy| := abs_sub _ _
      _ = |d₂| + |c.a2| * |dy| := by rw [abs_mul]
      _ ≤ L + |c.a2| * L := add_le_add hd₂ (mul_le_mul_of_nonneg_left hdy (abs_nonneg _))
  have he' : C.N (t₁ - (c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂))
      (t₂ - (c.b2 * x - c.a2 * (c.b0 * x + r₁))) ≤ Ê := by
    have e1 : t₁ - (c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂) =
        (-c.a1 * e₁ + e₂) + (d₁ - c.a1 * dy) := by
      simp only [hd₁_def, hdy_def, e₁, e₂]; ring
    have e2 : t₂ - (c.b2 * x - c.a2 * (c.b0 * x + r₁)) =
        (-c.a2 * e₁) + (d₂ - c.a2 * dy) := by
      simp only [hd₂_def, hdy_def, e₁]; ring
    rw [e1, e2]
    calc C.N ((-c.a1 * e₁ + e₂) + (d₁ - c.a1 * dy)) ((-c.a2 * e₁) + (d₂ - c.a2 * dy))
        ≤ C.N (-c.a1 * e₁ + e₂) (-c.a2 * e₁) + C.N (d₁ - c.a1 * dy) (d₂ - c.a2 * dy) :=
          C.add_le _ _ _ _
      _ ≤ C.ρ * Ê + C.K * (L * roundGain c) := by
          refine add_le_add ((C.contract _ _).trans
            (mul_le_mul_of_nonneg_left he C.ρ_nonneg)) ?_
          refine (C.le_sum _ _).trans (mul_le_mul_of_nonneg_left ?_ C.K_nonneg)
          unfold roundGain
          linarith
      _ ≤ Ê := hE
  -- The exact state stays within `R`.
  have hr' : C.N (c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂) (c.b2 * x - c.a2 * (c.b0 * x + r₁))
      ≤ R := by
    have e1 : c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂ =
        (-c.a1 * r₁ + r₂) + (c.b1 - c.a1 * c.b0) * x := by ring
    have e2 : c.b2 * x - c.a2 * (c.b0 * x + r₁) = (-c.a2 * r₁) + (c.b2 - c.a2 * c.b0) * x := by
      ring
    rw [e1, e2]
    calc C.N ((-c.a1 * r₁ + r₂) + (c.b1 - c.a1 * c.b0) * x)
          ((-c.a2 * r₁) + (c.b2 - c.a2 * c.b0) * x)
        ≤ C.N (-c.a1 * r₁ + r₂) (-c.a2 * r₁) +
            C.N ((c.b1 - c.a1 * c.b0) * x) ((c.b2 - c.a2 * c.b0) * x) := C.add_le _ _ _ _
      _ ≤ C.ρ * R + C.K * inputGain c * M := by
          refine add_le_add ((C.contract _ _).trans
            (mul_le_mul_of_nonneg_left hr C.ρ_nonneg)) ?_
          refine (C.le_sum _ _).trans ?_
          unfold inputGain
          rw [abs_mul, abs_mul, ← add_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hx (by positivity)) C.K_nonneg
      _ ≤ R := hR
  -- The output's error is the first state error plus this step's output rounding.
  have hy : |y - (c.b0 * x + r₁)| ≤ C.cInf * Ê + L := by
    have e : y - (c.b0 * x + r₁) = e₁ + dy := by simp only [hdy_def, e₁]; ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add
      ((C.le_fst _ _).trans (mul_le_mul_of_nonneg_left he hci)) hdy)
  exact ⟨hy, hr', he'⟩

/-- The induction behind `block_error_real`. Two bounds hold at every step: the exact state
`r` measures at most `R`, and the error `s - r` (computed minus exact state) measures at most
`Ê`. The three inequalities make them invariant: the first keeps the exact state bounded
(stability), the second keeps the error bounded, and the third keeps the computed state within
`Sb`, where each step's rounding is at most `L`. -/
theorem block_error_core (c : CoeffsReal) (C : Contraction c) (Sb M L R Ê : ℝ)
    (hR : C.ρ * R + C.K * inputGain c * M ≤ R)
    (hE : C.ρ * Ê + C.K * (L * roundGain c) ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb) :
    ∀ (xs : List ℝ) (s r f : ℝ × ℝ) (ys : List ℝ),
      (∀ x ∈ xs, |x| ≤ M) → C.N r.1 r.2 ≤ R → C.N (s.1 - r.1) (s.2 - r.2) ≤ Ê →
      WithinLocalErr c Sb M L s xs f ys →
      List.Forall₂ (fun y e => |y - e| ≤ C.cInf * Ê + L) ys (filt_real c r xs).2 ∧
        |f.1 - (filt_real c r xs).1.1| ≤ C.cInf * Ê ∧
        |f.2 - (filt_real c r xs).1.2| ≤ C.cInf * Ê := by
  intro xs
  induction xs with
  | nil =>
    intro s r f ys _ _ he hw
    cases ys with
    | nil =>
      obtain ⟨s₁, s₂⟩ := s
      simp only [WithinLocalErr] at hw
      subst hw
      refine ⟨List.Forall₂.nil, ?_, ?_⟩
      · exact (C.le_fst _ _).trans (mul_le_mul_of_nonneg_left he C.cInf_nonneg)
      · exact (C.le_snd _ _).trans (mul_le_mul_of_nonneg_left he C.cInf_nonneg)
    | cons => obtain ⟨s₁, s₂⟩ := s; simp [WithinLocalErr] at hw
  | cons x xs ih =>
    intro s r f ys hM hr he hw
    obtain ⟨s₁, s₂⟩ := s
    obtain ⟨r₁, r₂⟩ := r
    cases ys with
    | nil => simp [WithinLocalErr] at hw
    | cons y ys =>
      simp only [WithinLocalErr] at hw
      obtain ⟨t₁, t₂, hloc, hrest⟩ := hw
      simp only at hr he
      have hx : |x| ≤ M := hM x (by simp)
      -- The computed state is within `Sb`, so this step's roundings are at most `L`.
      obtain ⟨hs₁, hs₂⟩ := block_state_le c C hS hr he
      obtain ⟨hdy, hd₁, hd₂⟩ := hloc hs₁ hs₂ hx
      obtain ⟨hy, hr', he'⟩ := block_step c C hR hE hx hr he hdy hd₁ hd₂
      obtain ⟨h1, h2, h3⟩ := ih (t₁, t₂)
        (c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂, c.b2 * x - c.a2 * (c.b0 * x + r₁)) f ys
        (fun z hz => hM z (List.mem_cons_of_mem _ hz)) hr' he' hrest
      exact ⟨List.Forall₂.cons hy h1, h2, h3⟩

/-- `R = N(s) + K·inputGain·M/(1 − ρ)`: a bound on the measure `N` of the exact filter's state,
from start `s` with inputs at most `M` (an invariant of the proof's induction; not part of
`block_error_real`'s conclusion). -/
noncomputable def exactStateBound (c : CoeffsReal) (C : Contraction c) (M : ℝ) (s : ℝ × ℝ) : ℝ :=
  C.N s.1 s.2 + C.K * inputGain c * M / (1 - C.ρ)

/-- `Sb = cInf·(R·(1 − ρ) + K·κ·α)/(1 − ρ − cInf·K·κ·β)`, with `R = exactStateBound` and
`κ = roundGain`: a bound on each computed state value, when one step's roundings are at most
`α + β·Sb` (an invariant of the proof's induction; not part of `block_error_real`'s
conclusion). -/
noncomputable def computedStateBound (c : CoeffsReal) (C : Contraction c) (M α β : ℝ)
    (s : ℝ × ℝ) : ℝ :=
  C.cInf * (exactStateBound c C M s * (1 - C.ρ) + C.K * roundGain c * α) /
    (1 - C.ρ - C.cInf * C.K * roundGain c * β)

/-- `L = α + β·Sb`, with `Sb = computedStateBound`: the bound on one step's roundings. -/
noncomputable def localErrBound (c : CoeffsReal) (C : Contraction c) (M α β : ℝ)
    (s : ℝ × ℝ) : ℝ :=
  α + β * computedStateBound c C M α β s

/-- `Ê = K·L·κ/(1 − ρ)`, with `L = localErrBound` and `κ = roundGain`: a bound on the measure
`N` of the state error, computed minus exact (an invariant of the proof's induction; not part of
`block_error_real`'s conclusion, which bounds each state value by `cInf·Ê`). -/
noncomputable def stateErrBound (c : CoeffsReal) (C : Contraction c) (M α β : ℝ)
    (s : ℝ × ℝ) : ℝ :=
  C.K * (localErrBound c C M α β s * roundGain c) / (1 - C.ρ)

/-- `R = exactStateBound`, `Sb = computedStateBound`, `L = localErrBound` and
`Ê = stateErrBound` satisfy what `block_step` and `block_state_le` need, when `0 ≤ M`, `0 ≤ α`,
`0 ≤ β` and `cInf·K·κ·β < 1 − ρ` (`κ = roundGain`): `ρ·R + K·inputGain·M ≤ R`,
`ρ·Ê + K·L·κ ≤ Ê`, `cInf·(R + Ê) ≤ Sb`, the starting state `s` measures at most `R`, and the
zero error `s − s` measures at most `Ê`. -/
theorem block_constants (c : CoeffsReal) (C : Contraction c) (M α β : ℝ) (s : ℝ × ℝ)
    (hM0 : 0 ≤ M) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : C.cInf * C.K * roundGain c * β < 1 - C.ρ) :
    let R := exactStateBound c C M s
    let Sb := computedStateBound c C M α β s
    let L := localErrBound c C M α β s
    let Ê := stateErrBound c C M α β s
    C.ρ * R + C.K * inputGain c * M ≤ R ∧ C.ρ * Ê + C.K * (L * roundGain c) ≤ Ê ∧
      C.cInf * (R + Ê) ≤ Sb ∧ C.N s.1 s.2 ≤ R ∧ C.N (s.1 - s.1) (s.2 - s.2) ≤ Ê := by
  intro R Sb L Ê
  have hρ := C.ρ_lt_one
  have h1ρ : 0 < 1 - C.ρ := by linarith
  have hK := C.K_nonneg
  have hci := C.cInf_nonneg
  have hG : 0 ≤ inputGain c := by unfold inputGain; positivity
  have hκ : 0 ≤ roundGain c := by unfold roundGain; positivity
  have hD : 0 < 1 - C.ρ - C.cInf * C.K * roundGain c * β := by linarith
  have hRdef : R = exactStateBound c C M s := rfl
  have hSbdef : Sb = computedStateBound c C M α β s := rfl
  have hN0 : 0 ≤ C.N s.1 s.2 := C.nonneg _ _
  -- The three invariance conditions of `block_error_core`.
  have hR : C.ρ * R + C.K * inputGain c * M ≤ R := by
    have e : C.K * inputGain c * M = (1 - C.ρ) * (C.K * inputGain c * M / (1 - C.ρ)) := by
      field_simp
    have : R = C.N s.1 s.2 + C.K * inputGain c * M / (1 - C.ρ) := rfl
    nlinarith [C.ρ_nonneg]
  have hLdef : L = α + β * Sb := rfl
  have hEdef : Ê * (1 - C.ρ) = C.K * (L * roundGain c) := by
    simp only [Ê, L, stateErrBound]; field_simp
  have hE : C.ρ * Ê + C.K * (L * roundGain c) ≤ Ê := by
    nlinarith [hEdef]
  have hSbeq : Sb * (1 - C.ρ - C.cInf * C.K * roundGain c * β) =
      C.cInf * (R * (1 - C.ρ) + C.K * roundGain c * α) := by
    simp only [hSbdef, hRdef, computedStateBound]; field_simp
  have hS : C.cInf * (R + Ê) ≤ Sb := by
    -- Ê·(1-ρ) = K·(α + β·Sb)·κ, and Sb·(1-ρ-cInf·K·κ·β) = cInf·(R·(1-ρ) + K·κ·α).
    have hE' : Ê * (1 - C.ρ) = C.K * roundGain c * α + C.K * roundGain c * β * Sb := by
      rw [hEdef, hLdef]; ring
    have key : C.cInf * (R + Ê) * (1 - C.ρ) = Sb * (1 - C.ρ) := by
      linear_combination C.cInf * hE' - hSbeq
    exact le_of_eq (mul_right_cancel₀ h1ρ.ne' key)
  have hr : C.N s.1 s.2 ≤ R := by
    rw [hRdef]; unfold exactStateBound
    have : 0 ≤ C.K * inputGain c * M / (1 - C.ρ) := by positivity
    linarith
  have hR0 : 0 ≤ R := hN0.trans hr
  have he : C.N (s.1 - s.1) (s.2 - s.2) ≤ Ê := by
    have h0 := C.le_sum 0 0
    simp only [sub_self, abs_zero, add_zero, mul_zero] at h0 ⊢
    have hE0 : 0 ≤ Ê := by
      have : 0 ≤ Ê * (1 - C.ρ) := by
        rw [hEdef]
        have hL0 : 0 ≤ L := by
          rw [hLdef]
          have : 0 ≤ Sb := by
            rw [hSbdef]; unfold computedStateBound
            have : 0 ≤ C.cInf * (R * (1 - C.ρ) + C.K * roundGain c * α) := by positivity
            exact div_nonneg this hD.le
          positivity
        positivity
      exact nonneg_of_mul_nonneg_left this h1ρ
    linarith
  exact ⟨hR, hE, hS, hr, he⟩

/-- **Whole-block error of the biquad, on real numbers.** Let `C` be a `Contraction`, and
suppose `0 ≤ M`, `0 ≤ α`, `0 ≤ β`, every input in `xs` is at most `M`,
`WithinLocalErr c Sb M L s xs f ys` holds with `Sb = computedStateBound c C M α β s` and
`L = localErrBound c C M α β s`, and `cInf·K·κ·β < 1 − ρ` with `κ = roundGain c`. Then, with
`Ê = stateErrBound c C M α β s`, for a list `xs` of any length, `ys` and the outputs of
`filt_real c s xs` have the same length and each `y` in `ys` is within `cInf·Ê + L` of the
corresponding exact output, and each of `f`'s two values is within `cInf·Ê` of the
corresponding value of `filt_real c s xs`'s final state. -/
theorem block_error_real (c : CoeffsReal) (C : Contraction c) (M α β : ℝ) (hM0 : 0 ≤ M)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : C.cInf * C.K * roundGain c * β < 1 - C.ρ)
    (xs : List ℝ) (s f : ℝ × ℝ) (ys : List ℝ) (hM : ∀ x ∈ xs, |x| ≤ M)
    (hw : WithinLocalErr c (computedStateBound c C M α β s) M (localErrBound c C M α β s)
      s xs f ys) :
    let Ê := stateErrBound c C M α β s
    let L := localErrBound c C M α β s
    List.Forall₂ (fun y e => |y - e| ≤ C.cInf * Ê + L) ys (filt_real c s xs).2 ∧
      |f.1 - (filt_real c s xs).1.1| ≤ C.cInf * Ê ∧
      |f.2 - (filt_real c s xs).1.2| ≤ C.cInf * Ê := by
  intro Ê L
  obtain ⟨hR, hE, hS, hr, he⟩ := block_constants c C M α β s hM0 hα hβ hsmall
  exact block_error_core c C _ M L _ Ê hR hE hS xs s s f ys hM hr he hw

/-- `α`: the part of the bound on one step's roundings that does not grow with the state,
for unit roundoff `u`, underflow error `η` and inputs at most `M`:
`7·u·((|b0| + |b1| + |b2|)·M + 4·(|a1| + |a2|)·|b0|·M + (3·(|a1| + |a2|) + 1)·η) + 4·η`. -/
noncomputable def localErrBase (c : CoeffsReal) (u η M : ℝ) : ℝ :=
  7 * u * ((|c.b0| + |c.b1| + |c.b2|) * M + 4 * (|c.a1| + |c.a2|) * |c.b0| * M +
    (3 * (|c.a1| + |c.a2|) + 1) * η) + 4 * η

/-- `β`: how fast the bound on one step's roundings grows with the state bound `Sb`, for unit
roundoff `u`: `7·u·(2·(|a1| + |a2|) + 1)`. -/
noncomputable def localErrSlope (c : CoeffsReal) (u : ℝ) : ℝ :=
  7 * u * (2 * (|c.a1| + |c.a2|) + 1)

/-- `localErrBase` is nonnegative. -/
theorem localErrBase_nonneg (c : CoeffsReal) {u η M : ℝ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hM : 0 ≤ M) : 0 ≤ localErrBase c u η M := by
  unfold localErrBase; positivity

/-- `localErrSlope` is nonnegative. -/
theorem localErrSlope_nonneg (c : CoeffsReal) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ localErrSlope c u := by
  unfold localErrSlope; positivity

/-- `localErrBase` is positive when `η > 0`. -/
theorem localErrBase_pos (c : CoeffsReal) {u η M : ℝ} (hu : 0 ≤ u) (hη : 0 < η)
    (hM : 0 ≤ M) : 0 < localErrBase c u η M := by
  unfold localErrBase; positivity

/-- One rounding `r` of an exact value `e` with `|e| ≤ E`, within `u·|e| + η` of `e`, is within
`u·E + η` of `e` and at most `2·E + η` in size (when `0 ≤ u ≤ 1`). -/
theorem round_bounds {r e E u η : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (h : |r - e| ≤ u * |e| + η) (hE : |e| ≤ E) :
    |r - e| ≤ u * E + η ∧ |r| ≤ 2 * E + η := by
  have h1 := mul_le_mul_of_nonneg_left hE hu0
  have hE0 : 0 ≤ E := (abs_nonneg _).trans hE
  have h2 : u * E ≤ 1 * E := mul_le_mul_of_nonneg_right hu1 hE0
  have h3 : |r| ≤ |r - e| + |e| := by
    have := abs_add_le (r - e) e
    rwa [sub_add_cancel] at this
  constructor <;> linarith

/-- **One step's roundings, on real numbers.** One transposed-direct-form-II step computed with
nine roundings, each within `u·|e| + η` of the exact operation `e` on the computed operands:
`P0 ≈ b0·X`, output `Y ≈ P0 + S1`, `P1 ≈ b1·X`, `Q1 ≈ a1·Y`, `D1 ≈ P1 - Q1`, new state
`T1 ≈ D1 + S2`, `P2 ≈ b2·X`, `Q2 ≈ a2·Y`, new state `T2 ≈ P2 - Q2`. If `0 ≤ u ≤ 1`, `0 ≤ η`,
`|X| ≤ M` and `|S1|, |S2| ≤ Sb`, then `Y`, `T1` and `T2` are each within
`localErrBase c u η M + localErrSlope c u · Sb` of the exact step from the computed state and
the computed output: `b0·X + S1`, `b1·X - a1·Y + S2` and `b2·X - a2·Y`. -/
theorem step_localErr (c : CoeffsReal) {u η M Sb X S1 S2 P0 Y P1 Q1 D1 T1 P2 Q2 T2 : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hη : 0 ≤ η)
    (hX : |X| ≤ M) (hS1 : |S1| ≤ Sb) (hS2 : |S2| ≤ Sb)
    (hP0 : |P0 - c.b0 * X| ≤ u * |c.b0 * X| + η)
    (hY : |Y - (P0 + S1)| ≤ u * |P0 + S1| + η)
    (hP1 : |P1 - c.b1 * X| ≤ u * |c.b1 * X| + η)
    (hQ1 : |Q1 - c.a1 * Y| ≤ u * |c.a1 * Y| + η)
    (hD1 : |D1 - (P1 - Q1)| ≤ u * |P1 - Q1| + η)
    (hT1 : |T1 - (D1 + S2)| ≤ u * |D1 + S2| + η)
    (hP2 : |P2 - c.b2 * X| ≤ u * |c.b2 * X| + η)
    (hQ2 : |Q2 - c.a2 * Y| ≤ u * |c.a2 * Y| + η)
    (hT2 : |T2 - (P2 - Q2)| ≤ u * |P2 - Q2| + η) :
    let L := localErrBase c u η M + localErrSlope c u * Sb
    |Y - (c.b0 * X + S1)| ≤ L ∧ |T1 - (c.b1 * X - c.a1 * Y + S2)| ≤ L ∧
      |T2 - (c.b2 * X - c.a2 * Y)| ≤ L := by
  intro L
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hX
  have hSb : 0 ≤ Sb := (abs_nonneg _).trans hS1
  have hbX : ∀ b : ℝ, |b * X| ≤ |b| * M := fun b => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hX (abs_nonneg _)
  -- The output.
  obtain ⟨e0, p0⟩ := round_bounds hu0 hu1 hP0 (hbX c.b0)
  have z0 : |P0 + S1| ≤ 2 * (|c.b0| * M) + η + Sb := by
    have := abs_add_le P0 S1; linarith
  obtain ⟨eY, yb⟩ := round_bounds hu0 hu1 hY z0
  have dy : |Y - (c.b0 * X + S1)| ≤ |Y - (P0 + S1)| + |P0 - c.b0 * X| := by
    have := abs_add_le (Y - (P0 + S1)) (P0 - c.b0 * X)
    rwa [show Y - (P0 + S1) + (P0 - c.b0 * X) = Y - (c.b0 * X + S1) by ring] at this
  have haY : ∀ a : ℝ, |a * Y| ≤ |a| * (2 * (2 * (|c.b0| * M) + η + Sb) + η) := fun a => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left yb (abs_nonneg _)
  -- The first new state value: four roundings.
  obtain ⟨e1, p1⟩ := round_bounds hu0 hu1 hP1 (hbX c.b1)
  obtain ⟨f1, q1⟩ := round_bounds hu0 hu1 hQ1 (haY c.a1)
  have z1 : |P1 - Q1| ≤ 2 * (|c.b1| * M) + η +
      (2 * (|c.a1| * (2 * (2 * (|c.b0| * M) + η + Sb) + η)) + η) := by
    have := abs_sub P1 Q1; linarith
  obtain ⟨g1, d1⟩ := round_bounds hu0 hu1 hD1 z1
  have w1 : |D1 + S2| ≤ 2 * (2 * (|c.b1| * M) + η +
      (2 * (|c.a1| * (2 * (2 * (|c.b0| * M) + η + Sb) + η)) + η)) + η + Sb := by
    have := abs_add_le D1 S2; linarith
  obtain ⟨h1, -⟩ := round_bounds hu0 hu1 hT1 w1
  have dt1 : |T1 - (c.b1 * X - c.a1 * Y + S2)| ≤ |T1 - (D1 + S2)| + |D1 - (P1 - Q1)| +
      |P1 - c.b1 * X| + |Q1 - c.a1 * Y| := by
    have k := abs_add_three (T1 - (D1 + S2)) (D1 - (P1 - Q1)) (P1 - c.b1 * X)
    have k' := abs_sub (T1 - (D1 + S2) + (D1 - (P1 - Q1)) + (P1 - c.b1 * X))
      (Q1 - c.a1 * Y)
    rw [show T1 - (D1 + S2) + (D1 - (P1 - Q1)) + (P1 - c.b1 * X) - (Q1 - c.a1 * Y) =
      T1 - (c.b1 * X - c.a1 * Y + S2) by ring] at k'
    linarith
  -- The second new state value: three roundings.
  obtain ⟨e2, p2⟩ := round_bounds hu0 hu1 hP2 (hbX c.b2)
  obtain ⟨f2, q2⟩ := round_bounds hu0 hu1 hQ2 (haY c.a2)
  have z2 : |P2 - Q2| ≤ 2 * (|c.b2| * M) + η +
      (2 * (|c.a2| * (2 * (2 * (|c.b0| * M) + η + Sb) + η)) + η) := by
    have := abs_sub P2 Q2; linarith
  obtain ⟨g2, -⟩ := round_bounds hu0 hu1 hT2 z2
  have dt2 : |T2 - (c.b2 * X - c.a2 * Y)| ≤ |T2 - (P2 - Q2)| + |P2 - c.b2 * X| +
      |Q2 - c.a2 * Y| := by
    have k := abs_add_le (T2 - (P2 - Q2)) (P2 - c.b2 * X)
    have k' := abs_sub (T2 - (P2 - Q2) + (P2 - c.b2 * X)) (Q2 - c.a2 * Y)
    rw [show T2 - (P2 - Q2) + (P2 - c.b2 * X) - (Q2 - c.a2 * Y) =
      T2 - (c.b2 * X - c.a2 * Y) by ring] at k'
    linarith
  -- Every monomial of `L` is nonnegative.
  have hb0 := abs_nonneg c.b0
  have hb1 := abs_nonneg c.b1
  have hb2 := abs_nonneg c.b2
  have ha1 := abs_nonneg c.a1
  have ha2 := abs_nonneg c.a2
  have m1 : 0 ≤ u * |c.b0| * M := by positivity
  have m2 : 0 ≤ u * |c.b1| * M := by positivity
  have m3 : 0 ≤ u * |c.b2| * M := by positivity
  have m4 : 0 ≤ u * |c.a1| * |c.b0| * M := by positivity
  have m5 : 0 ≤ u * |c.a2| * |c.b0| * M := by positivity
  have m6 : 0 ≤ u * |c.a1| * η := by positivity
  have m7 : 0 ≤ u * |c.a2| * η := by positivity
  have m8 : 0 ≤ u * |c.a1| * Sb := by positivity
  have m9 : 0 ≤ u * |c.a2| * Sb := by positivity
  have m10 : 0 ≤ u * η := by positivity
  have m11 : 0 ≤ u * Sb := by positivity
  simp only [L, localErrBase, localErrSlope]
  refine ⟨by linarith, by linarith, by linarith⟩

/-- `V`: a bound on the exact value of each of the nine operations of one step (by
`step_values_le`), for underflow error `η`, inputs at most `M` and state values at most `Sb`:
`4·(|b0| + |b1| + |b2|)·M + 4·(|a1| + |a2|)·(4·|b0|·M + 2·Sb + 3·η) + Sb + 5·η`. -/
noncomputable def stepValueBound (c : CoeffsReal) (η M Sb : ℝ) : ℝ :=
  4 * (|c.b0| + |c.b1| + |c.b2|) * M + 4 * (|c.a1| + |c.a2|) * (4 * |c.b0| * M + 2 * Sb + 3 * η) +
    Sb + 5 * η

/-- **One step's exact operation values, on real numbers.** With the names of `step_localErr`
(`P0 ≈ b0·X`, `Y ≈ P0 + S1`, `P1 ≈ b1·X`, `Q1 ≈ a1·Y`, `D1 ≈ P1 - Q1`, `P2 ≈ b2·X`,
`Q2 ≈ a2·Y`, each rounding within `u·|e| + η` of its exact operation
`e`): if `0 ≤ u ≤ 1`, `0 ≤ η`, `|X| ≤ M` and `|S1|, |S2| ≤ Sb`, then the exact value of each of
the nine operations, computed from the earlier rounded results, is at most
`V = stepValueBound c η M Sb` in size. Each bound assumes only the roundings that come before
that operation: `b0·X`, `b1·X` and `b2·X` none; `P0 + S1` that of `P0`; `a1·Y` and `a2·Y` those
of `P0` and `Y`; `P1 - Q1` also those of `P1` and `Q1`; `D1 + S2` also that of `D1`; `P2 - Q2`
those of `P0`, `Y`, `P2` and `Q2`. -/
theorem step_values_le (c : CoeffsReal) {u η M Sb X S1 S2 P0 Y P1 Q1 D1 P2 Q2 : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hη : 0 ≤ η)
    (hX : |X| ≤ M) (hS1 : |S1| ≤ Sb) (hS2 : |S2| ≤ Sb) :
    let V := stepValueBound c η M Sb
    |c.b0 * X| ≤ V ∧ |c.b1 * X| ≤ V ∧ |c.b2 * X| ≤ V ∧
      (|P0 - c.b0 * X| ≤ u * |c.b0 * X| + η → |P0 + S1| ≤ V ∧
        (|Y - (P0 + S1)| ≤ u * |P0 + S1| + η → |c.a1 * Y| ≤ V ∧ |c.a2 * Y| ≤ V ∧
          (|P1 - c.b1 * X| ≤ u * |c.b1 * X| + η → |Q1 - c.a1 * Y| ≤ u * |c.a1 * Y| + η →
            |P1 - Q1| ≤ V ∧ (|D1 - (P1 - Q1)| ≤ u * |P1 - Q1| + η → |D1 + S2| ≤ V)) ∧
          (|P2 - c.b2 * X| ≤ u * |c.b2 * X| + η → |Q2 - c.a2 * Y| ≤ u * |c.a2 * Y| + η →
            |P2 - Q2| ≤ V))) := by
  intro V
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hX
  have hSb : 0 ≤ Sb := (abs_nonneg _).trans hS1
  have hb0 := abs_nonneg c.b0
  have hb1 := abs_nonneg c.b1
  have hb2 := abs_nonneg c.b2
  have ha1 := abs_nonneg c.a1
  have ha2 := abs_nonneg c.a2
  have hbX : ∀ b : ℝ, |b * X| ≤ |b| * M := fun b => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hX (abs_nonneg _)
  -- `Yr` bounds the rounded output; every monomial of `V` is nonnegative.
  set Yr := 4 * |c.b0| * M + 2 * Sb + 3 * η with hYr
  have hYr0 : 0 ≤ Yr := by positivity
  have m1 : 0 ≤ |c.b0| * M := by positivity
  have m2 : 0 ≤ |c.b1| * M := by positivity
  have m3 : 0 ≤ |c.b2| * M := by positivity
  have m4 : 0 ≤ |c.a1| * Yr := by positivity
  have m5 : 0 ≤ |c.a2| * Yr := by positivity
  have hV : V = 4 * (|c.b0| * M) + 4 * (|c.b1| * M) + 4 * (|c.b2| * M) + 4 * (|c.a1| * Yr) +
      4 * (|c.a2| * Yr) + Sb + 5 * η := by
    simp only [V, stepValueBound, hYr]; ring
  refine ⟨?_, ?_, ?_, fun hP0 => ?_⟩
  · have := hbX c.b0; linarith
  · have := hbX c.b1; linarith
  · have := hbX c.b2; linarith
  obtain ⟨-, p0⟩ := round_bounds hu0 hu1 hP0 (hbX c.b0)
  have z0 : |P0 + S1| ≤ 2 * (|c.b0| * M) + η + Sb := by
    have := abs_add_le P0 S1; linarith
  refine ⟨by linarith, fun hY => ?_⟩
  obtain ⟨-, yb⟩ := round_bounds hu0 hu1 hY z0
  have haY : ∀ a : ℝ, |a * Y| ≤ |a| * Yr := fun a => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (by rw [hYr]; linarith) (abs_nonneg _)
  refine ⟨by have := haY c.a1; linarith, by have := haY c.a2; linarith,
    fun hP1 hQ1 => ?_, fun hP2 hQ2 => ?_⟩
  · obtain ⟨-, p1⟩ := round_bounds hu0 hu1 hP1 (hbX c.b1)
    obtain ⟨-, q1⟩ := round_bounds hu0 hu1 hQ1 (haY c.a1)
    have z1 : |P1 - Q1| ≤ 2 * (|c.b1| * M) + η + (2 * (|c.a1| * Yr) + η) := by
      have := abs_sub P1 Q1; linarith
    refine ⟨by linarith, fun hD1 => ?_⟩
    obtain ⟨-, d1⟩ := round_bounds hu0 hu1 hD1 z1
    have := abs_add_le D1 S2
    linarith
  · obtain ⟨-, p2⟩ := round_bounds hu0 hu1 hP2 (hbX c.b2)
    obtain ⟨-, q2⟩ := round_bounds hu0 hu1 hQ2 (haY c.a2)
    have := abs_sub P2 Q2
    linarith

/-- **The invariant inequalities force `cInf·K·κ·β < 1 − ρ`.** If numbers `Sb`, `R`, `Ê` and
states `r`, `s` satisfy `ρ·Ê + K·κ·(α + β·Sb) ≤ Ê`, `cInf·(R + Ê) ≤ Sb`, `N(r) ≤ R` and
`N(s − r) ≤ Ê` (hypotheses of `noOverflow_f64_of_inputs` / `_f32`), with `α > 0` and
`cInf·K·κ > 0` (`κ = roundGain c`), then `cInf·K·κ·β < 1 − ρ`. So where that condition fails,
those hypotheses cannot all hold. -/
theorem smallness_of_invariant (c : CoeffsReal) (C : Contraction c)
    {Sb R Ê α β r₁ r₂ s₁ s₂ : ℝ}
    (hE : C.ρ * Ê + C.K * ((α + β * Sb) * roundGain c) ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb) (hr : C.N r₁ r₂ ≤ R) (he : C.N (s₁ - r₁) (s₂ - r₂) ≤ Ê)
    (hα : 0 < α) (hpos : 0 < C.cInf * C.K * roundGain c) :
    C.cInf * C.K * roundGain c * β < 1 - C.ρ := by
  have hR0 : 0 ≤ R := le_trans (C.nonneg _ _) hr
  have hE0 : 0 ≤ Ê := le_trans (C.nonneg _ _) he
  by_contra! hnot
  have hρ := C.ρ_lt_one
  have hci := C.cInf_nonneg
  have hSb0 : 0 ≤ Sb := le_trans (by positivity) hS
  have hSE : C.cInf * Ê ≤ Sb := by nlinarith
  -- cInf·(1 - ρ)·Ê ≥ cInf·K·κ·(α + β·Sb), multiplying `hE` by `cInf ≥ 0`.
  have h1 : C.cInf * (C.K * ((α + β * Sb) * roundGain c)) ≤ C.cInf * ((1 - C.ρ) * Ê) :=
    mul_le_mul_of_nonneg_left (by linarith) hci
  -- cInf·K·κ·β·Sb ≥ (1 - ρ)·Sb ≥ (1 - ρ)·cInf·Ê.
  have h2 : (1 - C.ρ) * Sb ≤ C.cInf * C.K * roundGain c * β * Sb :=
    mul_le_mul_of_nonneg_right hnot hSb0
  have h3 : (1 - C.ρ) * (C.cInf * Ê) ≤ (1 - C.ρ) * Sb :=
    mul_le_mul_of_nonneg_left hSE (by linarith)
  have h4 : 0 < C.cInf * C.K * roundGain c * α := mul_pos hpos hα
  nlinarith [h1, h2, h3, h4]

/-- `Sb'` at given numbers: `ci·(n₀ + k·G·M + k·κ·α)/(1 − ρ' − ci·k·κ·β)` (`G = inputGain c`,
`κ = roundGain c`). With `ci`, `k` and `ρ'` equal to `cInf`, `K` and `ρ` of a `Contraction` and
`n₀ = N(s)·(1 − ρ)`, it equals `computedStateBound`; `block_bounds_le` and `block_bounds_ge`
compare the two when the numbers are only above or below those. -/
noncomputable def stateBoundAt (c : CoeffsReal) (M α β n₀ ci k ρ' : ℝ) : ℝ :=
  ci * (n₀ + k * inputGain c * M + k * roundGain c * α) / (1 - ρ' - ci * k * roundGain c * β)

/-- The bound on each output's error at given numbers: `(α + β·Sb')·(1 + ci·k·κ/(1 − ρ'))`, with
`Sb' = stateBoundAt c M α β n₀ ci k ρ'` and `κ = roundGain c`. With `ci`, `k` and `ρ'` equal to
`cInf`, `K` and `ρ` of a `Contraction` and `n₀ = N(s)·(1 − ρ)`, it equals `cInf·Ê + L`;
`block_bounds_le` and `block_bounds_ge` compare the two when the numbers are only above or below
those. -/
noncomputable def outErrBoundAt (c : CoeffsReal) (M α β n₀ ci k ρ' : ℝ) : ℝ :=
  (α + β * stateBoundAt c M α β n₀ ci k ρ') * (1 + ci * k * roundGain c / (1 - ρ'))

/-- **Numbers above the bounds, from numbers above `cInf`, `K` and `ρ`.** Let `0 ≤ M`, `0 ≤ α`,
`0 ≤ β`, and let `n₀`, `ci`, `k` and `ρu` be at least `N(s)`, `cInf`, `K` and `ρ`, with
`ci·k·κ·β < 1 − ρu` (`κ = roundGain c`). Then `cInf·K·κ·β < 1 − ρ` (the condition of
`block_error_real`), and, with `Sb' = stateBoundAt c M α β n₀ ci k ρu`:
`Sb = computedStateBound ≤ Sb'`, `L = localErrBound ≤ α + β·Sb'`,
`α ≤ cInf·Ê + L ≤ outErrBoundAt c M α β n₀ ci k ρu` (with `Ê = stateErrBound`, so `cInf·Ê + L`
is `block_error_real`'s bound on each output's error), and `stepValueBound c η M Sb` is at most
`stepValueBound c η M Sb'` for every `η`. -/
theorem block_bounds_le (c : CoeffsReal) (C : Contraction c) (M α β η n₀ ci k ρu : ℝ)
    (s : ℝ × ℝ) (hM0 : 0 ≤ M) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hs : C.N s.1 s.2 ≤ n₀)
    (hci : C.cInf ≤ ci) (hk : C.K ≤ k) (hρ : C.ρ ≤ ρu)
    (hsm : ci * k * roundGain c * β < 1 - ρu) :
    C.cInf * C.K * roundGain c * β < 1 - C.ρ ∧
      computedStateBound c C M α β s ≤ stateBoundAt c M α β n₀ ci k ρu ∧
      localErrBound c C M α β s ≤ α + β * stateBoundAt c M α β n₀ ci k ρu ∧
      α ≤ C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s ∧
      C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s ≤
        outErrBoundAt c M α β n₀ ci k ρu ∧
      stepValueBound c η M (computedStateBound c C M α β s) ≤
        stepValueBound c η M (stateBoundAt c M α β n₀ ci k ρu) := by
  unfold outErrBoundAt
  set Sb' := stateBoundAt c M α β n₀ ci k ρu with hSb'def
  set L' := α + β * Sb' with hL'def
  have hρ0 := C.ρ_nonneg
  have hρ1 := C.ρ_lt_one
  have hK0 := C.K_nonneg
  have hc0 := C.cInf_nonneg
  have hN0 := C.nonneg s.1 s.2
  have hG : 0 ≤ inputGain c := by unfold inputGain; positivity
  have hκ : 0 ≤ roundGain c := by unfold roundGain; positivity
  have hci0 : 0 ≤ ci := hc0.trans hci
  have hk0 : 0 ≤ k := hK0.trans hk
  have hCK : C.cInf * C.K ≤ ci * k := mul_le_mul hci hk hK0 hci0
  have hCKκ : C.cInf * C.K * roundGain c ≤ ci * k * roundGain c :=
    mul_le_mul_of_nonneg_right hCK hκ
  have hCKκβ : C.cInf * C.K * roundGain c * β ≤ ci * k * roundGain c * β :=
    mul_le_mul_of_nonneg_right hCKκ hβ
  have hsmall : C.cInf * C.K * roundGain c * β < 1 - C.ρ := by linarith
  have hD' : 0 < 1 - ρu - ci * k * roundGain c * β := by linarith
  have hDD : 1 - ρu - ci * k * roundGain c * β ≤ 1 - C.ρ - C.cInf * C.K * roundGain c * β := by
    linarith
  have h1ρ : 0 < 1 - C.ρ := by linarith
  have h1ρu : 0 < 1 - ρu := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hci0 hk0) hκ) hβ]
  -- `R·(1 − ρ) = N(s)·(1 − ρ) + K·G·M`.
  have hR : exactStateBound c C M s * (1 - C.ρ) =
      C.N s.1 s.2 * (1 - C.ρ) + C.K * inputGain c * M := by
    unfold exactStateBound; field_simp
  have hX0 : 0 ≤ exactStateBound c C M s * (1 - C.ρ) + C.K * roundGain c * α := by
    rw [hR]; have := h1ρ.le; positivity
  have hXY : exactStateBound c C M s * (1 - C.ρ) + C.K * roundGain c * α ≤
      n₀ + k * inputGain c * M + k * roundGain c * α := by
    rw [hR]
    have h1 : C.N s.1 s.2 * (1 - C.ρ) ≤ n₀ := by nlinarith
    have h2 : C.K * inputGain c * M ≤ k * inputGain c * M := by gcongr
    have h3 : C.K * roundGain c * α ≤ k * roundGain c * α := by gcongr
    linarith
  have hSb : computedStateBound c C M α β s ≤ Sb' := by
    rw [hSb'def]; unfold computedStateBound stateBoundAt
    exact div_le_div₀ (by have := hX0.trans hXY; positivity)
      (mul_le_mul hci hXY hX0 hci0) hD' hDD
  have hSb0 : 0 ≤ computedStateBound c C M α β s := by
    unfold computedStateBound
    exact div_nonneg (mul_nonneg hc0 hX0) (by linarith)
  have hSb'0 : 0 ≤ Sb' := hSb0.trans hSb
  have hL : localErrBound c C M α β s ≤ L' := by
    unfold localErrBound
    have := mul_le_mul_of_nonneg_left hSb hβ
    linarith
  have hLα : α ≤ localErrBound c C M α β s := by
    unfold localErrBound
    have := mul_nonneg hβ hSb0
    linarith
  have he : C.cInf * stateErrBound c C M α β s =
      localErrBound c C M α β s * (C.cInf * C.K * roundGain c / (1 - C.ρ)) := by
    unfold stateErrBound; ring
  have ht0 : 0 ≤ C.cInf * C.K * roundGain c / (1 - C.ρ) := by
    have := mul_nonneg (mul_nonneg hc0 hK0) hκ
    exact div_nonneg this h1ρ.le
  have ht : C.cInf * C.K * roundGain c / (1 - C.ρ) ≤ ci * k * roundGain c / (1 - ρu) :=
    div_le_div₀ (mul_nonneg (mul_nonneg hci0 hk0) hκ) hCKκ h1ρu (by linarith)
  have hL0 : 0 ≤ localErrBound c C M α β s := hα.trans hLα
  refine ⟨hsmall, hSb, hL, ?_, ?_, ?_⟩
  · rw [he]
    have := mul_nonneg hL0 ht0
    linarith
  · rw [he]
    have h := mul_le_mul hL (add_le_add_left ht 1) (by linarith) (by positivity)
    linarith
  · unfold stepValueBound
    have : 0 ≤ |c.a1| + |c.a2| := by positivity
    nlinarith

/-- **Numbers below the bounds, from numbers below `cInf`, `K` and `ρ`.** Let `0 ≤ M`, `0 ≤ α`,
`0 ≤ β`, `cInf·K·κ·β < 1 − ρ` (`κ = roundGain c`, `G = inputGain c`), and let `ci ≥ 0`, `k ≥ 0`
and `ρl` be at most `cInf`, `K` and `ρ`. Then `stateBoundAt c M α β 0 ci k ρl` is at most
`Sb = computedStateBound`, and `outErrBoundAt c M α β 0 ci k ρl` is at most `cInf·Ê + L` (with
`Ê = stateErrBound` and `L = localErrBound`), the bound of `block_error_real` on each output's
error. -/
theorem block_bounds_ge (c : CoeffsReal) (C : Contraction c) (M α β ci k ρl : ℝ) (s : ℝ × ℝ)
    (hM0 : 0 ≤ M) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : C.cInf * C.K * roundGain c * β < 1 - C.ρ)
    (hci0 : 0 ≤ ci) (hk0 : 0 ≤ k) (hci : ci ≤ C.cInf) (hk : k ≤ C.K) (hρ : ρl ≤ C.ρ) :
    stateBoundAt c M α β 0 ci k ρl ≤ computedStateBound c C M α β s ∧
      outErrBoundAt c M α β 0 ci k ρl ≤
        C.cInf * stateErrBound c C M α β s + localErrBound c C M α β s := by
  unfold outErrBoundAt
  set Sb'' := stateBoundAt c M α β 0 ci k ρl with hSb''def
  set L'' := α + β * Sb'' with hL''def
  have hρ1 := C.ρ_lt_one
  have hK0 := C.K_nonneg
  have hc0 := C.cInf_nonneg
  have hN0 := C.nonneg s.1 s.2
  have hG : 0 ≤ inputGain c := by unfold inputGain; positivity
  have hκ : 0 ≤ roundGain c := by unfold roundGain; positivity
  have hCK : ci * k ≤ C.cInf * C.K := mul_le_mul hci hk hk0 hc0
  have hCKκ : ci * k * roundGain c ≤ C.cInf * C.K * roundGain c :=
    mul_le_mul_of_nonneg_right hCK hκ
  have hCKκβ : ci * k * roundGain c * β ≤ C.cInf * C.K * roundGain c * β :=
    mul_le_mul_of_nonneg_right hCKκ hβ
  have hD : 0 < 1 - C.ρ - C.cInf * C.K * roundGain c * β := by linarith
  have hDD : 1 - C.ρ - C.cInf * C.K * roundGain c * β ≤ 1 - ρl - ci * k * roundGain c * β := by
    linarith
  have h1ρ : 0 < 1 - C.ρ := by linarith
  have hR : exactStateBound c C M s * (1 - C.ρ) =
      C.N s.1 s.2 * (1 - C.ρ) + C.K * inputGain c * M := by
    unfold exactStateBound; field_simp
  have hY0 : 0 ≤ 0 + k * inputGain c * M + k * roundGain c * α := by positivity
  have hXY : 0 + k * inputGain c * M + k * roundGain c * α ≤
      exactStateBound c C M s * (1 - C.ρ) + C.K * roundGain c * α := by
    rw [hR]
    have h1 : 0 ≤ C.N s.1 s.2 * (1 - C.ρ) := mul_nonneg hN0 h1ρ.le
    have h2 : k * inputGain c * M ≤ C.K * inputGain c * M := by gcongr
    have h3 : k * roundGain c * α ≤ C.K * roundGain c * α := by gcongr
    linarith
  have hSb : Sb'' ≤ computedStateBound c C M α β s := by
    rw [hSb''def]; unfold computedStateBound stateBoundAt
    exact div_le_div₀ (mul_nonneg hc0 (hY0.trans hXY)) (mul_le_mul hci hXY hY0 hc0) hD hDD
  have hSb''0 : 0 ≤ Sb'' := by
    rw [hSb''def]; exact div_nonneg (mul_nonneg hci0 hY0) (by linarith)
  have hL : L'' ≤ localErrBound c C M α β s := by
    unfold localErrBound
    have := mul_le_mul_of_nonneg_left hSb hβ
    linarith
  have hL''0 : 0 ≤ L'' := by have := mul_nonneg hβ hSb''0; linarith
  have he : C.cInf * stateErrBound c C M α β s =
      localErrBound c C M α β s * (C.cInf * C.K * roundGain c / (1 - C.ρ)) := by
    unfold stateErrBound; ring
  have ht : ci * k * roundGain c / (1 - ρl) ≤ C.cInf * C.K * roundGain c / (1 - C.ρ) :=
    div_le_div₀ (mul_nonneg (mul_nonneg hc0 hK0) hκ) hCKκ h1ρ (by linarith)
  have ht0 : 0 ≤ ci * k * roundGain c / (1 - ρl) :=
    div_nonneg (mul_nonneg (mul_nonneg hci0 hk0) hκ) (by linarith)
  refine ⟨hSb, ?_⟩
  rw [he]
  have h := mul_le_mul hL (add_le_add_left ht 1) (by linarith) (hL''0.trans hL)
  linarith

/-- **When the condition of `block_error_real` fails.** If `0 ≤ k`, `0 ≤ β`, `ci`, `k` and `ρl`
are at most `cInf`, `K` and `ρ`, and `1 − ρl ≤ ci·k·κ·β` (`κ = roundGain c`), then
`cInf·K·κ·β < 1 − ρ` is false. -/
theorem smallness_fails (c : CoeffsReal) (C : Contraction c) (β ci k ρl : ℝ) (hβ : 0 ≤ β)
    (hk0 : 0 ≤ k) (hci : ci ≤ C.cInf) (hk : k ≤ C.K) (hρ : ρl ≤ C.ρ)
    (h : 1 - ρl ≤ ci * k * roundGain c * β) :
    ¬ C.cInf * C.K * roundGain c * β < 1 - C.ρ := by
  have hκ : 0 ≤ roundGain c := by unfold roundGain; positivity
  have hCK : ci * k ≤ C.cInf * C.K := mul_le_mul hci hk hk0 C.cInf_nonneg
  have : ci * k * roundGain c * β ≤ C.cInf * C.K * roundGain c * β :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK hκ) hβ
  intro hlt
  linarith

/-- `norm_num` with the coefficients `c` and the bound formulas unfolded: closes the statements
about rational numbers in the worked examples of `BlockF64.lean` and `BlockF32.lean`. -/
scoped macro "bound_norm_num" "[" c:ident "]" : tactic =>
  `(tactic| norm_num [$c:ident, outErrBoundAt, stateBoundAt, localErrBase, localErrSlope,
    inputGain, roundGain, stepValueBound, abs_of_neg, abs_of_pos])

end conjure_dsp_lib.biquad

end
