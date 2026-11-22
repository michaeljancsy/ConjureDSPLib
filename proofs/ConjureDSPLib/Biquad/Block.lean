module

public import ConjureDSPLib.Biquad.Textbook
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# The biquad over a whole block: the real-number argument

The transposed-direct-form-II biquad keeps two state values. If the computed state differs from
the exact state by `e = (e₁, e₂)`, one step changes that difference to `M·e + w`, where

`M·(v₁, v₂) = (-a1·v₁ + v₂, -a2·v₁)`

(the filter's own state-update map, whose eigenvalues are its poles) and `w` comes from this
step's rounding. Whether such errors pile up depends on `M`. This file is parametric in a
`Contraction`: any way `N` of measuring a pair of numbers under which `M` shrinks every pair by a
factor `ρ < 1`. `Biquad/Contraction.lean` gives one for typical filters.

With it, `block_error_real` shows that over a block of any length the computed outputs and state
stay within fixed distances of the exact filter's, provided each step's rounding stays within a
bound `L` while the state stays within a bound `Sb`. This file uses real numbers only; the
floating-point and Rust layers are in `BlockF64.lean` and `BlockF32.lean`.
-/

@[expose] public section

namespace conjure_dsp_lib.biquad

/-- A way `N` of measuring pairs `(v₁, v₂)` under which the biquad's state-update map shrinks every
pair by at least the factor `ρ < 1`. `cInf` and `K` compare `N` with the plain sizes `|v₁|`,
`|v₂|`. -/
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

/-- `LocalErrOK c Sb M L s xs f ys`: the computed outputs `ys` and final state `f` come from
inputs `xs` starting from computed state `s`, and at every step where both state values are at
most `Sb` in size and the input is at most `M` in size, the step's three roundings (in the
output, and in each new state value) are each at most `L` in size. Each rounding is measured
against the exact step taken from the computed state and the computed output. -/
def LocalErrOK (c : CoeffsReal) (Sb M L : ℝ) : ℝ × ℝ → List ℝ → ℝ × ℝ → List ℝ → Prop
  | s, [], f, [] => f = s
  | (s₁, s₂), x :: xs, f, y :: ys =>
    ∃ t₁ t₂ : ℝ,
      (|s₁| ≤ Sb → |s₂| ≤ Sb → |x| ≤ M →
        |y - (c.b0 * x + s₁)| ≤ L ∧ |t₁ - (c.b1 * x - c.a1 * y + s₂)| ≤ L ∧
          |t₂ - (c.b2 * x - c.a2 * y)| ≤ L) ∧
      LocalErrOK c Sb M L (t₁, t₂) xs f ys
  | _, _, _, _ => False

/-- The induction behind `block_error_real`. Two bounds hold at every step: the exact state
`r` measures at most `R`, and the error `s - r` (computed minus exact state) measures at most
`Ê`. The three inequalities make them invariant: the first keeps the exact state bounded
(stability), the second keeps the error bounded, and the third keeps the computed state within
`Sb`, where each step's rounding is at most `L`. -/
theorem block_error_core (c : CoeffsReal) (C : Contraction c) (Sb M L R Ê : ℝ)
    (hR : C.ρ * R + C.K * (|c.b1 - c.a1 * c.b0| + |c.b2 - c.a2 * c.b0|) * M ≤ R)
    (hE : C.ρ * Ê + C.K * (L * (2 + |c.a1| + |c.a2|)) ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb) :
    ∀ (xs : List ℝ) (s r f : ℝ × ℝ) (ys : List ℝ),
      (∀ x ∈ xs, |x| ≤ M) → C.N r.1 r.2 ≤ R → C.N (s.1 - r.1) (s.2 - r.2) ≤ Ê →
      LocalErrOK c Sb M L s xs f ys →
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
      simp only [LocalErrOK] at hw
      subst hw
      refine ⟨List.Forall₂.nil, ?_, ?_⟩
      · exact (C.le_fst _ _).trans (mul_le_mul_of_nonneg_left he C.cInf_nonneg)
      · exact (C.le_snd _ _).trans (mul_le_mul_of_nonneg_left he C.cInf_nonneg)
    | cons => obtain ⟨s₁, s₂⟩ := s; simp [LocalErrOK] at hw
  | cons x xs ih =>
    intro s r f ys hM hr he hw
    obtain ⟨s₁, s₂⟩ := s
    obtain ⟨r₁, r₂⟩ := r
    cases ys with
    | nil => simp [LocalErrOK] at hw
    | cons y ys =>
      simp only [LocalErrOK] at hw
      obtain ⟨t₁, t₂, hloc, hrest⟩ := hw
      simp only at hr he
      have hx : |x| ≤ M := hM x (by simp)
      have hci := C.cInf_nonneg
      -- The computed state is within `Sb`, so this step's roundings are at most `L`.
      have hs₁ : |s₁| ≤ Sb := by
        have h1 := C.le_fst r₁ r₂
        have h2 := C.le_fst (s₁ - r₁) (s₂ - r₂)
        calc |s₁| = |r₁ + (s₁ - r₁)| := by ring_nf
          _ ≤ |r₁| + |s₁ - r₁| := abs_add_le _ _
          _ ≤ C.cInf * R + C.cInf * Ê := add_le_add
              (h1.trans (mul_le_mul_of_nonneg_left hr hci))
              (h2.trans (mul_le_mul_of_nonneg_left he hci))
          _ ≤ Sb := by linarith
      have hs₂ : |s₂| ≤ Sb := by
        have h1 := C.le_snd r₁ r₂
        have h2 := C.le_snd (s₁ - r₁) (s₂ - r₂)
        calc |s₂| = |r₂ + (s₂ - r₂)| := by ring_nf
          _ ≤ |r₂| + |s₂ - r₂| := abs_add_le _ _
          _ ≤ C.cInf * R + C.cInf * Ê := add_le_add
              (h1.trans (mul_le_mul_of_nonneg_left hr hci))
              (h2.trans (mul_le_mul_of_nonneg_left he hci))
          _ ≤ Sb := by linarith
      obtain ⟨hdy, hd₁, hd₂⟩ := hloc hs₁ hs₂ hx
      set dy := y - (c.b0 * x + s₁) with hdy_def
      set d₁ := t₁ - (c.b1 * x - c.a1 * y + s₂) with hd₁_def
      set d₂ := t₂ - (c.b2 * x - c.a2 * y) with hd₂_def
      set e₁ := s₁ - r₁
      set e₂ := s₂ - r₂
      -- The new error is `M` applied to the old error, plus this step's rounding `w`.
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
          _ ≤ C.ρ * Ê + C.K * (L * (2 + |c.a1| + |c.a2|)) := by
              refine add_le_add ((C.contract _ _).trans
                (mul_le_mul_of_nonneg_left he C.ρ_nonneg)) ?_
              refine (C.le_sum _ _).trans (mul_le_mul_of_nonneg_left ?_ C.K_nonneg)
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
          _ ≤ C.ρ * R + C.K * (|c.b1 - c.a1 * c.b0| + |c.b2 - c.a2 * c.b0|) * M := by
              refine add_le_add ((C.contract _ _).trans
                (mul_le_mul_of_nonneg_left hr C.ρ_nonneg)) ?_
              refine (C.le_sum _ _).trans ?_
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
      obtain ⟨h1, h2, h3⟩ := ih (t₁, t₂)
        (c.b1 * x - c.a1 * (c.b0 * x + r₁) + r₂, c.b2 * x - c.a2 * (c.b0 * x + r₁)) f ys
        (fun z hz => hM z (List.mem_cons_of_mem _ hz)) hr' he' hrest
      exact ⟨List.Forall₂.cons hy h1, h2, h3⟩

/-- How much the filter can amplify its input into its state: `|b1 - a1·b0| + |b2 - a2·b0|`. -/
def inputGain (c : CoeffsReal) : ℝ := |c.b1 - c.a1 * c.b0| + |c.b2 - c.a2 * c.b0|

/-- How much one step's three roundings can add to the state error: `2 + |a1| + |a2|`. -/
def roundGain (c : CoeffsReal) : ℝ := 2 + |c.a1| + |c.a2|

/-- `R`: a bound on the measure of the exact filter's state, from start `s` with inputs at most
`M` in size. -/
noncomputable def exactStateBound (c : CoeffsReal) (C : Contraction c) (M : ℝ) (s : ℝ × ℝ) : ℝ :=
  C.N s.1 s.2 + C.K * inputGain c * M / (1 - C.ρ)

/-- `Sb`: a bound on each computed state value, when one step's roundings are at most
`α + β·Sb`. -/
noncomputable def computedStateBound (c : CoeffsReal) (C : Contraction c) (M α β : ℝ)
    (s : ℝ × ℝ) : ℝ :=
  C.cInf * (exactStateBound c C M s * (1 - C.ρ) + C.K * roundGain c * α) /
    (1 - C.ρ - C.cInf * C.K * roundGain c * β)

/-- `L`: the bound on one step's roundings, `α + β·Sb`. -/
noncomputable def stepRoundBound (c : CoeffsReal) (C : Contraction c) (M α β : ℝ)
    (s : ℝ × ℝ) : ℝ :=
  α + β * computedStateBound c C M α β s

/-- `Ê`: a bound on the measure of the state error (computed minus exact). -/
noncomputable def stateErrBound (c : CoeffsReal) (C : Contraction c) (M α β : ℝ)
    (s : ℝ × ℝ) : ℝ :=
  C.K * (stepRoundBound c C M α β s * roundGain c) / (1 - C.ρ)

/-- **Whole-block error of the biquad, on real numbers.** Start the computed filter and the exact
filter from the same state `s`, with inputs at most `M` in size. Suppose each step's roundings are
at most `α + β·Sb` whenever the state is within `Sb` (`LocalErrOK`, with `Sb` and `L` as
defined above), and `cInf·K·(2 + |a1| + |a2|)·β < 1 - ρ` (the rounding feedback is small). Then
over a block of any length, every computed output is within `cInf·Ê + L` of the exact output,
and each computed state value ends within `cInf·Ê` of the exact one. -/
theorem block_error_real (c : CoeffsReal) (C : Contraction c) (M α β : ℝ) (hM0 : 0 ≤ M)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsmall : C.cInf * C.K * roundGain c * β < 1 - C.ρ)
    (xs : List ℝ) (s f : ℝ × ℝ) (ys : List ℝ) (hM : ∀ x ∈ xs, |x| ≤ M)
    (hw : LocalErrOK c (computedStateBound c C M α β s) M (stepRoundBound c C M α β s) s xs f ys) :
    let Ê := stateErrBound c C M α β s
    let L := stepRoundBound c C M α β s
    List.Forall₂ (fun y e => |y - e| ≤ C.cInf * Ê + L) ys (filt_real c s xs).2 ∧
      |f.1 - (filt_real c s xs).1.1| ≤ C.cInf * Ê ∧
      |f.2 - (filt_real c s xs).1.2| ≤ C.cInf * Ê := by
  intro Ê L
  have hρ := C.ρ_lt_one
  have h1ρ : 0 < 1 - C.ρ := by linarith
  have hK := C.K_nonneg
  have hci := C.cInf_nonneg
  have hG : 0 ≤ inputGain c := by unfold inputGain; positivity
  have hκ : 0 ≤ roundGain c := by unfold roundGain; positivity
  have hD : 0 < 1 - C.ρ - C.cInf * C.K * roundGain c * β := by linarith
  set R := exactStateBound c C M s with hRdef
  set Sb := computedStateBound c C M α β s with hSbdef
  have hN0 : 0 ≤ C.N s.1 s.2 := C.nonneg _ _
  have hR0 : 0 ≤ R := by
    rw [hRdef]; unfold exactStateBound
    have : 0 ≤ C.K * inputGain c * M / (1 - C.ρ) := by positivity
    linarith
  -- The three invariance conditions of `block_error_core`.
  have hR : C.ρ * R + C.K * (|c.b1 - c.a1 * c.b0| + |c.b2 - c.a2 * c.b0|) * M ≤ R := by
    have e : C.K * inputGain c * M = (1 - C.ρ) * (C.K * inputGain c * M / (1 - C.ρ)) := by
      field_simp
    have : R = C.N s.1 s.2 + C.K * inputGain c * M / (1 - C.ρ) := rfl
    unfold inputGain at e this
    nlinarith [C.ρ_nonneg]
  have hLdef : L = α + β * Sb := rfl
  have hEdef : Ê * (1 - C.ρ) = C.K * (L * roundGain c) := by
    simp only [Ê, L, stateErrBound]; field_simp
  have hE : C.ρ * Ê + C.K * (L * (2 + |c.a1| + |c.a2|)) ≤ Ê := by
    have : C.K * (L * (2 + |c.a1| + |c.a2|)) = C.K * (L * roundGain c) := rfl
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
  exact block_error_core c C Sb M L R Ê hR hE hS xs s s f ys hM hr he hw

end conjure_dsp_lib.biquad

end
