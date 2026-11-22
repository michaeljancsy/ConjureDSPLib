module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Order.Field.Basic
public import ConjureDSPLib.TwoState

/-!
# The state-variable filter over a whole block: the real-number argument

`svfStep_real` is one step of the SVF of `src/svf.rs` in exact arithmetic, with the same operations
in the same order as `svfStep_f64` / `svfStep_f32`:

`hp = (x − (k + g)·s1 − s2)·d`, `bp = g·hp + s1`, `lp = g·bp + s2`,
output `(m_hp·hp + m_bp·bp) + m_lp·lp`, new state `(g·hp + bp, g·bp + lp)`.

`svfStep_real_linear` shows that this is linear: the new state is `A·s + b·x` and the output
`cOut·s + dx·x`, with the entries `a11`, `a12`, `a21`, `a22`, `bx1`, `bx2`, `cs1`, `cs2` and `dx`
given in terms of `g`, `k`, `d` and the mix, for any real `g`, `k`, `d` (it does not use
`d = 1/(1 + g·(g + k))`).

If the computed state differs from the exact one by `e`, one step changes that difference to
`A·e + w`, where `w` comes from this step's rounding. As for the biquad (`Biquad/Block.lean`),
this file is parametric in a `Contraction`: a measure `N` of pairs under which `A` shrinks every
pair by at least `ρ < 1`, the shared `two_state.Contraction` (`TwoState.lean`) at `A`.
`Svf/Contraction.lean` gives one for complex poles and transfers any biquad `Contraction` of the
matching biquad.

`block_error_real`: over a block of any length, if the inputs are at most `M`, each step's
roundings from a state within `Sb` are at most `Ly` on the output and `Ls` on the state
(`WithinLocalErr`), and `cInf·(R + Ê) ≤ Sb` with `R = N(s) + K·G·M/(1 − ρ)` and
`Ê = K·Ls/(1 − ρ)`, then each output is within `outGain·cInf·Ê + Ly` of the exact filter's and
each final state value within `cInf·Ê`. Unlike `Biquad/Block.lean`, `Sb` is any number with that
property rather than a closed form; the worked examples exhibit one.

`step_chain` bounds one step's sixteen roundings: computed with roundings each within
`u·|e| + η` of the exact operation `e` on the computed operands, the output is within
`stepErrOut` and the new state within `stepErrState` (the two errors added) of `svfStep_real`
from the same state, and, when `stepValueBound ≤ V`, all sixteen propositions `Fᵢ` hold (for
floats, no operation overflows). Those three are
built from per-operation bounds `opK1` … `opT2` (bounds on the exact operation values) and
`errK1` … `errT2` (bounds on the computed values' distances from the exact step's).
-/

@[expose] public section

namespace conjure_dsp_lib.svf

/-- SVF coefficients as real numbers: the integrators' gain `g`, the damping `k`, `d` (in the
Rust code `1 / (1 + g·(g + k))`, but any real number here), and the output mix. -/
structure CoeffsReal where
  /-- The integrators' gain. -/
  g : ℝ
  /-- The damping. -/
  k : ℝ
  /-- The stored `1 / (1 + g·(g + k))`; any real number here. -/
  d : ℝ
  /-- Weight of `hp` in the output. -/
  m_hp : ℝ
  /-- Weight of `bp` in the output. -/
  m_bp : ℝ
  /-- Weight of `lp` in the output. -/
  m_lp : ℝ

/-- One SVF step in exact arithmetic, from state `s` on input `x`, with the operations of the
Rust step in the same order: returns the output and the new state. -/
def svfStep_real (c : CoeffsReal) (s : ℝ × ℝ) (x : ℝ) : ℝ × (ℝ × ℝ) :=
  let hp := (x - (c.k + c.g) * s.1 - s.2) * c.d
  let bp := c.g * hp + s.1
  let lp := c.g * bp + s.2
  (c.m_hp * hp + c.m_bp * bp + c.m_lp * lp, (c.g * hp + bp, c.g * bp + lp))

/-- The SVF in exact arithmetic: run `svfStep_real` over a list of inputs from state `s`, returning
the final state and the outputs. It is the real-number counterpart of `filt_f64` / `filt_f32`. -/
def filt_real (c : CoeffsReal) : ℝ × ℝ → List ℝ → (ℝ × ℝ) × List ℝ
  | s, [] => (s, [])
  | s, x :: xs =>
    let r := filt_real c (svfStep_real c s x).2 xs
    (r.1, (svfStep_real c s x).1 :: r.2)

/-- Entry (1, 1) of the state-update matrix `A`: `1 − 2·g·d·(k + g)`. -/
def a11 (c : CoeffsReal) : ℝ := 1 - 2 * c.g * c.d * (c.k + c.g)
/-- Entry (1, 2) of `A`: `−2·g·d`. -/
def a12 (c : CoeffsReal) : ℝ := -(2 * c.g * c.d)
/-- Entry (2, 1) of `A`: `2·g·(1 − g·d·(k + g))`. -/
def a21 (c : CoeffsReal) : ℝ := 2 * c.g * (1 - c.g * c.d * (c.k + c.g))
/-- Entry (2, 2) of `A`: `1 − 2·g²·d`. -/
def a22 (c : CoeffsReal) : ℝ := 1 - 2 * c.g * c.g * c.d
/-- The input's weight in the new first state value: `2·g·d`. -/
def bx1 (c : CoeffsReal) : ℝ := 2 * c.g * c.d
/-- The input's weight in the new second state value: `2·g²·d`. -/
def bx2 (c : CoeffsReal) : ℝ := 2 * c.g * c.g * c.d
/-- The first state value's weight in the output:
`−m_hp·d·(k + g) + (m_bp + m_lp·g)·(1 − g·d·(k + g))`. -/
def cs1 (c : CoeffsReal) : ℝ :=
  -(c.m_hp * c.d * (c.k + c.g)) + (c.m_bp + c.m_lp * c.g) * (1 - c.g * c.d * (c.k + c.g))
/-- The second state value's weight in the output: `−(m_hp + m_bp·g)·d + m_lp·(1 − g²·d)`. -/
def cs2 (c : CoeffsReal) : ℝ := -((c.m_hp + c.m_bp * c.g) * c.d) + c.m_lp * (1 - c.g * c.g * c.d)
/-- The input's weight in the output: `(m_hp + m_bp·g + m_lp·g²)·d`. -/
def dx (c : CoeffsReal) : ℝ := (c.m_hp + c.m_bp * c.g + c.m_lp * c.g * c.g) * c.d

/-- **One exact step is linear.** From state `(s1, s2)` on input `x`, the output is
`cs1·s1 + cs2·s2 + dx·x` and the new state is `(a11·s1 + a12·s2 + bx1·x, a21·s1 + a22·s2 + bx2·x)`,
for any real coefficients. -/
theorem svfStep_real_linear (c : CoeffsReal) (s1 s2 x : ℝ) :
    svfStep_real c (s1, s2) x = (cs1 c * s1 + cs2 c * s2 + dx c * x,
      (a11 c * s1 + a12 c * s2 + bx1 c * x, a21 c * s1 + a22 c * s2 + bx2 c * x)) := by
  simp only [svfStep_real, cs1, cs2, dx, a11, a12, a21, a22, bx1, bx2, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- A way `N` of measuring pairs `(v₁, v₂)`, with `N` nonnegative and `N(u + v) ≤ N(u) + N(v)`,
under which the SVF's state-update map `v ↦ A·v` (`a11` … `a22`) takes every pair to one whose
measure is at most `ρ` times the original's, with `0 ≤ ρ < 1`. `cInf ≥ 0` compares each entry
with `N`: `|v₁| ≤ cInf·N(v₁, v₂)` and `|v₂| ≤ cInf·N(v₁, v₂)`. `K ≥ 0` compares `N` with the
entries' sizes: `N(v₁, v₂) ≤ K·(|v₁| + |v₂|)`. It is the shared `two_state.Contraction` at the
SVF's matrix `A`; the biquad's `Contraction` is the same structure at its companion matrix. -/
abbrev Contraction (c : CoeffsReal) : Type := two_state.Contraction (a11 c) (a12 c) (a21 c) (a22 c)

/-- `WithinLocalErr c Sb M Ly Ls s xs f ys`: `ys` has one entry per input, and there are
intermediate states starting at `s` and ending at `f` such that, at every step where both state
values are at most `Sb` and the input at most `M`, the output is within `Ly` of the exact step's
from that state (`svfStep_real`), and the two next state values' distances from the exact step's add
up to at most `Ls`. -/
def WithinLocalErr (c : CoeffsReal) (Sb M Ly Ls : ℝ) :
    ℝ × ℝ → List ℝ → ℝ × ℝ → List ℝ → Prop
  | s, [], f, [] => f = s
  | s, x :: xs, f, y :: ys =>
    ∃ t : ℝ × ℝ,
      (|s.1| ≤ Sb → |s.2| ≤ Sb → |x| ≤ M →
        |y - (svfStep_real c s x).1| ≤ Ly ∧
          |t.1 - (svfStep_real c s x).2.1| + |t.2 - (svfStep_real c s x).2.2| ≤ Ls) ∧
      WithinLocalErr c Sb M Ly Ls t xs f ys
  | _, _, _, _ => False

/-- `G = |bx1| + |bx2|`: the size of one input's direct contribution to the next state, per unit
of input. -/
def inputGain (c : CoeffsReal) : ℝ := |bx1 c| + |bx2 c|

/-- `|cs1| + |cs2|`: how much a state error can move the output, per unit of the larger state
value's error. -/
def outGain (c : CoeffsReal) : ℝ := |cs1 c| + |cs2 c|

/-- `inputGain` is nonnegative. -/
theorem inputGain_nonneg (c : CoeffsReal) : 0 ≤ inputGain c := by unfold inputGain; positivity

/-- `outGain` is nonnegative. -/
theorem outGain_nonneg (c : CoeffsReal) : 0 ≤ outGain c := by unfold outGain; positivity

/-- One step of the induction behind `block_error_real`. Suppose the exact state `r` measures at
most `R`, the error `s − r` (computed minus exact state) at most `Ê`, the input `x` is at most
`M`, the computed output `y` is within `Ly` of the exact step's from `s`, and the computed next
state `t`'s two distances from the exact step's from `s` add up to at most `Ls`. If
`ρ·R + K·G·M ≤ R` and `ρ·Ê + K·Ls ≤ Ê` (`G = inputGain`), then `y` is within
`outGain·cInf·Ê + Ly` of the exact output from `r`, the exact next state from `r` measures at
most `R`, and the next error at most `Ê`. -/
theorem block_step (c : CoeffsReal) (C : Contraction c) {M Ly Ls R Ê x y : ℝ}
    {s r t : ℝ × ℝ}
    (hR : C.ρ * R + C.K * inputGain c * M ≤ R) (hE : C.ρ * Ê + C.K * Ls ≤ Ê)
    (hx : |x| ≤ M) (hr : C.N r.1 r.2 ≤ R) (he : C.N (s.1 - r.1) (s.2 - r.2) ≤ Ê)
    (hdy : |y - (svfStep_real c s x).1| ≤ Ly)
    (hdt : |t.1 - (svfStep_real c s x).2.1| + |t.2 - (svfStep_real c s x).2.2| ≤ Ls) :
    |y - (svfStep_real c r x).1| ≤ outGain c * C.cInf * Ê + Ly ∧
      C.N (svfStep_real c r x).2.1 (svfStep_real c r x).2.2 ≤ R ∧
      C.N (t.1 - (svfStep_real c r x).2.1) (t.2 - (svfStep_real c r x).2.2) ≤ Ê := by
  obtain ⟨s₁, s₂⟩ := s
  obtain ⟨r₁, r₂⟩ := r
  obtain ⟨t₁, t₂⟩ := t
  simp only at hr he hdt ⊢
  rw [svfStep_real_linear] at hdy hdt ⊢
  simp only at hdy hdt ⊢
  set e₁ := s₁ - r₁ with he₁
  set e₂ := s₂ - r₂ with he₂
  -- The new error is `A·e` plus this step's rounding.
  have he' : C.N (t₁ - (a11 c * r₁ + a12 c * r₂ + bx1 c * x))
      (t₂ - (a21 c * r₁ + a22 c * r₂ + bx2 c * x)) ≤ Ê := by
    have q1 : t₁ - (a11 c * r₁ + a12 c * r₂ + bx1 c * x) =
        (a11 c * e₁ + a12 c * e₂) + (t₁ - (a11 c * s₁ + a12 c * s₂ + bx1 c * x)) := by
      rw [he₁, he₂]; ring
    have q2 : t₂ - (a21 c * r₁ + a22 c * r₂ + bx2 c * x) =
        (a21 c * e₁ + a22 c * e₂) + (t₂ - (a21 c * s₁ + a22 c * s₂ + bx2 c * x)) := by
      rw [he₁, he₂]; ring
    rw [q1, q2]
    exact C.map_add_le he hdt hE
  -- The exact state stays within `R`.
  have hr' : C.N (a11 c * r₁ + a12 c * r₂ + bx1 c * x) (a21 c * r₁ + a22 c * r₂ + bx2 c * x)
      ≤ R :=
    C.map_add_le hr (two_state.abs_mul_add_abs_mul_le hx) (by rw [← mul_assoc]; exact hR)
  -- The output's error is `cOut·e` plus this step's output rounding.
  have hy : |y - (cs1 c * r₁ + cs2 c * r₂ + dx c * x)| ≤ outGain c * C.cInf * Ê + Ly := by
    have q : y - (cs1 c * r₁ + cs2 c * r₂ + dx c * x) =
        (cs1 c * e₁ + cs2 c * e₂) + (y - (cs1 c * s₁ + cs2 c * s₂ + dx c * x)) := by
      rw [he₁, he₂]; ring
    have h1 : |e₁| ≤ C.cInf * Ê := C.fst_le he
    have h2 : |e₂| ≤ C.cInf * Ê := C.snd_le he
    rw [q]
    calc _ ≤ |cs1 c * e₁ + cs2 c * e₂| + |y - (cs1 c * s₁ + cs2 c * s₂ + dx c * x)| :=
          abs_add_le _ _
      _ ≤ (|cs1 c| * |e₁| + |cs2 c| * |e₂|) + Ly := by
          refine add_le_add ?_ hdy
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (|cs1 c| * (C.cInf * Ê) + |cs2 c| * (C.cInf * Ê)) + Ly := by
          gcongr
      _ = outGain c * C.cInf * Ê + Ly := by unfold outGain; ring
  exact ⟨hy, hr', he'⟩

/-- The induction behind `block_error_real`: the exact state `r` measures at most `R` and the
error `s − r` at most `Ê` at every step, when `ρ·R + K·G·M ≤ R`, `ρ·Ê + K·Ls ≤ Ê` and
`cInf·(R + Ê) ≤ Sb`. -/
theorem block_error_core (c : CoeffsReal) (C : Contraction c) (Sb M Ly Ls R Ê : ℝ)
    (hR : C.ρ * R + C.K * inputGain c * M ≤ R) (hE : C.ρ * Ê + C.K * Ls ≤ Ê)
    (hS : C.cInf * (R + Ê) ≤ Sb) :
    ∀ (xs : List ℝ) (s r f : ℝ × ℝ) (ys : List ℝ),
      (∀ x ∈ xs, |x| ≤ M) → C.N r.1 r.2 ≤ R → C.N (s.1 - r.1) (s.2 - r.2) ≤ Ê →
      WithinLocalErr c Sb M Ly Ls s xs f ys →
      List.Forall₂ (fun y e => |y - e| ≤ outGain c * C.cInf * Ê + Ly) ys (filt_real c r xs).2 ∧
        |f.1 - (filt_real c r xs).1.1| ≤ C.cInf * Ê ∧
        |f.2 - (filt_real c r xs).1.2| ≤ C.cInf * Ê := by
  intro xs
  induction xs with
  | nil =>
    intro s r f ys _ _ he hw
    cases ys with
    | nil =>
      simp only [WithinLocalErr] at hw
      subst hw
      exact ⟨List.Forall₂.nil, C.fst_le he, C.snd_le he⟩
    | cons => simp [WithinLocalErr] at hw
  | cons x xs ih =>
    intro s r f ys hM hr he hw
    cases ys with
    | nil => simp [WithinLocalErr] at hw
    | cons y ys =>
      simp only [WithinLocalErr] at hw
      obtain ⟨t, hloc, hrest⟩ := hw
      have hx : |x| ≤ M := hM x (by simp)
      obtain ⟨hs₁, hs₂⟩ := C.state_le hS hr he
      obtain ⟨hdy, hdt⟩ := hloc hs₁ hs₂ hx
      obtain ⟨hy, hr', he'⟩ := block_step c C hR hE hx hr he hdy hdt
      obtain ⟨h1, h2, h3⟩ := ih t (svfStep_real c r x).2 f ys
        (fun z hz => hM z (List.mem_cons_of_mem _ hz)) hr' he' hrest
      exact ⟨List.Forall₂.cons hy h1, h2, h3⟩

/-- `R = N(s) + K·G·M/(1 − ρ)` (`G = inputGain`): a bound on the measure of the exact filter's
state, from start `s` with inputs at most `M` (an invariant of the proof's induction). -/
noncomputable def exactStateBound (c : CoeffsReal) (C : Contraction c) (M : ℝ) (s : ℝ × ℝ) : ℝ :=
  C.N s.1 s.2 + C.K * inputGain c * M / (1 - C.ρ)

/-- `Ê = K·Ls/(1 − ρ)`: a bound on the measure of the state error, computed minus exact, when one
step's roundings on the state add up to at most `Ls`. -/
noncomputable def stateErrBound (c : CoeffsReal) (C : Contraction c) (Ls : ℝ) : ℝ :=
  C.K * Ls / (1 - C.ρ)

/-- `R = exactStateBound` and `Ê = stateErrBound c C Ls` satisfy what `block_step` needs, when
`0 ≤ M` and `0 ≤ Ls`: `ρ·R + K·G·M ≤ R`, `ρ·Ê + K·Ls ≤ Ê`, the starting state `s` measures at
most `R`, and the zero error `s − s` measures at most `Ê`. -/
theorem block_constants (c : CoeffsReal) (C : Contraction c) (M Ls : ℝ) (s : ℝ × ℝ)
    (hM0 : 0 ≤ M) (hLs : 0 ≤ Ls) :
    let R := exactStateBound c C M s
    let Ê := stateErrBound c C Ls
    C.ρ * R + C.K * inputGain c * M ≤ R ∧ C.ρ * Ê + C.K * Ls ≤ Ê ∧ C.N s.1 s.2 ≤ R ∧
      C.N (s.1 - s.1) (s.2 - s.2) ≤ Ê := by
  intro R Ê
  have h1ρ : 0 < 1 - C.ρ := by linarith [C.ρ_lt_one]
  have hE0 : 0 ≤ Ê := by have := C.K_nonneg; simp only [Ê, stateErrBound]; positivity
  exact ⟨C.exactBound_invariant s.1 s.2 _ M, C.errBound_invariant Ls,
    C.le_exactBound s.1 s.2 (inputGain_nonneg c) hM0, C.sub_self_le hE0⟩

/-- **Whole-block error of the SVF, on real numbers.** Let `C` be a `Contraction`, `0 ≤ M`,
`0 ≤ Ls`, every input in `xs` at most `M`, and `Sb` a number with `cInf·(R + Ê) ≤ Sb`, where
`R = exactStateBound c C M s` and `Ê = stateErrBound c C Ls`. If
`WithinLocalErr c Sb M Ly Ls s xs f ys` holds, then for a list `xs` of any length, `ys` and the
outputs of `filt_real c s xs` have the same length, each `y` in `ys` is within
`outGain·cInf·Ê + Ly` of the corresponding exact output, and each of `f`'s two values is within
`cInf·Ê` of the corresponding value of `filt_real c s xs`'s final state. -/
theorem block_error_real (c : CoeffsReal) (C : Contraction c) (M Sb Ly Ls : ℝ) (hM0 : 0 ≤ M)
    (hLs : 0 ≤ Ls) (s : ℝ × ℝ)
    (hS : C.cInf * (exactStateBound c C M s + stateErrBound c C Ls) ≤ Sb)
    (xs : List ℝ) (f : ℝ × ℝ) (ys : List ℝ) (hM : ∀ x ∈ xs, |x| ≤ M)
    (hw : WithinLocalErr c Sb M Ly Ls s xs f ys) :
    let Ê := stateErrBound c C Ls
    List.Forall₂ (fun y e => |y - e| ≤ outGain c * C.cInf * Ê + Ly) ys (filt_real c s xs).2 ∧
      |f.1 - (filt_real c s xs).1.1| ≤ C.cInf * Ê ∧
      |f.2 - (filt_real c s xs).1.2| ≤ C.cInf * Ê := by
  intro Ê
  obtain ⟨hR, hE, hr, he⟩ := block_constants c C M Ls s hM0 hLs
  exact block_error_core c C Sb M Ly Ls _ Ê hR hE hS xs s s f ys hM hr he hw

/-- `ci·(n₀ + k·(G·M + Ls)/(1 − ρ'))` (`G = inputGain c`): with `ci`, `k`, `ρ'` and `n₀` equal to
`cInf`, `K`, `ρ` and `N(s)` of a `Contraction`, it is `cInf·(R + Ê)`, the left side of the
condition on `Sb` in `block_error_real`. -/
noncomputable def stateBoundAt (c : CoeffsReal) (M Ls n₀ ci k ρ' : ℝ) : ℝ :=
  ci * (n₀ + k * (inputGain c * M + Ls) / (1 - ρ'))

/-- `outGain·ci·(k·Ls/(1 − ρ')) + Ly`: with `ci`, `k` and `ρ'` equal to `cInf`, `K` and `ρ` of a
`Contraction`, it is `block_error_real`'s bound on each output's error. -/
noncomputable def outErrBoundAt (c : CoeffsReal) (Ly Ls ci k ρ' : ℝ) : ℝ :=
  outGain c * ci * (k * Ls / (1 - ρ')) + Ly

/-- **Numbers above the bounds, from numbers above `cInf`, `K`, `ρ` and `N(s)`.** If `0 ≤ M`,
`0 ≤ Ls`, `N(s) ≤ n₀`, `cInf ≤ ci`, `K ≤ k`, `ρ ≤ ρu < 1`, then
`cInf·(R + Ê) ≤ stateBoundAt c M Ls n₀ ci k ρu` (with `R`, `Ê` as in `block_error_real`) and
`outGain·cInf·Ê + Ly ≤ outErrBoundAt c Ly Ls ci k ρu`. -/
theorem block_bounds_le (c : CoeffsReal) (C : Contraction c) (M Ly Ls n₀ ci k ρu : ℝ)
    (s : ℝ × ℝ) (hM0 : 0 ≤ M) (hLs : 0 ≤ Ls) (hs : C.N s.1 s.2 ≤ n₀) (hci : C.cInf ≤ ci)
    (hk : C.K ≤ k) (hρ : C.ρ ≤ ρu) (hρu : ρu < 1) :
    C.cInf * (exactStateBound c C M s + stateErrBound c C Ls) ≤
        stateBoundAt c M Ls n₀ ci k ρu ∧
      outGain c * C.cInf * stateErrBound c C Ls + Ly ≤ outErrBoundAt c Ly Ls ci k ρu := by
  have hρ1 := C.ρ_lt_one
  have hK0 := C.K_nonneg
  have hc0 := C.cInf_nonneg
  have hG := inputGain_nonneg c
  have hO := outGain_nonneg c
  have h1 : 0 < 1 - C.ρ := by linarith
  have h1u : 0 < 1 - ρu := by linarith
  have hd : 1 - ρu ≤ 1 - C.ρ := by linarith
  have hX : 0 ≤ inputGain c * M + Ls := by positivity
  -- `K·X/(1 − ρ) ≤ k·X/(1 − ρu)` for `X ≥ 0`.
  have key : ∀ X : ℝ, 0 ≤ X → C.K * X / (1 - C.ρ) ≤ k * X / (1 - ρu) := fun X hX0 =>
    div_le_div₀ (by have := hK0.trans hk; positivity) (mul_le_mul_of_nonneg_right hk hX0) h1u hd
  constructor
  · unfold exactStateBound stateErrBound stateBoundAt
    have e : C.K * inputGain c * M / (1 - C.ρ) + C.K * Ls / (1 - C.ρ) =
        C.K * (inputGain c * M + Ls) / (1 - C.ρ) := by ring
    have hin : C.N s.1 s.2 + C.K * (inputGain c * M + Ls) / (1 - C.ρ) ≤
        n₀ + k * (inputGain c * M + Ls) / (1 - ρu) := add_le_add hs (key _ hX)
    have h0 : 0 ≤ C.N s.1 s.2 + C.K * (inputGain c * M + Ls) / (1 - C.ρ) := by
      have := C.nonneg s.1 s.2; positivity
    calc C.cInf * (C.N s.1 s.2 + C.K * inputGain c * M / (1 - C.ρ) + C.K * Ls / (1 - C.ρ))
        = C.cInf * (C.N s.1 s.2 + C.K * (inputGain c * M + Ls) / (1 - C.ρ)) := by
          rw [add_assoc, e]
      _ ≤ ci * (n₀ + k * (inputGain c * M + Ls) / (1 - ρu)) :=
          mul_le_mul hci hin h0 (hc0.trans hci)
  · unfold stateErrBound outErrBoundAt
    have hE0 : 0 ≤ C.K * Ls / (1 - C.ρ) := by positivity
    have := mul_le_mul (mul_le_mul_of_nonneg_left hci hO) (key Ls hLs) hE0
      (by have := hc0.trans hci; positivity)
    linarith

/-! ## One step's roundings -/

section StepBounds

variable (c : CoeffsReal) (u η M Sb : ℝ)

/-- Bound on `|k + g|`, the first operation's exact value. -/
noncomputable def opK1 : ℝ := |c.k + c.g|
/-- Bound on `|K1·s1|` (`K1` the computed `k + g`). -/
noncomputable def opP : ℝ := ((1 + u) * opK1 c + η) * Sb
/-- Bound on `|x − P|` (`P` the computed `K1·s1`). -/
noncomputable def opD1 : ℝ := M + ((1 + u) * opP c u η Sb + η)
/-- Bound on `|D1 − s2|` (`D1` the computed `x − P`). -/
noncomputable def opD2 : ℝ := ((1 + u) * opD1 c u η M Sb + η) + Sb
/-- Bound on `|D2·d|` (`D2` the computed `D1 − s2`). -/
noncomputable def opH : ℝ := ((1 + u) * opD2 c u η M Sb + η) * |c.d|
/-- Bound on `|g·H|` (`H` the computed `hp`). -/
noncomputable def opQ : ℝ := |c.g| * ((1 + u) * opH c u η M Sb + η)
/-- Bound on `|Q + s1|` (`Q` the computed `g·hp`). -/
noncomputable def opB : ℝ := ((1 + u) * opQ c u η M Sb + η) + Sb
/-- Bound on `|g·B|` (`B` the computed `bp`). -/
noncomputable def opR : ℝ := |c.g| * ((1 + u) * opB c u η M Sb + η)
/-- Bound on `|R + s2|` (`R` the computed `g·bp`). -/
noncomputable def opL : ℝ := ((1 + u) * opR c u η M Sb + η) + Sb
/-- Bound on `|m_hp·H|`. -/
noncomputable def opY1 : ℝ := |c.m_hp| * ((1 + u) * opH c u η M Sb + η)
/-- Bound on `|m_bp·B|`. -/
noncomputable def opY2 : ℝ := |c.m_bp| * ((1 + u) * opB c u η M Sb + η)
/-- Bound on `|Y1 + Y2|` (the computed `m_hp·hp` and `m_bp·bp`). -/
noncomputable def opY3 : ℝ := ((1 + u) * opY1 c u η M Sb + η) + ((1 + u) * opY2 c u η M Sb + η)
/-- Bound on `|m_lp·Lp|` (`Lp` the computed `lp`). -/
noncomputable def opY4 : ℝ := |c.m_lp| * ((1 + u) * opL c u η M Sb + η)
/-- Bound on `|Y3 + Y4|`, the output's last operation. -/
noncomputable def opY : ℝ := ((1 + u) * opY3 c u η M Sb + η) + ((1 + u) * opY4 c u η M Sb + η)
/-- Bound on `|Q + B|`, the new first state value's last operation. -/
noncomputable def opT1 : ℝ := ((1 + u) * opQ c u η M Sb + η) + ((1 + u) * opB c u η M Sb + η)
/-- Bound on `|R + Lp|`, the new second state value's last operation. -/
noncomputable def opT2 : ℝ := ((1 + u) * opR c u η M Sb + η) + ((1 + u) * opL c u η M Sb + η)

/-- Bound on the computed `k + g`'s distance from `k + g`. -/
noncomputable def errK1 : ℝ := u * opK1 c + η
/-- Bound on the computed `P`'s distance from `(k + g)·s1`. -/
noncomputable def errP : ℝ := u * opP c u η Sb + η + errK1 c u η * Sb
/-- Bound on the computed `D1`'s distance from `x − (k + g)·s1`. -/
noncomputable def errD1 : ℝ := u * opD1 c u η M Sb + η + errP c u η Sb
/-- Bound on the computed `D2`'s distance from `x − (k + g)·s1 − s2`. -/
noncomputable def errD2 : ℝ := u * opD2 c u η M Sb + η + errD1 c u η M Sb
/-- Bound on the computed `hp`'s distance from the exact step's `hp`. -/
noncomputable def errH : ℝ := u * opH c u η M Sb + η + errD2 c u η M Sb * |c.d|
/-- Bound on the computed `g·hp`'s distance from the exact step's. -/
noncomputable def errQ : ℝ := u * opQ c u η M Sb + η + |c.g| * errH c u η M Sb
/-- Bound on the computed `bp`'s distance from the exact step's. -/
noncomputable def errB : ℝ := u * opB c u η M Sb + η + errQ c u η M Sb
/-- Bound on the computed `g·bp`'s distance from the exact step's. -/
noncomputable def errR : ℝ := u * opR c u η M Sb + η + |c.g| * errB c u η M Sb
/-- Bound on the computed `lp`'s distance from the exact step's. -/
noncomputable def errL : ℝ := u * opL c u η M Sb + η + errR c u η M Sb
/-- Bound on the computed `m_hp·hp`'s distance from the exact step's. -/
noncomputable def errY1 : ℝ := u * opY1 c u η M Sb + η + |c.m_hp| * errH c u η M Sb
/-- Bound on the computed `m_bp·bp`'s distance from the exact step's. -/
noncomputable def errY2 : ℝ := u * opY2 c u η M Sb + η + |c.m_bp| * errB c u η M Sb
/-- Bound on the computed `m_hp·hp + m_bp·bp`'s distance from the exact step's. -/
noncomputable def errY3 : ℝ := u * opY3 c u η M Sb + η + (errY1 c u η M Sb + errY2 c u η M Sb)
/-- Bound on the computed `m_lp·lp`'s distance from the exact step's. -/
noncomputable def errY4 : ℝ := u * opY4 c u η M Sb + η + |c.m_lp| * errL c u η M Sb
/-- Bound on the computed output's distance from the exact step's. -/
noncomputable def errY : ℝ := u * opY c u η M Sb + η + (errY3 c u η M Sb + errY4 c u η M Sb)
/-- Bound on the computed new first state value's distance from the exact step's. -/
noncomputable def errT1 : ℝ := u * opT1 c u η M Sb + η + (errQ c u η M Sb + errB c u η M Sb)
/-- Bound on the computed new second state value's distance from the exact step's. -/
noncomputable def errT2 : ℝ := u * opT2 c u η M Sb + η + (errR c u η M Sb + errL c u η M Sb)

/-- `Ly`: the bound on one step's output rounding, `errY`. -/
noncomputable def stepErrOut : ℝ := errY c u η M Sb

/-- `Ls`: the bound on one step's state roundings added up, `errT1 + errT2`. -/
noncomputable def stepErrState : ℝ := errT1 c u η M Sb + errT2 c u η M Sb

/-- `V`: the sum of the sixteen operation bounds `opK1` … `opT2`, so at least each of them. -/
noncomputable def stepValueBound : ℝ :=
  opK1 c + opP c u η Sb + opD1 c u η M Sb + opD2 c u η M Sb + opH c u η M Sb + opQ c u η M Sb +
    opB c u η M Sb + opR c u η M Sb + opL c u η M Sb + opY1 c u η M Sb + opY2 c u η M Sb +
    opY3 c u η M Sb + opY4 c u η M Sb + opY c u η M Sb + opT1 c u η M Sb + opT2 c u η M Sb

end StepBounds

/-- Unfolds `stepErrOut`, `stepErrState`, `stepValueBound` and every per-operation bound
`errK1` … `errT2`, `opK1` … `opT2` they are built from. -/
scoped macro "unfold_step_bounds" : tactic =>
  `(tactic| simp only [stepErrOut, stepErrState, stepValueBound, errY, errY3, errY4, errY1,
    errY2, errT1, errT2, errL, errR, errB, errQ, errH, errD2, errD1, errP, errK1, opY, opY3, opY4,
    opY1, opY2, opT1, opT2, opL, opR, opB, opQ, opH, opD2, opD1, opP, opK1])

/-- One rounding `r` of `e`, within `u·|e| + η` of it, with `|e| ≤ ob`: `r` is within `u·ob + η`
of `e` and at most `(1 + u)·ob + η` in size. -/
theorem rnd_bound {u η r e ob : ℝ} (hu : 0 ≤ u) (h : |r - e| ≤ u * |e| + η) (he : |e| ≤ ob) :
    |r - e| ≤ u * ob + η ∧ |r| ≤ (1 + u) * ob + η := by
  have h1 := mul_le_mul_of_nonneg_left he hu
  have h3 : |r| ≤ |r - e| + |e| := by
    have := abs_add_le (r - e) e
    rwa [sub_add_cancel] at this
  constructor <;> nlinarith

private theorem err_add {Z A B a b δ Ea Eb : ℝ} (hz : |Z - (A + B)| ≤ δ) (ha : |A - a| ≤ Ea)
    (hb : |B - b| ≤ Eb) : |Z - (a + b)| ≤ δ + (Ea + Eb) := by
  have := abs_add_three (Z - (A + B)) (A - a) (B - b)
  rw [show Z - (A + B) + (A - a) + (B - b) = Z - (a + b) by ring] at this
  linarith

private theorem err_sub {Z A B a b δ Ea Eb : ℝ} (hz : |Z - (A - B)| ≤ δ) (ha : |A - a| ≤ Ea)
    (hb : |B - b| ≤ Eb) : |Z - (a - b)| ≤ δ + (Ea + Eb) := by
  have h := abs_add_three (Z - (A - B)) (A - a) (b - B)
  rw [show Z - (A - B) + (A - a) + (b - B) = Z - (a - b) by ring, abs_sub_comm b B] at h
  linarith

private theorem err_cmul {Z A a k δ Ea : ℝ} (hz : |Z - k * A| ≤ δ) (ha : |A - a| ≤ Ea) :
    |Z - k * a| ≤ δ + |k| * Ea := by
  have h := abs_add_le (Z - k * A) (k * (A - a))
  rw [show Z - k * A + k * (A - a) = Z - k * a by ring, abs_mul] at h
  have := mul_le_mul_of_nonneg_left ha (abs_nonneg k)
  linarith

private theorem err_mulc {Z A a k δ Ea : ℝ} (hz : |Z - A * k| ≤ δ) (ha : |A - a| ≤ Ea) :
    |Z - a * k| ≤ δ + Ea * |k| := by
  have h := abs_add_le (Z - A * k) ((A - a) * k)
  rw [show Z - A * k + (A - a) * k = Z - a * k by ring, abs_mul] at h
  have := mul_le_mul_of_nonneg_right ha (abs_nonneg k)
  linarith

private theorem abs_add_le_of {A B a b : ℝ} (ha : |A| ≤ a) (hb : |B| ≤ b) : |A + B| ≤ a + b :=
  (abs_add_le A B).trans (add_le_add ha hb)

private theorem abs_sub_le_of {A B a b : ℝ} (ha : |A| ≤ a) (hb : |B| ≤ b) : |A - B| ≤ a + b :=
  (abs_sub A B).trans (add_le_add ha hb)

private theorem abs_cmul_le_of {A a k : ℝ} (ha : |A| ≤ a) : |k * A| ≤ |k| * a := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left ha (abs_nonneg k)

private theorem abs_mulc_le_of {A a k : ℝ} (ha : |A| ≤ a) : |A * k| ≤ a * |k| := by
  rw [abs_mul]; exact mul_le_mul_of_nonneg_right ha (abs_nonneg k)

/-- **One step's roundings, on real numbers.** One SVF step computed with sixteen roundings:
`K1 ≈ k + g`, `P ≈ K1·S1`, `D1 ≈ X − P`, `D2 ≈ D1 − S2`, `H ≈ D2·d` (`hp`), `Q ≈ g·H`,
`B ≈ Q + S1` (`bp`), `R ≈ g·B`, `Lp ≈ R + S2` (`lp`), `Y1 ≈ m_hp·H`, `Y2 ≈ m_bp·B`,
`Y3 ≈ Y1 + Y2`, `Y4 ≈ m_lp·Lp`, output `Y ≈ Y3 + Y4`, new state `T1 ≈ Q + B` and `T2 ≈ R + Lp`.
Each rounding comes with a proposition `Fᵢ` (for floats, "this result is finite"): hypothesis
`hᵢ` says that if the propositions of its operands hold and its exact value `e` (on the computed
operands) is at most `V` in size, then `Fᵢ` holds and the rounding is within `u·|e| + η` of `e`.
If `0 ≤ u`, `0 ≤ η`, `|X| ≤ M`, `|S1|, |S2| ≤ Sb` and `stepValueBound ≤ V`, then all sixteen
`Fᵢ` hold, `Y` is within `stepErrOut` of `svfStep_real`'s output from `(S1, S2)` on `X`, and the
distances of `T1` and `T2` from its new state add up to at most `stepErrState`. -/
theorem step_chain (c : CoeffsReal)
    {u η M Sb V X S1 S2 K1 P D1 D2 H Q B R Lp Y1 Y2 Y3 Y4 Y T1 T2 : ℝ}
    {F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13 F14 F15 F16 : Prop}
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hX : |X| ≤ M) (hS1 : |S1| ≤ Sb) (hS2 : |S2| ≤ Sb)
    (hV : stepValueBound c u η M Sb ≤ V)
    (h1 : |c.k + c.g| ≤ V → F1 ∧ |K1 - (c.k + c.g)| ≤ u * |c.k + c.g| + η)
    (h2 : F1 → |K1 * S1| ≤ V → F2 ∧ |P - K1 * S1| ≤ u * |K1 * S1| + η)
    (h3 : F2 → |X - P| ≤ V → F3 ∧ |D1 - (X - P)| ≤ u * |X - P| + η)
    (h4 : F3 → |D1 - S2| ≤ V → F4 ∧ |D2 - (D1 - S2)| ≤ u * |D1 - S2| + η)
    (h5 : F4 → |D2 * c.d| ≤ V → F5 ∧ |H - D2 * c.d| ≤ u * |D2 * c.d| + η)
    (h6 : F5 → |c.g * H| ≤ V → F6 ∧ |Q - c.g * H| ≤ u * |c.g * H| + η)
    (h7 : F6 → |Q + S1| ≤ V → F7 ∧ |B - (Q + S1)| ≤ u * |Q + S1| + η)
    (h8 : F7 → |c.g * B| ≤ V → F8 ∧ |R - c.g * B| ≤ u * |c.g * B| + η)
    (h9 : F8 → |R + S2| ≤ V → F9 ∧ |Lp - (R + S2)| ≤ u * |R + S2| + η)
    (h10 : F5 → |c.m_hp * H| ≤ V → F10 ∧ |Y1 - c.m_hp * H| ≤ u * |c.m_hp * H| + η)
    (h11 : F7 → |c.m_bp * B| ≤ V → F11 ∧ |Y2 - c.m_bp * B| ≤ u * |c.m_bp * B| + η)
    (h12 : F10 → F11 → |Y1 + Y2| ≤ V → F12 ∧ |Y3 - (Y1 + Y2)| ≤ u * |Y1 + Y2| + η)
    (h13 : F9 → |c.m_lp * Lp| ≤ V → F13 ∧ |Y4 - c.m_lp * Lp| ≤ u * |c.m_lp * Lp| + η)
    (h14 : F12 → F13 → |Y3 + Y4| ≤ V → F14 ∧ |Y - (Y3 + Y4)| ≤ u * |Y3 + Y4| + η)
    (h15 : F6 → F7 → |Q + B| ≤ V → F15 ∧ |T1 - (Q + B)| ≤ u * |Q + B| + η)
    (h16 : F8 → F9 → |R + Lp| ≤ V → F16 ∧ |T2 - (R + Lp)| ≤ u * |R + Lp| + η) :
    (F1 ∧ F2 ∧ F3 ∧ F4 ∧ F5 ∧ F6 ∧ F7 ∧ F8 ∧ F9 ∧ F10 ∧ F11 ∧ F12 ∧ F13 ∧ F14 ∧ F15 ∧ F16) ∧
      |Y - (svfStep_real c (S1, S2) X).1| ≤ stepErrOut c u η M Sb ∧
      |T1 - (svfStep_real c (S1, S2) X).2.1| + |T2 - (svfStep_real c (S1, S2) X).2.2| ≤
        stepErrState c u η M Sb := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hX
  have hSb : 0 ≤ Sb := (abs_nonneg _).trans hS1
  -- Every operation bound is nonnegative, so each is at most `V`.
  have o1 : 0 ≤ opK1 c := abs_nonneg _
  have o2 : 0 ≤ opP c u η Sb := by unfold opP; positivity
  have o3 : 0 ≤ opD1 c u η M Sb := by unfold opD1; positivity
  have o4 : 0 ≤ opD2 c u η M Sb := by unfold opD2; positivity
  have o5 : 0 ≤ opH c u η M Sb := by unfold opH; positivity
  have o6 : 0 ≤ opQ c u η M Sb := by unfold opQ; positivity
  have o7 : 0 ≤ opB c u η M Sb := by unfold opB; positivity
  have o8 : 0 ≤ opR c u η M Sb := by unfold opR; positivity
  have o9 : 0 ≤ opL c u η M Sb := by unfold opL; positivity
  have o10 : 0 ≤ opY1 c u η M Sb := by unfold opY1; positivity
  have o11 : 0 ≤ opY2 c u η M Sb := by unfold opY2; positivity
  have o12 : 0 ≤ opY3 c u η M Sb := by unfold opY3; positivity
  have o13 : 0 ≤ opY4 c u η M Sb := by unfold opY4; positivity
  have o14 : 0 ≤ opY c u η M Sb := by unfold opY; positivity
  have o15 : 0 ≤ opT1 c u η M Sb := by unfold opT1; positivity
  have o16 : 0 ≤ opT2 c u η M Sb := by unfold opT2; positivity
  unfold stepValueBound at hV
  -- `K1 ≈ k + g`.
  have b1 : |c.k + c.g| ≤ opK1 c := le_rfl
  obtain ⟨f1, r1⟩ := h1 (by linarith)
  obtain ⟨d1, z1⟩ := rnd_bound hu r1 b1
  have e1 : |K1 - (c.k + c.g)| ≤ errK1 c u η := d1
  -- `P ≈ K1·S1`.
  have b2 : |K1 * S1| ≤ opP c u η Sb := by
    unfold opP; rw [abs_mul]; exact mul_le_mul z1 hS1 (abs_nonneg _) (by positivity)
  obtain ⟨f2, r2⟩ := h2 f1 (by linarith)
  obtain ⟨d2, z2⟩ := rnd_bound hu r2 b2
  have e2 : |P - (c.k + c.g) * S1| ≤ errP c u η Sb := by
    have := err_mulc d2 e1 (k := S1)
    have h := mul_le_mul_of_nonneg_left hS1 (by unfold errK1; positivity : 0 ≤ errK1 c u η)
    unfold errP; linarith
  -- `D1 ≈ X − P`.
  have b3 : |X - P| ≤ opD1 c u η M Sb := by unfold opD1; exact abs_sub_le_of hX z2
  obtain ⟨f3, r3⟩ := h3 f2 (by linarith)
  obtain ⟨d3, z3⟩ := rnd_bound hu r3 b3
  have e3 : |D1 - (X - (c.k + c.g) * S1)| ≤ errD1 c u η M Sb := by
    have := err_sub d3 (show |X - X| ≤ 0 by simp) e2
    unfold errD1; linarith
  -- `D2 ≈ D1 − S2`.
  have b4 : |D1 - S2| ≤ opD2 c u η M Sb := by unfold opD2; exact abs_sub_le_of z3 hS2
  obtain ⟨f4, r4⟩ := h4 f3 (by linarith)
  obtain ⟨d4, z4⟩ := rnd_bound hu r4 b4
  have e4 : |D2 - (X - (c.k + c.g) * S1 - S2)| ≤ errD2 c u η M Sb := by
    have := err_sub d4 e3 (show |S2 - S2| ≤ 0 by simp)
    unfold errD2; linarith
  -- `H ≈ D2·d`, the computed `hp`.
  have b5 : |D2 * c.d| ≤ opH c u η M Sb := by
    unfold opH; exact abs_mulc_le_of z4
  obtain ⟨f5, r5⟩ := h5 f4 (by linarith)
  obtain ⟨d5, z5⟩ := rnd_bound hu r5 b5
  obtain ⟨hp, hhp⟩ : ∃ hp, hp = (X - (c.k + c.g) * S1 - S2) * c.d := ⟨_, rfl⟩
  have e5 : |H - hp| ≤ errH c u η M Sb := by
    have := err_mulc d5 e4
    rw [hhp]; unfold errH; linarith
  -- `Q ≈ g·H`.
  have b6 : |c.g * H| ≤ opQ c u η M Sb := by unfold opQ; exact abs_cmul_le_of z5
  obtain ⟨f6, r6⟩ := h6 f5 (by linarith)
  obtain ⟨d6, z6⟩ := rnd_bound hu r6 b6
  have e6 : |Q - c.g * hp| ≤ errQ c u η M Sb := by
    have := err_cmul d6 e5
    unfold errQ; linarith
  -- `B ≈ Q + S1`, the computed `bp`.
  have b7 : |Q + S1| ≤ opB c u η M Sb := by unfold opB; exact abs_add_le_of z6 hS1
  obtain ⟨f7, r7⟩ := h7 f6 (by linarith)
  obtain ⟨d7, z7⟩ := rnd_bound hu r7 b7
  obtain ⟨bp, hbp⟩ : ∃ bp, bp = c.g * hp + S1 := ⟨_, rfl⟩
  have e7 : |B - bp| ≤ errB c u η M Sb := by
    have := err_add d7 e6 (show |S1 - S1| ≤ 0 by simp)
    rw [hbp]; unfold errB; linarith
  -- `R ≈ g·B`.
  have b8 : |c.g * B| ≤ opR c u η M Sb := by unfold opR; exact abs_cmul_le_of z7
  obtain ⟨f8, r8⟩ := h8 f7 (by linarith)
  obtain ⟨d8, z8⟩ := rnd_bound hu r8 b8
  have e8 : |R - c.g * bp| ≤ errR c u η M Sb := by
    have := err_cmul d8 e7
    unfold errR; linarith
  -- `Lp ≈ R + S2`, the computed `lp`.
  have b9 : |R + S2| ≤ opL c u η M Sb := by unfold opL; exact abs_add_le_of z8 hS2
  obtain ⟨f9, r9⟩ := h9 f8 (by linarith)
  obtain ⟨d9, z9⟩ := rnd_bound hu r9 b9
  obtain ⟨lp, hlp⟩ : ∃ lp, lp = c.g * bp + S2 := ⟨_, rfl⟩
  have e9 : |Lp - lp| ≤ errL c u η M Sb := by
    have := err_add d9 e8 (show |S2 - S2| ≤ 0 by simp)
    rw [hlp]; unfold errL; linarith
  -- The output: `Y1 ≈ m_hp·H`, `Y2 ≈ m_bp·B`, `Y3 ≈ Y1 + Y2`, `Y4 ≈ m_lp·Lp`, `Y ≈ Y3 + Y4`.
  have b10 : |c.m_hp * H| ≤ opY1 c u η M Sb := by unfold opY1; exact abs_cmul_le_of z5
  obtain ⟨f10, r10⟩ := h10 f5 (by linarith)
  obtain ⟨d10, z10⟩ := rnd_bound hu r10 b10
  have e10 : |Y1 - c.m_hp * hp| ≤ errY1 c u η M Sb := by
    have := err_cmul d10 e5
    unfold errY1; linarith
  have b11 : |c.m_bp * B| ≤ opY2 c u η M Sb := by unfold opY2; exact abs_cmul_le_of z7
  obtain ⟨f11, r11⟩ := h11 f7 (by linarith)
  obtain ⟨d11, z11⟩ := rnd_bound hu r11 b11
  have e11 : |Y2 - c.m_bp * bp| ≤ errY2 c u η M Sb := by
    have := err_cmul d11 e7
    unfold errY2; linarith
  have b12 : |Y1 + Y2| ≤ opY3 c u η M Sb := by unfold opY3; exact abs_add_le_of z10 z11
  obtain ⟨f12, r12⟩ := h12 f10 f11 (by linarith)
  obtain ⟨d12, z12⟩ := rnd_bound hu r12 b12
  have e12 : |Y3 - (c.m_hp * hp + c.m_bp * bp)| ≤ errY3 c u η M Sb := by
    have := err_add d12 e10 e11
    unfold errY3; linarith
  have b13 : |c.m_lp * Lp| ≤ opY4 c u η M Sb := by unfold opY4; exact abs_cmul_le_of z9
  obtain ⟨f13, r13⟩ := h13 f9 (by linarith)
  obtain ⟨d13, z13⟩ := rnd_bound hu r13 b13
  have e13 : |Y4 - c.m_lp * lp| ≤ errY4 c u η M Sb := by
    have := err_cmul d13 e9
    unfold errY4; linarith
  have b14 : |Y3 + Y4| ≤ opY c u η M Sb := by unfold opY; exact abs_add_le_of z12 z13
  obtain ⟨f14, r14⟩ := h14 f12 f13 (by linarith)
  obtain ⟨d14, -⟩ := rnd_bound hu r14 b14
  have e14 : |Y - (c.m_hp * hp + c.m_bp * bp + c.m_lp * lp)| ≤ errY c u η M Sb := by
    have := err_add d14 e12 e13
    unfold errY; linarith
  -- The new state: `T1 ≈ Q + B`, `T2 ≈ R + Lp`.
  have b15 : |Q + B| ≤ opT1 c u η M Sb := by unfold opT1; exact abs_add_le_of z6 z7
  obtain ⟨f15, r15⟩ := h15 f6 f7 (by linarith)
  obtain ⟨d15, -⟩ := rnd_bound hu r15 b15
  have e15 : |T1 - (c.g * hp + bp)| ≤ errT1 c u η M Sb := by
    have := err_add d15 e6 e7
    unfold errT1; linarith
  have b16 : |R + Lp| ≤ opT2 c u η M Sb := by unfold opT2; exact abs_add_le_of z8 z9
  obtain ⟨f16, r16⟩ := h16 f8 f9 (by linarith)
  obtain ⟨d16, -⟩ := rnd_bound hu r16 b16
  have e16 : |T2 - (c.g * bp + lp)| ≤ errT2 c u η M Sb := by
    have := err_add d16 e8 e9
    unfold errT2; linarith
  subst hlp hbp hhp
  refine ⟨⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16⟩, ?_, ?_⟩
  · exact e14
  · unfold stepErrState
    exact add_le_add e15 e16

/-- `stepErrOut` is nonnegative. -/
theorem stepErrOut_nonneg (c : CoeffsReal) {u η M Sb : ℝ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hM : 0 ≤ M) (hSb : 0 ≤ Sb) : 0 ≤ stepErrOut c u η M Sb := by
  unfold_step_bounds
  positivity

/-- `stepErrOut` is positive when `η > 0`. -/
theorem stepErrOut_pos (c : CoeffsReal) {u η M Sb : ℝ} (hu : 0 ≤ u) (hη : 0 < η)
    (hM : 0 ≤ M) (hSb : 0 ≤ Sb) : 0 < stepErrOut c u η M Sb := by
  unfold_step_bounds
  positivity

/-- `stepErrState` is nonnegative. -/
theorem stepErrState_nonneg (c : CoeffsReal) {u η M Sb : ℝ} (hu : 0 ≤ u) (hη : 0 ≤ η)
    (hM : 0 ≤ M) (hSb : 0 ≤ Sb) : 0 ≤ stepErrState c u η M Sb := by
  unfold_step_bounds
  positivity

/-- **One step's roundings, without finiteness.** `step_chain` with every `Fᵢ` true: if
`0 ≤ u`, `0 ≤ η`, `|X| ≤ M`, `|S1|, |S2| ≤ Sb`, and each of the sixteen roundings is within
`u·|e| + η` of its exact operation `e` on the computed operands, then `Y` is within
`stepErrOut` of `svfStep_real`'s output from `(S1, S2)` on `X`, and the distances of `T1` and `T2`
from its new state add up to at most `stepErrState`. -/
theorem step_localErr (c : CoeffsReal)
    {u η M Sb X S1 S2 K1 P D1 D2 H Q B R Lp Y1 Y2 Y3 Y4 Y T1 T2 : ℝ}
    (hu : 0 ≤ u) (hη : 0 ≤ η) (hX : |X| ≤ M) (hS1 : |S1| ≤ Sb) (hS2 : |S2| ≤ Sb)
    (h1 : |K1 - (c.k + c.g)| ≤ u * |c.k + c.g| + η)
    (h2 : |P - K1 * S1| ≤ u * |K1 * S1| + η)
    (h3 : |D1 - (X - P)| ≤ u * |X - P| + η)
    (h4 : |D2 - (D1 - S2)| ≤ u * |D1 - S2| + η)
    (h5 : |H - D2 * c.d| ≤ u * |D2 * c.d| + η)
    (h6 : |Q - c.g * H| ≤ u * |c.g * H| + η)
    (h7 : |B - (Q + S1)| ≤ u * |Q + S1| + η)
    (h8 : |R - c.g * B| ≤ u * |c.g * B| + η)
    (h9 : |Lp - (R + S2)| ≤ u * |R + S2| + η)
    (h10 : |Y1 - c.m_hp * H| ≤ u * |c.m_hp * H| + η)
    (h11 : |Y2 - c.m_bp * B| ≤ u * |c.m_bp * B| + η)
    (h12 : |Y3 - (Y1 + Y2)| ≤ u * |Y1 + Y2| + η)
    (h13 : |Y4 - c.m_lp * Lp| ≤ u * |c.m_lp * Lp| + η)
    (h14 : |Y - (Y3 + Y4)| ≤ u * |Y3 + Y4| + η)
    (h15 : |T1 - (Q + B)| ≤ u * |Q + B| + η)
    (h16 : |T2 - (R + Lp)| ≤ u * |R + Lp| + η) :
    |Y - (svfStep_real c (S1, S2) X).1| ≤ stepErrOut c u η M Sb ∧
      |T1 - (svfStep_real c (S1, S2) X).2.1| + |T2 - (svfStep_real c (S1, S2) X).2.2| ≤
        stepErrState c u η M Sb :=
  (step_chain c (V := stepValueBound c u η M Sb) (F1 := True) (F2 := True) (F3 := True)
    (F4 := True) (F5 := True) (F6 := True) (F7 := True) (F8 := True) (F9 := True)
    (F10 := True) (F11 := True) (F12 := True) (F13 := True) (F14 := True) (F15 := True)
    (F16 := True) hu hη hX hS1 hS2 le_rfl
    (fun _ => ⟨trivial, h1⟩) (fun _ _ => ⟨trivial, h2⟩) (fun _ _ => ⟨trivial, h3⟩)
    (fun _ _ => ⟨trivial, h4⟩) (fun _ _ => ⟨trivial, h5⟩) (fun _ _ => ⟨trivial, h6⟩)
    (fun _ _ => ⟨trivial, h7⟩) (fun _ _ => ⟨trivial, h8⟩) (fun _ _ => ⟨trivial, h9⟩)
    (fun _ _ => ⟨trivial, h10⟩) (fun _ _ => ⟨trivial, h11⟩) (fun _ _ _ => ⟨trivial, h12⟩)
    (fun _ _ => ⟨trivial, h13⟩) (fun _ _ _ => ⟨trivial, h14⟩) (fun _ _ _ => ⟨trivial, h15⟩)
    (fun _ _ _ => ⟨trivial, h16⟩)).2

end conjure_dsp_lib.svf

end
