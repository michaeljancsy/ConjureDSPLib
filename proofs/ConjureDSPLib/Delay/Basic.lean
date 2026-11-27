module

public import Aeneas
public import Mathlib.Data.List.Rotate

/-!
# The delay line: facts shared by both precisions

Facts about natural numbers, lists and Aeneas's `Result` that `SpecF64.lean` and `SpecF32.lean`
both use, for `process`, `read` and `write`. None mentions a float.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace conjure_dsp_lib.delay

/-- Moving on by one and wrapping at `L` is adding one mod `L`. -/
theorem succ_mod_eq (x L : ℕ) (hL : 0 < L) :
    (x + 1) % L = if x % L + 1 = L then 0 else x % L + 1 := by
  have hx := Nat.mod_lt x hL
  rcases (by omega : L = 1 ∨ 2 ≤ L) with rfl | h2
  · simp [Nat.mod_one]
  · rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < L)]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)

/-- Choosing between two results that cannot fail is choosing between their values. -/
theorem ite_ok {α : Type} (c : Prop) [Decidable c] (x y : α) :
    (if c then (ok x : Result α) else ok y) = ok (if c then x else y) := by
  split <;> rfl

/-- `m ⦃ P ⦄` (Aeneas's notation for "running `m` never fails, and its result satisfies `P`")
means that `m` returns some `x` with `P x`. -/
theorem exists_ok_of_spec {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) :
    ∃ x, m = ok x ∧ P x := by
  revert h
  cases m <;> simp

/-- After the loop: buffer index `k` holds history sample `n + (k - w) mod L`, so reading the
buffer in time order from `w` gives the history from sample `n` on. -/
theorem rotate_eq_drop {α : Type} (L n w : ℕ) (S b : List α) (hS : S.length = L + n)
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

/-- Dropping `n₁` samples, appending `a₂`, then dropping `n₂` more is appending `a₂` and then
dropping `n₁ + n₂`, when `H` has at least `n₁` samples. -/
theorem drop_append_drop {α : Type} (H a₂ : List α) (n₁ n₂ : ℕ) (h : n₁ ≤ H.length) :
    (H.drop n₁ ++ a₂).drop n₂ = (H ++ a₂).drop (n₁ + n₂) := by
  rw [← List.drop_append_of_le_length h, List.drop_drop]

/-- Outputs of two blocks, each read from its own history at `L + j - d`, joined together, are
the outputs of one block read from the whole history: `o₁` comes from `R ++ a₁`, `o₂` from
`(R ++ a₁).drop n₁ ++ a₂` (the history after the first block, then `a₂`), and `o` from
`R ++ a₁ ++ a₂`. -/
theorem outputs_append {α : Type} (R a₁ a₂ o₁ o₂ o : List α) (L d : ℕ) (hR : R.length = L)
    (hd : d ≤ L) (ho₁ : o₁.length = a₁.length)
    (h₁ : ∀ j < a₁.length, o₁[j]? = (R ++ a₁)[L + j - d]?) (ho₂ : o₂.length = a₂.length)
    (h₂ : ∀ j < a₂.length, o₂[j]? = ((R ++ a₁).drop a₁.length ++ a₂)[L + j - d]?)
    (ho : o.length = a₁.length + a₂.length)
    (h : ∀ j < a₁.length + a₂.length, o[j]? = (R ++ a₁ ++ a₂)[L + j - d]?) :
    o₁ ++ o₂ = o := by
  apply List.ext_getElem?
  intro m
  rcases Nat.lt_or_ge m a₁.length with hm | hm
  · rw [List.getElem?_append_left (by omega), h₁ m hm, h m (by omega),
      List.getElem?_append_left (l₁ := R ++ a₁) (by simp; omega)]
  · rcases Nat.lt_or_ge m (a₁.length + a₂.length) with hm' | hm'
    · rw [List.getElem?_append_right (by omega), ho₁, h₂ _ (by omega), h m hm',
        ← List.drop_append_of_le_length (by simp), List.getElem?_drop]
      congr 1
      omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- The read index of `read_f64` / `read_f32`, written with `mod`: for `L > 0`, with
`d = min D (L - 1)` and `w = p mod L`, `(p + L - d) mod L` is `w - d` when `d ≤ w`, and
`w + (L - d)` otherwise. -/
theorem read_index_eq (L p D d w : ℕ) (hL : 0 < L) (hd : d = min D (L - 1)) (hw : w = p % L) :
    (p + L - min D (L - 1)) % L = if d ≤ w then w - d else w + (L - d) := by
  rw [← hd]
  subst hw
  have hdL : d < L := by omega
  obtain ⟨q, t, hq, rfl⟩ : ∃ q t, q < L ∧ p = q + L * t :=
    ⟨p % L, p / L, Nat.mod_lt _ hL, (Nat.mod_add_div p L).symm⟩
  have hmod : (q + L * t) % L = q := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hq]
  rw [hmod]
  have e : q + L * t + L - d = (q + L - d) + L * t := by
    generalize L * t = m
    omega
  rw [e, Nat.add_mul_mod_self_left]
  split_ifs with h
  · rw [show q + L - d = (q - d) + L by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Writing `x` at index `p mod L` of a list of length `L > 0` and reading the result in time
order from `(p + 1) mod L` gives the list read in time order from `p`, followed by `x`, without
its first (oldest) element. -/
theorem rotate_set_eq_drop {α : Type} (l : List α) (p : ℕ) (x : α) (hL : 0 < l.length) :
    (l.set (p % l.length) x).rotate ((p + 1) % l.length) = (l.rotate p ++ [x]).drop 1 := by
  have hq : p % l.length < l.length := Nat.mod_lt _ hL
  have htake : (l.take (p % l.length)).length = p % l.length := by
    simp only [List.length_take]
    omega
  rw [List.set_eq_take_append_cons_drop, if_pos hq, ← List.rotate_mod l p,
    List.rotate_eq_drop_append_take hq.le, List.drop_eq_getElem_cons hq, succ_mod_eq p _ hL]
  split_ifs with h
  · have hnil : l.drop (p % l.length + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simp [hnil]
  · rw [List.rotate_eq_drop_append_take (by
      simp only [List.length_append, List.length_cons, List.length_drop, htake]
      omega)]
    have h1 : (l.take (p % l.length)).drop (p % l.length + 1) = [] :=
      List.drop_eq_nil_of_le (by rw [htake]; omega)
    have h2 : (l.take (p % l.length)).take (p % l.length + 1) = l.take (p % l.length) :=
      List.take_of_length_le (by rw [htake]; omega)
    rw [List.drop_append, List.take_append, h1, h2, htake, Nat.add_sub_cancel_left]
    simp

end conjure_dsp_lib.delay

end
