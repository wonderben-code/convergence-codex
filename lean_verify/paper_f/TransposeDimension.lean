import TransposeSplit

/-!
# `dim Sym_n = n(n+1)/2` at every finite index type, not just at `n = 2`

`TransposeSplit` built the transpose's two eigenspaces as `Submodule ℂ`s and computed both
dimensions **at `Fin 2` only**, from the complement of a one-dimensional span. Its own "what is
NOT claimed" section says so:

> *"**No general `n`.** `dim Sym_n = n(n+1)/2` is not proved here; `finrank_symSub_two` is
> `n = 2`, obtained from the complement rather than from a basis. The general formula that
> `F2_3_ChiralityForced`'s docstring calls "standard linear algebra" was, as of 2026-08-28, still
> unproved anywhere in the estate."*

**This file removes that restriction.** The route is a coordinate map, not a basis: an
antisymmetric matrix is determined by, and freely determined by, its strictly-upper-triangular
entries, so `asymSub ι` is linearly equivalent to functions on `{(i, j) : i < j}`. Counting that
index set against the diagonal gives the dimension; the symmetric side follows from the
complement that `TransposeSplit` already proved.

## What is proved

> **`asymEquiv`** — a `LinearEquiv` between `asymSub ι` and `UpperPairs ι → ℂ` at any finite
> **linearly ordered** index type. Injectivity is antisymmetry (the lower triangle is minus the
> upper, the diagonal is minus itself); surjectivity is an explicit inverse `ofUpper` that fills
> the lower triangle by negation and the diagonal with zero.
>
> **`two_mul_card_upperPairs`** — `2 · #{(i, j) : i < j} + #ι = #ι · #ι`, obtained by splitting
> `Finset.offDiag` into its two halves and swapping them into each other.
>
> **`two_mul_finrank_asymSub_of_fintype`** and **`two_mul_finrank_symSub_of_fintype`** — the two
> dimensions at **any finite index type, with no order hypothesis at all**. The order is
> scaffolding: it is what `UpperPairs` needs to pick a representative of `{i, j}`, and since the
> conclusions name no order it can be manufactured inside the proof from `Fintype.equivFin`
> rather than demanded of the caller. Both are stated multiplicatively, so that neither truncated
> subtraction nor natural-number division appears in the statement.
>
> **`finrank_asymSub_choose`** and **`finrank_symSub_choose`** — the same two facts as binomial
> coefficients, `C(#ι, 2)` and `C(#ι + 1, 2)`: one free parameter per unordered pair of distinct
> indices, and one per unordered pair distinct or not.
>
> **`finrank_asymSub_fin`** and **`finrank_symSub_fin`** — the familiar closed forms `n(n−1)/2`
> and `n(n+1)/2` at `ι = Fin n`. The second is the formula `TransposeSplit`'s header recorded as
> unproved anywhere in the estate.
>
> **`general_recovers_two`** — the general count returns `1` and `3` at `n = 2`. For the
> antisymmetric side this is a real cross-check against an unrelated route (a one-element span);
> for the symmetric side it is not, and the docstring says why. Neither is a second proof of the
> `Fin 2` case, which stands where it was written.

## What is NOT claimed

**No basis is constructed.** `asymEquiv` is a linear equivalence with an explicitly given
inverse, and a basis can be pulled back through it, but no `Module.Basis` is defined below and
none of the usual basis lemmas are available from this file.

**The `Fin 2` agreement is weaker on the symmetric side than on the antisymmetric side.**
`TransposeSplit.finrank_asymSub_two` came from `asymSub (Fin 2)` being the span of one nonzero
matrix — a route this file never takes — so `1` is genuinely derived twice.
`TransposeSplit.finrank_symSub_two`, however, came from `isCompl_symSub_asymSub` by subtracting
that `1` from `4`, and **this file reaches `3` through the same complement**. Only the input
differs. `general_recovers_two`'s docstring states this rather than letting the pair read as two
independent confirmations.

**`ℂ` throughout, and no other field.** `symSub` and `asymSub` are `TransposeSplit`'s spaces
over `ℂ`, and every statement below is over `ℂ`. The restriction is deliberate rather than
incidental: in characteristic `2` the conditions `Aᵀ = A` and `Aᵀ = -A` are the same condition,
so the two spaces would coincide and could not be complementary. **That last sentence is prose,
not a theorem below** — nothing here is proved, or disproved, over any field but `ℂ`.

**Nothing about `SU(2)`, spin, representations, or Lie brackets.** `symSub` is not a Lie
subalgebra and this file does not say it is; the transpose splitting is a splitting of the
*module* `Matrix ι ι ℂ` and nothing below brackets two elements together. `TransposeSplit`'s
correction of `F2_3_ChiralityForced`'s parenthetical is unaffected and unrepeated here.

**Nothing in `TransposeSplit` is withdrawn.** `finrank_asymSub_two` and `finrank_symSub_two`
keep their proofs; the file's `n = 2` restriction is superseded rather than corrected, and a
dated note in that file says so.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TransposeDimension

open Matrix TransposeSplit

/-! ## 1. The strictly-upper index set and its cardinality -/

/-- The index set of a strictly upper triangle: ordered pairs `(i, j)` with `i < j`. This is
where the free parameters of an antisymmetric matrix live. -/
abbrev UpperPairs (ι : Type*) [LT ι] : Type _ := {p : ι × ι // p.1 < p.2}

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The filter defining `UpperPairs` may be taken over `Finset.offDiag` instead of over all of
`ι × ι`, because `i < j` already forbids `i = j`. -/
theorem filter_lt_eq_offDiag_filter :
    {p ∈ (Finset.univ : Finset (ι × ι)) | p.1 < p.2}
      = {p ∈ (Finset.univ : Finset ι).offDiag | p.1 < p.2} := by
  ext p
  constructor
  · intro hp
    have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
      ⟨Finset.mem_univ _, Finset.mem_univ _, ne_of_lt hlt⟩, hlt⟩
  · intro hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩

/-- Swapping coordinates carries the strictly-upper half of `offDiag` onto the strictly-lower
half, so the two halves have the same size. -/
theorem card_filter_lt_eq_card_filter_not_lt :
    {p ∈ (Finset.univ : Finset ι).offDiag | p.1 < p.2}.card
      = {p ∈ (Finset.univ : Finset ι).offDiag | ¬ p.1 < p.2}.card := by
  refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_offDiag, Finset.mem_univ,
      true_and] at hp ⊢
    exact ⟨(Ne.symm hp.1), not_lt.mpr (le_of_lt hp.2)⟩
  · rintro ⟨i, j⟩ hp
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_offDiag, Finset.mem_univ,
      true_and] at hp ⊢
    exact ⟨(Ne.symm hp.1), lt_of_le_of_ne (not_lt.mp hp.2) (Ne.symm hp.1)⟩
  · rintro ⟨i, j⟩ _
    rfl
  · rintro ⟨i, j⟩ _
    rfl

/-- **The count.** Twice the number of strictly-upper pairs, plus the diagonal, is `#ι · #ι`.
Stated this way so that neither truncated subtraction nor natural division occurs. -/
theorem two_mul_card_upperPairs :
    2 * Fintype.card (UpperPairs ι) + Fintype.card ι = Fintype.card ι * Fintype.card ι := by
  classical
  have hsplit :
      {p ∈ (Finset.univ : Finset ι).offDiag | p.1 < p.2}.card
        + {p ∈ (Finset.univ : Finset ι).offDiag | ¬ p.1 < p.2}.card
        = (Finset.univ : Finset ι).offDiag.card :=
    Finset.card_filter_add_card_filter_not _
  have hoff : (Finset.univ : Finset ι).offDiag.card
      = Fintype.card ι * Fintype.card ι - Fintype.card ι := by
    simp [Finset.card_univ]
  have hcard : Fintype.card (UpperPairs ι)
      = {p ∈ (Finset.univ : Finset ι).offDiag | p.1 < p.2}.card := by
    rw [← filter_lt_eq_offDiag_filter]
    exact Fintype.card_subtype _
  have hle : Fintype.card ι ≤ Fintype.card ι * Fintype.card ι := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  rw [hcard]
  rw [← card_filter_lt_eq_card_filter_not_lt] at hsplit
  generalize Fintype.card ι * Fintype.card ι = M at hoff hle ⊢
  omega

/-! ## 2. Antisymmetric matrices are their strictly-upper entries -/

omit [Fintype ι] [LinearOrder ι] in
/-- Antisymmetry read off one pair of entries: `A j i = -A i j`. -/
theorem entry_swap {A : Matrix ι ι ℂ} (hA : Aᵀ = -A) (i j : ι) : A j i = -A i j := by
  have h := congrFun (congrFun hA i) j
  simpa using h

omit [Fintype ι] in
/-- An antisymmetric matrix whose strictly-upper entries all vanish is zero: the lower triangle
is minus the upper, and each diagonal entry is minus itself. -/
theorem eq_zero_of_upper_eq_zero {A : Matrix ι ι ℂ} (hA : Aᵀ = -A)
    (h : ∀ i j, i < j → A i j = 0) : A = 0 := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · simpa using h i j hij
  · subst hij
    have hd : A i i = -A i i := by
      have := entry_swap hA i i
      simpa using this
    have : A i i = 0 := by linear_combination hd / 2
    simpa using this
  · have h1 : A j i = 0 := h j i hij
    have h2 : A j i = -A i j := entry_swap hA i j
    have : A i j = 0 := by linear_combination h2 - h1
    simpa using this

/-- The coordinate map: an antisymmetric matrix restricted to its strictly-upper entries. -/
def asymCoords (ι : Type*) [Fintype ι] [LinearOrder ι] :
    asymSub ι →ₗ[ℂ] (UpperPairs ι → ℂ) where
  toFun A := fun p => (A : Matrix ι ι ℂ) p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse construction: fill the strictly-upper triangle from `f`, the strictly-lower
triangle by negation, and the diagonal with zero. -/
def ofUpper (f : UpperPairs ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => if h : i < j then f ⟨(i, j), h⟩ else if h' : j < i then -f ⟨(j, i), h'⟩ else 0

omit [Fintype ι] in
/-- `ofUpper f` really is antisymmetric. -/
theorem ofUpper_transpose (f : UpperPairs ι → ℂ) : (ofUpper f)ᵀ = -(ofUpper f) := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, ofUpper]
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_neg (asymm h), dif_pos h, dif_pos h]
  · subst h
    rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i), neg_zero]
  · rw [dif_pos h, dif_neg (asymm h), dif_pos h, neg_neg]

/-- `ofUpper` is a right inverse of `asymCoords`. -/
theorem asymCoords_ofUpper (f : UpperPairs ι → ℂ) :
    asymCoords ι ⟨ofUpper f, ofUpper_transpose f⟩ = f := by
  funext p
  obtain ⟨⟨i, j⟩, hij⟩ := p
  simp only [asymCoords, LinearMap.coe_mk, AddHom.coe_mk, ofUpper, dif_pos hij]

theorem asymCoords_injective : Function.Injective (asymCoords ι) := by
  intro A B hAB
  apply Subtype.ext
  have hA : (A : Matrix ι ι ℂ)ᵀ = -(A : Matrix ι ι ℂ) := A.2
  have hB : (B : Matrix ι ι ℂ)ᵀ = -(B : Matrix ι ι ℂ) := B.2
  have hsub : ((A : Matrix ι ι ℂ) - (B : Matrix ι ι ℂ))ᵀ
      = -((A : Matrix ι ι ℂ) - (B : Matrix ι ι ℂ)) := by
    rw [Matrix.transpose_sub, hA, hB]
    abel
  have hzero : (A : Matrix ι ι ℂ) - (B : Matrix ι ι ℂ) = 0 := by
    refine eq_zero_of_upper_eq_zero hsub ?_
    intro i j hij
    have := congrFun hAB ⟨(i, j), hij⟩
    simp only [asymCoords, LinearMap.coe_mk, AddHom.coe_mk] at this
    simp [this]
  exact sub_eq_zero.mp hzero

theorem asymCoords_surjective : Function.Surjective (asymCoords ι) :=
  fun f => ⟨⟨ofUpper f, ofUpper_transpose f⟩, asymCoords_ofUpper f⟩

/-- **The equivalence.** Antisymmetric matrices are exactly free choices of strictly-upper
entries. -/
noncomputable def asymEquiv (ι : Type*) [Fintype ι] [LinearOrder ι] :
    asymSub ι ≃ₗ[ℂ] (UpperPairs ι → ℂ) :=
  LinearEquiv.ofBijective (asymCoords ι) ⟨asymCoords_injective, asymCoords_surjective⟩

/-! ## 3. The two dimensions at any finite linearly ordered index type -/

theorem finrank_asymSub_eq_card :
    Module.finrank ℂ (asymSub ι) = Fintype.card (UpperPairs ι) := by
  rw [(asymEquiv ι).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- `2 · dim Asym + #ι = #ι · #ι`. -/
theorem two_mul_finrank_asymSub :
    2 * Module.finrank ℂ (asymSub ι) + Fintype.card ι = Fintype.card ι * Fintype.card ι := by
  rw [finrank_asymSub_eq_card]
  exact two_mul_card_upperPairs

omit [LinearOrder ι] in
theorem finrank_matrix_eq :
    Module.finrank ℂ (Matrix ι ι ℂ) = Fintype.card ι * Fintype.card ι := by
  simp [Module.finrank_matrix]

omit [LinearOrder ι] in
/-- The complement `TransposeSplit.isCompl_symSub_asymSub` turns one dimension into the other.
The order plays no part here, which is why this statement carries no `LinearOrder`. -/
theorem finrank_symSub_add_finrank_asymSub :
    Module.finrank ℂ (symSub ι) + Module.finrank ℂ (asymSub ι)
      = Fintype.card ι * Fintype.card ι := by
  rw [Submodule.finrank_add_eq_of_isCompl isCompl_symSub_asymSub, finrank_matrix_eq]

/-- `2 · dim Sym = #ι · #ι + #ι`. -/
theorem two_mul_finrank_symSub :
    2 * Module.finrank ℂ (symSub ι) = Fintype.card ι * Fintype.card ι + Fintype.card ι := by
  have h1 := two_mul_finrank_asymSub (ι := ι)
  have h2 := finrank_symSub_add_finrank_asymSub (ι := ι)
  omega

/-! ## 4. The linear order was scaffolding -/

/-! The order below is transported from `Fin (card ι)`, which every finite type admits. It is
introduced with `letI` inside the two proofs and **deliberately never registered as an
`instance`**: a `LinearOrder` on every `Fintype` would collide with the orders types already
carry — `Fin n` most of all — and the collision would be silent and global. Nothing depends on
which order it is, because the statements it proves name no order at all. -/

/-- `2 · dim Asym + #ι = #ι · #ι` at **any** finite index type. -/
theorem two_mul_finrank_asymSub_of_fintype (ι : Type*) [Fintype ι] :
    2 * Module.finrank ℂ (asymSub ι) + Fintype.card ι = Fintype.card ι * Fintype.card ι := by
  letI : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact two_mul_finrank_asymSub

/-- `2 · dim Sym = #ι · #ι + #ι` at **any** finite index type. -/
theorem two_mul_finrank_symSub_of_fintype (ι : Type*) [Fintype ι] :
    2 * Module.finrank ℂ (symSub ι) = Fintype.card ι * Fintype.card ι + Fintype.card ι := by
  letI : LinearOrder ι :=
    LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact two_mul_finrank_symSub

/-! ## 5. Closed forms -/

/-- The arithmetic bridge `n(n−1) + n = n·n`, stated separately because truncated subtraction
makes it false-looking and `ring` cannot see through `n - 1` at `n = 0`. -/
theorem nat_mul_sub_one_add_self (n : ℕ) : n * (n - 1) + n = n * n := by
  cases n with
  | zero => rfl
  | succ k => simp only [Nat.succ_sub_one]; ring

/-- **`dim Asym_ι = C(#ι, 2)`** — one free parameter per unordered pair of distinct indices. -/
theorem finrank_asymSub_choose (ι : Type*) [Fintype ι] :
    Module.finrank ℂ (asymSub ι) = (Fintype.card ι).choose 2 := by
  have h := two_mul_finrank_asymSub_of_fintype ι
  have hmul := nat_mul_sub_one_add_self (Fintype.card ι)
  rw [Nat.choose_two_right]
  omega

/-- **`dim Sym_ι = C(#ι + 1, 2)`** — one free parameter per unordered pair, distinct or not. -/
theorem finrank_symSub_choose (ι : Type*) [Fintype ι] :
    Module.finrank ℂ (symSub ι) = (Fintype.card ι + 1).choose 2 := by
  have h := two_mul_finrank_symSub_of_fintype ι
  have hmul : (Fintype.card ι + 1) * Fintype.card ι
      = Fintype.card ι * Fintype.card ι + Fintype.card ι := by ring
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  omega

/-- The familiar `n(n−1)/2`. -/
theorem finrank_asymSub_fin (n : ℕ) :
    Module.finrank ℂ (asymSub (Fin n)) = n * (n - 1) / 2 := by
  rw [finrank_asymSub_choose, Fintype.card_fin, Nat.choose_two_right]

/-- The familiar `n(n+1)/2` — the formula `TransposeSplit`'s header recorded as unproved. -/
theorem finrank_symSub_fin (n : ℕ) :
    Module.finrank ℂ (symSub (Fin n)) = n * (n + 1) / 2 := by
  rw [finrank_symSub_choose, Fintype.card_fin, Nat.choose_two_right, Nat.add_sub_cancel,
    Nat.mul_comm]

/-- **Agreement with the `n = 2` case.**

For the antisymmetric side this is a genuine cross-check: `TransposeSplit.finrank_asymSub_two`
came from `asymSub (Fin 2)` being the span of one nonzero matrix, and `finrank_asymSub_fin` comes
from the coordinate equivalence, which never mentions `Fin 2`. Two unrelated routes, same numeral.

For the symmetric side it is **weaker than that, and the difference is worth stating**: both
routes obtain `dim Sym` from `TransposeSplit.isCompl_symSub_asymSub` by subtracting `dim Asym`
from `4`. Only the input differs. So `3` is not independently re-derived here; what is
independently re-derived is the `1` it is computed from. -/
theorem general_recovers_two :
    Module.finrank ℂ (asymSub (Fin 2)) = 1 ∧ Module.finrank ℂ (symSub (Fin 2)) = 3 :=
  ⟨by rw [finrank_asymSub_fin], by rw [finrank_symSub_fin]⟩

end TransposeDimension
