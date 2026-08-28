import TracelessRealSplit
import CascadeFoundation

/-!
# `M₂(ℂ)` has two different `3 + 1` decompositions, and one file glosses one as the other

`F2_3_ChiralityForced` writes, in the prose of Part 6:

> *"`M₂ = Sym₂ ⊕ Asym₂`; `dim(Sym₂) = 3` (**the SU(2) Lie algebra + identity, i.e., spin-1 +
> scalar**); `dim(Asym₂) = 1`."*

**The parenthetical describes a different decomposition.** "Spin-1 plus scalar" is
`traceless ⊕ ℂ·I`, the `SU(2)`-equivariant splitting of `M₂(ℂ)` by the **trace**; the file's
`Sym₂ ⊕ Asym₂` is the splitting by the **transpose**. Both are `3 + 1`, and they are **not the
same two spaces**: the identity is symmetric and not traceless, and the antisymmetric generator is
traceless and not a scalar. The gloss also does not add up on its own terms — "the `SU(2)` Lie
algebra + identity" is `3 + 1 = 4`, attached to a space of dimension `3`.

**This is `ERRATUM 325`'s pattern a third time**: two different decompositions with the same pair
of dimensions, conflated because nothing in the estate could compare the spaces. That file's four
results — `sym_dim_2`, `asym_dim_2`, `sym_asym_total`, `transpose_eigenspaces` — are **arithmetic
on numerals**; `sym_dim_2` is literally `2 * (2 + 1) / 2 = 3`, and its own docstring fences the
content as *"standard linear algebra"*. So there was never a space to compare.

**This file supplies the spaces.**

## What is proved

> **`symSub` and `asymSub`** — the transpose's `+1` and `−1` eigenspaces as `Submodule ℂ`s, at any
> finite index type; **`isCompl_symSub_asymSub`**, so the splitting is real and not asserted.
>
> **`finrank_asymSub_two = 1`** and **`finrank_symSub_two = 3`** — the two numerals of
> `sym_dim_2` and `asym_dim_2`, now dimensions of exhibited spaces rather than hand-typed integers.
>
> **`symSub_ne_tracelessMatrix`** and **`asymSub_ne_scalars`** — **the two decompositions are
> different**, each refuted by one witness: `1` is symmetric and not traceless, `!![0,1;-1,0]` is
> antisymmetric and not a scalar.
>
> **`same_dimensions`** — and they have the same dimensions, `3` and `1` either way, which is the
> whole reason the gloss survived.

## What is NOT claimed

**Nothing about `SU(2)`, spin, or representations.** No group acts anywhere below, no
representation is defined, and **the claim that `traceless ⊕ ℂ·I` is the `SU(2)`-equivariant
splitting is not proved here** — it is named in this header to say what the parenthetical was
reaching for, and naming is not proving. What is proved is that the two splittings are different
and have the same dimensions.

> **Still open on 2026-08-28, and deliberately recorded next to a fence that closed the same
> day.** The sentence above — *"the claim that `traceless ⊕ ℂ·I` is the `SU(2)`-equivariant
> splitting is not proved here"* — is **not** superseded and nothing withdraws it. `SU(2)`
> -equivariance is unproved anywhere in this estate: no group acts in `TransposeDimension`
> either, and its header says so. The note is here because the *neighbouring* fence, the one
> about general `n`, was discharged that day, and `F2_3_ChiralityForced` carries a supersession
> note quoting **both** halves of its own version of the pair. A reader arriving at this
> paragraph from that note must not read the closure as covering this half. It does not.

**No general `n`.** `dim Sym_n = n(n+1)/2` is not proved here; `finrank_symSub_two` is `n = 2`,
obtained from the complement rather than from a basis. The general formula that
`F2_3_ChiralityForced`'s docstring calls *"standard linear algebra"* was, as of 2026-08-28, still
unproved anywhere in the estate.

> **Superseded 2026-08-28 (same day).** `TransposeDimension` now proves it, at **any finite index
> type and with no order hypothesis**: `finrank_symSub_choose` gives `dim Sym_ι = C(#ι + 1, 2)`
> and `finrank_symSub_fin` gives the `n(n+1)/2` form, with `finrank_asymSub_choose` /
> `finrank_asymSub_fin` for the antisymmetric side. The route is a coordinate equivalence
> (`asymEquiv`), not a basis, so the sentence above about "rather than from a basis" is still
> accurate about **both** files. **Nothing here is withdrawn**: `finrank_asymSub_two` remains the
> independent span-based derivation of `1`, which `TransposeDimension.general_recovers_two`
> cross-checks. The paragraph is kept as written because it is the record of what was open.

**Nothing in `F2_3_ChiralityForced` is withdrawn.** Its four results are true arithmetic with
untouched proofs; what is corrected is one parenthetical, in place, with the original kept.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TransposeSplit

open Matrix

variable {ι : Type*} [Fintype ι]

/-! ## 1. The transpose's two eigenspaces -/

def symSub (ι : Type*) [Fintype ι] : Submodule ℂ (Matrix ι ι ℂ) where
  carrier := {A | Aᵀ = A}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    rw [Matrix.transpose_add, hA, hB]
  zero_mem' := by simp
  smul_mem' c A hA := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    rw [Matrix.transpose_smul, hA]

def asymSub (ι : Type*) [Fintype ι] : Submodule ℂ (Matrix ι ι ℂ) where
  carrier := {A | Aᵀ = -A}
  add_mem' {A B} hA hB := by
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    rw [Matrix.transpose_add, hA, hB, neg_add]
  zero_mem' := by simp
  smul_mem' c A hA := by
    simp only [Set.mem_setOf_eq] at hA ⊢
    rw [Matrix.transpose_smul, hA, smul_neg]

theorem mem_symSub_iff (A : Matrix ι ι ℂ) : A ∈ symSub ι ↔ Aᵀ = A := Iff.rfl

theorem mem_asymSub_iff (A : Matrix ι ι ℂ) : A ∈ asymSub ι ↔ Aᵀ = -A := Iff.rfl

omit [Fintype ι] in
theorem eq_symPart_add_asymPart (A : Matrix ι ι ℂ) :
    A = (2 : ℂ)⁻¹ • (A + Aᵀ) + (2 : ℂ)⁻¹ • (A - Aᵀ) := by
  rw [← smul_add]
  have h : A + Aᵀ + (A - Aᵀ) = (2 : ℂ) • A := by
    rw [two_smul]
    abel
  rw [h, smul_smul]
  norm_num

theorem isCompl_symSub_asymSub : IsCompl (symSub ι) (asymSub ι) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro A h1 h2
    have hs : Aᵀ = A := h1
    have ha : Aᵀ = -A := h2
    have hneg : A = -A := hs.symm.trans ha
    have h2' : (2 : ℂ) • A = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hneg]
      abel
    exact (smul_eq_zero.mp h2').resolve_left two_ne_zero
  · rw [codisjoint_iff, eq_top_iff]
    intro A _
    rw [eq_symPart_add_asymPart A]
    refine Submodule.add_mem_sup ?_ ?_
    · rw [mem_symSub_iff, Matrix.transpose_smul, Matrix.transpose_add,
        Matrix.transpose_transpose, add_comm]
    · rw [mem_asymSub_iff, Matrix.transpose_smul, Matrix.transpose_sub,
        Matrix.transpose_transpose, ← neg_sub A Aᵀ, smul_neg]

/-! ## 2. The two dimensions at `n = 2` -/

/-- The single antisymmetric generator. -/
def asymGen : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem asymGen_mem : asymGen ∈ asymSub (Fin 2) := by
  rw [mem_asymSub_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [asymGen]

theorem asymSub_two_eq_span : asymSub (Fin 2) = Submodule.span ℂ {asymGen} := by
  refine le_antisymm ?_ (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr asymGen_mem))
  intro A hA
  have h : Aᵀ = -A := hA
  have h00 : A 0 0 = 0 := by
    have := congrFun (congrFun h 0) 0
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linear_combination this / 2
  have h11 : A 1 1 = 0 := by
    have := congrFun (congrFun h 1) 1
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
    linear_combination this / 2
  have h10 : A 1 0 = -A 0 1 := by
    have := congrFun (congrFun h 0) 1
    simpa only [Matrix.transpose_apply, Matrix.neg_apply] using this
  refine Submodule.mem_span_singleton.mpr ⟨A 0 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [asymGen, h00, h11, h10]

theorem asymGen_ne_zero : asymGen ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [asymGen] at this

theorem finrank_asymSub_two : Module.finrank ℂ (asymSub (Fin 2)) = 1 := by
  rw [asymSub_two_eq_span, finrank_span_singleton asymGen_ne_zero]

theorem finrank_symSub_two : Module.finrank ℂ (symSub (Fin 2)) = 3 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (symSub (Fin 2)) (asymSub (Fin 2))
  rw [codisjoint_iff.mp isCompl_symSub_asymSub.codisjoint,
    disjoint_iff.mp isCompl_symSub_asymSub.disjoint, finrank_bot, finrank_top,
    finrank_asymSub_two] at h
  have htot : Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 4 := by
    simp [Module.finrank_matrix]
  omega

/-! ## 3. The two decompositions are different -/

/-- `1` is symmetric and is not traceless. -/
theorem symSub_ne_tracelessMatrix : symSub (Fin 2) ≠ TracelessMatrix 2 := by
  intro h
  have hone : (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ symSub (Fin 2) := by
    rw [mem_symSub_iff]
    exact Matrix.transpose_one
  rw [h] at hone
  have htr : Matrix.trace (1 : Matrix (Fin 2) (Fin 2) ℂ) = 0 := hone
  rw [Matrix.trace_one] at htr
  norm_num at htr

/-- `!![0,1;-1,0]` is antisymmetric and is not a scalar. -/
theorem asymSub_ne_scalars :
    asymSub (Fin 2) ≠ Submodule.span ℂ {(1 : Matrix (Fin 2) (Fin 2) ℂ)} := by
  intro h
  have hmem : asymGen ∈ Submodule.span ℂ {(1 : Matrix (Fin 2) (Fin 2) ℂ)} := by
    rw [← h]; exact asymGen_mem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h01 := congrFun (congrFun hc 0) 1
  simp [asymGen] at h01

/-- **AND THEY HAVE THE SAME DIMENSIONS**, which is why the gloss survived. -/
theorem same_dimensions :
    Module.finrank ℂ (symSub (Fin 2)) = Module.finrank ℂ (TracelessMatrix 2)
      ∧ Module.finrank ℂ (asymSub (Fin 2))
          = Module.finrank ℂ (Submodule.span ℂ {(1 : Matrix (Fin 2) (Fin 2) ℂ)}) := by
  constructor
  · rw [finrank_symSub_two, traceless_dim_2]
  · rw [finrank_asymSub_two, finrank_span_singleton (one_ne_zero)]

end TransposeSplit
