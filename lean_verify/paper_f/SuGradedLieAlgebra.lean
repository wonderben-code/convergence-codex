import SuBlockIdentification

/-!
# The compact form is a `GradedLieAlgebra` in Mathlib's own sense

`SuBlockGrading` proved the four bracket rules over `ℝ` and then declined the instance, with a
reason rather than a shrug:

> *"**No `GradedLieAlgebra` instance over `ℝ`.** `BlockGrading` instantiates Mathlib's class for
> `gl(p+q)` over `ℂ`; the analogue here would need the grading to decompose the **whole** real
> algebra, and `suEven ⊔ suOdd` is `tracelessSkewMat`, not `⊤`. No `ZMod 2`-indexed family is
> built below and no instance is declared."*

The reason was right and the conclusion was too narrow. The grading does decompose a whole
algebra — **just not the matrices**. It decomposes `tracelessSkewLie` itself, which
`TracelessSkewLie` built as a `LieSubalgebra ℝ` and which is therefore a Lie algebra in its own
right. Pulled back into that subtype the two pieces do sum to `⊤`, and the instance goes through.

## What is proved

> **`suPart : ZMod 2 → Submodule ℝ (SuAlg p q)`** — the two graded pieces of `SuBlockGrading`,
> pulled back along the subtype inclusion, with `mem_suPart_zero` / `mem_suPart_one` reducing
> membership to the matrix-level statements so **none of that file's work is redone**.
>
> **`sup_suPart = ⊤` and `inf_suPart = ⊥`** — inside the compact form the two pieces are
> complementary, which is exactly what failed to hold in the matrices and is why the instance was
> declined there.
>
> **`GradedLieAlgebra (suPart p q)`** — Mathlib's class, at `ZMod 2`, for the **compact** form.
> Its `SetLike.GradedBracket` half is `SuBlockGrading`'s four rules read through
> `Submodule.mem_comap`; its `DirectSum.Decomposition` half is the `IsCompl` above through
> `DirectSum.isInternal_submodule_iff_isCompl`.

## What is NOT claimed

**Nothing new about the mathematics.** Every bracket rule and every complementarity fact is
`SuBlockGrading`'s, cited through membership lemmas. **This file changes where the grading lives,
not what it says** — from a pair of submodules of the matrix algebra to a grading of a Lie algebra
by Mathlib's predicate. That is the whole content and it is worth exactly that much.

**Still nothing about maximal tori, rank, roots or Cartan subalgebras.** Six units have now left
those fences where they are.

**No group, no compactness, no smooth structure**, and the name `su` is not used for any
declaration, following `F4_1e_SpectralTripleArithmetic`.

**No `LieSubmodule` for the odd piece**, over `ℝ` or otherwise; `BlockOddModule`'s analogue is
still unwritten.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SuGradedLieAlgebra

open Matrix TracelessSkewLie SuBlockGrading

variable {p q : ℕ}

/-- The compact form at block size `p + q`, as a Lie algebra in its own right. -/
abbrev SuAlg (p q : ℕ) : Type := (tracelessSkewLie (Fin p ⊕ Fin q))

/-! ## 1. The two pieces, inside the compact form -/

noncomputable def suPart (p q : ℕ) (i : ZMod 2) : Submodule ℝ (SuAlg p q) :=
  Submodule.comap (tracelessSkewLie (Fin p ⊕ Fin q)).toSubmodule.subtype
    (if i = 0 then suEven p q else suOdd p q)

theorem mem_suPart_zero (x : SuAlg p q) :
    x ∈ suPart p q 0 ↔ (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈ suEven p q := by
  rw [suPart, if_pos rfl, Submodule.mem_comap]
  exact Iff.rfl

theorem mem_suPart_one (x : SuAlg p q) :
    x ∈ suPart p q 1 ↔ (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈ suOdd p q := by
  rw [suPart, if_neg (by decide), Submodule.mem_comap]
  exact Iff.rfl

theorem suEven_le : suEven p q ≤ tracelessSkewMat (Fin p ⊕ Fin q) := inf_le_right

theorem suOdd_le : suOdd p q ≤ tracelessSkewMat (Fin p ⊕ Fin q) := inf_le_right

/-! ## 2. Inside the compact form they are complementary -/

/-- **THIS IS WHAT FAILED IN THE MATRICES.** `suEven ⊔ suOdd` is `tracelessSkewMat` there, not
`⊤`; pulled back into `tracelessSkewMat` itself it *is* `⊤`. -/
theorem sup_suPart : suPart p q 0 ⊔ suPart p q 1 = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
      ∈ tracelessSkewMat (Fin p ⊕ Fin q) := x.property
  rw [← SuBlockGrading.sup_eq] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  refine Submodule.mem_sup.mpr ⟨⟨a, suEven_le ha⟩, (mem_suPart_zero _).mpr ha,
    ⟨b, suOdd_le hb⟩, (mem_suPart_one _).mpr hb, ?_⟩
  exact Subtype.ext hab

theorem inf_suPart : suPart p q 0 ⊓ suPart p q 1 = ⊥ := by
  rw [← le_bot_iff]
  intro x hx
  have h0 : (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈ suEven p q :=
    (mem_suPart_zero x).mp hx.1
  have h1 : (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈ suOdd p q :=
    (mem_suPart_one x).mp hx.2
  have hzero : (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = 0 := by
    have hmem : (x : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈ suEven p q ⊓ suOdd p q :=
      ⟨h0, h1⟩
    rw [SuBlockGrading.inf_eq_bot] at hmem
    simpa using hmem
  simpa using Subtype.ext hzero

/-! ## 3. Mathlib's class -/

theorem isInternal_suPart : DirectSum.IsInternal (suPart p q) := by
  rw [DirectSum.isInternal_submodule_iff_isCompl (suPart p q) (i := 0) (j := 1)
    (by decide) BlockGrading.univ_zmod_two]
  exact ⟨disjoint_iff.mpr inf_suPart, codisjoint_iff.mpr sup_suPart⟩

/-- **THE FOUR RULES OF `SuBlockGrading`, READ THROUGH THE INCLUSION.** -/
instance gradedBracket_suPart : SetLike.GradedBracket (suPart p q) where
  bracket_mem := by
    rintro i j k gi gj hsum hgi hgj
    rcases BlockGrading.zmod_two_eq i with rfl | rfl <;>
      rcases BlockGrading.zmod_two_eq j with rfl | rfl
    · have hk : k = 0 := by rw [← hsum]; decide
      subst hk
      rw [mem_suPart_zero] at hgi hgj ⊢
      exact lie_suEven_suEven hgi hgj
    · have hk : k = 1 := by rw [← hsum]; decide
      subst hk
      rw [mem_suPart_zero] at hgi
      rw [mem_suPart_one] at hgj ⊢
      exact lie_suEven_suOdd hgi hgj
    · have hk : k = 1 := by rw [← hsum]; decide
      subst hk
      rw [mem_suPart_one] at hgi ⊢
      rw [mem_suPart_zero] at hgj
      exact lie_suOdd_suEven hgi hgj
    · have hk : k = 0 := by rw [← hsum]; decide
      subst hk
      rw [mem_suPart_one] at hgi hgj
      rw [mem_suPart_zero]
      exact lie_suOdd_suOdd hgi hgj

noncomputable instance decomposition_suPart : DirectSum.Decomposition (suPart p q) :=
  isInternal_suPart.chooseDecomposition

/-- **THE COMPACT FORM IS A `GradedLieAlgebra` OVER `ZMod 2`**, which `SuBlockGrading` declined
because it was looking at the wrong ambient algebra. -/
noncomputable instance gradedLieAlgebra_suPart : GradedLieAlgebra (suPart p q) where
  __ := gradedBracket_suPart
  __ := decomposition_suPart

end SuGradedLieAlgebra
