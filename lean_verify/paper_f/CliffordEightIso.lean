import CliffordSixIso

/-!
# `Cl₈(ℂ) ≅ M₁₆(ℂ)`

The last conjunct of `F1_7_SpacetimeForced.clifford_complex_even_dims` that was still arithmetic
standing where an algebra statement belongs, and the second of the two isomorphisms
`WALLS §W7.1` records as open.

> **`equivM16`** — `CliffordAlgebra Q₈ ≃ₐ[ℂ] Matrix (Fin 16) (Fin 16) ℂ`, where
> `Q₈ = Q₆ ⊥ ⟨1,1⟩` on a space `finrank_V8` proves eight-dimensional.

## Why this file is short

`CliffordSixIso`'s record predicted, and labelled as a prediction (`ERRATUM 194`), that the
construction *"should apply with `Cl₆` in place of `Cl₄`"*. `CliffordPeriodicity` made the
construction general, so **the prediction is not tested here — it was discharged when the general
statement was proved**, and what remains is one application of it plus the same transport.

**It stands on the whole chain**: `CliffordIso` (`n = 4`), `CliffordPeriodicity` (the step),
`CliffordSixIso` (`n = 6`). Remove any one and this file has nothing to say.

## What is NOT proved

**Not the classification entry.** `Q₈` is one specific eight-dimensional form; the entry quantifies
over every nondegenerate one, which needs a normal-form theorem the estate does not have. **The
restriction is not pedantic** — `CliffordDimension.finrank_cliffordAlgebra_congr` gives dimension
`256` for *every* form on this space including the zero form, whose Clifford algebra is the
exterior algebra and is not a matrix algebra.

**Nothing about odd dimensions**, where the classification is `Cl_{2k+1}(ℂ) ≅ M ⊕ M` rather than a
single matrix algebra, and this construction does not reach it.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.


## ⚠ "A NORMAL-FORM THEOREM THE ESTATE DOES NOT HAVE" IS FALSE. Annotated 1 September 2026

Kept as written (`ERRATUM 94`). `CliffordClassification` — **which imports this file** — found the
theorem in Mathlib as `QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` and proved
**`clifford_iso_M16_of_nondegenerate`**: for every 8-dimensional complex space and every
nondegenerate `Q` on it, `CliffordAlgebra Q ≃ₐ[ℂ] M₁₆(ℂ)`. **That is exactly "the classification
entry" this section says is out of reach**, and it is reached out of this file's `Q₈` case.

`CliffordSixIso` carries the same sentence and **was** annotated, on 2026-08-27; this file, and
`F1_7_SpacetimeForced`, were not. That one of three got the note is `ERRATUM 390`'s subject.

**The second paragraph stands unchanged and is why the quantified statement needs nondegeneracy:**
`CliffordDimension.finrank_cliffordAlgebra_congr` gives dimension `256` for every form including
the zero form, whose Clifford algebra is the exterior algebra. **And the odd-dimension paragraph
stands too** — `Cl_{2k+1}(ℂ)` is untouched here and `CentralIdemInvariant`'s remaining clause is
still open.
-/

namespace CliffordEightIso

open Matrix CliffordAlgebra

noncomputable section

/-- the eight-dimensional space. -/
abbrev V8 := CliffordSixIso.V6 × (ℂ × ℂ)

/-- `Q₈ = Q₆ ⊥ ⟨1,1⟩`. -/
abbrev Q₈ : QuadraticForm ℂ V8 := CliffordPeriodicity.Qext CliffordSixIso.Q₆

theorem finrank_V8 : Module.finrank ℂ V8 = 8 := by
  simp [Module.finrank_prod]

/-- The dimension agrees with the general formula. -/
theorem finrank_clifford_Q8 : Module.finrank ℂ (CliffordAlgebra Q₈) = 256 := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  rw [CliffordDimension.finrank_cliffordAlgebra ℂ V8 Q₈, finrank_V8]
  norm_num

/-- **`Cl₈(ℂ) ≅ M₁₆(ℂ)`.** -/
def equivM16 : CliffordAlgebra Q₈ ≃ₐ[ℂ] Matrix (Fin 16) (Fin 16) ℂ :=
  (CliffordPeriodicity.periodicityEquiv CliffordSixIso.Q₆).trans
    ((AlgEquiv.mapMatrix CliffordSixIso.equivM8).trans
      ((Matrix.compAlgEquiv (Fin 2) (Fin 8) ℂ ℂ).trans
        (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv)))

end

end CliffordEightIso
