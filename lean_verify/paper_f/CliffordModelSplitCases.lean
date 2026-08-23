/-
  CliffordModelSplitCases.lean — the two split residues in the shape a reader expects.

  WHY. `CliffordModelResidues` named every residue, and recorded one presentational residue rather
  than glossing it: `Cl(0,7;ℝ)` came out as `M₂(M₄(ℝ) × M₄(ℝ))`, and the textbook writes
  `M₈(ℝ) × M₈(ℝ)`. Same algebra, different arrangement. The bridge is
  `Mₙ(A × B) ≃ Mₙ(A) × Mₙ(B)`, which this estate had as `CliffordOddLadder.matrixProd` **over ℂ
  only**. Nothing in that proof used ℂ — it is entrywise — so the fix was the variable line, and
  the ℂ use is unchanged and instantiates the generalisation (`ERRATUM 201`).

  WHAT IS PROVED.

  * **`clifford_neg_seven_split`** — `Cl(0,7;ℝ) ≃ₐ[ℝ] M₈(ℝ) × M₈(ℝ)`;
  * **`clifford_pos_five_split`** — `Cl(5,0;ℝ) ≃ₐ[ℝ] M₂(ℍ) × M₂(ℍ)`, the other place a product
    sits inside a matrix algebra for the same reason;
  * the two infinite families restated in the split shape.

  **THE TABLE IS NOW IN THE TEXTBOOK'S OWN NOTATION**, entry for entry:
  `Cl(r,0)` for `r = 0,…,8` is `ℝ`, `ℝ × ℝ`, `M₂(ℝ)`, `M₂(ℂ)`, `M₂(ℍ)`, `M₂(ℍ) × M₂(ℍ)`, `M₄(ℍ)`,
  `M₈(ℂ)`, `M₁₆(ℝ)`; `Cl(0,r)` is `ℝ`, `ℂ`, `ℍ`, `ℍ × ℍ`, `M₂(ℍ)`, `M₄(ℂ)`, `M₈(ℝ)`,
  `M₈(ℝ) × M₈(ℝ)`, `M₁₆(ℝ)`.

  ONE HONEST LABEL ON THAT SENTENCE (`ERRATUM 250`). *"In the textbook's own notation"* is a claim
  about agreement with the standard eight-fold table, and it was checked **against that table as I
  know it, not against a cited source**. What IS machine-checked is everything else: each entry is
  an `AlgEquiv` proved in this estate, and the two `r = 8` entries are `clifford_pos_eight_zero`
  and its mirror rather than a ninth base case.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import CliffordModelResidues
import CliffordOddLadder

namespace CliffordModelSplitCases

open CliffordSignatureModel CliffordModelPeriodicity CliffordModelTable CliffordModelResidues
open CliffordOddLadder
open QuadraticForm QuadraticMap
open scoped Quaternion

noncomputable section

/-! ## 1. `Cl(0,7)` in the textbook's shape -/

/-- **`Cl(0,7;ℝ) ≃ₐ[ℝ] M₈(ℝ) × M₈(ℝ)`.** `CliffordModelResidues.clifford_neg_seven` with the
product pulled out through `matrixProd` and each factor flattened. -/
theorem clifford_neg_seven_split :
    Nonempty (CliffordAlgebra (sigForm 0 7) ≃ₐ[ℝ]
      Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ) := by
  obtain ⟨e⟩ := clifford_neg_seven
  have split := matrixProd ℝ (Fin 2) (Matrix (Fin 4) (Fin 4) ℝ) (Matrix (Fin 4) (Fin 4) ℝ)
  exact ⟨(e.trans split).trans
    ((matrixPowFlatten ℝ 2 2).prodCongr (matrixPowFlatten ℝ 2 2))⟩

/-! ## 2. `Cl(5,0)` in the textbook's shape

The same shape for the same reason: `clifford_five_zero` produces `M₂(ℍ × ℍ)` because it reaches
`(5,0)` from `Cl(0,3) = ℍ × ℍ`, and the product ends up inside the matrices. -/

/-- **`Cl(5,0;ℝ) ≃ₐ[ℝ] M₂(ℍ) × M₂(ℍ)`.** -/
theorem clifford_pos_five_split :
    Nonempty (CliffordAlgebra (sigForm 5 0) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℍ[ℝ] × Matrix (Fin 2) (Fin 2) ℍ[ℝ]) := by
  obtain ⟨e⟩ := clifford_pos_five
  exact ⟨e.trans (matrixProd ℝ (Fin 2) ℍ[ℝ] ℍ[ℝ])⟩

/-! ## 3. The two families, restated -/

theorem clifford_neg_mod_seven_split (n : ℕ) (h : n % 8 = 7) :
    Nonempty (CliffordAlgebra (sigForm 0 n) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (n / 8))) (Fin (16 ^ (n / 8)))
        (Matrix (Fin 8) (Fin 8) ℝ × Matrix (Fin 8) (Fin 8) ℝ)) :=
  clifford_model_of_residue_neg clifford_neg_seven_split n h

theorem clifford_pos_mod_five_split (m : ℕ) (h : m % 8 = 5) :
    Nonempty (CliffordAlgebra (sigForm m 0) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (m / 8))) (Fin (16 ^ (m / 8)))
        (Matrix (Fin 2) (Fin 2) ℍ[ℝ] × Matrix (Fin 2) (Fin 2) ℍ[ℝ])) :=
  clifford_model_of_residue clifford_pos_five_split m h

end

end CliffordModelSplitCases
