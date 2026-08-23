/-
  CliffordModelResidues.lean — the five that were left, closed.

  WHY. `CliffordModelTable` left the real classification needing exactly five algebras:
  `Cl (sigForm 6 0)`, `Cl (sigForm 7 0)`, `Cl (sigForm 0 5)`, `Cl (sigForm 0 6)`,
  `Cl (sigForm 0 7)`. It deliberately named no route, because the tempting sentence — *the move
  that reached `(5,0)` reaches `(6,0)`* — had not been checked, and `ERRATUM 246` and `ERRATUM 250`
  are both about writing that kind of sentence before checking it.

  IT WAS CHECKED, AND ALL FIVE FALL, WITH NOTHING NEW BUILT. Reading `clifford_step_pos` and
  `clifford_step_neg` rather than recalling them:

  * `clifford_step_pos` : `sigPos Q' = sigPos Q + 2` and `dim +2` give `Cl Q' ≃ M₂(Cl (−Q))`;
  * `clifford_step_neg` : the same on `sigNeg` gives `Cl Q' ≃ Cl (−Q) ⊗[ℝ] ℍ`.

  **Both land on `Cl (−Q)`, and negating a model transposes its signature** — `clifford_neg_model`,
  one line from `CliffordSignatureModel.clifford_model`. So each step reads a residue off the
  OTHER side of the table, and the five missing residues are each two steps from a residue the
  table already had. **The estate's own `clifford_five_zero` is this trick at `(5,0)` and it was
  sitting there.** What was missing was not a theorem; it was the observation that the two steps
  cross the diagonal, `d ↦ 2 − d` and `d ↦ −d − 2`.

  WHAT IS PROVED.

  * `clifford_pos_six` — **`Cl(6,0;ℝ) ≃ₐ[ℝ] M₄(ℍ)`**, from `(0,4)`;
  * `clifford_neg_six` — **`Cl(0,6;ℝ) ≃ₐ[ℝ] M₈(ℝ)`**, from `(4,0)` through `ℍ ⊗ ℍ ≃ M₄(ℝ)`;
  * `clifford_neg_five` — **`Cl(0,5;ℝ) ≃ₐ[ℝ] M₄(ℂ)`**, from `(3,0)` through `ℂ ⊗ ℍ ≃ M₂(ℂ)`;
  * `clifford_pos_seven` — **`Cl(7,0;ℝ) ≃ₐ[ℝ] M₈(ℂ)`**, from `(0,5)` above;
  * `clifford_neg_seven` — **`Cl(0,7;ℝ) ≃ₐ[ℝ] M₂(M₄(ℝ) × M₄(ℝ))`**, from `(5,0)` through
    `prodRight` and `ℍ ⊗ ℍ`;
  * the five infinite families they generate, so **every residue class on both diagonals is now
    named**.

  ONE PRESENTATIONAL RESIDUE, STATED RATHER THAN GLOSSED. The textbook writes `Cl(0,7)` as
  `M₈(ℝ) × M₈(ℝ)`, and what is proved here is `M₂(M₄(ℝ) × M₄(ℝ))` — the same algebra, differently
  arranged. Moving between them needs `Mₙ(A × B) ≃ Mₙ(A) × Mₙ(B)`; **this estate has exactly that,
  as `CliffordOddLadder.matrixProd`, over ℂ and not over ℝ** (grepped, not recalled — and Mathlib
  has no version at all). Generalising its base ring is a small change and is not made here.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import CliffordModelTable
import ComplexQuaternionTensor
import Mathlib.RingTheory.TensorProduct.Pi

namespace CliffordModelResidues

open CliffordPeriodicityQuantified CliffordPeriodicityEight CliffordRealQuantified
open CliffordRealSignatures CliffordSignatureModel CliffordModelPeriodicity CliffordModelTable
open QuadraticForm QuadraticMap
open scoped Quaternion TensorProduct

noncomputable section

/-! ## 1. The negatives of the models

`clifford_step_pos` and `clifford_step_neg` both land on `Cl (−Q)`, so both need the negated model
to be nondegenerate and its signature known. Both are one line from `sigPos_neg` / `sigNeg_neg`
and `separatingLeft_of_sig`. -/

theorem sep_neg_sigForm (p q : ℕ) :
    (QuadraticMap.associated (R := ℝ) (-(sigForm p q))).SeparatingLeft := by
  refine separatingLeft_of_sig ?_
  rw [sigPos_neg, sigNeg_neg, sigPos_sigForm, sigNeg_sigForm, finrank_sigSpace]
  omega

theorem sigPos_neg_sigForm (p q : ℕ) : sigPos (-(sigForm p q)) = q := by
  rw [sigPos_neg, sigNeg_sigForm]

theorem sigNeg_neg_sigForm (p q : ℕ) : sigNeg (-(sigForm p q)) = p := by
  rw [sigNeg_neg, sigPos_sigForm]

/-- **NEGATING A MODEL TRANSPOSES ITS SIGNATURE**, so the Clifford algebra the two steps land on is
always another model — and the whole table applies to it. This is `CliffordSignatureModel`'s
`clifford_model` (every nondegenerate form IS the model of its signature) at the one place it is
needed, and it is why neither step below has to identify an unfamiliar algebra. -/
theorem clifford_neg_model (p q : ℕ) :
    Nonempty (CliffordAlgebra (-(sigForm p q)) ≃ₐ[ℝ] CliffordAlgebra (sigForm q p)) := by
  have h := clifford_model (sep_neg_sigForm p q)
  rwa [sigPos_neg_sigForm, sigNeg_neg_sigForm] at h

/-! ## 2. `(6,0)`, from `(0,4)` across the diagonal -/

/-- `Cl (−(sigForm 4 0))` is a `(0,4)` algebra, so it is `M₂(ℍ)`. -/
theorem clifford_neg_sigForm_four :
    Nonempty (CliffordAlgebra (-(sigForm 4 0)) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ]) := by
  obtain ⟨t⟩ := clifford_neg_model 4 0
  obtain ⟨b⟩ := clifford_neg_four
  exact ⟨t.trans b⟩

/-- **`Cl(6,0;ℝ) ≃ₐ[ℝ] M₄(ℍ)`.** One application of `clifford_step_pos`, which crosses the
diagonal, onto a base the estate already had. -/
theorem clifford_pos_six :
    Nonempty (CliffordAlgebra (sigForm 6 0) ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℍ[ℝ]) := by
  obtain ⟨e⟩ := clifford_step_pos (Q := sigForm 4 0) (sep_sigForm 4 0) (sep_sigForm 6 0)
    (by rw [finrank_sigSpace, finrank_sigSpace])
    (by rw [sigPos_sigForm, sigPos_sigForm])
  obtain ⟨f⟩ := clifford_neg_sigForm_four
  exact ⟨(e.trans f.mapMatrix).trans (matrixPowFlatten ℍ[ℝ] 2 1)⟩

/-! ## 3. `(0,6)`, from `(4,0)` across the diagonal the other way -/

/-- `Cl (−(sigForm 0 4))` is a `(4,0)` algebra, so it is `M₂(ℍ)`. -/
theorem clifford_neg_sigForm_zero_four :
    Nonempty (CliffordAlgebra (-(sigForm 0 4)) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ]) := by
  obtain ⟨t⟩ := clifford_neg_model 0 4
  obtain ⟨b⟩ := clifford_pos_four
  exact ⟨t.trans b⟩

/-- **`Cl(0,6;ℝ) ≃ₐ[ℝ] M₈(ℝ)`.** `clifford_step_neg` onto `(4,0)`, then `M₂(ℍ) ⊗ ℍ ≃ M₂(ℍ ⊗ ℍ)`
and `ℍ ⊗ ℍ ≃ M₄(ℝ)`, both already in the estate. -/
theorem clifford_neg_six :
    Nonempty (CliffordAlgebra (sigForm 0 6) ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ) := by
  obtain ⟨e⟩ := clifford_step_neg (Q := sigForm 0 4) (sep_sigForm 0 4) (sep_sigForm 0 6)
    (by rw [finrank_sigSpace, finrank_sigSpace])
    (by rw [sigNeg_sigForm, sigNeg_sigForm])
  obtain ⟨f⟩ := clifford_neg_sigForm_zero_four
  refine ⟨((((e.trans (Algebra.TensorProduct.congr f AlgEquiv.refl)).trans
    (matrixTensorRight (Fin 2) ℍ[ℝ] ℍ[ℝ])).trans
      (AlgEquiv.mapMatrix QuaternionTensor.equivM4)).trans
        (matrixPowFlatten ℝ 2 2))⟩

/-! ## 4. `(0,5)`, from `(3,0)`, and `(7,0)` on top of it -/

/-- **`Cl(0,5;ℝ) ≃ₐ[ℝ] M₄(ℂ)`.** `clifford_step_neg` onto `(3,0)`, then `M₂(ℂ) ⊗ ℍ ≃ M₂(ℂ ⊗ ℍ)` and
`ComplexQuaternionTensor.equivM2C` (`ℂ ⊗ ℍ ≃ M₂(ℂ)`), which this estate built and Mathlib has
not. -/
theorem clifford_neg_five :
    Nonempty (CliffordAlgebra (sigForm 0 5) ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℂ) := by
  obtain ⟨e⟩ := clifford_step_neg (Q := sigForm 0 3) (sep_sigForm 0 3) (sep_sigForm 0 5)
    (by rw [finrank_sigSpace, finrank_sigSpace])
    (by rw [sigNeg_sigForm, sigNeg_sigForm])
  obtain ⟨t⟩ := clifford_neg_model 0 3
  obtain ⟨b⟩ := clifford_pos_three
  exact ⟨(((e.trans (Algebra.TensorProduct.congr (t.trans b) AlgEquiv.refl)).trans
    (matrixTensorRight (Fin 2) ℂ ℍ[ℝ])).trans
      (AlgEquiv.mapMatrix ComplexQuaternionTensor.equivM2C)).trans
        (matrixPowFlatten ℂ 2 1)⟩

/-- **`Cl(7,0;ℝ) ≃ₐ[ℝ] M₈(ℂ)`.** `clifford_step_pos` onto `(0,5)`, which the line above supplies.
This is the one case that needed another of the five first, and it is the reason `(0,5)` is
proved before it rather than beside it. -/
theorem clifford_pos_seven :
    Nonempty (CliffordAlgebra (sigForm 7 0) ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℂ) := by
  obtain ⟨e⟩ := clifford_step_pos (Q := sigForm 5 0) (sep_sigForm 5 0) (sep_sigForm 7 0)
    (by rw [finrank_sigSpace, finrank_sigSpace])
    (by rw [sigPos_sigForm, sigPos_sigForm])
  obtain ⟨t⟩ := clifford_neg_model 5 0
  obtain ⟨b⟩ := clifford_neg_five
  exact ⟨(e.trans (t.trans b).mapMatrix).trans (matrixPowFlatten ℂ 2 2)⟩

/-! ## 5. `(0,7)`, from `(5,0)`, where the base is a product -/

/-- **`Cl(0,7;ℝ) ≃ₐ[ℝ] M₂(M₄(ℝ) × M₄(ℝ))`.** `clifford_step_neg` onto `(5,0)`, whose algebra is
`M₂(ℍ × ℍ)`; the tensor moves past the matrices and then past the product
(`Algebra.TensorProduct.prodRight`, after a `comm` because the product is on the LEFT of the
tensor), and `ℍ ⊗ ℍ ≃ M₄(ℝ)` closes both factors.

The textbook writes this algebra as `M₈(ℝ) × M₈(ℝ)`. It is the same algebra; see the header. -/
theorem clifford_neg_seven :
    Nonempty (CliffordAlgebra (sigForm 0 7) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ)) := by
  obtain ⟨e⟩ := clifford_step_neg (Q := sigForm 0 5) (sep_sigForm 0 5) (sep_sigForm 0 7)
    (by rw [finrank_sigSpace, finrank_sigSpace])
    (by rw [sigNeg_sigForm, sigNeg_sigForm])
  obtain ⟨t⟩ := clifford_neg_model 0 5
  obtain ⟨b⟩ := clifford_pos_five
  exact ⟨((e.trans (Algebra.TensorProduct.congr (t.trans b) AlgEquiv.refl)).trans
    (matrixTensorRight (Fin 2) (ℍ[ℝ] × ℍ[ℝ]) ℍ[ℝ])).trans
      (AlgEquiv.mapMatrix
        (((Algebra.TensorProduct.comm ℝ (ℍ[ℝ] × ℍ[ℝ]) ℍ[ℝ]).trans
          (Algebra.TensorProduct.prodRight ℝ ℝ ℍ[ℝ] ℍ[ℝ] ℍ[ℝ])).trans
            (QuaternionTensor.equivM4.prodCongr QuaternionTensor.equivM4)))⟩

/-! ## 6. The five infinite families they generate

With these, **every residue class on both diagonals is named**. -/

theorem clifford_pos_mod_six (m : ℕ) (h : m % 8 = 6) :
    Nonempty (CliffordAlgebra (sigForm m 0) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (m / 8))) (Fin (16 ^ (m / 8))) (Matrix (Fin 4) (Fin 4) ℍ[ℝ])) :=
  clifford_model_of_residue clifford_pos_six m h

theorem clifford_neg_mod_six (n : ℕ) (h : n % 8 = 6) :
    Nonempty (CliffordAlgebra (sigForm 0 n) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (n / 8))) (Fin (16 ^ (n / 8))) (Matrix (Fin 8) (Fin 8) ℝ)) :=
  clifford_model_of_residue_neg clifford_neg_six n h

theorem clifford_pos_mod_seven (m : ℕ) (h : m % 8 = 7) :
    Nonempty (CliffordAlgebra (sigForm m 0) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (m / 8))) (Fin (16 ^ (m / 8))) (Matrix (Fin 8) (Fin 8) ℂ)) :=
  clifford_model_of_residue clifford_pos_seven m h

theorem clifford_neg_mod_five (n : ℕ) (h : n % 8 = 5) :
    Nonempty (CliffordAlgebra (sigForm 0 n) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (n / 8))) (Fin (16 ^ (n / 8))) (Matrix (Fin 4) (Fin 4) ℂ)) :=
  clifford_model_of_residue_neg clifford_neg_five n h

theorem clifford_neg_mod_seven (n : ℕ) (h : n % 8 = 7) :
    Nonempty (CliffordAlgebra (sigForm 0 n) ≃ₐ[ℝ]
      Matrix (Fin (16 ^ (n / 8))) (Fin (16 ^ (n / 8)))
        (Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) ℝ × Matrix (Fin 4) (Fin 4) ℝ))) :=
  clifford_model_of_residue_neg clifford_neg_seven n h

end

end CliffordModelResidues
