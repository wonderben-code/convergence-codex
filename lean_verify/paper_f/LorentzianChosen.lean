/-
  LorentzianChosen: "(4,0) and (0,4) excluded structurally" is FALSE, and here is the theorem

  SPINE LINK L9 ("Lorentzian signature (1,3)").

  WHAT THE JULY SPINE SAYS, AND WHY IT IS WRONG. L9's headline carries the clause
  *"(4,0) and (0,4) excluded structurally"*. The recompute's L9 refuter reported it as
  false, and the estate already contains the ingredients that refute it — but as three
  separate `Nonempty` statements about three different targets, with no single theorem
  putting them together. **This file is that theorem**, and it is four lines of
  composition: `Cl(1,3;ℝ)`, `Cl(4,0;ℝ)` and `Cl(0,4;ℝ)` are pairwise isomorphic as
  ℝ-algebras, all three being `M₂(ℍ[ℝ])`.

  So nothing about the CLIFFORD ALGEBRA excludes the Riemannian signatures. The exclusion
  is the Riemannian-versus-Lorentzian physical input, which is
  `ASSUMPTIONS_LEDGER` 6 — recorded there since 18 August, and its own update says in
  terms that the signature selection is *"about whether (1,3) is forced by the cascade or
  chosen and then exhibited"*. **The spine sentence must read "chosen", and after this
  file that is a consequence of a theorem rather than a reading of a table.**

  AND THE POSITIVE HALF, WHICH IS THE MATHEMATICALLY CORRECT RESOLUTION. The algebras
  agree; the FORMS do not. `sigPos` — the dimension of a maximal positive-definite
  subspace — is `1` for `Q₁₃` and `4` for `sigForm 4 0` and `0` for `sigForm 0 4`, so the
  three quadratic forms are pairwise inequivalent while their Clifford algebras are
  isomorphic. **`forms_differ_though_algebras_agree`** states both halves at once. That
  is the honest content of L9's clause: the Clifford functor forgets the signature, and
  anything that selects a signature must see the form, not the algebra it generates.

  WHAT IS **NOT** PROVED HERE.
  * That `(1,3)` IS forced. Nothing in this file or in the estate derives the Lorentzian
    signature from the cascade; that is `ASSUMPTIONS_LEDGER` 6 and is untouched.
  * That `M₂(ℍ)` is forced as the real form of `M₄(ℂ)`. The estate's only declaration
    named for that clause, `F3_8f_ConnesNCG.quaternionic_structure_forced`, has the
    statement `16 = 16 ∧ 4 = 4` and contains no `ℍ` at all (`ERRATUM 560`).
  * The `(2,2)` exclusion, which is genuinely structural and genuinely proved elsewhere:
    `CliffordRealTwoTwo.clifford13_not_ringEquiv_clifford22` rests on the
    orthogonal-idempotent invariant of `IdempotentRankInvariant`, not on a dimension
    count. **That is the contrast worth keeping**: `(2,2)` is excluded by an invariant of
    the algebra, and `(4,0)`/`(0,4)` cannot be, because they give the same algebra.
  * Simple-connectedness of `Spin(1,3)`. No file in this estate computes a `π₁` of
    anything; seven files carry that disclaimer.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import CliffordModelTable
import CentralIdemInvariant
import CliffordRealMinkowski
import CliffordRealSignatures

namespace LorentzianChosen

open CliffordSignatureModel CliffordRealSignatures

/-! ## 1. The three algebras are one algebra -/

/-- **`Cl(1,3;ℝ) ≅ Cl(4,0;ℝ)`.** Both are `M₂(ℍ[ℝ])`: the left by
`CliffordRealMinkowski.cliffordRealMinkowskiEquiv`, the right by
`CliffordModelTable.clifford_pos_four`. -/
theorem clifford13_algEquiv_clifford40 :
    Nonempty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃ₐ[ℝ]
      CliffordAlgebra (sigForm 4 0)) := by
  obtain ⟨g⟩ := CliffordModelTable.clifford_pos_four
  exact ⟨CliffordRealMinkowski.cliffordRealMinkowskiEquiv.trans g.symm⟩

/-- **`Cl(1,3;ℝ) ≅ Cl(0,4;ℝ)`.** -/
theorem clifford13_algEquiv_clifford04 :
    Nonempty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃ₐ[ℝ]
      CliffordAlgebra (sigForm 0 4)) := by
  obtain ⟨g⟩ := CliffordModelTable.clifford_neg_four
  exact ⟨CliffordRealMinkowski.cliffordRealMinkowskiEquiv.trans g.symm⟩

/-- **THE REFUTATION, IN ONE STATEMENT.** The three signatures `(1,3)`, `(4,0)` and
`(0,4)` give pairwise isomorphic real Clifford algebras. **So no property of the Clifford
algebra excludes the two Riemannian signatures**, and L9's clause *"(4,0) and (0,4)
excluded structurally"* is false as a statement about the algebra. -/
theorem three_signatures_one_algebra :
    Nonempty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃ₐ[ℝ]
        CliffordAlgebra (sigForm 4 0))
    ∧ Nonempty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃ₐ[ℝ]
        CliffordAlgebra (sigForm 0 4))
    ∧ Nonempty (CliffordAlgebra (sigForm 4 0) ≃ₐ[ℝ] CliffordAlgebra (sigForm 0 4)) :=
  ⟨clifford13_algEquiv_clifford40, clifford13_algEquiv_clifford04,
   CentralIdemInvariant.algEquiv_pos_four_neg_four⟩

/-! ## 2. The forms do differ, and that is where a selection must look -/

/-- **THE POSITIVE HALF.** The three algebras agree and the three FORMS do not:
`sigPos` is `1`, `4` and `0` respectively. So the Clifford functor forgets the signature,
and **anything that selects a signature must see the quadratic form rather than the
algebra it generates.** -/
theorem forms_differ_though_algebras_agree :
    sigPos CliffordRealMinkowski.Q₁₃ = 1
    ∧ sigPos (sigForm 4 0) = 4
    ∧ sigPos (sigForm 0 4) = 0
    ∧ Nonempty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃ₐ[ℝ]
        CliffordAlgebra (sigForm 4 0))
    ∧ Nonempty (CliffordAlgebra (sigForm 4 0) ≃ₐ[ℝ] CliffordAlgebra (sigForm 0 4)) :=
  ⟨sigPos_Q₁₃, sigPos_sigForm 4 0, sigPos_sigForm 0 4,
   clifford13_algEquiv_clifford40, CentralIdemInvariant.algEquiv_pos_four_neg_four⟩

/-- The three `sigPos` values are pairwise distinct, so no two of the three forms are
equivalent. Stated separately because the conjunction above gives the values and a reader
should not have to do the arithmetic. -/
theorem sigPos_pairwise_ne :
    sigPos CliffordRealMinkowski.Q₁₃ ≠ sigPos (sigForm 4 0)
    ∧ sigPos CliffordRealMinkowski.Q₁₃ ≠ sigPos (sigForm 0 4)
    ∧ sigPos (sigForm 4 0) ≠ sigPos (sigForm 0 4) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [sigPos_Q₁₃, sigPos_sigForm] <;> omega

end LorentzianChosen
