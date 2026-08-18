import CliffordRealSignatures
import IdempotentRankInvariant

/-!
# `Cl(2,2;ℝ) ≅ M₄(ℝ)`, and a docstring's exclusion becomes a theorem

`F1_7_SpacetimeForced.signature_determination` carries a table of five real forms with `p + q = 4`
and the algebra each gives, and then a Lean statement that is arithmetic on natural numbers —
`(0 : ℕ) = 0 ∧ (1 : ℕ) = 1 ∧ …` — standing in for it. Its recorded reason is *"OUT OF SCOPE:
signature classification of real Clifford algebras is standard but not in Mathlib"*, which is an
`ERRATUM 200` case: it prices the **technique**, not the **statement**.

This file takes one more line of that table. Of its five rows the estate already proves two —
`Cl(1,3) ≅ M₂(ℍ)` and `Cl(3,1) ≅ M₄(ℝ)` — and this adds the third:

> **`equivM4R`** — `Cl(2,2;ℝ) ≃ₐ[ℝ] M₄(ℝ)`.

`(2,2)` sits on the diagonal `p − q ≡ 0`, which `CliffordRealDiagonals` reached, so the hyperbolic
step gets there from `Cl(1,1) ≅ M₂(ℝ)` in a single rung. Then the row's actual claim — that `(2,2)`
is **excluded** because it does not give `M₂(ℍ)` — becomes a theorem:

> **`clifford13_not_ringEquiv_clifford22`** — `Cl(1,3;ℝ) ≇ Cl(2,2;ℝ)`, from
> `IdempotentRankInvariant.matrix2H_not_ringEquiv_matrix4R`.

## What is still out of reach, and why

Two rows remain: `Cl(4,0)` and `Cl(0,4)`, both claimed `≅ M₂(ℍ)`. They sit on `p − q ≡ 4` and
`≡ −4 ≡ 4 (mod 8)` — **one of the four residue classes `WALLS §W7.2` records as having no base
case**. The hyperbolic step cannot reach them from anything this estate has, and
`SignatureArithmetic.sigPos_sub_sigNeg_QextHyp` is the proof that it cannot. So the wall is not an
abstraction here: it is exactly the reason two named rows of one docstring's table stay unproved
while the other three do not.

**No published tag moves**, and `signature_determination` is left standing rather than rewritten
(`ERRATUM 94`); what this file provides is the material a later supersession would need.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealTwoTwo

open Matrix CliffordAlgebra QuadraticForm QuadraticMap SignatureArithmetic

noncomputable section

/-- signature `(2,2)`: `Q₁₁` with a second hyperbolic plane adjoined. -/
abbrev Q₂₂ : QuadraticForm ℝ ((Unit × (ℝ × ℝ)) × (ℝ × ℝ)) :=
  CliffordPeriodicityHyperbolic.QextHyp CliffordRealDiagonals.Q₁₁

/-- **`Cl(2,2;ℝ) ≅ M₄(ℝ)`** — one rung of the hyperbolic step above `Cl(1,1) ≅ M₂(ℝ)`, then the
standard flattening of `M₂(M₂(ℝ))`. -/
def equivM4R : CliffordAlgebra Q₂₂ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact (CliffordPeriodicityHyperbolic.periodicityEquivHyp CliffordRealDiagonals.Q₁₁).trans
    ((AlgEquiv.mapMatrix CliffordRealDiagonals.equivM2R).trans
      ((Matrix.compAlgEquiv (Fin 2) (Fin 2) ℝ ℝ).trans
        (Matrix.reindexAlgEquiv ℝ ℝ finProdFinEquiv)))

/-! ## Its signature, and nondegeneracy -/

theorem sigPos_Q₂₂ : sigPos Q₂₂ = 2 := by
  rw [Q₂₂, sigPos_QextHyp, CliffordRealSignatures.sigPos_Q₁₁]

theorem sigNeg_Q₂₂ : sigNeg Q₂₂ = 2 := by
  rw [Q₂₂, sigNeg_QextHyp, CliffordRealSignatures.sigNeg_Q₁₁]

theorem sep_Q₂₂ : (QuadraticMap.associated (R := ℝ) Q₂₂).SeparatingLeft :=
  CliffordRealSignatures.separatingLeft_of_sig (by rw [sigPos_Q₂₂, sigNeg_Q₂₂]; simp)

/-- **Every** nondegenerate real form of signature `(2,2)` gives `M₄(ℝ)`. -/
theorem clifford_iso_M4R_of_sig_two_two {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 4) (hsig : sigPos Q = 2) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) := by
  obtain ⟨e⟩ := CliffordRealQuantified.cliffordEquiv_of_sigPos_eq hQ sep_Q₂₂ (by simp [hdim])
    (by rw [hsig, sigPos_Q₂₂])
  exact ⟨e.trans equivM4R⟩

/-! ## The exclusion

`F1_7`'s table says `(2,2)` is *excluded* because it does not give `M₂(ℍ)`. That is a
non-isomorphism claim, and non-isomorphism does not follow from having two different names for two
algebras — it needs an invariant. `IdempotentRankInvariant` supplies one. -/

/-- **`Cl(1,3;ℝ) ≇ Cl(2,2;ℝ)`.** The two forms have the same dimension and different signatures,
and the algebras are genuinely different — which is what `F1_7`'s table asserts and what its Lean
statement does not say. -/
theorem clifford13_not_ringEquiv_clifford22 :
    IsEmpty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃+* CliffordAlgebra Q₂₂) := by
  refine ⟨fun φ => ?_⟩
  exact IdempotentRankInvariant.matrix2H_not_ringEquiv_matrix4R.elim
    ((CliffordRealMinkowski.cliffordRealMinkowskiEquiv.symm.toRingEquiv.trans φ).trans
      equivM4R.toRingEquiv)

/-- The ℝ-algebra form of the same statement. -/
theorem clifford13_not_algEquiv_clifford22 :
    IsEmpty (CliffordAlgebra CliffordRealMinkowski.Q₁₃ ≃ₐ[ℝ] CliffordAlgebra Q₂₂) :=
  ⟨fun φ => clifford13_not_ringEquiv_clifford22.elim φ.toRingEquiv⟩

/-- And `Cl(2,2) ≅ Cl(3,1)`, which the same table lists as two rows both giving `M₄(ℝ)`. Recorded
because it is the *positive* half of the exclusion and follows from the same two isomorphisms. -/
def clifford22_algEquiv_clifford31 :
    CliffordAlgebra Q₂₂ ≃ₐ[ℝ] CliffordAlgebra CliffordRealMajorana.Q₃₁ :=
  equivM4R.trans CliffordRealMajorana.cliffordMajoranaEquiv.symm

end

end CliffordRealTwoTwo
