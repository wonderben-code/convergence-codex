import CliffordPeriodicityQuantified

/-!
# The three base cases the estate did not have in quantified form

`ℝ`, `ℂ` and `ℍ` — the Clifford algebras of the zero-dimensional form, of `−x²`, and of
`−x² − y²`. **Mathlib has all three**, as `CliffordAlgebraRing.equiv`,
`CliffordAlgebraComplex.equiv` and `CliffordAlgebraQuaternion.equiv`, each stated for one
particular form. This file quantifies them, which is one application of
`CliffordRealQuantified.cliffordEquiv_of_sigPos_eq` apiece.

> **`clifford_iso_R_of_sig`**, **`clifford_iso_C_of_sig`**, **`clifford_iso_H_of_sig`** —
> `(p,q) = (0,0)`, `(0,1)`, `(0,2)`.

## Why these three and not others

They are exactly the states a reach computation over the estate's five moves leaves
undetermined. Every other `(p,q)` reduces to one of the estate's base cases; these three do not,
because every move strictly lowers `p + q` and there is nothing below them. Adding them makes the
base set closed downward, which is what a reduction argument needs.
-/

namespace CliffordRealSmallBases

open CliffordRealQuantified CliffordRealSignatures QuadraticMap
open scoped Quaternion

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-! ### `(0,0)` -/

theorem sep_zero_unit :
    (QuadraticMap.associated (R := ℝ) (0 : QuadraticForm ℝ Unit)).SeparatingLeft := by
  refine separatingLeft_of_sig ?_
  rw [sigPos_eq_zero_of_finrank_zero _ (by simp), sigNeg_eq_zero_of_finrank_zero _ (by simp)]
  simp

/-- **`Cl(0,0;ℝ) ≅ ℝ`**, for every form on a zero-dimensional real space. -/
theorem clifford_iso_R_of_sig (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 0) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] ℝ) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_zero_unit (by simp [hdim])
    (by rw [sigPos_eq_zero_of_finrank_zero _ hdim,
      sigPos_eq_zero_of_finrank_zero _ (by simp : Module.finrank ℝ Unit = 0)])
  exact ⟨e.trans CliffordAlgebraRing.equiv⟩

/-! ### `(0,1)` -/

theorem complexQ_eq :
    CliffordAlgebraComplex.Q = (-1 : ℝ) • (QuadraticMap.sq : QuadraticForm ℝ ℝ) := by
  ext x
  simp [CliffordAlgebraComplex.Q, QuadraticMap.sq]

theorem sigPos_complexQ : sigPos CliffordAlgebraComplex.Q = 0 := by
  rw [complexQ_eq, SignatureArithmetic.sigPos_smul_sq]
  norm_num

theorem sigNeg_complexQ : sigNeg CliffordAlgebraComplex.Q = 1 := by
  rw [complexQ_eq, SignatureArithmetic.sigNeg_smul_sq]
  norm_num

theorem sep_complexQ :
    (QuadraticMap.associated (R := ℝ) CliffordAlgebraComplex.Q).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_complexQ, sigNeg_complexQ]; simp)

/-- **`Cl(0,1;ℝ) ≅ ℂ`**, for every nondegenerate real form of dimension `1` with `sigPos = 0`. -/
theorem clifford_iso_C_of_sig (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 1) (hsig : sigPos Q = 0) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] ℂ) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_complexQ (by simp [hdim])
    (by rw [hsig, sigPos_complexQ])
  exact ⟨e.trans CliffordAlgebraComplex.equiv⟩

/-! ### `(0,2)` -/

/-- **`Cl(0,2;ℝ) ≅ ℍ`**, for every nondegenerate real form of dimension `2` with `sigPos = 0`. -/
theorem clifford_iso_H_of_sig (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 2) (hsig : sigPos Q = 0) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] ℍ[ℝ]) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ CliffordPeriodicityQuantified.sep_N_neg
    (by simp [hdim]) (by rw [hsig]; simp [CliffordTensorTwo.N]; norm_num)
  exact ⟨e.trans CliffordTensorTwo.rightQuat⟩

end

end CliffordRealSmallBases
