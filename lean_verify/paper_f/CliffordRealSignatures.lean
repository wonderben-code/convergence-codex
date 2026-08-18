import SignatureArithmetic
import CliffordRealSignatureStep

/-!
# Every named real form's signature, and the six isomorphisms quantified

`CliffordRealQuantified` proves that a real Clifford algebra's isomorphism class depends only on
dimension and signature, and `SignatureArithmetic` proves that signatures add over orthogonal sums.
Both closed by recording the same debt: **no named form in this estate had its signature computed**,
so the concrete isomorphisms were not instances of their own generalisation. This file pays it.

## Why it is short

Every real form this estate names is built from `CliffordAlgebraQuaternion.Q c₁ c₂`, which Mathlib
*defines* as `(c₁ • sq).prod (c₂ • sq)` — an orthogonal sum of two lines. So `sigPos_prod` and
`sigPos_smul_sq` compute all six mechanically, with no diagonalisation and no case analysis:

| form | built as | signature |
|---|---|---|
| `CliffordRealDiagonals.Q₁₁` | `QextHyp 0` on `Unit` | `(1,1)` |
| `CliffordRealDiagonals.Q₁₂` | `QextHyp (−x²)` | `(1,2)` |
| `CliffordRealMinkowski.Q₁₃` | `Q(1,−1) ⊥ Q(−1,−1)` | `(1,3)` |
| `CliffordRealMajorana.Q₃₁` | `Q(−1,1) ⊥ Q(1,1)` | `(3,1)` |
| `CliffordRealSignatureStep.Q₂₄` | `QextHyp Q₁₃` | `(2,4)` |
| `CliffordRealSignatureStep.Q₄₂` | `QextHyp Q₃₁` | `(4,2)` |

**The names were always accurate.** `Q₁₃` was called `Q₁₃` because whoever wrote it did the
arithmetic on paper; until now nothing in Lean said so. Six names stop being assertions.

Nondegeneracy comes free from the same numbers: `separatingLeft_of_sig` turns
`sigPos + sigNeg = finrank` into `SeparatingLeft`, which is the converse of
`CliffordRealQuantified.finrank_radical_eq_zero`.

## What is proved

Six theorems of the form *for **every** nondegenerate real quadratic form of dimension `d` and
`sigPos p`, `Cl(Q) ≃ₐ[ℝ] …`* — `M₂(ℝ)`, `M₂(ℂ)`, `M₂(ℍ)`, `M₄(ℝ)`, `M₄(ℍ)`, `M₈(ℝ)`.

## What this does NOT do

**It does not move the wall.** `WALLS §W7.2`'s wall is the four residue classes
`p − q ≡ 1, 3, 4, 5`, which have no base case. All six results below sit on the four
diagonals already reachable. The `sigPos` hypotheses are hypotheses; a form of signature
`(2,1)` is outside every statement here.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealSignatures

open QuadraticForm QuadraticMap SignatureArithmetic
open scoped Quaternion

noncomputable section

/-! ## The quaternionic two-variable form -/

@[simp] theorem sigPos_quaternionQ (c₁ c₂ : ℝ) :
    sigPos (CliffordAlgebraQuaternion.Q c₁ c₂)
      = (if 0 < c₁ then 1 else 0) + (if 0 < c₂ then 1 else 0) := by
  simp only [CliffordAlgebraQuaternion.Q, sigPos_prod, sigPos_smul_sq]

@[simp] theorem sigNeg_quaternionQ (c₁ c₂ : ℝ) :
    sigNeg (CliffordAlgebraQuaternion.Q c₁ c₂)
      = (if c₁ < 0 then 1 else 0) + (if c₂ < 0 then 1 else 0) := by
  simp only [CliffordAlgebraQuaternion.Q, sigNeg_prod, sigNeg_smul_sq]

/-! ## Nondegeneracy from the signature

The converse of `CliffordRealQuantified.finrank_radical_eq_zero`: if the two halves of the signature
already exhaust the dimension there is no room left for a radical, so the form is nondegenerate. -/

theorem separatingLeft_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} (h : sigPos Q + sigNeg Q = Module.finrank ℝ V) :
    (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft := by
  have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := Q)
  have hz : Module.finrank ℝ Q.radical = 0 := by omega
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, ← QuadraticMap.radical_eq_ker_associated]
  exact Submodule.finrank_eq_zero.mp hz

/-- A form on a zero-dimensional space has zero signature; there is no room for anything else. -/
theorem sigPos_eq_zero_of_finrank_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (h : Module.finrank ℝ V = 0) : sigPos Q = 0 :=
  Nat.le_zero.mp (h ▸ sigPos_le_finrank (Q := Q))

theorem sigNeg_eq_zero_of_finrank_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) (h : Module.finrank ℝ V = 0) : sigNeg Q = 0 :=
  sigPos_eq_zero_of_finrank_zero (-Q) h

/-! ## The six named forms -/

section Named

open CliffordRealDiagonals CliffordRealMinkowski CliffordRealMajorana CliffordRealSignatureStep

theorem sigPos_Q₁₁ : sigPos Q₁₁ = 1 := by
  rw [Q₁₁, sigPos_QextHyp, sigPos_eq_zero_of_finrank_zero _ (by simp)]
theorem sigNeg_Q₁₁ : sigNeg Q₁₁ = 1 := by
  rw [Q₁₁, sigNeg_QextHyp, sigNeg_eq_zero_of_finrank_zero _ (by simp)]

theorem sigPos_Q₁₂ : sigPos Q₁₂ = 1 := by
  have h : CliffordAlgebraComplex.Q = (-1 : ℝ) • QuadraticMap.sq := by
    ext x; simp [CliffordAlgebraComplex.Q, QuadraticMap.sq]
  rw [Q₁₂, sigPos_QextHyp, h, sigPos_smul_sq]; norm_num
theorem sigNeg_Q₁₂ : sigNeg Q₁₂ = 2 := by
  have h : CliffordAlgebraComplex.Q = (-1 : ℝ) • QuadraticMap.sq := by
    ext x; simp [CliffordAlgebraComplex.Q, QuadraticMap.sq]
  rw [Q₁₂, sigNeg_QextHyp, h, sigNeg_smul_sq]; norm_num

theorem sigPos_Q₁₃ : sigPos Q₁₃ = 1 := by rw [Q₁₃, sigPos_prod]; norm_num
theorem sigNeg_Q₁₃ : sigNeg Q₁₃ = 3 := by rw [Q₁₃, sigNeg_prod]; norm_num

theorem sigPos_Q₃₁ : sigPos Q₃₁ = 3 := by rw [Q₃₁, sigPos_prod]; norm_num
theorem sigNeg_Q₃₁ : sigNeg Q₃₁ = 1 := by rw [Q₃₁, sigNeg_prod]; norm_num

theorem sigPos_Q₂₄ : sigPos Q₂₄ = 2 := by rw [Q₂₄, sigPos_QextHyp, sigPos_Q₁₃]
theorem sigNeg_Q₂₄ : sigNeg Q₂₄ = 4 := by rw [Q₂₄, sigNeg_QextHyp, sigNeg_Q₁₃]

theorem sigPos_Q₄₂ : sigPos Q₄₂ = 4 := by rw [Q₄₂, sigPos_QextHyp, sigPos_Q₃₁]
theorem sigNeg_Q₄₂ : sigNeg Q₄₂ = 2 := by rw [Q₄₂, sigNeg_QextHyp, sigNeg_Q₃₁]

/-! ### Nondegeneracy, read off the same numbers -/

theorem sep_Q₁₁ : (QuadraticMap.associated (R := ℝ) Q₁₁).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_Q₁₁, sigNeg_Q₁₁]; simp)
theorem sep_Q₁₂ : (QuadraticMap.associated (R := ℝ) Q₁₂).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_Q₁₂, sigNeg_Q₁₂]; simp)
theorem sep_Q₁₃ : (QuadraticMap.associated (R := ℝ) Q₁₃).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_Q₁₃, sigNeg_Q₁₃]; simp)
theorem sep_Q₃₁ : (QuadraticMap.associated (R := ℝ) Q₃₁).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_Q₃₁, sigNeg_Q₃₁]; simp)
theorem sep_Q₂₄ : (QuadraticMap.associated (R := ℝ) Q₂₄).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_Q₂₄, sigNeg_Q₂₄]; simp)
theorem sep_Q₄₂ : (QuadraticMap.associated (R := ℝ) Q₄₂).SeparatingLeft :=
  separatingLeft_of_sig (by rw [sigPos_Q₄₂, sigNeg_Q₄₂]; simp)

/-! ## The six isomorphisms, quantified

Each reads: *for **every** nondegenerate real quadratic form of this dimension and this `sigPos`* —
not for the named one. The named form is now only a witness that the signature is attainable. -/

open CliffordRealQuantified in
/-- **Every** nondegenerate real form of signature `(1,1)`. -/
theorem clifford_iso_M2R_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 2) (hsig : sigPos Q = 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_Q₁₁ (by simp [hdim]) (by rw [hsig, sigPos_Q₁₁])
  exact ⟨e.trans equivM2R⟩

open CliffordRealQuantified in
/-- **Every** nondegenerate real form of signature `(1,2)`. -/
theorem clifford_iso_M2C_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 3) (hsig : sigPos Q = 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_Q₁₂ (by simp [hdim]) (by rw [hsig, sigPos_Q₁₂])
  exact ⟨e.trans equivM2C⟩

open CliffordRealQuantified in
/-- **Every** nondegenerate real form of signature `(1,3)` — the Minkowski signature, and the
theorem `F1_7` wants: the spacetime algebra does not depend on the coordinates it is written in. -/
theorem clifford_iso_M2H_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 4) (hsig : sigPos Q = 1) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ]) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_Q₁₃ (by simp [hdim]) (by rw [hsig, sigPos_Q₁₃])
  exact ⟨e.trans cliffordRealMinkowskiEquiv⟩

open CliffordRealQuantified in
/-- **Every** nondegenerate real form of signature `(3,1)` — the opposite convention, and a
different algebra, which is the content of the two theorems standing side by side. -/
theorem clifford_iso_M4R_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 4) (hsig : sigPos Q = 3) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_Q₃₁ (by simp [hdim]) (by rw [hsig, sigPos_Q₃₁])
  exact ⟨e.trans cliffordMajoranaEquiv⟩

open CliffordRealQuantified in
/-- **Every** nondegenerate real form of signature `(2,4)`. -/
theorem clifford_iso_M4H_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 6) (hsig : sigPos Q = 2) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℍ[ℝ]) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_Q₂₄ (by simp [hdim]) (by rw [hsig, sigPos_Q₂₄])
  exact ⟨e.trans equivM4H⟩

open CliffordRealQuantified in
/-- **Every** nondegenerate real form of signature `(4,2)`. -/
theorem clifford_iso_M8R_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 6) (hsig : sigPos Q = 4) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ) := by
  obtain ⟨e⟩ := cliffordEquiv_of_sigPos_eq hQ sep_Q₄₂ (by simp [hdim]) (by rw [hsig, sigPos_Q₄₂])
  exact ⟨e.trans equivM8R⟩

end Named

end

end CliffordRealSignatures
