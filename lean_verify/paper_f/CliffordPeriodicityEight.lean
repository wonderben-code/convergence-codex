import CliffordTensorTwo

/-!
# The eight-fold periodicity: `Cl(Q ⊥ ⟨1,1⟩^⊥⁴) ≅ M₁₆(Cl Q)`

`CliffordTensorTwo` proved the two decomposition relations and `QuaternionTensor` proved
`ℍ ⊗ ℍ ≅ M₄(ℝ)`. This file is the **assembly**, which `PROGRESS_LOG` entry 31 named as the
remaining step and said was transport rather than mathematics. It was.

> **`equivEight`** — `Cl(Q ⊥ ⟨1,1⟩^⊥⁴) ≃ₐ[ℝ] M₁₆(Cl Q)`, and
> **`equivEightNeg`** — `Cl(Q ⊥ ⟨−1,−1⟩^⊥⁴) ≃ₐ[ℝ] M₁₆(Cl Q)`,
> for every real quadratic form `Q` on every finite-dimensional real space.

## The chain

`stepTwo` composes the two relations of `CliffordTensorTwo` once each:
`Cl(Q ⊥ ⟨1,1⟩ ⊥ ⟨1,1⟩) ≅ M₂(Cl Q ⊗ ℍ)`. The negation in the middle is what turns the second
*positive* step into a *negative* one, which is why the quaternions appear at all. Two applications
give `M₂(M₂(Cl Q ⊗ ℍ) ⊗ ℍ)`; `matrixTensorRight` moves the tensor factor inside the matrix,
`quatQuat` collapses `ℍ ⊗ ℍ` to `M₄(ℝ)` via `QuaternionTensor.equivM4`, and two applications of
`Matrix.compAlgEquiv` plus one reindex turn `M₂(M₂(M₄(·)))` into `M₁₆(·)`.

`stepTwoNeg` and `equivEightNeg` are the mirror, using the same two relations in the other order.

`neg_prod` — *negating an orthogonal sum negates each summand* — is **absent from Mathlib**
(`QuadraticMap.neg_prod` does not resolve in the pinned environment dump) and is proved here.

## What this is, and what it is not

**It is** the periodicity, for every form, as an algebra isomorphism, both ways.

**It is not yet the signature-level statement quantified over arbitrary forms.** The `Signature`
section proves what the construction does to `(p, q)` — `sigPos_eight` gives `p ↦ p + 8` with `q`
fixed, `sigNeg_eight_neg` gives `q ↦ q + 8` with `p` fixed — so the towers here *do* sit on the
right diagonals. Reading `equivEight` as *"`Cl(p+8,q) ≅ M₁₆(Cl(p,q))` for every form of signature
`(p+8,q)`"* additionally needs: every nondegenerate real form of signature `(p+8, q)` is isometric
to `Q ⊥ ⟨1,1⟩^⊥⁴` for some `Q` of signature `(p,q)`. That is Sylvester plus bookkeeping and
`CliffordRealQuantified.cliffordEquiv_of_sigPos_eq` is the tool for it, **but it is not written
here**, and `ERRATUM 212` is the entry about asserting a reach one step ahead of proving it.
-/

namespace CliffordPeriodicityEight

open CliffordTensorTwo CliffordAlgebra QuadraticMap
open scoped TensorProduct Quaternion

noncomputable section

/-- **Absent from Mathlib** (`QuadraticMap.neg_prod` does not resolve in the environment dump):
negating an orthogonal sum negates each summand. -/
theorem neg_prod {W₁ W₂ : Type*} [AddCommGroup W₁] [Module ℝ W₁] [AddCommGroup W₂] [Module ℝ W₂]
    (Q₁ : QuadraticForm ℝ W₁) (Q₂ : QuadraticForm ℝ W₂) :
    -(Q₁.prod Q₂) = (-Q₁).prod (-Q₂) := by
  ext x
  simp [QuadraticMap.prod_apply]
  ring

theorem neg_N (c₁ c₂ : ℝ) : -(N c₁ c₂) = N (-c₁) (-c₂) := by
  ext x
  simp [N, CliffordAlgebraQuaternion.Q_apply]
  ring

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem neg_Qext (Q : QuadraticForm ℝ V) (c₁ c₂ : ℝ) :
    -(Qext Q c₁ c₂) = Qext (-Q) (-c₁) (-c₂) := by
  rw [Qext, neg_prod, neg_N]

/-- The instance of `neg_Qext` the mirror chain needs, with `- -1` normalised. -/
theorem neg_Qext_neg (Q : QuadraticForm ℝ V) : -(Qext Q (-1) (-1)) = Qext (-Q) 1 1 := by
  rw [neg_Qext]
  simp only [neg_neg]

variable [FiniteDimensional ℝ V]

/-- Peeling the negation off a doubly-negated form. -/
def unNeg (Q : QuadraticForm ℝ V) : CliffordAlgebra (- -Q) ≃ₐ[ℝ] CliffordAlgebra Q :=
  CliffordTensorTwo.congrQ (neg_neg Q)

/-- **Two positive steps.** `Cl(Q ⊥ ⟨1,1⟩ ⊥ ⟨1,1⟩) ≅ M₂(Cl Q ⊗ ℍ)`: the positive step gives the
matrix factor, the negation turns the second positive step into a negative one, and the negative
step gives the quaternion factor. -/
def stepTwo (Q : QuadraticForm ℝ V) :
    CliffordAlgebra (Qext (Qext Q 1 1) 1 1) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q ⊗[ℝ] ℍ[ℝ]) :=
  (equivMatrixTwo (Qext Q 1 1)).trans <|
    AlgEquiv.mapMatrix <|
      (CliffordTensorTwo.congrQ (neg_Qext Q 1 1)).trans <|
        (equivQuatTwo (-Q)).trans <|
          Algebra.TensorProduct.congr (unNeg Q) AlgEquiv.refl

section Transport

variable (n : Type*) [Fintype n] [DecidableEq n]
variable (A B : Type*) [Ring A] [Algebra ℝ A] [Ring B] [Algebra ℝ B]

/-- `Mₙ(A) ⊗ B ≅ Mₙ(A ⊗ B)`: pull the matrix factor out with `matrixEquivTensor`, commute it past
`B`, and push it back in. -/
def matrixTensorRight :
    Matrix n n A ⊗[ℝ] B ≃ₐ[ℝ] Matrix n n (A ⊗[ℝ] B) :=
  (Algebra.TensorProduct.congr (matrixEquivTensor n ℝ A) AlgEquiv.refl).trans <|
    (Algebra.TensorProduct.assoc ℝ ℝ ℝ A (Matrix n n ℝ) B).trans <|
      (Algebra.TensorProduct.congr AlgEquiv.refl
          (Algebra.TensorProduct.comm ℝ (Matrix n n ℝ) B)).trans <|
        (Algebra.TensorProduct.assoc ℝ ℝ ℝ A B (Matrix n n ℝ)).symm.trans
          (matrixEquivTensor n ℝ (A ⊗[ℝ] B)).symm

end Transport

/-- `(A ⊗ ℍ) ⊗ ℍ ≅ M₄(A)`: reassociate, apply `QuaternionTensor.equivM4`, absorb. -/
def quatQuat (A : Type*) [Ring A] [Algebra ℝ A] :
    (A ⊗[ℝ] ℍ[ℝ]) ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) A :=
  (Algebra.TensorProduct.assoc ℝ ℝ ℝ A ℍ[ℝ] ℍ[ℝ]).trans <|
    (Algebra.TensorProduct.congr AlgEquiv.refl QuaternionTensor.equivM4).trans
      (matrixEquivTensor (Fin 4) ℝ A).symm

/-- `2 · (2 · 4) = 16`, as an index equivalence. -/
def fin16 : Fin 2 × (Fin 2 × Fin 4) ≃ Fin 16 :=
  ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- `2 · (4 · 2) = 16`, the shape the mirror chain produces. -/
def fin16' : Fin 2 × (Fin 4 × Fin 2) ≃ Fin 16 :=
  ((Equiv.refl (Fin 2)).prodCongr finProdFinEquiv).trans finProdFinEquiv

/-- **The four-step chain.** `Cl(Q ⊥ ⟨1,1⟩ ⊥ ⟨1,1⟩ ⊥ ⟨1,1⟩ ⊥ ⟨1,1⟩) ≅ M₁₆(Cl Q)`.

Two applications of `stepTwo` give `M₂(M₂(Cl Q ⊗ ℍ) ⊗ ℍ)`; `matrixTensorRight` moves the inner
tensor inside the matrix; `quatQuat` collapses `ℍ ⊗ ℍ` to `M₄(ℝ)`; and two applications of
`Matrix.compAlgEquiv` plus one reindex turn `M₂(M₂(M₄(·)))` into `M₁₆(·)`. -/
def equivEight (Q : QuadraticForm ℝ V) :
    CliffordAlgebra (Qext (Qext (Qext (Qext Q 1 1) 1 1) 1 1) 1 1) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) (CliffordAlgebra Q) :=
  (stepTwo (Qext (Qext Q 1 1) 1 1)).trans <|
    (AlgEquiv.mapMatrix (Algebra.TensorProduct.congr (stepTwo Q) AlgEquiv.refl)).trans <|
      (AlgEquiv.mapMatrix
          (matrixTensorRight (Fin 2) (CliffordAlgebra Q ⊗[ℝ] ℍ[ℝ]) ℍ[ℝ])).trans <|
        (AlgEquiv.mapMatrix (AlgEquiv.mapMatrix (quatQuat (CliffordAlgebra Q)))).trans <|
          (AlgEquiv.mapMatrix
              (Matrix.compAlgEquiv (Fin 2) (Fin 4) (CliffordAlgebra Q) ℝ)).trans <|
            (Matrix.compAlgEquiv (Fin 2) (Fin 2 × Fin 4) (CliffordAlgebra Q) ℝ).trans
              (Matrix.reindexAlgEquiv ℝ (CliffordAlgebra Q) fin16)

/-- **Two negative steps.** `Cl(Q ⊥ ⟨−1,−1⟩ ⊥ ⟨−1,−1⟩) ≅ M₂(Cl Q) ⊗ ℍ`. Same construction as
`stepTwo` with the two relations used in the other order, which is why the factors come out
swapped. -/
def stepTwoNeg (Q : QuadraticForm ℝ V) :
    CliffordAlgebra (Qext (Qext Q (-1) (-1)) (-1) (-1)) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) ⊗[ℝ] ℍ[ℝ] :=
  (equivQuatTwo (Qext Q (-1) (-1))).trans <|
    Algebra.TensorProduct.congr
      ((CliffordTensorTwo.congrQ (neg_Qext_neg Q)).trans <|
        (equivMatrixTwo (-Q)).trans (AlgEquiv.mapMatrix (unNeg Q)))
      AlgEquiv.refl

/-- **The mirror chain.** `Cl(Q ⊥ ⟨−1,−1⟩^⊥⁴) ≅ M₁₆(Cl Q)`. -/
def equivEightNeg (Q : QuadraticForm ℝ V) :
    CliffordAlgebra (Qext (Qext (Qext (Qext Q (-1) (-1)) (-1) (-1)) (-1) (-1)) (-1) (-1)) ≃ₐ[ℝ]
      Matrix (Fin 16) (Fin 16) (CliffordAlgebra Q) :=
  (stepTwoNeg (Qext (Qext Q (-1) (-1)) (-1) (-1))).trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.mapMatrix (stepTwoNeg Q)) AlgEquiv.refl).trans <|
      (matrixTensorRight (Fin 2) (Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) ⊗[ℝ] ℍ[ℝ])
          ℍ[ℝ]).trans <|
        (AlgEquiv.mapMatrix (quatQuat (Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)))).trans <|
          (AlgEquiv.mapMatrix
              (Matrix.compAlgEquiv (Fin 4) (Fin 2) (CliffordAlgebra Q) ℝ)).trans <|
            (Matrix.compAlgEquiv (Fin 2) (Fin 4 × Fin 2) (CliffordAlgebra Q) ℝ).trans
              (Matrix.reindexAlgEquiv ℝ (CliffordAlgebra Q) fin16')

/-! ### What the chain does to the signature

The isomorphisms above are statements about **forms**. These four lemmas say what the construction
does to `(p, q)`, which is what makes `equivEight` readable as *the eight-fold periodicity* rather
than as a fact about one particular tower of products. -/

section Signature

open CliffordRealSignatures

variable (Q : QuadraticForm ℝ V)

@[simp] theorem sigPos_Qext_pos : sigPos (Qext Q 1 1) = sigPos Q + 2 := by
  simp [Qext, N, SignatureArithmetic.sigPos_prod]

@[simp] theorem sigNeg_Qext_pos : sigNeg (Qext Q 1 1) = sigNeg Q := by
  simp [Qext, N, SignatureArithmetic.sigNeg_prod]

@[simp] theorem sigPos_Qext_neg : sigPos (Qext Q (-1) (-1)) = sigPos Q := by
  simp [Qext, N, SignatureArithmetic.sigPos_prod]

@[simp] theorem sigNeg_Qext_neg : sigNeg (Qext Q (-1) (-1)) = sigNeg Q + 2 := by
  simp [Qext, N, SignatureArithmetic.sigNeg_prod]

/-- **`p ↦ p + 8`, `q` fixed.** -/
theorem sigPos_eight :
    sigPos (Qext (Qext (Qext (Qext Q 1 1) 1 1) 1 1) 1 1) = sigPos Q + 8 := by
  simp

theorem sigNeg_eight :
    sigNeg (Qext (Qext (Qext (Qext Q 1 1) 1 1) 1 1) 1 1) = sigNeg Q := by
  simp

/-- **`q ↦ q + 8`, `p` fixed.** -/
theorem sigNeg_eight_neg :
    sigNeg (Qext (Qext (Qext (Qext Q (-1) (-1)) (-1) (-1)) (-1) (-1)) (-1) (-1))
      = sigNeg Q + 8 := by
  simp

theorem sigPos_eight_neg :
    sigPos (Qext (Qext (Qext (Qext Q (-1) (-1)) (-1) (-1)) (-1) (-1)) (-1) (-1))
      = sigPos Q := by
  simp

end Signature

end

end CliffordPeriodicityEight
