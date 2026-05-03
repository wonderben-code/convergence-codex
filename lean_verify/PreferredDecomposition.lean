/-
  Emergence Stage 3: Preferred Decomposition of D₂
  =================================================

  Paper E — Emergence of the Standard Model from the Generator Construction

  CLAIM: D₂ = End(M₂(ℂ)) = M₄(ℂ) has a canonical tensor decomposition:
    M₄(ℂ) ≅ M₂(ℂ) ⊗ M₂(ℂ)

  This decomposition arises because:
  1. For any central simple algebra A: End(A) ≅ A ⊗ A^op (Azumaya property)
  2. M₂(ℂ)^op ≅ M₂(ℂ) via transpose (since ℂ is commutative)
  3. Therefore: End(M₂(ℂ)) ≅ M₂(ℂ) ⊗ M₂(ℂ)^op ≅ M₂(ℂ) ⊗ M₂(ℂ)

  The Kronecker product isomorphism gives the concrete form:
    M₂(ℂ) ⊗ M₂(ℂ) ≅ M_{Fin 2 × Fin 2}(ℂ) ≅ M₄(ℂ)

  The automorphism group of M₂(ℂ) ⊗ M₂(ℂ) naturally contains
  Aut(M₂(ℂ)) × Aut(M₂(ℂ)) ⊃ PSU(2) × PSU(2).
  This is the Pati-Salam intermediate symmetry SU(2)_L × SU(2)_R.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1
  Target: 0 sorry
-/

import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Complex.Basic

open Matrix
open scoped TensorProduct

/-!
## Part 1: The Kronecker Product Isomorphism

M₂(ℂ) ⊗_ℂ M₂(ℂ) ≅ M_{Fin 2 × Fin 2}(ℂ) as ℂ-algebras.
The Kronecker product maps A ⊗ B to the block matrix with entries A_{ij} · B.
-/

/-- **Theorem 3.1 (Kronecker Isomorphism):**
    M₂(ℂ) ⊗ M₂(ℂ) ≅ M_{Fin 2 × Fin 2}(ℂ) as ℂ-algebras.
    The tensor product of two 2×2 matrix algebras is a matrix algebra
    indexed by the product index set. -/
noncomputable def kronecker_M2_equiv :
    (Matrix (Fin 2) (Fin 2) ℂ ⊗[ℂ] Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℂ]
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  kroneckerAlgEquiv (Fin 2) (Fin 2) ℂ

/-- Generalisation: Mₘ(ℂ) ⊗ Mₙ(ℂ) ≅ M_{m×n}(ℂ) for any m, n. -/
noncomputable def kronecker_Mmn_equiv (m n : ℕ) :
    (Matrix (Fin m) (Fin m) ℂ ⊗[ℂ] Matrix (Fin n) (Fin n) ℂ) ≃ₐ[ℂ]
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  kroneckerAlgEquiv (Fin m) (Fin n) ℂ

/-!
## Part 2: M₂(ℂ)^op ≅ M₂(ℂ) via Transpose

Since ℂ is commutative, the transpose map gives an algebra isomorphism
from Mₙ(ℂ) to its opposite algebra Mₙ(ℂ)^op.
This is what converts the Azumaya decomposition End(A) ≅ A ⊗ A^op
into the symmetric form A ⊗ A.
-/

/-- **Theorem 3.2 (Opposite via Transpose):**
    M₂(ℂ) ≅ M₂(ℂ)^op as ℂ-algebras.
    Since ℂ is commutative, transpose is an algebra isomorphism
    to the opposite algebra (not just an anti-homomorphism). -/
noncomputable def M2_equiv_op :
    Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ :=
  transposeAlgEquiv (R := ℂ) (m := Fin 2) (α := ℂ)

/-- Generalisation: Mₙ(ℂ)^op ≅ Mₙ(ℂ) for any n. -/
noncomputable def Mn_equiv_op (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
  transposeAlgEquiv (R := ℂ) (m := Fin n) (α := ℂ)

/-!
## Part 3: Index Identification

Fin 2 × Fin 2 ≃ Fin 4 — the product index set has 4 elements.
This canonical equivalence identifies M_{Fin 2 × Fin 2}(ℂ) with M₄(ℂ).
-/

/-- The canonical equivalence Fin 2 × Fin 2 ≃ Fin 4. -/
def fin2_prod_equiv_fin4 : Fin 2 × Fin 2 ≃ Fin 4 :=
  finProdFinEquiv

/-- The product index has cardinality 4. -/
theorem card_fin2_prod : Fintype.card (Fin 2 × Fin 2) = 4 := by
  simp [Fintype.card_prod, Fintype.card_fin]

/-!
## Part 4: Reindexing — M_{Fin 2 × Fin 2}(ℂ) ≅ M₄(ℂ)

Using the equivalence Fin 2 × Fin 2 ≃ Fin 4, we reindex the
matrix algebra to get the standard form M₄(ℂ).
-/

/-- **Theorem 3.3 (Reindexing):**
    M_{Fin 2 × Fin 2}(ℂ) ≅ M₄(ℂ) as ℂ-algebras via finProdFinEquiv. -/
noncomputable def reindex_to_M4 :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ :=
  reindexAlgEquiv ℂ ℂ fin2_prod_equiv_fin4

/-!
## Part 5: The Full Tensor Decomposition

Combining the Kronecker isomorphism with reindexing:
  M₂(ℂ) ⊗ M₂(ℂ)  ≅  M_{Fin 2 × Fin 2}(ℂ)  ≅  M₄(ℂ)

This proves D₂ = M₄(ℂ) ≅ M₂(ℂ) ⊗ M₂(ℂ), the preferred
tensor decomposition of the second iteration.
-/

/-- **Theorem 3.4 (Tensor Decomposition of D₂):**
    M₂(ℂ) ⊗ M₂(ℂ) ≅ M₄(ℂ) as ℂ-algebras.
    Combined with Stage 1 (D₂ = End(ℂ⁴) ≅ M₄(ℂ)), this gives
    the preferred tensor decomposition of D₂. -/
noncomputable def M2_tensor_M2_equiv_M4 :
    (Matrix (Fin 2) (Fin 2) ℂ ⊗[ℂ] Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℂ]
    Matrix (Fin 4) (Fin 4) ℂ :=
  kronecker_M2_equiv.trans reindex_to_M4

/-!
## Part 6: The Preferred Decomposition Summary

All machine-verified results combined into a single theorem.
-/

/-- **THE PREFERRED DECOMPOSITION AT D₂:**

    The second iteration D₂ = End(M₂(ℂ)) = M₄(ℂ) decomposes as:

    1. M₂(ℂ) ⊗ M₂(ℂ) ≅ M₄(ℂ) as ℂ-algebras (Kronecker + reindexing).
    2. M₂(ℂ) ≅ M₂(ℂ)^op via transpose (ℂ is commutative).
    3. |Fin 2 × Fin 2| = 4 (index identification).

    Combined with the Azumaya property End(A) ≅ A ⊗ A^op for
    central simple A (established algebra, not formalised here),
    and Theorem 3.2, we get the canonical decomposition:
      D₂ = End(M₂(ℂ)) ≅ M₂(ℂ) ⊗ M₂(ℂ)^op ≅ M₂(ℂ) ⊗ M₂(ℂ)

    The automorphism group of M₂(ℂ) ⊗ M₂(ℂ) naturally contains:
      Aut(M₂(ℂ)) × Aut(M₂(ℂ)) ⊃ PSU(2) × PSU(2)

    This is the Pati-Salam intermediate symmetry SU(2)_L × SU(2)_R.
    The SECOND iteration already contains a product gauge structure. -/
theorem preferred_decomposition_at_D2 :
    -- Kronecker + reindex gives M₂ ⊗ M₂ ≅ M₄
    Nonempty ((Matrix (Fin 2) (Fin 2) ℂ ⊗[ℂ] Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℂ]
              Matrix (Fin 4) (Fin 4) ℂ) ∧
    -- Transpose gives M₂ ≅ M₂^op
    Nonempty (Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ) ∧
    -- Product index has 4 elements
    Fintype.card (Fin 2 × Fin 2) = 4 :=
  ⟨⟨M2_tensor_M2_equiv_M4⟩, ⟨M2_equiv_op⟩, card_fin2_prod⟩
