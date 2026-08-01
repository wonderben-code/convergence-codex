/-
# The Schur product theorem: positive semidefiniteness is closed under the
# Hadamard (entrywise) product

**What is proven.** For matrices over any `RCLike` field (so ℝ and ℂ):

* `exists_gram` — every positive semidefinite matrix is a Gram matrix `Pᴴ * P`
  (through Mathlib's C⋆-order on matrices, `CStarAlgebra.nonneg_iff_eq_star_mul_self`).
* `hadamard_eq_gram` — the Hadamard product of two Gram matrices is itself a Gram
  matrix, over the PRODUCT index: `(Pᴴ P) ⊙ (Qᴴ Q) = Rᴴ R` with
  `R (k,l) j = P k j * Q l j`.
* `posSemidef_hadamard` — THE SCHUR PRODUCT THEOREM: `A.PosSemidef → B.PosSemidef
  → (A ⊙ B).PosSemidef`.
* `posSemidef_allOnes`, `posSemidef_entrywise_prod` (families indexed by
  `Fin m`), and `posSemidef_entrywise_prod'` (families indexed by ANY finite
  type, by transport along `Fintype.equivFin`) — the iterated form: the
  entrywise product of a finite family of PSD matrices is PSD (empty product
  = all-ones matrix, itself the Gram matrix of a single vector). An
  adversarial review (round 4, F5) caught the header saying "ANY finite
  family" while only the `Fin`-indexed version existed; the general version
  now exists.
* `posSemidef_diagonal_diag` — corollary with independent content: the diagonal
  part of a PSD matrix is PSD (Schur against the identity).
* Concrete witnesses: `!![2,1;1,2] ⊙ !![2,1;1,2] = !![4,1;1,4]` is PSD, and
  `!![0,1;1,0]` is NOT PSD — the hypothesis genuinely excludes matrices.

**Why this file exists.** This is stair S1 of the OS2-d>1 staircase
(UNLOCK_WATCHLIST): the reflected covariance matrix of a d-dimensional
OU-product field is the entrywise product of d one-dimensional covariance
factors; for d ≥ 3 at least two spectator factors multiply and closure of PSD
under entrywise products is exactly what the assembly needs.
`posSemidef_entrywise_prod` is the form the assembly (stair S3) consumes.

**Route.** NOT the spectral-decomposition route sketched on the watchlist — a
shorter one found during the build: Gram decomposition through the C⋆-algebra
order (Mathlib's scoped `MatrixOrder`), then the product-index Gram identity,
then `posSemidef_conjTranspose_mul_self`. No eigenvalues, no analysis.

**Checked against Mathlib v4.29.1.** `Matrix.hadamard` exists with no
positivity lemma; the Kronecker analogue `PosSemidef.kronecker` exists, the
Hadamard one does not. This file fills that gap.

**Scope honesty.** Pure matrix linear algebra. Nothing here mentions measures,
fields, or reflection positivity; the OS2 assembly that consumes this is a
separate file with its own honesty box.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Notation

namespace SchurProduct

open Matrix
open scoped ComplexOrder MatrixOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- Every positive semidefinite matrix over `ℝ` or `ℂ` is a Gram matrix
`Pᴴ * P`. (Mathlib has the converse `posSemidef_conjTranspose_mul_self`; this
direction comes out of the C⋆-algebra order on square matrices.) -/
theorem exists_gram [Fintype n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ P : Matrix n n 𝕜, A = Pᴴ * P := by
  classical
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  exact ⟨P, by rw [hP, star_eq_conjTranspose]⟩

/-- The rectangular matrix whose Gram form is the Hadamard product of the Gram
forms of `P` and `Q`: rows are indexed by PAIRS `(k, l)`, and row `(k, l)` is
the entrywise product of row `k` of `P` with row `l` of `Q`. -/
def gramPair (P Q : Matrix n n 𝕜) : Matrix (n × n) n 𝕜 :=
  Matrix.of fun kl j => P kl.1 j * Q kl.2 j

/-- The Hadamard product of two Gram matrices is the Gram matrix of
`gramPair`: `(Pᴴ P) ⊙ (Qᴴ Q) = Rᴴ R` with `R (k,l) j = P k j * Q l j`.
Entrywise this is just `(∑ₖ aₖ)(∑ₗ bₗ) = ∑₍ₖ,ₗ₎ aₖbₗ`. -/
theorem hadamard_eq_gram [Fintype n] (P Q : Matrix n n 𝕜) :
    (Pᴴ * P) ⊙ (Qᴴ * Q) = (gramPair P Q)ᴴ * gramPair P Q := by
  ext i j
  simp only [hadamard_apply, Matrix.mul_apply, conjTranspose_apply, gramPair, Matrix.of_apply,
    Fintype.sum_prod_type, Finset.sum_mul_sum, star_mul']
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- **The Schur product theorem.** The Hadamard (entrywise) product of two
positive semidefinite matrices is positive semidefinite. -/
theorem posSemidef_hadamard [Finite n] {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A ⊙ B).PosSemidef := by
  have := Fintype.ofFinite n
  obtain ⟨P, rfl⟩ := exists_gram hA
  obtain ⟨Q, rfl⟩ := exists_gram hB
  rw [hadamard_eq_gram]
  exact posSemidef_conjTranspose_mul_self _

/-- The all-ones matrix is positive semidefinite: it is the Gram matrix of the
single vector `(1, …, 1)`. This is the empty case of the iterated Schur
theorem. -/
theorem posSemidef_allOnes [Finite n] :
    (Matrix.of fun _ _ => (1 : 𝕜) : Matrix n n 𝕜).PosSemidef := by
  have key : (Matrix.of fun _ _ => (1 : 𝕜) : Matrix n n 𝕜)
      = (Matrix.of fun _ _ => (1 : 𝕜) : Matrix Unit n 𝕜)ᴴ
        * (Matrix.of fun _ _ => (1 : 𝕜) : Matrix Unit n 𝕜) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [key]
  exact posSemidef_conjTranspose_mul_self _

/-- **Iterated Schur product theorem.** The entrywise product of a finite
family of positive semidefinite matrices is positive semidefinite. This is the
form the d-dimensional OS2 assembly consumes (one factor per coordinate). -/
theorem posSemidef_entrywise_prod [Finite n] {m : ℕ} (M : Fin m → Matrix n n 𝕜)
    (hM : ∀ k, (M k).PosSemidef) :
    (Matrix.of fun i j => ∏ k, M k i j).PosSemidef := by
  induction m with
  | zero =>
      simpa [Fin.prod_univ_zero] using (posSemidef_allOnes (𝕜 := 𝕜) (n := n))
  | succ m ih =>
      have key : (Matrix.of fun i j => ∏ k, M k i j)
          = (M 0) ⊙ (Matrix.of fun i j => ∏ k : Fin m, M k.succ i j) := by
        ext i j
        simp [Fin.prod_univ_succ, hadamard_apply]
      rw [key]
      exact posSemidef_hadamard (hM 0) (ih _ fun k => hM _)

/-- **Iterated Schur product theorem over an ARBITRARY finite index type**:
transport of `posSemidef_entrywise_prod` along `Fintype.equivFin`. -/
theorem posSemidef_entrywise_prod' {ι : Type*} [Fintype ι] [Finite n]
    (M : ι → Matrix n n 𝕜) (hM : ∀ k, (M k).PosSemidef) :
    (Matrix.of fun i j => ∏ k, M k i j).PosSemidef := by
  have h := posSemidef_entrywise_prod
    (fun l : Fin (Fintype.card ι) => M ((Fintype.equivFin ι).symm l))
    (fun l => hM _)
  have heq : (Matrix.of fun i j =>
      ∏ l : Fin (Fintype.card ι), M ((Fintype.equivFin ι).symm l) i j)
      = (Matrix.of fun i j => ∏ k, M k i j) := by
    ext i j
    exact Fintype.prod_equiv (Fintype.equivFin ι).symm _ _ (fun l => rfl)
  rwa [heq] at h

/-- Corollary with content of its own: the diagonal part of a positive
semidefinite matrix is positive semidefinite (Schur product against the
identity matrix). -/
theorem posSemidef_diagonal_diag [Finite n] [DecidableEq n] {B : Matrix n n 𝕜}
    (hB : B.PosSemidef) : (Matrix.diagonal fun i => B i i).PosSemidef := by
  have := Fintype.ofFinite n
  have h1 : (1 : Matrix n n 𝕜).PosSemidef := by
    simpa using posSemidef_conjTranspose_mul_self (1 : Matrix n n 𝕜)
  have key : Matrix.diagonal (fun i => B i i) = (1 : Matrix n n 𝕜) ⊙ B := by
    ext i j
    by_cases h : i = j <;> simp [hadamard_apply, h]
  rw [key]
  exact posSemidef_hadamard h1 hB

/- ## Concrete witnesses: the theorem bites, the hypothesis excludes -/

/-- A concrete PSD matrix, proven PSD from the definition (quadratic form is a
sum of squares): `x ⬝ !![2,1;1,2] x = x₀² + (x₀+x₁)² + x₁²`. -/
theorem twoOneOneTwo_posSemidef : (!![(2 : ℝ), 1; 1, 2]).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x
    have h : (star x) ⬝ᵥ ((!![(2 : ℝ), 1; 1, 2]).mulVec x)
        = x 0 ^ 2 + (x 0 + x 1) ^ 2 + x 1 ^ 2 := by
      simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      ring
    rw [h]
    positivity

/-- The Hadamard square of the concrete witness, computed entrywise. -/
theorem hadamard_square_concrete :
    (!![(2 : ℝ), 1; 1, 2] ⊙ !![(2 : ℝ), 1; 1, 2]) = !![(4 : ℝ), 1; 1, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadamard_apply] <;> norm_num

/-- Non-vacuity of the Schur theorem on concrete data:
`!![4,1;1,4]` is PSD because it is the Hadamard square of a PSD matrix. -/
theorem fourOneOneFour_posSemidef : (!![(4 : ℝ), 1; 1, 4]).PosSemidef := by
  rw [← hadamard_square_concrete]
  exact posSemidef_hadamard twoOneOneTwo_posSemidef twoOneOneTwo_posSemidef

/-- The hypothesis genuinely excludes matrices: the symmetric matrix
`!![0,1;1,0]` is NOT positive semidefinite (its quadratic form at `(1, −1)`
is `−2`). PSD is not a triviality of symmetry. -/
theorem not_posSemidef_offDiag : ¬ (!![(0 : ℝ), 1; 1, 0]).PosSemidef := by
  intro h
  have h2 := h.dotProduct_mulVec_nonneg ![1, -1]
  have hval : (star ![(1 : ℝ), -1]) ⬝ᵥ ((!![(0 : ℝ), 1; 1, 0]).mulVec ![1, -1])
      = -2 := by
    simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
    norm_num
  rw [hval] at h2
  linarith

end SchurProduct
