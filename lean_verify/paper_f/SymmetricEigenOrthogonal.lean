import PathAdjBasis
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-!
# Eigenvectors of a symmetric matrix, at different eigenvalues, are orthogonal

`BoxSpectrumComplete` computed the `d`-dimensional box's whole adjacency spectrum and its exact
radius `2d·cos(π/(n+1))`, strictly inside the degree bound `2d`. **That does not yet improve any
operator bound**, because `LaplacianDegreeBound` works with the quadratic form `x ⬝ᵥ A *ᵥ x` and a
list of eigenvalues bounds a quadratic form only through an **orthogonal** eigenbasis.
`BoxAdjBasis`'s basis is proved independent and **not** orthogonal — its own closing section says
so. This file starts the orthogonality.

> **`dotProduct_eq_zero_of_eigen_ne`** — if `A` is symmetric and `A *ᵥ u = a • u`,
> `A *ᵥ v = b • v` with `a ≠ b`, then `u ⬝ᵥ v = 0`. Three lines: move `A` across the dot product
> and read the same number two ways.
>
> **`pathVec_dotProduct_eq_zero`** — hence the path graph's `n` sine modes are **pairwise
> orthogonal**, because `PathAdjBasis.eigenvalue_injective` already proves their eigenvalues
> distinct.

## Why it is stated with `⬝ᵥ` and not with `inner`

Mathlib has this fact — `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces` — for a symmetric
operator on an inner product space, as a statement about eigen**spaces**. Reaching it from here
would mean carrying `Fin n → ℝ` into `EuclideanSpace ℝ (Fin n)`, turning `Matrix.mulVec` into a
`LinearMap`, and extracting a vector-level statement from a subspace-level one. **Everything in
this chain and in `LaplacianDegreeBound` is written with the root-level `dotProduct` and its `⬝ᵥ`
notation**, so this is that fact transcribed into the vocabulary its consumers use, and it is a
transcription and not a new theorem: the Mathlib statement is cited here so a reader is not left
thinking the estate found something Mathlib lacks. (The function is `dotProduct` at the root and
**not** `Matrix.dotProduct`, which resolves to nothing in the pinned dump — probed 31 Aug 2026 —
while the lemmas about it do keep the prefix, `Matrix.dotProduct_mulVec` among them.)

## What this is NOT

**It is not the box's orthogonality.** The `d`-dimensional modes are products of path modes, and
in `d ≥ 2` **the eigenvalues repeat** — `(1, 2)` and `(2, 1)` give the same sum of cosines — so
`dotProduct_eq_zero_of_eigen_ne` **cannot** deliver the box directly. The box needs the inner
product to factorise across the product structure instead. **That is not done here** and as of
31 Aug 2026 no cost is offered for it (`ERRATUM 194`, `ERRATUM 246`).

**No norm is computed.** `pathVec n k ⬝ᵥ pathVec n k` is not evaluated; the classical value
`(n+1)/2` is not proved here and is not needed for orthogonality.

**No operator bound follows yet.** Turning an orthogonal eigenbasis into `x ⬝ᵥ A *ᵥ x ≤ ρ (x ⬝ᵥ x)`
is a further step, not taken here.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SymmetricEigenOrthogonal

open Matrix SimpleGraph PathAdjSpectrum

/-! ## 1. The general fact -/

variable {V : Type*} [Fintype V]

/-- **DIFFERENT EIGENVALUES FORCE ORTHOGONALITY.** `a·(u ⬝ᵥ v)` and `b·(u ⬝ᵥ v)` are the same
number — `A` moves from one side of the dot product to the other because `Aᵀ = A` — so their
difference `(a − b)·(u ⬝ᵥ v)` vanishes. -/
theorem dotProduct_eq_zero_of_eigen_ne {A : Matrix V V ℝ} (hA : A.IsSymm)
    {u v : V → ℝ} {a b : ℝ} (hu : A *ᵥ u = a • u) (hv : A *ᵥ v = b • v) (hab : a ≠ b) :
    u ⬝ᵥ v = 0 := by
  have hmove : u ⬝ᵥ (A *ᵥ v) = (A *ᵥ u) ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]
  rw [hu, hv, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at hmove
  have hsub : (b - a) * (u ⬝ᵥ v) = 0 := by rw [sub_mul]; linarith
  rcases mul_eq_zero.1 hsub with h | h
  · exact absurd (sub_eq_zero.1 h).symm hab
  · exact h

/-! ## 2. The path's sine modes -/

/-- **THE PATH'S `n` MODES ARE PAIRWISE ORTHOGONAL.** The eigenvalues are distinct
(`PathAdjBasis.eigenvalue_injective`) and the adjacency matrix is symmetric
(`SimpleGraph.isSymm_adjMatrix`), so §1 applies with nothing else to check. -/
theorem pathVec_dotProduct_eq_zero {n : ℕ} {k l : Fin n} (hkl : k ≠ l) :
    pathVec n (k.val + 1) ⬝ᵥ pathVec n (l.val + 1) = 0 := by
  refine dotProduct_eq_zero_of_eigen_ne (SimpleGraph.isSymm_adjMatrix _)
    (adjMatrix_mulVec_pathVec n (k.val + 1)) (adjMatrix_mulVec_pathVec n (l.val + 1)) ?_
  intro hcon
  exact hkl (PathAdjBasis.eigenvalue_injective n hcon)

end SymmetricEigenOrthogonal
