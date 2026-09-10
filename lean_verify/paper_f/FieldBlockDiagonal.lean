import FieldCommutantSpectral

/-!
# The symmetry group of the propagator, block by block

`FieldCommutantSpectral.mem_symmetryMatrices_iff` proved that an orthogonal matrix is a symmetry
of the Gaussian field exactly when it preserves every eigenspace of the propagator, and fenced the
next question: *which* orthogonal maps those are depends on the multiplicities, and **that
composition is not made**. `UNLOCK_WATCHLIST`'s *exact count of the symmetries on the torus* item
says the same thing from the other side, and says what the answer should look like — *the symmetry
group of a degenerate propagator should be `∏ᵢ O(dᵢ)` over the distinct eigenvalues, with `dᵢ` the
multiplicities* — and that **the composition is not made**.

**This file makes it.** For a non-zero mass, an orthogonal `R` is a symmetry of the Gaussian field
**iff its conjugate by the propagator's eigenvector matrix vanishes at every pair of indices
carrying different eigenvalues** (`mem_symmetryMatrices_iff_blockDiagonal`), and that conjugate is
itself orthogonal (`conj_transpose_mul_self`). So conjugation carries the symmetry group onto the
orthogonal matrices that are **block diagonal with respect to the partition of indices by
eigenvalue** — which is `∏ᵢ O(dᵢ)` with the blocks the eigenvalue fibres.

**The route is matrix algebra and not spectral analysis**, which is why it is one file. The
previous unit needed `eigenvectorBasis` to know the eigenvectors span; this one needs only that
they assemble into an orthogonal matrix `P` with `green · P = P · D` (`green_mul_eigP`, proved
column by column from `Matrix.IsHermitian.mulVec_eigenvectorBasis`). After that,
`Pᵀ · green · P = D`, conjugation is injective (`eq_of_conj_eq`), and the whole question reduces to
**when a matrix commutes with a diagonal one** — which is `commutes_diagonal_iff`, an entrywise
fact with no graph, eigenvalue or symmetry in it: `(M · diagonal d) i j = M i j · d j` and
`(diagonal d · M) i j = d i · M i j`, so the two agree at `(i, j)` iff `M i j = 0` or `d i = d j`.

**`commutes_diagonal_iff` was searched for before it was written** (`ERRATUM 42`'s rule — grep the
shape, not the name): Mathlib's `Matrix.commute_diagonal` is the case of **two** diagonal matrices,
and the general one is not in `Data/Matrix/` or `LinearAlgebra/Matrix/` under any name found.

## What is proved

**`commutes_diagonal_iff`** — a matrix commutes with `diagonal d` iff its entries vanish wherever
`d` takes different values. General, entrywise, no hypotheses.

**`green_isHermitian`, `eigP`, `eigMu`, `eigP_apply`** — the propagator's eigenvector matrix and
eigenvalue vector, named so the statements below fit on a line.

**`eigP_transpose_mul_self`, `eigP_mul_transpose_self`** — `Pᵀ P = 1` and `P Pᵀ = 1`, which over
`ℝ` is what `Matrix.unitaryGroup` membership says.

**`green_mul_eigP`, `transpose_mul_green_mul_eigP`** — `green · P = P · D` and `Pᵀ · green · P = D`:
the propagator diagonalised.

**`eq_of_conj_eq`** — conjugation by `P` is injective, which is what makes the characterisation an
`iff` rather than an implication.

**`conj_mul_diagonal`, `diagonal_mul_conj`** — the two products the characterisation compares,
each rewritten as a conjugate of a product with the propagator.

**`comm_iff_blockDiagonal`** — **A MATRIX COMMUTES WITH THE PROPAGATOR IFF ITS CONJUGATE IS BLOCK
DIAGONAL.** For any matrix; orthogonality plays no part, exactly as in the previous unit.

**`conj_transpose_mul_self`** — the conjugate of an orthogonal matrix is orthogonal, so the blocks
are orthogonal and not merely invertible.

**`mem_symmetryMatrices_iff_blockDiagonal`** — **THE SYMMETRY GROUP OF THE PROPAGATOR IS EXACTLY
THE ORTHOGONAL BLOCK-DIAGONAL GROUP IN ITS EIGENBASIS**, and **`blockDiagonal_off_fibre`** is that
with the eigenvalue named, so a consumer can quote the fibre rather than a pair of indices.

## What is NOT here

**NO GROUP ISOMORPHISM, AND SO NO COUNT.** What is proved is a **characterisation of membership**,
not an isomorphism `symmetryMatrices ≃* ∏ᵢ O(dᵢ)`. Building that needs the index type of distinct
eigenvalues as a quotient, a `Matrix.blockDiagonal` over it, and the two group homomorphisms;
none of the three is here. **So the *exact count of the symmetries on the torus* item is NOT
closed** — `FieldTorusRotation.infinite_symmetryMatrices_torus` still gives `Set.Infinite` and
nothing finer, and an infinite group is what `∏ᵢ O(dᵢ)` is whenever some `dᵢ ≥ 2`, which
`FieldTorusRotation.oneFreq` says is always. **Not attempted, no cost claimed** (`ERRATUM 246`).
[⚠ **THE ISOMORPHISM NOW EXISTS AND THE SENTENCE IS KEPT AS WRITTEN** (`ERRATUM 94`, 10 SEP 2026):
`FieldBlockGroup.conjEigEquiv` built it onto the block-diagonal monoid and
`FieldBlockProduct.symmetry_mulEquiv_prod` composes that with
`FieldBlockProduct.blockProdEquiv` to give `symmetrySubmonoid G m ≃* ∀ c : Lev (eigMu G m hm),
Matrix.unitaryGroup (Fib (eigMu G m hm) c) ℝ` — the product over the distinct eigenvalues, with all
three of the missing pieces built: the index type is `Set.range (eigMu G m hm)`, the assembly is
`Matrix.blockDiagonal'` through `Equiv.sigmaSubtypeFiberEquiv`, and the homomorphism is a
`MulEquiv`. **The clause about the COUNT stands unchanged**: the group is infinite whenever a block
has size two, so `Set.Infinite` is still the finest cardinality statement and this sentence was
right about that.]

**NO IDENTIFICATION OF THE BLOCK SIZES WITH THE MULTIPLICITIES.** The blocks here are indexed by
the fibres of `Matrix.IsHermitian.eigenvalues`, and that the fibre of `μ` has size equal to
`finrank` of the `μ`-eigenspace is **not proved here and is not in this estate**. It is what would
join this description to `TorusRealMultiplicity.finrank_eigenspace_massive_real` and
`BoxEigenspaceDimension`'s fibre counts, and until it exists the phrase `∏ᵢ O(dᵢ)` is a reading of
these theorems rather than one of them.
[⚠ **BOTH HALVES OF THIS PARAGRAPH ARE NOW FALSE AND IT IS KEPT AS WRITTEN** (`ERRATUM 94`,
10 SEP 2026). The first half went false three entries later and was never marked until now:
`FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre` proves the fibre of `μ` has size
`finrank` of the `μ`-eigenspace, and `ker_massive_sub_eq_ker_green_sub` joins it to
`TorusRealMultiplicity`'s counts by showing the two eigenspaces are the SAME submodule. The second
half went false today: `FieldBlockProduct.blockProdEquiv` makes `∏ᵢ O(dᵢ)` one of these theorems
rather than a reading of them, and `FieldBlockProduct.card_fib_eq_finrank_eigenspace` is the
identification this paragraph asked for, stated at a factor of that product.]

**NOTHING ABOUT WHICH GRAPHS.** No graph is named anywhere in this file; every statement is at an
arbitrary finite `SimpleGraph` with a non-zero mass. The degeneracies that make the description
interesting are the box's and the torus's, and they are elsewhere.

**NO WALL MOVES.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A
description of a finite-volume symmetry group — even an exact one — is a wider shadow of an axiom
and not a smaller gap in it, and this file is a description rather than an exact one.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a `Fintype V` with `DecidableEq V`, a
`SimpleGraph V` with `DecidableRel G.Adj`, a real mass `m`, and `hm : m ≠ 0` on every statement
that mentions the propagator — the last because `green` is positive definite, hence Hermitian, only
away from zero mass. `commutes_diagonal_iff` takes none of them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldBlockDiagonal

open Matrix GraphLaplacian FieldRotationCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Commuting with a diagonal matrix, entrywise -/

/-- **A MATRIX COMMUTES WITH A DIAGONAL MATRIX EXACTLY WHERE ITS ENTRIES VANISH OFF THE DIAGONAL'S
LEVEL SETS.** No graph, no eigenvalue, no symmetry: `(M * diagonal d) i j = M i j * d j` and
`(diagonal d * M) i j = d i * M i j`, so the two agree at `(i, j)` iff `M i j = 0`
or `d i = d j`. -/
theorem commutes_diagonal_iff {M : Matrix V V ℝ} {d : V → ℝ} :
    M * diagonal d = diagonal d * M ↔ ∀ i j, d i ≠ d j → M i j = 0 := by
  constructor
  · intro h i j hne
    have hEq := congrFun (congrFun h i) j
    rw [mul_diagonal, diagonal_mul] at hEq
    have hfac : M i j * (d j - d i) = 0 := by rw [mul_sub]; linarith
    rcases mul_eq_zero.1 hfac with h' | h'
    · exact h'
    · exact absurd (sub_eq_zero.1 h').symm hne
  · intro h
    ext i j
    rw [mul_diagonal, diagonal_mul]
    by_cases hij : d i = d j
    · rw [hij]; ring
    · rw [h i j hij]; ring

/-! ## 2. The propagator's eigenvector matrix -/

section
variable (G) (m)

/-- The propagator is Hermitian at a non-zero mass, because it is positive definite. -/
theorem green_isHermitian (hm : m ≠ 0) : (green G m).IsHermitian :=
  (green_posDef G hm).isHermitian

/-- The orthogonal matrix whose columns are the propagator's eigenvectors. -/
noncomputable def eigP (hm : m ≠ 0) : Matrix V V ℝ :=
  ((green_isHermitian G m hm).eigenvectorUnitary : Matrix V V ℝ)

/-- The propagator's eigenvalues, indexed the same way as `eigP`'s columns. -/
noncomputable def eigMu (hm : m ≠ 0) : V → ℝ :=
  (green_isHermitian G m hm).eigenvalues

end

theorem eigP_apply (hm : m ≠ 0) (i j : V) :
    eigP G m hm i j = (green_isHermitian G m hm).eigenvectorBasis j i := rfl

/-- **`Pᵀ P = 1`**: the eigenvector matrix is orthogonal, which over `ℝ` is what being unitary
says. -/
theorem eigP_transpose_mul_self (hm : m ≠ 0) :
    (eigP G m hm)ᵀ * eigP G m hm = 1 := by
  have h := (green_isHermitian G m hm).eigenvectorUnitary.2.1
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **`green P = P D`**: the eigenvector matrix carries the propagator to the diagonal of its
eigenvalues. Both sides have `(i, j)` entry `μⱼ · Pᵢⱼ`, the left because column `j` of `P` is the
`j`-th eigenvector. -/
theorem green_mul_eigP (hm : m ≠ 0) :
    green G m * eigP G m hm = eigP G m hm * diagonal (eigMu G m hm) := by
  ext i j
  rw [mul_diagonal]
  have hcol : (fun k => eigP G m hm k j) = ⇑((green_isHermitian G m hm).eigenvectorBasis j) := rfl
  have : (green G m * eigP G m hm) i j = (green G m *ᵥ (fun k => eigP G m hm k j)) i := rfl
  rw [this, hcol, (green_isHermitian G m hm).mulVec_eigenvectorBasis]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [eigP_apply, eigMu]
  ring

/-- **`P Pᵀ = 1`** as well: a square matrix with `Pᵀ P = 1` over `ℝ` has the other identity too,
and the unitary group carries both. -/
theorem eigP_mul_transpose_self (hm : m ≠ 0) :
    eigP G m hm * (eigP G m hm)ᵀ = 1 := by
  have h := (green_isHermitian G m hm).eigenvectorUnitary.2.2
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **`Pᵀ green P = D`**: the propagator diagonalised. -/
theorem transpose_mul_green_mul_eigP (hm : m ≠ 0) :
    (eigP G m hm)ᵀ * green G m * eigP G m hm = diagonal (eigMu G m hm) := by
  rw [Matrix.mul_assoc, green_mul_eigP, ← Matrix.mul_assoc, eigP_transpose_mul_self,
    Matrix.one_mul]

/-- Conjugation by `P` is injective, which is the whole of what makes the characterisation an
`iff`. -/
theorem eq_of_conj_eq (hm : m ≠ 0) {X Y : Matrix V V ℝ}
    (h : (eigP G m hm)ᵀ * X * eigP G m hm = (eigP G m hm)ᵀ * Y * eigP G m hm) : X = Y := by
  have hP := eigP_mul_transpose_self (G := G) (m := m) hm
  have key : ∀ Z : Matrix V V ℝ,
      eigP G m hm * ((eigP G m hm)ᵀ * Z * eigP G m hm) * (eigP G m hm)ᵀ = Z := by
    intro Z
    simp only [Matrix.mul_assoc]
    rw [hP, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]
  rw [← key X, h, key Y]

/-! ## 3. The characterisation -/

/-- The two products the characterisation compares, each as a conjugate of a product with the
propagator. -/
theorem conj_mul_diagonal (hm : m ≠ 0) (R : Matrix V V ℝ) :
    ((eigP G m hm)ᵀ * R * eigP G m hm) * diagonal (eigMu G m hm)
      = (eigP G m hm)ᵀ * (R * green G m) * eigP G m hm := by
  rw [← transpose_mul_green_mul_eigP (G := G) (m := m) hm]
  have hP := eigP_mul_transpose_self (G := G) (m := m) hm
  simp only [Matrix.mul_assoc]
  congr 1
  rw [← Matrix.mul_assoc (eigP G m hm), hP, Matrix.one_mul]

theorem diagonal_mul_conj (hm : m ≠ 0) (R : Matrix V V ℝ) :
    diagonal (eigMu G m hm) * ((eigP G m hm)ᵀ * R * eigP G m hm)
      = (eigP G m hm)ᵀ * (green G m * R) * eigP G m hm := by
  rw [← transpose_mul_green_mul_eigP (G := G) (m := m) hm]
  have hP := eigP_mul_transpose_self (G := G) (m := m) hm
  simp only [Matrix.mul_assoc]
  congr 2
  rw [← Matrix.mul_assoc (eigP G m hm), hP, Matrix.one_mul]

/-- **A MATRIX COMMUTES WITH THE PROPAGATOR EXACTLY WHEN ITS CONJUGATE BY THE EIGENVECTOR MATRIX
IS BLOCK DIAGONAL** — blocks indexed by the distinct eigenvalues. -/
theorem comm_iff_blockDiagonal (hm : m ≠ 0) (R : Matrix V V ℝ) :
    R * green G m = green G m * R ↔
      ∀ i j, eigMu G m hm i ≠ eigMu G m hm j →
        ((eigP G m hm)ᵀ * R * eigP G m hm) i j = 0 := by
  rw [← commutes_diagonal_iff, conj_mul_diagonal, diagonal_mul_conj]
  exact ⟨fun h => by rw [h], fun h => eq_of_conj_eq hm h⟩

/-- **THE CONJUGATE OF AN ORTHOGONAL MATRIX IS ORTHOGONAL**, so the blocks the previous theorem
isolates are themselves orthogonal — which is what makes the description a product of orthogonal
groups rather than of general linear ones. -/
theorem conj_transpose_mul_self (hm : m ≠ 0) {R : Matrix V V ℝ} (hR : Rᵀ * R = 1) :
    ((eigP G m hm)ᵀ * R * eigP G m hm)ᵀ * ((eigP G m hm)ᵀ * R * eigP G m hm) = 1 := by
  have hP := eigP_mul_transpose_self (G := G) (m := m) hm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (eigP G m hm) ((eigP G m hm)ᵀ), hP, Matrix.one_mul,
    ← Matrix.mul_assoc Rᵀ R, hR, Matrix.one_mul, eigP_transpose_mul_self]

/-- **THE SYMMETRY GROUP OF THE PROPAGATOR IS EXACTLY THE ORTHOGONAL BLOCK-DIAGONAL GROUP IN ITS
EIGENBASIS.** An orthogonal `R` is a symmetry iff its conjugate by the eigenvector matrix vanishes
at every pair of indices carrying different eigenvalues — and that conjugate is orthogonal by
`conj_transpose_mul_self`. This is the description `∏ᵢ O(dᵢ)`, stated without constructing the
product group: the blocks are the eigenvalue fibres and each carries an orthogonal matrix. -/
theorem mem_symmetryMatrices_iff_blockDiagonal (hm : m ≠ 0) {R : Matrix V V ℝ} :
    R ∈ symmetryMatrices G m ↔
      Rᵀ * R = 1 ∧ ∀ i j, eigMu G m hm i ≠ eigMu G m hm j →
        ((eigP G m hm)ᵀ * R * eigP G m hm) i j = 0 := by
  rw [symmetryMatrices, Set.mem_setOf_eq]
  exact and_congr_right fun _ => comm_iff_blockDiagonal hm R

/-- **THE BLOCK AT AN EIGENVALUE IS INDEXED BY ITS FIBRE**, whose size is the eigenvalue's
multiplicity as `Matrix.IsHermitian` counts it. Stated so that the two halves of the description
are joined by a lemma rather than by a reader. -/
theorem blockDiagonal_off_fibre (hm : m ≠ 0) {R : Matrix V V ℝ}
    (hR : R ∈ symmetryMatrices G m) {μ : ℝ} {i j : V}
    (hi : eigMu G m hm i = μ) (hj : eigMu G m hm j ≠ μ) :
    ((eigP G m hm)ᵀ * R * eigP G m hm) i j = 0 :=
  ((mem_symmetryMatrices_iff_blockDiagonal hm).1 hR).2 i j (by rw [hi]; exact fun h => hj h.symm)

end FieldBlockDiagonal
