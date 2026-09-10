import FieldBlockDiagonal
import FieldCycleRotation
import FieldSimpleCriterion

/-!
# The multiplicity of an eigenvalue is the size of its fibre

`FieldBlockDiagonal` proved that the symmetry group of the propagator is the orthogonal
block-diagonal group in its eigenbasis, with the blocks indexed by the **fibres** of
`Matrix.IsHermitian.eigenvalues`. Its own fence named what was missing before that reading is a
theorem: *that the fibre of `μ` has size equal to `finrank` of the `μ`-eigenspace is **not proved
here and is not in this estate***, and it is *what would join this description to
`TorusRealMultiplicity.finrank_eigenspace_massive_real` and `BoxEigenspaceDimension`'s fibre
counts*. **This file is that join.**

**The bridge, and it is not the obvious one.** Mathlib has the statement for **linear maps** —
`LinearMap.IsSymmetric.card_filter_eigenvalues_eq` — and reaching it from a matrix means going
through `toEuclideanLin`, the sorting permutation inside `eigenvalues₀`, and a reindexing of
`Fin (card V)` back to `V`. **None of that is used.** The route here is matrix algebra on the
diagonalisation the previous unit already built: `green = P · D · Pᵀ`, so
`green − μ·1 = P · diagonal(μᵢ − μ) · Pᵀ`; multiplying by an invertible matrix does not change
rank; the rank of a diagonal matrix is its number of non-zero entries; and rank-nullity turns that
into the kernel's dimension. Four library lemmas and no spectral theory.

**And then the estate's own counts are stated for the wrong matrix**, which is the second half of
the join. `TorusRealMultiplicity` and `BoxEigenspaceDimension` count eigenspaces of `massive`, and
`FieldBlockDiagonal`'s blocks are fibres of `green`'s eigenvalues. The two eigenspaces are **the
same submodule** (`ker_massive_sub_eq_ker_green_sub`) — not merely of equal dimension — because an
eigenvector of `massive` at `μ ≠ 0` is an eigenvector of `green` at `μ⁻¹` and back again, and both
transfers were already in the estate (`FieldSignReflection.green_mulVec_of_massive_mulVec`,
`FieldSimpleCriterion.massive_mulVec_of_green_mulVec`).

## What is proved

**`finrank_ker_toLin'`** — rank-nullity for a square matrix, in the form the count needs: the
kernel's dimension is `card V − rank`.

**`isUnit_det_eigP`** — the eigenvector matrix has non-zero determinant, from `P Pᵀ = 1`.

**`green_eq_conj_diagonal`, `green_sub_smul_eq_conj`** — `green = P D Pᵀ` and
`green − μ·1 = P · diagonal(μᵢ − μ) · Pᵀ`.

**`rank_green_sub_smul`** — the rank of the shifted propagator is the number of eigenvalues away
from `μ`.

**`finrank_eigenspace_eq_card_fibre`** — **THE MULTIPLICITY OF AN EIGENVALUE OF THE PROPAGATOR IS
THE SIZE OF ITS FIBRE**, for the eigenspace `ker (toLin' green − μ · id)` the estate's other
multiplicity results use.

**`ker_massive_sub_eq_ker_green_sub`, `finrank_eigenspace_massive_eq_card_fibre`** — the same
statement for `massive`, which is the matrix the torus's and the box's counts are about. **This is
the join `FieldBlockDiagonal`'s fence asked for.**

## What is NOT here

**NO GROUP ISOMORPHISM, SO THE COUNT ITEM IS STILL NOT CLOSED.** `FieldBlockDiagonal` gives a test
for membership and this file gives the block sizes; together they say the symmetry group is
`∏ᵢ O(dᵢ)` with the `dᵢ` identified, but **no `symmetryMatrices ≃* ∏ᵢ O(dᵢ)` is constructed** —
that still needs the distinct eigenvalues as a quotient index type and two homomorphisms, and none
of the three is written. **Not attempted, no cost claimed** (`ERRATUM 246`).
[⚠ **NOW CONSTRUCTED, and the sentence is kept as written** (`ERRATUM 94`, 10 SEP 2026):
`FieldBlockProduct.symmetry_mulEquiv_prod`. All three pieces this paragraph named exist — the index
type is `Set.range (eigMu G m hm)` rather than a quotient, which serves the same purpose and is
finite because `V` is; the assembly is `Matrix.blockDiagonal'` through
`Equiv.sigmaSubtypeFiberEquiv`; and the homomorphism is a `MulEquiv` in both directions.
**THIS FILE'S OWN THEOREM IS WHAT MAKES THE FACTORS MEAN ANYTHING**:
`FieldBlockProduct.card_fib_eq_finrank_eigenspace` is `finrank_eigenspace_eq_card_fibre` read at a
level of the product, so the factor at `μ` is the orthogonal group of a space of dimension `μ`'s
multiplicity. The `NO NUMBER` paragraph below stands unchanged.]

**NO NUMBER, AND THERE IS NOT GOING TO BE ONE.** `∏ᵢ O(dᵢ)` is infinite as soon as some `dᵢ ≥ 2`,
and `FieldTorusRotation.oneFreq` says the torus is degenerate in every dimension. So
`FieldTorusRotation.infinite_symmetryMatrices_torus` remains the finest cardinality statement, and
that is the right answer rather than a missing one.

**NO SPECTRAL THEORY, AND SO NO SORTING.** The eigenvalue function here is Mathlib's
`Matrix.IsHermitian.eigenvalues`, whose ordering is an artefact of `eigenvalues₀`'s sort. Nothing
in this file depends on that order — the statements are about fibres, which are order-blind — and
nothing here relates the fibres to `Polynomial.rootMultiplicity` of the characteristic polynomial,
which is the other standard notion of multiplicity and is absent from this estate.

**NO GRAPH IS NAMED.** Every statement is at an arbitrary finite `SimpleGraph` with `m ≠ 0`. The
degeneracies that make the multiplicities interesting are the torus's and the box's, and they are
elsewhere; what is added here is that their counts and this chain's blocks are the same numbers.

**NO WALL MOVES.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a `Fintype V` with `DecidableEq V`, a
`SimpleGraph V` with `DecidableRel G.Adj`, a real mass `m` with `hm : m ≠ 0` wherever the
propagator appears, and `hμ : μ ≠ 0` on the two `massive` statements — the last because the
inversion `μ ↦ μ⁻¹` is what relates the two matrices' eigenvalues and it needs `μ` away from zero.
`finrank_ker_toLin'` takes none of them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldEigenMultiplicity

open Matrix GraphLaplacian FieldBlockDiagonal
open FieldCycleRotation (mem_eigenspace_iff_mulVec)

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Two facts with no graph in them -/

/-- **RANK-NULLITY FOR A SQUARE MATRIX**, in the form the eigenspace count needs. -/
theorem finrank_ker_toLin' (A : Matrix V V ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' A)) = Fintype.card V - A.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hr : (Matrix.toLin' A) = A.mulVecLin := rfl
  rw [Matrix.rank, ← hr]
  omega

/-- The eigenvector matrix has unit determinant, because `Pᵀ P = 1`. -/
theorem isUnit_det_eigP (hm : m ≠ 0) : IsUnit (eigP G m hm).det := by
  have h : (eigP G m hm).det * ((eigP G m hm)ᵀ).det = 1 := by
    rw [← Matrix.det_mul, eigP_mul_transpose_self (G := G) (m := m) hm, Matrix.det_one]
  rw [isUnit_iff_ne_zero]
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-! ## 2. The propagator, shifted and diagonalised -/

/-- **`green = P D Pᵀ`**. -/
theorem green_eq_conj_diagonal (hm : m ≠ 0) :
    green G m = eigP G m hm * diagonal (eigMu G m hm) * (eigP G m hm)ᵀ := by
  rw [← green_mul_eigP, Matrix.mul_assoc, eigP_mul_transpose_self, Matrix.mul_one]

/-- **`green − μ·1 = P (D − μ·1) Pᵀ`**, with the shifted diagonal written out. -/
theorem green_sub_smul_eq_conj (hm : m ≠ 0) (μ : ℝ) :
    green G m - μ • (1 : Matrix V V ℝ)
      = eigP G m hm * diagonal (fun i => eigMu G m hm i - μ) * (eigP G m hm)ᵀ := by
  have hd : (diagonal fun i => eigMu G m hm i - μ)
      = diagonal (eigMu G m hm) - μ • (1 : Matrix V V ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    · simp [Matrix.one_apply_ne h, h]
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, green_eq_conj_diagonal hm]
  congr 1
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, eigP_mul_transpose_self]

/-! ## 3. The count -/

/-- **THE RANK OF THE SHIFTED PROPAGATOR IS THE NUMBER OF EIGENVALUES AWAY FROM `μ`.** -/
theorem rank_green_sub_smul (hm : m ≠ 0) (μ : ℝ) :
    (green G m - μ • (1 : Matrix V V ℝ)).rank
      = Fintype.card {i : V // eigMu G m hm i ≠ μ} := by
  rw [green_sub_smul_eq_conj hm μ,
    Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (by rw [Matrix.det_transpose]; exact isUnit_det_eigP hm),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (isUnit_det_eigP hm),
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight fun i => by simp [sub_eq_zero])

/-- **THE MULTIPLICITY OF AN EIGENVALUE IS THE SIZE OF ITS FIBRE.** The eigenspace the estate's
multiplicity results use — `ker (toLin' green − μ · id)` — has dimension exactly the number of
indices at which `Matrix.IsHermitian.eigenvalues` takes the value `μ`. **This is the bridge from
`FieldBlockDiagonal`'s blocks to the multiplicities.** -/
theorem finrank_eigenspace_eq_card_fibre (hm : m ≠ 0) (μ : ℝ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (green G m) - μ • LinearMap.id))
      = Fintype.card {i : V // eigMu G m hm i = μ} := by
  have hlin : (Matrix.toLin' (green G m) - μ • LinearMap.id)
      = Matrix.toLin' (green G m - μ • (1 : Matrix V V ℝ)) := by
    rw [map_sub]
    congr 1
    ext x i
    simp
  rw [hlin, finrank_ker_toLin', rank_green_sub_smul hm μ]
  have hcompl : Fintype.card {i : V // eigMu G m hm i ≠ μ}
      = Fintype.card V - Fintype.card {i : V // eigMu G m hm i = μ} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i : V // eigMu G m hm i = μ} ≤ Fintype.card V :=
    Fintype.card_subtype_le _
  omega

/-! ## 4. Joining it to the estate's multiplicity counts, which are stated for `massive` -/

/-- **THE TWO EIGENSPACES ARE THE SAME SUBMODULE.** An eigenvector of `massive` at `μ ≠ 0` is an
eigenvector of `green` at `μ⁻¹` and back again, so the kernels coincide — not merely have equal
dimension. Both transfers are the estate's own
(`FieldSignReflection.green_mulVec_of_massive_mulVec` and
`FieldSimpleCriterion.massive_mulVec_of_green_mulVec`). -/
theorem ker_massive_sub_eq_ker_green_sub (hm : m ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    LinearMap.ker (Matrix.toLin' (massive G m) - μ • LinearMap.id)
      = LinearMap.ker (Matrix.toLin' (green G m) - μ⁻¹ • LinearMap.id) := by
  ext x
  rw [mem_eigenspace_iff_mulVec, mem_eigenspace_iff_mulVec]
  constructor
  · exact FieldSignReflection.green_mulVec_of_massive_mulVec hm hμ
  · intro h
    have := FieldSimpleCriterion.massive_mulVec_of_green_mulVec hm (inv_ne_zero hμ) h
    rwa [inv_inv] at this

/-- **THE MULTIPLICITY OF AN EIGENVALUE OF `massive` IS A FIBRE OF THE PROPAGATOR'S EIGENVALUE
FUNCTION.** This is the join the watchlist asked for: the estate's multiplicity results — the
torus's and the box's — are stated for `massive`, and `FieldBlockDiagonal`'s blocks are fibres of
`Matrix.IsHermitian.eigenvalues` of `green`. The two are the same number. -/
theorem finrank_eigenspace_massive_eq_card_fibre (hm : m ≠ 0) {μ : ℝ} (hμ : μ ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (massive G m) - μ • LinearMap.id))
      = Fintype.card {i : V // eigMu G m hm i = μ⁻¹} := by
  rw [ker_massive_sub_eq_ker_green_sub hm hμ, finrank_eigenspace_eq_card_fibre hm]

end FieldEigenMultiplicity
