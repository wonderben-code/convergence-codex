import FieldEigenMultiplicity

/-!
# The symmetry group is the block-diagonal orthogonal group, as an isomorphism

`FieldBlockDiagonal` characterised membership: an orthogonal matrix is a symmetry of the Gaussian
field **iff** its conjugate by the propagator's eigenvector matrix is block diagonal for the
eigenvalue partition. `FieldEigenMultiplicity` then identified each block's size with the
eigenvalue's multiplicity. Both files, and the `UNLOCK_WATCHLIST` item they answer, fenced the same
remaining thing: **a characterisation of membership is not a group isomorphism**, and the
`∏ᵢ O(dᵢ)` *packaging* — the word that item and `FieldReflectionCount`'s fence both used — was not
built. **This file builds it.**

**`conjEigEquiv` is a `MulEquiv`** from `FieldSymmetryGroup.symmetrySubmonoid G m` onto
`blockDiagSubmonoid (eigMu G m hm)`: conjugation by the eigenvector matrix carries the symmetries
onto the block-diagonal orthogonal matrices, multiplicatively, with the inverse conjugation as its
inverse. With `FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre` supplying the block sizes,
that is the product-of-orthogonal-groups description as a statement about groups rather than about
sets.

**The level function is abstract, and that is the design.** `blockDiagSubmonoid` takes any
`d : V → ℝ` and contains no graph, no propagator and no eigenvector matrix; the propagator's
eigenvalues enter only at the point of use, in `conjEigEquiv`'s type. So the block-diagonal group
is a general object about a partition of an index set, and the geometry is supplied to it.

**Why the bundling is a `Submonoid` and not a `Subgroup`.** `Matrix V V ℝ` is a monoid, so
`Submonoid` is what bundles here — the same choice `FieldSymmetryGroup.symmetrySubmonoid` and
`FieldSymmetryIso.linSym` make, and for the same reason. The group law is not missing: it is
`FieldSymmetryGroup`'s four lemmas, `transpose_mem` supplying inverses, and on the block-diagonal
side the transpose of a block-diagonal orthogonal matrix is one. **Carrying both into
`Matrix.orthogonalGroup` was tried and is recorded as `ERRATUM 484` — that abbreviation sits behind
a `local instance` whose lemmas Mathlib's own `TODO` questions, which `FieldSymmetryIso` had
already written down.**
⚠ **AND THE `Subgroup` ROUTE DOES EXIST IN THIS ESTATE, WHICH THIS PARAGRAPH SHOULD HAVE SAID**
(added 2026-09-10 by `RE-SWEEP #46`, `ERRATUM 94`): `FieldSymmetryInclusion.linSymGL` bundles the
**linear** symmetries as a `Subgroup` of `Matrix.GeneralLinearGroup V ℝ`, **taking no hypothesis on
the mass**, because the ambient group supplies the inverse. So the sentence above is right that
`Matrix V V ℝ` is only a monoid and wrong to leave the impression that no group bundling was
available: the route `FieldSymmetryGroup`'s own fence named — *carrying the symmetries into
`Matrix.GeneralLinearGroup`* — was taken for the sibling group on 6 September. **Doing the same for
`symmetryMatrices`, and upgrading `conjEigEquiv` to a `Subgroup` isomorphism, is not done here and
no cost is claimed for it** (`ERRATUM 246`).
[⚠ **BOTH ARE NOW DONE, AND NOT BY THE ROUTE THIS PARAGRAPH NAMED, and the sentence is kept as
written** (`ERRATUM 94`, 10 SEP 2026). `FieldSymmetrySubgroup.symmetrySubgroup` bundles
`symmetryMatrices` as a `Subgroup` — of **`Matrix.unitaryGroup V ℝ`**, not of
`Matrix.GeneralLinearGroup`, because every symmetry here is orthogonal and the orthogonal group is
the ambient it already sits in; `linSymGL` needs the bigger ambient precisely because a LINEAR
symmetry need not be orthogonal. `FieldSymmetrySubgroup.symmetrySubgroup_mulEquiv_prod` is the
`Subgroup` isomorphism, onto the product of the orthogonal groups of the eigenspaces via
`FieldBlockProduct`, so it upgrades `conjEigEquiv`'s target as well as its source. **The paragraph
was right that a group bundling was available and right about which fence it answered; it was wrong
only about which ambient group would be the one used.**]

**How this group sits inside `FieldSymmetryIso`'s, exactly.** `FieldSymmetryInclusion.
symmetryMatrices_eq` says `symmetryMatrices G m = {L | L ∈ linSym G m ∧ Lᵀ * L = 1}` — **the
isometric symmetries are precisely the orthogonal elements of the linear ones**, with no mass
hypothesis at all — and `FieldSymmetryProper.symmetryMatrices_eq_linSym_iff` makes the inclusion a
dichotomy: they coincide **iff** the propagator has a single eigenvalue, which
`FieldSymmetryEdgeless` reads off as **iff the graph has no edges**. So the two groups of the
*What is NOT here* section below are related by a theorem and not merely distinguished by a
sentence.

## What is proved

**`blockDiag_mul`** — a product of block-diagonal matrices is block diagonal: for each summand
index the level differs from the row's or from the column's, since it cannot equal both.

**`blockDiagSubmonoid`, `mem_blockDiagSubmonoid`** — the block-diagonal orthogonal matrices as a
`Submonoid`, for an abstract level function.

**`conjEig`, `unconjEig`, `unconjEig_conjEig`, `conjEig_unconjEig`, `conjEig_mul`** — conjugation
by the eigenvector matrix, its inverse, and multiplicativity.

**`conjEig_transpose_mul_self`, `unconjEig_transpose_mul_self`** — both conjugations preserve
orthogonality.

**`conjEigEquiv_forward_aux`, `conjEigEquiv_backward_aux`** — the two membership steps, each one
line from `FieldBlockDiagonal.comm_iff_blockDiagonal`.

**`conjEigEquiv`** — **THE ISOMORPHISM.** The symmetry group of the propagator is the
block-diagonal orthogonal group in its eigenbasis.

## What is NOT here

**NO LITERAL `∏ᵢ O(dᵢ)`.** The target is `blockDiagSubmonoid`, the matrices that are block
diagonal for the eigenvalue partition — **not** a dependent product `Π (μ : distinct eigenvalues),
Matrix.orthogonalGroup (fibre μ) ℝ`. Identifying the two needs the distinct eigenvalues as a
quotient index type and a `Matrix.blockDiagonal` over it, and neither is written. **What is proved
is the isomorphism onto the block-diagonal group; that this group *is* the product is the reading,
and the reading is not formalised.** **Not attempted, no cost claimed** (`ERRATUM 246`).
[⚠ **THE READING IS NOW FORMALISED AND THIS PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`,
10 SEP 2026): `FieldBlockProduct.blockProdEquiv` is `blockDiagSubmonoid d ≃* ∀ c : Lev d,
Matrix.unitaryGroup (Fib d c) ℝ`, the dependent product this paragraph describes, for an arbitrary
level function. The two things it named as missing are both there: the index type is
`Set.range d` — the levels actually ATTAINED, which is what makes every factor non-trivial
(`FieldBlockProduct.fib_nonempty`) — and the `Matrix.blockDiagonal` over it is
`Matrix.blockDiagonal'` reached through `Equiv.sigmaSubtypeFiberEquiv`. The target is
`Matrix.unitaryGroup` and not `Matrix.orthogonalGroup`, so `ERRATUM 484`'s trap is still avoided
and `FieldBlockProduct.mem_unitaryGroup_iff_transpose` proves the two agree over `ℝ`. The
`NO NUMBER` paragraph below stands unchanged.]

**NO NUMBER, AND THERE IS NOT GOING TO BE ONE.** A block-diagonal orthogonal group is infinite as
soon as one block has size two or more, and `FieldTorusRotation.oneFreq` says the torus is
degenerate in every dimension. `FieldTorusRotation.infinite_symmetryMatrices_torus` remains the
finest cardinality statement and is the right answer rather than a missing one.

**THIS IS NOT `FieldSymmetryIso`'s GROUP, AND THE DIFFERENCE MATTERS.**
`FieldSymmetryIso.conjSqEquiv` proves the **linear** symmetry group — matrices with
`L · green · Lᵀ = green`, orthogonality not required — is isomorphic to the **full** orthogonal
group of `ℝ^V`, at every graph and every non-zero mass. This file's group is the **isometric**
symmetries, the orthogonal matrices commuting with the propagator, which is a proper subgroup in
general and is the block-diagonal one. **An estate holding both statements needs a reader to know
which is which**, and neither supersedes the other.

**NO GRAPH IS NAMED**, and no `OS` axiom is touched. **NO WALL MOVES**: `W1`'s open part is `OS0`
and `OS4`, and `OS1` in its continuum sense. An exact description of a finite-volume symmetry
group is a wider shadow of an axiom, not a smaller gap in it.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a `Fintype V` with `DecidableEq V`, a
`SimpleGraph V` with `DecidableRel G.Adj`, a real mass `m`, and `hm : m ≠ 0` on everything that
mentions the propagator — the eigenvector matrix existing only because `green` is positive
definite, hence Hermitian, away from zero mass. `blockDiag_mul` takes none of them, and
`blockDiagSubmonoid` takes only the index type.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldBlockGroup

open Matrix GraphLaplacian FieldRotationCount FieldBlockDiagonal FieldSymmetryGroup

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The block-diagonal orthogonal matrices, for an abstract level function -/

omit [DecidableEq V] in
/-- **A PRODUCT OF BLOCK-DIAGONAL MATRICES IS BLOCK DIAGONAL.** For each summand index `k` the
level at `k` differs from that at `i` or from that at `j`, because it cannot equal both. -/
theorem blockDiag_mul {d : V → ℝ} {M N : Matrix V V ℝ}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) (hN : ∀ i j, d i ≠ d j → N i j = 0) :
    ∀ i j, d i ≠ d j → (M * N) i j = 0 := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : d i = d k
  · rw [hN k j (by rw [← hik]; exact hij), mul_zero]
  · rw [hM i k hik, zero_mul]

/-- **THE BLOCK-DIAGONAL ORTHOGONAL MATRICES ARE A SUBMONOID**, for any level function
`d : V → ℝ`. No graph, no propagator and no eigenvector matrix appears here: the propagator's
eigenvalues are supplied only where this is used. -/
def blockDiagSubmonoid (d : V → ℝ) : Submonoid (Matrix V V ℝ) where
  carrier := {M | Mᵀ * M = 1 ∧ ∀ i j, d i ≠ d j → M i j = 0}
  mul_mem' := by
    intro M N hM hN
    refine ⟨?_, blockDiag_mul hM.2 hN.2⟩
    rw [Matrix.transpose_mul]
    calc Nᵀ * Mᵀ * (M * N) = Nᵀ * (Mᵀ * M) * N := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM.1, Matrix.mul_one, hN.1]
  one_mem' := by
    refine ⟨by rw [Matrix.transpose_one, Matrix.one_mul], fun i j hij => ?_⟩
    exact Matrix.one_apply_ne fun h => hij (by rw [h])

@[simp] theorem mem_blockDiagSubmonoid {d : V → ℝ} {M : Matrix V V ℝ} :
    M ∈ blockDiagSubmonoid d ↔ Mᵀ * M = 1 ∧ ∀ i j, d i ≠ d j → M i j = 0 := Iff.rfl

/-! ## 2. Conjugation by the eigenvector matrix -/

/-- Conjugation by the propagator's eigenvector matrix. -/
noncomputable def conjEig (hm : m ≠ 0) (R : Matrix V V ℝ) : Matrix V V ℝ :=
  (eigP G m hm)ᵀ * R * eigP G m hm

/-- The inverse conjugation. -/
noncomputable def unconjEig (hm : m ≠ 0) (M : Matrix V V ℝ) : Matrix V V ℝ :=
  eigP G m hm * M * (eigP G m hm)ᵀ

theorem unconjEig_conjEig (hm : m ≠ 0) (R : Matrix V V ℝ) :
    unconjEig (G := G) hm (conjEig (G := G) hm R) = R := by
  have hP := eigP_mul_transpose_self (G := G) (m := m) hm
  simp only [unconjEig, conjEig, Matrix.mul_assoc]
  rw [hP, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem conjEig_unconjEig (hm : m ≠ 0) (M : Matrix V V ℝ) :
    conjEig (G := G) hm (unconjEig (G := G) hm M) = M := by
  have hP := eigP_transpose_mul_self (G := G) (m := m) hm
  simp only [unconjEig, conjEig, Matrix.mul_assoc]
  rw [hP, Matrix.mul_one, ← Matrix.mul_assoc, hP, Matrix.one_mul]

theorem conjEig_mul (hm : m ≠ 0) (R S : Matrix V V ℝ) :
    conjEig (G := G) hm (R * S) = conjEig (G := G) hm R * conjEig (G := G) hm S := by
  have hP := eigP_mul_transpose_self (G := G) (m := m) hm
  simp only [conjEig, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (eigP G m hm) ((eigP G m hm)ᵀ), hP, Matrix.one_mul]

/-- Conjugation preserves orthogonality, in the direction that lands in the block-diagonal side. -/
theorem conjEig_transpose_mul_self (hm : m ≠ 0) {R : Matrix V V ℝ} (hR : Rᵀ * R = 1) :
    (conjEig (G := G) hm R)ᵀ * conjEig (G := G) hm R = 1 :=
  conj_transpose_mul_self hm hR

/-- And in the other direction. -/
theorem unconjEig_transpose_mul_self (hm : m ≠ 0) {M : Matrix V V ℝ} (hM : Mᵀ * M = 1) :
    (unconjEig (G := G) hm M)ᵀ * unconjEig (G := G) hm M = 1 := by
  have hPt := eigP_transpose_mul_self (G := G) (m := m) hm
  have hP := eigP_mul_transpose_self (G := G) (m := m) hm
  rw [unconjEig, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((eigP G m hm)ᵀ) (eigP G m hm), hPt, Matrix.one_mul,
    ← Matrix.mul_assoc Mᵀ M, hM, Matrix.one_mul, hP]

/-- Forward membership: a symmetry conjugates to a block-diagonal orthogonal matrix. -/
theorem conjEigEquiv_forward_aux (hm : m ≠ 0) {R : Matrix V V ℝ}
    (hR : R ∈ symmetryMatrices G m) :
    conjEig (G := G) hm R ∈ blockDiagSubmonoid (eigMu G m hm) :=
  ⟨conjEig_transpose_mul_self hm hR.1, (comm_iff_blockDiagonal hm R).1 hR.2⟩

/-- Backward membership: a block-diagonal orthogonal matrix unconjugates to a symmetry. -/
theorem conjEigEquiv_backward_aux (hm : m ≠ 0) {M : Matrix V V ℝ}
    (hM : M ∈ blockDiagSubmonoid (eigMu G m hm)) :
    unconjEig (G := G) hm M ∈ symmetryMatrices G m := by
  refine ⟨unconjEig_transpose_mul_self hm hM.1, ?_⟩
  refine (comm_iff_blockDiagonal hm _).2 ?_
  rw [← conjEig, conjEig_unconjEig (G := G) hm M]
  exact hM.2

/-! ## 3. The packaging -/

/-- **THE SYMMETRY GROUP OF THE PROPAGATOR IS THE BLOCK-DIAGONAL ORTHOGONAL GROUP, AS A
MULTIPLICATIVE ISOMORPHISM.** Conjugation by the eigenvector matrix is a `MulEquiv` from the
estate's `FieldSymmetryGroup.symmetrySubmonoid` onto `blockDiagSubmonoid` at the propagator's
eigenvalue function. Together with `FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre`,
which makes each block's size the eigenvalue's multiplicity, this is the `∏ᵢ O(dᵢ)` packaging the
watchlist has asked for since the count was made. -/
noncomputable def conjEigEquiv (hm : m ≠ 0) :
    symmetrySubmonoid G m ≃* blockDiagSubmonoid (eigMu G m hm) where
  toFun R := ⟨conjEig (G := G) hm R.1,
    conjEigEquiv_forward_aux hm R.2⟩
  invFun M := ⟨unconjEig (G := G) hm M.1,
    conjEigEquiv_backward_aux hm M.2⟩
  left_inv R := Subtype.ext (unconjEig_conjEig (G := G) hm R.1)
  right_inv M := Subtype.ext (conjEig_unconjEig (G := G) hm M.1)
  map_mul' R S := Subtype.ext (conjEig_mul (G := G) hm R.1 S.1)

end FieldBlockGroup
