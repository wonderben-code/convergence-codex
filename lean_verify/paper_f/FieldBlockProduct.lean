import FieldBlockGroup

/-!
# The block-diagonal orthogonal group is literally a product of orthogonal groups

`FieldBlockGroup` built `conjEigEquiv`, a `MulEquiv` from the Gaussian field's symmetry monoid onto
`blockDiagSubmonoid (eigMu G m hm)` — the orthogonal matrices that vanish between distinct
eigenvalue levels. Its header fenced the remaining step in the words the `UNLOCK_WATCHLIST` item
uses: **no literal `∏ᵢ O(dᵢ)`** — the target was the block-diagonal matrices, not a dependent
product over the distinct levels, and identifying the two *needs a quotient index type and a
`Matrix.blockDiagonal` over it, neither written, so the product reading is a reading and is not
formalised*. **This file writes it.**

**`blockProdEquiv` is a `MulEquiv`** from `blockDiagSubmonoid d`, for any level function
`d : V → ℝ`, onto `∀ c : Lev d, Matrix.unitaryGroup (Fib d c) ℝ` — the dependent product, over the
DISTINCT values of `d`, of the orthogonal groups of the fibres. Composed with `conjEigEquiv` that
is the product decomposition of the symmetry group itself (`symmetry_mulEquiv_prod`), with the
fibres identified as eigenvalue multiplicities by `FieldEigenMultiplicity`.

## What carries it

The index type is `Lev d := Set.range d`, the distinct levels, which is finite because `V` is —
`Set.range` carries no `Fintype` instance in Mathlib and one is supplied here. The reindexing is
`Equiv.sigmaSubtypeFiberEquiv`, which splits `V` as `Σ c : Lev d, Fib d c` precisely because every
value of `d` is in its own range, and `Matrix.reindexAlgEquiv` carries that to an algebra
equivalence of matrix rings. **The index of the sigma is `Lev d` and not `ℝ`, which is what makes
this possible at all**: `Matrix.blockDiagonal'RingHom` needs a `Fintype` index, `ℝ` is not one, and
the range is.

## What is NOT here

* **No cardinality, and there cannot be one.** A block-diagonal orthogonal group is infinite as
  soon as a block has size two, which `FieldTorusRotation.oneFreq` says the torus always does.
  This is a description, not a count.
* **`Matrix.unitaryGroup _ ℝ` is the orthogonal group and the file says so rather than using
  `Matrix.orthogonalGroup`**, which `ERRATUM 484` records as a trap: it is an `abbrev` behind a
  local `starRingOfComm` instance whose lemmas Mathlib's own `TODO` questions. `star_eq_transpose`
  is the bridge and it is used, not assumed.
* **No `Subgroup` of `GeneralLinearGroup`.** `FieldSymmetryInclusion.linSymGL` takes that route for
  the LINEAR symmetries and it is not taken here; the target monoid is a product of `unitary`
  submonoids, and every factor is a group, but no `Subgroup` instance is built.
* **The empty fibres are not excluded and do not need to be.** Every `c : Lev d` is attained, so
  every fibre is nonempty — that is what indexing by the range buys, and it is why the product has
  one factor per distinct eigenvalue rather than one per real number.
* **Nothing about which graphs give which block sizes.** The decomposition is stated for an
  arbitrary `d`; the eigenvalue multiplicities are `FieldEigenMultiplicity`'s and are not restated.

**No wall moves.** `W1`'s open part is still `OS0`, `OS4` and `OS1` in its continuum sense. Knowing
the finite-volume symmetry group as a product of orthogonal groups is a shadow known exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[Fintype V]` and `[DecidableEq V]`
throughout, and **no declaration in §§1–3 takes a mass, a graph or a propagator** — they are
statements about an arbitrary `d : V → ℝ`. Only §4 takes `m ≠ 0`, and only because `conjEigEquiv`
and `eigMu` do.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldBlockProduct

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The distinct levels, the fibres, and the splitting of `V` -/

/-- The distinct values of the level function: the index of the product. -/
abbrev Lev (d : V → ℝ) := Set.range d

/-- The fibre of the level function over a value. -/
abbrev Fib (d : V → ℝ) (c : ℝ) := {i : V // d i = c}

/-- `Set.range` carries no `Fintype` instance in Mathlib, and the product needs one because
`Matrix.blockDiagonal'` is indexed by a `Fintype`. The range of a map out of a finite type is
finite, so this is `Set.Finite.fintype` and nothing more.

**IT IS DELIBERATELY `scoped`.** Mathlib's omission is not an oversight: the instance is
noncomputable and its head `Fintype ↥(Set.range ?f)` would fire on every range in scope, so making
it global from a paper file would change instance search estate-wide for a convenience one file
needs. Every constant below has it baked into its body, so nothing downstream has to re-synthesize
it to USE `blockProdEquiv`; a file that wants to prove WITH `splitAlg` gets it by opening this
namespace, which is a decision that file makes rather than one this one makes for it. -/
noncomputable scoped instance instFintypeLev (d : V → ℝ) : Fintype (Lev d) :=
  (Set.finite_range d).fintype

/-- The level of an index, as an element of the range. -/
def lev (d : V → ℝ) (i : V) : Lev d := ⟨d i, ⟨i, rfl⟩⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem lev_val (d : V → ℝ) (i : V) : ((lev d i : Lev d) : ℝ) = d i := rfl

/-- **`V` SPLITS AS THE DISJOINT UNION OF THE FIBRES OVER THE DISTINCT LEVELS.** This is
`Equiv.sigmaSubtypeFiberEquiv`, whose hypothesis is that every value of `d` lies in the predicate
— here, in `d`'s own range, which is `rfl`. -/
def sigmaLevEquiv (d : V → ℝ) : (Σ c : Lev d, Fib d (c : ℝ)) ≃ V :=
  Equiv.sigmaSubtypeFiberEquiv d (· ∈ Set.range d) fun x => ⟨x, rfl⟩

omit [Fintype V] [DecidableEq V] in
@[simp] theorem sigmaLevEquiv_apply (d : V → ℝ) (x : Σ c : Lev d, Fib d (c : ℝ)) :
    sigmaLevEquiv d x = x.2.1 := rfl

omit [Fintype V] [DecidableEq V] in
@[simp] theorem sigmaLevEquiv_symm_apply (d : V → ℝ) (i : V) :
    (sigmaLevEquiv d).symm i = ⟨lev d i, ⟨i, rfl⟩⟩ := rfl

omit [Fintype V] [DecidableEq V] in
/-- **EVERY FACTOR OF THE PRODUCT IS THE ORTHOGONAL GROUP OF A NONEMPTY SPACE.** Indexing by the
RANGE rather than by `ℝ` is what buys this: there is one factor per level actually attained, and no
trivial padding. It is the check against a product that is a product only formally. -/
theorem fib_nonempty (d : V → ℝ) (c : Lev d) : Nonempty (Fib d (c : ℝ)) :=
  ⟨⟨c.2.choose, c.2.choose_spec⟩⟩

/-! ## 2. Matrices on the split index, and block diagonality transported -/

/-- **THE MATRIX RING OF `V` IS THE MATRIX RING OF THE SPLIT INDEX**, as an algebra equivalence.
`Matrix.reindexAlgEquiv` needs both index types to be finite with decidable equality, and the sigma
is finite because `Lev d` is — which is the whole reason the index of the product is the RANGE of
`d` and not `ℝ`. -/
noncomputable def splitAlg (d : V → ℝ) :
    Matrix (Σ c : Lev d, Fib d (c : ℝ)) (Σ c : Lev d, Fib d (c : ℝ)) ℝ ≃ₐ[ℝ] Matrix V V ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (sigmaLevEquiv d)

theorem splitAlg_symm_apply (d : V → ℝ) (M : Matrix V V ℝ)
    (x y : Σ c : Lev d, Fib d (c : ℝ)) : (splitAlg d).symm M x y = M x.2.1 y.2.1 := rfl

theorem splitAlg_apply (d : V → ℝ)
    (N : Matrix (Σ c : Lev d, Fib d (c : ℝ)) (Σ c : Lev d, Fib d (c : ℝ)) ℝ) (i j : V) :
    splitAlg d N i j = N ((sigmaLevEquiv d).symm i) ((sigmaLevEquiv d).symm j) := rfl

omit [Fintype V] [DecidableEq V] in
/-- Two indices sit in different blocks exactly when their levels differ. -/
theorem fst_ne_iff (d : V → ℝ) {x y : Σ c : Lev d, Fib d (c : ℝ)} :
    x.1 ≠ y.1 ↔ d x.2.1 ≠ d y.2.1 := by
  constructor
  · intro h hd
    exact h (Subtype.ext (by rw [← x.2.2, ← y.2.2, hd]))
  · intro h hc
    exact h (by rw [x.2.2, y.2.2, hc])

/-- **BLOCK DIAGONALITY IS THE SAME CONDITION ON EITHER INDEX.** On `V` it is *the entry vanishes
when the levels differ*; on the split index it is *the entry vanishes off the diagonal blocks*. -/
theorem offDiag_iff (d : V → ℝ) (M : Matrix V V ℝ) :
    (∀ x y : Σ c : Lev d, Fib d (c : ℝ), x.1 ≠ y.1 → (splitAlg d).symm M x y = 0)
      ↔ ∀ i j, d i ≠ d j → M i j = 0 := by
  constructor
  · intro h i j hij
    exact h ((sigmaLevEquiv d).symm i) ((sigmaLevEquiv d).symm j) ((fst_ne_iff d).2 hij)
  · intro h x y hxy
    exact h x.2.1 y.2.1 ((fst_ne_iff d).1 hxy)

omit [Fintype V] [DecidableEq V] in
/-- A matrix on the split index that vanishes off its diagonal blocks is the block-diagonal matrix
assembled from those blocks. Mathlib has the other round trip (`blockDiag'_blockDiagonal'`) and not
this one, which needs the hypothesis. -/
theorem blockDiagonal'_blockDiag' {d : V → ℝ}
    {N : Matrix (Σ c : Lev d, Fib d (c : ℝ)) (Σ c : Lev d, Fib d (c : ℝ)) ℝ}
    (h : ∀ x y, x.1 ≠ y.1 → N x y = 0) :
    Matrix.blockDiagonal' (Matrix.blockDiag' N) = N := by
  ext x y
  obtain ⟨c, i⟩ := x
  obtain ⟨c', j⟩ := y
  by_cases hc : c = c'
  · subst hc
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hc, h _ _ hc]

/-! ## 3. The product decomposition -/

/-- Assemble a matrix on `V` from one orthogonal block per distinct level. -/
noncomputable def ofBlocks (d : V → ℝ) (B : ∀ c : Lev d, Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ) :
    Matrix V V ℝ :=
  splitAlg d (Matrix.blockDiagonal' B)

theorem ofBlocks_one (d : V → ℝ) : ofBlocks d 1 = 1 := by
  rw [ofBlocks, Matrix.blockDiagonal'_one, map_one]

theorem ofBlocks_mul (d : V → ℝ)
    (B B' : ∀ c : Lev d, Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ) :
    ofBlocks d (B * B') = ofBlocks d B * ofBlocks d B' := by
  rw [ofBlocks, ofBlocks, ofBlocks, show B * B' = fun c => B c * B' c from rfl,
    Matrix.blockDiagonal'_mul, map_mul]

theorem ofBlocks_injective (d : V → ℝ) : Function.Injective (ofBlocks d) := by
  intro B B' h
  exact Matrix.blockDiagonal'_injective ((splitAlg d).injective h)

/-- Reindexing commutes with transposition, entrywise. -/
theorem splitAlg_transpose (d : V → ℝ)
    (N : Matrix (Σ c : Lev d, Fib d (c : ℝ)) (Σ c : Lev d, Fib d (c : ℝ)) ℝ) :
    splitAlg d Nᵀ = (splitAlg d N)ᵀ := rfl

theorem ofBlocks_transpose (d : V → ℝ)
    (B : ∀ c : Lev d, Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ) :
    (ofBlocks d B)ᵀ = ofBlocks d fun c => (B c)ᵀ := by
  rw [ofBlocks, ofBlocks, ← Matrix.blockDiagonal'_transpose, splitAlg_transpose]

/-- **THE BLOCKS OF AN ASSEMBLED MATRIX ARE THE BLOCKS IT WAS ASSEMBLED FROM.** -/
theorem blockDiag'_symm_ofBlocks (d : V → ℝ)
    (B : ∀ c : Lev d, Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ) :
    Matrix.blockDiag' ((splitAlg d).symm (ofBlocks d B)) = B := by
  rw [ofBlocks, AlgEquiv.symm_apply_apply]
  exact Matrix.blockDiag'_blockDiagonal' B

/-- An assembled matrix is block diagonal. -/
theorem ofBlocks_blockDiag (d : V → ℝ)
    (B : ∀ c : Lev d, Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ) :
    ∀ i j, d i ≠ d j → ofBlocks d B i j = 0 := by
  refine (offDiag_iff d _).1 ?_
  intro x y hxy
  rw [ofBlocks, AlgEquiv.symm_apply_apply]
  exact Matrix.blockDiagonal'_apply_ne _ _ _ hxy

/-- **AND EVERY BLOCK-DIAGONAL MATRIX IS ASSEMBLED FROM ITS OWN BLOCKS.** -/
theorem ofBlocks_blockDiag' (d : V → ℝ) {M : Matrix V V ℝ}
    (hM : ∀ i j, d i ≠ d j → M i j = 0) :
    ofBlocks d (Matrix.blockDiag' ((splitAlg d).symm M)) = M := by
  rw [ofBlocks, blockDiagonal'_blockDiag' ((offDiag_iff d M).2 hM), AlgEquiv.apply_symm_apply]

theorem ofBlocks_orthogonal_iff (d : V → ℝ)
    (B : ∀ c : Lev d, Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ) :
    (ofBlocks d B)ᵀ * ofBlocks d B = 1 ↔ ∀ c, (B c)ᵀ * B c = 1 := by
  rw [ofBlocks_transpose, ← ofBlocks_mul, ← ofBlocks_one d, (ofBlocks_injective d).eq_iff]
  exact ⟨fun h c => congrFun h c, fun h => funext h⟩

/-- Over `ℝ` the star is the transpose, so `Matrix.unitaryGroup` IS the orthogonal group. Stated
rather than assumed, because `Matrix.orthogonalGroup` is the trap `ERRATUM 484` records. -/
theorem mem_unitaryGroup_iff_transpose {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : A ∈ Matrix.unitaryGroup n ℝ ↔ Aᵀ * A = 1 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **THE PRODUCT OF THE ORTHOGONAL GROUPS OF THE FIBRES IS THE BLOCK-DIAGONAL ORTHOGONAL
MONOID.** One factor per DISTINCT level, and the isomorphism is *assemble the blocks*. -/
noncomputable def prodBlockEquiv (d : V → ℝ) :
    (∀ c : Lev d, Matrix.unitaryGroup (Fib d (c : ℝ)) ℝ) ≃*
      FieldBlockGroup.blockDiagSubmonoid d where
  toFun B := ⟨ofBlocks d fun c => (B c : Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ),
    (ofBlocks_orthogonal_iff d _).2 (fun c => (mem_unitaryGroup_iff_transpose _).1 (B c).2),
    ofBlocks_blockDiag d _⟩
  invFun M c := ⟨Matrix.blockDiag' ((splitAlg d).symm M.1) c, by
    refine (mem_unitaryGroup_iff_transpose _).2 ?_
    refine (ofBlocks_orthogonal_iff d _).1 ?_ c
    rw [ofBlocks_blockDiag' d M.2.2]
    exact M.2.1⟩
  left_inv B := by
    funext c
    exact Subtype.ext (congrFun (blockDiag'_symm_ofBlocks d _) c)
  right_inv M := Subtype.ext (ofBlocks_blockDiag' d M.2.2)
  map_mul' B B' := Subtype.ext (ofBlocks_mul d _ _)

/-- **THE BLOCK-DIAGONAL ORTHOGONAL MONOID IS A PRODUCT OF ORTHOGONAL GROUPS, ONE PER DISTINCT
LEVEL.** This is the `∏ᵢ O(dᵢ)` that `FieldBlockGroup`'s header, `FieldReflectionCount`'s fence and
the `UNLOCK_WATCHLIST` item all named as a reading rather than a theorem. -/
noncomputable def blockProdEquiv (d : V → ℝ) :
    FieldBlockGroup.blockDiagSubmonoid d ≃*
      ∀ c : Lev d, Matrix.unitaryGroup (Fib d (c : ℝ)) ℝ :=
  (prodBlockEquiv d).symm

@[simp] theorem blockProdEquiv_symm_apply_coe (d : V → ℝ)
    (B : ∀ c : Lev d, Matrix.unitaryGroup (Fib d (c : ℝ)) ℝ) :
    (((blockProdEquiv d).symm B : FieldBlockGroup.blockDiagSubmonoid d) : Matrix V V ℝ)
      = ofBlocks d fun c => (B c : Matrix (Fib d (c : ℝ)) (Fib d (c : ℝ)) ℝ) := rfl

/-! ## 4. The symmetry group of the Gaussian field, as a product of orthogonal groups -/

section Field

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

open GraphLaplacian FieldBlockDiagonal FieldBlockGroup FieldSymmetryGroup

/-- **THE FACTOR AT AN EIGENVALUE IS THE ORTHOGONAL GROUP OF A SPACE WHOSE DIMENSION IS THAT
EIGENVALUE'S MULTIPLICITY.** The index type of the factor at `c` is not merely equinumerous with
the eigenspace — it is literally the type `FieldEigenMultiplicity` counts, so this is that file's
theorem read at a level of the product rather than a new computation. -/
theorem card_fib_eq_finrank_eigenspace (hm : m ≠ 0) (c : Lev (eigMu G m hm)) :
    Fintype.card (Fib (eigMu G m hm) (c : ℝ))
      = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (green G m) - (c : ℝ) • LinearMap.id)) :=
  (FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre hm _).symm

/-- **THE GAUSSIAN FIELD'S SYMMETRY MONOID IS A PRODUCT OF ORTHOGONAL GROUPS, ONE FOR EACH
DISTINCT EIGENVALUE OF THE PROPAGATOR**, the factor at an eigenvalue being the orthogonal group of
its fibre — whose dimension is that eigenvalue's multiplicity by the theorem just above. The
domain is `FieldRotationCount.symmetryMatrices`, the orthogonal matrices commuting with the
propagator, which `FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` shows are
exactly the orthogonal matrices whose induced map preserves the field. -/
noncomputable def symmetry_mulEquiv_prod (hm : m ≠ 0) :
    symmetrySubmonoid G m ≃*
      ∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ :=
  (conjEigEquiv (G := G) hm).trans (blockProdEquiv (eigMu G m hm))

end Field

end FieldBlockProduct
