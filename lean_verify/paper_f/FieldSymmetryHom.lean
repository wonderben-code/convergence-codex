import FieldSymmetryInclusion
import FieldSignGroup
import FieldSymmetryEdgeless
import FieldSymmetrySubgroup
import FieldSymmetryFinite

/-!
# The isometric symmetry group inside the linear one, as a homomorphism of GROUPS

**FOUR FILES OF THIS CHAIN FENCE THE SAME MISSING OBJECT, IN NEARLY THE SAME WORDS.**
`FieldSignGroup`, `FieldSymmetryInclusion`, `FieldSymmetryProper` and `FieldSymmetryEdgeless` each
record that `FieldSignGroup.symmetriesSubgroup` — the isometric symmetries as *linear isometry
equivalences* — and `FieldSymmetryInclusion.linSymGL` — the linear symmetries as a subgroup of
`GL V ℝ` — are group objects over different ambient types, and that **no homomorphism between them
is constructed**. This file constructs it. The `UNLOCK_WATCHLIST` item that has carried the clause
since 5 September names it as the whole of what is left there apart from an index and a cardinality,
and both of those are still open below.

**WHAT HAD TO BE PROVED RATHER THAN SUBSTITUTED, MEASURED BEFORE WRITING** — `ERRATUM 500`'s rule,
which found three missing steps and no blocker:

* **THE MATRIX OF AN ISOMETRY, AS A FUNCTION.** `FieldSymmetryIso.exists_matrix` already has the
  construction — the inverse of `Matrix.toEuclideanLin` at the underlying linear map — but it has it
  **inside an existential**, and a homomorphism needs a **function**. Lifting it out is `isoMat`,
  and it is the same move `FieldSymmetryIso` itself had to make for `invConj` when a `MulEquiv`
  needed a map rather than a witness.
* **THE MATRIX OF AN ISOMETRY IS ORTHOGONAL.** `FieldOrthIsometry` runs the other way — an
  orthogonal matrix to an isometry — and **nothing in this estate ran this way**.
  `transpose_mul_isoMat` is the inner-product argument on the estate's own
  `FieldOrthIsometry.inner_mv_transpose`: `⟪x, (MᵀM)y⟫ = ⟪Mx, My⟫ = ⟪Tx, Ty⟫ = ⟪x, y⟫`, with
  `LinearIsometryEquiv.inner_map_map` in the middle and `ext_inner_left` at the end.
* **A MATRIX IS DETERMINED BY ITS ACTION ON `EuclideanSpace`.** `eq_of_mv_eq`; not in this estate
  either, and one line from the injectivity of `Matrix.toEuclideanLin`.
* **AND NO STEP OF THAT NEEDS THE MASS.** Thirteen of the twenty-eight declarations here take no
  graph, no propagator and no mass — read from `#check`, not from the `variable` block. The mass
  enters exactly where the matrix has to land in `linSym`, through
  `FieldSymmetryIso.mem_linSym_iff_gaussianField_map`, whose reverse direction needs `green`
  invertible.

## What is proved

**`isoMat`, `isoMatHom`, `isoMatGL`** — the matrix of a linear isometry equivalence, multiplicative,
and bundled into `GL V ℝ` through `MonoidHom.toHomUnits`. No graph and no mass.

**`symHom`** — **THE HOMOMORPHISM THE FOUR FENCES NAME**: a group homomorphism
`symmetriesSubgroup G m →* linSymGL G m`, at any non-zero mass on any finite graph.

**`symHom_injective`**, **`symEquivRange`** — it is injective, so the isometric symmetry group
**is** a subgroup of the linear one and not merely mapped into it: `symEquivRange` is the
isomorphism onto its image.

**`mem_range_symHom_iff`** — **AND THE IMAGE IS EXACTLY THE ORTHOGONAL PART**: an element of
`linSymGL` is in the image iff its matrix lies in `FieldRotationCount.symmetryMatrices`. Both
directions are needed and the backward one is where `FieldOrthIsometry.orthIsometry` earns its keep.

**`range_symHom_eq_top_iff_no_adj`** — **THE DICHOTOMY, AT GROUP LEVEL**: the image is the **whole**
linear symmetry group **if and only if the graph has no edges**, which is
`FieldSymmetryEdgeless.symmetryMatrices_eq_linSym_iff_no_adj` transported through the range
characterisation. **`range_symHom_ne_top`** — so one edge makes it a proper subgroup, as a statement
about subgroups rather than about sets of matrices.

**`symmetriesEquiv`, `symmetriesMulEquiv`** — **AND THE TWO PACKAGINGS OF THE ISOMETRIC GROUP ARE
ONE GROUP**: the isometry equivalences of `FieldLineCount.symmetries` and the matrices of
`FieldRotationCount.symmetryMatrices` are in bijection, and
`FieldSymmetrySubgroup.symmetrySubgroup` is isomorphic to `symmetriesSubgroup` as a group. That is a
**second** fence — `FieldSymmetryFinite` states in its own words that *the criterion is about
matrices and the count is about isometries, and the two are not the same set*, and that saying
otherwise would need *the matrix-to-isometry correspondence shown injective*.

**`symmetriesMulEquivProd`** — so `FieldSymmetrySubgroup`'s product decomposition, one orthogonal
group per distinct propagator eigenvalue, is a statement about the group this estate **counts**.

**`card_symmetryMatrices`, `card_symmetryMatrices_of_finite`** — **THE SENTENCE
`FieldSymmetryFinite` SAYS IS NOT MADE THERE, MADE**: at a simple propagator spectrum, and
equivalently whenever the symmetry matrices are finite, there are exactly `2 ^ |V|` of them. That
file's `card_of_finite` concluded about the isometries from a hypothesis about the matrices, and its
fence says why the matrix count was not stated.

## What is NOT here

* **NO INDEX.** The four fences also say *no index*, and that is **unchanged**:
  `range_symHom_ne_top` says the subgroup is proper and **nothing here measures how much is
  missing**. Not attempted, no cost claimed (`ERRATUM 246`).
* **NO CARDINALITY ON THE LINEAR SIDE.** `FieldSymmetryIso.conjSqEquiv` moves that question onto
  Mathlib's `unitaryGroup`, which is not this estate's object, and nothing here touches it. The
  count made above is the **isometric** side, which is finite exactly when the spectrum is simple.
* **`[Nonempty V]` IS TAKEN BY THE DICHOTOMY AND BY NOTHING ELSE**, inherited from
  `FieldSymmetryEdgeless`, whose own header says the empty case is true for a `Subsingleton` reason
  nobody has written. The homomorphism, its injectivity and the range characterisation take no such
  hypothesis.
* **NOTHING AT `m = 0`.** Fifteen of the twenty-eight declarations take `m ≠ 0`, and every one of
  them needs it: `green` is invertible only there.
* **NOTHING IN THE CONTINUUM, AND NO WALL MOVES.** `W1`'s open part is still `OS0` and `OS4`, and
  `OS1` in its continuum sense. A symmetry group identified at group level in finite volume is a
  shadow named exactly.

**NO NAME IN THIS FILE DUPLICATES ONE IN THE ESTATE, AND THE NATURAL NAMES WOULD HAVE.** `mat`,
`mat_one` and `mat_mul` are `LorentzIdentityComponent`'s — for the same idea, the matrix of a group
element — checked with a grep before writing, so everything here is `isoMat*`. The estate already
cannot be loaded into a single Lean environment because of 28 such collisions (`PROGRESS_LOG`'s
`DECISIONS NEEDED` item 5) and this file adds none.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `V` a `Fintype` with `DecidableEq`, a
`SimpleGraph V` with `DecidableRel G.Adj` and a real `m`. `isoMat`, `isoMatHom`, `isoMatGL` and the
ten lemmas around them take **only the `V` instances** — no graph, no propagator, no mass — and
`eq_of_mv_eq` takes only `[Fintype V]`, the decidability being its proof's and not its statement's.
`m ≠ 0` is taken by fifteen declarations, `[Nonempty V]` by three, and **no declaration here assumes
a simple spectrum except the two counting theorems**, which take it in `FieldLineCount`'s form
(injectivity of the propagator's eigenvalue enumeration) or as finiteness of the matrix set.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldSymmetryHom

open Matrix GraphLaplacian RayleighMatrix FieldHouseholder FieldOrthIsometry
open FieldRotationCount FieldSymmetryIso FieldSymmetryInclusion FieldLinearClassified
open FieldLineCount FieldSignGroup FieldBlockDiagonal FieldBlockProduct
open scoped FieldBlockProduct

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The matrix of a linear isometry equivalence -/

noncomputable def isoMat (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) : Matrix V V ℝ :=
  Matrix.toEuclideanLin.symm T.toLinearEquiv.toLinearMap

@[simp] theorem mv_isoMat (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V)
    (x : EuclideanSpace ℝ V) : mv (isoMat T) x = T x := by
  change Matrix.toEuclideanLin (isoMat T) x = T x
  rw [isoMat, Matrix.toEuclideanLin.apply_symm_apply]
  rfl

omit [DecidableEq V] in
/-- A matrix is determined by its action on `EuclideanSpace ℝ V`. The `DecidableEq V` that
`Matrix.toEuclideanLin` needs is the proof's and not the statement's, so it is supplied by
`classical` rather than assumed. -/
theorem eq_of_mv_eq {A B : Matrix V V ℝ} (h : ∀ x, mv A x = mv B x) : A = B := by
  classical
  exact Matrix.toEuclideanLin.injective (LinearMap.ext fun x => h x)

theorem isoMat_eq {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V} {M : Matrix V V ℝ}
    (h : ∀ x, mv M x = T x) : isoMat T = M :=
  eq_of_mv_eq fun x => by rw [mv_isoMat]; exact (h x).symm

theorem isoMat_injective : Function.Injective
    (isoMat : (EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) → Matrix V V ℝ) := by
  intro T T' h
  refine LinearIsometryEquiv.ext fun x => ?_
  rw [← mv_isoMat T, ← mv_isoMat T', h]

@[simp] theorem isoMat_one :
    isoMat (1 : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) = 1 :=
  isoMat_eq fun x => by rw [mv_one]; simp

theorem isoMat_mul (T₁ T₂ : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    isoMat (T₁ * T₂) = isoMat T₁ * isoMat T₂ :=
  isoMat_eq fun x => by rw [mv_mul, mv_isoMat, mv_isoMat, LinearIsometryEquiv.coe_mul]; rfl

theorem transpose_mul_isoMat (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    (isoMat T)ᵀ * isoMat T = 1 := by
  refine eq_of_mv_eq fun y => ?_
  rw [mv_one]
  refine ext_inner_left ℝ fun x => ?_
  rw [mv_mul, ← inner_mv_transpose, mv_isoMat, mv_isoMat, T.inner_map_map]

theorem isoMat_orthIsometry {M : Matrix V V ℝ} (h : Mᵀ * M = 1) : isoMat (orthIsometry h) = M :=
  isoMat_eq fun _ => rfl

/-! ## 2. As a homomorphism of groups -/

noncomputable def isoMatHom :
    (EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) →* Matrix V V ℝ where
  toFun := isoMat
  map_one' := isoMat_one
  map_mul' := isoMat_mul

noncomputable def isoMatGL :
    (EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) →* GL V ℝ :=
  (isoMatHom (V := V)).toHomUnits

@[simp] theorem coe_isoMatGL (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    ((isoMatGL T : GL V ℝ) : Matrix V V ℝ) = isoMat T := rfl

theorem isoMat_mem_linSym (hm : m ≠ 0) {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : T ∈ symmetries G m) : isoMat T ∈ linSym G m := by
  refine (mem_linSym_iff_gaussianField_map hm).mpr ?_
  have hfun : ⇑(mvCLM (isoMat T)) = ⇑T := funext fun x => mv_isoMat T x
  rw [hfun]
  exact hT

noncomputable def symHom (hm : m ≠ 0) : symmetriesSubgroup G m →* linSymGL G m :=
  MonoidHom.codRestrict (isoMatGL.comp (symmetriesSubgroup G m).subtype) (linSymGL G m)
    (fun T => mem_linSymGL.mpr (by
      change isoMat (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) ∈ linSym G m
      exact isoMat_mem_linSym hm T.2))

@[simp] theorem coe_symHom (hm : m ≠ 0) (T : symmetriesSubgroup G m) :
    (((symHom hm T : linSymGL G m) : GL V ℝ) : Matrix V V ℝ)
      = isoMat (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) := rfl

theorem symHom_injective (hm : m ≠ 0) : Function.Injective (symHom (G := G) (m := m) hm) := by
  intro T T' h
  refine Subtype.ext (isoMat_injective ?_)
  rw [← coe_symHom hm T, ← coe_symHom hm T', h]

/-! ## 3. The image, and when it is everything -/

theorem mem_range_symHom_iff (hm : m ≠ 0) (U : linSymGL G m) :
    U ∈ (symHom (G := G) (m := m) hm).range ↔
      (((U : GL V ℝ) : Matrix V V ℝ)) ∈ symmetryMatrices G m := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨T, rfl⟩
    rw [symmetryMatrices_eq]
    exact ⟨by rw [coe_symHom]; exact isoMat_mem_linSym hm T.2,
      by rw [coe_symHom]; exact transpose_mul_isoMat _⟩
  · intro hU
    refine ⟨⟨orthIsometry hU.1, gaussianField_map_of_mem hm hU⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    rw [coe_symHom, isoMat_orthIsometry]

theorem symHom_surjective_iff_no_adj [Nonempty V] (hm : m ≠ 0) :
    Function.Surjective (symHom (G := G) (m := m) hm) ↔ ∀ i j, ¬ G.Adj i j := by
  rw [← FieldSymmetryEdgeless.symmetryMatrices_eq_linSym_iff_no_adj hm]
  constructor
  · intro hsurj
    refine Set.eq_of_subset_of_subset symmetryMatrices_subset_linSym fun L hL => ?_
    have hu : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (isUnit_det_of_mem_linSym hm hL)
    obtain ⟨T, hT⟩ := hsurj ⟨hu.unit, by rw [mem_linSymGL, hu.unit_spec]; exact hL⟩
    have hmat : isoMat (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) = L := by
      rw [← coe_symHom hm T, hT, hu.unit_spec]
    rw [symmetryMatrices_eq]
    exact ⟨hL, hmat ▸ transpose_mul_isoMat _⟩
  · intro heq U
    refine (mem_range_symHom_iff hm U).mpr ?_
    rw [heq]
    exact mem_linSymGL.mp U.2

noncomputable def symEquivRange (hm : m ≠ 0) :
    symmetriesSubgroup G m ≃* (symHom (G := G) (m := m) hm).range :=
  MonoidHom.ofInjective (symHom_injective hm)

theorem range_symHom_eq_top_iff_no_adj [Nonempty V] (hm : m ≠ 0) :
    (symHom (G := G) (m := m) hm).range = ⊤ ↔ ∀ i j, ¬ G.Adj i j := by
  rw [MonoidHom.range_eq_top, symHom_surjective_iff_no_adj]

theorem range_symHom_ne_top [Nonempty V] (hm : m ≠ 0) {i j : V} (hij : G.Adj i j) :
    (symHom (G := G) (m := m) hm).range ≠ ⊤ := fun htop =>
  (range_symHom_eq_top_iff_no_adj hm).mp htop i j hij

/-! ## 4. The isometries and the matrices are the same group -/

theorem isoMat_mem_symmetryMatrices (hm : m ≠ 0)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V} (hT : T ∈ symmetries G m) :
    isoMat T ∈ symmetryMatrices G m :=
  ⟨transpose_mul_isoMat T,
    (mem_linSym_iff_comm (transpose_mul_isoMat T)).mp (isoMat_mem_linSym hm hT)⟩

theorem orthIsometry_isoMat (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    orthIsometry (transpose_mul_isoMat T) = T :=
  LinearIsometryEquiv.ext fun x => mv_isoMat T x

/-- **THE ISOMETRIC SYMMETRIES AND THE SYMMETRY MATRICES ARE THE SAME SET.** -/
noncomputable def symmetriesEquiv (hm : m ≠ 0) :
    symmetries G m ≃ symmetryMatrices G m where
  toFun T := ⟨isoMat T.1, isoMat_mem_symmetryMatrices hm T.2⟩
  invFun R := ⟨orthIsometry R.2.1, gaussianField_map_of_mem hm R.2⟩
  left_inv T := Subtype.ext (orthIsometry_isoMat T.1)
  right_inv R := Subtype.ext (isoMat_orthIsometry R.2.1)

/-- **AND THE SAME GROUP.** -/
noncomputable def symmetriesMulEquiv (hm : m ≠ 0) :
    symmetriesSubgroup G m ≃* FieldSymmetrySubgroup.symmetrySubgroup G m where
  toFun T := ⟨⟨isoMat T.1, mem_unitary_iff.mpr (transpose_mul_isoMat T.1)⟩,
    isoMat_mem_symmetryMatrices hm T.2⟩
  invFun R := ⟨orthIsometry R.2.1, gaussianField_map_of_mem hm R.2⟩
  left_inv T := Subtype.ext (orthIsometry_isoMat T.1)
  right_inv R := Subtype.ext (Subtype.ext (isoMat_orthIsometry R.2.1))
  map_mul' T₁ T₂ := Subtype.ext (Subtype.ext (isoMat_mul T₁.1 T₂.1))

/-- **AND THE PRODUCT DECOMPOSITION IS ABOUT THE GROUP THIS ESTATE COUNTS.** -/
noncomputable def symmetriesMulEquivProd (hm : m ≠ 0) :
    symmetriesSubgroup G m ≃*
      ∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ :=
  (symmetriesMulEquiv hm).trans (FieldSymmetrySubgroup.symmetrySubgroup_mulEquiv_prod hm)

/-- **SO THE COUNT IS A COUNT OF MATRICES TOO** — the statement `FieldSymmetryFinite` says is not
made there. -/
theorem card_symmetryMatrices (hm : m ≠ 0)
    (hsimple : Function.Injective (green_posDef G hm).isHermitian.eigenvalues) :
    Nat.card (symmetryMatrices G m) = 2 ^ Fintype.card V := by
  rw [← Nat.card_congr (symmetriesEquiv hm)]
  exact FieldLineCount.card_symmetries hm hsimple

/-- **AND THE FINITENESS CRITERION NOW COUNTS THE MATRICES**, which is the sentence
`FieldSymmetryFinite`'s own fence says is not made there. -/
theorem card_symmetryMatrices_of_finite (hm : m ≠ 0) (hfin : (symmetryMatrices G m).Finite) :
    Nat.card (symmetryMatrices G m) = 2 ^ Fintype.card V :=
  card_symmetryMatrices hm ((FieldSymmetryFinite.finite_iff_injective hm).1 hfin)

end FieldSymmetryHom
