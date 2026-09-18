/-
  FieldLinearGroup.lean — the linear symmetry GROUP of the Gaussian field, as a group of MAPS.

  WHY THIS FILE EXISTS. `UNLOCK_WATCHLIST`'s item *the linear symmetry
  classification as a GROUP isomorphism, and lifted from matrices to continuous
  linear maps* has had both of its named clauses discharged — clause (b) by
  `FieldSymmetryIso.conjSqEquiv` and `FieldSymmetryInclusion.linSymGL`, clause (a)
  by `FieldLinearMaps.gaussianField_map_iff_conjSq_clm`. What its 2026-09-13
  annotation says is left is **the group of MAPS**:

    > transporting the `Subgroup` along `mvCLMEquiv` needs `mvCLM` multiplicative,
    > which is true and unbuilt because nothing consumes it (`ERRATUM 246`)

  `FieldLinearMaps`'s own header says the same in its fence: *`symmetry_clm_set_eq`
  is a SET equality … claiming a group of maps without building one would be the
  `ERRATUM 545` move*. **This file builds it, so both sentences are now overtaken**
  and both carry a dated `⚠` keeping the text as written (`ERRATUM 94`).

  **PROBED BEFORE WRITING.** `mvCLM` occurs across `paper_f` with **no**
  multiplicativity, `map_one`, `AlgEquiv`, `MonoidHom` or `unitary` statement
  anywhere — the names `mvCLM_mul`, `mvCLM_one`, `mvCLMAlgEquiv`, `mvCLMMonoidHom`,
  `linSymCLM` and `linSymCLMGL` were all free. The gap the annotation describes was
  real and it is the whole obstruction.

  WHAT THIS FILE PROVES.

  1. **`mvCLM_one`, `mvCLM_mul`** — a matrix and a continuous linear map are the same
     datum **as algebras** and not only as vector spaces. Each is one `ext` and a
     `simp` that unfolds `RayleighMatrix.mv`; read off the proof terms, the unit's step
     is `Matrix.one_mulVec` and the product's is `Matrix.mulVec_mulVec`.
     `mvCLMAlgEquiv` is the `≃ₐ[ℝ]` on top of them and `mvCLMMonoidHom` its monoid
     projection, which is what transport needs.
  2. **`linSymCLM`** — the linear symmetries **as a `Submonoid` of maps**, the image
     of `FieldSymmetryIso.linSym` under `mvCLMMonoidHom`. `mem_linSymCLM_iff` says a
     map lies in it **iff** its pushforward fixes the Gaussian field, so the object is
     the symmetry group and not merely an image; `coe_linSymCLM` is
     `FieldLinearMaps.symmetry_clm_set_eq` read off it. `linSymCLMEquiv` is a
     `MulEquiv` from `Matrix.unitaryGroup V ℝ`.
  3. **`isometryEquivLinSymCLM`** — **THE DELIVERABLE, AND NO MATRIX APPEARS IN IT.**
     The group of linear isometries of `EuclideanSpace ℝ V` — the orthogonal group of
     `ℝ^V`, as maps — is isomorphic to the linear symmetry group of the Gaussian
     field. The bridge is `mvCLM_mem_unitary_iff` (a matrix is orthogonal iff its map
     is unitary, through `FieldLinearClassified.adjoint_mvCLM`) composed with
     Mathlib's `Unitary.linearIsometryEquiv`. The item's `LIKELY OUTCOME` line asks
     for exactly this sentence.
  4. **`linSymCLMGL`** — the same group as a `Subgroup` of the invertible maps,
     mirroring `FieldSymmetryInclusion.linSymGL` on the matrix side, and taking **no
     hypothesis on the mass**: the ambient group supplies the inverse and
     `mvCLM_injective` transports it back to a matrix identity, so
     `isUnit_det_of_mem_linSym` is not needed.

  WHAT IS NOT CLAIMED. **No cardinality and no index** — the item's own two remaining
  residues, unchanged. `isometryEquivLinSymCLM` moves every counting question onto
  Mathlib's isometry group, which is not this estate's object, and nothing here
  measures what `FieldSymmetryHom.range_symHom_ne_top` says is missing. Not attempted
  (`ERRATUM 246`). **Nothing about non-linear maps**, and — correcting four places
  that say otherwise (`ERRATUM 645`) — that is **not** a clause of this item: the
  item's `BLOCKED ON` line says *two things stop that being the sentence a reader
  wants* and enumerates (a) and (b) only. The non-linear clause belongs to the item
  *an orthogonal `T` whose pushforward fixes `gaussianField G m` COMMUTES with …*,
  whose own line reads **WHAT REMAINS IS GENUINELY NON-LINEAR MAPS**.
  **No wall moves**: `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum
  sense — knowing the linear symmetries as a group of maps rather than as a set of
  maps is the same shadow, bundled the way a reader can use.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import FieldLinearMaps
import FieldSymmetryInclusion

namespace FieldLinearGroup

open Matrix MeasureTheory
open GraphLaplacian FieldSqrtConjugation FieldLinearClassified FieldLinearMaps FieldSymmetryIso

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. `mvCLM` is multiplicative — the step the watchlist item names -/

/-- **THE IDENTITY MATRIX IS THE IDENTITY MAP.** -/
@[simp] theorem mvCLM_one : mvCLM (1 : Matrix V V ℝ) = 1 := by
  ext v
  simp [RayleighMatrix.mv]

/-- **AND A PRODUCT OF MATRICES IS A COMPOSITE OF MAPS.** This is the one step the
watchlist item says is *true and unbuilt because nothing consumes it*, and it is one
`ext` and `Matrix.mulVec_mulVec`. **23 of this file's 24 declarations have this or
`mvCLM_one` in their transitive dependencies** — counted from the environment, not
estimated — the exception being §4's `mem_linSym_of_mul_eq_one`, which is about
matrices only. -/
theorem mvCLM_mul (A B : Matrix V V ℝ) : mvCLM (A * B) = mvCLM A * mvCLM B := by
  ext v
  simp [RayleighMatrix.mv]

theorem mvCLM_eq_one_iff {L : Matrix V V ℝ} : mvCLM L = 1 ↔ L = 1 := by
  rw [← mvCLM_one]
  exact mvCLM_eq_iff

/-- **SO A MATRIX AND A CONTINUOUS LINEAR MAP ARE THE SAME DATUM AS ALGEBRAS.**
`FieldLinearMaps.mvCLMEquiv` is the `≃ₗ[ℝ]`; this is the `≃ₐ[ℝ]` above it. -/
def mvCLMAlgEquiv (V : Type*) [Fintype V] [DecidableEq V] :
    Matrix V V ℝ ≃ₐ[ℝ] (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :=
  AlgEquiv.ofLinearEquiv (mvCLMEquiv V) mvCLM_one mvCLM_mul

@[simp] theorem mvCLMAlgEquiv_apply (M : Matrix V V ℝ) : mvCLMAlgEquiv V M = mvCLM M := rfl

/-- The monoid projection of `mvCLMAlgEquiv`, which is what `Submonoid.map` takes. -/
def mvCLMMonoidHom (V : Type*) [Fintype V] [DecidableEq V] :
    Matrix V V ℝ →* (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :=
  (mvCLMAlgEquiv V).toAlgHom.toRingHom.toMonoidHom

@[simp] theorem mvCLMMonoidHom_apply (M : Matrix V V ℝ) : mvCLMMonoidHom V M = mvCLM M := rfl

/-! ## 2. The linear symmetries as a `Submonoid` of maps -/

/-- **THE LINEAR SYMMETRY GROUP, AS MAPS.** `FieldSymmetryIso.linSym` transported
along `mvCLMMonoidHom`; `mem_linSymCLM_iff` below is what makes this the symmetry
group rather than an image of one. -/
def linSymCLM (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Submonoid (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :=
  (linSym G m).map (mvCLMMonoidHom V)

theorem mem_linSymCLM_iff_symm_mem {T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V} :
    T ∈ linSymCLM G m ↔ (mvCLMEquiv V).symm T ∈ linSym G m := by
  simp only [linSymCLM, Submonoid.mem_map, mvCLMMonoidHom_apply]
  constructor
  · rintro ⟨L, hL, hLT⟩
    have hsymm : (mvCLMEquiv V).symm T = L := by
      rw [← hLT, ← mvCLMEquiv_apply, LinearEquiv.symm_apply_apply]
    rwa [hsymm]
  · intro h
    exact ⟨(mvCLMEquiv V).symm T, h, mvCLM_symm T⟩

/-- **A MAP LIES IN `linSymCLM` IFF ITS PUSHFORWARD FIXES THE GAUSSIAN FIELD.** -/
theorem mem_linSymCLM_iff (hm : m ≠ 0) (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    T ∈ linSymCLM G m ↔ Measure.map T (gaussianField G m) = gaussianField G m :=
  mem_linSymCLM_iff_symm_mem.trans (symmetry_clm_iff_mem_linSym hm T).symm

/-- `FieldLinearMaps.symmetry_clm_set_eq` read off the `Submonoid`: the set that file
describes **is** the carrier of a group. -/
theorem coe_linSymCLM (hm : m ≠ 0) :
    (linSymCLM G m : Set (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
      = {T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V |
          Measure.map T (gaussianField G m) = gaussianField G m} := by
  ext T
  exact mem_linSymCLM_iff hm T

/-- **THE `MulEquiv` THE ITEM ASKS FOR, IN ITS MATRIX-SIDE FORM.**
`FieldSymmetryIso.conjSqEquiv` composed with the transport. -/
def linSymCLMEquiv (hm : m ≠ 0) : Matrix.unitaryGroup V ℝ ≃* linSymCLM G m :=
  (conjSqEquiv (G := G) hm).trans
    (Submonoid.equivMapOfInjective (linSym G m) (mvCLMMonoidHom V) mvCLM_injective)

@[simp] theorem coe_linSymCLMEquiv (hm : m ≠ 0) (O : Matrix.unitaryGroup V ℝ) :
    ((linSymCLMEquiv (G := G) hm O : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
      = mvCLM (conjSq G m O.1) := rfl

/-! ## 3. The orthogonal group of `ℝ^V`, with no matrix in the statement -/

/-- **A MATRIX IS ORTHOGONAL IFF ITS MAP IS UNITARY.** The adjoint is the transpose
(`FieldLinearClassified.adjoint_mvCLM`) and `star` on a matrix is the transpose
(`FieldSymmetryIso.star_eq_transpose`), so the two conditions are the same pair of
equations carried across §1. -/
theorem mvCLM_mem_unitary_iff {L : Matrix V V ℝ} :
    mvCLM L ∈ unitary (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
      ↔ L ∈ Matrix.unitaryGroup V ℝ := by
  have hstar : star (mvCLM L) = mvCLM Lᵀ := by
    rw [ContinuousLinearMap.star_eq_adjoint, adjoint_mvCLM]
  rw [Unitary.mem_iff, Unitary.mem_iff, hstar, FieldSymmetryIso.star_eq_transpose,
    ← mvCLM_mul, ← mvCLM_mul, mvCLM_eq_one_iff, mvCLM_eq_one_iff]

/-- **SO THE UNITARY MAPS ARE EXACTLY THE IMAGE OF THE ORTHOGONAL MATRICES.** -/
theorem unitary_eq_map_unitaryGroup :
    unitary (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
      = (Matrix.unitaryGroup V ℝ).map (mvCLMMonoidHom V) := by
  ext T
  simp only [Submonoid.mem_map, mvCLMMonoidHom_apply]
  constructor
  · intro h
    refine ⟨(mvCLMEquiv V).symm T, ?_, mvCLM_symm T⟩
    exact mvCLM_mem_unitary_iff.mp (by rwa [mvCLM_symm])
  · rintro ⟨L, hL, rfl⟩
    exact mvCLM_mem_unitary_iff.mpr hL

/-- The orthogonal matrices and the unitary maps are the same group. -/
def unitaryMatrixEquivCLM (V : Type*) [Fintype V] [DecidableEq V] :
    Matrix.unitaryGroup V ℝ ≃* unitary (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :=
  (Submonoid.equivMapOfInjective (Matrix.unitaryGroup V ℝ) (mvCLMMonoidHom V)
    mvCLM_injective).trans (MulEquiv.submonoidCongr unitary_eq_map_unitaryGroup.symm)

/-- **THE MATRIX OF A LINEAR ISOMETRY IS ORTHOGONAL** — the direction
`FieldOrthIsometry` does not run, and what §3's composition needs. -/
theorem symm_coe_mem_unitaryGroup (e : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    (mvCLMEquiv V).symm (e : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
      ∈ Matrix.unitaryGroup V ℝ := by
  refine mvCLM_mem_unitary_iff.mp ?_
  rw [mvCLM_symm]
  simpa using (Unitary.linearIsometryEquiv.symm e).2

/-- **THE SENTENCE THE WATCHLIST ITEM'S `LIKELY OUTCOME` LINE ASKS FOR: the linear
symmetry group of the Gaussian field is isomorphic to the orthogonal group of `ℝ^V`.**
Both sides are groups of MAPS — the left is Mathlib's group of linear isometries of
`EuclideanSpace ℝ V`, the right this estate's symmetries of `gaussianField G m` — and
no matrix occurs in the statement. The conjugation by the propagator's square root is
inside `conjSqEquiv`, where the matrix side keeps it. -/
def isometryEquivLinSymCLM (hm : m ≠ 0) :
    (EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) ≃* linSymCLM G m :=
  (Unitary.linearIsometryEquiv.symm.trans (unitaryMatrixEquivCLM V).symm).trans
    (linSymCLMEquiv hm)

/-! ## 4. The same group as a `Subgroup` of the invertible maps -/

theorem symm_mul_symm (S T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    (mvCLMEquiv V).symm (S * T) = (mvCLMEquiv V).symm S * (mvCLMEquiv V).symm T := by
  refine mvCLM_injective ?_
  rw [mvCLM_mul, mvCLM_symm, mvCLM_symm, mvCLM_symm]

theorem symm_one : (mvCLMEquiv V).symm 1 = 1 := by
  refine mvCLM_injective ?_
  rw [mvCLM_symm, mvCLM_one]

/-- **A TWO-SIDED INVERSE ALREADY IN HAND STAYS IN `linSym`, AT ANY MASS.**
`FieldSymmetryInclusion.inv_mem_linSym` takes `m ≠ 0` because it must *produce* the
inverse from `isUnit_det_of_mem_linSym`; the closure step itself needs no hypothesis on
the mass or the graph, and separating the two is what lets §4 below mirror `linSymGL`
with no hypothesis at all. -/
theorem mem_linSym_of_mul_eq_one {L M : Matrix V V ℝ} (hML : M * L = 1)
    (hL : L ∈ linSym G m) : M ∈ linSym G m := by
  rw [mem_linSym] at hL ⊢
  calc M * green G m * Mᵀ
      = M * (L * green G m * Lᵀ) * Mᵀ := by rw [hL]
    _ = M * L * green G m * (Lᵀ * Mᵀ) := by simp only [Matrix.mul_assoc]
    _ = green G m := by
        rw [hML, Matrix.one_mul, ← Matrix.transpose_mul, hML, Matrix.transpose_one,
          Matrix.mul_one]

/-- The matrices of an invertible map and of its inverse multiply to `1`, which is §1
plus `Units`. -/
theorem symm_inv_mul_symm (U : (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)ˣ) :
    (mvCLMEquiv V).symm ↑U⁻¹ * (mvCLMEquiv V).symm ↑U = 1 := by
  rw [← symm_mul_symm, ← Units.val_mul, inv_mul_cancel, Units.val_one, symm_one]

/-- **THE LINEAR SYMMETRIES AS A `Subgroup` OF THE INVERTIBLE MAPS**, mirroring
`FieldSymmetryInclusion.linSymGL` on the matrix side. **No hypothesis on the mass**:
the ambient group supplies the inverse and §1 carries it back to a matrix identity, so
`isUnit_det_of_mem_linSym` is never reached. -/
def linSymCLMGL (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Subgroup (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)ˣ where
  carrier := {U | (U : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) ∈ linSymCLM G m}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one]
    exact (linSymCLM G m).one_mem
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul] at ha hb ⊢
    exact (linSymCLM G m).mul_mem ha hb
  inv_mem' {U} h := by
    simp only [Set.mem_setOf_eq, mem_linSymCLM_iff_symm_mem] at h ⊢
    exact mem_linSym_of_mul_eq_one (symm_inv_mul_symm U) h

@[simp] theorem mem_linSymCLMGL {U : (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)ˣ} :
    U ∈ linSymCLMGL G m
      ↔ (U : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) ∈ linSymCLM G m := Iff.rfl

/-! ## 5. Review round 70 — the ways this could be hollow

**"§1 is two `simp` calls."** It is, and the watchlist item said so before this file
existed — *`mvCLM` multiplicative, which is true and unbuilt because nothing consumes
it*. The content is the word **consumes**, and it is counted rather than asserted:
walking the transitive constant dependencies of all 24 declarations, **23 of them
reach `mvCLM_mul` or `mvCLM_one`.** The one that does not is
`mem_linSym_of_mul_eq_one`, which is a statement about matrices and is §4's
by-product — so the exception is the part of this file that is *not* about maps, which
is the right exception to have. A fact nobody can use is a gap however short its proof,
and that the item was right about the SIZE of the step is recorded, not hidden.

**"`linSymCLM` could be an image with no claim to being a symmetry group."** That is
exactly the `ERRATUM 545` move the file it supersedes warns against, and
`mem_linSymCLM_iff` is the answer: a map lies in `linSymCLM` **iff** its pushforward
fixes `gaussianField G m`. Without that theorem the definition would be a transport
and nothing more.

**"§3 might be Mathlib's theorem with a rename."** `Unitary.linearIsometryEquiv` is
Mathlib's and is used as such. What is not Mathlib's is `mvCLM_mem_unitary_iff` — the
bridge from the ORTHOGONAL MATRICES to the UNITARY MAPS, which needs this estate's
`adjoint_mvCLM` because Mathlib's `star` on continuous linear maps is the adjoint and
nothing says the adjoint of `mvCLM L` is `mvCLM Lᵀ` except that theorem. Composing
three equivalences is bundling; the middle one is the content.

**"§4 duplicates §2."** It does not: §2's object is a `Submonoid` of a monoid that has
non-invertible elements, and §4's is a `Subgroup` of the units. The matrix side carries
both for the same reason — `linSym` is a `Submonoid` and `linSymGL` a `Subgroup` — and
the estate's fence about `linSym` being *a group in substance* with *no `Subgroup`
instance constructed* is what the second packaging answers on the map side.

**"The item might now be closed."** It is not, and the header says which two residues
survive: **no cardinality** and **no index**. Both are named in the item's own
governing `STATUS 11 SEP 2026` line and neither is attempted here (`ERRATUM 246`).
⚠ **ONE OF THE TWO RESIDUES FALLS ON 2026-09-18, kept as written** (`ERRATUM 94`): **`no
index` is closed on a named graph** — `FieldSymmetryIndex.index_range_symHom_eq_zero_line`, index
**`0`** for `symHom`'s range in `linSymGL` on `boxGraph 1 (k+1)` — and **`no cardinality` survives
alone**, still for the reason this file gives, that `isometryEquivLinSymCLM` and `conjSqEquiv` move
every count onto Mathlib's objects rather than the estate's. The item's governing line is updated
accordingly. **Not closed in general**: the index argument needs the isometric side finite, which
holds iff the spectrum is simple (`FieldSymmetryFinite.finite_iff_injective`).
What this file does close is the *group of MAPS*, which is the third residue that line
does not name and the 2026-09-13 annotation does.
-/

end

end FieldLinearGroup
