/-
  FieldLinearMaps.lean — the linear classification, over MAPS rather than matrices.

  WHY THIS FILE EXISTS. `UNLOCK_WATCHLIST`'s item *the linear symmetry
  classification as a GROUP isomorphism, and lifted from matrices to continuous
  linear maps* names two obstacles:

    **(a) MATRICES, NOT MAPS.** That every continuous linear map on
    `EuclideanSpace ℝ V` is `mvCLM L` for some `L` is standard —
    `Matrix.toEuclideanLin` is a `LinearEquiv` and a linear map in finite
    dimension is continuous — and **it is not invoked**. Until it is, the
    classification quantifies over matrices.

    **(b) SETS, NOT GROUPS.** … `conjSq_bijOn` is a bijection of sets.

  **(b) HAS BEEN DONE SINCE AND THE ITEM WAS NEVER ANNOTATED** — `ERRATUM 546`.
  `FieldSymmetryIso.conjSqEquiv` is a `MulEquiv`, `FieldSymmetrySubgroup.symmetrySubgroup`
  is a `Subgroup`, and `FieldSymmetryInclusion.linSymGL` is the linear symmetries'
  `Subgroup` of `GL(V)`. `FieldLinearClassified`'s own header records all three in
  dated ⚠ notes; the watchlist item does not, and it is the item a reader consults
  to find out what is left.

  **(a) SURVIVES, AND IT IS THIS FILE.** Probed before writing: `mvCLM` occurs in
  `paper_f` with no `surjective`, `exists`, `equiv` or `onto` statement about it
  anywhere. So the classification really did quantify over matrices only, and a
  reader asking *which continuous linear maps preserve the field* got no answer.

  WHAT THIS FILE PROVES.

  1. **`mvCLMEquiv`** — `mvCLM` IS an equivalence: `Matrix.toEuclideanLin`
     (`LinearEquiv`, Mathlib) composed with `LinearMap.toContinuousLinearMap`
     (`LinearEquiv` in finite dimension, Mathlib). The item called this standard
     and it is; what it is not is invoked, and one composition is the whole of it.
     `mvCLM_surjective`, `mvCLM_injective`, `mvCLM_eq_iff`.
  2. **`gaussianField_map_iff_conjSq_clm`** — **THE CLASSIFICATION OVER MAPS.** A
     continuous linear map `T` on `EuclideanSpace ℝ V` preserves the Gaussian field
     if and only if `T = mvCLM (C^{1/2} O C^{-1/2})` for some orthogonal `O`. The
     quantifier is over every `T`, with no matrix in the hypothesis.
  3. `symmetry_clm_iff_orthogonal` — the same read as a statement about the matrix
     `mvCLMEquiv.symm T`, which is the form a reader with a map in hand wants: the
     map is a symmetry exactly when its matrix lies in `FieldSymmetryIso.linSym`.

  WHAT IS NOT CLAIMED. **No group of MAPS is built.** The `Subgroup` and `MulEquiv`
  of clause (b) live on matrices, and transporting them along `mvCLMEquiv` would
  need `mvCLM` to be multiplicative — which it is, `Matrix.toEuclideanLin` being an
  algebra map, and which is not proved here because nothing consumes it
  (`ERRATUM 246`). **Nothing about non-linear maps**, which is the item's own third
  clause and untouched. **No wall moves**: `W1`'s open part is `OS0` and `OS4`, and
  `OS1` in its continuum sense — knowing the linear symmetries over maps rather
  than over matrices is the same shadow, described in the reader's language.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import FieldLinearClassified
import FieldSymmetryIso

namespace FieldLinearMaps

open Matrix MeasureTheory
open GraphLaplacian FieldSqrtConjugation FieldLinearClassified

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. `mvCLM` is an equivalence -/

/-- **A MATRIX AND A CONTINUOUS LINEAR MAP ARE THE SAME DATUM.**
`Matrix.toEuclideanLin` is Mathlib's `LinearEquiv` from matrices to linear maps and
`LinearMap.toContinuousLinearMap` is Mathlib's `LinearEquiv` from linear maps to
continuous ones in finite dimension. `mvCLM` is their composition and the watchlist
item called invoking that standard; it is, and nobody had. -/
def mvCLMEquiv (V : Type*) [Fintype V] [DecidableEq V] :
    Matrix V V ℝ ≃ₗ[ℝ] (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :=
  (Matrix.toEuclideanLin : Matrix V V ℝ ≃ₗ[ℝ] _).trans LinearMap.toContinuousLinearMap

@[simp] theorem mvCLMEquiv_apply (M : Matrix V V ℝ) : mvCLMEquiv V M = mvCLM M := rfl

theorem mvCLM_surjective :
    Function.Surjective (mvCLM : Matrix V V ℝ → (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) :=
  fun T => ⟨(mvCLMEquiv V).symm T, by
    rw [← mvCLMEquiv_apply, LinearEquiv.apply_symm_apply]⟩

theorem mvCLM_injective :
    Function.Injective (mvCLM : Matrix V V ℝ → (EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) :=
  fun A B h => (mvCLMEquiv V).injective (by simpa using h)

theorem mvCLM_symm (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    mvCLM ((mvCLMEquiv V).symm T) = T := by
  rw [← mvCLMEquiv_apply, LinearEquiv.apply_symm_apply]

theorem mvCLM_eq_iff {A B : Matrix V V ℝ} : mvCLM A = mvCLM B ↔ A = B :=
  ⟨fun h => mvCLM_injective h, fun h => h ▸ rfl⟩

/-! ## 2. The classification, over maps -/

/-- **THE LINEAR CLASSIFICATION WITH NO MATRIX IN THE HYPOTHESIS.** A continuous
linear map on `EuclideanSpace ℝ V` preserves the Gaussian field **iff** it is the
map of a conjugated orthogonal matrix. `FieldLinearClassified.gaussianField_map_iff_conjSq`
says this of matrices; §1 is what carries it to every `T`. -/
theorem gaussianField_map_iff_conjSq_clm (hm : m ≠ 0)
    (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    Measure.map T (gaussianField G m) = gaussianField G m ↔
      ∃ O : Matrix V V ℝ, Oᵀ * O = 1 ∧ mvCLM (conjSq G m O) = T := by
  obtain ⟨L, rfl⟩ := mvCLM_surjective T
  rw [gaussianField_map_iff_conjSq hm L]
  constructor
  · rintro ⟨O, hO, rfl⟩
    exact ⟨O, hO, rfl⟩
  · rintro ⟨O, hO, hT⟩
    exact ⟨O, hO, mvCLM_injective hT⟩

/-- The same with the matrix recovered rather than existentially quantified: `T` is
a symmetry exactly when its own matrix lies in `FieldSymmetryIso.linSym`, the
`Submonoid` clause (b) of the watchlist item turned into a group. -/
theorem symmetry_clm_iff_mem_linSym (hm : m ≠ 0)
    (T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    Measure.map T (gaussianField G m) = gaussianField G m
      ↔ (mvCLMEquiv V).symm T ∈ FieldSymmetryIso.linSym G m := by
  have hT : mvCLM ((mvCLMEquiv V).symm T) = T := mvCLM_symm T
  constructor
  · intro h
    refine FieldSymmetryIso.mem_linSym_of_gaussianField_map hm ?_
    rwa [hT]
  · intro h
    have h2 := FieldSymmetryIso.gaussianField_map_of_mem_linSym hm h
    rwa [hT] at h2

/-- **AND SO THE SYMMETRIES OF THE FIELD AMONG CONTINUOUS LINEAR MAPS ARE EXACTLY
THE IMAGE OF `linSym`.** Stated as a set equality, which is what a reader with a
map in hand can use directly. -/
theorem symmetry_clm_set_eq (hm : m ≠ 0) :
    {T : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V |
        Measure.map T (gaussianField G m) = gaussianField G m}
      = mvCLM '' (FieldSymmetryIso.linSym G m : Set (Matrix V V ℝ)) := by
  ext T
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
  rw [symmetry_clm_iff_mem_linSym hm T]
  exact ⟨fun h => ⟨(mvCLMEquiv V).symm T, h, mvCLM_symm T⟩,
    fun ⟨L, hL, hLT⟩ => by rw [← hLT, ← mvCLMEquiv_apply, LinearEquiv.symm_apply_apply]; exact hL⟩

/-! ## 3. Review round 69 — the ways this could be hollow

**"§1 is two `LinearEquiv`s composed."** It is, and the watchlist item said so
before this file existed — *"standard … and it is not invoked"*. The content is
that nobody had invoked it, which was checked by grep before a line was written:
`mvCLM` appeared with no surjectivity, injectivity or equivalence statement
anywhere in `paper_f`. A composition nobody performs is a gap however short it is.

**"§2 could be `gaussianField_map_iff_conjSq` with a variable renamed."** The
QUANTIFIER is the difference and it is the only difference: that theorem's `L`
ranges over matrices and this one's `T` over every continuous linear map, and
turning one into the other is exactly the surjectivity §1 supplies. That is what
the watchlist item asked for and what it said stopped the classification being
*the sentence a reader wants*.

**"The group statement might be hiding here."** It is not, and the header says so:
`symmetry_clm_set_eq` is a SET equality. Transporting the `Subgroup` and `MulEquiv`
along `mvCLMEquiv` needs `mvCLM` multiplicative — true, `Matrix.toEuclideanLin`
being an algebra map — and is not done because nothing consumes it. Claiming a
group of maps without building one would be the `ERRATUM 545` move.

**"The watchlist item might not have been stale."** Clause (b) is: it says
*"`conjSq_bijOn` is a bijection of sets. That `conjSq` carries matrix
multiplication to matrix multiplication is one line and is not proved"*, and
`FieldSymmetryIso.conjSq_mul` proves exactly that line, with `conjSqEquiv` the
`MulEquiv` on top of it. `FieldLinearClassified`'s header carries dated ⚠ notes for
all of it; the ITEM does not, and the item is what a reader consults. `ERRATUM 546`.
-/

end

end FieldLinearMaps
