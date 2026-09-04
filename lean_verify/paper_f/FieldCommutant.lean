import FieldIsometryInvariance
import FieldSignFlip
import RayleighMatrix

/-!
# Preserving the form is commuting with the propagator

`FieldIsometryInvariance` proved that an isometry preserving the propagator's quadratic form is a
symmetry of the Gaussian field, and every unit since has hunted for isometries satisfying that
hypothesis by inspecting the form directly. **The hypothesis has a standard equivalent that nothing
in this estate had written down**: an isometry preserves the form **if and only if it commutes with
the propagator's action on vectors.**

That is the form the question wants to be asked in. *Preserve a quadratic form* is a condition to be
checked vector by vector; *commute with a symmetric operator* is a condition with a theory attached
— the commutant of a symmetric operator is where its eigenspaces live, and it is exactly where the
open case of this chain (a connected graph) has to be settled.

## What is proved

**`quadForm_eq_inner`** — the `dotProduct` form and the `EuclideanSpace` inner product agree, which
is the bridge `LaplacianSharpEquality` names as a thing it needed and did not build.

**`preservesQuadForm_of_commutes`** — if `T` commutes with `x ↦ green *ᵥ x` then it preserves the
form. One line of isometry, no polarisation.

**`commutes_of_preservesQuadForm`** — and conversely, by polarising the quadratic form into the
bilinear one and using that the propagator is symmetric, so `⟪x, green y⟫ = ⟪green x, y⟫`.

**`preservesQuadForm_iff_commutes`** — the biconditional, and with
`FieldIsometryInvariance.gaussianField_map_isometry` behind it: **an isometry commuting with the
propagator is a symmetry of the field.**

**`commutes_permField`**, **`commutes_signFlip`** — the estate's two known families, restated in the
new vocabulary, each in a line from the corresponding `PreservesQuadForm` lemma.

## What this changes about the open question

The statement still open is *there is an invariant isometry of `green` on a connected graph outside
the permutations, the signs and their composites* (`ERRATUM 453`'s rule: this is the statement, and
what follows is one route). **In the commutant vocabulary the route is visible**: any orthogonal map
acting as a rotation on a degenerate eigenspace of `green` and as the identity on its orthogonal
complement commutes with `green`, and
`CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` supplies a two-dimensional eigenspace on
the connected cycle. **What is missing is the construction of that map**, and this file does not
build it. Not attempted; no cost claimed (`ERRATUM 246`).

> ⚠ **THE STATEMENT WAS PROVED THE NEXT UNIT, BY A ROUTE THAT IS NOT THIS ONE, AND THIS PARAGRAPH
> IS KEPT AS WRITTEN** (`ERRATUM 94`, **`ERRATUM 454`**, 2026-09-04). `FieldHouseholder` exhibits an
> invariant isometry on **every** finite graph with `3 ≤ |V|`, connected ones included: the
> **Householder reflection through the all-ones line**, `(2/|V|) · J − 1`. It needs **no degenerate
> eigenspace and no rotation** — the all-ones vector is an eigenvector of `green` at `m⁻²` on every
> graph (`GreenExpansion.green_mulVec_one`, in this estate since 12 August), so a symmetric operator
> preserves both that line and its complement, and the reflection swapping their roles commutes.
> **A one-dimensional eigenspace was enough.** The paragraph above is right that the rotation route
> would work and wrong to leave the impression it was the way in — **the third fence in a row to
> name a route the answer did not take.**

## What is NOT here

**No new symmetry**, and no claim that the commutant is larger than the known families on any
particular graph.

**Nothing spectral.** No eigenvector, eigenspace or diagonalisation appears; the biconditional is
proved by polarisation alone, which is why it needs no hypothesis on the graph.

**Not a statement about the measure's full symmetry group.** Commuting is equivalent to preserving
the form, and preserving the form is *sufficient* for invariance. Whether it is *necessary* is
asked nowhere in this chain and is not asked here.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldCommutant

open Matrix GraphLaplacian FieldAutInvariance FieldIsometryInvariance FieldSignFlip
open RayleighMatrix

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The bridge between the two vocabularies -/

omit [DecidableEq V] in
/-- **THE `dotProduct` FORM IS THE INNER PRODUCT AGAINST THE MATRIX ACTION.**
`LaplacianSharpEquality` names this bridge as something it needed and did not build. -/
theorem quadForm_eq_inner (A : Matrix V V ℝ) (x : EuclideanSpace ℝ V) :
    x ⬝ᵥ (A *ᵥ x) = inner ℝ x (mv A x) := by
  rw [inner_expand]
  simp only [dotProduct, Matrix.mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mv_row]

omit [DecidableEq V] in
/-- The bilinear form, in the same vocabulary. -/
theorem inner_mv_comm (A : Matrix V V ℝ) (hA : A.IsSymm) (x y : EuclideanSpace ℝ V) :
    inner ℝ x (mv A y) = inner ℝ (mv A x) y := by
  rw [inner_expand, inner_expand]
  simp only [mv_row, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hsym : A b a = A a b := by
    have h := congrFun (congrFun hA a) b
    simpa [Matrix.transpose_apply] using h
  rw [hsym]
  ring

/-! ## 2. The two directions -/

/-- **COMMUTING GIVES THE FORM**, in one line of isometry. -/
theorem preservesQuadForm_of_commutes {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : ∀ x, mv (green G m) (T x) = T (mv (green G m) x)) :
    PreservesQuadForm G m T := by
  intro t
  rw [quadForm_eq_inner, quadForm_eq_inner]
  have hsymm : ∀ y, mv (green G m) (T.symm y) = T.symm (mv (green G m) y) := by
    intro y
    apply T.injective
    rw [T.apply_symm_apply, ← hT (T.symm y), T.apply_symm_apply]
  rw [hsymm t, T.symm.inner_map_map]

/-- **AND THE FORM GIVES COMMUTING**, by polarisation and the propagator's symmetry. -/
theorem commutes_of_preservesQuadForm (hm : m ≠ 0)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V} (hT : PreservesQuadForm G m T) (x : V → ℝ) :
    mv (green G m) (T (WithLp.toLp 2 x)) = T (mv (green G m) (WithLp.toLp 2 x)) := by
  have hQ : ∀ t : EuclideanSpace ℝ V,
      inner ℝ (T.symm t) (mv (green G m) (T.symm t)) = inner ℝ t (mv (green G m) t) := by
    intro t
    have := hT t
    rwa [quadForm_eq_inner, quadForm_eq_inner] at this
  have hB : ∀ t s : EuclideanSpace ℝ V,
      inner ℝ (T.symm t) (mv (green G m) (T.symm s)) = inner ℝ t (mv (green G m) s) := by
    intro t s
    have hts := hQ (t + s)
    have ht := hQ t
    have hs := hQ s
    simp only [map_add, RayleighMatrix.mv_add, inner_add_left, inner_add_right] at hts
    have hsym1 : inner ℝ (T.symm s) (mv (green G m) (T.symm t))
        = inner ℝ (T.symm t) (mv (green G m) (T.symm s)) := by
      rw [inner_mv_comm _ (green_isSymm G hm), real_inner_comm]
    have hsym2 : inner ℝ s (mv (green G m) t) = inner ℝ t (mv (green G m) s) := by
      rw [inner_mv_comm _ (green_isSymm G hm), real_inner_comm]
    rw [hsym1] at hts
    rw [hsym2] at hts
    linarith [hts, ht, hs]
  refine ext_inner_left ℝ fun u => ?_
  have h1 := hB u (T (WithLp.toLp 2 x))
  rw [T.symm_apply_apply] at h1
  rw [← h1, ← T.inner_map_map (T.symm u) (mv (green G m) (WithLp.toLp 2 x)), T.apply_symm_apply]

/-- **THE BICONDITIONAL.** -/
theorem preservesQuadForm_iff_commutes (hm : m ≠ 0)
    (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    PreservesQuadForm G m T ↔ ∀ x : EuclideanSpace ℝ V,
      mv (green G m) (T x) = T (mv (green G m) x) :=
  ⟨fun h x => commutes_of_preservesQuadForm hm h (WithLp.ofLp x),
    fun h => preservesQuadForm_of_commutes h⟩

/-! ## 3. The two known families, in the new vocabulary -/

/-- A graph automorphism commutes with the propagator. -/
theorem commutes_permField {θ : V ≃ V} (hθ : IsGraphAut G θ) (hm : m ≠ 0)
    (x : EuclideanSpace ℝ V) :
    mv (green G m) (permField θ x) = permField θ (mv (green G m) x) :=
  (preservesQuadForm_iff_commutes hm _).mp (preservesQuadForm_permField hθ m) x

/-- And so does a sign flip on a union of connected components. -/
theorem commutes_signFlip (hm : m ≠ 0) {s : Finset V} (hs : IsComponentClosed G s)
    (x : EuclideanSpace ℝ V) :
    mv (green G m) (signFlip s x) = signFlip s (mv (green G m) x) :=
  (preservesQuadForm_iff_commutes hm _).mp (preservesQuadForm_signFlip hm hs) x

/-- **AN ISOMETRY COMMUTING WITH THE PROPAGATOR IS A SYMMETRY OF THE FIELD.** -/
theorem gaussianField_map_of_commutes (hm : m ≠ 0)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : ∀ x, mv (green G m) (T x) = T (mv (green G m) x)) :
    (MeasureTheory.Measure.map T (gaussianField G m)) = gaussianField G m :=
  gaussianField_map_isometry hm (preservesQuadForm_of_commutes hT)

end FieldCommutant
