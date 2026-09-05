import FieldCommutantSpectral

/-!
# Invariance of the measure FORCES commuting — the direction the chain had been reading in

`ERRATUM 456`, written one unit ago, found that this estate proves *commuting ⟹ symmetry of the
Gaussian field* and **never the converse**, so every count of `symmetryMatrices` was a lower bound
on the symmetry group rather than a count of it. **This proves the converse.** The chain's sentences
are now backed by theorems instead of by a reading.

**The argument is the one the watchlist filed, and it is short because Mathlib carries both
halves.** A Gaussian measure is determined by its covariance;
`ProbabilityTheory.covarianceBilin_map` says a pushforward along a continuous linear map
transports the covariance form through the map's adjoint;
and `covarianceBilin_multivariateGaussian` evaluates the covariance form of this estate's
`gaussianField` as `x ⬝ᵥ green *ᵥ y`. So invariance reads off directly as
`(T⁻¹x) ⬝ᵥ green *ᵥ (T⁻¹x) = x ⬝ᵥ green *ᵥ x`, which is `FieldIsometryInvariance.PreservesQuadForm`
on the nose, and `FieldCommutant.commutes_of_preservesQuadForm` finishes.

## What is proved

**`adjoint_coe`** — the adjoint of a linear isometry equivalence is its inverse. One application of
`ContinuousLinearMap.eq_adjoint_iff` against `LinearIsometryEquiv.inner_map_map`.

**`preservesQuadForm_of_gaussianField_map`** — **an isometry whose pushforward fixes the Gaussian
field preserves the propagator's quadratic form.**

**`commutes_of_gaussianField_map`** — hence it commutes with the propagator.

**`gaussianField_map_iff_commutes`** — **the biconditional**: an isometry is a symmetry of the
Gaussian field **iff** it commutes with the propagator. The other direction is
`FieldCommutant.gaussianField_map_of_commutes`, unchanged.

**`mem_symmetryMatrices_iff_gaussianField_map`** — **so for orthogonal matrices, `symmetryMatrices`
IS the symmetry group** and not merely a subset of it. Every lower bound this chain has proved is
now a statement about the symmetry group itself: `FieldRotationCount.infinite_symmetryMatrices_box`
says the box's Gaussian field has infinitely many symmetries and, **among orthogonal matrices, that
none were being missed**; and `FieldCommutantSpectral.mem_symmetryMatrices_iff` now genuinely
characterises them — an orthogonal map is a symmetry of the field exactly when it preserves every
eigenspace of the propagator, which is the sentence `ERRATUM 456` struck out for being unproved.

## What is NOT here

**Only ISOMETRIES are characterised.** `gaussianField_map_iff_commutes` quantifies over
`EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V`. **A measure-preserving map that is not a linear
isometry is not covered** — not a linear map that fails to be isometric, and not a non-linear one.
The full automorphism group of the measure is untouched. **Not attempted, no cost claimed**
(`ERRATUM 246`).

**No description of the eigenspaces**, so `FieldCommutantSpectral`'s fence stands: which orthogonal
maps preserve every eigenspace still depends on multiplicities nobody has computed for a general
graph.

**No `∏ᵢ O(dᵢ)` isomorphism.** Still the shape and not the theorem (`ERRATUM 194`).

**Nothing about the torus at `d > 1`.**

**No wall moves — and this is the unit where that most needs saying.** Turning *at least this many
symmetries* into *exactly these symmetries* is the largest single upgrade this chain has made, and
`W1`'s open part is **unchanged**: `OS0` and `OS4`, and `OS1` in its continuum sense. A symmetry
group known exactly in finite volume is a shadow known exactly, not a smaller gap.

**The mass hypothesis is needed by every statement below except `adjoint_coe`**, which mentions no
graph — checked against the binders and not asserted (`ERRATUM 455` and its addendum).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldInvarianceCommutes

open Matrix GraphLaplacian FieldIsometryInvariance FieldCommutant FieldOrthIsometry
open FieldRotationCount MeasureTheory ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The adjoint of an isometry is its inverse -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem adjoint_coe (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    ContinuousLinearMap.adjoint (T.toContinuousLinearEquiv : EuclideanSpace ℝ V →L[ℝ]
      EuclideanSpace ℝ V) = (T.symm.toContinuousLinearEquiv : EuclideanSpace ℝ V →L[ℝ]
      EuclideanSpace ℝ V) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  calc inner ℝ (T.symm x) y = inner ℝ (T (T.symm x)) (T y) := (T.inner_map_map _ _).symm
    _ = inner ℝ x (T y) := by rw [T.apply_symm_apply]

/-! ## 2. Invariance forces the quadratic form, hence commuting -/

/-- **AN ISOMETRY WHOSE PUSHFORWARD FIXES THE GAUSSIAN FIELD PRESERVES THE PROPAGATOR'S QUADRATIC
FORM.** The covariance of a Gaussian measure is determined by the measure, and
`covarianceBilin_map` transports it through the adjoint. -/
theorem preservesQuadForm_of_gaussianField_map (hm : m ≠ 0)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : Measure.map T (gaussianField G m) = gaussianField G m) :
    PreservesQuadForm G m T := by
  intro t
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  have hL : Measure.map (T.toContinuousLinearEquiv : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
      (gaussianField G m) = gaussianField G m := hT
  have hmem : MemLp id 2 (gaussianField G m) := IsGaussian.memLp_two_id
  have key := covarianceBilin_map (μ := gaussianField G m) hmem
    (T.toContinuousLinearEquiv : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) t t
  rw [hL, adjoint_coe, gaussianField, covarianceBilin_multivariateGaussian hps,
    covarianceBilin_multivariateGaussian hps] at key
  exact key.symm

/-- **SO IT COMMUTES WITH THE PROPAGATOR.** -/
theorem commutes_of_gaussianField_map (hm : m ≠ 0)
    {T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V}
    (hT : Measure.map T (gaussianField G m) = gaussianField G m) (x : V → ℝ) :
    RayleighMatrix.mv (green G m) (T (WithLp.toLp 2 x))
      = T (RayleighMatrix.mv (green G m) (WithLp.toLp 2 x)) :=
  commutes_of_preservesQuadForm hm (preservesQuadForm_of_gaussianField_map hm hT) x

/-- **THE BICONDITIONAL: AN ISOMETRY IS A SYMMETRY OF THE GAUSSIAN FIELD IFF IT COMMUTES WITH THE
PROPAGATOR.** -/
theorem gaussianField_map_iff_commutes (hm : m ≠ 0)
    (T : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V) :
    Measure.map T (gaussianField G m) = gaussianField G m ↔
      ∀ x : EuclideanSpace ℝ V,
        RayleighMatrix.mv (green G m) (T x) = T (RayleighMatrix.mv (green G m) x) :=
  ⟨fun hT x => commutes_of_gaussianField_map hm hT (WithLp.ofLp x),
    fun hT => gaussianField_map_of_commutes hm hT⟩

/-! ## 3. So `symmetryMatrices` is the symmetry group, not a subset of it -/

/-- **FOR ORTHOGONAL MATRICES, `symmetryMatrices` IS EXACTLY THE SET WHOSE ISOMETRY FIXES THE
MEASURE.** Every lower bound this chain proved is a statement about the symmetry group itself. -/
theorem mem_symmetryMatrices_iff_gaussianField_map (hm : m ≠ 0) {R : Matrix V V ℝ}
    (hR : Rᵀ * R = 1) :
    R ∈ symmetryMatrices G m ↔
      Measure.map (orthIsometry hR) (gaussianField G m) = gaussianField G m := by
  constructor
  · exact fun hmem => gaussianField_map_of_mem hm hmem
  · intro hmap
    refine ⟨hR, ?_⟩
    refine (FieldCommutantSpectral.mul_green_comm_iff hm R).mpr fun x μ hx => ?_
    have hcomm := commutes_of_gaussianField_map hm hmap
    have : green G m *ᵥ (R *ᵥ x) = R *ᵥ (green G m *ᵥ x) := by
      have h := hcomm x
      simpa [RayleighMatrix.mv, orthIsometry] using h
    rw [this, hx, Matrix.mulVec_smul]

end FieldInvarianceCommutes
