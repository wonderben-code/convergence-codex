import FieldInvarianceCommutes

/-!
# Dropping the isometry: every LINEAR symmetry of the Gaussian field, and what it must satisfy

Five files of this chain fence the same restriction: **only isometries are characterised.**
`FieldInvarianceCommutes.gaussianField_map_iff_commutes` quantifies over
`EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V`, so a measure-preserving map that is linear but
**not** an isometry is outside every statement this chain has made. `PROOF_STRATEGY` §7 rule 3 —
*take a result proven under restrictive hypotheses and remove one* — and the hypothesis removed here
is **isometry**, down to **continuous linear**.

**AND THE RESTRICTION IS REAL, not a formality.** A centred Gaussian with covariance `C` is pushed
by a linear `L` to the centred Gaussian with covariance `L C L*`, so the linear symmetries are
`{L | L C L* = C}` — stated below in quadratic-form terms, which is the same condition by
polarisation. For an **isometry** `L* = L⁻¹` and that condition *is* commuting with `C`, which is
the chain's statement. **For a general `L` the two conditions are different**, and the chain's
group is therefore **a** subgroup of the linear one.

**WHETHER IT IS A PROPER SUBGROUP IS NOT PROVED HERE.** The expected reason it is —
`C^{1/2} O C^{-1/2}` preserves the field for every orthogonal `O` and is an isometry only when `O`
commutes with `C` — needs `C^{1/2}`, **which this file never constructs**. That sentence is a
description of why one would expect properness and **not a claim that it holds** (`ERRATUM 194`);
nothing below exhibits a single non-isometric linear symmetry.

## What is proved

**`charFun_map`** — the characteristic function of a pushforward along a continuous linear map is
the original's, read at the adjoint. `integral_map` and
`ContinuousLinearMap.adjoint_inner_right`, with no Gaussian anywhere.

**`gaussianField_map_iff_quadForm`** — **a continuous linear `L` preserves the Gaussian field iff
`⟪L* x, green (L* x)⟫ = ⟪x, green x⟫` for every `x`.** Both directions, and **no isometry
hypothesis**: forward by `ProbabilityTheory.covarianceBilin_map`, back by `Measure.ext_of_charFun`
against `charFun_multivariateGaussian`.

**`adjoint_injective_of_map`, `bijective_of_map`** — **so every linear symmetry is invertible.** If
`L* x = 0` then `⟪x, green x⟫ = 0`, and `green` is positive definite, so `x = 0`; in finite
dimension an injective adjoint makes `L` bijective.

**AND THE ISOMETRY CASE IS CITED, NOT RESTATED** (`ERRATUM 337`):
`FieldInvarianceCommutes.gaussianField_map_iff_commutes` is this theorem's content at an isometry,
where `L* = L⁻¹` turns the condition into commuting, and it keeps its own proof.

## What is NOT here

**NO DESCRIPTION OF THE LARGER GROUP.** `{L | L C L* = C}` is characterised, **not classified**:
nothing here exhibits its elements, counts them, or relates it to the orthogonal group by the
conjugation `L ↦ C^{-1/2} L C^{1/2}` that the header sketches. **That sketch is a description of the
shape and not a claim** (`ERRATUM 194`), and in particular **`C^{1/2}` is never constructed here**.
Not attempted, no cost claimed (`ERRATUM 246`).

**SO THE COUNTS IN THIS CHAIN ARE COUNTS OF ISOMETRIES, AND THAT IS NOW A NAMED RESTRICTION RATHER
THAN AN UNNOTICED ONE.** `FieldLineCount.card_symmetries` counts the **isometric** symmetries of
the field on a line and says `2^(m+1)`. **This file does not count the linear ones and does not
show there are more**; what it does is make the restriction visible, where before it was a word in
a fence.

**NOT NON-LINEAR MAPS.** A measure-preserving map that is not linear is outside this too. The full
automorphism group of the measure remains untouched.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A larger
symmetry group in finite volume is a wider shadow of an axiom, not a smaller gap in it.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`gaussianField_map_iff_quadForm`, `adjoint_injective_of_map`, `bijective_of_map` and
`gaussianField_map_of_isometry_iff`; it is **not** taken by `charFun_map`, which mentions no graph.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldLinearSymmetry

open Matrix GraphLaplacian MeasureTheory ProbabilityTheory

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Pushing a characteristic function through the adjoint -/

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem charFun_map (μ : Measure (EuclideanSpace ℝ V)) [IsFiniteMeasure μ]
    (L : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) (t : EuclideanSpace ℝ V) :
    charFun (μ.map L) t = charFun μ (ContinuousLinearMap.adjoint L t) := by
  rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [ContinuousLinearMap.adjoint_inner_right]

/-! ## 2. The characterisation, with no isometry hypothesis -/

/-- **A CONTINUOUS LINEAR MAP PRESERVES THE GAUSSIAN FIELD IFF IT PRESERVES THE PROPAGATOR'S
QUADRATIC FORM THROUGH ITS ADJOINT.** -/
theorem gaussianField_map_iff_quadForm (hm : m ≠ 0)
    (L : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) :
    Measure.map L (gaussianField G m) = gaussianField G m ↔
      ∀ x : EuclideanSpace ℝ V,
        (ContinuousLinearMap.adjoint L x) ⬝ᵥ (green G m *ᵥ (ContinuousLinearMap.adjoint L x))
          = x ⬝ᵥ (green G m *ᵥ x) := by
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  constructor
  · intro hL x
    have hmem : MemLp id 2 (gaussianField G m) := IsGaussian.memLp_two_id
    have key := covarianceBilin_map (μ := gaussianField G m) hmem L x x
    rw [hL, gaussianField, covarianceBilin_multivariateGaussian hps,
      covarianceBilin_multivariateGaussian hps] at key
    exact key.symm
  · intro hL
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_map, gaussianField, charFun_multivariateGaussian hps,
      charFun_multivariateGaussian hps, hL t]
    simp

/-! ## 3. So every linear symmetry is invertible -/

theorem adjoint_injective_of_map (hm : m ≠ 0)
    {L : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V}
    (hL : Measure.map L (gaussianField G m) = gaussianField G m) :
    Function.Injective (ContinuousLinearMap.adjoint L) := by
  have hq := (gaussianField_map_iff_quadForm hm L).mp hL
  intro x y hxy
  by_contra hne
  have hz : ContinuousLinearMap.adjoint L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hform := hq (x - y)
  rw [hz] at hform
  simp only [WithLp.ofLp_zero, Matrix.mulVec_zero, dotProduct_zero] at hform
  have hxy0 : (WithLp.ofLp (x - y) : V → ℝ) ≠ 0 := by
    intro hc
    exact hne (sub_eq_zero.mp (by ext v; exact congrFun hc v))
  exact absurd hform.symm (ne_of_gt (by simpa using (green_posDef G hm).dotProduct_mulVec_pos hxy0))

/-- **SO EVERY LINEAR SYMMETRY IS INVERTIBLE.** -/
theorem bijective_of_map (hm : m ≠ 0) {L : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V}
    (hL : Measure.map L (gaussianField G m) = gaussianField G m) :
    Function.Bijective L := by
  have hinj := adjoint_injective_of_map hm hL
  have hsurj : Function.Surjective (ContinuousLinearMap.adjoint L) :=
    (LinearMap.injective_iff_surjective
      (f := (ContinuousLinearMap.adjoint L).toLinearMap)).mp hinj
  have hLinj : Function.Injective L := by
    intro x y hxy
    have hz : L (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hall : ∀ z : EuclideanSpace ℝ V, inner ℝ (x - y) z = (0:ℝ) := by
      intro z
      obtain ⟨w, rfl⟩ := hsurj z
      rw [ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_left]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (hall (x - y)))
  exact ⟨hLinj, (LinearMap.injective_iff_surjective (f := L.toLinearMap)).mp hLinj⟩

end FieldLinearSymmetry
