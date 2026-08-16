import LatticeCorrelatedStein

/-!
# `√G` is invertible, and the two side conditions come off

`LatticeCorrelatedStein.poincare_correlated_stein` carries two a.e.-strong-measurability
hypotheses on `Φ` and on each `γ j` against the field. Its header says exactly why they are there
and exactly what would remove them:

> Deriving them instead would need `y ↦ √G y` to be a measurable embedding — true at `m ≠ 0`,
> since `green` is positive definite — and that is **not proved here and not costed**.

This file proves it and removes them. **`poincare_correlated_stein_of_class` has the Stein pair
condition as its only hypothesis besides `m ≠ 0`.**

## The route, which needs no topology

`√G·√G = G` and `G` is positive definite, so `det(√G)² = det G > 0` and `√G` is invertible. The
change of variables is then a **bijection with an explicit inverse** — `ω ↦ (√G)⁻¹ ω` — and both
directions are linear on a finite-dimensional space, hence measurable. That is a `MeasurableEquiv`
built by hand, and `MeasurableEquiv.measurableEmbedding` finishes it. No continuous linear
equivalence, no finite-dimensionality lemma, no `Homeomorph`.

`MeasurableEmbedding.memLp_map_measure_iff` then transports square-integrability across the change
of variables **with no measurability hypothesis of its own**, which is what makes the removal
possible rather than merely convenient.

## The gradient tuple comes back too, and that is the part with content

`SteinPairField` constrains only the *combination* `i ↦ ∑ⱼ γⱼ(√G ·)·(√G eᵢ)ⱼ`, not the individual
`γ j`. Reading `(√G *ᵥ eᵢ)ⱼ = √G ⱼ ᵢ` and using symmetry, that combination is exactly
`√G *ᵥ γ(√G ·)` — so **invertibility recovers each `γ j` as a linear combination of the tuple**
(`memLp_gamma_comp`), and square-integrability of the individual `γ j` follows from
square-integrability of the combination.

*Precisely which thing needs invertibility: the **recovery argument**, not the conclusion. A
singular `√G` makes the combination blind to `ker √G`, so this route to the individual `γ j` would
be unavailable — that is a statement about the proof, and no claim is made here that the
conclusion would then fail. The first draft of this paragraph said "this step is false", which a
reader could take as a claim about the theorem; the review corrected the scope rather than the
substance.*

## What is proved

* `isUnit_det_sqrt_green`, `sqrtGreenEquiv`, `measurableEmbedding_sqrtMap` — the change of
  variables is a measurable equivalence at every nonzero mass;
* `memLp_field_of_comp` — square-integrability transports back to the field, no hypothesis;
* `memLp_phi`, `memLp_gamma` — `Φ` and each `γ j` are in `L²` **against the field**, from the class
  alone;
* **`poincare_correlated_stein_of_class`** — the correlated Poincaré inequality on the Stein class
  with the two side conditions **gone**, and a machine-checked `example` confirming it implies the
  previous statement.

## What this is NOT

~~**It is still not a proof that the class at the field is strictly wider than `C¹`.** ... what it
does is supply the invertibility that a witness would need, since the natural candidate is
`ω ↦ |((√G)⁻¹ ω) v|` ... **That witness is not constructed here.**~~

**SUPERSEDED — THE WITNESS IS NOW BUILT, AND IT IS THE CANDIDATE NAMED ABOVE.**
`LatticeFieldWitness` defines exactly `ω ↦ |((√G)⁻¹ ω) v|`, proves it is a Stein pair against the
field, proves it is not `ContDiff ℝ 1`, and concludes the class is strictly wider. Kept per
`ERRATUM 94`. **The sentence "naming a route is not walking it" stands unamended** — it was the
right caution at the time, and the route being walked one unit later does not make refusing to
claim it in advance wrong.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeSqrtEquiv

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian GaussianProductMeasure
open LatticeFieldProduct LatticeGradientForm LatticeCorrelatedPoincare
open LatticeSteinPoincarePi LatticePoincarePi LatticeCorrelatedStein
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. `√G` is invertible -/

/-- **`det √G ≠ 0`.** Squaring the determinant gives `det G`, which is positive because `G` is. -/
theorem isUnit_det_sqrt_green (hm : m ≠ 0) : IsUnit (CFC.sqrt (green K m)).det := by
  rw [isUnit_iff_ne_zero]
  intro h
  have hprod : (CFC.sqrt (green K m)).det * (CFC.sqrt (green K m)).det = (green K m).det := by
    rw [← Matrix.det_mul, sqrt_green_mul_self_general (H := K) hm]
  rw [h, mul_zero] at hprod
  exact absurd hprod.symm (green_posDef K hm).det_pos.ne'

/-- **The change of variables is a measurable equivalence**, with the explicit inverse
`ω ↦ (√G)⁻¹ ω`. Both directions are linear in finitely many coordinates, so measurability is
automatic; no topology is used. -/
noncomputable def sqrtGreenEquiv (hm : m ≠ 0) : (W → ℝ) ≃ᵐ EuclideanSpace ℝ W where
  toFun y := WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)
  invFun ω := (CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)
  left_inv y := by
    simp only [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (isUnit_det_sqrt_green (K := K) hm), Matrix.one_mulVec]
  right_inv ω := by
    simp only [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_det_sqrt_green (K := K) hm), Matrix.one_mulVec,
      WithLp.toLp_ofLp]
  measurable_toFun := by
    have hM : Measurable fun y : W → ℝ =>
        WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y) := by fun_prop
    exact hM
  measurable_invFun := by
    have hM : Measurable fun ω : EuclideanSpace ℝ W =>
        (CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω) := by fun_prop
    exact hM

@[simp] theorem sqrtGreenEquiv_apply (hm : m ≠ 0) (y : W → ℝ) :
    sqrtGreenEquiv (K := K) hm y = WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y) := rfl

/-- **And therefore a measurable embedding**, which is the form the `L²` transport wants. -/
theorem measurableEmbedding_sqrtMap (hm : m ≠ 0) :
    MeasurableEmbedding
      (fun y : W → ℝ => WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)) :=
  (sqrtGreenEquiv (K := K) hm).measurableEmbedding

/-! ## 2. Square-integrability transports back to the field, with no hypothesis -/

/-- The pushforward identity, in the direction this file uses. -/
theorem map_sqrt_eq_field :
    Measure.map (fun y : W → ℝ => WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)) (gaussPiOf W)
      = gaussianField K m :=
  (LatticeFieldProduct.gaussianField_eq_map_pi (H := K) (m := m)).symm

/-- **`MemLp` against the field from `MemLp` of the composition** — no measurability hypothesis,
because `MeasurableEmbedding.memLp_map_measure_iff` asks for none. -/
theorem memLp_field_of_comp (hm : m ≠ 0) {u : EuclideanSpace ℝ W → ℝ}
    (hu : MemLp (fun y => u (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))) 2 (gaussPiOf W)) :
    MemLp u 2 (gaussianField K m) := by
  have hiff := (measurableEmbedding_sqrtMap (K := K) hm).memLp_map_measure_iff
    (μ := gaussPiOf W) (g := u) (p := 2)
  rw [map_sqrt_eq_field (K := K) (m := m)] at hiff
  exact hiff.mpr hu

/-! ## 3. The class alone gives `L²` for `Φ` and for every `γ j` -/

variable {Φ : EuclideanSpace ℝ W → ℝ} {γ : W → EuclideanSpace ℝ W → ℝ}

/-- `Φ` is square-integrable against the field, from the class alone. -/
theorem memLp_phi (hm : m ≠ 0) (h : SteinPairField K m Φ γ) :
    MemLp Φ 2 (gaussianField K m) :=
  memLp_field_of_comp (K := K) hm h.memLp

/-- **The tuple's components are recovered by inverting `√G`.**

`SteinPairField` constrains only `i ↦ ∑ⱼ γⱼ(√G ·)·(√G eᵢ)ⱼ`, which is `√G *ᵥ γ(√G ·)` once
`(√G *ᵥ eᵢ)ⱼ = √G ⱼ ᵢ` and symmetry are used. Multiplying by `(√G)⁻¹` returns each component as a
finite linear combination of square-integrable functions. **This step is false, not merely
unproved, for a singular `√G`.** -/
theorem memLp_gamma_comp (hm : m ≠ 0) (h : SteinPairField K m Φ γ) (j : W) :
    MemLp (fun y : W → ℝ => γ j (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))) 2 (gaussPiOf W) := by
  classical
  have hcomb : ∀ i : W, MemLp (fun y : W → ℝ =>
      ∑ k, γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
        * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) k) 2 (gaussPiOf W) := h.memLp_grad
  -- the combination is `√G *ᵥ γ(√G ·)`, read entrywise
  have hentry : ∀ (i : W) (y : W → ℝ),
      (∑ k, γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
        * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) k)
      = (CFC.sqrt (green K m) *ᵥ
          fun k => γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))) i := by
    intro i y
    have hsym : ∀ a b, CFC.sqrt (green K m) a b = CFC.sqrt (green K m) b a := fun a b =>
      congrFun (congrFun (isSymm_sqrt_green (G := K) (m := m)) b) a
    have hcol : ∀ k, (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) k
        = CFC.sqrt (green K m) k i := by
      intro k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    simp only [hcol]
    change _ = ∑ k, CFC.sqrt (green K m) i k
      * γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
    exact Finset.sum_congr rfl fun k _ => by rw [hsym k i]; ring
  -- invert
  have hrw : (fun y : W → ℝ => γ j (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)))
      = fun y => ∑ i, (CFC.sqrt (green K m))⁻¹ j i
          * ∑ k, γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
              * (CFC.sqrt (green K m) *ᵥ Pi.single i (1 : ℝ)) k := by
    funext y
    simp only [hentry]
    have hinv : ((CFC.sqrt (green K m))⁻¹ *ᵥ (CFC.sqrt (green K m) *ᵥ
        fun k => γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))))
        = fun k => γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_sqrt_green (K := K) hm),
        Matrix.one_mulVec]
    calc γ j (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y))
        = ((CFC.sqrt (green K m))⁻¹ *ᵥ (CFC.sqrt (green K m) *ᵥ
            fun k => γ k (WithLp.toLp 2 (CFC.sqrt (green K m) *ᵥ y)))) j := by rw [hinv]
      _ = _ := rfl
  rw [hrw]
  exact memLp_finset_sum _ fun i _ => (hcomb i).const_mul _

/-- Each `γ j` is square-integrable against the field, from the class alone. -/
theorem memLp_gamma (hm : m ≠ 0) (h : SteinPairField K m Φ γ) (j : W) :
    MemLp (γ j) 2 (gaussianField K m) :=
  memLp_field_of_comp (K := K) hm (memLp_gamma_comp (K := K) hm h j)

/-! ## 4. The inequality, with the side conditions gone -/

/-- **THE CORRELATED POINCARÉ INEQUALITY ON THE STEIN CLASS, WITH NO SIDE CONDITIONS.**

`∫Φ² − (∫Φ)² ≤ ∫ γ ⬝ᵥ G *ᵥ γ` against `gaussianField K m`, whose only hypotheses are `m ≠ 0` and
membership of the class. The two measurability conditions `LatticeCorrelatedStein` carried are
supplied by §3 rather than assumed. -/
theorem poincare_correlated_stein_of_class (hm : m ≠ 0) (h : SteinPairField K m Φ γ) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m)) - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ ∫ ω, (fun j => γ j ω) ⬝ᵥ green K m *ᵥ (fun j => γ j ω) ∂(gaussianField K m) :=
  poincare_correlated_stein hm (memLp_phi (K := K) hm h).1
    (fun j => (memLp_gamma (K := K) hm h j).1) h

/-- **The strengthening is machine-checked**: the previous statement is exactly this one with two
hypotheses that §3 now proves, so anything the old theorem concluded, the new one concludes from
strictly less. -/
example (hm : m ≠ 0) (hΦm : AEStronglyMeasurable Φ (gaussianField K m))
    (hγm : ∀ j, AEStronglyMeasurable (γ j) (gaussianField K m))
    (h : SteinPairField K m Φ γ) :
    poincare_correlated_stein hm hΦm hγm h
      = poincare_correlated_stein_of_class hm h := rfl

end LatticeSqrtEquiv
