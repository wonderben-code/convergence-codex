import LatticeUniformStein
import LatticeFieldWitness
import BoxDegree
import TorusDecay

/-!
# The non-smooth observable's variance bound, and it is the degree

`LatticeUniformStein` closed with a caveat about its own reach:

> Applying this to `LatticeFieldWitness.absCoordField` gives a bound whose `L` involves `(√G)⁻¹`,
> and **nothing here analyses how that grows with the box**. It plausibly does not grow — `(√G)⁻¹`
> is controlled by the largest eigenvalue of `massive`, which a degree bound controls — but that is
> **not proved here and not costed**.

This file does that analysis, and the answer is **exact rather than an estimate**:

```
∑ⱼ ((√G)⁻¹ ⱼ ᵥ)²  =  deg(v) + m²
```

no inequality, no eigenvalue bound, no operator norm. So the witness's variance bound is

```
Var |((√G)⁻¹ ω) v|  ≤  m⁻² · (deg v + m²)
```

and on any family of graphs of bounded degree — `boxGraph` and `torusGraph` included — **that
constant does not grow with the box at all**.

## Why it is exact, which is the whole content

`√G` is symmetric and squares to `G`, so `(√G)⁻¹` is symmetric and squares to `G⁻¹ = massive`.
A column's sum of squares is then a **diagonal entry of `massive`** — by symmetry, `∑ⱼ Sⱼᵥ² =
∑ⱼ Sᵥⱼ Sⱼᵥ = (S·S)ᵥᵥ` — and `massive = lapMatrix + m²·1` has `deg v + m²` on the diagonal.

**The eigenvalue argument the caveat gestured at is not needed and is not used.** What looked like
an estimate about how `(√G)⁻¹` grows is an identity about one matrix entry.

*That is the **sixth** time on this chain that the anticipated obstacle or machinery turned out to
be unnecessary, and the ordinal is **counted rather than asserted** (`ERRATUM 183` — the first
draft of this paragraph said "fifth" with nothing behind it). The six: (1) the change of variables
was Mathlib's definition; (2) the measure identification was an existing lemma; (3) the hypothesis
class was not a class; (4) the gradient identity needed no gradients; (5) the measurable
equivalence needed no topology; (6) this. A reader can check the list against the four recorded on
the correlated-Poincaré watchlist item plus `LatticeSqrtEquiv`'s header.*

## What is proved

* `isSymm_sqrtInv`, `sqrtInv_mul_self` — `(√G)⁻¹` is symmetric and squares to `massive`;
* **`sum_sq_sqrtInv_col`** — the identity above, exactly;
* `sgn_sq_le_one`, `sum_sq_sgnCoordField_le` — the witness's tuple is bounded in `ℓ²` by
  `√(deg v + m²)`, pointwise;
* **`variance_absCoordField_le`** — the displayed variance bound;
* **`variance_absCoordField_le_of_degree`** — and at bounded degree, a constant naming only `Δ`
  and `m`: **a volume-uniform variance bound for an observable that is not differentiable.**
* **`variance_absCoordField_box`, `variance_absCoordField_torus`** — instantiated at the estate's
  own lattices, at every dimension and **every side length**, with `n` absent from the right-hand
  side. *Added in review: "the constant does not grow with the box" is this file's headline, and a
  headline should be a theorem rather than a remark about two lemmas elsewhere.*

## What this is NOT

**It is not a claim that this bound is sharp.** `poincare_uniform_stein` discards the propagator's
geometry and `sgn² ≤ 1` discards the sign, so two inequalities separate this from anything tight.
Nothing here says how much is lost.

**`OS4` does not move.** A volume-uniform bound on one observable is not a tightness argument; no
sequence of measures, no limit and no compactness appears here, as throughout this chain.

**No spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeWitnessBound

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeCorrelatedStein LatticeSqrtEquiv LatticeUniformStein LatticeFieldWitness
open LatticeGradientForm LatticeFieldProduct AbsSteinWitness
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. `(√G)⁻¹` squares to `massive` -/

theorem isUnit_det_green (hm : m ≠ 0) : IsUnit (green K m).det :=
  isUnit_iff_ne_zero.mpr (green_posDef K hm).det_pos.ne'

theorem isUnit_det_massive (hm : m ≠ 0) : IsUnit (massive K m).det :=
  isUnit_iff_ne_zero.mpr (massive_posDef K hm).det_pos.ne'

/-- The inverse of a symmetric matrix is symmetric. -/
theorem isSymm_sqrtInv : ((CFC.sqrt (green K m))⁻¹).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_nonsing_inv, isSymm_sqrt_green (G := K) (m := m)]

/-- **`(√G)⁻¹ · (√G)⁻¹ = massive`.** Inverting `√G·√G = G` and then `green = massive⁻¹`. -/
theorem sqrtInv_mul_self (hm : m ≠ 0) :
    (CFC.sqrt (green K m))⁻¹ * (CFC.sqrt (green K m))⁻¹ = massive K m := by
  have hsq : CFC.sqrt (green K m) * CFC.sqrt (green K m) = green K m :=
    sqrt_green_mul_self_general (H := K) hm
  have hrev : (CFC.sqrt (green K m) * CFC.sqrt (green K m))⁻¹
      = (CFC.sqrt (green K m))⁻¹ * (CFC.sqrt (green K m))⁻¹ := Matrix.mul_inv_rev _ _
  rw [← hrev, hsq, green, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_massive (K := K) hm)]

/-! ## 2. The column sum is a diagonal entry of `massive`, hence the degree -/

/-- **THE IDENTITY, AND IT IS AN EQUALITY.**
`∑ⱼ ((√G)⁻¹ ⱼ ᵥ)² = deg(v) + m²` — no estimate, no eigenvalue bound. -/
theorem sum_sq_sqrtInv_col (hm : m ≠ 0) (v : W) :
    ∑ j, ((CFC.sqrt (green K m))⁻¹ j v) ^ 2 = (K.degree v : ℝ) + m ^ 2 := by
  have hsym : ∀ a b, (CFC.sqrt (green K m))⁻¹ a b = (CFC.sqrt (green K m))⁻¹ b a := fun a b =>
    congrFun (congrFun (isSymm_sqrtInv (K := K) (m := m)) b) a
  have hdiag : ((CFC.sqrt (green K m))⁻¹ * (CFC.sqrt (green K m))⁻¹) v v
      = (K.degree v : ℝ) + m ^ 2 := by
    rw [sqrtInv_mul_self (K := K) hm, massive]
    simp [GraphLaplacian.lapMatrix_diag]
  rw [← hdiag, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hsym v j]; ring

/-! ## 3. The witness's tuple is bounded pointwise -/

theorem sgn_sq_le_one (t : ℝ) : sgn t ^ 2 ≤ 1 := by
  unfold sgn
  by_cases h1 : t < 0
  · simp [h1]
  · by_cases h2 : 0 < t <;> simp [h1, h2]

/-- The witness's gradient tuple has `ℓ²` norm at most `√(deg v + m²)`, at every point. -/
theorem sum_sq_sgnCoordField_le (hm : m ≠ 0) (v : W) (ω : EuclideanSpace ℝ W) :
    ∑ j, (sgnCoordField K m v j ω) ^ 2 ≤ (K.degree v : ℝ) + m ^ 2 := by
  have hfac : ∀ j, (sgnCoordField K m v j ω) ^ 2
      = ((CFC.sqrt (green K m))⁻¹ j v) ^ 2
        * sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v) ^ 2 := by
    intro j
    unfold sgnCoordField
    ring
  rw [show (∑ j, (sgnCoordField K m v j ω) ^ 2)
      = (∑ j, ((CFC.sqrt (green K m))⁻¹ j v) ^ 2)
        * sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v) ^ 2 by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => hfac j]
  rw [sum_sq_sqrtInv_col (K := K) hm v]
  have hnn : (0 : ℝ) ≤ (K.degree v : ℝ) + m ^ 2 := by positivity
  nlinarith [sgn_sq_le_one (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v),
    sq_nonneg (sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v))]

/-! ## 4. The variance bound -/

/-- **THE VARIANCE OF A NON-DIFFERENTIABLE OBSERVABLE OF THE LATTICE FIELD.**

`Var |((√G)⁻¹ ω) v| ≤ m⁻²·(deg v + m²)`, at every finite vertex type and every nonzero mass. -/
theorem variance_absCoordField_le (hm : m ≠ 0) (v : W) :
    (∫ ω, absCoordField K m v ω * absCoordField K m v ω ∂(gaussianField K m))
      - (∫ ω, absCoordField K m v ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ((K.degree v : ℝ) + m ^ 2) := by
  have hnn : (0 : ℝ) ≤ (K.degree v : ℝ) + m ^ 2 := by positivity
  have hL : ∀ ω, ∑ j, (sgnCoordField K m v j ω) ^ 2
      ≤ (Real.sqrt ((K.degree v : ℝ) + m ^ 2)) ^ 2 := by
    intro ω
    rw [Real.sq_sqrt hnn]
    exact sum_sq_sgnCoordField_le (K := K) hm v ω
  have := poincare_uniform_stein_of_bounded (K := K) hm
    (absCoordField_steinPairField (K := K) hm v) hL
  rwa [Real.sq_sqrt hnn] at this

/-- **AND AT BOUNDED DEGREE THE CONSTANT NAMES ONLY `Δ` AND `m`.**

So along any family of graphs of degree at most `Δ` the bound **does not grow with the box**: a
volume-uniform variance bound for an observable that is not differentiable. §5 instantiates it at
the estate's two lattices rather than leaving that as a remark. -/
theorem variance_absCoordField_le_of_degree (hm : m ≠ 0) (v : W) {Δ : ℕ}
    (hΔ : ∀ w : W, K.degree w ≤ Δ) :
    (∫ ω, absCoordField K m v ω * absCoordField K m v ω ∂(gaussianField K m))
      - (∫ ω, absCoordField K m v ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ((Δ : ℝ) + m ^ 2) := by
  refine (variance_absCoordField_le (K := K) hm v).trans ?_
  have hpos : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  have hdeg : (K.degree v : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ v
  exact mul_le_mul_of_nonneg_left (by linarith) hpos

/-! ## 5. At the estate's own lattices, where "does not grow with the box" is the point

The degree bounds are `BoxDegree.boxGraph_degree_le` and `TorusDecay.torusGraph_degree_le`, both
`≤ 2d` at **every** side length. Stated here rather than left in a docstring, because "the constant
does not grow with the box" is this file's headline and a headline should be a theorem. -/

/-- **ON THE BOX, AT EVERY SIDE LENGTH, THE SAME CONSTANT.** -/
theorem variance_absCoordField_box {d n : ℕ} (hm : m ≠ 0) (v : BoxGraph.Site d n) :
    (∫ ω, absCoordField (BoxGraph.boxGraph d n) m v ω
        * absCoordField (BoxGraph.boxGraph d n) m v ω ∂(gaussianField (BoxGraph.boxGraph d n) m))
      - (∫ ω, absCoordField (BoxGraph.boxGraph d n) m v ω
          ∂(gaussianField (BoxGraph.boxGraph d n) m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ((2 * d : ℕ) + m ^ 2) :=
  variance_absCoordField_le_of_degree hm v (fun w => BoxDegree.boxGraph_degree_le w)

/-- **AND ON THE PERIODIC BOX.** `n` does not appear on the right-hand side. -/
theorem variance_absCoordField_torus {d n : ℕ} (hm : m ≠ 0) (v : BoxGraph.Site d n) :
    (∫ ω, absCoordField (TorusReflection.torusGraph d n) m v ω
        * absCoordField (TorusReflection.torusGraph d n) m v ω
        ∂(gaussianField (TorusReflection.torusGraph d n) m))
      - (∫ ω, absCoordField (TorusReflection.torusGraph d n) m v ω
          ∂(gaussianField (TorusReflection.torusGraph d n) m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ((2 * d : ℕ) + m ^ 2) :=
  variance_absCoordField_le_of_degree hm v (fun w => TorusDecay.torusGraph_degree_le w)

end LatticeWitnessBound
