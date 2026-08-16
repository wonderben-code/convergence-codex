import LatticeWitnessBound
import LatticeIsserlisSmeared

/-!
# How much the Poincaré route loses on the witness: all of it

`LatticeWitnessBound` proved `Var |((√G)⁻¹ ω) v| ≤ m⁻²·(deg v + m²)` and closed with a caveat:

> **It is not a claim that this bound is sharp.** `poincare_uniform_stein` discards the
> propagator's geometry and `sgn² ≤ 1` discards the sign, so two inequalities separate this from
> anything tight. Nothing here says how much is lost.

This file says how much. The answer is that the general machinery is **badly** lossy on this
observable, and the reason is visible once the witness is looked at directly rather than through
the inequality:

```
∫ |((√G)⁻¹ ω) v|² dμ  =  1
```

**exactly** — no graph, no degree, no mass. Hence `Var ≤ 1`, an absolute constant, where the
Poincaré route gave `deg(v)/m² + 1`. The overshoot is the whole of `deg(v)/m²`.

## Why the second moment is exactly `1`

`((√G)⁻¹ ω) v` is **linear** in `ω` — it is the smeared field `⟪a, ω⟫` at `a = (√G)⁻¹`'s `v`-th
row. So `LatticeIsserlisSmeared.smeared_twoPoint` evaluates its second moment as `a ⬝ᵥ G *ᵥ a`,
and

```
(√G)⁻¹ · G · (√G)⁻¹  =  (√G)⁻¹ · √G · √G · (√G)⁻¹  =  1
```

so that quadratic form is the `(v,v)` entry of the identity. The absolute value never enters:
`|x|·|x| = x·x`, and the second moment cannot see the kink.

**AND THE LOSS IS LOCALISED TO ONE STEP, WHICH §5 PROVES RATHER THAN EXPLAINS.** The first draft
of this paragraph said the Poincaré route "could not have found this". **That is false**, and the
review caught it: the *sharp* inequality `Var ≤ ∫ γ ⬝ᵥ G *ᵥ γ` finds it perfectly well, because
`quadForm_sgnCoordField` shows that integrand is exactly `sgn²`, hence `≤ 1`. What loses is the
**single** step `∫ γ ⬝ᵥ G *ᵥ γ ≤ m⁻²·∑ⱼ γⱼ²` — the one that discards the propagator to buy a
graph-free constant — and on this observable the propagator is precisely what cancels. So the
`sgn² ≤ 1` step costs nothing, the sharp Poincaré inequality costs nothing, and `quadForm_green_le`
costs all of `deg(v)/m²`.

## What is proved

* `absCoordField_eq_abs_inner` — the witness is `|⟪a, ω⟫|` for an explicit `a`;
* `sqrtInv_mul_green_mul_sqrtInv` — `(√G)⁻¹ · G · (√G)⁻¹ = 1`;
* **`second_moment_absCoordField`** — `∫ Φ² dμ = 1`, an equality;
* **`variance_absCoordField_le_one`** — and therefore `Var Φ ≤ 1`, absolutely;
* **`poincare_bound_ge_one`, `poincare_bound_strictly_worse`** — the Poincaré constant is never
  smaller than `1`, and is **strictly** larger at any site with a neighbour. The loss is measured,
  not asserted;
* **`quadForm_sgnCoordField`, `sharp_poincare_integrand_le_one`** — and the loss is **localised**:
  the sharp inequality's integrand is exactly `sgn²`, so the sharp Poincaré route reaches `1` as
  well and the entire overshoot belongs to the uniform step.

## What this is NOT

**It does not compute the variance.** `Var = 1 − (∫Φ)²`, and `∫|⟪a,ω⟫|` is a Gaussian absolute
first moment — `√(2/π)` classically, making the variance `1 − 2/π`. **That integral is not
evaluated here**, so what is proved is the bound `Var ≤ 1` and not the exact value
(`ERRATUM 183`: the value is named as classical, not claimed as proved).

**It does not make `LatticeWitnessBound` wrong or redundant.** That unit's claim was about the
*general machinery* — that a volume-uniform constant exists at all, for every Stein pair. This unit
says that on *one* observable a direct computation beats it, and by how much. Both are true and
they are about different things: a general tool being lossy on a special case is the normal
situation, and the useful thing is to know the size of the gap.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeWitnessExact

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeFieldWitness LatticeWitnessBound LatticeIsserlisSmeared LatticeFieldProduct
open LatticeSqrtEquiv AbsSteinWitness
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The witness is the absolute value of a smeared field -/

/-- The `v`-th row of `(√G)⁻¹`, as a test function. -/
noncomputable def sqrtInvRow (K : SimpleGraph W) [DecidableRel K.Adj] (m : ℝ) (v : W) :
    EuclideanSpace ℝ W :=
  WithLp.toLp 2 (fun j => (CFC.sqrt (green K m))⁻¹ v j)

/-- **`|((√G)⁻¹ ω) v| = |⟪a, ω⟫|`.** The quantity inside the absolute value is linear in `ω`,
which is the observation the whole file rests on. -/
theorem absCoordField_eq_abs_inner (v : W) (ω : EuclideanSpace ℝ W) :
    absCoordField K m v ω = |(inner ℝ (sqrtInvRow K m v) ω : ℝ)| := by
  unfold absCoordField sqrtInvRow
  congr 1
  simp only [PiLp.inner_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun x _ => ?_
  exact ((RCLike.inner_apply (𝕜 := ℝ) ((CFC.sqrt (green K m))⁻¹ v x)
    (ω.ofLp x)).trans (by simp [mul_comm])).symm

/-! ## 2. The propagator cancels -/

/-- **`(√G)⁻¹ · G · (√G)⁻¹ = 1`.** Because `G = √G·√G` and the inverses meet it on both sides. -/
theorem sqrtInv_mul_green_mul_sqrtInv (hm : m ≠ 0) :
    (CFC.sqrt (green K m))⁻¹ * green K m * (CFC.sqrt (green K m))⁻¹ = 1 := by
  have hsq : CFC.sqrt (green K m) * CFC.sqrt (green K m) = green K m :=
    sqrt_green_mul_self_general (H := K) hm
  have hL : (CFC.sqrt (green K m))⁻¹ * CFC.sqrt (green K m) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_det_sqrt_green (K := K) hm)
  have hR : CFC.sqrt (green K m) * (CFC.sqrt (green K m))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (isUnit_det_sqrt_green (K := K) hm)
  have hexp : (CFC.sqrt (green K m))⁻¹ * green K m * (CFC.sqrt (green K m))⁻¹
      = (CFC.sqrt (green K m))⁻¹ * (CFC.sqrt (green K m) * CFC.sqrt (green K m))
        * (CFC.sqrt (green K m))⁻¹ := by rw [hsq]
  rw [hexp, ← Matrix.mul_assoc, hL, Matrix.one_mul, hR]

/-- The test function's own `G`-quadratic form is `1`. -/
theorem dotG_sqrtInvRow (hm : m ≠ 0) (v : W) :
    dotG K m (sqrtInvRow K m v) (sqrtInvRow K m v) = 1 := by
  have hsym : ∀ a b, (CFC.sqrt (green K m))⁻¹ a b = (CFC.sqrt (green K m))⁻¹ b a := fun a b =>
    congrFun (congrFun (isSymm_sqrtInv (K := K) (m := m)) b) a
  have hentry : ((CFC.sqrt (green K m))⁻¹ * green K m * (CFC.sqrt (green K m))⁻¹) v v = 1 := by
    rw [sqrtInv_mul_green_mul_sqrtInv (K := K) hm]
    simp
  rw [← hentry]
  unfold dotG sqrtInvRow
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec]
  have hLHS : (∑ i, (CFC.sqrt (green K m))⁻¹ v i
        * ∑ j, green K m i j * (CFC.sqrt (green K m))⁻¹ v j)
      = ∑ i, ∑ j, (CFC.sqrt (green K m))⁻¹ v i * green K m i j
          * (CFC.sqrt (green K m))⁻¹ v j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hRHS : (∑ k, (∑ i, (CFC.sqrt (green K m))⁻¹ v i * green K m i k)
        * (CFC.sqrt (green K m))⁻¹ k v)
      = ∑ k, ∑ i, (CFC.sqrt (green K m))⁻¹ v i * green K m i k
          * (CFC.sqrt (green K m))⁻¹ v k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [hsym k v]
  rw [hLHS, hRHS]
  exact Finset.sum_comm

/-! ## 3. The second moment, exactly -/

/-- **THE SECOND MOMENT IS `1`, AT EVERY GRAPH AND EVERY NONZERO MASS.**

`∫ |((√G)⁻¹ ω) v|² dμ = 1` — no degree, no mass, no geometry. The absolute value is invisible to
a second moment (`|x|·|x| = x·x`), and the propagator cancels against the two inverses. -/
theorem second_moment_absCoordField (hm : m ≠ 0) (v : W) :
    ∫ ω, absCoordField K m v ω * absCoordField K m v ω ∂(gaussianField K m) = 1 := by
  have hrw : ∀ ω : EuclideanSpace ℝ W,
      absCoordField K m v ω * absCoordField K m v ω
        = (inner ℝ (sqrtInvRow K m v) ω : ℝ) * (inner ℝ (sqrtInvRow K m v) ω : ℝ) := by
    intro ω
    rw [absCoordField_eq_abs_inner, abs_mul_abs_self]
  simp only [hrw]
  rw [smeared_twoPoint (G := K) hm, dotG_sqrtInvRow (K := K) hm]

/-- **AND SO THE VARIANCE IS AT MOST `1` — an absolute constant.** -/
theorem variance_absCoordField_le_one (hm : m ≠ 0) (v : W) :
    (∫ ω, absCoordField K m v ω * absCoordField K m v ω ∂(gaussianField K m))
      - (∫ ω, absCoordField K m v ω ∂(gaussianField K m)) ^ 2 ≤ 1 := by
  rw [second_moment_absCoordField (K := K) hm v]
  nlinarith [sq_nonneg (∫ ω, absCoordField K m v ω ∂(gaussianField K m))]

/-! ## 4. Measuring the loss -/

omit [DecidableEq W] in
/-- The Poincaré route's constant is never below `1`, so it never beats §3. -/
theorem poincare_bound_ge_one (hm : m ≠ 0) (v : W) :
    (1 : ℝ) ≤ (m ^ 2)⁻¹ * ((K.degree v : ℝ) + m ^ 2) := by
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  have hEq : (m ^ 2)⁻¹ * ((K.degree v : ℝ) + m ^ 2)
      = (m ^ 2)⁻¹ * (K.degree v : ℝ) + 1 := by
    field_simp
  have hnn : (0 : ℝ) ≤ (m ^ 2)⁻¹ * (K.degree v : ℝ) := by positivity
  linarith [hEq.ge, hEq.le]

omit [DecidableEq W] in
/-- **AND IT IS STRICTLY WORSE AT ANY SITE WITH A NEIGHBOUR**, by exactly `deg(v)/m²`.

So the gap between the two bounds is not a constant factor to be absorbed: on a `d`-dimensional
box at small mass it is `2d/m²`, and it grows without bound as `m → 0`. That is the size of what
`LatticeWitnessBound`'s caveat left unmeasured. -/
theorem poincare_bound_strictly_worse (hm : m ≠ 0) (v : W) (hv : 0 < K.degree v) :
    (1 : ℝ) < (m ^ 2)⁻¹ * ((K.degree v : ℝ) + m ^ 2) := by
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  have hdeg : (0 : ℝ) < (K.degree v : ℝ) := by exact_mod_cast hv
  have hEq : (m ^ 2)⁻¹ * ((K.degree v : ℝ) + m ^ 2)
      = (m ^ 2)⁻¹ * (K.degree v : ℝ) + 1 := by
    field_simp
  have hgt : (0 : ℝ) < (m ^ 2)⁻¹ * (K.degree v : ℝ) :=
    mul_pos (inv_pos.mpr hpos) hdeg
  linarith [hEq.ge, hEq.le]

/-! ## 5. Where the loss actually is

The sharp correlated inequality bounds the variance by `∫ γ ⬝ᵥ G *ᵥ γ`. On this observable that
integrand is **exactly** `sgn²`, so the sharp route reaches `1` too and loses nothing. The whole
overshoot measured in §4 therefore belongs to one step — `quadForm_green_le`, which trades the
propagator for `m⁻²`. -/

/-- **The sharp inequality's integrand is exactly `sgn²`.** The propagator cancels against the two
inverses, precisely as in §2. -/
theorem quadForm_sgnCoordField (hm : m ≠ 0) (v : W) (ω : EuclideanSpace ℝ W) :
    (fun j => sgnCoordField K m v j ω) ⬝ᵥ green K m *ᵥ (fun j => sgnCoordField K m v j ω)
      = sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v) ^ 2 := by
  have hsym : ∀ a b, (CFC.sqrt (green K m))⁻¹ a b = (CFC.sqrt (green K m))⁻¹ b a := fun a b =>
    congrFun (congrFun (isSymm_sqrtInv (K := K) (m := m)) b) a
  have hw : (fun j => sgnCoordField K m v j ω)
      = sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v)
        • (WithLp.ofLp (sqrtInvRow K m v)) := by
    funext j
    unfold sgnCoordField sqrtInvRow
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsym j v]
    ring
  rw [hw, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  have hdg := dotG_sqrtInvRow (K := K) hm v
  unfold dotG at hdg
  rw [hdg]
  ring

/-- **AND SO THE SHARP POINCARÉ ROUTE ALSO REACHES `1`.** The integrand is at most `1` pointwise,
so `Var ≤ ∫ 1 = 1` by the sharp inequality alone — no direct computation needed. **The `m⁻²` step
is the only lossy one.** -/
theorem sharp_poincare_integrand_le_one (hm : m ≠ 0) (v : W) (ω : EuclideanSpace ℝ W) :
    (fun j => sgnCoordField K m v j ω) ⬝ᵥ green K m *ᵥ (fun j => sgnCoordField K m v j ω) ≤ 1 := by
  rw [quadForm_sgnCoordField (K := K) hm v ω]
  exact sgn_sq_le_one _

end LatticeWitnessExact
