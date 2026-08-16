import LatticeMoments

/-!
# The connected four-point function of the lattice field

`LatticeMoments` (`57122f9`) proved `∫ ⟪f,ω⟫⁴ = 3·(fᵀGf)²` for every test function, and read it at
`f = δₚ` to get the estate's first individual higher correlation, `∫ (ω p)⁴ = 3·G(p,p)²`. Its
header named what it was not:

> *"Recovering the full symmetric 4-linear form from the quartic is **polarisation**, and
> polarisation of a quartic is sixteen terms, not four. It is not done here."*

`PROOF_STRATEGY` §3 says to re-attempt `B → C` the moment `B` lands. **This is that attempt, and it
reaches the TWO-SITE case**: `∫ (ω p)²(ω q)² = G(p,p)·G(q,q) + 2·G(p,q)²`, which is Isserlis for the
index pattern `(p,p,q,q)` — the three pairings `{pp}{qq}`, `{pq}{pq}`, `{pq}{pq}`.

## The polarisation that is actually needed is two terms, not sixteen

Sixteen is the count for four *distinct* vectors. For `(p,p,q,q)` the identity

    (a + b)⁴ + (a − b)⁴ − 2a⁴ − 2b⁴ = 12·a²b²

does it with **two** test functions, `δₚ + δ_q` and `δₚ − δ_q`, both of which `moment_four` already
evaluates. What the step costs is not algebra but **integrability**: turning that pointwise identity
into an identity between integrals needs each of the four terms integrable on its own.
`ProbabilityTheory.integrable_pow_of_mem_interior_integrableExpSet` supplies exactly that from the
hypothesis `LatticeMoments.zero_mem_interior_integrableExpSet` already establishes, so the
integrability is free and the unit is the bookkeeping.

## What is proved

* `integrable_pow_pair` — every power of every `⟪f,·⟫` is integrable;
* `inner_addSingle`, `inner_subSingle`, `linVar_addSingle`, `linVar_subSingle` — the two test
  functions and their variances, `G(p,p) ± 2G(p,q) + G(q,q)`, using `GraphLaplacian.green_isSymm`;
* `integral_polarisation` — the pointwise identity carried across the integral sign;
* **`isserlis_sq_sq`** — `∫ (ω p)²(ω q)² = G(p,p)·G(q,q) + 2·G(p,q)²`;
* **`connected_four_point`** — hence the TRUNCATED correlation
  `∫ (ω p)²(ω q)² − (∫ (ω p)²)(∫ (ω q)²) = 2·G(p,q)²`. **This is the one worth having**: the
  disconnected part cancels exactly, and what is left is the square of the two-point function.
* `connected_four_point_nonneg`, and `connected_four_point_eq_zero_iff` — it is never negative, and
  it vanishes exactly when the two sites are uncorrelated.

## What this is NOT

**It is still not Isserlis.** The general statement is
`E[ωₐω_bω_cω_d] = G_{ab}G_{cd} + G_{ac}G_{bd} + G_{ad}G_{bc}` at four arbitrary indices, and this
is the pattern `(p,p,q,q)`. The patterns `(p,p,p,q)` and `(p,q,r,s)` need three and fifteen further
polarisation terms respectively and are **not** proved here. What has changed since
`LatticeMoments` is that the two-site case is done and the method is visibly the same one; what has
not changed is that nobody has done the general count.

**And OS4 still does not move.** `connected_four_point` is a finite-volume identity. Composing it
with `GreenDecay.covariance_abs_le` would give exponential decay of the connected four-point
function — that composition is **not written here**, because `GreenDecay`'s bound is on the Green
function and this file does not import it; and even with it, OS4's two remaining pieces, the
infinite-volume limit and the continuum, are untouched. **No published tag moves.**
-/

namespace LatticeIsserlis

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian LatticeMoments

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Integrability, which is the only thing that is not algebra -/

/-- **EVERY POWER OF EVERY SMEARED FIELD IS INTEGRABLE.** From
`LatticeMoments.zero_mem_interior_integrableExpSet` and Mathlib's
`integrable_pow_of_mem_interior_integrableExpSet`. This is what makes the polarisation below an
identity between integrals rather than one between pointwise functions. -/
theorem integrable_pow_pair (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (n : ℕ) :
    Integrable (fun ω => (inner ℝ f ω : ℝ) ^ n) (gaussianField G m) :=
  integrable_pow_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet (G := G) hm f) n

/-- Integrability at a site, and at a sum or difference of two sites: the four functions the
polarisation needs. -/
theorem integrable_pow_of_eq (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (n : ℕ)
    {u : EuclideanSpace ℝ V → ℝ} (hu : ∀ ω, (inner ℝ f ω : ℝ) = u ω) :
    Integrable (fun ω => (u ω) ^ n) (gaussianField G m) :=
  (integrable_pow_pair (G := G) hm f n).congr
    (Filter.Eventually.of_forall fun ω => by simp only [hu])

/-! ## 2. The two test functions -/

theorem inner_addSingle (p q : V) (ω : EuclideanSpace ℝ V) :
    (inner ℝ (EuclideanSpace.single p (1 : ℝ) + EuclideanSpace.single q (1 : ℝ)) ω : ℝ)
      = ω p + ω q := by
  rw [inner_add_left, inner_single, inner_single]

theorem inner_subSingle (p q : V) (ω : EuclideanSpace ℝ V) :
    (inner ℝ (EuclideanSpace.single p (1 : ℝ) - EuclideanSpace.single q (1 : ℝ)) ω : ℝ)
      = ω p - ω q := by
  rw [inner_sub_left, inner_single, inner_single]

/-- The variance of `⟪δₚ + δ_q, ·⟫`. `green_isSymm` is what makes the two cross terms equal. -/
theorem linVar_addSingle (hm : m ≠ 0) (p q : V) :
    linVar G m (EuclideanSpace.single p (1 : ℝ) + EuclideanSpace.single q (1 : ℝ))
      = green G m p p + 2 * green G m p q + green G m q q := by
  have hs : green G m q p = green G m p q :=
    congrFun (congrFun (green_isSymm (G := G) hm) p) q
  simp [linVar, Matrix.mulVec_add, Matrix.mulVec_single, hs]
  ring

theorem linVar_subSingle (hm : m ≠ 0) (p q : V) :
    linVar G m (EuclideanSpace.single p (1 : ℝ) - EuclideanSpace.single q (1 : ℝ))
      = green G m p p - 2 * green G m p q + green G m q q := by
  have hs : green G m q p = green G m p q :=
    congrFun (congrFun (green_isSymm (G := G) hm) p) q
  simp [linVar, Matrix.mulVec_sub, Matrix.mulVec_single, hs]
  ring

/-! ## 3. The polarisation -/

/-- **THE POINTWISE IDENTITY, CARRIED ACROSS THE INTEGRAL SIGN.**
`(a+b)⁴ + (a−b)⁴ − 2a⁴ − 2b⁴ = 12 a²b²`, integrated. Each of the four terms on the left is
integrable by §1, which is why the split is legitimate. -/
theorem integral_polarisation (hm : m ≠ 0) (p q : V) :
    12 * ∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m)
      = (∫ ω, (ω p + ω q) ^ 4 ∂(gaussianField G m))
        + (∫ ω, (ω p - ω q) ^ 4 ∂(gaussianField G m))
        - 2 * (∫ ω, (ω p) ^ 4 ∂(gaussianField G m))
        - 2 * (∫ ω, (ω q) ^ 4 ∂(gaussianField G m)) := by
  have hA : Integrable (fun ω : EuclideanSpace ℝ V => (ω p + ω q) ^ 4) (gaussianField G m) :=
    integrable_pow_of_eq (G := G) hm _ 4 (inner_addSingle p q)
  have hB : Integrable (fun ω : EuclideanSpace ℝ V => (ω p - ω q) ^ 4) (gaussianField G m) :=
    integrable_pow_of_eq (G := G) hm _ 4 (inner_subSingle p q)
  have hC : Integrable (fun ω : EuclideanSpace ℝ V => (ω p) ^ 4) (gaussianField G m) :=
    integrable_pow_of_eq (G := G) hm _ 4 (inner_single p)
  have hD : Integrable (fun ω : EuclideanSpace ℝ V => (ω q) ^ 4) (gaussianField G m) :=
    integrable_pow_of_eq (G := G) hm _ 4 (inner_single q)
  have hsum : Integrable
      (fun ω : EuclideanSpace ℝ V => (ω p + ω q) ^ 4 + (ω p - ω q) ^ 4) (gaussianField G m) :=
    hA.add hB
  have hrest : Integrable
      (fun ω : EuclideanSpace ℝ V => 2 * (ω p) ^ 4 + 2 * (ω q) ^ 4) (gaussianField G m) :=
    (hC.const_mul 2).add (hD.const_mul 2)
  have hpt : ∀ ω : EuclideanSpace ℝ V,
      ((ω p + ω q) ^ 4 + (ω p - ω q) ^ 4) - (2 * (ω p) ^ 4 + 2 * (ω q) ^ 4)
        = 12 * ((ω p) ^ 2 * (ω q) ^ 2) := fun ω => by ring
  have hstep := integral_sub hsum hrest
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hstep
  rw [integral_const_mul, integral_add hA hB, integral_add (hC.const_mul 2) (hD.const_mul 2),
    integral_const_mul, integral_const_mul] at hstep
  rw [hstep]
  ring

/-- **ISSERLIS FOR THE PATTERN `(p,p,q,q)`.** `∫ (ω p)²(ω q)² = G(p,p)·G(q,q) + 2·G(p,q)²` — the
three pairings of four points into two, with the middle two equal.

`GraphLaplacian.twoPoint` is the two-point function; `LatticeMoments.moment_four_single` is the
one-site fourth moment; this is the first correlation of order four **at two different sites**. -/
theorem isserlis_sq_sq (hm : m ≠ 0) (p q : V) :
    ∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m)
      = green G m p p * green G m q q + 2 * (green G m p q) ^ 2 := by
  have hA := moment_four (G := G) hm
    (EuclideanSpace.single p (1 : ℝ) + EuclideanSpace.single q (1 : ℝ))
  have hB := moment_four (G := G) hm
    (EuclideanSpace.single p (1 : ℝ) - EuclideanSpace.single q (1 : ℝ))
  rw [linVar_addSingle hm p q] at hA
  rw [linVar_subSingle hm p q] at hB
  have hA' : ∫ ω, (ω p + ω q) ^ 4 ∂(gaussianField G m)
      = 3 * (green G m p p + 2 * green G m p q + green G m q q) ^ 2 :=
    Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [inner_addSingle p q ω])) hA
  have hB' : ∫ ω, (ω p - ω q) ^ 4 ∂(gaussianField G m)
      = 3 * (green G m p p - 2 * green G m p q + green G m q q) ^ 2 :=
    Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      simp only [inner_subSingle p q ω])) hB
  have hpol := integral_polarisation (G := G) hm p q
  rw [hA', hB', moment_four_single hm p, moment_four_single hm q] at hpol
  linarith [hpol]

/-! ## 4. The truncated correlation, which is the one that means something -/

/-- **THE CONNECTED FOUR-POINT FUNCTION IS `2·G(p,q)²`.**

The disconnected part `(∫ω_p²)(∫ω_q²) = G(p,p)G(q,q)` cancels exactly, and what survives is twice
the square of the two-point function. **That is the statement a clustering argument consumes**: a
connected correlation controlled by the square of a quantity that already has a decay estimate
(`GreenDecay`). The composition is not made here — see the file header. -/
theorem connected_four_point (hm : m ≠ 0) (p q : V) :
    (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (ω p) ^ 2 ∂(gaussianField G m)) * (∫ ω, (ω q) ^ 2 ∂(gaussianField G m))
      = 2 * (green G m p q) ^ 2 := by
  have hp : ∫ ω, (ω p) ^ 2 ∂(gaussianField G m) = green G m p p := by
    have := GraphLaplacian.twoPoint G hm p p
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  have hq : ∫ ω, (ω q) ^ 2 ∂(gaussianField G m) = green G m q q := by
    have := GraphLaplacian.twoPoint G hm q q
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  rw [isserlis_sq_sq hm p q, hp, hq]
  ring

/-- And it is never negative. -/
theorem connected_four_point_nonneg (hm : m ≠ 0) (p q : V) :
    0 ≤ (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (ω p) ^ 2 ∂(gaussianField G m)) * (∫ ω, (ω q) ^ 2 ∂(gaussianField G m)) := by
  rw [connected_four_point hm p q]
  positivity

/-- **AND IT VANISHES EXACTLY WHEN THE TWO SITES ARE UNCORRELATED.** So the connected four-point
function carries no information the two-point function does not — which is the content of the field
being Gaussian, stated as a biconditional rather than asserted. -/
theorem connected_four_point_eq_zero_iff (hm : m ≠ 0) (p q : V) :
    (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (ω p) ^ 2 ∂(gaussianField G m)) * (∫ ω, (ω q) ^ 2 ∂(gaussianField G m)) = 0
      ↔ green G m p q = 0 := by
  rw [connected_four_point hm p q]
  constructor
  · intro h
    have h2 : (green G m p q) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  · intro h; rw [h]; ring

end LatticeIsserlis
