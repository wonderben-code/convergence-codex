import LatticeGeneratingFunctional
import GreenDisconnected
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# The lattice field factorises across a reachability barrier

`FieldAutInvariance` delivered the finite-volume shadow of **OS3** and said in capitals that it was
not OS3. `LatticeGeneratingFunctional` did the same for **OS0**. This is the third of the four, and
it takes the same care.

The `UNLOCK_WATCHLIST` item for the OS axioms says of the three that are not OS2:

> **STILL OPEN: OS0** …, **OS1** …, **OS4** (clustering). **None attempted, none made easier.**

`OS0` has since been attempted. This attempts `OS4`'s finite-volume content.

## What is delivered

> **`generatingFunctional_add_of_orthogonal`** — if `⟪f, G g⟫ = 0` then
> `S(f + g) = S(f) · S(g)`.
>
> **`greenPairing_eq_zero_of_separated`** — that hypothesis holds whenever `f` and `g` are
> supported on opposite sides of a reachability barrier.
>
> **`generatingFunctional_add_of_separated`** — the two together.

## **THIS IS NOT OS4, AND MUST NOT BE RECORDED AS OS4**

OS4 is **asymptotic** clustering: correlations between observables tend to a product as their
supports are translated apart, in the infinite-volume limit. What is proved here is **exact**
factorisation across a barrier that is already total — two vertices with no path between them. A
finite graph has components where the continuum has distance, and *"the correlation vanishes because
there is no path"* is a different statement from *"the correlation decays because the path is
long"*.

The estate already has the second kind, and it is worth naming so the two are not confused:
`GreenDecay` and `TorusDecay` bound the propagator by the graph distance, and
`LatticeConnectedDecay`, `LatticeFourPointClustering` and `LatticeHigherClustering` carry that up
to moments. **All of those are statements about the COVARIANCE.** What is new here is the same move
`FieldAutInvariance` made for OS3: passing from a statement about the matrix to a statement about
the **field** — the generating functional itself factorises, which is independence of the two
families of observables, not a bound on one correlation.

## Why the barrier hypothesis is the honest one

`GreenDisconnected.green_eq_zero_of_not_reachable` is exact: the propagator is **zero**, not small,
between components. So the factorisation is exact, and stating it with an ε would be weaker and
less true.
-/

namespace LatticeFieldFactorises

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)

/-! ## 1. The Green pairing vanishes across a barrier -/

/-- **The cross term is zero when the supports are separated by reachability.** Every surviving
summand would need a source `u` with `f u ≠ 0` and a sink `v` with `g v ≠ 0`; the first is reachable
from `p` and the second is not, so `u` and `v` are unreachable from each other and the propagator
between them vanishes. -/
theorem greenPairing_eq_zero_of_separated (hm : m ≠ 0) (p : V)
    (f g : EuclideanSpace ℝ V)
    (hf : ∀ v, ¬ G.Reachable p v → f v = 0)
    (hg : ∀ v, G.Reachable p v → g v = 0) :
    (WithLp.ofLp f) ⬝ᵥ green G m *ᵥ (WithLp.ofLp g) = 0 := by
  simp only [dotProduct, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : G.Reachable p u
  · refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun v _ => ?_)
    by_cases hv : G.Reachable p v
    · rw [hg v hv, mul_zero]
    · have hnr : ¬ G.Reachable u v := fun h => hv (hu.trans h)
      rw [GreenDisconnected.green_eq_zero_of_not_reachable G hm hnr, zero_mul]
  · rw [hf u hu, zero_mul]

/-! ## 2. …so the generating functional factorises -/

/-- **`S(f + g) = S(f) · S(g)`** whenever the Green pairing of `f` and `g` vanishes. -/
theorem generatingFunctional_add_of_orthogonal (hm : m ≠ 0) (f g : EuclideanSpace ℝ V)
    (h : (WithLp.ofLp f) ⬝ᵥ green G m *ᵥ (WithLp.ofLp g) = 0) :
    ∫ ω, Real.exp ⟪f + g, ω⟫ ∂(gaussianField G m)
      = (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m))
        * (∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m)) := by
  rw [LatticeGeneratingFunctional.generatingFunctional hm,
    LatticeGeneratingFunctional.generatingFunctional hm,
    LatticeGeneratingFunctional.generatingFunctional hm, ← Real.exp_add]
  congr 1
  have hsymm : (WithLp.ofLp g) ⬝ᵥ green G m *ᵥ (WithLp.ofLp f)
      = (WithLp.ofLp f) ⬝ᵥ green G m *ᵥ (WithLp.ofLp g) := by
    simp only [dotProduct, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [(green_isSymm G hm).apply u v]
    ring
  have hadd : (WithLp.ofLp (f + g)) ⬝ᵥ green G m *ᵥ (WithLp.ofLp (f + g))
      = (WithLp.ofLp f) ⬝ᵥ green G m *ᵥ (WithLp.ofLp f)
        + (WithLp.ofLp g) ⬝ᵥ green G m *ᵥ (WithLp.ofLp g) := by
    simp only [WithLp.ofLp_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, h, hsymm]
    ring
  rw [hadd]
  ring

/-- **The two together**: the field's generating functional factorises across a reachability
barrier. -/
theorem generatingFunctional_add_of_separated (hm : m ≠ 0) (p : V) (f g : EuclideanSpace ℝ V)
    (hf : ∀ v, ¬ G.Reachable p v → f v = 0)
    (hg : ∀ v, G.Reachable p v → g v = 0) :
    ∫ ω, Real.exp ⟪f + g, ω⟫ ∂(gaussianField G m)
      = (∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m))
        * (∫ ω, Real.exp ⟪g, ω⟫ ∂(gaussianField G m)) :=
  generatingFunctional_add_of_orthogonal G m hm f g
    (greenPairing_eq_zero_of_separated G m hm p f g hf hg)

/-! ## 3. …and the observables are genuinely independent

Factorisation of the generating functional is a statement about one pair of observables. **Zero
covariance between jointly Gaussian variables is independence**, and Mathlib has that criterion
(`HasGaussianLaw.indepFun_of_covariance_eq_zero`), so the statement can be made about the
σ-algebras rather than about an integral. That is the strongest form of the finite-volume shadow
this file can carry — and it is still not OS4, for the reason the header gives.
-/

open LatticeGeneratingFunctional in
/-- **The covariance of two linear observables is the Green pairing.** The off-diagonal companion
of `LatticeGeneratingFunctional.variance_pair`, proved the same way. -/
theorem covariance_pair (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    cov[pair f, pair g; gaussianField G m]
      = (WithLp.ofLp f) ⬝ᵥ green G m *ᵥ (WithLp.ofLp g) := by
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  rw [show (⇑(pair f)) = (fun u => ⟪f, u⟫) from rfl,
    show (⇑(pair g)) = (fun u => ⟪g, u⟫) from rfl,
    ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, gaussianField,
    covarianceBilin_multivariateGaussian hps]

open LatticeGeneratingFunctional in
/-- **The two observables are jointly Gaussian**, being a continuous linear image of the field. -/
theorem hasGaussianLaw_pair (f g : EuclideanSpace ℝ V) :
    HasGaussianLaw (fun ω => (pair f ω, pair g ω)) (gaussianField G m) :=
  IsGaussian.hasGaussianLaw_id.map_fun ((pair f).prod (pair g))

open LatticeGeneratingFunctional in
/-- **INDEPENDENCE, not just factorisation.** Two linear observables of the lattice field on
opposite sides of a reachability barrier are independent. -/
theorem indepFun_pair_of_separated (hm : m ≠ 0) (p : V) (f g : EuclideanSpace ℝ V)
    (hf : ∀ v, ¬ G.Reachable p v → f v = 0)
    (hg : ∀ v, G.Reachable p v → g v = 0) :
    IndepFun (pair f) (pair g) (gaussianField G m) :=
  (hasGaussianLaw_pair G m f g).indepFun_of_covariance_eq_zero
    (by rw [covariance_pair G m hm]; exact greenPairing_eq_zero_of_separated G m hm p f g hf hg)

end LatticeFieldFactorises
