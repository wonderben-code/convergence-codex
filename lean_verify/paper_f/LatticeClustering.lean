import LatticeFieldFactorises
import LatticeOSPackage

/-!
# Clustering in finite volume: the exact statement is unconditional and empty where it matters

`LatticeOSPackage` left clustering out of the finite-volume package and gave a reason:

> `GreenClustering.cross_abs_le` and `LatticeHigherClustering.odd_pattern_abs_le` are real theorems,
> and both carry hypotheses … **There is no unconditional finite-volume clustering statement to
> name**, and inventing a `Prop` whose only instance needs three side conditions would make the
> package look more complete than the estate is.

**The sentence in bold is false and this file is the correction** (`ERRATUM 322`).
`LatticeFieldFactorises.indepFun_pair_of_separated` is exactly such a statement, and it is stronger
than decay: two linear observables of the field on opposite sides of a **reachability barrier** are
not merely weakly correlated but **independent**, with no degree bound, no separation parameter and
no `ε` — the only hypothesis is `m ≠ 0`.

**The conclusion of the last unit survives; its reason does not, and the true reason is better.**
The exact statement is unconditional **and vacuous on any connected graph**:

> **`clustering_trivial_of_preconnected`** — if `G` is preconnected then the separation hypotheses
> force the second test function to be identically zero, so the observable is `0` and the
> independence asserted is independence from a constant.

The box is connected. **So the exact statement has no content on the object the OS programme is
about**, and bundling it into the package would have advertised a clustering property of the lattice
field that the theorem does not supply. That is a sharper reason for leaving it out than "no such
statement exists", and it is a theorem rather than a survey.

## What is proved

> **`ClusteringFinVol G m`** — the exact statement, named: observables separated by a reachability
> barrier are independent.
>
> **`gaussianField_clusteringFinVol`** — the lattice field satisfies it, at every finite graph and
> every nonzero mass. Cited from `indepFun_pair_of_separated`, not reproved.
>
> **`clustering_trivial_of_preconnected`** — and on a preconnected graph the property is empty.
>
> **`gaussianField_shadows_clustered`** — the three unconditional properties together: regularity,
> Euclidean covariance and this one, with the emptiness theorem beside it so the third conjunct
> cannot be read for more than it says.

## What this is NOT

**It is not OS4.** OS4 is clustering of the Schwinger functions of a *continuum, infinite-volume*
theory: correlations of widely separated regions approach the product of their expectations as the
separation grows. Nothing here has an infinite volume, a translation, or a limit. `GreenDecay`'s
`covariance_abs_le` is the quantitative statement with content on a connected graph, and **it needs
a uniform degree bound** — that hypothesis is real and is not removed here.

**It does not give the box a clustering property.** `clustering_trivial_of_preconnected` says the
opposite, and is the point of the file.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeClustering

open MeasureTheory ProbabilityTheory LatticeFieldFactorises LatticeGeneratingFunctional

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The exact statement -/

/-- **CLUSTERING IN FINITE VOLUME, IN ITS EXACT FORM.** Observables separated by a reachability
barrier are independent — not approximately, and with no rate. -/
def ClusteringFinVol (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Prop :=
  ∀ (p : V) (f g : EuclideanSpace ℝ V),
    (∀ v, ¬ G.Reachable p v → f v = 0) → (∀ v, G.Reachable p v → g v = 0) →
      IndepFun (⇑(pair f)) (⇑(pair g)) (GraphLaplacian.gaussianField G m)

/-- The lattice field satisfies it. `LatticeFieldFactorises.indepFun_pair_of_separated` is the
theorem; this records that it is an instance of the named property and reproves nothing. -/
theorem gaussianField_clusteringFinVol (hm : m ≠ 0) : ClusteringFinVol G m :=
  fun p f g hf hg => indepFun_pair_of_separated G m hm p f g hf hg

/-! ## 2. And where it has content -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **ON A CONNECTED GRAPH THE STATEMENT IS EMPTY.** Every vertex is reachable from `p`, so the
second hypothesis forces `g = 0` and the independence asserted is independence from a constant.
**The box is connected**, so the exact statement says nothing about the object the OS programme is
about — which is why `LatticeOSPackage` was right to leave clustering out of its bundle, though not
for the reason it gave (`ERRATUM 322`). -/
theorem clustering_trivial_of_preconnected (hG : G.Preconnected) (p : V)
    (g : EuclideanSpace ℝ V) (hg : ∀ v, G.Reachable p v → g v = 0) : g = 0 := by
  ext v
  exact hg v (hG p v)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The same, said about the observable rather than the test function: the second factor of every
instance is the zero random variable. -/
theorem pair_eq_zero_of_preconnected (hG : G.Preconnected) (p : V)
    (g : EuclideanSpace ℝ V) (hg : ∀ v, G.Reachable p v → g v = 0) :
    pair g = 0 := by
  rw [clustering_trivial_of_preconnected hG p g hg]
  exact map_zero _

/-! ## 3. The three unconditional properties -/

/-- **REGULARITY, COVARIANCE AND EXACT CLUSTERING**, at every finite graph and every nonzero mass,
with nothing else assumed. `clustering_trivial_of_preconnected` stands beside it so the third
conjunct is not read for more than it says: on a connected graph it is empty. -/
theorem gaussianField_shadows_clustered (hm : m ≠ 0) :
    LatticeOSPackage.RegularFinVol G m
      ∧ LatticeOS1.EuclideanCovariantFinVol G m
      ∧ ClusteringFinVol G m :=
  ⟨LatticeOSPackage.gaussianField_regularFinVol hm,
   LatticeOS1.gaussianField_euclideanCovariantFinVol hm,
   gaussianField_clusteringFinVol hm⟩

end LatticeClustering
