import RimWalk
import FieldBoundaryEnergy
import PeierlsCover

/-!
# What is left of S3b-ii, written as an object rather than as a paragraph

`PROOF_STRATEGY` §3 permits leaving a chain **only** once the remaining leg is written down
precisely. Five files of this chain have landed — `FieldBoundaryEnergy` (the energy estimate
with no `+`-cut hypothesis, and the one inequality covering both branches), `DualPathCount`
(the entropy count, linear prefactor and geometric tail), `OuterFaceObstruction` (why one
outer-face vertex fails), `ExtendedDual` (why four succeed, and even plaquette degrees with no
boundary condition) and `RimWalk` (the translation between the construction and the count).
This file states what is not proved, in the estate's convention for a gap: a `def` returning
`Prop`, so it can be pointed at rather than described.

## The residue, restated — and it is ONE statement, not the two `ERRATUM 97` named

`ERRATUM 97` corrected an overclaim by saying the residue was two things: a circuits-plus-paths
decomposition, and the open-path analogue of `RayWalk`'s ray argument. **Attempting the next
rung shows that framing is still not right, and in the other direction.** Those are not two
conjuncts. They are two candidate **routes to the same statement** —

> **`ClusterReachesRim`** — for a site that is down and whose down cluster reaches the edge of
> the box, the plaquette at that site is connected, in the extended dual graph of the cluster,
> to one of the four rim vertices.

Prove it by either route and `RimWalk.exists_walk_to_bdry_of_reachable` turns it directly into
the object `DualPathCount` counts: that is `walk_to_bdry_of_gap` below, and it is the whole of
the reduction. **The decomposition is not independently required.** It was named as a residue
because the earlier, wrong framing reached for it first.

## The second thing that is genuinely missing, and why it is not an object here

A walk existing is not a walk being **long**. `DualPathCount.sum_walksTo_bdry_le` gives
`8 n (4 e^{-4β})^{L₀}`, and the `O(n)` surface term of step S5 needs `L₀` to grow with the
distance from `x` to the edge of the box. Reachability supplies no lower bound on length. That
is the original S3b "geometric length bound", still unproved and now the second half of what
is left.

**It is deliberately not written as a `def` here.** Doing so requires choosing the distance
function — `L∞` to the boundary, or the perimeter bound `2 d(x)` the route map states, or the
`PlaqLocal.Near` radius the estate already uses — and those are three different statements
with three different proofs. Picking one quickly is how a route map acquires a step nobody
checked, which is `ERRATUM 89`. Recorded in `UNLOCK_WATCHLIST` as a decision to make, not made
here.

Nothing in this file is a proof of anything about the Ising model.
`IsingBoundaryField.MagnetisationBound` is untouched, and so is
`FieldBoundaryEnergy.down_prob_le_cluster_sum`, whose right-hand side all of this is aimed at.
-/

namespace S3bResidue

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField PlaquetteLattice
open DualObstruction DualGraph ExtendedDual FieldCover FieldBoundaryEnergy PeierlsCover

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The gap, as an object -/

/-- The hypothesis that makes a site's cluster a **boundary-reaching** one: some site the down
cluster of `x` reaches lies on the boundary of the box. This is the second branch of the
route's step S2, and by `FieldCover.DownInside` it is exactly the negation of the first. -/
def ReachesBoundary (σ : Config n) (x : Site n) : Prop :=
  ∃ p : Site n, (downGraph σ).Reachable x p ∧ isBoundary p = true

/-- **THE GAP OF S3b-ii, NAMED.** For every configuration, every interior site that is down
with a cluster reaching the edge of the box: in the extended dual graph of that cluster, the
plaquette at the site is connected to one of the four rim vertices.

This is a `def` returning `Prop` and **nothing in this estate proves it**. It is stated over
all `σ` and all such `x` deliberately: a proof for one configuration is worth nothing to the
union bound, which quantifies over the whole event.

Two routes are known and neither is attempted. **(i)** A decomposition of an
even-except-at-the-rims graph into circuits plus paths between the odd vertices — for which
`RimWalk.odd_degree_isRim` supplies the hypothesis, and which neither the estate nor Mathlib
has. *Its arity is now known:* `RimParity.card_oddExt_eq_zero_or_two_or_four` says the odd
vertices number `0`, `2` or `4`, so such a decomposition would carry **at most two** open
paths, not an unbounded family. That bounds the theorem's shape; it does not supply the
theorem. **(ii)** The open-path analogue of `RayWalk.exists_circuit_near_of_down`: shoot a ray
from `x`, count crossings, and locate the piece near `x` — which is how the interior chain does
the
corresponding job. -/
def ClusterReachesRim (n : ℕ) : Prop :=
  ∀ (σ : Config n) (x : Site n) (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n),
    σ x = false → ReachesBoundary σ x →
      ∃ d : Fin 4, (extDual (clusterOn σ x)).Reachable
        (Sum.inl (plaqOf x hi hj)) (Sum.inr d)

/-! ## 2. The reduction, which is the part that is proved -/

/-- **GIVEN THE GAP, THE COUNTED OBJECT EXISTS.** `ClusterReachesRim` yields, for every
boundary-reaching down site, a walk in the ordinary dual graph of the cluster from the
plaquette at that site to a plaquette on the edge of the box — which is precisely what
`DualPathCount.card_walksTo_bdry_le` and `sum_walksTo_bdry_le` bound.

So the distance between this chain and its target is **one statement**, not a programme: the
translation is `RimWalk`, the count is `DualPathCount`, the energy is `FieldBoundaryEnergy`,
and the missing link is the hypothesis of this theorem. -/
theorem walk_to_bdry_of_gap (hgap : ClusterReachesRim n) (σ : Config n) (x : Site n)
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n)
    (hx : σ x = false) (hreach : ReachesBoundary σ x) :
    ∃ Q ∈ DualPathCount.bdryPlaq n,
      Nonempty ((dualGraph (clusterOn σ x)).Walk (plaqOf x hi hj) Q) := by
  obtain ⟨d, hd⟩ := hgap σ x hi hj hx hreach
  exact RimWalk.exists_walk_to_bdry_of_reachable hd

/-- The dichotomy the route's step S2 asserts, as a triviality that is worth having stated:
a down site either has a cluster that misses the boundary — `FieldCover.DownInside`, which
`FieldCover.field_peierls_small` bounds — or one that reaches it, which is `ReachesBoundary`.
There is no third case, and `FieldBoundaryEnergy.down_prob_le_cluster_sum` needs none. -/
theorem downInside_or_reachesBoundary (σ : Config n) (x : Site n) (hx : σ x = false) :
    DownInside σ x ∨ ReachesBoundary σ x := by
  classical
  by_cases h : ∀ p : Site n, (downGraph σ).Reachable x p → isBoundary p = false
  · exact Or.inl ⟨hx, h⟩
  · obtain ⟨p, hp, hb⟩ : ∃ p : Site n, (downGraph σ).Reachable x p ∧ isBoundary p ≠ false := by
      by_contra hc
      exact h fun p hr => not_ne_iff.mp fun hb => hc ⟨p, hr, hb⟩
    exact Or.inr ⟨p, hp, Bool.not_eq_false _ ▸ hb⟩

end S3bResidue
