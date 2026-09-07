import PathPieceEndpoints
import FieldBoundaryEnergy

/-!
# The piece the ray meets can be taken on the boundary of the down cluster

`WALLS` §W3.7 §4 names, as the first of three things that would have to exist, *a statement
relating the ray's odd piece to the cluster of `x`* — the piece `PathPieceEndpoints` delivers is a
subgraph of the dual graph of `σ`, and the one energy bound the estate holds with no boundary
condition, `FieldBoundaryEnergy.down_prob_le_cluster_sum`, is indexed by the down **cluster** of
`x`. The first alternative that section offers is a theorem, and it costs a few lines, because
`FieldCover` found the trick on 10 August: **the configuration that is down exactly on the cluster
of `x` and up everywhere else is a configuration**, its contour is the cluster's edge boundary,
and that boundary lies inside `σ`'s contour (`FieldCover.contour_clusterOff_subset`). `FieldCover`
ran the `+` chain on it when the cluster misses the boundary. This file runs the arc's enclosure
statement on it with no such restriction.

## What is proved

**`clusterOff_eq_true_of_up`** — an up site of `σ` is up in the cluster configuration.

**`clusterOn_mem_clusters`** — the cluster of a down site is one of the clusters
`down_prob_le_cluster_sum` sums over; **`contour_clusterOn`** — the two cluster configurations
(`FieldCover.clusterOff`, down on the cluster; `FieldBoundaryEnergy.clusterOn`, its negation) have
the same contour.

**`exists_odd_piece_cluster_leftRay`** — for a down site whose row meets the left edge at an up
site, with no other hypothesis: a piece of the **cluster configuration's** dual graph — a cycle,
or a path between two rim plaquettes — is crossed oddly by the ray, and its bonds lie in the
cluster's edge boundary and in `σ`'s contour.

**`exists_cluster_with_odd_piece_leftRay`** — the same, stated on a cluster `ν ∈ clusters x` with
`ClusterEvent ν σ`: the index set and the event of `down_prob_le_cluster_sum`.

## What is NOT here

**NO BOUND ON ANY PROBABILITY, AND THE REASON IS NOW ONE COUNT.** `gibbs_field_bound_of_cluster`
bounds the weight of each cluster by `e^{−4β|∂ν|}`; the piece located here lies in `∂ν`; what the
sum over `ν ∈ clusters x` then needs is **the number of clusters `ν ∋ x` with `|∂ν| = L`, bounded
by `C · c^L`** — a count of connected site sets by the size of their edge boundary, which nothing
in this estate has. **Not attempted, no cost claimed** (`ERRATUM 246`); grouping the clusters by
their odd piece does not help, because many clusters share one piece and the rest of their
boundary is uncounted.

**THE PATH BRANCH IS NOT SHOWN TO BE THE BOUNDARY-REACHING CASE.** That a cycle piece of the
cluster's boundary crossed oddly forces the cluster to miss the rim, and a path piece forces it to
reach the rim, is planar topology this file does not do; both branches are carried.

**WHICH PLAQUETTE THE RAY CROSSES IS NOT EXTRACTED**, as in `PathPieceEndpoints`, so the length
bound `distToEdge_le_length_of_mem_support` is not yet a bound in terms of `x`.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `clusterOff_eq_true_of_up` takes
`σ x = false` and `σ p = true`; the two ray theorems take exactly `RayCircuitSurrounding`'s —
the row bounds `0 < b`, `b + 1 < n` and the ray's two endpoint spins — and nothing on the box, the
boundary or the cluster.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace ClusterPiece

open IsingFiniteVolume IsingContourEnergy IsingContourClosed IsingContourPlaquette
open PlaquetteLattice IsingBoundaryField DualObstruction DualGraph DualBonds
open IsingContourSeparation RayWalk FieldCover FieldBoundaryEnergy DualPathCount
open PathPieceEndpoints SimpleGraph

variable {n : ℕ}

/-- An up site of `σ` is up in the cluster configuration: it is not in the down cluster. -/
theorem clusterOff_eq_true_of_up {σ : Config n} {x p : Site n} (hx : σ x = false)
    (hp : σ p = true) : clusterOff σ x p = true := by
  cases h : clusterOff σ x p
  · have := down_of_reachable hx (clusterOff_eq_false_iff.mp h)
    rw [hp] at this
    exact Bool.noConfusion this
  · rfl

/-- The cluster configuration of a down site is one of the clusters `down_prob_le_cluster_sum`
sums over. -/
theorem clusterOn_mem_clusters {σ : Config n} {x : Site n} (hx : σ x = false) :
    clusterOn σ x ∈ clusters x :=
  Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

theorem contour_clusterOn (σ : Config n) (x : Site n) :
    contour (clusterOn σ x) = contour (clusterOff σ x) :=
  contour_not (clusterOff σ x)

/-- **THE PIECE THE RAY MEETS CAN BE TAKEN ON THE EDGE BOUNDARY OF THE DOWN CLUSTER.** -/
theorem exists_odd_piece_cluster_leftRay (σ : Config n) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n)
    (hx : σ (col b k hk) = false) (he : σ (edge b.val b.isLt) = true) :
    ∃ H : SimpleGraph (Plaq n), H ≤ dualGraph (clusterOff σ (col b k hk)) ∧
      ((∃ P Q : Plaq n, P ≠ Q ∧ IsBdryPlaq P ∧ IsBdryPlaq Q ∧ IsPathGraphBetween H P Q) ∨
        IsCycleGraph H) ∧
      ¬ Even (crossings (bonds (clusterOff σ (col b k hk)) H) (leftRay b k hk)) ∧
      bonds (clusterOff σ (col b k hk)) H ⊆ contour (clusterOn σ (col b k hk)) ∧
      bonds (clusterOff σ (col b k hk)) H ⊆ contour σ := by
  obtain ⟨H, hle, hkind, hodd⟩ := exists_odd_piece_rim_leftRay (clusterOff σ (col b k hk))
    b hb0 hj k hk (clusterOff_self σ _) (clusterOff_eq_true_of_up hx he)
  refine ⟨H, hle, hkind, hodd, ?_, ?_⟩
  · rw [contour_clusterOn]
    exact bonds_subset _ _
  · exact (bonds_subset _ _).trans (contour_clusterOff_subset hx)

/-- The same, phrased on the cluster `down_prob_le_cluster_sum` indexes by. -/
theorem exists_cluster_with_odd_piece_leftRay (σ : Config n) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n)
    (hx : σ (col b k hk) = false) (he : σ (edge b.val b.isLt) = true) :
    ∃ ν ∈ clusters (col b k hk), ClusterEvent ν σ ∧
      ∃ H : SimpleGraph (Plaq n),
        ((∃ P Q : Plaq n, P ≠ Q ∧ IsBdryPlaq P ∧ IsBdryPlaq Q ∧ IsPathGraphBetween H P Q) ∨
          IsCycleGraph H) ∧
        ¬ Even (crossings (bonds (clusterOff σ (col b k hk)) H) (leftRay b k hk)) ∧
        bonds (clusterOff σ (col b k hk)) H ⊆ contour ν := by
  obtain ⟨H, -, hkind, hodd, hsub, -⟩ := exists_odd_piece_cluster_leftRay σ b hb0 hj k hk hx he
  exact ⟨clusterOn σ _, clusterOn_mem_clusters hx, clusterEvent_cluster hx, H, hkind, hodd, hsub⟩

end ClusterPiece
