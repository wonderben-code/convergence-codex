import S3bRefutation
import RayWalk

/-!
# Where the cluster boundary is, and the one branch on which it is nowhere

`ERRATUM 108` refuted `S3bResidue.ClusterReachesRim` — the specification the field-model Peierls
route's step S3b-ii was written against — and the `UNLOCK_WATCHLIST` block for that route says
what comes next in as many words:

> **"Someone REPAIRS the statement; that is the first task on this step, ahead of any route to
> it. Route (ii) is a route to a false statement and should not be attempted until the statement
> is fixed."**

This file is the first half of route (ii) — *"shoot a ray from `x`, count crossings, and locate
the piece near `x`"* — and it is deliberately not the repair itself. What it produces is the
thing a repaired statement has to be built out of, together with **a proof of exactly which
configurations the old statement was wrong about**.

## The dichotomy

**`leftEdge_reachable_or_contour_edge_on_ray`.** For every configuration and every site `x`,
walk the leftward ray from `x` to the left edge of the box. Then **either the left-edge site at
the end of that ray is in `x`'s down cluster, or the cluster's contour contains a bond ON THE
RAY** — hence at `L∞` distance at most `x.1` from `x`, which is the distance from `x` to that
edge.

There is no third case and no hypothesis: not `PlusBoundary`, not `x` down, not `x` interior.

## Why the second branch is the one the route wants, and the first is the one that killed it

The route needs a broken bond *near* `x` to start a dual walk from. Branch two supplies one and
says where it is. **Branch one is the refutation.** `ERRATUM 108`'s witness is the all-down
configuration, whose cluster is the whole box and whose `clusterOn` is therefore constant with an
empty contour — and `allDown_left_branch` proves that this configuration lands in branch one at
**every** site, so the dichotomy is not refuted by the thing that refuted its predecessor. That
is a check rather than an assertion, which is the whole of what `ERRATUM 108` found missing.

So the degenerate case is not an awkward corner to be excluded by hand. It is a named branch of
a proved dichotomy, and what distinguishes it is a property of the cluster (*it reaches the left
edge along the whole ray*) rather than a property of `x`.

## Both branches fire, so this is not excluded middle wearing a hat

A dichotomy whose second branch never happens is worth nothing, and §4 alone does not rule that
out. **`both_branches_realised`** settles it on a `2 × 2` box at one site: the all-down
configuration takes the first branch and **cannot** take the second — its contour is empty — and
the all-up configuration, whose down-graph has no edges at all, takes the second.

## The degenerate branch is exactly one thing, and that is §7

`allDown` is not one awkward witness among many. The crossing lemma says, with no ray involved,
that **a cluster's contour is empty only if the cluster is the whole box** — so every boundary
site is in it. The route's estimate suppresses a cluster by
`exp(-4β|contour|) · exp(-2βh·k)`, two mechanisms, and
**`contour_nonempty_or_all_boundary`** says they are never both idle: an empty contour is exactly
the case in which the second term is as large as it can be.

## What this does NOT do

**It does not repair `ClusterReachesRim`, and it does not close S3b-ii.** A bond of the contour
gives an edge of the dual graph; the route needs a WALK from a plaquette near `x` out to a rim,
and getting from "there is an edge here" to "there is a walk to the rim" is the circuits-plus-paths
decomposition and the parity argument that the watchlist records as residues (a) and (b). Neither
is touched here.

**And §7 is not the estimate either.** It rules out the case where BOTH suppression terms are
worthless; it says nothing quantitative about a cluster with a small nonempty contour that also
misses most of the boundary, which is the case `DualPathCount` exists to handle and the one the
route actually turns on.

**It settles one third of the `DECISION NEEDED` on that route, and only by narrowing it.** The
question was *which distance* — `L∞` to the boundary, the route map's `2 d(x)` perimeter form, or
`PlaqLocal.Near`'s radius. The ray answers it for its own branch and answers it in the first
form, because that is what the construction produces rather than what was convenient: the bond
sits on the ray, so its column is at most `x.1`. **The other two forms are not thereby refuted**,
and the perimeter form in particular is about a different quantity. The decision is narrower, not
made.

**And the bound is one-sided.** The ray runs LEFT. A site near the left edge gets a short ray and
a nearby bond; a site near the right edge gets a long one. The four-direction statement — take the
nearest edge — is not proved here, and would need the other three rays, which `RayWalk` does not
build.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ClusterRayCrossing

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField IsingContourSeparation
open FieldCover FieldBoundaryEnergy S3bResidue S3bRefutation RayWalk SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Leaving the cluster costs a contour bond

The one graph-theoretic fact, with no lattice geometry in it: a walk that starts inside the
cluster and ends outside it must cross the cluster's own boundary, and the crossing is a bond of
`contour (clusterOn σ x)` because `clusterOn` is exactly the indicator of the cluster.
-/

/-- A site off the cluster is `false` for `clusterOn`. -/
theorem clusterOn_eq_false_of_not_reachable {σ : Config n} {x p : Site n}
    (h : ¬ (downGraph σ).Reachable x p) : clusterOn σ x p = false :=
  Bool.not_eq_true _ |>.mp fun hc => h (clusterOn_eq_true_iff.mp hc)

/-- **THE CROSSING LEMMA.** A walk from inside `x`'s cluster to outside it contains a bond of
that cluster's contour. Induction on the walk, splitting on whether the second vertex is still
in the cluster: if it is, recurse; if it is not, the first edge is the crossing. -/
theorem exists_contour_edge_of_walk {σ : Config n} {x : Site n} :
    ∀ {a y : Site n} (w : (latticeGraph n).Walk a y),
      (downGraph σ).Reachable x a → ¬ (downGraph σ).Reachable x y →
      ∃ e ∈ w.edges, e ∈ contour (clusterOn σ x) := by
  intro a y w
  induction w with
  | nil => intro ha hy; exact absurd ha hy
  | @cons u v z hadj w' ih =>
      intro ha hy
      by_cases hv : (downGraph σ).Reachable x v
      · obtain ⟨e, hew, hec⟩ := ih hv hy
        exact ⟨e, by simp [hew], hec⟩
      · refine ⟨s(u, v), by simp, ?_⟩
        rw [mem_contour]
        refine ⟨(latticeGraph_adj u v).mp hadj, ?_⟩
        rw [clusterOn_eq_true_iff.mpr ha, clusterOn_eq_false_of_not_reachable hv]
        decide

/-! ## 2. The ray, and where its bonds are

`RayWalk.leftRay` is the walk from column `k` of a row to that row's left-edge site. Its support
is the row's initial segment, which is what turns "a bond somewhere on the ray" into a distance.
-/

/-- **EVERY SITE OF THE RAY IS ON `x`'s ROW, AT A COLUMN NO LARGER THAN `x`'s.** -/
theorem support_leftRay (b : Fin n) :
    ∀ (k : ℕ) (hk : k < n), ∀ p ∈ (leftRay b k hk).support, p.2 = b ∧ p.1.val ≤ k := by
  intro k
  induction k with
  | zero =>
      intro hk p hp
      rw [leftRay_zero] at hp
      have hp' : p = col b 0 hk := List.mem_singleton.mp hp
      subst hp'
      exact ⟨rfl, Nat.le_refl 0⟩
  | succ k ih =>
      intro hk p hp
      rw [leftRay_succ] at hp
      rcases List.mem_cons.mp hp with h | h
      · subst h; exact ⟨rfl, by simp [col]⟩
      · obtain ⟨h1, h2⟩ := ih (by omega) p h
        exact ⟨h1, by omega⟩

/-- And hence every BOND of the ray has both ends there. `Walk.edges` are pairs of adjacent
support vertices, which is `SimpleGraph.Walk.fst_mem_support_of_mem_edges` and its sibling. -/
theorem mem_ray_edge_bounds (b : Fin n) (k : ℕ) (hk : k < n) {p q : Site n}
    (he : s(p, q) ∈ (leftRay b k hk).edges) :
    (p.2 = b ∧ p.1.val ≤ k) ∧ (q.2 = b ∧ q.1.val ≤ k) :=
  ⟨support_leftRay b k hk p (Walk.fst_mem_support_of_mem_edges _ he),
   support_leftRay b k hk q (Walk.snd_mem_support_of_mem_edges _ he)⟩

/-! ## 3. The dichotomy -/

/-- **THE DICHOTOMY, WITH NO HYPOTHESIS AT ALL.** For any configuration and any site, either the
left-edge site of that site's row is in its down cluster, or the cluster's contour contains a
bond of the leftward ray. -/
theorem leftEdge_reachable_or_contour_edge_on_ray (σ : Config n) (b : Fin n) (k : ℕ)
    (hk : k < n) :
    (downGraph σ).Reachable (col b k hk) (edge b.val b.isLt)
      ∨ ∃ e ∈ (leftRay b k hk).edges, e ∈ contour (clusterOn σ (col b k hk)) := by
  by_cases h : (downGraph σ).Reachable (col b k hk) (edge b.val b.isLt)
  · exact Or.inl h
  · exact Or.inr (exists_contour_edge_of_walk (leftRay b k hk) (Reachable.refl _) h)

/-- **THE SECOND BRANCH, LOCATED.** The bond it produces lies on `x`'s row at a column no larger
than `x`'s own — so at `L∞` distance at most `x.1` from `x`, which is exactly the distance from
`x` to the left edge. This is the form the covering step needs its starting bond in. -/
theorem contour_edge_near_of_not_reachable {σ : Config n} (b : Fin n) (k : ℕ) (hk : k < n)
    (h : ¬ (downGraph σ).Reachable (col b k hk) (edge b.val b.isLt)) :
    ∃ p q : Site n, s(p, q) ∈ contour (clusterOn σ (col b k hk))
      ∧ p.2 = b ∧ q.2 = b ∧ p.1.val ≤ k ∧ q.1.val ≤ k := by
  obtain ⟨e, hew, hec⟩ := exists_contour_edge_of_walk (leftRay b k hk) (Reachable.refl _) h
  induction e using Sym2.ind with
  | _ p q =>
      obtain ⟨⟨hp2, hp1⟩, ⟨hq2, hq1⟩⟩ := mem_ray_edge_bounds b k hk hew
      exact ⟨p, q, hec, hp2, hq2, hp1, hq1⟩

/-! ## 4. The refuting configuration is branch one, everywhere

`ERRATUM 108` killed `ClusterReachesRim` with the all-down configuration. A repaired statement
that this configuration also refutes is not a repair, so the check belongs here and not in a
paragraph. -/

/-- **THE ALL-DOWN CONFIGURATION IS IN THE FIRST BRANCH AT EVERY SITE.** Its down-graph is the
whole lattice graph (`S3bRefutation.downGraph_allDown`), and the ray itself is a walk in that
graph, so the left-edge site is reachable — with no connectivity theorem needed, because the
witness is the ray. -/
theorem allDown_left_branch (b : Fin n) (k : ℕ) (hk : k < n) :
    (downGraph (allDown n)).Reachable (col b k hk) (edge b.val b.isLt) := by
  rw [downGraph_allDown]
  exact ⟨leftRay b k hk⟩

/-- **AND SO THE DICHOTOMY SURVIVES WHAT REFUTED `ClusterReachesRim`.** On `ERRATUM 108`'s
witness the disjunction is discharged by its first branch, at every site — the second branch is
never invoked, and never has to be, because there is no contour to invoke it with. -/
theorem allDown_dichotomy_first (b : Fin n) (k : ℕ) (hk : k < n) :
    (downGraph (allDown n)).Reachable (col b k hk) (edge b.val b.isLt)
      ∧ contour (clusterOn (allDown n) (col b k hk)) = ∅ :=
  ⟨allDown_left_branch b k hk, contour_clusterOn_allDown _⟩

/-! ## 5. What the branches say about each other

The two branches are not merely exhaustive; on the degenerate configuration the second is
*impossible*, so the dichotomy carries information rather than being a restatement of excluded
middle. -/

/-- **THE SECOND BRANCH IS UNREACHABLE ON THE REFUTING WITNESS**, and this is what makes the
dichotomy worth stating: an empty contour has no bonds at all, so a statement that offered only
the second branch could not hold there. That is `ERRATUM 108` in one line, and it is the reason
the repaired statement has to be a dichotomy rather than a conclusion. -/
theorem allDown_no_second_branch (b : Fin n) (k : ℕ) (hk : k < n) :
    ¬ ∃ e ∈ (leftRay b k hk).edges, e ∈ contour (clusterOn (allDown n) (col b k hk)) := by
  rintro ⟨e, -, hec⟩
  rw [contour_clusterOn_allDown] at hec
  exact absurd hec (Finset.notMem_empty e)

/-! ## 6. And the second branch is inhabited, so the dichotomy is not one branch in disguise

§4 shows the first branch fires on the configuration that refuted the old specification. That on
its own is compatible with the second branch never firing at all, which would make the dichotomy
worthless — the vacuity attack this project runs on every new structure. So here is a
configuration in the second branch.
-/

/-- Every site up. Its down-graph has no edges at all, so every cluster is a single site. -/
def allUp (n : ℕ) : Config n := fun _ => true

theorem not_reachable_allUp {x y : Site n} (hxy : x ≠ y) :
    ¬ (downGraph (allUp n)).Reachable x y := by
  rintro ⟨w⟩
  cases w with
  | nil => exact hxy rfl
  | cons hadj _ => exact absurd hadj.2.1 (by simp [allUp])

theorem col_ne_edge (b : Fin n) (k : ℕ) (hk : k < n) (hk0 : 0 < k) :
    col b k hk ≠ edge b.val b.isLt := by
  intro hc
  have : k = 0 := congrArg (fun p => p.1.val) hc
  omega

/-- **THE SECOND BRANCH FIRES**, at every site off the left edge, on the all-up configuration:
nothing is down, so `x`'s cluster is `{x}` alone, the left-edge site is not in it, and the ray
must cross out. Together with §4 the dichotomy has a witness on each side. -/
theorem allUp_second_branch (b : Fin n) (k : ℕ) (hk : k < n) (hk0 : 0 < k) :
    ∃ e ∈ (leftRay b k hk).edges, e ∈ contour (clusterOn (allUp n) (col b k hk)) := by
  rcases leftEdge_reachable_or_contour_edge_on_ray (allUp n) b k hk with h | h
  · exact absurd h (not_reachable_allUp (col_ne_edge b k hk hk0))
  · exact h

/-- **BOTH BRANCHES ARE REALISED AND NEITHER IS AUTOMATIC**, stated as one theorem so a reader
cannot take the dichotomy for an instance of excluded middle. On a `2 × 2` box at the site
`(1, 0)`: the all-down configuration takes the first branch and CANNOT take the second (its
contour is empty), and the all-up configuration takes the second. -/
theorem both_branches_realised :
    ((downGraph (allDown 2)).Reachable (col 0 1 one_lt_two) (edge (0 : Fin 2).val (by omega))
      ∧ ¬ ∃ e ∈ (leftRay (0 : Fin 2) 1 one_lt_two).edges,
            e ∈ contour (clusterOn (allDown 2) (col 0 1 one_lt_two)))
    ∧ (∃ e ∈ (leftRay (0 : Fin 2) 1 one_lt_two).edges,
          e ∈ contour (clusterOn (allUp 2) (col 0 1 one_lt_two))) :=
  ⟨⟨allDown_left_branch 0 1 one_lt_two, allDown_no_second_branch 0 1 one_lt_two⟩,
    allUp_second_branch 0 1 one_lt_two Nat.one_pos⟩

/-! ## 7. The degenerate branch is exactly one configuration of the cluster

§4 treats the all-down configuration as *a* witness in branch one. It is more than that, and the
crossing lemma of §1 says so without any ray: **the only way a cluster's contour can be empty is
for the cluster to be the whole box.**

That matters for the route rather than for tidiness. The field-model estimate
`FieldBoundaryEnergy.down_prob_le_cluster_sum` suppresses a cluster `ν` by
`exp(-4β|contour ν|) · exp(-2βh·k(ν))`, where `k(ν)` counts the boundary sites in `ν` — **two
mechanisms, and the theorems below say they cannot both be idle.** If the contour is empty the
first is worth nothing, and that is exactly the case in which the cluster contains *every*
boundary site and the second is worth as much as it can be.
-/

/-- **AN EMPTY CLUSTER CONTOUR MEANS THE CLUSTER IS EVERYTHING.** No ray and no geometry: the
lattice graph is connected, so a site outside the cluster would supply a walk out of it, and §1
turns that walk into a contour bond. -/
theorem reachable_of_contour_clusterOn_empty {σ : Config n} {x : Site n} (hn : 0 < n)
    (h : contour (clusterOn σ x) = ∅) (y : Site n) : (downGraph σ).Reachable x y := by
  by_contra hy
  obtain ⟨w⟩ := (latticeGraph_connected hn).preconnected x y
  obtain ⟨e, -, hec⟩ := exists_contour_edge_of_walk w (Reachable.refl _) hy
  rw [h] at hec
  exact absurd hec (Finset.notMem_empty e)

/-- And hence every boundary site is in the cluster, which is the quantity the field term of the
estimate is paid in. -/
theorem boundary_mem_cluster_of_contour_empty {σ : Config n} {x : Site n} (hn : 0 < n)
    (h : contour (clusterOn σ x) = ∅) {p : Site n} (hp : isBoundary p = true) :
    (downGraph σ).Reachable x p ∧ isBoundary p = true :=
  ⟨reachable_of_contour_clusterOn_empty hn h p, hp⟩

/-- **THE TWO SUPPRESSION MECHANISMS ARE NOT BOTH IDLE.** For any configuration and any site,
either the cluster's contour is nonempty — the energy term of
`FieldBoundaryEnergy.down_prob_le_cluster_sum` has something to charge — or the cluster contains
**every** boundary site, which is the largest the field term can be.

This is the shape the route's remaining leg has to have, and it is stated here so that the leg is
written down rather than gestured at: what is NOT proved is any *quantitative* interpolation
between the two, and the estimate needs one. A cluster with a small nonempty contour that also
misses most of the boundary is not excluded by this theorem, and is exactly the case the count in
`DualPathCount` exists to handle. -/
theorem contour_nonempty_or_all_boundary (σ : Config n) (x : Site n) (hn : 0 < n) :
    contour (clusterOn σ x) ≠ ∅
      ∨ ∀ p : Site n, isBoundary p = true → (downGraph σ).Reachable x p := by
  by_cases h : contour (clusterOn σ x) = ∅
  · exact Or.inr fun p _ => reachable_of_contour_clusterOn_empty hn h p
  · exact Or.inl h

/-- **AND THE REFUTING CONFIGURATION IS THE RIGHT-HAND BRANCH**, which is the sharp form of §4:
`allDown` is not one awkward witness among many, it is what the empty-contour case forces. -/
theorem allDown_all_boundary (hn : 0 < n) (x : Site n) (p : Site n) :
    (downGraph (allDown n)).Reachable x p :=
  reachable_of_contour_clusterOn_empty hn (contour_clusterOn_allDown x) p

end ClusterRayCrossing
