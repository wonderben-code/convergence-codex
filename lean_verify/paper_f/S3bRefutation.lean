import S3bResidue

/-!
# `ClusterReachesRim` is false, and the reason is the case with no contour at all

`S3bResidue.ClusterReachesRim` was written down as the named gap of S3b-ii: for every
configuration and every site down with a cluster reaching the edge of the box, the plaquette
**at that site** is connected, in the extended dual graph of the cluster, to one of the four
rim vertices. `S3bResidue.walk_to_bdry_of_gap` proves the reduction from it, and two routes to
it were recorded. Route (i) was finished this same day (`RimParity`, `EdgeAddParity`).

**The statement is false.** Not hard, not open — false, and this file proves it.

> **`not_clusterReachesRim`** — for every `n > 1`, `¬ ClusterReachesRim n`.

## The witness, and why it is not a technicality

Take `σ` **all down**. Every site is down, so the down-cluster of any site is the whole box —
which certainly reaches the edge, so `ReachesBoundary` holds. But `clusterOn σ x` is then
constant, and **a constant configuration has empty contour**: no bond has ends that differ. So
`extDual (clusterOn σ x)` is the empty graph on `Plaq n ⊕ Fin 4`, the plaquette at `x` is
isolated, and it reaches nothing at all — least of all a rim vertex, which is a different
vertex.

**This is not an artefact of choosing a corner.** `reachesBoundary_allDown` is proved for
*every* site, via `IsingContourSeparation.latticeGraph_connected`, because with everything down
the down-graph *is* the lattice graph. `not_clusterReachesRim_interior` states the same
refutation at the strictly interior site `(1,1)`.

## What was actually wrong with the specification

Compare the interior analogue the estate already has.
`RayWalk.exists_circuit_near_of_down` does **not** claim that the plaquette at `x` lies on the
contour. It produces a plaquette `P` in a **ball** of radius `L + 1` around `x` that lies on a
circuit. `ClusterReachesRim` asked for the plaquette at `x` itself, which is strictly stronger
and, as above, not true: a site deep inside a droplet has no broken bond on its own plaquette.

The physics is not damaged by this — the all-down configuration has no contour to pay for, and
in the boundary-field estimate its cost is carried entirely by the field term, not by
`down_prob_le_cluster_sum`'s contour factor. What is damaged is the *statement*, which
quantified over all `σ` and so swept the no-contour case in with the rest.

**The repair is not attempted here and is not obvious**, which is why this file refutes rather
than replaces. A corrected statement has to either restrict to configurations whose cluster has
a nonempty boundary near `x`, or — matching the interior chain — weaken "the plaquette at `x`"
to "some plaquette within `L + 1` of `x`", at which point the length `L` reappears and meets
the length-control question `S3bResidue` already flags as a DECISION NEEDED. Choosing between
those quickly, to make the list tidy, is `ERRATUM 89`.

**AND THE WITNESS HAS SINCE BEEN REPLACED BY A CRITERION.** `RimBoundary` proves that *any*
configuration constant along the edge of the box has no rim edge whatever, so the all-down
witness below is one instance of a class: `RimBoundary.not_reachable_rim_allDown` re-derives this
file's conclusion without computing a contour at all. What that buys is the necessary condition
on a repair — some boundary site must lie **outside** the cluster — which this file's single
witness could not have supplied.

`S3bResidue.walk_to_bdry_of_gap` remains true — it is an implication, and an implication from a
false hypothesis is no less valid. What it is not is *useful*, and the ledger now says so.
`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace S3bRefutation

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField PlaquetteLattice
open IsingContourSeparation
open DualObstruction DualGraph ExtendedDual FieldCover FieldBoundaryEnergy PeierlsCover
open S3bResidue

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The witness -/

/-- Every site down. -/
def allDown (n : ℕ) : Config n := fun _ => false

/-- With everything down, the down-graph is the whole lattice graph. -/
theorem downGraph_allDown : downGraph (allDown n) = latticeGraph n := by
  ext p q
  exact ⟨fun h => h.1, fun h => ⟨h, rfl, rfl⟩⟩

/-- **The cluster reaches the boundary from every site**, because the down-graph is connected.
So the hypothesis of `ClusterReachesRim` is satisfied, and satisfied everywhere — the
refutation does not depend on where `x` is put. -/
theorem reachesBoundary_allDown (hn : 0 < n) (x : Site n) : ReachesBoundary (allDown n) x := by
  refine ⟨(⟨0, hn⟩, ⟨0, hn⟩), ?_, isBoundary_corner n hn⟩
  rw [downGraph_allDown]
  exact (latticeGraph_connected hn).preconnected x _

/-! ## 2. The cluster is constant, so its contour is empty -/

/-- Adjacent sites are in the same cluster, since the edge between them is a down-edge. -/
theorem clusterOn_allDown_adj (x : Site n) {p q : Site n} (h : adj p q) :
    clusterOn (allDown n) x p = clusterOn (allDown n) x q := by
  have hpq : (downGraph (allDown n)).Reachable p q :=
    SimpleGraph.Adj.reachable (show (downGraph (allDown n)).Adj p q from ⟨h, rfl, rfl⟩)
  have hiff : clusterOn (allDown n) x p = true ↔ clusterOn (allDown n) x q = true := by
    rw [clusterOn_eq_true_iff, clusterOn_eq_true_iff]
    exact ⟨fun hr => hr.trans hpq, fun hr => hr.trans hpq.symm⟩
  cases hp : clusterOn (allDown n) x p <;> cases hq : clusterOn (allDown n) x q <;>
    simp_all

/-- **A CONSTANT CONFIGURATION HAS NO CONTOUR.** A bond is broken when its ends differ, and no
two adjacent sites differ here. -/
theorem contour_clusterOn_allDown (x : Site n) : contour (clusterOn (allDown n) x) = ∅ := by
  ext e
  induction e using Sym2.ind with
  | _ p q =>
    simp only [Finset.notMem_empty, iff_false]
    intro hmem
    rw [mem_contour] at hmem
    exact hmem.2 (clusterOn_allDown_adj x hmem.1)

/-- **AND SO THE EXTENDED DUAL GRAPH IS EMPTY.** Every kind of edge — plaquette to plaquette,
plaquette to rim, rim to rim — needs either a broken side or is `False` outright. -/
theorem extDual_allDown_eq_bot (x : Site n) :
    extDual (clusterOn (allDown n) x) = ⊥ := by
  have hc := contour_clusterOn_allDown x
  ext a b
  simp only [SimpleGraph.bot_adj, iff_false]
  cases a with
  | inl P =>
    cases b with
    | inl Q =>
      rintro ⟨d, hd, -, -⟩
      rw [hc] at hd
      exact absurd hd (Finset.notMem_empty _)
    | inr d =>
      rintro ⟨hd, -⟩
      rw [hc] at hd
      exact absurd hd (Finset.notMem_empty _)
  | inr d =>
    cases b with
    | inl Q =>
      rintro ⟨hd, -⟩
      rw [hc] at hd
      exact absurd hd (Finset.notMem_empty _)
    | inr e => exact id

/-! ## 3. The refutation -/

/-- In the empty graph the plaquette at `x` reaches no rim, because it reaches only itself and
it is not a rim. -/
theorem not_reachable_rim (x : Site n) (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n)
    (d : Fin 4) :
    ¬ (extDual (clusterOn (allDown n) x)).Reachable
        (Sum.inl (plaqOf x hi hj)) (Sum.inr d) := by
  rw [extDual_allDown_eq_bot]
  -- `SimpleGraph.reachable_bot` will not unify its universe here, so the one-line induction:
  -- a walk in the empty graph never takes a step, so its endpoints coincide.
  have key : ∀ a b : ExtV n, (⊥ : SimpleGraph (ExtV n)).Walk a b → a = b := by
    intro a b w
    induction w with
    | nil => rfl
    | cons hadj _ => exact hadj.elim
  rintro ⟨w⟩
  exact absurd (key _ _ w) (by simp)

/-- **`ClusterReachesRim` IS FALSE.** All sites down: the hypothesis holds at every site, and
the conclusion fails at every site, because a constant configuration has no contour and the
extended dual graph of an empty contour has no edges. -/
theorem not_clusterReachesRim (hn : 1 < n) : ¬ ClusterReachesRim n := by
  have h0 : 0 < n := by omega
  intro h
  obtain ⟨d, hd⟩ :=
    h (allDown n) ((⟨0, h0⟩, ⟨0, h0⟩) : Site n) (by simpa using hn) (by simpa using hn) rfl
      (reachesBoundary_allDown h0 _)
  exact not_reachable_rim _ _ _ d hd

/-- The same at a **strictly interior** site, so that no one need wonder whether the corner was
doing the work. -/
theorem not_clusterReachesRim_interior (hn : 2 < n) : ¬ ClusterReachesRim n := by
  have h0 : 0 < n := by omega
  intro h
  obtain ⟨d, hd⟩ :=
    h (allDown n) ((⟨1, by omega⟩, ⟨1, by omega⟩) : Site n) (by simpa using hn) (by simpa using hn)
      rfl (reachesBoundary_allDown h0 _)
  exact not_reachable_rim _ _ _ d hd

end S3bRefutation
