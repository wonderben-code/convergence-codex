import CycleDecomposition

/-!
# Adding an edge between the two odd vertices makes every degree even

`CycleDecomposition.exists_cycle_decomposition` needs `EvenDegrees` and gives an edge-disjoint
union of cycles. `RimParity` says the extended dual graph misses that hypothesis at `0`, `2` or
`4` vertices and nowhere else. This file is the classical repair for the `2` case, proved in
full generality for any finite simple graph:

> **`evenDegrees_sup_edge`** — if `u ≠ v` are non-adjacent, both of odd degree, and every other
> vertex has even degree, then `G ⊔ edge u v` has **all** degrees even.

So `G ⊔ edge u v` decomposes into cycles (`exists_cycle_decomposition_sup_edge`), and the
decomposition covers `G`'s edges together with the one added edge — which is the standard route
to "circuits plus one open path".

## What this is and is not

It is a parity statement about neighbour sets, and it is complete: the three cases of
`neighborSet_sup_edge` (the two endpoints, and everything else) are proved, not assumed.

**§4 then cuts the added edge back out**, which is the part an earlier version of this header
declared impossible:

> **`reachable_of_odd_pair`** — a finite graph that is even everywhere except at two
> non-adjacent vertices has those two vertices **connected in the graph itself**.

That is the circuits-plus-one-path statement in the form anything downstream actually wants: not
a list of pieces, but a walk between the two odd vertices of the original graph.

**The header used to say this step was blocked, and it was not (`ERRATUM 107`).** The claim was
that the decomposition returns cycle *graphs* rather than walks, "so there is nothing to
rotate". `CycleDecomposition.IsCycleGraph` is *defined* as
`∃ v (p : H.Walk v v), p.IsCycle ∧ p.toSubgraph.spanningCoe = H` — the walk is existentially
bound in the definition — and Mathlib's
`SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle` converts a cycle through an edge
into reachability after deleting it. Neither fact was hard to find; the block was inferred from
the *name* `IsCycleGraph` and never checked against the definition.

**§5 then removes every hypothesis of `reachable_of_odd_pair`, and with them the `4` case.** The
edge-adding route needs to know the two odd vertices are the only ones, distinct and
non-adjacent, and with four odd vertices it needs a choice of pairing. None of that is
necessary, because handshake applies to a single **connected component** just as well as to the
whole graph:

> **`exists_odd_reachable`** — in any finite graph, a vertex of odd degree has another vertex of
> odd degree **that it can reach**. No other hypothesis.

The component is taken as a spanning subgraph on the same vertex type (`compGraph`), so no new
instances are needed; vertices outside the component have degree `0` there and cannot be the
partner handshake produces. §§2–4 are kept because the decomposition itself is the useful object
for anything that wants the circuits and not just the path.

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-! ## 1. The neighbour sets of `G ⊔ edge u v`, in all three cases -/

/-- Away from the two endpoints, adding the edge changes nothing — and this needs no hypothesis
relating `u` and `v` at all. -/
theorem neighborSet_sup_edge_of_ne {w : V} (hwu : w ≠ u) (hwv : w ≠ v) :
    (G ⊔ edge u v).neighborSet w = G.neighborSet w := by
  ext x
  simp only [mem_neighborSet, sup_adj, edge_adj]
  refine ⟨fun h => h.elim id (fun hc => ?_), Or.inl⟩
  rcases hc.1 with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact absurd h1 hwu
  · exact absurd h1 hwv

/-- At `u`, the neighbour set gains exactly `v`. -/
theorem neighborSet_sup_edge_left (hne : u ≠ v) :
    (G ⊔ edge u v).neighborSet u = insert v (G.neighborSet u) := by
  ext x
  -- `rw` rather than `simp`: `simp` normalises the `u = u` produced by `edge_adj` to `True`,
  -- and then the obvious `⟨rfl, rfl⟩` no longer typechecks.
  rw [Set.mem_insert_iff, mem_neighborSet, mem_neighborSet, sup_adj, edge_adj]
  constructor
  · rintro (h | ⟨(⟨-, rfl⟩ | ⟨h1, -⟩), -⟩)
    · exact Or.inr h
    · exact Or.inl rfl
    · exact absurd h1 hne
  · rintro (rfl | h)
    · exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
    · exact Or.inl h

/-- At `v`, symmetrically. -/
theorem neighborSet_sup_edge_right (hne : u ≠ v) :
    (G ⊔ edge u v).neighborSet v = insert u (G.neighborSet v) := by
  rw [show G ⊔ edge u v = G ⊔ edge v u from by rw [edge_comm]]
  exact neighborSet_sup_edge_left hne.symm

/-! ## 2. The parity statement -/

/-- **ADDING THE EDGE MAKES EVERY DEGREE EVEN.** `u` and `v` are the two odd vertices and they
are not already joined, so each gains exactly one neighbour and each count moves from odd to
even; every other vertex is untouched and was even already.

This is the hypothesis `CycleDecomposition.exists_cycle_decomposition` asks for, manufactured
from a graph that fails it at exactly two places. -/
theorem evenDegrees_sup_edge [Finite V] (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hu : ¬ Even (G.neighborSet u).ncard) (hv : ¬ Even (G.neighborSet v).ncard)
    (hrest : ∀ w, w ≠ u → w ≠ v → Even (G.neighborSet w).ncard) :
    EvenDegrees (G ⊔ edge u v) := by
  intro w
  by_cases hwu : w = u
  · subst hwu
    rw [neighborSet_sup_edge_left hne,
      Set.ncard_insert_of_notMem (by simpa [mem_neighborSet] using hnadj) (Set.toFinite _)]
    exact Nat.even_add_one.mpr hu
  by_cases hwv : w = v
  · subst hwv
    rw [neighborSet_sup_edge_right hne,
      Set.ncard_insert_of_notMem
        (by simpa [mem_neighborSet] using fun hc => hnadj hc.symm) (Set.toFinite _)]
    exact Nat.even_add_one.mpr hv
  · rw [neighborSet_sup_edge_of_ne hwu hwv]
    exact hrest w hwu hwv

/-! ## 3. What it unlocks, stated against the estate's own decomposition theorem -/

/-- **THE DECOMPOSITION EXISTS FOR THE REPAIRED GRAPH.** Two odd vertices, one added edge, and
`CycleDecomposition.exists_cycle_decomposition` applies to the result.

Note carefully what the conclusion is about: it decomposes `G ⊔ edge u v`, not `G`. Reading a
`G`-path from `u` to `v` out of it needs a walk, and the decomposition returns cycle *graphs*.
That step is not here. -/
theorem exists_cycle_decomposition_sup_edge [Finite V] (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hu : ¬ Even (G.neighborSet u).ncard) (hv : ¬ Even (G.neighborSet v).ncard)
    (hrest : ∀ w, w ≠ u → w ≠ v → Even (G.neighborSet w).ncard) :
    ∃ L : List (SimpleGraph V), (∀ H ∈ L, IsCycleGraph H) ∧ L.Pairwise Disjoint ∧
      L.foldr (· ⊔ ·) ⊥ = G ⊔ edge u v :=
  exists_cycle_decomposition _ (evenDegrees_sup_edge hne hnadj hu hv hrest)

/-- The added edge really is new: `G` is strictly below the repaired graph, so the
decomposition above is not a decomposition of `G` in disguise. -/
theorem lt_sup_edge_of_odd (hne : u ≠ v) (hnadj : ¬ G.Adj u v) : G < G ⊔ edge u v :=
  lt_sup_edge _ _ _ hne hnadj

/-! ## 4. Cutting the added edge back out

An earlier draft of this file said the decomposition was as far as one could go, because it
returns cycle *graphs* rather than walks and so "there is nothing to rotate". **That was wrong
and is recorded as `ERRATUM 107`.** `CycleDecomposition.IsCycleGraph` is *defined* as
`∃ v (p : H.Walk v v), p.IsCycle ∧ p.toSubgraph.spanningCoe = H` — the walk is right there,
existentially bound — and Mathlib's
`SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle` turns a cycle through an edge into
reachability after deleting it. Both were found by opening the definition instead of reading its
name. -/

/-- Adjacency in a `foldr`-union is adjacency in one of the members. -/
theorem foldr_sup_adj {L : List (SimpleGraph V)} {a b : V} :
    (L.foldr (· ⊔ ·) ⊥).Adj a b ↔ ∃ H ∈ L, H.Adj a b := by
  induction L with
  | nil => simp
  | cons K L ih => simp [ih, or_and_right, exists_or]

/-- A member of the list sits below the union. -/
theorem le_foldr_sup {L : List (SimpleGraph V)} {H : SimpleGraph V} (hH : H ∈ L) :
    H ≤ L.foldr (· ⊔ ·) ⊥ := fun _ _ h => foldr_sup_adj.mpr ⟨H, hH, h⟩

/-- **DELETING AN EDGE OF A DECOMPOSED GRAPH LEAVES ITS ENDPOINTS CONNECTED.** Every edge of a
cycle decomposition lies on one of the cycles, and a cycle through an edge is exactly what
Mathlib's `adj_and_reachable_delete_edges_iff_exists_cycle` consumes. -/
theorem reachable_sdiff_of_cycle_decomposition {L : List (SimpleGraph V)}
    (hcyc : ∀ H ∈ L, IsCycleGraph H) (hsup : L.foldr (· ⊔ ·) ⊥ = G) (huv : G.Adj u v) :
    (G \ fromEdgeSet {s(u, v)}).Reachable u v := by
  classical
  obtain ⟨H, hHL, hHadj⟩ := foldr_sup_adj.mp (hsup ▸ huv)
  obtain ⟨w, p, hp, hEq⟩ := hcyc H hHL
  have hmem : s(u, v) ∈ p.edges := by
    rw [← hEq] at hHadj
    rw [← Walk.adj_toSubgraph_iff_mem_edges]
    simpa using hHadj
  have hle : H ≤ G := hsup ▸ le_foldr_sup hHL
  exact (adj_and_reachable_delete_edges_iff_exists_cycle.mpr
    ⟨w, p.mapLe hle, hp.mapLe hle, p.edges_mapLe_eq_edges hle ▸ hmem⟩).2

/-- Deleting the edge just added gives back exactly the graph it was added to. -/
theorem sup_edge_sdiff_edge (hnadj : ¬ G.Adj u v) :
    (G ⊔ edge u v) \ fromEdgeSet {s(u, v)} = G := by
  have hE : (edge u v : SimpleGraph V) = fromEdgeSet {s(u, v)} := rfl
  rw [← hE]
  ext a b
  simp only [sdiff_adj, sup_adj, edge_adj]
  constructor
  · rintro ⟨h | h, hn⟩
    · exact h
    · exact absurd h hn
  · intro h
    refine ⟨Or.inl h, ?_⟩
    rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), -⟩
    · exact hnadj h
    · exact hnadj h.symm

/-- **THE OPEN PATH.** Two odd vertices, non-adjacent: they are connected **in `G` itself**.
Add the edge between them, decompose the result into cycles, and cut the added edge back out —
the cycle carrying it becomes a `G`-walk from `u` to `v`.

This is the circuits-plus-one-path statement in the only form that matters downstream: not a
list of pieces, but a walk between the two odd vertices, in the original graph. -/
theorem reachable_of_odd_pair [Finite V] (hne : u ≠ v) (hnadj : ¬ G.Adj u v)
    (hu : ¬ Even (G.neighborSet u).ncard) (hv : ¬ Even (G.neighborSet v).ncard)
    (hrest : ∀ w, w ≠ u → w ≠ v → Even (G.neighborSet w).ncard) :
    G.Reachable u v := by
  obtain ⟨L, hcyc, -, hsup⟩ := exists_cycle_decomposition_sup_edge hne hnadj hu hv hrest
  have hadj : (G ⊔ edge u v).Adj u v :=
    Or.inr ((edge_adj u v u v).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
  exact sup_edge_sdiff_edge hnadj ▸ reachable_sdiff_of_cycle_decomposition hcyc hsup hadj

/-! ## 5. The same conclusion with three hypotheses removed

`reachable_of_odd_pair` needs to know that `u` and `v` are the **only** odd vertices, that they
are distinct, and that they are non-adjacent. None of that is necessary. The handshake lemma
applies to any finite graph, and it applies just as well to **one connected component of it** —
so an odd vertex always has an odd partner *in its own component*, and the partner is therefore
reachable.

The component is taken as a spanning subgraph on the same vertex type rather than as an induced
subgraph on a subtype, which keeps every instance the ambient graph already had. -/

/-- `G` with every edge outside `u`'s component deleted. Same vertex type, so no new `Fintype`
or `DecidableEq` is needed anywhere below. -/
@[simps]
def compGraph (G : SimpleGraph V) (u : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∧ G.Reachable u a
  symm := fun _ _ ⟨hab, hua⟩ => ⟨hab.symm, hua.trans hab.reachable⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem compGraph_le (G : SimpleGraph V) (u : V) : compGraph G u ≤ G := fun _ _ h => h.1

/-- Inside the component, `compGraph` has the neighbours `G` has. -/
theorem neighborSet_compGraph_of_reachable {u w : V} (h : G.Reachable u w) :
    (compGraph G u).neighborSet w = G.neighborSet w := by
  ext x; exact ⟨fun hx => hx.1, fun hx => ⟨hx, h⟩⟩

/-- Outside it, no neighbours at all. -/
theorem neighborSet_compGraph_of_not_reachable {u w : V} (h : ¬ G.Reachable u w) :
    (compGraph G u).neighborSet w = ∅ := by
  ext x; exact ⟨fun hx => absurd hx.2 h, fun hx => hx.elim⟩

/-- **AN ODD VERTEX HAS AN ODD PARTNER IT CAN REACH.** No hypothesis beyond finiteness and the
oddness of `u`: handshake applied to `u`'s component, where every vertex outside the component
has degree `0` and so cannot be the partner the lemma produces.

This is `reachable_of_odd_pair` with `u ≠ v`, `¬ G.Adj u v` and "these are the only two odd
vertices" all dropped. -/
theorem exists_odd_reachable [Finite V] {u : V} (hu : ¬ Even (G.neighborSet u).ncard) :
    ∃ v, v ≠ u ∧ ¬ Even (G.neighborSet v).ncard ∧ G.Reachable u v := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hself : (compGraph G u).neighborSet u = G.neighborSet u :=
    neighborSet_compGraph_of_reachable (Reachable.refl u)
  have hoddu : Odd ((compGraph G u).degree u) := by
    rw [degree_eq_ncard_neighborSet, hself]
    exact Nat.not_even_iff_odd.mp hu
  obtain ⟨w, hwu, hw⟩ :=
    (compGraph G u).exists_ne_odd_degree_of_exists_odd_degree u hoddu
  have hreach : G.Reachable u w := by
    by_contra hc
    rw [degree_eq_ncard_neighborSet, neighborSet_compGraph_of_not_reachable hc] at hw
    simp at hw
  refine ⟨w, hwu, ?_, hreach⟩
  rw [← neighborSet_compGraph_of_reachable hreach, ← degree_eq_ncard_neighborSet]
  exact Nat.not_even_iff_odd.mpr hw

end SimpleGraph
