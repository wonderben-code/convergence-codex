import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Even degrees force a cycle

This file proves the gate theorem for the Peierls step (wall W3):

> a finite graph in which **every vertex has even degree** and **at least one edge
> exists** cannot be acyclic — it contains a cycle.

Peierls' argument counts *contours*, and a contour is a circuit. The route from
"the boundary of a spin configuration has all degrees even" to "the boundary is a
disjoint union of circuits" begins with exactly this statement: an even-degree
edge set that is not empty must contain a cycle, which can then be peeled off and
the argument repeated. This file proves the base case. **It does not prove the
decomposition**, which is a further induction on the number of edges, and it does
not touch the planar geometry (contours of length `L` surrounding a site, the
`3 ^ |γ|` bound) that W3 actually rests on.

## What Mathlib has, and what it does not

Scope of the search, run 2026-08-10 against Mathlib v4.29.1: every declaration
signature in `Mathlib/` was scanned — **240239** of them — for one mentioning
acyclicity together with any degree notion (`degree`, `minDegree`, `maxDegree`).

* Mentioning `IsAcyclic` and a degree: **0**.
* Mentioning `IsTree` and a degree: **2**, both in
  `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean` —
  `IsTree.minDegree_eq_one_of_nontrivial` and
  `IsTree.exists_vert_degree_one_of_nontrivial`.

So the statement below is not in the library, but it is *not* true that the library
never relates the two notions: it relates them under the extra hypothesis of
**connectivity**, which an even-degree edge set does not have. Listing the results
that would combine to give the statement (the rule that a non-existence claim must
name what nearly gives the thing):

1. `IsTree.exists_vert_degree_one_of_nontrivial` — a nontrivial tree has a leaf.
2. `IsAcyclic.isTree_connectedComponent` — a connected component of an acyclic graph
   is a tree. **This is what removes the connectivity hypothesis**, and an earlier
   attempt at this theorem missed it and went looking for a longest-path argument
   instead.
3. A transport of degrees between a component and its ambient graph — the only piece
   that is genuinely absent, and the only piece proved from scratch here.

## What makes it go through

Restrict to the connected component of one endpoint of the edge. By (2) it is a tree;
it is nontrivial because the edge has two distinct ends, both of which lie in it; so
by (1) it has a vertex of degree one *inside the component*. Transporting that back to
the ambient graph is (3), `SimpleGraph.ConnectedComponent.degree_toSimpleGraph`: a
component contains all the neighbours of each of its vertices, so the induced graph on
a component loses no edges at its own vertices, and degrees measured inside it agree
with degrees measured in the whole graph.

## Main results

* `SimpleGraph.ConnectedComponent.neighborSetEquiv` — the neighbours of a vertex
  inside its own component are its neighbours in the graph.
* `SimpleGraph.ConnectedComponent.degree_toSimpleGraph` — hence the degrees agree.
* `SimpleGraph.exists_degree_one_of_isAcyclic` — a finite acyclic graph with an edge
  has a vertex of degree one. This trades the connectivity hypothesis of
  `IsTree.exists_vert_degree_one_of_nontrivial` for the hypothesis that an edge
  exists, which under connectivity is implied by nontriviality — so the original is
  recovered from it, and `IsTree.exists_vert_degree_one_of_nontrivial'` does exactly
  that as a check. `bot_nontrivial_no_degree_one` shows the trade is forced.
* `SimpleGraph.not_isAcyclic_of_forall_degree_ne_one` and
  `SimpleGraph.exists_isCycle_of_forall_degree_ne_one` — the gate theorem at its
  natural strength: no leaf and an edge forbid acyclicity.
* `SimpleGraph.not_isAcyclic_of_forall_even_degree` and
  `SimpleGraph.exists_isCycle_of_forall_even_degree` — the even-degree corollaries,
  in negative and positive form. These are what Peierls consumes.
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-! ## 1. Degrees inside a connected component

A connected component is closed under adjacency, so the graph induced on it keeps
every edge at every one of its vertices. Nothing here needs acyclicity. -/

namespace ConnectedComponent

/-- The neighbours of a vertex `v` in the graph induced on its own connected
component are exactly its neighbours in the ambient graph. The forward map is the
coercion; the inverse is available because a component is closed under adjacency
(`ConnectedComponent.mem_supp_of_adj_mem_supp`). -/
@[simps]
def neighborSetEquiv (C : G.ConnectedComponent) (v : C) :
    C.toSimpleGraph.neighborSet v ≃ G.neighborSet (v : V) where
  toFun w := ⟨(w : C), w.2⟩
  invFun u := ⟨⟨(u : V), C.mem_supp_of_adj_mem_supp v.2 u.2⟩, u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The degree of a vertex in the graph induced on its own connected component
equals its degree in the ambient graph. -/
theorem degree_toSimpleGraph (C : G.ConnectedComponent) (v : C)
    [Fintype (C.toSimpleGraph.neighborSet v)] [Fintype (G.neighborSet (v : V))] :
    C.toSimpleGraph.degree v = G.degree (v : V) := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact Fintype.card_congr (C.neighborSetEquiv v)

end ConnectedComponent

/-! ## 2. An acyclic graph with an edge has a leaf

`IsTree.exists_vert_degree_one_of_nontrivial` says a nontrivial tree has a vertex of
degree one. Dropping connectivity costs nothing once one knows that each component of
an acyclic graph is a tree — but the hypothesis has to change shape, and the change is
forced rather than convenient: `bot_nontrivial_no_degree_one` below exhibits a
nontrivial acyclic graph with no vertex of degree one, so "nontrivial" alone cannot
survive the removal of connectivity. What replaces it is "has an edge". -/

/-- **A finite acyclic graph with at least one edge has a vertex of degree one.**

This is `IsTree.exists_vert_degree_one_of_nontrivial` with connectivity removed. The
proof restricts to the connected component of one endpoint of the edge, which is a
tree by `IsAcyclic.isTree_connectedComponent`, and transports the resulting degree
back along `ConnectedComponent.degree_toSimpleGraph`. -/
theorem exists_degree_one_of_isAcyclic [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {a b : V} (hab : G.Adj a b) : ∃ v, G.degree v = 1 := by
  classical
  set C := G.connectedComponentMk a with hCdef
  have ha : a ∈ C.supp := rfl
  have hb : b ∈ C.supp := C.mem_supp_of_adj_mem_supp ha hab
  haveI : Fintype (C : Type _) := Fintype.ofFinite _
  haveI : Nontrivial (C : Type _) :=
    ⟨⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab.ne (congrArg Subtype.val h)⟩⟩
  haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  obtain ⟨v, hv⟩ := (hG.isTree_connectedComponent C).exists_vert_degree_one_of_nontrivial
  exact ⟨(v : V), by rw [← C.degree_toSimpleGraph v]; exact hv⟩

/-- The same statement with the edge presented as `G ≠ ⊥` rather than as a named pair. -/
theorem exists_degree_one_of_isAcyclic_of_ne_bot [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.IsAcyclic) (hne : G ≠ ⊥) : ∃ v, G.degree v = 1 := by
  obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hne
  exact G.exists_degree_one_of_isAcyclic hG hab

/-- Consistency check on the previous theorem (it is advertised as a generalisation, so
the thing it generalises must follow from it): a nontrivial tree has a vertex of degree
one. Recovered here from `exists_degree_one_of_isAcyclic` by producing the edge from
connectivity, which is where the nontriviality hypothesis is spent. -/
theorem IsTree.exists_vert_degree_one_of_nontrivial' [Fintype V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : G.IsTree) : ∃ v, G.degree v = 1 := by
  obtain ⟨v⟩ := (inferInstance : Nonempty V)
  obtain ⟨w, hw⟩ := h.connected.preconnected.exists_adj_of_nontrivial v
  exact G.exists_degree_one_of_isAcyclic h.isAcyclic hw

/-- Sharpness of the hypothesis change: the edgeless graph on two vertices is acyclic
and its vertex type is nontrivial, yet no vertex has degree one. So `exists_degree_one_
of_isAcyclic` cannot be stated with `Nontrivial V` in place of the edge, and the
connectivity in `IsTree.exists_vert_degree_one_of_nontrivial` is doing real work. -/
theorem bot_nontrivial_no_degree_one :
    (⊥ : SimpleGraph (Fin 2)).IsAcyclic ∧ Nontrivial (Fin 2) ∧
      ∀ v, (⊥ : SimpleGraph (Fin 2)).degree v ≠ 1 :=
  ⟨isAcyclic_bot, inferInstance, fun v => by simp⟩

/-! ## 3. The gate theorem

What the leaf theorem really forbids is a *degree-one* vertex, so the gate is stated
first at that generality and the even-degree form is read off from it: an even number
is not `1`. Stating it this way costs nothing and covers, for instance, edge sets all
of whose degrees are `0` or `2` — the shape a contour actually has — without asking
for evenness at the vertices of degree `0`. -/

/-- **A finite graph with no vertex of degree one and at least one edge is not
acyclic.** The strongest form of the gate: `exists_degree_one_of_isAcyclic` says an
acyclic graph with an edge *has* a leaf, so forbidding leaves forbids acyclicity. -/
theorem not_isAcyclic_of_forall_degree_ne_one [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≠ 1) {a b : V} (hab : G.Adj a b) :
    ¬ G.IsAcyclic := by
  intro hG
  obtain ⟨v, hv⟩ := G.exists_degree_one_of_isAcyclic hG hab
  exact hdeg v hv

/-- **A finite graph with all degrees even and at least one edge is not acyclic.** -/
theorem not_isAcyclic_of_forall_even_degree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) {a b : V} (hab : G.Adj a b) : ¬ G.IsAcyclic :=
  G.not_isAcyclic_of_forall_degree_ne_one (fun v hv => by simpa [hv] using heven v) hab

/-- **A finite graph with no vertex of degree one and at least one edge contains a
cycle.** -/
theorem exists_isCycle_of_forall_degree_ne_one [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ v, G.degree v ≠ 1) {a b : V} (hab : G.Adj a b) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  by_contra hcon
  exact G.not_isAcyclic_of_forall_degree_ne_one hdeg hab fun v c hc => hcon ⟨v, c, hc⟩

/-- **A finite graph with all degrees even and at least one edge contains a cycle.**

This is the form the Peierls step consumes: the boundary of a spin configuration has
all degrees even, so as long as it is not empty it contains a circuit, which can be
removed to leave a smaller even-degree edge set. -/
theorem exists_isCycle_of_forall_even_degree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v)) {a b : V} (hab : G.Adj a b) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  by_contra hcon
  exact G.not_isAcyclic_of_forall_even_degree heven hab fun v c hc => hcon ⟨v, c, hc⟩

/-- The cycle form with the edge presented as `G ≠ ⊥`. -/
theorem exists_isCycle_of_forall_even_degree_of_ne_bot [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (heven : ∀ v, Even (G.degree v)) (hne : G ≠ ⊥) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hne
  exact G.exists_isCycle_of_forall_even_degree heven hab

/-- Contrapositive, stated positively: an acyclic graph with an edge has a vertex of
odd degree. Recorded separately because this is the shape the handshake-lemma route
would have produced, and it is worth having both spellings addressable. -/
theorem exists_odd_degree_of_isAcyclic [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) {a b : V} (hab : G.Adj a b) : ∃ v, Odd (G.degree v) := by
  obtain ⟨v, hv⟩ := G.exists_degree_one_of_isAcyclic hG hab
  exact ⟨v, hv ▸ odd_one⟩

end SimpleGraph
