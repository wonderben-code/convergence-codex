import EvenDegreeCycle

/-!
# An even-degree graph is an edge-disjoint union of cycles

`EvenDegreeCycle` proved the gate: a finite graph with all degrees even and at
least one edge contains a cycle. That is the base case of the statement Peierls
actually consumes, and this file proves the statement:

> a finite graph has all degrees even **if and only if** its edges split into
> finitely many pairwise edge-disjoint cycles.

The forward direction is the induction the gate was the base case of — take a
cycle, delete its edges, the degrees stay even, the edge count drops, recurse.
The converse is proved too, so the result is a characterisation rather than a
one-way decomposition: degrees add over edge-disjoint graphs, and a cycle
contributes `2` at each of its vertices and `0` elsewhere.

## What this does *not* do

It does not touch the planar geometry that wall W3 rests on: contours of a given
length surrounding a fixed site, and the `3 ^ |γ|` counting bound. The
decomposition says a contour set *is* a union of circuits; it says nothing about
how many circuits of a given length there are, or which sites they surround.

## Degrees without decidability

The induction builds `G \ H` from `G`, and `SimpleGraph.degree` needs a `Fintype`
instance on the neighbour set which would have to be rebuilt (classically) at each
step — leaving the statement's `degree` and the induction's `degree` computed from
different instances. To avoid that entirely, evenness is stated as `EvenDegrees`,
through `Set.ncard` of the neighbour set, which needs no instance at all;
`evenDegrees_iff_forall_even_degree` is the bridge back to `degree` and is the one
place an instance is used.

## Main results

* `SimpleGraph.EvenDegrees` — all degrees even, instance-free.
* `SimpleGraph.IsCycleGraph` — the graph is exactly the edge set of one cycle.
* `SimpleGraph.EvenDegrees.sdiff_cycle` — cutting a cycle out keeps degrees even.
* `SimpleGraph.exists_cycle_decomposition` — the forward direction.
* `SimpleGraph.evenDegrees_of_cycle_decomposition` — the converse.
* `SimpleGraph.evenDegrees_iff_exists_cycle_decomposition` — the characterisation.
-/

namespace SimpleGraph

variable {V : Type*}

/-! ## 1. Degrees as cardinalities

Everything below is stated with `Set.ncard`, which carries no decidability or
finiteness instance. This section is the bridge to `SimpleGraph.degree`. -/

/-- The degree of a vertex is the cardinality of its neighbour set. -/
theorem degree_eq_ncard_neighborSet (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = (G.neighborSet v).ncard := by
  rw [← card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card']
  simp [Set.toFinset_card]

/-- Every vertex has even degree. Stated through `Set.ncard` so that it survives the
graph surgery below without dragging a decidability instance along. -/
def EvenDegrees (G : SimpleGraph V) : Prop := ∀ v, Even (G.neighborSet v).ncard

theorem evenDegrees_iff_forall_even_degree [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : EvenDegrees G ↔ ∀ v, Even (G.degree v) := by
  refine forall_congr' fun v => ?_
  rw [degree_eq_ncard_neighborSet]

@[simp] theorem evenDegrees_bot : EvenDegrees (⊥ : SimpleGraph V) := by
  intro v
  simp [show (⊥ : SimpleGraph V).neighborSet v = ∅ from by ext w; simp]

/-! ## 2. Cutting a cycle out of a graph

The only fact about cycles used here is Mathlib's
`Walk.IsCycle.ncard_neighborSet_toSubgraph_eq_two`: a cycle has exactly two
neighbours at each vertex it visits. Off its support it has none, which is the
second lemma below. -/

theorem neighborSet_sdiff (G H : SimpleGraph V) (v : V) :
    (G \ H).neighborSet v = G.neighborSet v \ H.neighborSet v := by
  ext w; simp [SimpleGraph.sdiff_adj]

theorem ncard_neighborSet_sdiff [Finite V] {G H : SimpleGraph V} (hle : H ≤ G) (v : V) :
    ((G \ H).neighborSet v).ncard = (G.neighborSet v).ncard - (H.neighborSet v).ncard := by
  rw [neighborSet_sdiff]
  exact Set.ncard_diff fun w hw => hle hw

/-- Off its own support, a walk has no neighbours. -/
theorem neighborSet_spanningCoe_toSubgraph_eq_empty {G : SimpleGraph V} {u w : V}
    (p : G.Walk u w) {v : V} (hv : v ∉ p.support) :
    (p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet v = ∅ := by
  ext x
  simp only [mem_neighborSet, Subgraph.spanningCoe_adj, Set.mem_empty_iff_false, iff_false]
  intro hadj
  exact hv (by simpa [Walk.verts_toSubgraph] using hadj.fst_mem)

/-- A cycle contributes exactly `2` at each vertex it visits. -/
theorem ncard_neighborSet_cycle_of_mem {G : SimpleGraph V} {u : V} {p : G.Walk u u}
    (hp : p.IsCycle) {v : V} (hv : v ∈ p.support) :
    ((p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet v).ncard = 2 := by
  rw [show (p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet v
      = p.toSubgraph.neighborSet v from by ext w; simp]
  exact hp.ncard_neighborSet_toSubgraph_eq_two hv

/-- A cycle contributes an even number of neighbours at *every* vertex: `2` on its
support and `0` off it. This is all the induction below needs. -/
theorem even_ncard_neighborSet_cycle {G : SimpleGraph V} {u : V} {p : G.Walk u u}
    (hp : p.IsCycle) (v : V) :
    Even ((p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet v).ncard := by
  by_cases hv : v ∈ p.support
  · rw [ncard_neighborSet_cycle_of_mem hp hv]; exact even_two
  · rw [neighborSet_spanningCoe_toSubgraph_eq_empty p hv, Set.ncard_empty]; exact ⟨0, rfl⟩

/-- **Deleting the edges of a cycle preserves evenness of every degree.** The
subtraction is truncated and it does not matter: `Even.tsub` needs no inequality
between the two even numbers, because if the second exceeds the first the
difference is `0`, which is even. -/
theorem EvenDegrees.sdiff_cycle [Finite V] {G : SimpleGraph V} (h : EvenDegrees G)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    EvenDegrees (G \ p.toSubgraph.spanningCoe) := by
  intro v
  rw [ncard_neighborSet_sdiff (Subgraph.spanningCoe_le _)]
  exact Even.tsub (h v) (even_ncard_neighborSet_cycle hp v)

/-! ## 3. The cycle graphs

`IsCycleGraph H` says `H` is precisely the edge set of a single cycle. The walk is
a walk *in `H`*, so the predicate is self-contained: it does not mention whatever
larger graph the cycle was originally found in. -/

/-- `H` is the edge set of a single cycle. -/
def IsCycleGraph (H : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : H.Walk v v), p.IsCycle ∧ p.toSubgraph.spanningCoe = H

/-- The graph cut out by a cycle is a cycle graph. The walk has to be moved into the
smaller graph, which is `Walk.transfer`; `Walk.IsCycle.transfer` carries the cycle
property across and `Walk.edges_transfer` says the edge list is unchanged, which via
`Walk.adj_toSubgraph_iff_mem_edges` is what makes the two subgraphs agree. -/
theorem isCycleGraph_spanningCoe_toSubgraph {G : SimpleGraph V} {u : V} {p : G.Walk u u}
    (hp : p.IsCycle) : IsCycleGraph (p.toSubgraph.spanningCoe : SimpleGraph V) := by
  have hmem : ∀ e ∈ p.edges, e ∈ (p.toSubgraph.spanningCoe : SimpleGraph V).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b => simpa [Walk.adj_toSubgraph_iff_mem_edges] using he
  refine ⟨u, p.transfer _ hmem, hp.transfer hmem, ?_⟩
  ext a b
  simp only [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges, Walk.edges_transfer]

/-- A cycle graph has all degrees even: `2` on the cycle, `0` off it. -/
theorem IsCycleGraph.evenDegrees {H : SimpleGraph V} (h : IsCycleGraph H) : EvenDegrees H := by
  obtain ⟨v, p, hp, hEq⟩ := h
  intro w
  rw [← hEq]
  exact even_ncard_neighborSet_cycle hp w

/-! ## 4. Sums over an edge-disjoint list

`Disjoint H K` for simple graphs is `H ⊓ K = ⊥`, i.e. no shared edge. Shared
*vertices* are allowed, and the first lemma is that they cost nothing: if two graphs
share no edge then no vertex has a common neighbour in both, so the neighbour sets
are disjoint and the cardinalities add. -/

theorem le_foldr_sup_of_mem {L : List (SimpleGraph V)} {H : SimpleGraph V} (hH : H ∈ L) :
    H ≤ L.foldr (· ⊔ ·) ⊥ := by
  induction L with
  | nil => simp at hH
  | cons K L ih =>
    rcases List.mem_cons.mp hH with rfl | h
    · exact le_sup_left
    · exact le_trans (ih h) le_sup_right

theorem disjoint_foldr_sup {K : SimpleGraph V} {L : List (SimpleGraph V)}
    (h : ∀ M ∈ L, Disjoint K M) : Disjoint K (L.foldr (· ⊔ ·) ⊥) := by
  induction L with
  | nil => simp
  | cons M L ih =>
    rw [List.foldr_cons]
    exact disjoint_sup_right.mpr
      ⟨h M (List.mem_cons_self ..), ih fun N hN => h N (List.mem_cons_of_mem _ hN)⟩

theorem ncard_neighborSet_sup_of_disjoint [Finite V] {H K : SimpleGraph V}
    (hd : Disjoint H K) (v : V) :
    ((H ⊔ K).neighborSet v).ncard = (H.neighborSet v).ncard + (K.neighborSet v).ncard := by
  have hsplit : (H ⊔ K).neighborSet v = H.neighborSet v ∪ K.neighborSet v := by
    ext w; simp
  have hdisj : Disjoint (H.neighborSet v) (K.neighborSet v) := by
    rw [Set.disjoint_left]
    intro w hw hw'
    exact hd.le_bot (⟨hw, hw'⟩ : (H ⊓ K).Adj v w)
  rw [hsplit, Set.ncard_union_eq hdisj]

/-! ## 5. The decomposition -/

private theorem exists_cycle_decomposition_aux [Finite V] :
    ∀ (n : ℕ) (G : SimpleGraph V), EvenDegrees G → G.edgeSet.ncard ≤ n →
      ∃ L : List (SimpleGraph V), (∀ H ∈ L, IsCycleGraph H) ∧ L.Pairwise Disjoint ∧
        L.foldr (· ⊔ ·) ⊥ = G := by
  intro n
  induction n with
  | zero =>
    intro G _ hcard
    have hE : G.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite _)).mp (Nat.le_zero.mp hcard)
    exact ⟨[], by simp, by simp, by simp [← edgeSet_eq_empty.mp hE]⟩
  | succ n ih =>
    intro G h hcard
    by_cases hbot : G = ⊥
    · exact ⟨[], by simp, by simp, by simp [hbot]⟩
    · classical
      haveI : Fintype V := Fintype.ofFinite V
      obtain ⟨u, p, hp⟩ :=
        G.exists_isCycle_of_forall_even_degree_of_ne_bot
          ((G.evenDegrees_iff_forall_even_degree).mp h) hbot
      set H : SimpleGraph V := p.toSubgraph.spanningCoe with hHdef
      have hHle : H ≤ G := Subgraph.spanningCoe_le _
      have hHadj : H.Adj u p.snd := p.toSubgraph_adj_snd hp.not_nil
      have hss : (G \ H).edgeSet ⊂ G.edgeSet := by
        refine edgeSet_ssubset_edgeSet.mpr (lt_of_le_of_ne sdiff_le fun hEq => ?_)
        have hadj : (G \ H).Adj u p.snd := by rw [hEq]; exact hHle hHadj
        exact hadj.2 hHadj
      have hlt : (G \ H).edgeSet.ncard < G.edgeSet.ncard := Set.ncard_lt_ncard hss
      obtain ⟨L, hL1, hL2, hL3⟩ := ih (G \ H) (h.sdiff_cycle hp) (by omega)
      refine ⟨H :: L, ?_, ?_, ?_⟩
      · intro K hK
        rcases List.mem_cons.mp hK with rfl | hK
        · exact isCycleGraph_spanningCoe_toSubgraph hp
        · exact hL1 K hK
      · refine List.pairwise_cons.mpr ⟨fun K hK => ?_, hL2⟩
        exact disjoint_sdiff_self_right.mono_right (hL3 ▸ le_foldr_sup_of_mem hK)
      · rw [List.foldr_cons, hL3, sup_sdiff_cancel_right hHle]

/-- **A finite graph with all degrees even is the edge-disjoint union of finitely
many cycles.** The list may be empty, which is the edgeless case. -/
theorem exists_cycle_decomposition [Finite V] (G : SimpleGraph V) (h : EvenDegrees G) :
    ∃ L : List (SimpleGraph V), (∀ H ∈ L, IsCycleGraph H) ∧ L.Pairwise Disjoint ∧
      L.foldr (· ⊔ ·) ⊥ = G :=
  exists_cycle_decomposition_aux _ G h le_rfl

/-- **Conversely, an edge-disjoint union of cycles has all degrees even.** -/
theorem evenDegrees_of_cycle_decomposition [Finite V] {G : SimpleGraph V}
    {L : List (SimpleGraph V)} (hcyc : ∀ H ∈ L, IsCycleGraph H) (hpair : L.Pairwise Disjoint)
    (hsup : L.foldr (· ⊔ ·) ⊥ = G) : EvenDegrees G := by
  subst hsup
  induction L with
  | nil => simp
  | cons K L ih =>
    obtain ⟨hKL, hpair'⟩ := List.pairwise_cons.mp hpair
    intro v
    rw [List.foldr_cons, ncard_neighborSet_sup_of_disjoint (disjoint_foldr_sup hKL)]
    exact Even.add ((hcyc K (List.mem_cons_self ..)).evenDegrees v)
      (ih (fun M hM => hcyc M (List.mem_cons_of_mem _ hM)) hpair' v)

/-- **The characterisation: all degrees even is exactly being an edge-disjoint union
of cycles.** -/
theorem evenDegrees_iff_exists_cycle_decomposition [Finite V] (G : SimpleGraph V) :
    EvenDegrees G ↔ ∃ L : List (SimpleGraph V), (∀ H ∈ L, IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = G :=
  ⟨G.exists_cycle_decomposition,
    fun ⟨_, h1, h2, h3⟩ => evenDegrees_of_cycle_decomposition h1 h2 h3⟩

/-- The decomposition in the form the gate theorem left off: a graph with all degrees
even and at least one edge has a **nonempty** decomposition. -/
theorem exists_cycle_decomposition_ne_nil [Finite V] (G : SimpleGraph V)
    (h : EvenDegrees G) (hne : G ≠ ⊥) :
    ∃ L : List (SimpleGraph V), L ≠ [] ∧ (∀ H ∈ L, IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = G := by
  obtain ⟨L, h1, h2, h3⟩ := G.exists_cycle_decomposition h
  refine ⟨L, ?_, h1, h2, h3⟩
  rintro rfl
  exact hne (by simpa using h3.symm)

end SimpleGraph
