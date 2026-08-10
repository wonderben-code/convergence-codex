import ContourCircuits

/-!
# Counting the circuits a contour decomposes into

`CycleDecomposition` says an even-degree graph *is* an edge-disjoint union of
circuits. Peierls does not use that sentence; it uses the **count** that follows
from it — a contour of length `|γ|` cannot be made of more than `|γ| / 3` circuits,
because every circuit has at least three edges. This file supplies that arithmetic.

## What is here

* `SimpleGraph.ncard_edgeSet_spanningCoe_toSubgraph` — a circuit's edge count is its
  walk's length, so `IsCycleGraph.three_le_ncard_edgeSet` gives the `3 ≤` that does
  the work. A cycle is a trail, so its edge list has no repeats, so counting the set
  and counting the list agree.
* `SimpleGraph.ncard_edgeSet_foldr_sup` — over a pairwise edge-disjoint list, the
  edge counts add.
* `SimpleGraph.three_mul_length_le_ncard_edgeSet` — hence `3 * (number of circuits)
  ≤ (number of edges)` for any decomposition.
* `ContourCircuits.three_mul_card_le_card_contour` — the same read on this estate's
  contour, under the hypothesis §2 of `ContourCircuits` shows is a real one.

## What is not here

Nothing about *which* circuits, nothing about lengths individually beyond the bound,
and nothing about the plane. The Peierls estimate needs the number of circuits of a
given length *surrounding a fixed site*, and "surrounds" is still undefined in this
estate. This bounds the number of pieces, not the number of shapes.
-/

namespace SimpleGraph

variable {V : Type*}

/-! ## 1. A circuit has as many edges as it has steps -/

/-- The edge set of a walk, as a set, is the set of members of its edge list. -/
theorem edgeSet_spanningCoe_toSubgraph {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    (p.toSubgraph.spanningCoe : SimpleGraph V).edgeSet = {e | e ∈ p.edges} := by
  ext e
  induction e using Sym2.ind with
  | _ a b => simp

/-- **A circuit has exactly as many edges as its walk has steps.** A cycle is a
trail, so `p.edges` has no duplicates and the set and the list are counted alike.

Stated about the walk's own graph rather than about an arbitrary `H` equal to it,
because the walk's *type* mentions the graph: rewriting `H` in a goal that still
contains `p` is not type correct. `IsCycleGraph.three_le_ncard_edgeSet` does the
transport, in a goal `p` has already left. -/
theorem ncard_edgeSet_spanningCoe_toSubgraph {G : SimpleGraph V} {v : V} {p : G.Walk v v}
    (hp : p.IsCycle) :
    (p.toSubgraph.spanningCoe : SimpleGraph V).edgeSet.ncard = p.length := by
  classical
  have hset : (p.toSubgraph.spanningCoe : SimpleGraph V).edgeSet = ↑p.edges.toFinset := by
    rw [edgeSet_spanningCoe_toSubgraph]; ext e; simp
  rw [hset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp.edges_nodup,
    Walk.length_edges]

/-- **Every circuit has at least three edges.** -/
theorem IsCycleGraph.three_le_ncard_edgeSet {H : SimpleGraph V} (h : IsCycleGraph H) :
    3 ≤ H.edgeSet.ncard := by
  obtain ⟨v, p, hp, hH⟩ := h
  rw [← hH, ncard_edgeSet_spanningCoe_toSubgraph hp]
  exact hp.three_le_length

/-! ## 2. Edge counts add over an edge-disjoint list -/

theorem disjoint_edgeSet_of_disjoint {H K : SimpleGraph V} (hd : Disjoint H K) :
    Disjoint H.edgeSet K.edgeSet := by
  rw [Set.disjoint_left]
  intro e heH heK
  induction e using Sym2.ind with
  | _ a b => exact hd.le_bot (⟨heH, heK⟩ : (H ⊓ K).Adj a b)

/-- Over a pairwise edge-disjoint list, the edge counts add. -/
theorem ncard_edgeSet_foldr_sup [Finite V] {L : List (SimpleGraph V)}
    (hpair : L.Pairwise Disjoint) :
    (L.foldr (· ⊔ ·) ⊥).edgeSet.ncard = (L.map fun H => H.edgeSet.ncard).sum := by
  induction L with
  | nil => simp
  | cons K L ih =>
    obtain ⟨hKL, hpair'⟩ := List.pairwise_cons.mp hpair
    have hsplit : ((K ⊔ L.foldr (· ⊔ ·) ⊥).edgeSet)
        = K.edgeSet ∪ (L.foldr (· ⊔ ·) ⊥).edgeSet := by
      ext e; induction e using Sym2.ind with | _ a b => simp
    rw [List.foldr_cons, hsplit,
      Set.ncard_union_eq (disjoint_edgeSet_of_disjoint (disjoint_foldr_sup hKL)),
      ih hpair', List.map_cons, List.sum_cons]

/-! ## 3. The bound -/

/-- **Three times the number of circuits is at most the number of edges.** Each
circuit contributes at least three edges and they do not share any. -/
theorem three_mul_length_le_ncard_edgeSet [Finite V] {G : SimpleGraph V}
    {L : List (SimpleGraph V)} (hcyc : ∀ H ∈ L, IsCycleGraph H)
    (hpair : L.Pairwise Disjoint) (hsup : L.foldr (· ⊔ ·) ⊥ = G) :
    3 * L.length ≤ G.edgeSet.ncard := by
  subst hsup
  rw [ncard_edgeSet_foldr_sup hpair]
  induction L with
  | nil => simp
  | cons K L ih =>
    have hK : 3 ≤ K.edgeSet.ncard := (hcyc K (List.mem_cons_self ..)).three_le_ncard_edgeSet
    have hrest : 3 * L.length ≤ (L.map fun H => H.edgeSet.ncard).sum :=
      ih (fun H hH => hcyc H (List.mem_cons_of_mem _ hH))
        (List.pairwise_cons.mp hpair).2
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- **A graph with all degrees even is an edge-disjoint union of at most
`edges / 3` circuits.** The decomposition and the bound in one statement. -/
theorem exists_cycle_decomposition_three_mul_le [Finite V] (G : SimpleGraph V)
    (h : EvenDegrees G) :
    ∃ L : List (SimpleGraph V), (∀ H ∈ L, IsCycleGraph H) ∧ L.Pairwise Disjoint ∧
      L.foldr (· ⊔ ·) ⊥ = G ∧ 3 * L.length ≤ G.edgeSet.ncard := by
  obtain ⟨L, h1, h2, h3⟩ := G.exists_cycle_decomposition h
  exact ⟨L, h1, h2, h3, three_mul_length_le_ncard_edgeSet h1 h2 h3⟩

end SimpleGraph

namespace ContourCircuits

open IsingFiniteVolume IsingContourEnergy SimpleGraph

variable {n : ℕ}

/-- **The Peierls-shaped statement, on this estate's contour**: whenever the
broken-bond graph has all degrees even, the contour is an edge-disjoint union of
circuits and **three times their number is at most `|γ|`**.

The hypothesis is exactly the one `ContourCircuits.not_evenDegrees_brokenGraph_sigmaOdd`
shows the primal box does not supply in general; this is the statement waiting for the
dual lattice, written down so that the arithmetic is not the thing that is missing. -/
theorem three_mul_card_le_card_contour (σ : Config n) (h : EvenDegrees (brokenGraph σ)) :
    ∃ L : List (SimpleGraph (Site n)), (∀ H ∈ L, IsCycleGraph H) ∧ L.Pairwise Disjoint ∧
      L.foldr (· ⊔ ·) ⊥ = brokenGraph σ ∧ 3 * L.length ≤ (contour σ).card := by
  obtain ⟨L, h1, h2, h3, h4⟩ := (brokenGraph σ).exists_cycle_decomposition_three_mul_le h
  refine ⟨L, h1, h2, h3, ?_⟩
  rwa [contour, ← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]

end ContourCircuits
