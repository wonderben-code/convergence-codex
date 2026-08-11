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

**It is not the decomposition theorem for open paths, and the gap is named precisely.** From a
cycle of `G ⊔ edge u v` through the added edge one wants to delete that edge and read off a
`G`-path from `u` to `v`. Deleting an edge from a cycle *does* leave a path — that is the
content of `SimpleGraph.Walk.IsCycle`'s rotation — but the estate's decomposition returns a
`List (SimpleGraph V)` of cycle **graphs** (`IsCycleGraph`), not walks, so there is no walk to
rotate. Recovering a walk from an `IsCycleGraph` is a separate theorem and this file does not
have it. **`S3bResidue.ClusterReachesRim` is therefore still unproved**, and the residue is
now smaller and sharper than "a circuits-plus-paths theorem": it is *walk extraction from
`IsCycleGraph`*.

**The `4` case is not handled.** With four odd vertices one adds two edges, and which two
pairs to join is a choice the graph does not make for you. Nothing here rules the case out and
nothing here treats it; `RimParity.card_oddExt_eq_zero_or_two_or_four` leaves it open.

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

end SimpleGraph
