import CyclePathExtract

/-!
# The piece is a path, and residue (a)'s last named step

Four files have taken this one step at a time. `OddVertexAugment` adjoins a vertex to make every
degree even; `CycleRestriction` cuts the cycles back to `V` and gets the edge partition and the
degree signature; `LeftPartWalk` brings a walk, a path and now the **edges** down from `V ⊕ Unit`;
`CyclePathExtract` cuts a cycle open at the added vertex and produces a path in the part. Each
fenced what came next, and the fence `CyclePathExtract` left is the last one:

> the path is a path **in** `leftPart H`, and **nothing shows its edges are exactly
> `leftPart H`'s**, which is what would make the piece *a path graph* rather than *a graph
> containing a path*.

**This proves that.**

## What is proved

**`SimpleGraph.IsPathGraph`** — `H` is the edge set of a single path, defined exactly as
`CycleDecomposition`'s `IsCycleGraph` is defined for cycles, with `IsPath` in place of `IsCycle`.
**This estate had no such predicate**, which is what the previous four fences were about.

**`edges_eq_cons_append`** — the edge list of a cycle based at the added vertex, split: the opening
edge, then the middle walk's edges, then the closing edge. Both outer edges contain the added
vertex, so **an edge between two `Sum.inl` vertices lies in the whole exactly when it lies in the
middle** (`mem_edges_middle_iff`).

**`isPathGraph_leftPart_of_cycle`** — **so when `H` is cut out by a cycle through the added vertex,
`leftPart H` IS a path graph.**

**`isPathGraph_leftPart_of_isCycleGraph`** — the same from any cycle walk cutting out `H` with the
added vertex on it, `Walk.rotate` supplying the basepoint and `rotate_edges` carrying the edge set.

## What is NOT here

**THE DECOMPOSITION IS NOT RESTATED AS ONE THEOREM.**
`CycleRestriction.exists_cycle_parts_decomposition` returns the cycles and their parts; **no theorem
here says "each part is a path graph or a cycle graph"**, because the case where the added vertex is
**off** the cycle needs a cycle in `V ⊕ Unit` carried back along `Sum.inl`, which is a different
lemma and is **not proved**. **Not attempted, no cost claimed** (`ERRATUM 246`). So residue (a) has
its hard half and not its statement.

**NOTHING IS SAID ABOUT WHICH PATH.** `IsPathGraph` is an existential; **no uniqueness** is claimed
and none holds — a path graph is cut out by two walks, one in each direction.

**NO CONVERSE, AND NO CHARACTERISATION.** Nothing says a path graph's `leftPart` came from a cycle.
The degree signature of `CycleRestriction` is **not** proved equivalent to `IsPathGraph`, and it is
not equivalent: a disjoint union of a path and a cycle has the same signature.

**W3 DOES NOT MOVE, AND WOULD NOT MOVE IF RESIDUE (a) CLOSED COMPLETELY.** `ERRATUM 97` is that
circuits-plus-paths is **necessary and not sufficient** for `S3b-ii`'s covering, because it does not
say which piece the plaquette at `x` lies on; residue (b) is untouched here and everywhere. **No
claim is made that the Peierls chain gains anything.**

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no finiteness and no decidability in any
statement** — `Walk.rotate` wants `DecidableEq` and `classical` supplies it inside the one proof
that uses it. `V` is arbitrary and `H` arbitrary on `V ⊕ Unit`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace SimpleGraph

variable {V : Type*}

/-- `H` is the edge set of a single path. The companion of `CycleDecomposition`'s `IsCycleGraph`,
which this estate had for cycles and not for paths. -/
def IsPathGraph (H : SimpleGraph V) : Prop :=
  ∃ (u v : V) (p : H.Walk u v), p.IsPath ∧ p.toSubgraph.spanningCoe = H

end SimpleGraph

namespace LeftPartPathGraph

open CycleRestriction LeftPartWalk CyclePathExtract SimpleGraph

variable {V : Type*} {H : SimpleGraph (V ⊕ Unit)}

/-! ## 1. Splitting the cycle's edge list -/

/-- The edges of a cycle based at the added vertex: the opening edge, the middle walk's edges, the
closing edge. -/
theorem edges_eq_cons_append (p : H.Walk (Sum.inr ()) (Sum.inr ())) (hpn : ¬ p.Nil)
    (htn : ¬ p.tail.Nil) :
    p.edges = s(Sum.inr (), p.snd) :: ((p.tail.dropLast).edges
      ++ [s(p.tail.penultimate, Sum.inr ())]) := by
  have hE1 : p.edges = s(Sum.inr (), p.snd) :: p.tail.edges := by
    conv_lhs => rw [← Walk.cons_tail_eq p hpn]
    rw [Walk.edges_cons]
  have hE2 : p.tail.edges
      = (p.tail.dropLast).edges ++ [s(p.tail.penultimate, Sum.inr ())] := by
    conv_lhs => rw [← Walk.concat_dropLast p.tail (p.tail.adj_penultimate htn)]
    rw [Walk.edges_concat, List.concat_eq_append]
  rw [hE1, hE2]

/-- **AN EDGE BETWEEN TWO OLD VERTICES IS IN THE CYCLE EXACTLY WHEN IT IS IN THE MIDDLE**, because
the two edges dropped both contain the added vertex. -/
theorem mem_edges_middle_iff (p : H.Walk (Sum.inr ()) (Sum.inr ())) (hpn : ¬ p.Nil)
    (htn : ¬ p.tail.Nil) (a b : V) :
    s(Sum.inl a, Sum.inl b) ∈ p.edges ↔ s(Sum.inl a, Sum.inl b) ∈ (p.tail.dropLast).edges := by
  rw [edges_eq_cons_append p hpn htn]
  simp

/-- Reading `H`'s adjacency off the cycle's edge list. Stated separately because rewriting `H`
itself is not type-correct — `p`'s own type mentions it. -/
theorem adj_iff_mem_edges {a : V ⊕ Unit} {p : H.Walk a a}
    (hH : p.toSubgraph.spanningCoe = H) (x y : V ⊕ Unit) :
    H.Adj x y ↔ s(x, y) ∈ p.edges := by
  rw [← Walk.adj_toSubgraph_iff_mem_edges, ← Subgraph.spanningCoe_adj, hH]

/-! ## 2. So the part is a path graph -/

/-- **THE PART CUT OUT BY A CYCLE THROUGH THE ADDED VERTEX IS THE EDGE SET OF A SINGLE PATH.** -/
theorem isPathGraph_leftPart_of_cycle (p : H.Walk (Sum.inr ()) (Sum.inr ()))
    (hp : p.IsCycle) (hH : p.toSubgraph.spanningCoe = H) : IsPathGraph (leftPart H) := by
  have hpn : ¬ p.Nil := hp.not_nil
  have htn : ¬ p.tail.Nil := by
    rw [Walk.nil_iff_length_eq]
    have h3 := hp.three_le_length
    have := Walk.length_tail_add_one hpn
    omega
  obtain ⟨hnotmem, hnodup⟩ := notMem_support_dropLast_tail p hp
  have hsnd : H.Adj (Sum.inr ()) p.snd := p.adj_snd hpn
  have hpen : H.Adj p.tail.penultimate (Sum.inr ()) := p.tail.adj_penultimate htn
  obtain ⟨y, hy'⟩ := eq_inl_of_ne hsnd.ne'
  obtain ⟨z, hz'⟩ := eq_inl_of_ne hpen.ne
  obtain ⟨q, hs, he⟩ := exists_walk_data_of_notMem ((p.tail.dropLast).copy hy' hz')
    (by rwa [Walk.support_copy])
  refine ⟨y, z, q, (Walk.isPath_def q).mpr ?_, ?_⟩
  · exact List.Nodup.of_map Sum.inl (by rw [hs, Walk.support_copy]; exact hnodup)
  · ext a b
    have hq : s(a, b) ∈ q.edges ↔ s(Sum.inl a, Sum.inl b) ∈ (p.tail.dropLast).edges := by
      rw [show s(Sum.inl a, Sum.inl b) = Sym2.map Sum.inl s(a, b) from rfl,
        ← Walk.edges_copy (p.tail.dropLast) hy' hz', ← he]
      exact (List.mem_map_of_injective (Sym2.map.injective Sum.inl_injective)).symm
    rw [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges, hq,
      ← mem_edges_middle_iff p hpn htn, leftPart_adj, adj_iff_mem_edges hH]

/-- **AND FROM ANY CYCLE CUTTING OUT `H` WITH THE ADDED VERTEX ON IT.** -/
theorem isPathGraph_leftPart_of_isCycleGraph {a : V ⊕ Unit} (p : H.Walk a a) (hp : p.IsCycle)
    (hH : p.toSubgraph.spanningCoe = H) (hmem : Sum.inr () ∈ p.support) :
    IsPathGraph (leftPart H) := by
  classical
  refine isPathGraph_leftPart_of_cycle (p.rotate _ hmem) (hp.rotate hmem) ?_
  ext u v
  rw [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges,
    (p.rotate_edges _ hmem).mem_iff, ← adj_iff_mem_edges hH]

end LeftPartPathGraph
