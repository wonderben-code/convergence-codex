import LeftPartPathGraph

/-!
# Every finite graph's edges are an edge-disjoint union of paths and cycles

`LeftPartPathGraph` closed the hard half of what `WALLS.md` §W3 and `UNLOCK_WATCHLIST` call
residue (a), and fenced the rest in one sentence: *no theorem says each part is a path graph or a
cycle graph, because the case where the added vertex is **off** the cycle needs a cycle in
`V ⊕ Unit` carried back along `Sum.inl`, a different lemma, and not proved.*

**That lemma is here, and with it the statement.**

## What is proved

**`isCycleGraph_leftPart_of_notMem`** — a cycle that **misses** the added vertex comes down a
cycle. The transport of `LeftPartWalk` already carries the support **and** the edges, and
`IsCycle` is exactly three conditions on those two lists — edges nodup, walk not nil, support tail
nodup — so each transfers by `List.Nodup.of_map` against the injectivity of `Sum.inl`.

**`exists_path_cycle_decomposition`** — **SO EVERY FINITE GRAPH'S EDGES ARE AN EDGE-DISJOINT UNION
OF PATHS AND CYCLES.** Adjoin one vertex joined to the odd-degree vertices
(`OddVertexAugment.augment`); every degree is then even, so the estate's Euler theorem decomposes
the result into cycles; cut each back to `V`; a cycle through the added vertex becomes a **path**
and a cycle missing it stays a **cycle**. The five files before this one are the five steps.

**This is the decomposition `WALLS.md` §W3 and `UNLOCK_WATCHLIST` record as absent from this
estate and from Mathlib — minus their bookkeeping.** What they name is *circuits **plus paths
between the odd vertices***; what is proved here is *paths and cycles*, with **no claim that the
paths' endpoints are the odd vertices** and **no count of them**. The difference is stated again
below, because it is the difference between this theorem and the classical one. Mathlib's
`Trails.lean` proves only the necessary direction and lists the converse in its own module to-
do.

## What is NOT here

**THE PATHS ARE NOT COUNTED AND THEIR ENDPOINTS ARE NOT IDENTIFIED.** The classical statement says
there are exactly *half the number of odd-degree vertices* paths, and that their endpoints are
**exactly** the odd vertices. **Neither is proved.** `CycleRestriction.card_odd_leftPart_le_two`
gives the degree signature of each piece and **nothing here counts pieces or matches endpoints to
odd vertices**. **Not attempted, no cost claimed** (`ERRATUM 246`). So what is proved is the
decomposition's **existence and shape**, not its classical bookkeeping.

**THE DECOMPOSITION IS NOT CANONICAL.** It depends on the list the Euler theorem returns, and
nothing here is a uniqueness statement; `IsPathGraph` and `IsCycleGraph` are both existentials.

**A PIECE MAY BE `⊥`.** Nothing rules out empty pieces in the returned list, and no theorem here
says the list is nonempty or its members are.

**W3 DOES NOT MOVE.** This closes residue (a), and `ERRATUM 97` — recorded in `ExtendedDual`, in
`UNLOCK_WATCHLIST` and repeated in the five headers before this one — is that residue (a) is
**necessary and not sufficient** for `S3b-ii`'s covering, because it does not say which piece the
plaquette at `x` lies on. **Residue (b), the open-path analogue of the ray argument, is untouched
here and everywhere.** **No claim is made that the Peierls chain gains anything**, and the closing
of (a) is not a step toward the wall so much as the removal of one excuse for not looking at (b).

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `isCycleGraph_leftPart_of_notMem` takes
**no finiteness and no decidability**; `exists_path_cycle_decomposition` takes **`Finite` and
nothing else**, the decidability `augment` needs being produced by `classical` inside
`CycleRestriction`'s proof.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LeftPartDecomposition

open CycleRestriction LeftPartWalk CyclePathExtract LeftPartPathGraph SimpleGraph

variable {V : Type*} {H : SimpleGraph (V ⊕ Unit)}

/-! ## 1. A cycle missing the added vertex comes down a cycle -/

/-- **A CYCLE THAT MISSES THE ADDED VERTEX RESTRICTS TO A CYCLE.** `IsCycle` is three conditions on
the edge list and the support, and the transport carries both. -/
theorem isCycleGraph_leftPart_of_notMem {a : V ⊕ Unit} (p : H.Walk a a) (hp : p.IsCycle)
    (hH : p.toSubgraph.spanningCoe = H) (hmem : Sum.inr () ∉ p.support) :
    IsCycleGraph (leftPart H) := by
  obtain ⟨y, hy⟩ := eq_inl_of_ne (fun hcon => hmem (hcon ▸ p.start_mem_support))
  obtain ⟨q, hs, he⟩ := exists_walk_data_of_notMem ((p.copy hy hy))
    (by rwa [Walk.support_copy])
  have hsc : q.support.map Sum.inl = p.support := by rwa [Walk.support_copy] at hs
  have hec : q.edges.map (Sym2.map Sum.inl) = p.edges := by rwa [Walk.edges_copy] at he
  have htrail : q.IsTrail :=
    ⟨List.Nodup.of_map _ (hec ▸ hp.isTrail.edges_nodup)⟩
  have hnenil : q ≠ Walk.nil := by
    intro hcon
    have hE : p.edges = [] := by rw [← hec, hcon]; rfl
    have hlen : p.length = 0 := by rw [← Walk.length_edges, hE]; rfl
    have h3 := hp.three_le_length
    omega
  have hnodup : q.support.tail.Nodup := by
    refine List.Nodup.of_map (Sum.inl : V → V ⊕ Unit) ?_
    have hcons : p.support = Sum.inl y :: q.support.tail.map Sum.inl := by
      rw [← hsc]
      conv_lhs => rw [Walk.support_eq_cons q]
      rfl
    have h2 := hp.support_nodup
    rw [hcons] at h2
    simpa using h2
  refine ⟨y, q, ⟨⟨htrail, hnenil⟩, hnodup⟩, ?_⟩
  ext u v
  have hq : s(u, v) ∈ q.edges ↔ s(Sum.inl u, Sum.inl v) ∈ p.edges := by
    rw [show s(Sum.inl u, Sum.inl v) = Sym2.map Sum.inl s(u, v) from rfl, ← hec]
    exact (List.mem_map_of_injective (Sym2.map.injective Sum.inl_injective)).symm
  rw [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges, hq, leftPart_adj,
    adj_iff_mem_edges hH]

/-! ## 2. So every finite graph's edges are a union of paths and cycles -/

/-- **EVERY FINITE GRAPH'S EDGES ARE AN EDGE-DISJOINT UNION OF PATHS AND CYCLES.** -/
theorem exists_path_cycle_decomposition {W : Type*} [Finite W] (G : SimpleGraph W) :
    ∃ L : List (SimpleGraph W), (∀ K ∈ L, IsPathGraph K ∨ IsCycleGraph K) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = G := by
  classical
  obtain ⟨L, hcyc, -, hdisj, hjoin⟩ := exists_cycle_parts_decomposition G
  refine ⟨L.map leftPart, ?_, hdisj, hjoin⟩
  intro K hK
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hK
  obtain ⟨a, p, hp, hspan⟩ := hcyc J hJ
  by_cases hmem : Sum.inr () ∈ p.support
  · exact Or.inl (isPathGraph_leftPart_of_isCycleGraph p hp hspan hmem)
  · exact Or.inr (isCycleGraph_leftPart_of_notMem p hp hspan hmem)

end LeftPartDecomposition
