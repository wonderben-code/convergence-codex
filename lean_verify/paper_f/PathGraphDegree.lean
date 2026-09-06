import LeftPartDecomposition

/-!
# The degrees of a path graph, which this estate did not have

`EvenRowParity` records, dated, that as of 2026-09-06 this estate has **no degree theorem for
`SimpleGraph.IsPathGraph` at all** — the predicate was defined the same day and appears only as a
conclusion, where the cycle case has `CycleDecomposition.ncard_neighborSet_cycle_of_mem`. **This is
that theorem.** It is the companion of the cycle one and it is what the correction term in the
row-parity telescope would be read off, since a path is even everywhere except at its two ends.

Mathlib supplies the three cases — `IsPath.neighborSet_toSubgraph_startpoint`,
`..._endpoint` and `ncard_neighborSet_toSubgraph_internal_eq_two` — indexed by position along the
walk. What is done here is the translation from *position* to *vertex*, which is where the work is:
a vertex of the path that is neither end is `p.getVert i` for some `0 < i < p.length`, and that
needs `getVert_zero` and `getVert_length` to rule the two ends out.

## What is proved

**`even_ncard_neighborSet_path`** — **a path's subgraph has an even number of neighbours at every
vertex that is not one of its two endpoints**: two on the path, none off it. Stated for the
spanning coercion, which is the form `IsPathGraph` and `EvenDegrees` both use.

**`ncard_neighborSet_path_endpoint`, `ncard_neighborSet_path_endpoint'`** — **and exactly one at
each endpoint**, when the walk is not nil. So the endpoints are precisely where evenness fails.

**`exists_endpoints_of_isPathGraph`** — the same read off the predicate: for any path graph there
are two vertices outside which every degree is even. **True of the nil case too**, where the graph
is `⊥` and every degree is `0`.

**`odd_ncard_neighborSet_path_endpoint`** — and at an endpoint of a non-nil path the count is
**odd**, which is the form a parity argument consumes.

## What is NOT here

**NO ROW-PARITY CORRECTION TERM, AND THAT IS THE POINT OF THE NEXT UNIT AND NOT THIS ONE.**
`EvenRowParity` takes `EvenDegrees H` **globally**, and a path graph does not satisfy it — that is
the whole content above. **Refining that chain to a pointwise hypothesis, and computing what the
telescope picks up at the two rows containing the endpoints, is not done here.** Not attempted, no
cost claimed (`ERRATUM 246`).

**NOTHING SAYS THE TWO ENDPOINTS ARE DISTINCT.** `exists_endpoints_of_isPathGraph` returns two
vertices and **does not claim `u ≠ v`**; on a nil walk they are equal, and no hypothesis here rules
that out. The endpoint counts are stated separately, each under `¬ p.Nil`.

**NO CONVERSE.** Nothing says a graph with exactly two odd-degree vertices is a path graph, and it
is not: a disjoint union of a path and a cycle has exactly two, which
`LeftPartPathGraph` already records against the degree signature.

**NO CONNECTION TO `LeftPartDecomposition`'s LIST.** That theorem returns pieces each of which is a
path graph or a cycle graph; **no theorem here counts odd vertices across the list** or matches them
to the original graph's odd vertices, which is the classical bookkeeping that decomposition also
does not have.

**W3 DOES NOT MOVE.** A degree computation is not a ray, a covering, or a crossing count.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no finiteness and no decidability
anywhere** — everything is stated with `Set.ncard`, which carries neither, exactly as
`CycleDecomposition`'s cycle-side theorems are.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-! ## 1. Away from the two endpoints, a path is even -/

/-- **A PATH'S SUBGRAPH HAS AN EVEN NUMBER OF NEIGHBOURS AT EVERY NON-ENDPOINT**: two on the path,
none off it. -/
theorem even_ncard_neighborSet_path {p : G.Walk u v} (hp : p.IsPath) {w : V}
    (hu : w ≠ u) (hv : w ≠ v) :
    Even ((p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet w).ncard := by
  by_cases hw : w ∈ p.support
  · obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    have hi0 : i ≠ 0 := by
      intro h
      exact hu (by rw [← hi, h, Walk.getVert_zero])
    have hilt : i < p.length := by
      rcases lt_or_eq_of_le hile with h | h
      · exact h
      · exact absurd (by rw [← hi, h, Walk.getVert_length]) hv
    have h2 : ((p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet w).ncard = 2 := by
      rw [show (p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet w
          = p.toSubgraph.neighborSet w from by ext x; simp, ← hi]
      exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt
    rw [h2]
    exact even_two
  · rw [neighborSet_spanningCoe_toSubgraph_eq_empty p hw, Set.ncard_empty]
    exact ⟨0, rfl⟩

/-! ## 2. And exactly one at each endpoint -/

theorem ncard_neighborSet_path_endpoint {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) :
    ((p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet u).ncard = 1 := by
  rw [show (p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet u
      = p.toSubgraph.neighborSet u from by ext x; simp,
    hp.neighborSet_toSubgraph_startpoint hnp, Set.ncard_singleton]

theorem ncard_neighborSet_path_endpoint' {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) :
    ((p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet v).ncard = 1 := by
  rw [show (p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet v
      = p.toSubgraph.neighborSet v from by ext x; simp,
    hp.neighborSet_toSubgraph_endpoint hnp, Set.ncard_singleton]

/-- **SO THE ENDPOINTS ARE PRECISELY WHERE EVENNESS FAILS**, in the form a parity argument
consumes. -/
theorem odd_ncard_neighborSet_path_endpoint {p : G.Walk u v} (hp : p.IsPath) (hnp : ¬ p.Nil) :
    Odd ((p.toSubgraph.spanningCoe : SimpleGraph V).neighborSet u).ncard := by
  rw [ncard_neighborSet_path_endpoint hp hnp]
  exact ⟨0, rfl⟩

/-! ## 3. Read off the predicate -/

/-- **EVERY PATH GRAPH HAS TWO VERTICES OUTSIDE WHICH EVERY DEGREE IS EVEN.** True of the nil case
as well, where the graph is `⊥`; **no claim is made that the two are distinct.** -/
theorem exists_endpoints_of_isPathGraph {H : SimpleGraph V} (hH : IsPathGraph H) :
    ∃ a b : V, ∀ w : V, w ≠ a → w ≠ b → Even ((H.neighborSet w).ncard) := by
  obtain ⟨a, b, p, hp, hspan⟩ := hH
  exact ⟨a, b, fun w hwa hwb => hspan ▸ even_ncard_neighborSet_path hp hwa hwb⟩

end SimpleGraph
