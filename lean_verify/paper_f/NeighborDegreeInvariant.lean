import AsymmetricGraph

/-!
# The invariant route does start — one rung above the one it was costed on

`AsymmetricGraph` proved its graph asymmetric by `decide` over all `720` permutations, and
`ERRATUM 447` recorded that the *invariant* route — pin vertices by a degree nothing else shares —
**does not start** there, because `no_unique_degree` shows every degree is repeated.

**That erratum is about the route as costed, and a reader could take it for more.** It is not true
that no invariant argument works on this graph; it is true that the rung the estate had built is
one short. **This file builds the next rung and runs the route on it**, with no enumeration over
permutations anywhere.

## The rung

**`IsGraphAut.neighborDegrees_image`** — the set of *degrees of the neighbours* of a vertex is an
automorphism invariant, at every graph, finite or not in its symmetry: `θ` carries neighbours to
neighbours (`GraphAutDegree.IsGraphAut.neighborFinset_image`) and preserves each of their degrees
(`GraphAutDegree.IsGraphAut.degree`), so the image set is untouched. Two applications of what the
previous unit built, composed — which is why the previous unit could not see it was needed.

**`IsGraphAut.eq_of_neighborDegrees_unique`** — a vertex alone in its **pair** *(degree, neighbours'
degrees)* is fixed by every automorphism. `GraphAutDegree.IsGraphAut.eq_of_degree_unique` is the
special case where the first coordinate already decides.

## The route

**`asymGraph_neighborDegrees_separate`** — on `AsymmetricGraph.asymGraph` that pair separates all
six vertices, by `decide` over the `36` ordered pairs of vertices. This is the paragraph
`AsymmetricGraph`'s docstring argues in words, checked: `4` and `5` have degree one and neighbours
of degree two and three; `2` and `3` have degree two, with neighbour-degree sets `{3}` and `{3,1}`;
`0` and `1` have degree three, with `{3,2}` and `{3,2,1}`.

**`asymGraph_asymmetric_invariant`** re-proves `AsymmetricGraph.asymGraph_asymmetric` from it in
three lines. **The two proofs are independent**: one enumerates `720` permutations, the other
enumerates `36` vertex pairs and quotes two general lemmas. Keeping both is deliberate — the
enumeration is what establishes that the *statement* is right, and the invariant proof is what
generalises, since neither general lemma mentions `Fin 6`.

## What this does NOT say

**`ERRATUM 447` is not withdrawn and no cost claim is repaired.** The prediction it corrects was
that the invariant route would be *shorter*, and it is not: this file needs a lemma that did not
exist plus its own `decide`, and it arrives second. What is corrected is the reachable impression
that the route is closed. **`ERRATUM 448` records the distinction.**

**Not a canonical-form or graph-isomorphism result.** The pair *(degree, neighbours' degrees)*
separates the vertices of **this** graph. It does not separate the vertices of every graph — a
regular graph defeats it at both coordinates — and nothing here claims a refinement that would.

**Not `Aut` as a group.** The estate's vocabulary is the predicate `FieldAutInvariance.IsGraphAut`,
and this file stays inside it (`UNLOCK_WATCHLIST`: `SimpleGraph.Aut` carries no such lemma at this
pin, and `--cites-lean` is what established that).

**No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace NeighborDegreeInvariant

open Finset SimpleGraph FieldAutInvariance GraphAutDegree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. The rung: neighbours' degrees are an automorphism invariant -/

omit [DecidableEq V] in
/-- **THE SET OF DEGREES OF THE NEIGHBOURS IS AN AUTOMORPHISM INVARIANT.**
`IsGraphAut.neighborFinset_image` moves the neighbours and `IsGraphAut.degree` fixes each of their
degrees; the composite is the statement. -/
theorem IsGraphAut.neighborDegrees_image {θ : V ≃ V} (h : IsGraphAut G θ) (p : V) :
    (G.neighborFinset (θ p)).image (fun u => G.degree u)
      = (G.neighborFinset p).image (fun u => G.degree u) := by
  classical
  rw [GraphAutDegree.IsGraphAut.neighborFinset_image h p, Finset.image_image]
  exact Finset.image_congr fun v _ => GraphAutDegree.IsGraphAut.degree h v

omit [DecidableEq V] in
/-- **A VERTEX ALONE IN ITS DEGREE *AND* ITS NEIGHBOURS' DEGREES IS FIXED BY EVERY AUTOMORPHISM.**
The second rung of an asymmetry argument; `IsGraphAut.eq_of_degree_unique` is the case where the
first coordinate already decides. -/
theorem IsGraphAut.eq_of_neighborDegrees_unique {θ : V ≃ V} (h : IsGraphAut G θ) {v : V}
    (huniq : ∀ w : V, G.degree w = G.degree v →
      (G.neighborFinset w).image (fun u => G.degree u)
        = (G.neighborFinset v).image (fun u => G.degree u) → w = v) :
    θ v = v :=
  huniq (θ v) (GraphAutDegree.IsGraphAut.degree h v) (IsGraphAut.neighborDegrees_image h v)

omit [DecidableEq V] in
/-- **AND SO A GRAPH THE PAIR SEPARATES IS ASYMMETRIC**, with no enumeration of permutations. -/
theorem eq_refl_of_neighborDegrees_separate
    (hsep : ∀ v w : V, G.degree w = G.degree v →
      (G.neighborFinset w).image (fun u => G.degree u)
        = (G.neighborFinset v).image (fun u => G.degree u) → w = v)
    {θ : V ≃ V} (h : IsGraphAut G θ) : θ = Equiv.refl V := by
  ext v
  exact IsGraphAut.eq_of_neighborDegrees_unique h (hsep v)

/-! ## 2. The route, run on the graph that defeated the first rung -/

open AsymmetricGraph

/-- **THE PAIR SEPARATES ALL SIX VERTICES OF `asymGraph`** — `36` ordered pairs by `decide`, where
degree alone separates none of the three same-degree pairs (`AsymmetricGraph.no_unique_degree`). -/
theorem asymGraph_neighborDegrees_separate :
    ∀ v w : Fin 6, asymGraph.degree w = asymGraph.degree v →
      (asymGraph.neighborFinset w).image (fun u => asymGraph.degree u)
        = (asymGraph.neighborFinset v).image (fun u => asymGraph.degree u) → w = v := by decide

/-- **ASYMMETRY AGAIN, BY INVARIANT RATHER THAN BY ENUMERATION.** Independent of
`AsymmetricGraph.asymGraph_asymmetric`: no permutation of `Fin 6` is ever inspected. -/
theorem asymGraph_asymmetric_invariant (θ : Equiv.Perm (Fin 6)) (h : IsGraphAut asymGraph θ) :
    θ = Equiv.refl (Fin 6) :=
  eq_refl_of_neighborDegrees_separate asymGraph_neighborDegrees_separate h

/-- The vacuity of finite-volume OS1 on `asymGraph`, re-derived through the invariant route — the
same theorem as `AsymmetricGraph.euclideanCovariantFinVol_vacuous`, on a disjoint proof. -/
theorem euclideanCovariantFinVol_vacuous' (m : ℝ) :
    LatticeOS1.EuclideanCovariantFinVol asymGraph m := by
  intro θ hθ k p
  rw [asymGraph_asymmetric_invariant θ hθ]
  rfl

end NeighborDegreeInvariant
