import GraphAutDegree
import LatticeOS1

/-!
# A graph whose only symmetry is the identity — so finite-volume OS1 really is vacuous somewhere

`TorusSiteTransitive` observed that `LatticeOS1.EuclideanCovariantFinVol` quantifies over the
automorphism group, so *"on a graph whose only automorphism is the identity, it holds by `rfl`"* —
and fenced that as **an observation about the definition, not a theorem**, because **no asymmetric
graph is constructed anywhere in this estate**. `GraphAutDegree` then costed building one.

**Here it is, and the graph is `asymGraph`**: a triangle `0–1–2`, a path `0–3–4` hanging off it, and
a pendant `1–5`. Its automorphism group is trivial (`asymGraph_asymmetric`), so
`euclideanCovariantFinVol_vacuous` holds **at every mass, with no hypothesis on `m` at all** — where
`LatticeOS1.gaussianField_euclideanCovariantFinVol` needs `m ≠ 0` and a change of variables. **That
contrast is the point**: on this graph the axiom is true because there is nothing for it to say.

## Why it is asymmetric, in words

Degrees are `3, 3, 2, 2, 1, 1` at `0, 1, 2, 3, 4, 5`. **No degree is unique**, so
`GraphAutDegree.IsGraphAut.eq_of_degree_unique` cannot start. What separates the pairs is the
*neighbours' degrees*: `4` and `5` both have degree one, but `4`'s neighbour has degree two and
`5`'s has degree three; `2` and `3` both have degree two, but `2`'s neighbours are the two
degree-three vertices while `3` has one of degree three and one of degree one; and `0` and `1`
differ the same way one level down.

## And the cost estimate written one unit ago was wrong in both directions — `ERRATUM 447`

`GraphAutDegree` costed two routes and predicted the wrong winner. It called the enumeration the
risky one — *"the risk is kernel reduction on `Equiv.Perm`, not the mathematics"* — and the
invariant route *"a short case analysis rather than an enumeration"*.

**The enumeration is the short one.** `decide` settles all `720` permutations in **20 seconds**,
needing exactly two accommodations, both one line: an `inferInstanceAs` for
`Decidable (IsGraphAut asymGraph θ)`, because `IsGraphAut` is a `def` that instance search will not
unfold, and `set_option maxRecDepth`.

**And the invariant route does not start.** It was costed on a degree sequence `(1,2,2,3,3,3)` with
the degree-`1` vertex pinned by uniqueness — but **that sequence has no unique degree either**, and
a first test graph built for this file had degrees `(1,3,2,4,2,2)`, three of them unique, **and was
still not asymmetric**: it admits the transposition `(4 5)`. Degrees alone do not separate the
smallest asymmetric graphs, which is precisely why they are the smallest.

> ⚠ **THAT ROUTE DOES NOT START; AN INVARIANT ROUTE DOES, ONE RUNG UP** (2026-09-04, `ERRATUM
> 448`; the paragraph is kept because the failed step is exactly what pointed at the working one).
> `NeighborDegreeInvariant.asymGraph_asymmetric_invariant` re-proves `asymGraph_asymmetric`
> **without inspecting a single permutation**, from the pair *(degree, the set of the neighbours'
> degrees)* — which separates all six vertices, `36` ordered pairs by `decide`. The rung it needs,
> `IsGraphAut.neighborDegrees_image`, is `GraphAutDegree`'s two lemmas composed. **The ordering
> `ERRATUM 447` corrects still stands**: that route needed a lemma that did not exist and arrived
> second.

## What is NOT here

**No general theory.** One graph, `decide`, and the consequence. Nothing here characterises
asymmetric graphs, counts them, or says anything about larger ones.

**Not a defect in `LatticeOS1`.** Its theorem is true and its proof is a real change of variables;
what this file shows is that the axiom's *content* depends on the graph, which is why
`TorusSiteTransitive` proved site-transitivity for the torus.

**Not a claim that `decide` scales.** Six vertices is `720` permutations; seven is `5040` and eight
is `40320`, and nothing here tests those.

**No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AsymmetricGraph

open SimpleGraph FieldAutInvariance

/-- Adjacency of `asymGraph`: triangle `0–1–2`, path `0–3–4`, pendant `1–5`. -/
def asymAdj : Fin 6 → Fin 6 → Bool
  | 0, 1 | 1, 0 => true
  | 1, 2 | 2, 1 => true
  | 2, 0 | 0, 2 => true
  | 0, 3 | 3, 0 => true
  | 3, 4 | 4, 3 => true
  | 1, 5 | 5, 1 => true
  | _, _ => false

/-- **A graph with no symmetry but the identity.** -/
def asymGraph : SimpleGraph (Fin 6) where
  Adj u v := asymAdj u v = true
  symm := by intro u v h; revert u v; decide
  loopless := ⟨by intro u h; revert u; decide⟩

instance : DecidableRel asymGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (asymAdj u v = true))

/-- `IsGraphAut` is a `def`, so instance search will not unfold it; this is the line that makes the
enumeration below possible at all. -/
instance decidableAut (θ : Equiv.Perm (Fin 6)) : Decidable (IsGraphAut asymGraph θ) :=
  inferInstanceAs (Decidable (∀ p q, asymGraph.Adj (θ p) (θ q) ↔ asymGraph.Adj p q))

/-! ## 1. The degrees, and why they do not settle it -/

/-- The degree sequence is `3, 3, 2, 2, 1, 1`. -/
theorem asymGraph_degrees : ∀ v : Fin 6, asymGraph.degree v = ![3, 3, 2, 2, 1, 1] v := by decide

/-- **NO DEGREE IS UNIQUE**, so `GraphAutDegree.IsGraphAut.eq_of_degree_unique` cannot pin a single
vertex here. This is stated rather than remarked because the previous unit's cost estimate assumed
the opposite. -/
theorem no_unique_degree : ∀ v : Fin 6, ∃ w : Fin 6, w ≠ v ∧
    asymGraph.degree w = asymGraph.degree v := by decide

/-! ## 2. Asymmetry -/

set_option maxRecDepth 100000 in
/-- **THE AUTOMORPHISM GROUP IS TRIVIAL.** All `720` permutations of six points, by `decide`. -/
theorem asymGraph_asymmetric (θ : Equiv.Perm (Fin 6)) (h : IsGraphAut asymGraph θ) :
    θ = Equiv.refl (Fin 6) := by
  revert θ
  decide

/-! ## 3. What it makes vacuous -/

/-- **FINITE-VOLUME OS1 HOLDS HERE FOR NO REASON AT ALL** — at **every** mass, with none of the
hypotheses `LatticeOS1.gaussianField_euclideanCovariantFinVol` needs, because the only automorphism
is the identity and the statement is then `rfl`. `TorusSiteTransitive` fenced this as an observation
about the definition; it is a theorem. -/
theorem euclideanCovariantFinVol_vacuous (m : ℝ) :
    LatticeOS1.EuclideanCovariantFinVol asymGraph m := by
  intro θ hθ k p
  rw [asymGraph_asymmetric θ hθ]
  rfl

end AsymmetricGraph
