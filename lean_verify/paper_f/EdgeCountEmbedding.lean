import RegularCrossEmbedding
import GreenLargeMass

/-!
# Regularity was the route, not the hypothesis

`RegularSelfEmbedding` and `RegularFieldEmbedding` both say, in terms, that **regularity is not
removable**: on a graph with two different degrees the local-bijection step fails at its first
line, so the map need not be an automorphism. **The first half of that sentence is true and the
second does not follow from it**, and this file is the correction — made by proving more, not by
rewording.

The local argument counts *neighbourhoods*, and to compare `|image of N(v)|` with `|N(φ v)|` it
needs the two to be the same number, which on a self-map is exactly regularity. **The global
argument counts EDGES**, and there is nothing to match up: `Sym2.map φ` is injective on
`G.edgeFinset` and lands in `G'.edgeFinset`, so if those two finsets have the same size the image
is all of it, and every edge of `G'` is the image of an edge of `G`. Degrees never appear.

## What that costs and what it buys

* **Two graphs**: `G.edgeFinset.card = G'.edgeFinset.card` replaces *"both `k`-regular with the
  same `k`"*. It is **strictly weaker** — `two_mul_edgeCard_of_regular` derives it from the two
  regularities and the matching vertex count, by the handshake — and it holds for pairs that are
  not regular at all.
* **One graph**: the hypothesis is **`rfl`**. So an injective edge-preserving self-map of **any**
  finite graph is an automorphism, with **no regularity, no connectivity, and no geometry**.

## What is proved

* **`edgeFinset_image_of_isGraphEmbedding`** — the edge map is onto, from injectivity and the
  matching edge count.
* **`adj_of_adj_map_of_edgeCard`** — hence adjacency is reflected; **`isoOfEdgeCard`** the
  isomorphism, **`gaussianField_map_of_edgeCard`** the equality of Gaussian fields.
* **`adj_of_adj_map_of_isSelfEmbedding`, `isoOfSelfEmbedding'`,
  `gaussianField_map_of_isSelfEmbedding'`** — the same on one graph, **regularity absent**.
* **`two_mul_edgeCard_of_regular`, `edgeCard_eq_of_regular`** — the handshake, and with it
  `RegularCrossEmbedding`'s theorem as an instance of this one (checked by the kernel below).

## `ERRATUM 48`, and the answer is about which GRAPHS, not which members

**It reaches no invariance of a fixed finite graph that the estate could not already state.** Every
automorphism the estate holds carries its `↔` already — `decide` supplies it on the small graphs
and `GraphReflection` proves it on the box — so on any *one* graph this is a cheaper entry
condition and nothing more, exactly as `TorusFieldEmbedding` had to concede.

**What is new is the class of graphs that can be mentioned at all.** Every theorem in
`RegularSelfEmbedding`, `RegularFieldEmbedding` and `RegularCrossEmbedding` carries
`IsRegularOfDegree k`. `GreenLargeMass.stepGraph_not_regular` — **the estate's own theorem, which
this file checks rather than re-proves** — says that hypothesis has no witness at all on
`stepGraph`: not merely stronger than needed, but unsatisfiable, so none of those three files can
be applied to it at any degree. `stepGraph_gaussianField_map` is this file applying to it.

## What this is NOT

**It is not OS3.** `FieldAutInvariance`'s capitals apply for the fifth time in this chain: a finite
graph has an automorphism group, not the Euclidean group, and dropping regularity does not change
that. **`OS4` does not move**, no spectral gap is claimed, and **no published tag moves.**

**It does not subsume `TorusEmbeddingMinimal.side_eq_of_isTorusEmbedding'`**, which *derives* the
equality of vertex counts rather than assuming it — nor does it remove `Fintype.card V =
Fintype.card W`, which is still what makes the map onto.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace EdgeCountEmbedding

open SimpleGraph GraphLaplacian RegularCrossEmbedding

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
variable {k : ℕ} {m : ℝ}

/-! ## 1. The edge map is onto, and degrees never enter -/

omit [DecidableEq V] in
/-- **THE EDGE SET IS EXHAUSTED.** `Sym2.map φ` is injective because `φ` is, and it lands inside
`G'.edgeFinset` because `φ` preserves edges; a subset of the same size is the whole thing.

This is the step regularity was carrying, done globally instead of locally. -/
theorem edgeFinset_image_of_isGraphEmbedding (hE : G.edgeFinset.card = G'.edgeFinset.card)
    {φ : V → W} (h : IsGraphEmbedding G G' φ) :
    G.edgeFinset.image (Sym2.map φ) = G'.edgeFinset := by
  refine Finset.eq_of_subset_of_card_le (fun e he => ?_) ?_
  · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    induction z using Sym2.ind with
    | _ a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hz
      rw [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact h.2 _ _ hz
  · rw [Finset.card_image_of_injective _ (Sym2.map.injective h.1), hE]

omit [DecidableEq V] [DecidableEq W] in
/-- **AND SO ADJACENCY IS REFLECTED, NOT ONLY PRESERVED** — from the edge count alone.

`RegularCrossEmbedding.adj_of_adj_map_of_isGraphEmbedding` is this with the hypothesis supplied by
`edgeCard_eq_of_regular`; the closing `example` checks that rather than asserting it. -/
theorem adj_of_adj_map_of_edgeCard (hE : G.edgeFinset.card = G'.edgeFinset.card) {φ : V → W}
    (h : IsGraphEmbedding G G' φ) {p q : V} (hpq : G'.Adj (φ p) (φ q)) : G.Adj p q := by
  classical
  have hmem : s(φ p, φ q) ∈ G.edgeFinset.image (Sym2.map φ) := by
    rw [edgeFinset_image_of_isGraphEmbedding hE h, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact hpq
  obtain ⟨z, hz, hzz⟩ := Finset.mem_image.mp hmem
  have hz' : z = s(p, q) := Sym2.map.injective h.1 (by rw [hzz, Sym2.map_mk])
  rw [hz', SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hz
  exact hz

/-! ## 2. Hence an isomorphism, and hence the measures agree -/

/-- **TWO GRAPHS WITH THE SAME NUMBER OF VERTICES AND THE SAME NUMBER OF EDGES, WITH AN INJECTIVE
EDGE-PRESERVING MAP BETWEEN THEM, ARE ISOMORPHIC** — and neither one need be regular. -/
noncomputable def isoOfEdgeCard (hcard : Fintype.card V = Fintype.card W)
    (hE : G.edgeFinset.card = G'.edgeFinset.card) {φ : V → W} (h : IsGraphEmbedding G G' φ) :
    G ≃g G' where
  toEquiv := Equiv.ofBijective φ (bijective_of_isGraphEmbedding hcard h)
  map_rel_iff' := ⟨adj_of_adj_map_of_edgeCard hE h, h.2 _ _⟩

/-- **AND THEREFORE THE GAUSSIAN FIELDS AGREE**, as an equality of measures on different spaces,
from a one-directional hypothesis and two counts. -/
theorem gaussianField_map_of_edgeCard (hcard : Fintype.card V = Fintype.card W)
    (hE : G.edgeFinset.card = G'.edgeFinset.card) {φ : V → W} (h : IsGraphEmbedding G G' φ)
    (hm : m ≠ 0) :
    (gaussianField G m).map
        (FieldIsoInvariance.congrField (isoOfEdgeCard hcard hE h).toEquiv)
      = gaussianField G' m :=
  FieldIsoInvariance.gaussianField_map_iso (isoOfEdgeCard hcard hE h) hm

/-! ## 3. One graph: the hypothesis is `rfl`, so regularity disappears entirely -/

/-- **AN INJECTIVE EDGE-PRESERVING SELF-MAP OF ANY FINITE GRAPH REFLECTS ADJACENCY.** No
regularity, no connectivity, no geometry — a graph has as many edges as itself.

**This is the correction.** `RegularSelfEmbedding.adj_of_adj_map_of_regular` takes
`G.IsRegularOfDegree k`, and the file's prose says it is not removable. It is: what needs it is
the neighbourhood count, and the conclusion does not need the neighbourhood count.

**The binders are part of the finding**, as they were for
`RegularSelfEmbedding.bijective_of_isSelfEmbedding`: `[Finite V]` and nothing else — no `Fintype`,
no `DecidableEq`, no `DecidableRel`, no regularity. -/
theorem adj_of_adj_map_of_isSelfEmbedding {V : Type*} [Finite V] {G : SimpleGraph V} {φ : V → V}
    (h : RegularSelfEmbedding.IsSelfEmbedding G φ) {p q : V} (hpq : G.Adj (φ p) (φ q)) :
    G.Adj p q := by
  classical
  have : Fintype V := Fintype.ofFinite V
  exact adj_of_adj_map_of_edgeCard rfl h hpq

/-- **HENCE AN AUTOMORPHISM OF ANY FINITE GRAPH.** `RegularSelfEmbedding.isoOfSelfEmbedding` with
its regularity hypothesis deleted. -/
noncomputable def isoOfSelfEmbedding' {φ : V → V}
    (h : RegularSelfEmbedding.IsSelfEmbedding G φ) : G ≃g G :=
  isoOfEdgeCard rfl rfl h

omit [DecidableEq V] in
/-- **AND THE UNDERLYING MAP IS THE ONE SUPPLIED**, so the automorphism is not some other map that
happens to exist. -/
theorem coe_isoOfSelfEmbedding' {φ : V → V} (h : RegularSelfEmbedding.IsSelfEmbedding G φ) :
    ⇑(isoOfSelfEmbedding' h).toEquiv = φ := rfl

omit [DecidableEq V] in
/-- The bridge to `FieldAutInvariance`, which is `map_rel_iff` under another name. -/
theorem isGraphAut_of_isSelfEmbedding' {φ : V → V}
    (h : RegularSelfEmbedding.IsSelfEmbedding G φ) :
    FieldAutInvariance.IsGraphAut G (isoOfSelfEmbedding' h).toEquiv :=
  fun _ _ => (isoOfSelfEmbedding' h).map_rel_iff

/-- **THE GAUSSIAN FIELD OF ANY FINITE GRAPH IS INVARIANT UNDER EVERY INJECTIVE EDGE-PRESERVING
SELF-MAP**, as an equality of measures.

`RegularFieldEmbedding.gaussianField_map_of_isSelfEmbedding` is this one with a hypothesis that is
not needed. -/
theorem gaussianField_map_of_isSelfEmbedding' {φ : V → V}
    (h : RegularSelfEmbedding.IsSelfEmbedding G φ) (hm : m ≠ 0) :
    (gaussianField G m).map (FieldAutInvariance.permField (isoOfSelfEmbedding' h).toEquiv)
      = gaussianField G m :=
  FieldAutInvariance.gaussianField_map_perm (isGraphAut_of_isSelfEmbedding' h) hm

/-! ## 4. The handshake: the regular case is this one -/

omit [DecidableEq V] in
/-- Twice the edge count is the vertex count times the degree — the degree-sum formula with a
constant summand. -/
theorem two_mul_edgeCard_of_regular (hreg : G.IsRegularOfDegree k) :
    2 * G.edgeFinset.card = Fintype.card V * k := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges, Finset.sum_congr rfl fun v _ => hreg v,
    Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq V] [DecidableEq W] in
/-- **SO `BOTH k-REGULAR` IMPLIES `SAME EDGE COUNT`**, given the matching vertex count. This is
what makes the hypothesis of §1 strictly weaker rather than merely different. -/
theorem edgeCard_eq_of_regular (hcard : Fintype.card V = Fintype.card W)
    (hreg : G.IsRegularOfDegree k) (hreg' : G'.IsRegularOfDegree k) :
    G.edgeFinset.card = G'.edgeFinset.card := by
  have h1 := two_mul_edgeCard_of_regular hreg
  have h2 := two_mul_edgeCard_of_regular hreg'
  rw [hcard] at h1
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) (h1.trans h2.symm)

/-- **`RegularCrossEmbedding`'S THEOREM IS THIS ONE**, with the edge count supplied by the
handshake. Checked by the kernel rather than asserted. -/
example (hcard : Fintype.card V = Fintype.card W) (hreg : G.IsRegularOfDegree k)
    (hreg' : G'.IsRegularOfDegree k) {φ : V → W} (h : IsGraphEmbedding G G' φ) {p q : V}
    (hpq : G'.Adj (φ p) (φ q)) : G.Adj p q :=
  adj_of_adj_map_of_edgeCard (edgeCard_eq_of_regular hcard hreg hreg') h hpq

/-- **AND `RegularSelfEmbedding`'S IS THIS ONE WITH THE REGULARITY UNUSED — the underscore is the
finding.** `_hreg` is bound so the statement is literally that file's, and never mentioned. -/
example (_hreg : G.IsRegularOfDegree k) {φ : V → V}
    (h : RegularSelfEmbedding.IsSelfEmbedding G φ) {p q : V} (hpq : G.Adj (φ p) (φ q)) :
    G.Adj p q :=
  adj_of_adj_map_of_isSelfEmbedding h hpq

/-! ## 5. `ERRATUM 48`: a graph on which the old hypothesis is unsatisfiable -/

/-- **THE OBSTRUCTION IS THE ESTATE'S OWN THEOREM, CHECKED HERE RATHER THAN RE-PROVED.**
`GreenLargeMass.stepGraph_not_regular` reads `¬ ∃ d, stepGraph.IsRegularOfDegree d`, so any attempt
to reach the field statement below through `RegularSelfEmbedding`, `RegularFieldEmbedding` or
`RegularCrossEmbedding` must produce a `k` that does not exist.

**This file first proved that fact and then found it already present** — the duplicate-name grep of
`ERRATUM 176` caught it, which is what that check is for. -/
example (k : ℕ) : ¬ GreenLargeMass.stepGraph.IsRegularOfDegree k :=
  fun h => GreenLargeMass.stepGraph_not_regular ⟨k, h⟩

/-- Adding three exchanges the two paths of `GreenLargeMass.stepGraph`, and **only injectivity and
edge-preservation are checked** — thirty-six cases and thirty-six cases, decided. -/
theorem stepGraph_translate_isSelfEmbedding :
    RegularSelfEmbedding.IsSelfEmbedding GreenLargeMass.stepGraph (fun p => p + 3) := by
  constructor
  · decide
  · decide

/-- **THE GAUSSIAN FIELD OF A NON-REGULAR GRAPH, INVARIANT UNDER A ONE-DIRECTIONAL MAP.** By
`stepGraph_not_regular` this statement cannot be reached through any earlier file in the chain. -/
theorem stepGraph_gaussianField_map (hm : m ≠ 0) :
    (gaussianField GreenLargeMass.stepGraph m).map
        (FieldAutInvariance.permField
          (isoOfSelfEmbedding' stepGraph_translate_isSelfEmbedding).toEquiv)
      = gaussianField GreenLargeMass.stepGraph m :=
  gaussianField_map_of_isSelfEmbedding' stepGraph_translate_isSelfEmbedding hm

end EdgeCountEmbedding
