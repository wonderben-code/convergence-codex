import RegularFieldEmbedding
import FieldIsoInvariance

/-!
# Two graphs, one-way: what replaces connectivity is equal cardinality

`RegularSelfEmbedding` handles a self-map: injective on a finite type is bijective, so regularity
alone upgrades a one-directional homomorphism to an automorphism. `TorusEmbeddingAllDims` handles
**two** tori and needs connectivity, because there the two vertex types may have different sizes
and counting says nothing.

**Neither is the general shape.** What the two-graph argument actually needs is that the two vertex
types have the **same cardinality** — and connectivity was the torus's way of *deriving* that, not
a hypothesis of the argument. State it directly and the geometry disappears:

> **Two `k`-regular graphs on vertex types of equal size, and an injective edge-preserving map
> between them, give an isomorphism.**

## Why this is worth a file rather than a remark

`FieldIsoInvariance.gaussianField_map_congr` — the cross-graph measure transport — asks its caller
for an **`↔`**: adjacency must be preserved *and reflected*. A caller with a one-directional
homomorphism cannot use it at all. **This supplies the `↔` from the `→`**, so the measure
statement becomes reachable from the weaker input, and
`gaussianField_map_of_isGraphEmbedding` is that composition.

That is the same trade `TorusFieldEmbedding` made at the torus and `RegularFieldEmbedding` made on
one graph, now made across two — and here, unlike at the torus, **the class of reachable
conclusions grows**, because the two graphs need not be equal or isomorphic *a priori*.

## What is proved

* **`IsGraphEmbedding`** — injective and edge-preserving, between two graphs.
* **`bijective_of_isGraphEmbedding`** — bijective, from injectivity and equal cardinality alone.
  **No adjacency, no regularity, no connectivity.**
* **`neighborFinset_image_of_isGraphEmbedding`** — the local-bijection step, from the two
  regularities.
* **`adj_of_adj_map_of_isGraphEmbedding`** — hence adjacency is reflected.
* **`isoOfGraphEmbedding`** — hence an isomorphism `G ≃g G'`.
* **`gaussianField_map_of_isGraphEmbedding`** — hence **the Gaussian fields agree**, as an equality
  of measures on different spaces, from a **one-directional** hypothesis.

## What this is NOT

**It does not subsume `TorusEmbeddingMinimal.side_eq_of_isTorusEmbedding'`.** That theorem *derives*
the equality of sizes rather than assuming it, and deriving it is exactly where connectivity and
the counting argument live. **This file assumes what that one proves**, and the two are therefore
complementary: that one says *the sizes must agree*, this one says *once they agree, everything
else follows from regularity*.

**Equal cardinality is not removable, and the reason needs one more word than it was given.** The
sentence said *"an injective map into a strictly larger regular graph of the same degree is still a
local bijection but not onto"*. **A local bijection into a CONNECTED target IS onto** — that is
`TorusEmbeddingAllDims`'s own argument — so the counterexample requires the target **disconnected**:
`C₄ ↪ C₄ ⊔ C₄`, both `2`-regular, injective, edge-preserving, not onto. The hypothesis stands; the
justification silently assumed disconnection.

**~~Regularity is not removable~~, needed at both ends with the same `k`. REFUTED 17 Aug 2026 by
`EdgeCountEmbedding.isoOfEdgeCard`; struck rather than rewritten, per `ERRATUM 94`.** It is replaced
by `G.edgeFinset.card = G'.edgeFinset.card`, which `EdgeCountEmbedding.two_mul_edgeCard_of_regular`
**derives** from the two regularities and the matching vertex count — strictly weaker, so the old
hypothesis was sufficient and never necessary. **Something here is irreducible and this file was
right about that**: `P₃ → K₃` by the identity is injective and edge-preserving and no isomorphism.
**The error was assuming the irreducible count had to be the DEGREE count.** It is the edge count.

**It is not OS3.** `FieldAutInvariance`'s capitals apply here for the fourth time in this chain:
relating two finite graphs is not the Euclidean group. **`OS4` does not move**, no spectral gap is
claimed, and **no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RegularCrossEmbedding

open SimpleGraph GraphLaplacian

/-! ## 1. The definition, and bijectivity from counting alone -/

/-- An injective, edge-preserving map **between two graphs**. -/
def IsGraphEmbedding {V W : Type*} (G : SimpleGraph V) (G' : SimpleGraph W) (φ : V → W) : Prop :=
  Function.Injective φ ∧ ∀ p q, G.Adj p q → G'.Adj (φ p) (φ q)

/-- **BIJECTIVE, FROM INJECTIVITY AND EQUAL CARDINALITY.** No adjacency, no regularity, no
connectivity.

This is what replaces `TorusEmbeddingAllDims`'s connectivity argument. That file could not assume
equal sizes — it was proving them — so it reached surjectivity through an adjacency-closed range
instead. Where the sizes are given, counting is the whole of it. -/
theorem bijective_of_isGraphEmbedding {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {G' : SimpleGraph W} {φ : V → W}
    (hcard : Fintype.card V = Fintype.card W) (h : IsGraphEmbedding G G' φ) :
    Function.Bijective φ :=
  (Fintype.bijective_iff_injective_and_card φ).mpr ⟨h.1, hcard⟩

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
variable {k : ℕ} {m : ℝ}

/-! ## 2. The local-bijection step, from the two regularities -/

omit [DecidableEq V] in
/-- **A LOCAL BIJECTION**, when both graphs are `k`-regular with the *same* `k`. Injectivity puts
`k` distinct images inside a neighbourhood of size `k`, so it exhausts it. -/
theorem neighborFinset_image_of_isGraphEmbedding (hreg : G.IsRegularOfDegree k)
    (hreg' : G'.IsRegularOfDegree k) {φ : V → W} (h : IsGraphEmbedding G G' φ) (v : V) :
    (G.neighborFinset v).image φ = G'.neighborFinset (φ v) := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact h.2 _ _ hx
  · rw [Finset.card_image_of_injective _ h.1, SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree, hreg v, hreg' (φ v)]

omit [DecidableEq V] [DecidableEq W] in
/-- **AND SO ADJACENCY IS REFLECTED**, not only preserved.

Both `DecidableEq`s are off the statement and supplied by `classical` inside, per the estate's
linter discriminator: `[DecidableEq V]` is unused by statement **and** proof (both linters fired),
while `[DecidableEq W]` is unused by the *statement* only — the proof's `Finset.image` needs it,
and `classical` supplies it. -/
theorem adj_of_adj_map_of_isGraphEmbedding (hreg : G.IsRegularOfDegree k)
    (hreg' : G'.IsRegularOfDegree k) {φ : V → W} (h : IsGraphEmbedding G G' φ) {p q : V}
    (hpq : G'.Adj (φ p) (φ q)) : G.Adj p q := by
  classical
  have hmem : φ q ∈ (G.neighborFinset p).image φ := by
    rw [neighborFinset_image_of_isGraphEmbedding hreg hreg' h p, SimpleGraph.mem_neighborFinset]
    exact hpq
  obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp hmem
  rw [SimpleGraph.mem_neighborFinset] at hw
  rwa [h.1 hwq] at hw

/-! ## 3. Hence an isomorphism, and hence the measures agree -/

/-- **TWO `k`-REGULAR GRAPHS OF EQUAL SIZE WITH AN INJECTIVE EDGE-PRESERVING MAP BETWEEN THEM ARE
ISOMORPHIC**, and the map is the isomorphism. -/
noncomputable def isoOfGraphEmbedding (hcard : Fintype.card V = Fintype.card W)
    (hreg : G.IsRegularOfDegree k) (hreg' : G'.IsRegularOfDegree k) {φ : V → W}
    (h : IsGraphEmbedding G G' φ) : G ≃g G' where
  toEquiv := Equiv.ofBijective φ (bijective_of_isGraphEmbedding hcard h)
  map_rel_iff' := ⟨adj_of_adj_map_of_isGraphEmbedding hreg hreg' h, h.2 _ _⟩

/-- **AND THEREFORE THE GAUSSIAN FIELDS AGREE**, as an equality of measures on different spaces —
**from a one-directional hypothesis.**

`FieldIsoInvariance.gaussianField_map_congr` asks its caller for an `↔`; a caller holding only a
homomorphism cannot use it. This supplies the `↔` from the `→`, given the two regularities and the
matching cardinality. -/
theorem gaussianField_map_of_isGraphEmbedding (hcard : Fintype.card V = Fintype.card W)
    (hreg : G.IsRegularOfDegree k) (hreg' : G'.IsRegularOfDegree k) {φ : V → W}
    (h : IsGraphEmbedding G G' φ) (hm : m ≠ 0) :
    (gaussianField G m).map
        (FieldIsoInvariance.congrField (isoOfGraphEmbedding hcard hreg hreg' h).toEquiv)
      = gaussianField G' m :=
  FieldIsoInvariance.gaussianField_map_iso (isoOfGraphEmbedding hcard hreg hreg' h) hm

/-! ## 4. The one-graph case is this one, checked by the kernel -/

/-- **`RegularSelfEmbedding`'S BIJECTIVITY IS THIS FILE'S AT `G' = G`**, with the cardinality
hypothesis discharged by `rfl`. Checked rather than asserted. -/
example {φ : V → V} (h : RegularSelfEmbedding.IsSelfEmbedding G φ) : Function.Bijective φ :=
  bijective_of_isGraphEmbedding (G := G) (G' := G) rfl h

end RegularCrossEmbedding
