import TorusBipartite
import TorusEmbeddingAllDims
import AdjSqForcesRegular

/-!
# The torus was never the point — finite and regular is the whole hypothesis

`TorusEmbeddingAllDims` proves that an injective, edge-preserving self-map of the torus at side
`≥ 3` is an automorphism. **Every line of that argument is about a finite regular graph and none
of it is about a torus.** The torus enters only to supply two facts —
`torusGraph_degree_eq` (regularity) and `torusGraph_connected` — and one of those two turns out
not to be needed.

## The fence, and the second one behind it

* **The graph.** The local-bijection step needs an *exact* degree at both ends. On a self-map both
  ends are the same graph, so **regularity is the entire hypothesis** and `torusGraph` is one
  instance of it.
* **Connectivity, and this is the part I did not expect.** `TorusEmbeddingAllDims` proves
  surjectivity by showing the range is closed under adjacency and invoking connectivity. **For a
  self-map that is unnecessary**: source and target are the *same finite type*, so injective
  implies surjective outright (`Finite.injective_iff_surjective`). The connectivity argument was
  needed there because that file compares tori of **two different side lengths**, hence two
  different types, where counting alone gives nothing.

So the general statement is **strictly cheaper** than its torus instance: one hypothesis instead
of two, and neither of them geometric.

## What is proved

* **`IsSelfEmbedding`** — injective and edge-preserving, on one graph.
* **`neighborFinset_image_of_regular`** — the local-bijection step, from regularity alone.
* **`adj_of_adj_map_of_regular`** — hence an embedding **reflects** adjacency, not only preserves
  it. The leaf is primed away from `TorusEmbeddingAllDims.adj_of_adj_map`: `ERRATUM 193` recorded
  what leaf collisions cost this estate, and the `28 duplicated declaration names` decision item
  is live.
* **`bijective_of_isSelfEmbedding`** — and is bijective, by finiteness. **No connectivity, no
  regularity, no adjacency, and not even the graph's decidability**: this one is pure counting on
  a finite type, and it takes `[Finite V]` and nothing else. At the torus it therefore holds at
  **every** side length — a third fence in this chain that belonged to the route rather than to
  the fact.
* **`isoOfSelfEmbedding`** — so it is an isomorphism of graphs, bundled.

## `ERRATUM 48`: a member the torus file could not produce

`bipGraph_selfEmbedding_iso` runs the criterion on `IndefiniteCoupling.bipGraph`, the estate's own
`2`-regular four-vertex example (`GreenExpansion.bipGraph_two_regular`). **That is not a torus at
any dimension or side length**, so it is outside everything `TorusEmbeddingAllDims` can state.
The criterion is therefore a genuine widening and not a rephrasing.

## What this is NOT

**Regularity is not removable.** On a graph with two different degrees an injective homomorphism
can carry a low-degree vertex's neighbourhood *into* a high-degree one without exhausting it, and
the local-bijection step fails at its first line — which is where `AdjSqForcesRegular`'s reading
applies in reverse: here the hypothesis is doing work, and saying so is worth as much as removing
one that is not.

**This is a self-map statement.** The two-side theorem —
`TorusEmbeddingMinimal.side_eq_of_isTorusEmbedding'`, that an embedding between tori of different
sides cannot exist — is **not** a corollary, because it compares different types and genuinely
needs connectivity and a cardinality argument. Nothing here supersedes it.

**`OS4` does not move**, nothing touches `gaussianField`, no reflection positivity is used or
affected, and **no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RegularSelfEmbedding

open SimpleGraph

/-! ## 1. The definition -/

/-- An injective, edge-preserving self-map of a graph. `TorusEmbeddingAllDims.IsTorusEmbedding`
is this at `torusGraph d a`, source and target equal. -/
def IsSelfEmbedding {V : Type*} (G : SimpleGraph V) (φ : V → V) : Prop :=
  Function.Injective φ ∧ ∀ p q, G.Adj p q → G.Adj (φ p) (φ q)

/-! ## 2. Bijectivity, which needs neither the graph nor connectivity -/

/-- **AN INJECTIVE SELF-MAP OF A FINITE TYPE IS BIJECTIVE.** No adjacency, no regularity, no
connectivity — the hypothesis used is `h.1`.

`TorusEmbeddingAllDims` reached surjectivity through an adjacency-closed range and
`torusGraph_connected`. **It had to**: there the source and target are tori of possibly different
side lengths, hence different types, and counting gives nothing. Here they are the same type.

**The binders are the finding rather than a tidy-up.** This theorem is stated outside the section
below, and it takes `[Finite V]` and nothing else — no `Fintype`, no `DecidableEq`, no
`DecidableRel`, no regularity, no graph structure beyond the one `IsSelfEmbedding` mentions. -/
theorem bijective_of_isSelfEmbedding {V : Type*} [Finite V] {G : SimpleGraph V} {φ : V → V}
    (h : IsSelfEmbedding G φ) : Function.Bijective φ :=
  ⟨h.1, Finite.injective_iff_surjective.mp h.1⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

/-! ## 3. The local-bijection step, from regularity alone -/

/-- **AN EMBEDDING OF A REGULAR GRAPH IS A LOCAL BIJECTION.** Injectivity puts `k` distinct
images inside a neighbourhood that has exactly `k` elements, so it exhausts it.

**An upper bound on the degree would not do**: it must be the same *exact* number at both ends,
which on a self-map is what regularity says. -/
theorem neighborFinset_image_of_regular (hreg : G.IsRegularOfDegree k)
    {φ : V → V} (h : IsSelfEmbedding G φ) (v : V) :
    (G.neighborFinset v).image φ = G.neighborFinset (φ v) := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact h.2 _ _ hx
  · rw [Finset.card_image_of_injective _ h.1, SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree, hreg v, hreg (φ v)]

omit [DecidableEq V] in
/-- **AND SO IT REFLECTS ADJACENCY, NOT ONLY PRESERVES IT.** This does not follow from
bijectivity: a bijective graph homomorphism can carry non-adjacent vertices to adjacent ones.

**`[DecidableEq V]` is off the statement and supplied by `classical` inside**, which is the
linter's own suggestion and the right reading of the estate's discriminator: the statement-level
linter fired and the proof-level one did not, so the hypothesis is absent from the *type* and
needed by the *proof* — `Finset.image` uses it. Dropping it outright, which is what I tried
first, does not compile. -/
theorem adj_of_adj_map_of_regular (hreg : G.IsRegularOfDegree k) {φ : V → V}
    (h : IsSelfEmbedding G φ) {p q : V} (hpq : G.Adj (φ p) (φ q)) : G.Adj p q := by
  classical
  have hmem : φ q ∈ (G.neighborFinset p).image φ := by
    rw [neighborFinset_image_of_regular hreg h p, SimpleGraph.mem_neighborFinset]
    exact hpq
  obtain ⟨w, hw, hwq⟩ := Finset.mem_image.mp hmem
  rw [SimpleGraph.mem_neighborFinset] at hw
  rwa [h.1 hwq] at hw

/-! ## 4. Hence an automorphism -/

/-- **EVERY INJECTIVE EDGE-PRESERVING SELF-MAP OF A FINITE REGULAR GRAPH IS AN AUTOMORPHISM.**

One hypothesis, and it is not geometric. -/
noncomputable def isoOfSelfEmbedding (hreg : G.IsRegularOfDegree k) {φ : V → V}
    (h : IsSelfEmbedding G φ) : G ≃g G where
  toEquiv := Equiv.ofBijective φ (bijective_of_isSelfEmbedding h)
  map_rel_iff' := ⟨adj_of_adj_map_of_regular hreg h, h.2 _ _⟩

/-! ## 5. The torus is one instance, and `bipGraph` is another the torus file cannot reach -/

/-- The torus is regular at side `≥ 3`, in every dimension —
`TorusEmbeddingAllDims.torusGraph_degree_eq` read as `IsRegularOfDegree`. -/
theorem torusGraph_isRegularOfDegree {d n : ℕ} (hn : 3 ≤ n) :
    (TorusReflection.torusGraph d n).IsRegularOfDegree (2 * d) :=
  fun p => TorusEmbeddingAllDims.torusGraph_degree_eq hn p

/-- **AND `TorusEmbeddingAllDims`'S BIJECTIVITY IS THIS FILE'S, AT THE TORUS** — checked by the
kernel rather than asserted.

**Note what is absent: `3 ≤ a`.** `TorusEmbeddingAllDims` reaches bijectivity through regularity
and connectivity, both of which need it. Reached this way a self-embedding of the torus is
bijective at **every** side length, including the degenerate `2` and the empty `0` — because
injectivity of a self-map of a finite type is all it ever was. **A third fence in this chain that
belonged to the route.** -/
example {d a : ℕ} {φ : BoxGraph.Site d a → BoxGraph.Site d a}
    (h : TorusEmbeddingAllDims.IsTorusEmbedding φ) : Function.Bijective φ :=
  bijective_of_isSelfEmbedding (G := TorusReflection.torusGraph d a) h

/-- **`ERRATUM 48`: A MEMBER THE TORUS FILE CANNOT PRODUCE.** `IndefiniteCoupling.bipGraph` is
the estate's own `2`-regular four-vertex graph (`GreenExpansion.bipGraph_two_regular`) and is a
torus at no dimension and no side length. Every injective edge-preserving self-map of it is an
automorphism. -/
noncomputable def bipGraph_selfEmbedding_iso {φ : Fin 4 → Fin 4}
    (h : IsSelfEmbedding IndefiniteCoupling.bipGraph φ) :
    IndefiniteCoupling.bipGraph ≃g IndefiniteCoupling.bipGraph :=
  isoOfSelfEmbedding GreenExpansion.bipGraph_two_regular h

end RegularSelfEmbedding
