import TorusEmbeddingMinimal
import FieldAutInvariance

/-!
# From a map of the graph to an invariance of the measure — and a sentence of mine was too strong

`RE-SWEEP #21`, written three commits ago at the end of the torus chain, said:

> This chain proved facts about a **graph**. The open frontier is about **measures on it**. … A
> graph-theoretic fact about the index set does not touch any of them.

**The first two sentences are right and the third is too strong.** `FieldAutInvariance` is a bridge
built for exactly this traffic: `gaussianField_map_perm` turns a graph *automorphism* into an
equality of *measures*, and its own header calls that "the form the remaining axioms would need".
`TorusEmbeddingAllDims.autOfIsTorusEmbedding` — proved the same day, one commit before the sweep —
manufactures graph automorphisms of the torus. **The two compose, and the sweep did not check
whether they did.** This file is the composition, and the sweep is corrected by proving it rather
than by rewording the sentence.

## What is proved

* **`isGraphAut_of_isTorusEmbedding`** — an injective, edge-preserving self-map of the torus at
  side `≥ 3` **is** a graph automorphism in `FieldAutInvariance`'s sense.
* **`gaussianField_map_of_isTorusEmbedding`** — hence **the Gaussian field on the torus is
  invariant under every such map**, as an equality of measures.
* **`isTorusEmbedding_of_isGraphAut`** — and conversely, every graph automorphism is such a map,
  trivially.

## `ERRATUM 48`, confronted rather than dodged

The rule is that a criterion producing no member it could not produce before is a criterion whose
usefulness is *asserted*. **So: does this produce a measure-invariance the estate could not already
state? No.** The two directions above say the notions **coincide** at side `≥ 3` — which is
today's `autOfIsTorusEmbedding` read as a fact about the class rather than about a single map. The
group of invariances is exactly the same group.

**What is genuinely weaker is the ENTRY CONDITION, and that is the whole of the claim.**
`IsGraphAut G θ` is an `↔` supplied for a **bijection** `θ : V ≃ V`. `IsTorusEmbedding φ` is a
one-directional `→` supplied for a bare **injection**. To use `gaussianField_map_perm` directly a
caller must produce the inverse map and prove that non-adjacent sites stay non-adjacent; to use the
theorem here a caller produces neither. **Two things fewer to check, the same conclusion, and the
reason the reduction is legitimate is a theorem** — `side_eq_of_isTorusEmbedding` and
`adj_of_adj_map` — rather than an appeal to the reader.

**Stated plainly so it cannot be over-read: this is a cheaper route to the same invariances, not
more of them.**

## What this is NOT

**It is not OS3, and `FieldAutInvariance`'s capitals apply here unchanged.** OS3 is invariance
under the Euclidean group; a finite graph has an automorphism group instead, and enlarging the ways
one may *present* an element of that group does not enlarge the group. **`OS4` does not move**: no
sequence of measures, no limit, no compactness.

**`3 ≤ a` is doing real work and `TorusEmbeddingMinimal.side_two_embeds` is why.** At side `2` an
injective edge-preserving map into a *different* torus exists, so nothing forces such a map to be
bijective and the passage to an automorphism fails at its first step.

**No published tag moves, and no spectral gap is claimed.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusFieldEmbedding

open TorusReflection TorusEmbeddingAllDims BoxGraph FieldAutInvariance

variable {d a : ℕ} {m : ℝ}

/-! ## 1. An embedding of the torus into itself is a graph automorphism -/

/-- **AN INJECTIVE, EDGE-PRESERVING SELF-MAP OF THE TORUS IS A GRAPH AUTOMORPHISM**, at side
`≥ 3` and in every dimension.

Neither surjectivity nor the reverse adjacency implication is assumed;
`TorusEmbeddingAllDims.surjective_of_isTorusEmbedding` and `adj_of_adj_map` supply them. -/
theorem isGraphAut_of_isTorusEmbedding (ha : 3 ≤ a) {φ : Site d a → Site d a}
    (h : IsTorusEmbedding φ) :
    IsGraphAut (torusGraph d a) (autOfIsTorusEmbedding ha h).toEquiv :=
  fun _ _ => (autOfIsTorusEmbedding ha h).map_rel_iff

/-- **AND THE UNDERLYING MAP IS THE ONE WE STARTED WITH**, so the automorphism is not some other
map that happens to exist. -/
theorem coe_autOfIsTorusEmbedding (ha : 3 ≤ a) {φ : Site d a → Site d a}
    (h : IsTorusEmbedding φ) :
    ⇑(autOfIsTorusEmbedding ha h).toEquiv = φ := rfl

/-! ## 2. Hence an invariance of the measure -/

/-- **THE GAUSSIAN FIELD ON THE TORUS IS INVARIANT UNDER EVERY INJECTIVE EDGE-PRESERVING
SELF-MAP**, as an equality of measures.

`FieldAutInvariance.gaussianField_map_perm` asks for a bijection satisfying an `↔`. This asks for
an injection satisfying a `→`. The conclusion is the same and the class of invariances is the
same — the gain is entirely in what the caller must supply. -/
theorem gaussianField_map_of_isTorusEmbedding (ha : 3 ≤ a) {φ : Site d a → Site d a}
    (h : IsTorusEmbedding φ) (hm : m ≠ 0) :
    (GraphLaplacian.gaussianField (torusGraph d a) m).map
        (permField (autOfIsTorusEmbedding ha h).toEquiv)
      = GraphLaplacian.gaussianField (torusGraph d a) m :=
  gaussianField_map_perm (isGraphAut_of_isTorusEmbedding ha h) hm

/-! ## 3. The converse, so the coincidence is stated in both directions -/

/-- **EVERY GRAPH AUTOMORPHISM IS AN EMBEDDING**, trivially — a bijection is an injection and an
`↔` gives a `→`.

With `isGraphAut_of_isTorusEmbedding` this says the two notions **coincide** at side `≥ 3`. That
is the honest reading of the pair: the criterion in §1 is a cheaper entry condition, **not** a
larger class. -/
theorem isTorusEmbedding_of_isGraphAut (θ : Site d a ≃ Site d a)
    (hθ : IsGraphAut (torusGraph d a) θ) : IsTorusEmbedding (⇑θ) :=
  ⟨θ.injective, fun _ _ hpq => (hθ _ _).mpr hpq⟩

end TorusFieldEmbedding
