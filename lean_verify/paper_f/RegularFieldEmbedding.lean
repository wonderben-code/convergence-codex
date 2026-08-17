import RegularSelfEmbedding
import TorusFieldEmbedding

/-!
# The measure-level statement, with the torus taken out of it too

`TorusFieldEmbedding` proves that an injective, edge-preserving self-map of the **torus** leaves
the Gaussian field invariant. `RegularSelfEmbedding` then showed the automorphism half of that
argument is about a **finite regular graph** and not about a torus. **The measure half was left
behind**, still stated at `torusGraph`, and it inherits the generalisation for free: the only
thing it does with the graph is hand an automorphism to
`FieldAutInvariance.gaussianField_map_perm`, which was general in the graph all along.

This is `PROOF_STRATEGY` §6 Q3 — *if the unit just finished was a B, retry B→C before touching the
queue* — and the B was `RegularSelfEmbedding`.

## What is proved

* **`isGraphAut_of_isSelfEmbedding`** — an injective edge-preserving self-map of a finite
  **regular** graph is a graph automorphism in `FieldAutInvariance`'s sense.
* **`gaussianField_map_of_isSelfEmbedding`** — hence **the Gaussian field of ANY finite regular
  graph is invariant under every such map**, as an equality of measures.
* **`bipGraph_gaussianField_map`** — the `ERRATUM 48` witness, at the measure level:
  `IndefiniteCoupling.bipGraph` is `2`-regular and is **a torus at no dimension and no side
  length**, so this is a statement `TorusFieldEmbedding` cannot make.

## What is genuinely gained, stated the way `TorusFieldEmbedding` had to state it

That file had to concede that its criterion reached **no invariance the estate could not already
state**, because on the torus the embeddings and the automorphisms coincide — the gain was a
cheaper entry condition and nothing more. **Here the gain is a larger class of GRAPHS**, and
`bipGraph` is the witness rather than the illustration. The two files therefore make different
kinds of claim, and this one is the stronger.

## What this is NOT

**Regularity is not removable**, for `RegularSelfEmbedding`'s reason: on a graph with two degrees
the local-bijection step fails at its first line, so the map need not be an automorphism and there
is nothing to hand to `gaussianField_map_perm`.

**It is not OS3.** `FieldAutInvariance`'s capitals apply here unchanged and for the third time in
this chain: a finite graph has an automorphism group, not the Euclidean group, and widening the
class of *graphs* does not change that.

**`OS4` does not move**, no spectral gap is claimed, and **no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RegularFieldEmbedding

open SimpleGraph GraphLaplacian FieldAutInvariance RegularSelfEmbedding

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ} {m : ℝ}

/-! ## 1. A self-embedding of a regular graph is an automorphism, in the measure file's sense -/

omit [DecidableEq V] in
/-- **THE BRIDGE, WITH NO TORUS IN IT.** `RegularSelfEmbedding.isoOfSelfEmbedding` produces a
`SimpleGraph.Iso`; `FieldAutInvariance.IsGraphAut` is exactly its `map_rel_iff`. -/
theorem isGraphAut_of_isSelfEmbedding (hreg : G.IsRegularOfDegree k) {φ : V → V}
    (h : IsSelfEmbedding G φ) :
    IsGraphAut G (isoOfSelfEmbedding hreg h).toEquiv :=
  fun _ _ => (isoOfSelfEmbedding hreg h).map_rel_iff

omit [DecidableEq V] in
/-- **AND THE UNDERLYING MAP IS THE ONE SUPPLIED**, so the automorphism is not some other map that
happens to exist. -/
theorem coe_isoOfSelfEmbedding (hreg : G.IsRegularOfDegree k) {φ : V → V}
    (h : IsSelfEmbedding G φ) : ⇑(isoOfSelfEmbedding hreg h).toEquiv = φ := rfl

/-! ## 2. Hence the measure is invariant, on every finite regular graph -/

/-- **THE GAUSSIAN FIELD OF ANY FINITE REGULAR GRAPH IS INVARIANT UNDER EVERY INJECTIVE
EDGE-PRESERVING SELF-MAP**, as an equality of measures.

`TorusFieldEmbedding.gaussianField_map_of_isTorusEmbedding` is this at `G = torusGraph d a`. -/
theorem gaussianField_map_of_isSelfEmbedding (hreg : G.IsRegularOfDegree k) {φ : V → V}
    (h : IsSelfEmbedding G φ) (hm : m ≠ 0) :
    (gaussianField G m).map (permField (isoOfSelfEmbedding hreg h).toEquiv)
      = gaussianField G m :=
  gaussianField_map_perm (isGraphAut_of_isSelfEmbedding hreg h) hm

/-! ## 3. `ERRATUM 48`, at the measure level: a graph that is no torus -/

/-- **THE WITNESS.** `IndefiniteCoupling.bipGraph` is the estate's own `2`-regular four-vertex
graph (`GreenExpansion.bipGraph_two_regular`), and it is a torus at no dimension and no side
length. Its Gaussian field is invariant under every injective edge-preserving self-map.

**`TorusFieldEmbedding` cannot state this**, which is the difference between that file's claim and
this one: there the gain was a cheaper entry condition on the same class, here it is a larger class
of graphs. -/
theorem bipGraph_gaussianField_map {φ : Fin 4 → Fin 4}
    (h : IsSelfEmbedding IndefiniteCoupling.bipGraph φ) (hm : m ≠ 0) :
    (gaussianField IndefiniteCoupling.bipGraph m).map
        (permField (isoOfSelfEmbedding GreenExpansion.bipGraph_two_regular h).toEquiv)
      = gaussianField IndefiniteCoupling.bipGraph m :=
  gaussianField_map_of_isSelfEmbedding GreenExpansion.bipGraph_two_regular h hm

/-! ## 4. The torus is one instance, checked by the kernel -/

/-- **AND THE TORUS STATEMENT IS THIS ONE AT `G = torusGraph d a`.** Checked rather than asserted,
with the regularity supplied by `RegularSelfEmbedding.torusGraph_isRegularOfDegree`. -/
example {d a : ℕ} (ha : 3 ≤ a) {φ : BoxGraph.Site d a → BoxGraph.Site d a}
    (h : TorusEmbeddingAllDims.IsTorusEmbedding φ) (hm : m ≠ 0) :
    (gaussianField (TorusReflection.torusGraph d a) m).map
        (permField (isoOfSelfEmbedding (torusGraph_isRegularOfDegree ha) h).toEquiv)
      = gaussianField (TorusReflection.torusGraph d a) m :=
  gaussianField_map_of_isSelfEmbedding (torusGraph_isRegularOfDegree ha) h hm

end RegularFieldEmbedding
