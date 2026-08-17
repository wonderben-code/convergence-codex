import TorusBipGraphSame
import TorusEmbeddingAllDims

/-!
# Connectivity of the target replaces the equal-cardinality hypothesis

`RegularCrossEmbedding` assumes `Fintype.card V = Fintype.card W` and says, correctly, that it
cannot simply be deleted: `C₄ ↪ C₄ ⊔ C₄` is injective, edge-preserving, `2`-regular at both ends,
and not onto. **But the counterexample needs the target DISCONNECTED**, and the file's own
justification did not say so — it was repaired in place when this file was written.

**A local bijection into a CONNECTED target is onto.** That argument is not new to this estate:
`TorusEmbeddingAllDims.surjective_of_isTorusEmbedding` is exactly it, written at the torus, and
`RegularCrossEmbedding`'s header says deriving the equality of sizes *"is exactly where connectivity
and the counting argument live"*. **True, and it does not have to live at the torus.** Stated for
graphs the lattice disappears, as it did for the self-map case:

> **Two `k`-regular graphs, the target connected, and an injective edge-preserving map between
> them: the map is onto, so the vertex counts AGREE rather than being assumed to.**

## What is proved

* **`range_adj_closed`** — the range is closed under adjacency, from the local-bijection step.
* **`surjective_of_connected`** — hence onto, by walking; `TorusEmbeddingGeneral.mem_of_walk` was
  already graph-agnostic and is reused unchanged.
* **`card_eq_of_connected`** — hence the counts agree. **This is the hypothesis
  `RegularCrossEmbedding` assumes, now derived.**
* **`isoOfConnected`, `gaussianField_map_of_connected`** — hence the isomorphism and the equality of
  Gaussian fields, with **no cardinality hypothesis anywhere in the statement**.
* **`no_embedding_of_card_ne`** — the contrapositive: **between connected `k`-regular graphs of
  different size there is no injective edge-preserving map at all.**

## `ERRATUM 48`: two of the estate's own objects, and a statement it could not make

`bipGraph_connected` transports connectivity across `TorusBipGraphSame.torusFour_iso_bipGraph`, and
`no_embedding_bipGraph_torus` then says: **there is no injective edge-preserving map from
`IndefiniteCoupling.bipGraph` into `TorusReflection.torusGraph 1 n` for any `n ≥ 3` with `n ≠ 4`.**

Both objects are the estate's, the conclusion is about **all** `n` at once so no `decide` reaches
it, and **`RegularCrossEmbedding` cannot state it**: its theorem needs the two counts to be equal,
which here is exactly what fails. The previous unit supplied the `n = 4` case as an *isomorphism*;
this one supplies every other `n` as an *impossibility*.

## What this is NOT

**`Nonempty V` is a real hypothesis, not a technicality.** The empty graph maps into anything, its
range is vacuously adjacency-closed, and the walk has nowhere to start.

**It does not remove regularity** — the local-bijection step is what makes the range
adjacency-closed, and that step is the one `EdgeCountEmbedding` had to go around rather than
through. **The two files replace different hypotheses and neither subsumes the other**:
`EdgeCountEmbedding` keeps the counts and drops regularity; this one keeps regularity and derives
the counts.

**It is not OS3**, for the sixth time in this chain. **`OS4` does not move**, no spectral gap is
claimed, and **no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ConnectedCrossEmbedding

open SimpleGraph GraphLaplacian RegularCrossEmbedding

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
variable {k : ℕ} {m : ℝ}

/-! ## 1. The range is closed under adjacency -/

omit [DecidableEq V] [DecidableEq W] in
/-- **A NEIGHBOUR OF SOMETHING HIT IS ITSELF HIT.** The local-bijection step says the image of
`v`'s neighbourhood is *all* of `φ v`'s, so a neighbour of `φ v` has a preimage. -/
theorem range_adj_closed (hreg : G.IsRegularOfDegree k) (hreg' : G'.IsRegularOfDegree k)
    {φ : V → W} (h : IsGraphEmbedding G G' φ) :
    ∀ ⦃x y⦄, x ∈ Set.range φ → G'.Adj x y → y ∈ Set.range φ := by
  classical
  rintro _ y ⟨v, rfl⟩ hxy
  have hmem : y ∈ (G.neighborFinset v).image φ := by
    rw [neighborFinset_image_of_isGraphEmbedding hreg hreg' h v, SimpleGraph.mem_neighborFinset]
    exact hxy
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hmem
  exact ⟨w, rfl⟩

/-! ## 2. Hence onto, and hence the counts agree rather than being assumed -/

omit [DecidableEq V] [DecidableEq W] in
/-- **ONTO, FROM CONNECTIVITY OF THE TARGET.** Start at `φ v₀`, walk to any `y`, and stay inside
the range the whole way. `TorusEmbeddingGeneral.mem_of_walk` was written graph-agnostically at the
torus and is reused here unchanged. -/
theorem surjective_of_connected [Nonempty V] (hconn : G'.Connected)
    (hreg : G.IsRegularOfDegree k) (hreg' : G'.IsRegularOfDegree k) {φ : V → W}
    (h : IsGraphEmbedding G G' φ) : Function.Surjective φ := by
  intro y
  obtain ⟨v₀⟩ := ‹Nonempty V›
  obtain ⟨w⟩ := hconn.preconnected (φ v₀) y
  exact TorusEmbeddingGeneral.mem_of_walk (range_adj_closed hreg hreg' h) w ⟨v₀, rfl⟩

omit [DecidableEq V] [DecidableEq W] in
/-- **AND SO THE VERTEX COUNTS AGREE — THIS IS `RegularCrossEmbedding`'S HYPOTHESIS, DERIVED.** -/
theorem card_eq_of_connected [Nonempty V] (hconn : G'.Connected) (hreg : G.IsRegularOfDegree k)
    (hreg' : G'.IsRegularOfDegree k) {φ : V → W} (h : IsGraphEmbedding G G' φ) :
    Fintype.card V = Fintype.card W :=
  Fintype.card_of_bijective ⟨h.1, surjective_of_connected hconn hreg hreg' h⟩

/-! ## 3. Hence the isomorphism and the fields, with no cardinality hypothesis -/

/-- **TWO `k`-REGULAR GRAPHS, THE TARGET CONNECTED, AND A ONE-DIRECTIONAL MAP: ISOMORPHIC.** No
count appears in the statement. -/
noncomputable def isoOfConnected [Nonempty V] (hconn : G'.Connected) (hreg : G.IsRegularOfDegree k)
    (hreg' : G'.IsRegularOfDegree k) {φ : V → W} (h : IsGraphEmbedding G G' φ) : G ≃g G' :=
  isoOfGraphEmbedding (card_eq_of_connected hconn hreg hreg' h) hreg hreg' h

/-- **AND THEREFORE THE GAUSSIAN FIELDS AGREE.** -/
theorem gaussianField_map_of_connected [Nonempty V] (hconn : G'.Connected)
    (hreg : G.IsRegularOfDegree k) (hreg' : G'.IsRegularOfDegree k) {φ : V → W}
    (h : IsGraphEmbedding G G' φ) (hm : m ≠ 0) :
    (gaussianField G m).map
        (FieldIsoInvariance.congrField (isoOfConnected hconn hreg hreg' h).toEquiv)
      = gaussianField G' m :=
  gaussianField_map_of_isGraphEmbedding (card_eq_of_connected hconn hreg hreg' h) hreg hreg' h hm

/-! ## 4. The contrapositive, which is the usable form -/

omit [DecidableEq V] [DecidableEq W] in
/-- **BETWEEN CONNECTED `k`-REGULAR GRAPHS OF DIFFERENT SIZE THERE IS NO INJECTIVE
EDGE-PRESERVING MAP AT ALL.** -/
theorem no_embedding_of_card_ne [Nonempty V] (hconn : G'.Connected) (hreg : G.IsRegularOfDegree k)
    (hreg' : G'.IsRegularOfDegree k) (hne : Fintype.card V ≠ Fintype.card W) (φ : V → W) :
    ¬ IsGraphEmbedding G G' φ :=
  fun h => hne (card_eq_of_connected hconn hreg hreg' h)

/-! ## 5. The torus theorem is this one, checked by the kernel -/

/-- **`TorusEmbeddingAllDims.surjective_of_isTorusEmbedding` IS THIS FILE'S AT THE TORUS**, with
connectivity from `TorusDecay.torusGraph_connected` and the two degrees from
`RegularSelfEmbedding.torusGraph_isRegularOfDegree`. Checked rather than asserted. -/
example {d a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) {φ : BoxGraph.Site d a → BoxGraph.Site d b}
    (h : TorusEmbeddingAllDims.IsTorusEmbedding φ) : Function.Surjective φ := by
  have : Nonempty (BoxGraph.Site d a) := ⟨fun _ => ⟨0, by omega⟩⟩
  exact surjective_of_connected (TorusDecay.torusGraph_connected d (by omega))
    (RegularSelfEmbedding.torusGraph_isRegularOfDegree ha)
    (RegularSelfEmbedding.torusGraph_isRegularOfDegree hb) h

/-! ## 6. `ERRATUM 48`: the estate's four-vertex graph against every other side length -/

/-- The four-vertex test graph is connected, transported across the previous unit's isomorphism
rather than re-derived — `SimpleGraph.Iso.connected_iff` at
`TorusBipGraphSame.torusFour_iso_bipGraph`. -/
theorem bipGraph_connected : IndefiniteCoupling.bipGraph.Connected :=
  TorusBipGraphSame.torusFour_iso_bipGraph.connected_iff.mp
    (TorusDecay.torusGraph_connected 1 (by norm_num))

/-- **THERE IS NO INJECTIVE EDGE-PRESERVING MAP FROM `bipGraph` INTO THE ONE-DIMENSIONAL TORUS AT
ANY SIDE LENGTH OTHER THAN FOUR.**

Both objects are the estate's own, the statement quantifies over **all** `n` so no `decide` reaches
it, and **`RegularCrossEmbedding` cannot state it** — its hypothesis is that the two counts agree,
which is precisely what fails here. The previous unit gave `n = 4` as an isomorphism; this gives
every other `n` as an impossibility. -/
theorem no_embedding_bipGraph_torus {n : ℕ} (hn : 3 ≤ n) (hne : n ≠ 4)
    (φ : Fin 4 → BoxGraph.Site 1 n) :
    ¬ IsGraphEmbedding IndefiniteCoupling.bipGraph (TorusReflection.torusGraph 1 n) φ := by
  refine no_embedding_of_card_ne (TorusDecay.torusGraph_connected 1 (by omega))
    GreenExpansion.bipGraph_two_regular
    (by simpa using RegularSelfEmbedding.torusGraph_isRegularOfDegree (d := 1) (n := n) hn) ?_ φ
  simpa [BoxGraph.Site, Fintype.card_fun] using fun hc => hne hc.symm

end ConnectedCrossEmbedding
