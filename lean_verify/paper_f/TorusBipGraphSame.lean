import RegularCrossEmbedding

/-!
# The estate's four-vertex test graph IS its one-dimensional torus at side four

`RegularCrossEmbedding` proves that two `k`-regular graphs of equal size with a one-directional
injective edge-preserving map between them are isomorphic, and that their Gaussian fields agree.
**This is that criterion used**, on two objects the estate has carried side by side since the
lattice was built and never once related.

* `IndefiniteCoupling.bipGraph` is `K₂,₂` on `Fin 4` — adjacency is *"exactly one of the two
  indices is below 2"*. It is the estate's worked example for reflection positivity, and
  `GreenExpansion.bipGraph_two_regular` gives its degree.
* `TorusReflection.torusGraph 1 4` is the periodic lattice at `d = 1`, side `4`, and
  `RegularSelfEmbedding.torusGraph_isRegularOfDegree` gives its degree.

**Both are `2`-regular on four vertices, and a `2`-regular simple graph on four vertices is a
four-cycle.** So they must be isomorphic — but *must be* is an argument in prose, and the estate's
standing habit is to distrust exactly that. Here it is a theorem.

## What the criterion buys, and it is the point of the file

The relabelling `0 ↦ 0, 1 ↦ 2, 2 ↦ 1, 3 ↦ 3` is supplied, and **only that it is injective and
sends edges to edges is checked** — sixteen cases, by `decide`. That it sends *non*-edges to
non-edges, and that it is onto, are **not** checked and are not needed:
`RegularCrossEmbedding.isoOfGraphEmbedding` supplies both from the two degrees and the two
cardinalities. **Without that criterion this file would have to verify the `↔`**, which is the
entry condition `FieldIsoInvariance.gaussianField_map_congr` demands.

## What is proved

* **`cycleRelabel`**, **`isGraphEmbedding_relabel`** — the map, and the one-directional check.
* **`torusFour_iso_bipGraph`** — **`torusGraph 1 4 ≃g bipGraph`.**
* **`gaussianField_torusFour_eq_bipGraph`** — **their Gaussian fields are the same measure**,
  transported along the relabelling, at every nonzero mass.

## What this is NOT

**It does not transport reflection positivity.** `bipGraph`'s reflection-positivity results
(`AdjSqForcesRegular.bipGraph_reflectionPositive_clean` and the rest) are statements about a
*graph together with a reflection `θ` and a half `H`*. An isomorphism of graphs carries the graph;
carrying the reflection and the half across it is a further step, **not taken here and not
claimed**. What transports for free is anything stated about the graph alone — the Green function,
by `green_congr`, and the Gaussian field, by the theorem below.

**It is one side length and one dimension.** Nothing here says `torusGraph d n` is any particular
named graph for other `d` or `n`; at `d = 1` the general identification is
`TorusCycleGraph.torusGraph_one_iso`, into Mathlib's `cycleGraph`, and this is a different target.

**`OS4` does not move**, no spectral gap is claimed, and **no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusBipGraphSame

open SimpleGraph GraphLaplacian TorusReflection BoxGraph RegularCrossEmbedding

/-! ## 1. The relabelling, and the one-directional check -/

/-- The four-cycle `0–1–2–3–0` of the torus, relabelled onto `bipGraph`'s four-cycle
`0–2–1–3–0`. -/
def cycleRelabel (p : Site 1 4) : Fin 4 := ![0, 2, 1, 3] (p 0)

/-- **INJECTIVE AND EDGE-PRESERVING — AND THAT IS ALL THAT IS CHECKED.** Sixteen cases, decided.

The reverse implication and surjectivity are supplied by `RegularCrossEmbedding` from the degrees
and the cardinalities, not verified here. -/
theorem isGraphEmbedding_relabel :
    IsGraphEmbedding (torusGraph 1 4) IndefiniteCoupling.bipGraph cycleRelabel := by
  constructor
  · decide
  · decide

/-! ## 2. The two hypotheses the criterion needs -/

/-- Four sites, four vertices. -/
theorem card_eq : Fintype.card (Site 1 4) = Fintype.card (Fin 4) := by decide

/-- The torus at side `4` is `2`-regular — `RegularSelfEmbedding.torusGraph_isRegularOfDegree` at
`d = 1`, with `2 * 1` reduced. -/
theorem torusFour_two_regular : (torusGraph 1 4).IsRegularOfDegree 2 := by
  simpa using RegularSelfEmbedding.torusGraph_isRegularOfDegree (d := 1) (n := 4) (by omega)

/-! ## 3. Hence the isomorphism, and hence the fields -/

/-- **THE ESTATE'S FOUR-VERTEX TEST GRAPH IS ITS ONE-DIMENSIONAL TORUS AT SIDE FOUR.** -/
noncomputable def torusFour_iso_bipGraph : torusGraph 1 4 ≃g IndefiniteCoupling.bipGraph :=
  isoOfGraphEmbedding card_eq torusFour_two_regular GreenExpansion.bipGraph_two_regular
    isGraphEmbedding_relabel

/-- **AND THEIR GAUSSIAN FIELDS ARE THE SAME MEASURE**, transported along the relabelling, at every
nonzero mass. -/
theorem gaussianField_torusFour_eq_bipGraph {m : ℝ} (hm : m ≠ 0) :
    (gaussianField (torusGraph 1 4) m).map
        (FieldIsoInvariance.congrField torusFour_iso_bipGraph.toEquiv)
      = gaussianField IndefiniteCoupling.bipGraph m :=
  gaussianField_map_of_isGraphEmbedding card_eq torusFour_two_regular
    GreenExpansion.bipGraph_two_regular isGraphEmbedding_relabel hm

end TorusBipGraphSame
