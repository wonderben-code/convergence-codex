import TorusCycleGraph
import TorusDecay
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-!
# What the bridge actually pays, rather than what its header said it would

`TorusCycleGraph` proved `torusGraph 1 (n+1) ≃g SimpleGraph.cycleGraph (n+1)` and then wrote, of
itself, that this **"hands the estate's `d = 1` torus to Mathlib's cycle theory"**, listing girth,
bipartiteness, colourings and the `Free`/`Copy` machinery as now reachable.

**IT REACHED NONE OF THEM.** `ERRATUM 48` is the rule that a criterion producing no member it could
not produce before is a criterion whose usefulness is *asserted*; an isomorphism whose consequences
are listed in prose and drawn nowhere is the same defect wearing different clothes, and it was in a
file committed one step earlier. **This file is the fold-back, and the fold-back is theorems.**

## What is proved, and what each one is worth

* **`chromaticNumber_eq_of_iso`** — the transport itself: isomorphic graphs have equal chromatic
  number. Mathlib has `Iso.degree_eq`, `Iso.minDegree_eq`, `Iso.maxDegree_eq` and
  `Iso.card_edgeFinset_eq`, but **no chromatic-number transport**, so this is the one piece the
  bridge needed and the library did not have. Stated for arbitrary graphs, not for the torus.
* **`torusGraph_one_chromaticNumber_even`** — `(torusGraph 1 n).chromaticNumber = 2` for even
  `n ≥ 2`. **The periodic lattice is bipartite at even side length.** The estate had no colouring
  statement of any kind, about any of its graphs.
* **`torusGraph_one_chromaticNumber_odd`** — and `= 3` for odd `n ≥ 2`, so **the evenness is not
  decoration**: the two parities give genuinely different graphs.
* **`torusGraph_one_bicoloring`**, **`torusGraph_one_bicoloring_apply`**,
  **`torusGraph_one_adj_parity_ne`** — the colouring as *data*, computed: a site's colour is the
  parity of its coordinate, and **no edge joins two sites of the same parity**. That is the
  even/odd sublattice decomposition of the periodic lattice, exhibited rather than described.
* **`torusGraph_one_degree`**, **`torusGraph_degree_le_attained`** — every site of `torusGraph 1 n`
  has degree **exactly** `2` for `n ≥ 3`. `TorusDecay.torusGraph_degree_le` bounds every degree by
  `2 * d`; this says the bound is **attained** at `d = 1`, so no estate estimate that consumes it —
  `GreenDecay.decayRate (2 * d)` and everything downstream — improves by sharpening it here.

## What this is NOT

**The parity coincidence is a coincidence until someone proves otherwise.**
`TorusReflection.reflectionPositive_torus` requires `Even n`, and bipartiteness requires `Even n`.
**Nothing here says the second is why the first holds**, and nothing in the estate connects them.
The two hypotheses agreeing is a fact about two statements, not a mechanism, and it is recorded
here as an observation precisely so that no later reader promotes it to an explanation.

**`girth` is still not reached, and that remains true — but the sentence that stood here about
what it was FOR was wrong, and is corrected the same day.** `girth (cycleGraph n) = n` is still
absent from Mathlib: `cycleGraph.cycle` is an explicit closed walk of length `n+3` with its length
computed, but **a closed walk is not a cycle until proved to be one**, `IsCycle` is not established
for it, and girth is an infimum over cycles. What was wrong is the *role*: this file, following
`TorusCycleGraph`, called that the Mathlib-side half of `TorusEmbedding`'s route to the general
`n ≥ 3` statement. **`TorusEmbeddingGeneral.no_embedding_double` proves that statement without
girth**, from an exact degree count and connectivity. **And the half that looked nearly in reach
was the useless half**: an exhibited cycle bounds girth from **above**, while excluding a short
cycle needs the bound from **below**.

**`d = 1` only**, for the reason `TorusCycleGraph` gave: `torusGraph d n` at `d ≥ 2` is a product
of cycles and `cycleGraph` is one cycle. Every statement here is about the one-dimensional ring.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.** A chromatic
number is not a measure-theoretic statement and nothing here touches `gaussianField`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusCycleTheory

open TorusReflection TorusCycleGraph SimpleGraph

/-! ## 1. The transport Mathlib does not have -/

/-- **ISOMORPHIC GRAPHS HAVE EQUAL CHROMATIC NUMBER.** Mathlib transports degree, minimum degree,
maximum degree and edge count along a `SimpleGraph.Iso`; it does not transport the chromatic
number, and this is the one transport the bridge needs.

The proof is that the two graphs are `Colorable` at exactly the same `n` — a colouring pulls back
along `Colorable.of_hom` in either direction — so the infima defining the two chromatic numbers
range over the same set. -/
theorem chromaticNumber_eq_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.chromaticNumber = H.chromaticNumber := by
  have hset : setOf G.Colorable = setOf H.Colorable := by
    ext n
    exact ⟨fun h => h.of_hom e.symm.toHom, fun h => h.of_hom e.toHom⟩
  rw [chromaticNumber_eq_biInf, chromaticNumber_eq_biInf, hset]

/-! ## 2. The periodic lattice is bipartite exactly when its side length is even -/

/-- **THE `d = 1` PERIODIC LATTICE IS BIPARTITE AT EVEN SIDE LENGTH.** Two colours suffice and one
does not, at every even `n ≥ 2`. The estate had no colouring statement about any of its graphs. -/
theorem torusGraph_one_chromaticNumber_even (n : ℕ) (h2 : 2 ≤ n) (he : Even n) :
    (torusGraph 1 n).chromaticNumber = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [chromaticNumber_eq_of_iso (torusGraph_one_iso k)]
  exact chromaticNumber_cycleGraph_of_even (k + 1) h2 he

/-- **AND IT IS NOT BIPARTITE AT ODD SIDE LENGTH**, needing three colours. So `Even n` in the
statement above is doing work: the two parities give genuinely different graphs. -/
theorem torusGraph_one_chromaticNumber_odd (n : ℕ) (h2 : 2 ≤ n) (ho : Odd n) :
    (torusGraph 1 n).chromaticNumber = 3 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [chromaticNumber_eq_of_iso (torusGraph_one_iso k)]
  exact chromaticNumber_cycleGraph_of_odd (k + 1) h2 ho

/-! ## 3. The colouring as data: the even/odd sublattice split -/

/-- The two-colouring itself, transported along the bridge — **data, not an existence claim**. -/
def torusGraph_one_bicoloring (n : ℕ) (he : Even (n + 1)) :
    (torusGraph 1 (n + 1)).Coloring Bool :=
  (cycleGraph.bicoloring_of_even (n + 1) he).comp (torusGraph_one_iso n).toHom

/-- **AND ITS VALUE IS THE PARITY OF THE SITE'S COORDINATE**, computed rather than asserted. -/
@[simp] theorem torusGraph_one_bicoloring_apply (n : ℕ) (he : Even (n + 1))
    (p : BoxGraph.Site 1 (n + 1)) :
    torusGraph_one_bicoloring n he p = decide ((p 0).val % 2 = 0) := rfl

/-- **NO EDGE OF THE PERIODIC LATTICE JOINS TWO SITES OF THE SAME PARITY**, at even side length.
This is the even/odd sublattice decomposition, stated as a theorem about `torusGraph`. -/
theorem torusGraph_one_adj_parity_ne (n : ℕ) (he : Even (n + 1))
    {p q : BoxGraph.Site 1 (n + 1)} (h : (torusGraph 1 (n + 1)).Adj p q) :
    decide ((p 0).val % 2 = 0) ≠ decide ((q 0).val % 2 = 0) := by
  have := (torusGraph_one_bicoloring n he).valid h
  simpa using this

/-! ## 4. The estate's own degree bound is attained -/

/-- **EVERY SITE OF THE `d = 1` PERIODIC LATTICE HAS DEGREE EXACTLY `2`**, for `n ≥ 3`. -/
theorem torusGraph_one_degree (n : ℕ) (p : BoxGraph.Site 1 (n + 3)) :
    (torusGraph 1 (n + 3)).degree p = 2 :=
  (SimpleGraph.Iso.degree_eq (torusGraph_one_iso (n + 2)) p).symm.trans cycleGraph_degree_three_le

/-- **SO `TorusDecay.torusGraph_degree_le`'S BOUND IS ATTAINED, NOT MERELY VALID.** That theorem
bounds every degree of `torusGraph d n` by `2 * d`; at `d = 1` and `n ≥ 3` the bound is an
equality, so `GreenDecay.decayRate (2 * d)` and every estate estimate downstream of it cannot be
improved by sharpening the degree bound in this case. -/
theorem torusGraph_degree_le_attained (n : ℕ) (p : BoxGraph.Site 1 (n + 3)) :
    (torusGraph 1 (n + 3)).degree p = 2 * 1 := by
  simpa using torusGraph_one_degree n p

end TorusCycleTheory
