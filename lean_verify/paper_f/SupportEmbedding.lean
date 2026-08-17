import ConnectedCrossEmbedding
import EdgeCountEmbedding

/-!
# The last assumed count comes off too — and here is what does not

`EdgeCountEmbedding` assumes two counts: the vertices agree and the edges agree.
`ConnectedCrossEmbedding` derives the vertex count from connectivity, but keeps regularity. **The
vertex count comes off with neither**, and the replacement is the weakest condition yet: *no vertex
of the target is isolated.*

Every vertex of `G'` lies on an edge; every edge of `G'` is the image of an edge of `G`; so every
vertex of `G'` is an image. **`surjective_of_support`** is those three sentences, and with it the
vertex count is **derived** rather than assumed, in a statement with **no regularity and no
connectivity** in it.

## What is proved

* **`surjective_of_support`** — onto, from the edge count and the absence of isolated vertices.
* **`card_eq_of_support`, `isoOfSupport`, `gaussianField_map_of_support`** — hence the vertex
  counts, the isomorphism, and the equality of Gaussian fields.
* **`exists_adj_of_regular`** — `k`-regular with `k > 0` has no isolated vertex, which is how the
  three criteria in this chain meet.

## And now the part this chain has repeatedly got wrong: what does NOT come off

Three times in two days a hypothesis was called irremovable on the strength of one proof route, and
three times that was wrong (`ERRATUM 194`). **So the remaining hypotheses are not asserted here.
They are refuted counterexamples, decided by the kernel.**

* **`edgeCard_not_removable`** — the identity from the three-point path into the complete graph on
  the same three points. Injective, edge-preserving, vertex counts equal, **no isolated vertex**,
  and it reflects nothing: `0` and `2` are adjacent in the target and not in the source. **The edge
  count is what fails**, and dropping it loses the conclusion.
* **`support_not_removable`** — the empty graph on one point into the empty graph on two. Both have
  zero edges, so the edge count holds; the map is injective and vacuously edge-preserving; it is
  not onto. **Isolated vertices are what fails.**
* **`connected_not_removable`** — `twoCycles` is two disjoint four-cycles on `Fin 8`, `2`-regular,
  and `torusGraph 1 4` embeds into it by doubling. **This is the `C₄ ↪ C₄ ⊔ C₄` that
  `RegularCrossEmbedding`, `EdgeCountEmbedding` and `ConnectedCrossEmbedding` have all cited in
  prose and none has exhibited.** It is now a theorem: the embedding exists and is not onto, so
  `ConnectedCrossEmbedding`'s connectivity hypothesis is doing work.

**Nothing in this section is a difficulty estimate.** Each is a witness, and each is `decide`d.

## What this is NOT

**It does not subsume the other two.** `EdgeCountEmbedding` covers targets *with* isolated vertices
when the vertex counts are given; `ConnectedCrossEmbedding` derives the edge count it never needs,
from regularity. **Three criteria, three different things assumed, and the counterexamples above
say why none is redundant.**

**It is not OS3**, for the seventh time in this chain. **`OS4` does not move**, no spectral gap is
claimed, and **no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SupportEmbedding

open SimpleGraph GraphLaplacian RegularCrossEmbedding

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
variable {k : ℕ} {m : ℝ}

/-! ## 1. Onto, from the edge count and no isolated vertex -/

omit [DecidableEq V] [DecidableEq W] in
/-- **EVERY VERTEX OF THE TARGET IS AN IMAGE.** It lies on an edge; that edge is the image of an
edge of `G`; so one of its two endpoints is the vertex.

**No regularity and no connectivity appear**, and the vertex count is a conclusion rather than a
hypothesis. -/
theorem surjective_of_support (hE : G.edgeFinset.card = G'.edgeFinset.card)
    (hsupp : ∀ w : W, ∃ w', G'.Adj w w') {φ : V → W} (h : IsGraphEmbedding G G' φ) :
    Function.Surjective φ := by
  classical
  intro w
  obtain ⟨w', hw'⟩ := hsupp w
  have hmem : s(w, w') ∈ G.edgeFinset.image (Sym2.map φ) := by
    rw [EdgeCountEmbedding.edgeFinset_image_of_isGraphEmbedding hE h,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hw'
  obtain ⟨z, -, hzz⟩ := Finset.mem_image.mp hmem
  induction z using Sym2.ind with
  | _ a b =>
    rw [Sym2.map_mk] at hzz
    rcases Sym2.eq_iff.mp hzz with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ⟨a, h1⟩
    · exact ⟨b, h2⟩

omit [DecidableEq V] [DecidableEq W] in
/-- **AND SO THE VERTEX COUNTS AGREE**, which `EdgeCountEmbedding` had to assume. -/
theorem card_eq_of_support (hE : G.edgeFinset.card = G'.edgeFinset.card)
    (hsupp : ∀ w : W, ∃ w', G'.Adj w w') {φ : V → W} (h : IsGraphEmbedding G G' φ) :
    Fintype.card V = Fintype.card W :=
  Fintype.card_of_bijective ⟨h.1, surjective_of_support hE hsupp h⟩

/-! ## 2. Hence the isomorphism and the fields -/

/-- **NO REGULARITY, NO CONNECTIVITY, AND NO VERTEX COUNT**: an injective edge-preserving map
between graphs with the same number of edges, into a target with no isolated vertex, is an
isomorphism. -/
noncomputable def isoOfSupport (hE : G.edgeFinset.card = G'.edgeFinset.card)
    (hsupp : ∀ w : W, ∃ w', G'.Adj w w') {φ : V → W} (h : IsGraphEmbedding G G' φ) : G ≃g G' :=
  EdgeCountEmbedding.isoOfEdgeCard (card_eq_of_support hE hsupp h) hE h

/-- **AND THEREFORE THE GAUSSIAN FIELDS AGREE.** -/
theorem gaussianField_map_of_support (hE : G.edgeFinset.card = G'.edgeFinset.card)
    (hsupp : ∀ w : W, ∃ w', G'.Adj w w') {φ : V → W} (h : IsGraphEmbedding G G' φ) (hm : m ≠ 0) :
    (gaussianField G m).map
        (FieldIsoInvariance.congrField (isoOfSupport hE hsupp h).toEquiv)
      = gaussianField G' m :=
  EdgeCountEmbedding.gaussianField_map_of_edgeCard (card_eq_of_support hE hsupp h) hE h hm

omit [DecidableEq V] [DecidableEq W] in
/-- **A `k`-REGULAR GRAPH WITH `k > 0` HAS NO ISOLATED VERTEX** — how the three criteria of this
chain meet, and the reason the hypothesis above is weaker than regularity rather than sideways
from it. -/
theorem exists_adj_of_regular (hk : 0 < k) (hreg : G'.IsRegularOfDegree k) (w : W) :
    ∃ w', G'.Adj w w' := by
  have hpos : 0 < (G'.neighborFinset w).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree, hreg w]; exact hk
  obtain ⟨w', hw'⟩ := Finset.card_pos.mp hpos
  exact ⟨w', (SimpleGraph.mem_neighborFinset _ _ _).mp hw'⟩

/-! ## 3. What does NOT come off, decided rather than asserted

`ERRATUM 194` fired three times in two days on this chain, every time because a hypothesis was
called irremovable on the strength of one proof route. These are witnesses instead.
-/

/-- **THE EDGE COUNT IS NOT REMOVABLE.** The identity from the three-point path
(`BoxGraph.boxGraph 1 3`) into the complete graph on the same three points: injective,
edge-preserving, equal vertex counts, no isolated vertex — and `0` and `2` are adjacent in the
target and not in the source. -/
theorem edgeCard_not_removable :
    IsGraphEmbedding (BoxGraph.boxGraph 1 3) (⊤ : SimpleGraph (BoxGraph.Site 1 3)) id ∧
      ¬ ∀ p q : BoxGraph.Site 1 3,
        (⊤ : SimpleGraph (BoxGraph.Site 1 3)).Adj (id p) (id q) → (BoxGraph.boxGraph 1 3).Adj p q :=
  ⟨⟨fun _ _ h => h, by decide⟩, by decide⟩

/-- **THE ABSENCE OF ISOLATED VERTICES IS NOT REMOVABLE**, and trivially: the empty graph on one
point into the empty graph on two. Both have zero edges, the map is injective and vacuously
edge-preserving, and it misses a vertex. -/
theorem support_not_removable :
    IsGraphEmbedding (⊥ : SimpleGraph (Fin 1)) (⊥ : SimpleGraph (Fin 2)) (fun _ => 0) ∧
      (⊥ : SimpleGraph (Fin 1)).edgeFinset.card = (⊥ : SimpleGraph (Fin 2)).edgeFinset.card ∧
      ¬ Function.Surjective (fun _ : Fin 1 => (0 : Fin 2)) :=
  ⟨⟨by decide, by decide⟩, by simp, by decide⟩

/-! ## 4. `C₄ ↪ C₄ ⊔ C₄`, cited in prose by three files and exhibited by none -/

/-- **TWO DISJOINT FOUR-CYCLES.** Labels differing by `2` in `Fin 8`: the evens form one cycle and
the odds the other. -/
def twoCycles : SimpleGraph (Fin 8) where
  Adj i j := i - j = 2 ∨ j - i = 2
  symm := by rintro i j (h | h); exacts [Or.inr h, Or.inl h]
  loopless := ⟨by
    intro i hi
    have h : (0 : Fin 8) = 2 := by rcases hi with h | h <;> rwa [sub_self] at h
    exact absurd h (by decide)⟩

instance : DecidableRel twoCycles.Adj := fun i j =>
  inferInstanceAs (Decidable (i - j = 2 ∨ j - i = 2))

/-- It is `2`-regular, so `ConnectedCrossEmbedding`'s degree hypotheses hold at both ends. -/
theorem twoCycles_two_regular : twoCycles.IsRegularOfDegree 2 := by
  change ∀ v, twoCycles.degree v = 2
  decide

/-- The four-cycle onto the even cycle: `0 ↦ 0, 1 ↦ 2, 2 ↦ 4, 3 ↦ 6`. -/
def doubling (p : BoxGraph.Site 1 4) : Fin 8 := ![0, 2, 4, 6] (p 0)

/-- **DROPPING CONNECTIVITY BREAKS `ConnectedCrossEmbedding`, AND HERE IS THE MAP.** Doubling sends
the four-cycle onto the even cycle: injective, edge-preserving, `2`-regular at both ends — and not
onto, so the vertex counts do not agree and no isomorphism exists.

`RegularCrossEmbedding`, `EdgeCountEmbedding` and `ConnectedCrossEmbedding` all cite this example
in prose. **It is a theorem now.** -/
theorem connected_not_removable :
    IsGraphEmbedding (TorusReflection.torusGraph 1 4) twoCycles doubling ∧
      ¬ Function.Surjective doubling :=
  ⟨⟨by decide, by decide⟩, by decide⟩

end SupportEmbedding
