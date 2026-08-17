import TorusCycleTheory
import TorusEmbedding

/-!
# The general statement, and the route I recorded to it was the wrong route

`TorusEmbedding` decided two side lengths and then said, of the general claim — **no injective
graph homomorphism `torusGraph 1 n → torusGraph 1 (2n)` for `n ≥ 3`** — that it is *"not proved
here"*, believable only for a reason that is *"an argument in prose, exactly the kind this file
exists to distrust"*. It recorded a two-half route: the estate half (`torusGraph 1 n` is
`cycleGraph n`) and the Mathlib half (`girth (cycleGraph n) = n`, absent from the library). Both
halves were repeated in `TorusCycleGraph`, in `UNLOCK_WATCHLIST` and in `TorusCycleTheory`.

**THE GENERAL STATEMENT IS PROVED HERE, AND THE MATHLIB HALF IS NOT USED.** No girth, no cycle, no
walk-that-must-be-shown-to-be-a-cycle. **The recorded route was harder than the problem.**

## What replaces it

The whole argument is degrees and connectivity, and both were already in the estate this morning.

* An injective homomorphism carries the two neighbours of `v` to two *distinct* neighbours of
  `φ v`. In `torusGraph 1 m` with `m ≥ 3` a site has **exactly** two neighbours
  (`TorusCycleTheory.torusGraph_one_degree`, proved earlier today as a fold-back, and used here
  within the hour). Two distinct elements of a two-element set exhaust it, so
  **`φ` maps the neighbourhood of `v` ONTO the neighbourhood of `φ v`** — it is a local
  bijection, which no amount of injectivity alone would give.
* Hence the range of `φ` is closed under adjacency. `TorusDecay.torusGraph_connected` says the
  target is connected, and a nonempty adjacency-closed set in a connected graph is everything.
* So `φ` is onto as well as injective, and the two side lengths agree.

## What is proved

* **`torusGraph_one_degree_of_three_le`** — degree exactly `2` at every side length `≥ 3`, the
  form the argument needs.
* **`mem_of_walk`** — an adjacency-closed set contains everything reachable from a point of it.
* **`neighborFinset_image`** — the local-bijection step, which is where the content is.
* **`side_eq_of_isSiteEmbedding`** — **any** embedding between one-dimensional tori of side
  lengths `≥ 3` forces the side lengths to be equal. This is stronger than what was asked and is
  the natural statement: such a map is automatically a bijection.
* **`no_embedding_of_ne`** — hence none exists when the sides differ.
* **`no_embedding_double`** — **`TorusEmbedding`'s general statement**, `n ≥ 3`, as a corollary.
* **`no_embedding_three_into_six'`** — the `decide`d instance re-derived from the general theorem,
  so the two agree rather than merely coexisting.

## What this does and does not do to the records

**`TorusEmbedding`'s recorded Mathlib-side obstacle is not an obstacle to THIS statement.** That
is a correction to my own record, made by proving the statement rather than by rewriting the note:
the note said what the route needed, and the route it described was not the only one. **The girth
fact is still absent from Mathlib** and is still interesting; it is simply not what this needed.

**`n = 2` is still the exception and is still explained.** `TorusEmbedding.embedding_two_into_four`
exhibits an embedding at `n = 2`, and `2 < 3`, so nothing here contradicts it — the hypothesis
`3 ≤ n` is exactly what excludes the degenerate side length at which the torus *is* the box.

**`d = 1` only**, as everywhere in this chain: at `d ≥ 2` sites do not have degree `2` and the
local-bijection step fails at its first line.

**It says nothing about covariances.** `UNLOCK_WATCHLIST`'s infinite-volume item is about a
compatible family of measures; this is about graph maps, and a missing graph embedding is not an
incompatible family. Clause (i) is `ASSUMPTIONS_LEDGER` 47, an author's decision, and it does not
move. **`OS4` does not move. No spectral gap is claimed. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusEmbeddingGeneral

open TorusReflection TorusEmbedding SimpleGraph

/-! ## 1. Degree exactly two, in the form the argument needs -/

/-- **EVERY SITE OF THE `d = 1` TORUS HAS EXACTLY TWO NEIGHBOURS AT EVERY SIDE LENGTH `≥ 3`**, the
`3 ≤ m` restatement of `TorusCycleTheory.torusGraph_one_degree`. -/
theorem torusGraph_one_degree_of_three_le {m : ℕ} (hm : 3 ≤ m) (p : BoxGraph.Site 1 m) :
    (torusGraph 1 m).degree p = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  exact TorusCycleTheory.torusGraph_one_degree k p

/-! ## 2. Connectivity, in the form the argument needs -/

/-- A set closed under adjacency contains the far end of every walk starting inside it. This is
the whole use made of connectivity, and it is stated for an arbitrary graph. -/
theorem mem_of_walk {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hS : ∀ ⦃x y⦄, x ∈ S → G.Adj x y → y ∈ S) : ∀ {u v : V}, G.Walk u v → u ∈ S → v ∈ S := by
  intro u v w
  induction w with
  | nil => exact id
  | cons h _ ih => exact fun hu => ih (hS hu h)

/-! ## 3. The local-bijection step, which is the content -/

/-- **AN EMBEDDING IS A LOCAL BIJECTION.** `φ` carries the neighbourhood of `v` *onto* the
neighbourhood of `φ v` — not merely into it.

Injectivity gives two distinct images inside a set that `torusGraph_one_degree_of_three_le` says
has exactly two elements, and two distinct elements of a two-element set are all of it. **Nothing
weaker than an exact degree count does this**: a bound `≤ 2` leaves the image possibly proper. -/
theorem neighborFinset_image {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    {φ : BoxGraph.Site 1 a → BoxGraph.Site 1 b} (h : IsSiteEmbedding φ) (v : BoxGraph.Site 1 a) :
    ((torusGraph 1 a).neighborFinset v).image φ = (torusGraph 1 b).neighborFinset (φ v) := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact h.2 _ _ hx
  · rw [Finset.card_image_of_injective _ h.1, SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree, torusGraph_one_degree_of_three_le ha,
      torusGraph_one_degree_of_three_le hb]

/-! ## 4. The general theorem -/

/-- **ANY EMBEDDING BETWEEN ONE-DIMENSIONAL TORI OF SIDE `≥ 3` FORCES THE SIDES TO BE EQUAL.**

`φ`'s range is closed under adjacency, by the local-bijection step; the target is connected, by
`TorusDecay.torusGraph_connected`; so the range is everything and `φ` is a bijection. -/
theorem side_eq_of_isSiteEmbedding {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    {φ : BoxGraph.Site 1 a → BoxGraph.Site 1 b} (h : IsSiteEmbedding φ) : a = b := by
  have hbase : BoxGraph.Site 1 a := fun _ => ⟨0, by omega⟩
  have hclosed : ∀ ⦃x y⦄, x ∈ Set.range φ → (torusGraph 1 b).Adj x y → y ∈ Set.range φ := by
    rintro _ y ⟨v, rfl⟩ hxy
    have : y ∈ ((torusGraph 1 a).neighborFinset v).image φ := by
      rw [neighborFinset_image ha hb h v, SimpleGraph.mem_neighborFinset]
      exact hxy
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp this
    exact ⟨w, rfl⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w⟩ := (TorusDecay.torusGraph_connected (n := b) 1 (by omega)).preconnected
      (φ hbase) y
    have hy : y ∈ Set.range φ := mem_of_walk hclosed w ⟨hbase, rfl⟩
    exact hy
  have hcard := Fintype.card_of_bijective ⟨h.1, hsurj⟩
  simpa using hcard

/-- **SO THERE IS NO EMBEDDING BETWEEN TORI OF DIFFERENT SIDE LENGTHS `≥ 3`.** -/
theorem no_embedding_of_ne {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a ≠ b)
    (φ : BoxGraph.Site 1 a → BoxGraph.Site 1 b) : ¬ IsSiteEmbedding φ :=
  fun h => hab (side_eq_of_isSiteEmbedding ha hb h)

/-- **`TorusEmbedding`'S GENERAL STATEMENT.** There is no injective graph homomorphism
`torusGraph 1 n → torusGraph 1 (2n)` for any `n ≥ 3` — proved, not argued in prose, and **without
the `girth (cycleGraph n) = n` that the recorded route said it needed.** -/
theorem no_embedding_double (n : ℕ) (hn : 3 ≤ n)
    (φ : BoxGraph.Site 1 n → BoxGraph.Site 1 (2 * n)) : ¬ IsSiteEmbedding φ :=
  no_embedding_of_ne hn (by omega) (by omega) φ

/-- **AND THE DECIDED INSTANCE IS THE GENERAL THEOREM AT `n = 3`**, so `TorusEmbedding`'s
computation and this argument agree rather than merely coexisting. -/
theorem no_embedding_three_into_six' :
    ¬ ∃ φ : BoxGraph.Site 1 3 → BoxGraph.Site 1 6, IsSiteEmbedding φ := by
  rintro ⟨φ, hφ⟩
  exact no_embedding_of_ne (by omega) (by omega) (by omega) φ hφ

end TorusEmbeddingGeneral
