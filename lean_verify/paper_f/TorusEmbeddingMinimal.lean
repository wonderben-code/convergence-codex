import TorusEmbeddingAllDims

/-!
# The hypothesis set, made minimal — one is redundant and the other two are witnessed

`TorusEmbeddingAllDims.side_eq_of_isTorusEmbedding` carries three hypotheses:

```
(hd : 1 ≤ d)  (ha : 3 ≤ a)  (hb : 3 ≤ b)
```

**`hb` is redundant**, and `AdjSqForcesRegular` is the estate's own precedent for why that is worth
a file rather than a footnote: *"a redundant hypothesis makes a class look narrower than it is."*
Read as written, the theorem looks like a statement about tori that are *both* large. It is a
statement about a large source and an arbitrary target.

**The reason is one line of counting and it was available the whole time.** An injective map forces
`a^d ≤ b^d`, hence `a ≤ b` once `d ≥ 1`. So either `b ≥ a ≥ 3` — and `hb` is free — or `b < a` and
there is no injection at all. **The hypothesis was never excluding anything.**

## What is proved

* **`card_site`** — `Fintype.card (Site d n) = n ^ d`, which the previous file used inside a
  `simpa` and never named.
* **`le_of_isTorusEmbedding`** — **injectivity alone** forces `a ≤ b`. No adjacency, no
  connectivity, no degree count: this is the counting half on its own, and separating it is what
  shows the geometric half was never needed for it.
* **`three_le_target`** — hence `3 ≤ b`, from `3 ≤ a`.
* **`side_eq_of_isTorusEmbedding'`**, **`no_torus_embedding_of_ne'`**,
  **`no_torus_embedding_double'`** — the previous file's theorems with `hb` gone.

## And the other two hypotheses are NOT removable, which is checked and not asserted

`ERRATUM 194` is about difficulty estimates written in the confident register of the theorems
around them. A claim that a hypothesis is *necessary* is the same kind of sentence, so both are
witnessed by an actual embedding rather than argued:

* **`embedding_of_dim_zero`** — at `d = 0` there is an embedding `Site 0 3 → Site 0 5`, with
  `3 ≠ 5`. `Site 0 n` is a one-point type whatever `n` is (the empty function), and
  `torusGraph 0 n` has no edges at all, so every map between them is an embedding and no counting
  argument can see the side length. **`1 ≤ d` is exactly what excludes this.**
* **`side_two_embeds`** — at `a = 2` there is an embedding `Site 1 2 → Site 1 4`, which is
  `TorusEmbedding.embedding_two_into_four` re-exported through `isTorusEmbedding_one_iff`. **`3 ≤ a`
  is exactly what excludes this**, and the reason is the estate's own
  `TorusReflection.torus_two_eq_box`: at side `2` the torus **is** the box, the two cyclic steps
  along a coordinate coincide, and the degree drops from `2d` to `d`.

**So the hypothesis set is now minimal**: one removed, two witnessed necessary.

## What this is NOT

**`side_two_embeds` is a witness at `d = 1` and is not a claim about every `d`.** It shows `3 ≤ a`
cannot simply be deleted. Whether an embedding `Site d 2 → Site d 4` exists for `d ≥ 2` is **not
settled here and is not needed** — one counterexample is enough to keep a hypothesis, and claiming
more than the witness gives is the failure this file's header is guarding against.

**Nothing new is proved about the torus.** Every theorem here is the previous file's with a
hypothesis discharged, or a witness that a hypothesis is doing work. **`OS4` does not move**,
nothing touches `gaussianField`, no reflection positivity is used or affected, and **no published
tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusEmbeddingMinimal

open TorusReflection TorusEmbeddingAllDims BoxGraph SimpleGraph

variable {d a b : ℕ}

/-! ## 1. The counting half, on its own -/

/-- The number of sites, named. The previous file computed this inside a `simpa` and never gave it
a name, which is why the counting step and the geometric step stayed tangled. -/
theorem card_site (d n : ℕ) : Fintype.card (Site d n) = n ^ d := by
  simp

/-- **INJECTIVITY ALONE FORCES `a ≤ b`.** No adjacency, no connectivity, no degree count — the
hypothesis used is `h.1` and nothing else.

Separating this from the geometry is the whole point: it is what shows `3 ≤ b` was never excluding
anything. -/
theorem le_of_isTorusEmbedding (hd : 1 ≤ d) {φ : Site d a → Site d b}
    (h : IsTorusEmbedding φ) : a ≤ b := by
  have hcard : Fintype.card (Site d a) ≤ Fintype.card (Site d b) :=
    Fintype.card_le_of_injective φ h.1
  rw [card_site, card_site] at hcard
  by_contra hlt
  exact absurd hcard
    (Nat.not_le.mpr (Nat.pow_lt_pow_left (Nat.not_le.mp hlt) (by omega : d ≠ 0)))

/-- **SO `3 ≤ b` IS IMPLIED BY `3 ≤ a`** and was redundant wherever it appeared beside it. -/
theorem three_le_target (hd : 1 ≤ d) (ha : 3 ≤ a) {φ : Site d a → Site d b}
    (h : IsTorusEmbedding φ) : 3 ≤ b :=
  le_trans ha (le_of_isTorusEmbedding hd h)

/-! ## 2. The previous file's theorems, with the redundant hypothesis gone -/

/-- **ANY EMBEDDING FROM A TORUS OF SIDE `≥ 3` FORCES THE SIDES EQUAL** — the target's side length
is not restricted. -/
theorem side_eq_of_isTorusEmbedding' (hd : 1 ≤ d) (ha : 3 ≤ a) {φ : Site d a → Site d b}
    (h : IsTorusEmbedding φ) : a = b :=
  side_eq_of_isTorusEmbedding hd ha (three_le_target hd ha h) h

/-- **AND SO THERE IS NO EMBEDDING INTO A TORUS OF A DIFFERENT SIDE**, whatever that side is. -/
theorem no_torus_embedding_of_ne' (hd : 1 ≤ d) (ha : 3 ≤ a) (hab : a ≠ b)
    (φ : Site d a → Site d b) : ¬ IsTorusEmbedding φ :=
  fun h => hab (side_eq_of_isTorusEmbedding' hd ha h)

/-- The doubling statement, restated from the sharpened form so the two agree. -/
theorem no_torus_embedding_double' (hd : 1 ≤ d) (n : ℕ) (hn : 3 ≤ n)
    (φ : Site d n → Site d (2 * n)) : ¬ IsTorusEmbedding φ :=
  no_torus_embedding_of_ne' hd hn (by omega) φ

/-! ## 3. The two remaining hypotheses are necessary, and here are the witnesses -/

/-- **AT `d = 0` THE SIDE LENGTHS NEED NOT AGREE.** `Site 0 n` is a one-point type for every `n` —
the empty function — and `torusGraph 0 n` has no edges, so every map between them is an embedding.
**This is what `1 ≤ d` excludes**, and it is exhibited rather than argued. -/
theorem embedding_of_dim_zero : ∃ φ : Site 0 3 → Site 0 5, IsTorusEmbedding φ := by
  refine ⟨fun _ => Fin.elim0, fun p q _ => ?_, fun p q hpq => ?_⟩
  · exact Subsingleton.elim p q
  · obtain ⟨i, -⟩ := hpq
    exact i.elim0

/-- **AT SIDE `2` AN EMBEDDING EXISTS**, so `3 ≤ a` is doing work. This is
`TorusEmbedding.embedding_two_into_four` read through `isTorusEmbedding_one_iff`, and the estate
already knows why side `2` is special: `TorusReflection.torus_two_eq_box` says the torus there
**is** the box, the two cyclic steps along a coordinate coincide, and the degree drops from `2d`
to `d`. -/
theorem side_two_embeds : ∃ φ : Site 1 2 → Site 1 4, IsTorusEmbedding φ := by
  obtain ⟨φ, hφ⟩ := TorusEmbedding.embedding_two_into_four
  exact ⟨φ, (isTorusEmbedding_one_iff φ).mpr hφ⟩

end TorusEmbeddingMinimal
