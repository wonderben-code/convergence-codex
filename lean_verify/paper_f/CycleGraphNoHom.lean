import TorusCycleGraph
import LaplacianSharpEquality

/-!
# No odd cycle maps into an even one, so half of the embedding question is not a girth problem

`TorusEmbedding` settles the watchlist's embedding question at **one instance**, by `decide`:
`no_embedding_three_into_six` says there is no injective adjacency-preserving
`Site 1 3 → Site 1 6`, and the register records that `n = 4` **overflowed the decision procedure's
stack** — *"a resource limit and evidence for nothing"*. The route to the general statement was
written out in the same block and costed: it needs `girth (cycleGraph n) = n`, whose lower bound the
register calls *"the real content"* and which Mathlib does not have.

**FOR ODD SIDE LENGTH NONE OF THAT IS NEEDED, AND THIS FILE IS THE PROOF.**

> **`isEmpty_hom_of_odd_of_even`** — for `n` odd and at least `3`, and `m` **even**, there is **no
> graph homomorphism at all** `cycleGraph n →g cycleGraph m`. Not "no injective one": none.
>
> **`isEmpty_torusHom_of_odd_of_even`** — the same on this project's own periodic lattice in one
> dimension, and **`no_hom_odd_into_double`** is the register's own `torusGraph 1 n → torusGraph 1
> (2n)` at every odd `n ≥ 3`.

**AND THE COLOURING FACTS WERE ALREADY HERE, WHICH SHARPENS WHAT THIS FILE ADDS.**
`TorusCycleTheory` drew `(torusGraph 1 n).chromaticNumber = 2` for even `n` and `= 3` for odd on
2026-08-17, and the register's own block records them. **What nobody drew is the consequence for
maps.** The same block, in the same paragraph, says *"Girth is still not reached … Half (b) still
has not moved"* — treating girth as **the** route to the embedding question when half of that
question was already settled by facts sitting four lines above the sentence. So this file's content
is not a colouring; it is that **colourability answers the odd case and girth was never needed for
it**.

**THE ARGUMENT IS TWO LINES AND USES NO GIRTH.** An even cycle is two-colourable
(`cycleGraph.bicoloring_of_even`, Mathlib's); a homomorphism pulls a colouring back
(`Colorable.of_hom`); an odd cycle has chromatic number `3`
(`chromaticNumber_cycleGraph_of_odd`, Mathlib's). Colourability is a **homomorphism invariant**, and
that is the whole of it — injectivity never enters, which is why the statement is stronger than the
one the register asks for.

## What this re-costs, and it is a route rather than a wall

**The register treats *"no embedding `torusGraph 1 n → torusGraph 1 (2n)` for `n ≥ 3`"* as one
problem with one obstruction.** It is two problems:

* **`n` odd** — closed here, by colourability, with no girth and no injectivity. `2n` is even
  whenever `n` is a natural number, so the target is always two-colourable and the source never is.
* **`n` even** — untouched, and it is where the mathematics is. `TorusEmbedding
  .embedding_two_into_four` exhibits an embedding at `n = 2`, so the even case is **not** vacuous
  and cannot fall to any parity argument. The girth route the register traced is needed for this
  half and only for this half.

**No cost is claimed for the even half** (`ERRATUM 246`, `ERRATUM 194`), and nothing here says it is
easier or harder than the register estimated. What changes is that the girth project is now known to
be needed for half the statement rather than all of it, and the half it is not needed for is done.

**`no_embedding_three_into_six` IS RECOVERED BELOW** (`ERRATUM 201`), so the generalisation is
instantiated at the statement it generalises rather than asserted to specialise — and the recovery
also **replaces a `decide`**, which is why `n = 4` overflowing is no longer relevant on this side.

## What this does NOT do

**It says nothing about the even case**, which is the whole of the remaining question and is stated
above rather than glossed.

**It does not prove any girth.** `girth (cycleGraph n) = n` remains absent from Mathlib and unproved
here; this file routes around it for the odd case and does not touch it.

**It does not move the infinite-volume item.** That item is about covariances and this is about
graph maps — the register's own sentence, and it is as true of this file as of the two it
generalises.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleGraphNoHom

open SimpleGraph TorusReflection TorusCycleGraph LaplacianSharpEquality

/-! ## 1. An even cycle is two-colourable -/

/-- Mathlib's `Bool`-valued bicolouring, read as `Colorable 2`. -/
theorem cycleGraph_colorable_two_of_even {m : ℕ} (hm : Even m) : (cycleGraph m).Colorable 2 := by
  simpa using (SimpleGraph.cycleGraph.bicoloring_of_even m hm).colorable

/-! ## 2. So nothing maps an odd cycle into an even one -/

/-- **NO GRAPH HOMOMORPHISM AT ALL**, injective or otherwise. Colourability is a homomorphism
invariant; the source needs three colours and the target has two. -/
theorem isEmpty_hom_of_odd_of_even {n m : ℕ} (h2 : 2 ≤ n) (hn : Odd n) (hm : Even m) :
    IsEmpty (cycleGraph n →g cycleGraph m) := by
  refine ⟨fun f => ?_⟩
  have hc : (cycleGraph n).Colorable 2 :=
    SimpleGraph.Colorable.of_hom f (cycleGraph_colorable_two_of_even hm)
  have hle := hc.chromaticNumber_le
  rw [chromaticNumber_cycleGraph_of_odd n h2 hn] at hle
  norm_num at hle

/-! ## 3. The same on this project's own periodic lattice -/

/-- The one-dimensional periodic lattice at even side length is two-colourable, through
`TorusCycleGraph.torusGraph_one_iso`. -/
theorem torus_one_colorable_two_of_even {m : ℕ} (hm : Even (m + 1)) :
    (torusGraph 1 (m + 1)).Colorable 2 :=
  SimpleGraph.Colorable.of_hom (torusGraph_one_iso m).toHom
    (cycleGraph_colorable_two_of_even hm)

/-- **AND SO NOTHING MAPS AN ODD LATTICE INTO AN EVEN ONE.** The non-colourability half is
`LaplacianSharpEquality.torus_not_colorable_two_of_odd` at `d = 0`, so this reuses that unit rather
than repeating its pullback along `axisHom`. -/
theorem isEmpty_torusHom_of_odd_of_even {n m : ℕ} (hn : Odd (n + 1)) (h3 : 3 ≤ n + 1)
    (hm : Even (m + 1)) :
    IsEmpty (torusGraph 1 (n + 1) →g torusGraph 1 (m + 1)) :=
  ⟨fun f => torus_not_colorable_two_of_odd (d := 0) hn h3
    (SimpleGraph.Colorable.of_hom f (torus_one_colorable_two_of_even hm))⟩

/-! ## 4. The register's own statement, at every odd side length -/

/-- **ROUTE C's ODD HALF.** The register asks for *"no injective graph homomorphism `torusGraph 1 n
→ torusGraph 1 (2n)` for `n ≥ 3`"*; at odd `n` there is no homomorphism whatever, and `2n` is even
for free. -/
theorem no_hom_odd_into_double {n : ℕ} (hn : Odd (n + 3)) :
    IsEmpty (torusGraph 1 (n + 3) →g torusGraph 1 (2 * (n + 3))) := by
  have hrw : 2 * (n + 3) = (2 * n + 5) + 1 := by ring
  rw [hrw]
  exact isEmpty_torusHom_of_odd_of_even (n := n + 2) (m := 2 * n + 5)
    (by simpa using hn) (by omega) ⟨n + 3, by ring⟩

/-! ## 5. And `TorusEmbedding`'s decided instance is recovered -/

/-- **`no_embedding_three_into_six` WITHOUT `decide`** (`ERRATUM 201`). That theorem needs the map
to be injective; this shows the adjacency half alone is already impossible. -/
example : ¬ ∃ φ : BoxGraph.Site 1 3 → BoxGraph.Site 1 6,
    TorusEmbedding.IsSiteEmbedding φ := by
  rintro ⟨φ, -, hadj⟩
  exact (isEmpty_torusHom_of_odd_of_even (n := 2) (m := 5)
    ⟨1, by norm_num⟩ (by norm_num) ⟨3, by norm_num⟩).elim ⟨φ, fun {a b} h => hadj a b h⟩

end CycleGraphNoHom
