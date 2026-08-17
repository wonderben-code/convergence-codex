import TorusReflection
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# The one-dimensional torus IS Mathlib's cycle graph

`TorusEmbedding` located the route to its own unproved general statement and recorded it in two
halves. **This file is the estate-side half.**

The estate's `torusGraph 1 n` is a graph on `BoxGraph.Site 1 n = Fin 1 → Fin n`, with adjacency
`adjT` written out by hand — *distinct, and one is the other's successor, with the wrap-around given
as two extra disjuncts*. Mathlib's `SimpleGraph.cycleGraph n` is `circulantGraph {1}` on `Fin n`,
whose adjacency is *distinct, and the difference is `1` in the additive group*. These are visibly
the same relation. **Visibly is not proved**, and `TorusEmbedding` said so.

## What is proved

* **`sub_one_iff`** — the arithmetic core: in `Fin (n+1)`, `a - b = 1` holds exactly when
  `b.val + 1 = a.val`, or `b` is the last index and `a` is `0`. This is the wrap, and it is where
  the work is: `Fin` subtraction is `%`-arithmetic, `omega` cannot see through it, and
  `Fin.val_add_one`'s own case split on `b = Fin.last n` is what supplies the two branches.
* **`adjT_iff_cycleGraph`** — hence `adjT a b ↔ (cycleGraph (n+1)).Adj a b`.
* **`torusGraph_one_iso`** — hence `torusGraph 1 (n+1) ≃g SimpleGraph.cycleGraph (n+1)`, the
  isomorphism transported along `Equiv.funUnique`.

## Why this is worth a file

**It hands the estate's `d = 1` torus to Mathlib's cycle theory.** Girth, bipartiteness,
colourings, Hamiltonicity and the `Free`/`Copy` machinery are all stated there for `cycleGraph`, and
none of them was reachable from `adjT`. The estate had a hand-rolled object where a standard one
already existed, and nothing connected them.

## What this is NOT

**It does not prove `TorusEmbedding`'s general statement**, which is a fact about this file and
remains true. The reason given here for why it does not was **wrong, and is corrected the same
day**: this said the general statement *"needs `girth (cycleGraph n) = n`"*, absent from Mathlib.
**It does not need it.** `TorusEmbeddingGeneral.no_embedding_double` proves the general statement
from an exact degree count and connectivity, using neither girth nor `cycleGraph`. The girth fact
is still absent from Mathlib and is still worth having; it was never the obstruction. *The
sentence is left standing rather than deleted because a wrong estimate of difficulty is worth
keeping next to the thing that refuted it.*

**It is `d = 1` only.** `torusGraph d n` for `d ≥ 2` is a product of cycles, and Mathlib's
`cycleGraph` is one cycle. Nothing here says anything about `d ≥ 2`, which is where the estate's
reflection-positivity work actually lives.

**`n = 0` is excluded by statement, not by oversight.** `cycleGraph 0` is `⊥` on an empty type and
`circulantGraph` needs an `AddGroup`, which `Fin 0` has not; everything here is stated at `n + 1`.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusCycleGraph

open TorusReflection SimpleGraph

variable {n : ℕ}

/-! ## 1. The wrap, which is the whole of the arithmetic -/

/-- **THE ARITHMETIC CORE.** In `Fin (n+1)`, `a - b = 1` exactly when `b` is one step below `a`,
either in the ordinary way or across the wrap.

`Fin` subtraction is arithmetic modulo `n+1` and `omega` cannot see through the `%`. What supplies
the two branches is `Fin.val_add_one`, whose own statement is a case split on `b = Fin.last n` —
so the wrap is handled by the library lemma rather than by hand. -/
theorem sub_one_iff (a b : Fin (n + 1)) :
    a - b = 1 ↔ (b.val + 1 = a.val ∨ (a.val = 0 ∧ b.val + 1 = n + 1)) := by
  rw [sub_eq_iff_eq_add, add_comm (1 : Fin (n + 1)) b]
  rw [Fin.ext_iff, Fin.val_add_one]
  by_cases hb : b = Fin.last n
  · subst hb
    simp only [Fin.val_last]
    have ha := a.isLt
    constructor
    · intro h; exact Or.inr ⟨h, trivial⟩
    · rintro (h | ⟨h, -⟩)
      · omega
      · exact h
  · simp only [if_neg hb]
    have hblt : b.val + 1 < n + 1 := by
      have : b.val ≠ n := by
        intro h; exact hb (Fin.ext (by simp [h]))
      omega
    constructor
    · intro h; exact Or.inl h.symm
    · rintro (h | ⟨-, h⟩)
      · exact h.symm
      · omega

/-! ## 2. The two adjacency relations agree -/

/-- **THE ESTATE'S `adjT` IS MATHLIB'S CYCLE ADJACENCY.** -/
theorem adjT_iff_cycleGraph (a b : Fin (n + 1)) :
    adjT a b ↔ (cycleGraph (n + 1)).Adj a b := by
  have hsub : ∀ x y : Fin (n + 1),
      x - y = 1 ↔ (y.val + 1 = x.val ∨ (x.val = 0 ∧ y.val + 1 = n + 1)) := sub_one_iff
  simp only [cycleGraph, circulantGraph, SimpleGraph.fromRel_adj, Set.mem_singleton_iff,
    adjT, hsub]
  tauto

/-! ## 3. The isomorphism -/

/-- `Site 1 n` is `Fin n`, by evaluation at the unique axis. -/
def siteEquiv (n : ℕ) : BoxGraph.Site 1 n ≃ Fin n := Equiv.funUnique (Fin 1) (Fin n)

/-- **THE ONE-DIMENSIONAL TORUS IS MATHLIB'S CYCLE GRAPH.** -/
def torusGraph_one_iso (n : ℕ) :
    torusGraph 1 (n + 1) ≃g SimpleGraph.cycleGraph (n + 1) where
  toEquiv := siteEquiv (n + 1)
  map_rel_iff' := by
    intro p q
    simp only [siteEquiv, Equiv.funUnique_apply]
    rw [torusGraph_adj, ← adjT_iff_cycleGraph]
    constructor
    · intro h
      exact ⟨0, fun j hj => absurd (Subsingleton.elim j 0) hj, h⟩
    · rintro ⟨i, -, h⟩
      rwa [Subsingleton.elim i 0] at h

end TorusCycleGraph
