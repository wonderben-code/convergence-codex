import TorusReflection

/-!
# Is there a site map from the torus at side `n` into the torus at side `2n`?

`UNLOCK_WATCHLIST`'s infinite-volume item opens by saying that **no embedding of `torusGraph d n`
into `torusGraph d (2n)`** exists, and `ASSUMPTIONS_LEDGER` entry 47 — written yesterday — offered
that as the *weaker, already-defensible* reading of the item's stronger claim about covariances,
adding that it **"needs no new mathematics and may be what was always meant"**.

**That sentence was prose, and this file checks it. It is not simply true.**

## What is actually the case, at the two side lengths a decision procedure reaches

* **`no_embedding_three_into_six`** — at `d = 1`, `n = 3`, there is **no** injective graph
  homomorphism `torusGraph 1 3 → torusGraph 1 6`. The obstruction is real.
* **`embedding_two_into_four`** — at `d = 1`, `n = 2`, there **is** one. So the claim as stated —
  no embedding, full stop — is false at the smallest side length.

Both are settled by `decide`, so neither is an argument that can be misread.

**And the exception is not an accident: the estate already knows why.**
`TorusReflection.torus_two_eq_box` proves `torusGraph d 2 = boxGraph d 2` — at side `2` the torus
*is* the box, because the wrap-around edge and the ordinary edge coincide. `n = 2` is the degenerate
side length, named as such by an existing theorem rather than explained here.

**This matters for the item because the item's own machinery runs on EVEN `n`** —
`reflectionPositive_torus` takes `Even n` — and `2` is even. So the one even side length reachable
by decision is the one where the embedding exists.

## What this does NOT settle, stated precisely

**It does not prove the item's claim, and it does not refute it.** Two side lengths are not a
theorem about all of them. The general statement — no injective graph homomorphism
`torusGraph 1 n → torusGraph 1 (2n)` for `n ≥ 3` — is **not proved here**. It is believable for the
usual reason (a homomorphic image of an `n`-cycle that is injective is an `n`-cycle subgraph, and a
`2n`-cycle contains none for `n ≥ 3`), and that reason is **an argument in prose, exactly the kind
this file exists to distrust**.

**`n = 4` was attempted and the decision procedure overflowed the stack.** That is a **resource
limit and is evidence for nothing**: it says the kernel ran out of room, not that a map does or does
not exist. Recorded so that no later reader mistakes a failed computation for a negative result.

**It says nothing about covariances.** The strong claim — that the torus covariances are
incompatible — is `ASSUMPTIONS_LEDGER` entry 47, remains an author's decision about what
*compatible* should mean, and is untouched by anything here. **A missing graph embedding is not
an incompatible family**: compatibility could be posed along a map that is not a graph homomorphism
at all.

**`OS4` does not move.** No sequence of measures, no limit, no compactness, no tightness.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusEmbedding

open TorusReflection

/-- A site map that is a graph homomorphism and injective — the weakest thing that deserves to be
called *an embedding of the small torus into the large one*, and the object the watchlist item says
does not exist. -/
def IsSiteEmbedding {m n : ℕ} (φ : BoxGraph.Site 1 m → BoxGraph.Site 1 n) : Prop :=
  Function.Injective φ ∧
    ∀ p q, (torusGraph 1 m).Adj p q → (torusGraph 1 n).Adj (φ p) (φ q)

instance {m n : ℕ} (φ : BoxGraph.Site 1 m → BoxGraph.Site 1 n) :
    Decidable (IsSiteEmbedding φ) := by
  unfold IsSiteEmbedding; infer_instance

set_option maxRecDepth 100000 in
/-- **AT SIDE `3` THERE IS NO SUCH MAP.** Decided, not argued. -/
theorem no_embedding_three_into_six :
    ¬ ∃ φ : BoxGraph.Site 1 3 → BoxGraph.Site 1 6, IsSiteEmbedding φ := by
  decide

set_option maxRecDepth 100000 in
/-- **AT SIDE `2` THERE IS ONE**, so "no embedding of `torusGraph d n` into `torusGraph d (2n)`" is
false as a blanket statement — and `2` is even, which is the parity the torus reflection machinery
requires (`TorusReflection.reflectionPositive_torus` takes `Even n`). -/
theorem embedding_two_into_four :
    ∃ φ : BoxGraph.Site 1 2 → BoxGraph.Site 1 4, IsSiteEmbedding φ := by
  decide

/-- **AND THE EXCEPTION IS THE KNOWN DEGENERATE SIDE LENGTH.** `TorusReflection.torus_two_eq_box`
already proves the torus at side `2` *is* the box — the wrap edge and the ordinary edge coincide —
so `embedding_two_into_four` is a fact about a graph the estate has always known collapses, not a
new pathology. Restated here so the two theorems above are read together. -/
theorem torus_two_is_box (d : ℕ) : torusGraph d 2 = BoxGraph.boxGraph d 2 :=
  torus_two_eq_box d

end TorusEmbedding
