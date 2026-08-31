import BoxGraph
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# The estate's box graph, in Mathlib's vocabulary: a box product of path graphs

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item records what would be needed to reach the box
graph's spectrum — *"the one-dimensional path's Dirichlet Laplacian has sine eigenvectors rather
than exponential ones, and the `d`-dimensional box is a tensor product of paths"* — and says of
both facts that **neither is formalised here and neither is probed**. This file probes, and proves
the first half of the object identification.

> **`boxGraph_adj_pathGraph`** — `(boxGraph d n).Adj p q` **iff** the two sites agree off one axis
> and are `pathGraph n`-adjacent on it. `SimpleGraph.pathGraph_adj` is *literally* the estate's
> per-coordinate condition, `u.val + 1 = v.val ∨ v.val + 1 = u.val`, so this is the estate's box
> named as the `d`-fold box product of paths.
>
> **`boxGraph_one_iso_pathGraph`** — and at `d = 1` it **is** a path graph, as a
> `SimpleGraph.Iso`.

## The probe the item asked for, run 31 August 2026

Against the pinned dump (`env_names.txt`, 471478 constants):

* `SimpleGraph.pathGraph` **present**, 10 names — and **no spectrum**: names pairing
  `pathGraph` or `cycleGraph` with `eigen` or `spectr` are **0**.
* `SimpleGraph.boxProd` **present** — Mathlib has the box product of graphs, binary, on `α × β` —
  and again **no spectrum**.
* `Matrix.tridiagonal`, `tridiagonal`: **0 each.** Mathlib has no tridiagonal-matrix API at all,
  which is the shape the path's Laplacian has.
* `dirichletLaplacian`: **0**. `Dirichlet` matches 164 names and **every one is a Dirichlet
  character or L-series**; none is an operator.
* `Matrix.kronecker` present, and **nothing pairs it with eigenvalues**.

**So the item's assessment stands and is now evidenced rather than assumed** (`ERRATUM 42`): the
objects exist and the spectral theory does not, in Mathlib or here.

## What this does NOT do

**It computes no eigenvalue.** The two facts the item names — the path's Dirichlet spectrum, and
the spectrum of a box product — are **both still absent**, and this file supplies neither. What it
supplies is that the estate's `boxGraph` is the object those theorems would be about, so a later
unit can state them in Mathlib's vocabulary instead of the estate's. **No cost is offered for
either** (`ERRATUM 194`, `ERRATUM 246`).

**It does not exhibit `boxGraph d n` as an iterated `SimpleGraph.boxProd`.** `boxProd` is binary on
`α × β` and `Site d n` is a function type; the transport needs
`(Fin (d + 1) → Fin n) ≃ Fin n × (Fin d → Fin n)` and an induction, and is not done here.
-/

namespace BoxGraphPath

open SimpleGraph BoxGraph

variable {d n : ℕ}

/-- **THE ESTATE'S BOX IS A BOX PRODUCT OF PATHS.** Two sites are adjacent exactly when they agree
off one axis and are `pathGraph`-adjacent on it. -/
theorem boxGraph_adj_pathGraph (p q : Site d n) :
    (boxGraph d n).Adj p q ↔
      ∃ i : Fin d, (∀ j, j ≠ i → p j = q j) ∧ (pathGraph n).Adj (p i) (q i) := by
  rw [boxGraph_adj]
  unfold BoxGraph.adj
  constructor
  · rintro ⟨i, hj, hi⟩
    exact ⟨i, hj, pathGraph_adj.2 hi⟩
  · rintro ⟨i, hj, hi⟩
    exact ⟨i, hj, pathGraph_adj.1 hi⟩

/-- At one dimension the single axis is forced, so adjacency is the path's. -/
theorem boxGraph_one_adj (p q : Site 1 n) :
    (boxGraph 1 n).Adj p q ↔ (pathGraph n).Adj (p 0) (q 0) := by
  rw [boxGraph_adj_pathGraph]
  constructor
  · rintro ⟨i, -, hi⟩
    have hz : i = 0 := Subsingleton.elim _ _
    subst hz
    exact hi
  · intro h
    exact ⟨0, fun j hj => absurd (Subsingleton.elim j 0) hj, h⟩

/-- **AND AT ONE DIMENSION IT IS A PATH GRAPH.** -/
def boxGraph_one_iso_pathGraph (n : ℕ) : boxGraph 1 n ≃g pathGraph n where
  toEquiv :=
    { toFun := fun p => p 0
      invFun := fun v => fun _ => v
      left_inv := fun p => by funext j; exact congrArg p (Subsingleton.elim 0 j)
      right_inv := fun _ => rfl }
  map_rel_iff' := (boxGraph_one_adj _ _).symm

end BoxGraphPath
