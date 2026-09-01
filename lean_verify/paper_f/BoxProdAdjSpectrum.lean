import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Eigenvalues add across a box product

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item names two facts a box spectrum would need.
`PathAdjSpectrum` and `PathAdjBasis` supplied the first — the path's sine eigenvectors, and that
they are a basis. This file supplies the second, which `BoxGraphPath`'s probe found **absent from
Mathlib**: nothing there pairs `boxProd` with `eigen` or `spectr`, and `Matrix.kronecker` is
present with nothing joining it to eigenvalues.

> **`neighborFinset_boxProd`** — a vertex of `G □ H` has, as neighbours, its `G`-neighbours at the
> same second coordinate together with its `H`-neighbours at the same first, and the two families
> are **disjoint** because a graph has no loops.
>
> **`prodVec`** — the pointwise product `u ⊗ v`, `(a, b) ↦ u a · v b`.
>
> **`adjMatrix_mulVec_prodVec`** — **eigenvalues add**: if `A_G u = c · u` and `A_H v = e · v`
> then `A_{G □ H} (u ⊗ v) = (c + e) · (u ⊗ v)`.

**Why it is this short.** The neighbour sum splits along the two families, each half factors
because one coordinate is held fixed, and what is left is the two hypotheses. No Kronecker product
is formed and no tensor algebra is used — the box product's adjacency is already a disjunction, and
`Finset.sum_union` on a disjoint pair is the whole argument.

## What this is NOT

**It is not a basis for the product**, and so not the product's whole spectrum: that the `|α|·|β|`
products of basis eigenvectors are independent is **not proved here**, and no cost is offered
(`ERRATUM 194`, `ERRATUM 246`).

**It is still the ADJACENCY matrix.** The estate's `GraphLaplacian.massive` is `D − A + m²` with
the true degree, and the degree of a box product is the sum of the two degrees — which is constant
only if both are. On a product of **paths** it is not, which is exactly what
`UNLOCK_WATCHLIST`'s box item says, and **that item does not move**. As of 31 August 2026 nothing
here reaches `massive`.

**Nothing connects it to `BoxGraph`.** `BoxGraphPath.boxGraph_adj_pathGraph` names the estate's box
as a `d`-fold product of paths on a **function type**, and this is the binary product on `α × β`;
the transport needs `(Fin (d + 1) → Fin n) ≃ Fin n × (Fin d → Fin n)` and an induction, still not
done.

## SIMPLIFIED 1 SEPTEMBER 2026 — the `Finset.filter` workaround is gone, and `ERRATUM 384` said to
test this rather than inherit it

The first draft stated everything through `Finset.filter` and bridged with
`SimpleGraph.neighborFinset_eq_filter`, because the product carries **two** competing `Fintype`
instances on its neighbour set and a `rw` between them does not match. That is a real trap and the
original note about it was accurate. **It is also unnecessary**, and `ERRATUM 384` — which found
`SimpleGraph.degree_boxProd` and `SimpleGraph.neighborFinset_boxProd` after this file had already
worked around their absence — named testing it here as a loose end for the next sweep. This is that
test, and it passes.

**`SimpleGraph.neighborFinset_boxProd` carries all three `Fintype (neighborSet _)` instances as
ARGUMENTS**, so it applies to whichever instance the goal happens to hold; there is nothing to
bridge. It also returns a `Finset.disjUnion` rather than a union, which retires the disjointness
lemma too. Two theorems — `filter_boxProd_adj` and `disjoint_boxProd_families`, used by nothing
outside this file, checked before deletion — are removed, and the file goes from 111 lines and
five declarations to 87 and three. The proof is now `Finset.sum_disjUnion`, two
`Finset.sum_product`s and one `linear_combination`, which is `BoxProdLapSpectrum`'s shape exactly.

**`boxProdDecidableAdj` STAYS, AND THAT WAS TESTED BY REMOVING IT.** Deleting it fails the build at
`adjMatrix_mulVec_prodVec` with *"failed to synthesize `DecidableRel (G □ H).Adj`"*. It is a
different need from the one the workaround addressed: **`SimpleGraph.adjMatrix`** cannot be formed
at all without decidable adjacency, whereas the friction the filters dodged was about which
`Fintype` the neighbour **set** carries. The two were adjacent in the original file and are not the
same problem.

**That name was `Matrix.adjMatrix` in the first draft of this note and it does not exist** — the
function is `SimpleGraph.adjMatrix`, probed 1 September, and the wrong spelling is kept here beside
the right one (`ERRATUM 94`, `ERRATUM 108`) because this file `open`s **both** `Matrix` and
`SimpleGraph` and a reader will guess the same way. It is the **fifth** guessed spelling of the
campaign and the second of exactly this shape, after `Matrix.dotProduct` for root-level
`dotProduct` earlier the same day; `--cites-lean` caught both. `ERRATUM 384`'s tally is extended in
its addendum.

**No statement changed.** `prodVec` and `adjMatrix_mulVec_prodVec` keep their signatures, which is
what lets the five files that consume them rebuild untouched.
-/

namespace BoxProdAdjSpectrum

open Finset Matrix SimpleGraph

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {G : SimpleGraph α} {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]

instance boxProdDecidableAdj : DecidableRel (G □ H).Adj := fun _ _ => by
  rw [boxProd_adj]; infer_instance

/-! ## 2. The product vector -/

/-- The pointwise product of a vector on `α` with one on `β`. -/
def prodVec (u : α → ℝ) (v : β → ℝ) : α × β → ℝ := fun p => u p.1 * v p.2

/-! ## 3. Eigenvalues add -/

/-- **EIGENVALUES ADD ACROSS A BOX PRODUCT.** -/
theorem adjMatrix_mulVec_prodVec {u : α → ℝ} {v : β → ℝ} {c e : ℝ}
    (hu : G.adjMatrix ℝ *ᵥ u = c • u) (hv : H.adjMatrix ℝ *ᵥ v = e • v) :
    (G □ H).adjMatrix ℝ *ᵥ prodVec u v = (c + e) • prodVec u v := by
  classical
  have hu' : ∀ a, ∑ a' ∈ G.neighborFinset a, u a' = c * u a := by
    intro a
    have h := congrFun hu a
    rw [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hv' : ∀ b, ∑ b' ∈ H.neighborFinset b, v b' = e * v b := by
    intro b
    have h := congrFun hv b
    rw [adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  funext p
  obtain ⟨a, b⟩ := p
  rw [adjMatrix_mulVec_apply, SimpleGraph.neighborFinset_boxProd, Finset.sum_disjUnion,
    Finset.sum_product, Finset.sum_product]
  simp only [prodVec, Finset.sum_singleton, ← Finset.sum_mul, ← Finset.mul_sum,
    Pi.smul_apply, smul_eq_mul]
  linear_combination (v b) * hu' a + (u a) * hv' b

end BoxProdAdjSpectrum
