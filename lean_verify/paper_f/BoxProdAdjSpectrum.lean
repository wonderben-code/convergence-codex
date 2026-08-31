import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Data.Real.Basic

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
-/

namespace BoxProdAdjSpectrum

open Finset Matrix SimpleGraph

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {G : SimpleGraph α} {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]

instance boxProdDecidableAdj : DecidableRel (G □ H).Adj := fun _ _ => by
  rw [boxProd_adj]; infer_instance

/-! ## 1. The neighbours of a vertex of the product -/

/-- **THE TWO FAMILIES, AND THEY ARE DISJOINT** — a `G`-neighbour differs in the first coordinate
and an `H`-neighbour agrees there, and a graph has no loops. Stated with `Finset.filter` rather
than `neighborFinset`, because the product carries **two** competing `Fintype` instances on its
neighbour set — Mathlib's `boxProdFintypeNeighborSet` and the one derived from `DecidableRel` —
and a `rw` between them does not match. `SimpleGraph.neighborFinset_eq_filter` is the bridge. -/
theorem filter_boxProd_adj (a : α) (b : β) :
    univ.filter ((G □ H).Adj (a, b))
      = (univ.filter (G.Adj a) ×ˢ ({b} : Finset β))
        ∪ (({a} : Finset α) ×ˢ univ.filter (H.Adj b)) := by
  ext p
  obtain ⟨a', b'⟩ := p
  simp only [mem_filter, mem_univ, true_and, boxProd_adj, mem_union, mem_product, mem_singleton]
  tauto

omit [DecidableEq α] [DecidableEq β] in
theorem disjoint_boxProd_families (a : α) (b : β) :
    Disjoint (univ.filter (G.Adj a) ×ˢ ({b} : Finset β))
      (({a} : Finset α) ×ˢ univ.filter (H.Adj b)) := by
  refine Finset.disjoint_left.2 ?_
  rintro ⟨a', b'⟩ h1 h2
  simp only [mem_product, mem_singleton, mem_filter, mem_univ, true_and] at h1 h2
  exact (G.ne_of_adj h1.1) h2.1.symm

/-! ## 2. The product vector -/

/-- The pointwise product of a vector on `α` with one on `β`. -/
def prodVec (u : α → ℝ) (v : β → ℝ) : α × β → ℝ := fun p => u p.1 * v p.2

/-! ## 3. Eigenvalues add -/

/-- **EIGENVALUES ADD ACROSS A BOX PRODUCT.** -/
theorem adjMatrix_mulVec_prodVec {u : α → ℝ} {v : β → ℝ} {c e : ℝ}
    (hu : G.adjMatrix ℝ *ᵥ u = c • u) (hv : H.adjMatrix ℝ *ᵥ v = e • v) :
    (G □ H).adjMatrix ℝ *ᵥ prodVec u v = (c + e) • prodVec u v := by
  have hu' : ∀ a, ∑ a' ∈ univ.filter (G.Adj a), u a' = c * u a := by
    intro a
    have h := congrFun hu a
    rw [adjMatrix_mulVec_apply, neighborFinset_eq_filter, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hv' : ∀ b, ∑ b' ∈ univ.filter (H.Adj b), v b' = e * v b := by
    intro b
    have h := congrFun hv b
    rw [adjMatrix_mulVec_apply, neighborFinset_eq_filter, Pi.smul_apply, smul_eq_mul] at h
    exact h
  funext p
  obtain ⟨a, b⟩ := p
  rw [adjMatrix_mulVec_apply, neighborFinset_eq_filter, filter_boxProd_adj,
    Finset.sum_union (disjoint_boxProd_families a b), Finset.sum_product, Finset.sum_product]
  simp only [prodVec, Finset.sum_singleton, ← Finset.sum_mul, ← Finset.mul_sum]
  rw [hu' a, hv' b]
  simp only [Pi.smul_apply, smul_eq_mul, prodVec]
  ring

end BoxProdAdjSpectrum
