import BoxProdAdjSpectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic.LinearCombination

/-!
# The Laplacian's eigenvalues add across a box product, degrees and all

`BoxProdAdjSpectrum` proved that eigenvalues add across `SimpleGraph.boxProd` **for the adjacency
matrix**, and every unit built on it carried the fence *"the estate's operator is `D − A + m²` with
the true degree, and a product's degree is the sum of the two degrees — constant only if both
are"*. `PathLapSpectrum` then showed the path's **free-boundary Laplacian** has exact eigenvectors
after all, so the missing piece is no longer the path: it is this.

> **`lapMatrix_mulVec_prodVec`** — **eigenvalues add for the Laplacian too**: if `L_G u = c·u` and
> `L_H v = e·v` then `L_{G □ H} (u ⊗ v) = (c + e)·(u ⊗ v)`.

## Why the degrees are not an obstacle here

The non-constant degree is what stops a **character** argument, and it is not what stops the
**sum**. Writing `L = D − A`, the diagonal splits as `deg_G a + deg_H b` and the neighbour set
splits into the same two families; pairing the `deg_G a` with the `G`-family and the `deg_H b` with
the `H`-family leaves exactly `(L_G u)(a)·v b + u a·(L_H v)(b)`. The degrees cancel **against their
own halves**, which is why nothing here needs them constant, and why the whole proof is one
`linear_combination` once the sum is split.

## Both halves of the split are MATHLIB'S, and the first draft of this file did not know that

`SimpleGraph.degree_boxProd` and `SimpleGraph.neighborFinset_boxProd` are both in the pinned tree,
and both are **instance-polymorphic** — they carry the three `Fintype (neighborSet _)` instances as
arguments, so they apply to whatever instance the goal happens to hold. That matters here:
`BoxProdAdjSpectrum` records that the product has **two** competing such instances and works around
them by restating everything with `Finset.filter`. **Mathlib's lemmas need no such workaround**, and
this file uses them directly.

The first draft proved the degree split by hand and claimed in this header that Mathlib had it not.
**That claim was false and the probe behind it was wrong**: it searched `boxProd_degree`, and the
name is `degree_boxProd`. Recorded rather than quietly fixed (`ERRATUM 42`, `ERRATUM 378`) — the
lemma written by hand was **deleted**, not kept beside Mathlib's.

## What this is NOT

**It is not the box.** `BoxGraph.boxGraph d n` is not treated here; that needs
`BoxGraphSuccIso.boxGraph_succ_iso`, an analogue of `GraphIsoSpectrum.mulVec_smul_iso` for
`lapMatrix`, and an induction on `d`. **None of the three is written here** and as of 31 Aug 2026
none is costed (`ERRATUM 194`, `ERRATUM 246`).

**It is not `massive`.** `GraphLaplacian.massive` is `L + m²`, and the `+ m²` shift is not stated.

**It is not a basis.** Independence of the products is `ProdVecIndependent`'s subject, and nothing
is drawn from it here.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxProdLapSpectrum

open Finset Matrix SimpleGraph BoxProdAdjSpectrum

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  {G : SimpleGraph α} {H : SimpleGraph β} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **EIGENVALUES ADD ACROSS A BOX PRODUCT, FOR THE LAPLACIAN.** -/
theorem lapMatrix_mulVec_prodVec {u : α → ℝ} {v : β → ℝ} {c e : ℝ}
    (hu : G.lapMatrix ℝ *ᵥ u = c • u) (hv : H.lapMatrix ℝ *ᵥ v = e • v) :
    (G □ H).lapMatrix ℝ *ᵥ prodVec u v = (c + e) • prodVec u v := by
  classical
  have hu' : ∀ a, (G.degree a : ℝ) * u a - ∑ a' ∈ G.neighborFinset a, u a' = c * u a := by
    intro a
    have h := congrFun hu a
    rw [SimpleGraph.lapMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hv' : ∀ b, (H.degree b : ℝ) * v b - ∑ b' ∈ H.neighborFinset b, v b' = e * v b := by
    intro b
    have h := congrFun hv b
    rw [SimpleGraph.lapMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  funext p
  obtain ⟨a, b⟩ := p
  rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.degree_boxProd,
    SimpleGraph.neighborFinset_boxProd, Finset.sum_disjUnion, Finset.sum_product,
    Finset.sum_product]
  simp only [prodVec, Finset.sum_singleton, ← Finset.sum_mul, ← Finset.mul_sum,
    Pi.smul_apply, smul_eq_mul, Nat.cast_add]
  linear_combination (v b) * hu' a + (u a) * hv' b

end BoxProdLapSpectrum
