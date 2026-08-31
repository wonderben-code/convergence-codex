import GraphIsoSpectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Laplacian eigenvectors transport along a graph isomorphism

`GraphIsoSpectrum` carried an **adjacency** eigenvector across a graph isomorphism, and that is what
`BoxGraphSuccIso` needed to reach `BoxGraph.boxGraph` from `SimpleGraph.boxProd`. `PathLapSpectrum`
and `BoxProdLapSpectrum` have now put the **Laplacian** in the same position — exact modes on the
path, eigenvalues adding across the product — and the same transport is missing for it.
`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* `STATUS (16)` names it as step (3)'s prerequisite.

> **`lapMatrix_mulVec_comp_symm`** — the Laplacian action commutes with relabelling.
>
> **`lapMatrix_mulVec_smul_iso`** — hence an eigenvector transports, **with the same eigenvalue**.

## Why it is not just `GraphIsoSpectrum` again

The adjacency version needed one fact: the neighbourhoods correspond. The Laplacian needs a second,
the **degrees** — and `SimpleGraph.Iso.degree_eq` supplies it and is **instance-polymorphic**, so it
applies to whatever `Fintype (neighborSet _)` the goal happens to hold. That is the same property
that made `SimpleGraph.degree_boxProd` the right tool in `BoxProdLapSpectrum` rather than a
hand-written lemma (`ERRATUM 384`), and it is why this file is short.

**Probed 31 August 2026, and for the concept rather than one spelling** (`ERRATUM 384`'s rule):
names pairing `lapMatrix` with `iso`, `congr` or `map` are `lapMatrix.congr_simp`,
`lapMatrix_toLinearMap₂'` and its two `_eq_zero_iff` variants — **none of them a transport**. Names
pairing `SimpleGraph.Iso` with `degree` are `degree_eq`, `minDegree_eq`, `maxDegree_eq`; the first
is used here.

## What this is NOT

**It computes no spectrum — it moves one**, and says nothing about which graphs are isomorphic.

**It is not the box.** `BoxGraph.boxGraph d n`'s Laplacian spectrum needs this **plus**
`BoxGraphSuccIso.boxGraph_succ_iso`, `BoxProdLapSpectrum.lapMatrix_mulVec_prodVec`,
`PathLapSpectrum.lapMatrix_mulVec_cosMode` and an induction on `d`. **The induction is not written
here** and as of 31 Aug 2026 is not costed (`ERRATUM 194`, `ERRATUM 246`).

**It is not `massive`**: the `+ m²` shift is not stated.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace GraphIsoLapSpectrum

open Finset Matrix SimpleGraph

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- **`L_H · (v ∘ e.symm) = (L_G · v) ∘ e.symm`.** The neighbour sum transports by
`GraphIsoSpectrum.sum_neighborFinset_iso`; the degree by `SimpleGraph.Iso.degree_eq`. -/
theorem lapMatrix_mulVec_comp_symm (e : G ≃g H) (v : V → ℝ) :
    H.lapMatrix ℝ *ᵥ (fun w => v (e.symm w)) = fun w => (G.lapMatrix ℝ *ᵥ v) (e.symm w) := by
  funext w
  obtain ⟨a, rfl⟩ : ∃ a, e a = w := ⟨e.symm w, e.right_inv w⟩
  have hinv : ∀ b : V, e.symm (e b) = b := fun b => e.left_inv b
  rw [hinv a]
  rw [SimpleGraph.lapMatrix_mulVec_apply, SimpleGraph.lapMatrix_mulVec_apply,
    GraphIsoSpectrum.sum_neighborFinset_iso e (fun w => v (e.symm w)) a,
    SimpleGraph.Iso.degree_eq e a]
  simp only [hinv]

/-- **AN EIGENVECTOR OF THE LAPLACIAN TRANSPORTS, AND THE EIGENVALUE DOES NOT MOVE.** -/
theorem lapMatrix_mulVec_smul_iso (e : G ≃g H) {v : V → ℝ} {c : ℝ}
    (hv : G.lapMatrix ℝ *ᵥ v = c • v) :
    H.lapMatrix ℝ *ᵥ (fun w => v (e.symm w)) = c • fun w => v (e.symm w) := by
  rw [lapMatrix_mulVec_comp_symm e v, hv]
  rfl

end GraphIsoLapSpectrum
