import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Data.Real.Basic

/-!
# Eigenvectors transport along a graph isomorphism

Every route from a small graph's spectrum to a large one's goes through an isomorphism: the estate's
`BoxGraph.boxGraph` lives on a **function type**, Mathlib's `SimpleGraph.boxProd` on a **pair
type**,
and `PathAdjSpectrum` computes on `SimpleGraph.pathGraph`. **Nothing carries a spectral statement
across an isomorphism**, in Mathlib or here: names pairing `SimpleGraph.Iso` or
`SimpleGraph.Embedding` with `adjMatrix` are **0** in the pinned dump, probed
31 August 2026.

> **`sum_neighborFinset_iso`** — an isomorphism matches neighbourhoods, so a sum over the
> neighbours of `e a` in `H` is the sum over the neighbours of `a` in `G` of the transported
> summand.
>
> **`adjMatrix_mulVec_comp_symm`** — hence `A_H *ᵥ (v ∘ e.symm) = (A_G *ᵥ v) ∘ e.symm`: the
> adjacency action commutes with relabelling.
>
> **`hasEigenvector_iso`** — so an eigenvector of `A_G` with eigenvalue `c` becomes one of `A_H`
> with the **same** eigenvalue, and a basis of eigenvectors transports to a basis.

**Why it is not merely `Matrix.submatrix`.** It is that, and saying so is the proof; what is absent
is the statement, and without it every use of a graph isomorphism in a spectral argument has to
re-derive the neighbourhood bijection by hand. `SimpleGraph.Iso.mapNeighborSet` is the set-level
fact and stops there.

## What this is NOT

**It computes no spectrum.** It moves one, and it says nothing about which graphs are isomorphic.
The estate's `boxGraph d n` is **not** exhibited here as an iterated `boxProd` — that transport
needs `Fin.consEquiv` and an induction on `d`, and is not done. No cost is offered
(`ERRATUM 194`, `ERRATUM 246`).
-/

namespace GraphIsoSpectrum

open Finset Matrix SimpleGraph

-- `DecidableEq` on the vertex types is not needed by anything below and was removed rather
-- than underscored; `comp_symm_ne_zero` needs none of the graph structure either.
variable {V W : Type*} [Fintype V] [Fintype W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-! ## 1. An isomorphism matches neighbourhoods -/

/-- **THE NEIGHBOUR SUM TRANSPORTS.** -/
theorem sum_neighborFinset_iso (e : G ≃g H) (w : W → ℝ) (a : V) :
    ∑ b ∈ H.neighborFinset (e a), w b = ∑ b ∈ G.neighborFinset a, w (e b) := by
  classical
  refine (Finset.sum_nbij' (fun b => e b) (fun b => e.symm b) ?_ ?_ ?_ ?_ ?_).symm
  · intro b hb
    simp only [mem_neighborFinset] at hb ⊢
    exact (e.map_adj_iff).2 hb
  · intro b hb
    simp only [mem_neighborFinset] at hb ⊢
    have := (e.symm.map_adj_iff (v := e a) (w := b)).2 hb
    simpa using this
  · intro b _; exact e.left_inv b
  · intro b _; exact e.right_inv b
  · intro b _; rfl

/-! ## 2. So the adjacency action commutes with relabelling -/

/-- **`A_H *ᵥ (v ∘ e.symm) = (A_G *ᵥ v) ∘ e.symm`.** -/
theorem adjMatrix_mulVec_comp_symm (e : G ≃g H) (v : V → ℝ) :
    H.adjMatrix ℝ *ᵥ (fun w => v (e.symm w)) = fun w => (G.adjMatrix ℝ *ᵥ v) (e.symm w) := by
  funext w
  obtain ⟨a, rfl⟩ : ∃ a, e a = w := ⟨e.symm w, e.right_inv w⟩
  have hinv : ∀ b : V, e.symm (e b) = b := fun b => e.left_inv b
  rw [adjMatrix_mulVec_apply, adjMatrix_mulVec_apply,
    sum_neighborFinset_iso e (fun w => v (e.symm w)) a]
  simp only [hinv]
  exact Finset.sum_congr (by rw [hinv]) fun _ _ => rfl

/-! ## 3. Hence eigenvectors, with the same eigenvalue -/

/-- **AN EIGENVECTOR TRANSPORTS, AND THE EIGENVALUE DOES NOT MOVE.** -/
theorem mulVec_smul_iso (e : G ≃g H) {v : V → ℝ} {c : ℝ}
    (hv : G.adjMatrix ℝ *ᵥ v = c • v) :
    H.adjMatrix ℝ *ᵥ (fun w => v (e.symm w)) = c • fun w => v (e.symm w) := by
  rw [adjMatrix_mulVec_comp_symm e v, hv]
  rfl

omit [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel H.Adj] in
/-- **AND A NONZERO EIGENVECTOR STAYS NONZERO.** -/
theorem comp_symm_ne_zero (e : G ≃g H) {v : V → ℝ} (hv : v ≠ 0) :
    (fun w => v (e.symm w)) ≠ 0 := by
  intro hcon
  apply hv
  funext a
  have := congrFun hcon (e a)
  simpa [e.left_inv] using this

end GraphIsoSpectrum
