import BoxAdjSpectrum
import ProdVecIndependent

/-!
# The box's `n^d` adjacency modes are a basis

`BoxAdjSpectrum` produced one explicit eigenvector of `(boxGraph d n).adjMatrix ℝ` per frequency
vector and fenced on the single question that would make them the **whole** spectrum: are they
independent? It also recorded why the cheap answer is unavailable —
`PathAdjBasis.pathVec_linearIndependent` gets independence from
`Module.End.eigenvectors_linearIndependent'` **because the path's eigenvalues are distinct**, and
in two or more dimensions they are not, since `(1, 2)` and `(2, 1)` give the same sum of cosines.
`ProdVecIndependent` then supplied the replacement as pure linear algebra and closed by saying the
dimension induction *"is not written"*. **This writes it.**

> **`boxVec_linearIndependent`** — the `n^d` vectors `boxVec d n (fun i => kᵢ + 1)`, one per
> `k : Site d n`, are linearly independent in `Site d n → ℝ`.
>
> **`boxBasis`** — hence they are a **basis**, indexed by the box's own site type.
>
> **`boxBasis_apply`** — and the basis vector at `k` is the mode it was built from, so the basis
> can be used without unfolding it.

## The induction

One axis at a time, the same shape as `BoxAdjSpectrum`'s. At `d = 0` the box has a single site and
the single mode is the constant `1`, nonzero, so `linearIndependent_unique` applies. At `d + 1`,
`PathAdjBasis.pathVec_linearIndependent` gives the new axis's `n` modes,
`ProdVecIndependent.prodVec_linearIndependent` multiplies them against the inductive hypothesis,
and the family is carried onto the box twice over: `linearIndependent_comp_equiv` relabels the
**domain** along `BoxGraphSuccIso.consSite`, and `LinearIndependent.comp` relabels the **index**
along the same equivalence. Both relabellings are needed and they are different maps —
`Fin n × Site d n` is the domain of the vectors and also the index of the family, and only after
both is the statement about `Site (d + 1) n` on both sides.

## What this is NOT

**It does not yet say the spectrum is exactly the `boxEig`s.** That step —
*every* eigenvalue of the adjacency matrix is one of them — needs
`SignlessTorusComplete.eigenvalue_iff_of_basis`, which is stated **over `ℂ`**, and everything here
is over `ℝ`. **Generalising `eigenvalue_iff_of_basis` from `ℂ` to an arbitrary field — its argument
uses no property of `ℂ` beyond being one — is not done here, and as of 31 Aug 2026 no cost is
offered for it** (`ERRATUM 194`, `ERRATUM 246`). What is proved is that a basis exists and what its
vectors are.

**No orthogonality.** The modes are independent; whether they are orthogonal for the standard inner
product is neither needed for a basis nor proved, and as of 31 Aug 2026 nothing here addresses it.

**Still the adjacency matrix.** `UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item is blocked on
`GraphLaplacian.massive` = `D − A + m²` with the true degree, and `PathDegreeBoundary.
pathGraph_degree` shows that degree is not constant on a path. **That item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxAdjBasis

open Finset Matrix SimpleGraph BoxGraph BoxGraphSuccIso BoxAdjSpectrum PathAdjSpectrum

variable {d n : ℕ}

/-- The frequency vector a site indexes: coordinate `kᵢ` names the mode `kᵢ + 1`, so the `n`
frequencies used on each axis are `1 … n` — exactly `PathAdjBasis`'s range. -/
noncomputable def siteVec (d n : ℕ) (k : Site d n) : Site d n → ℝ :=
  boxVec d n fun i => (k i).val + 1

theorem siteVec_succ (d n : ℕ) (k : Site (d + 1) n) :
    siteVec (d + 1) n k
      = (BoxProdAdjSpectrum.prodVec (pathVec n ((k 0).val + 1)) (siteVec d n (Fin.tail k)))
          ∘ (consSite d n).symm := by
  funext p
  simp [siteVec, boxVec, BoxProdAdjSpectrum.prodVec, Fin.prod_univ_succ, Fin.tail]

/-! ## 1. Independence, by induction on the dimension -/

/-- **THE `n^d` MODES ARE INDEPENDENT.** -/
theorem siteVec_linearIndependent (n d : ℕ) : LinearIndependent ℝ (siteVec d n) := by
  induction d with
  | zero =>
      refine LinearIndependent.of_subsingleton (default : Site 0 n) ?_
      intro hcon
      have h := congrFun hcon (default : Site 0 n)
      simp [siteVec, boxVec] at h
  | succ d ih =>
      have hprod := ProdVecIndependent.prodVec_linearIndependent
        (PathAdjBasis.pathVec_linearIndependent n) ih
      have hdom := ProdVecIndependent.linearIndependent_comp_equiv
        (v := fun p : Fin n × Site d n =>
          BoxProdAdjSpectrum.prodVec (pathVec n (p.1.val + 1)) (siteVec d n p.2))
        (consSite d n).symm hprod
      have hidx := hdom.comp (consSite d n).symm (Equiv.injective _)
      have hfam : ((fun p : Fin n × Site d n =>
          BoxProdAdjSpectrum.prodVec (pathVec n (p.1.val + 1)) (siteVec d n p.2)
            ∘ (consSite d n).symm) ∘ (consSite d n).symm) = siteVec (d + 1) n := by
        funext k
        rw [siteVec_succ]
        exact rfl
      rwa [hfam] at hidx

/-! ## 2. So they are a basis -/

/-- **THE BOX'S MODES, AS A BASIS INDEXED BY THE BOX'S OWN SITES.** -/
noncomputable def boxBasis (d n : ℕ) [NeZero n] :
    Module.Basis (Site d n) ℝ (Site d n → ℝ) :=
  basisOfLinearIndependentOfCardEqFinrank (siteVec_linearIndependent n d) (by simp)

/-- The basis vector at `k` is the mode it was built from. -/
theorem boxBasis_apply (d n : ℕ) [NeZero n] (k : Site d n) :
    boxBasis d n k = siteVec d n k :=
  congrFun (coe_basisOfLinearIndependentOfCardEqFinrank _ _) k

/-- **AND THE BASIS DIAGONALISES THE ADJACENCY MATRIX**, in the indexing a completeness argument
wants: one eigenvalue per site. -/
theorem adjMatrix_mulVec_siteVec (n d : ℕ) (k : Site d n) :
    (boxGraph d n).adjMatrix ℝ *ᵥ siteVec d n k
      = boxEig d n (fun i => (k i).val + 1) • siteVec d n k :=
  adjMatrix_mulVec_boxVec n d _

end BoxAdjBasis
