import BoxGraphSuccIso
import BoxProdAdjSpectrum
import PathAdjBasis

/-!
# The `d`-dimensional box's adjacency spectrum, explicitly

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item says what is **actually** true of the box and
calls it a different theorem: *"the one-dimensional path's Dirichlet Laplacian has sine
eigenvectors rather than exponential ones, and the `d`-dimensional box is a tensor product of
paths."* Five units have now built the pieces — `PathAdjSpectrum` (the sine vectors),
`PathAdjBasis` (they are a basis), `BoxProdAdjSpectrum` (eigenvalues add across `□`),
`GraphIsoSpectrum` (an eigenvector survives a relabelling) and `BoxGraphSuccIso` (the estate's box
is a path times the box one dimension down) — each fenced with *"nothing spectral follows"*.
**This is the file where it follows.**

> **`boxVec d n k p = ∏ i, sin((pᵢ + 1)·kᵢπ/(n+1))`** — the product of one sine mode per axis.
>
> **`adjMatrix_mulVec_boxVec`** — for **every** dimension `d`, **every** side length `n` and
> **every** frequency vector `k : Fin d → ℕ`:
> `A_{boxGraph d n} · boxVec d n k = (∑ i, 2·cos(kᵢπ/(n+1))) · boxVec d n k`.
> **No hypotheses.**
>
> **`boxVec_ne_zero`** and **`hasEigenvector_boxVec`** — and with `0 < kᵢ ≤ n` on every axis the
> vector is nonzero, so these are eigen**values**, `n^d` of them counted with the frequencies that
> produce them.

## How it is proved, and why it is short

Induction on `d`, one axis at a time, and every step is a theorem already in the estate. At `d = 0`
the box has no edges. At `d + 1`, `BoxGraphSuccIso.boxGraph_succ_iso` presents the box as
`pathGraph n □ boxGraph d n`; `PathAdjSpectrum.adjMatrix_mulVec_pathVec` supplies the path's mode
on the new axis; the inductive hypothesis supplies the box's on the rest;
`BoxProdAdjSpectrum.adjMatrix_mulVec_prodVec` adds the two eigenvalues; and
`GraphIsoSpectrum.mulVec_smul_iso` carries the result back along the isomorphism. What remains is
`Fin.prod_univ_succ` and `Fin.sum_univ_succ` — the product of sines and the sum of cosines each
peel their first factor exactly where `Fin.cons` peels the axis.

## What this is NOT

**IT IS NOT A BASIS, so it is not the whole spectrum.** The `n^d` vectors `boxVec d n k` for
`1 ≤ kᵢ ≤ n` are **not shown independent here**. `PathAdjBasis.pathVec_linearIndependent` gets
independence from `Module.End.eigenvectors_linearIndependent'` because the path's eigenvalues are
**distinct**; in `d ≥ 2` dimensions they are **not** — `(1,2)` and `(2,1)` give the same sum — so
that route is closed and a genuine product-of-bases argument is needed. **That argument is not
attempted in this file, and as of 31 Aug 2026 no cost is offered for it** (`ERRATUM 194`,
`ERRATUM 246`). Without it this exhibits eigenvalues and does not bound a multiplicity or a
maximum.

**IT IS THE ADJACENCY MATRIX.** The estate's operator is `GraphLaplacian.massive`, `D − A + m²`
with the **true** degree, and `PathDegreeBoundary.pathGraph_degree` shows that degree is `1` at a
path's ends and `2` inside — so `D` is not a scalar and `A`'s eigenvectors are not `massive`'s.
**`UNLOCK_WATCHLIST`'s box item does not move**, which is what that item has predicted of every
unit in this sequence. What changes is that the item's *"different theorem"* is now proved rather
than named.

**No continuum limit, no lattice spacing, no `d = 4` specialisation** beyond what `d` already
covers.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxAdjSpectrum

open Finset Matrix SimpleGraph BoxGraph BoxGraphSuccIso PathAdjSpectrum

variable {d n : ℕ}

/-! ## 1. The vector and the eigenvalue -/

/-- **ONE SINE MODE PER AXIS**, multiplied. -/
noncomputable def boxVec (d n : ℕ) (k : Fin d → ℕ) (p : Site d n) : ℝ :=
  ∏ i, pathVec n (k i) (p i)

/-- **THE SUM OF THE PER-AXIS EIGENVALUES.** -/
noncomputable def boxEig (d n : ℕ) (k : Fin d → ℕ) : ℝ :=
  ∑ i, 2 * Real.cos ((k i : ℝ) * Real.pi / ((n : ℝ) + 1))

@[simp] theorem boxGraph_succ_iso_symm_apply (d n : ℕ) (p : Site (d + 1) n) :
    (boxGraph_succ_iso d n).symm p = (p 0, Fin.tail p) := rfl

/-- Peeling the first axis takes the product apart exactly as `Fin.cons` takes the site apart. -/
theorem boxVec_succ (d n : ℕ) (k : Fin (d + 1) → ℕ) :
    (fun p : Site (d + 1) n =>
        BoxProdAdjSpectrum.prodVec (pathVec n (k 0)) (boxVec d n (Fin.tail k))
          ((boxGraph_succ_iso d n).symm p))
      = boxVec (d + 1) n k := by
  funext p
  simp [BoxProdAdjSpectrum.prodVec, boxVec, Fin.prod_univ_succ, Fin.tail]

theorem boxEig_succ (d n : ℕ) (k : Fin (d + 1) → ℕ) :
    2 * Real.cos ((k 0 : ℝ) * Real.pi / ((n : ℝ) + 1)) + boxEig d n (Fin.tail k)
      = boxEig (d + 1) n k := by
  simp [boxEig, Fin.sum_univ_succ, Fin.tail]

/-! ## 2. The eigenvalue equation, in every dimension and with no hypotheses -/

/-- **THE `d`-DIMENSIONAL BOX'S ADJACENCY MODES.** -/
theorem adjMatrix_mulVec_boxVec (n d : ℕ) (k : Fin d → ℕ) :
    (boxGraph d n).adjMatrix ℝ *ᵥ boxVec d n k = boxEig d n k • boxVec d n k := by
  revert k
  induction d with
  | zero =>
      intro k
      have hzero : (boxGraph 0 n).adjMatrix ℝ = 0 := by
        ext p q
        have hna : ¬ BoxGraph.adj p q := by rintro ⟨i, -, -⟩; exact i.elim0
        simp [SimpleGraph.adjMatrix_apply, hna]
      rw [hzero, Matrix.zero_mulVec]
      simp [boxEig]
  | succ d ih =>
      intro k
      have hu := adjMatrix_mulVec_pathVec n (k 0)
      have hprod := BoxProdAdjSpectrum.adjMatrix_mulVec_prodVec
        (G := pathGraph n) (H := boxGraph d n) hu (ih (Fin.tail k))
      have htr := GraphIsoSpectrum.mulVec_smul_iso (boxGraph_succ_iso d n) hprod
      rw [boxVec_succ, boxEig_succ] at htr
      exact htr

/-! ## 3. And the vector is nonzero, so these are eigenvalues -/

/-- At the corner site every factor is `sin` of an angle strictly inside `(0, π)`. -/
theorem pathVec_first_pos {k : ℕ} (hpos : 0 < k) (hle : k ≤ n) (hn : 0 < n) :
    0 < pathVec n k ⟨0, hn⟩ := by
  have hrw : pathVec n k ⟨0, hn⟩ = Real.sin ((k : ℝ) * Real.pi / ((n : ℝ) + 1)) := by
    simp [pathVec, svec]
  rw [hrw]
  exact Real.sin_pos_of_pos_of_lt_pi (PathAdjBasis.angle_pos hpos) (PathAdjBasis.angle_lt_pi hle)

/-- **NONZERO whenever every frequency lies in `1 … n`** — the corner site alone witnesses it. -/
theorem boxVec_ne_zero {k : Fin d → ℕ} (hn : 0 < n) (hpos : ∀ i, 0 < k i) (hle : ∀ i, k i ≤ n) :
    boxVec d n k ≠ 0 := by
  intro hcon
  have hp : (0 : ℝ) < ∏ i, pathVec n (k i) (⟨0, hn⟩ : Fin n) :=
    Finset.prod_pos fun i _ => pathVec_first_pos (hpos i) (hle i) hn
  have h := congrFun hcon (fun _ => (⟨0, hn⟩ : Fin n))
  rw [boxVec] at h
  simp only [Pi.zero_apply] at h
  rw [h] at hp
  exact lt_irrefl 0 hp

/-- **SO THE SUM OF COSINES IS AN EIGENVALUE OF THE `d`-DIMENSIONAL BOX.** -/
theorem hasEigenvector_boxVec {k : Fin d → ℕ} (hn : 0 < n) (hpos : ∀ i, 0 < k i)
    (hle : ∀ i, k i ≤ n) :
    Module.End.HasEigenvector (Matrix.mulVecLin ((boxGraph d n).adjMatrix ℝ))
      (boxEig d n k) (boxVec d n k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact adjMatrix_mulVec_boxVec n d k
  · exact boxVec_ne_zero hn hpos hle

end BoxAdjSpectrum
