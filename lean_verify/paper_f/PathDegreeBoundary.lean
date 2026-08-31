import PathAdjSpectrum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# The path's degree, exactly — and the obstruction its own item records, made quantitative

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item states its obstruction as *"a box has a
BOUNDARY and its degree is not constant (`BoxDegree` bounds it by `2d` and does not make it
equal)"*. Three units have now given the path's whole adjacency spectrum and the product rule, and
the item correctly predicted that neither would move it. **This file addresses the obstruction
itself**, in the one dimension where it can be pinned down exactly.

> **`pathGraph_degree`** — `deg j = [0 < j] + [j + 1 < n]`, one uniform formula: a vertex has a
> left neighbour unless it is first and a right neighbour unless it is last. The estate's
> `BoxDegree.boxGraph_degree_le` bounds the box's degree by `2d`; **this is an equality**, at
> `d = 1`.
>
> **`pathGraph_degree_interior`, `pathGraph_degree_first`, `pathGraph_degree_last`** — hence `2`
> inside and `1` at each end of a path with at least two vertices.
>
> **`lapMatrix_eq_dirichlet_sub_boundary`** — so
> `L = (2·I − A) − diagonal (fun j => 2 − deg j)`, and **the correction is supported exactly on the
> two endpoints**. That is the item's *"its degree is not constant"* as an equation.

**What this buys, stated carefully.** The estate's `GraphLaplacian.massive` is built from `L`, and
`PathAdjBasis` diagonalises `2·I − A`. The two differ by a **diagonal matrix of rank at most two**,
supported on the boundary. That is a much sharper statement of the gap than *"the degree is not
constant"*, and it is **all** it is: no perturbation theory is invoked, no eigenvalue of `L` is
computed, and no bound relating the two spectra is proved here.

## What this is NOT

**It does not compute the path Laplacian's spectrum**, and nothing here says a rank-two correction
is small. **It does not touch the `d`-dimensional box**, whose boundary is not two points and whose
degree defect is not rank two. `UNLOCK_WATCHLIST`'s box item **does not move**, for the reason it
has always given. No cost is offered for either (`ERRATUM 194`, `ERRATUM 246`).
-/

namespace PathDegreeBoundary

open Finset Matrix SimpleGraph PathAdjSpectrum

variable {n : ℕ}

/-! ## 1. The degree, exactly -/

/-- **ONE FORMULA AT EVERY VERTEX**: a left neighbour unless first, a right neighbour unless
last. -/
theorem pathGraph_degree (j : Fin n) :
    (pathGraph n).degree j = (if 0 < j.val then 1 else 0) + (if j.val + 1 < n then 1 else 0) := by
  classical
  rw [← card_neighborFinset_eq_degree, neighborFinset_pathGraph, Finset.filter_or,
    Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun i _ h1 h2 => by omega)]
  have hup : (univ.filter fun i : Fin n => j.val + 1 = i.val).card
      = if j.val + 1 < n then 1 else 0 := by
    by_cases hj : j.val + 1 < n
    · rw [if_pos hj]
      have : (univ.filter fun i : Fin n => j.val + 1 = i.val) = {⟨j.val + 1, hj⟩} := by
        ext i; simp [Fin.ext_iff, eq_comm]
      rw [this, Finset.card_singleton]
    · rw [if_neg hj]
      have : (univ.filter fun i : Fin n => j.val + 1 = i.val) = ∅ := by
        ext i
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        intro h; exact hj (h ▸ i.isLt)
      rw [this, Finset.card_empty]
  have hdn : (univ.filter fun i : Fin n => i.val + 1 = j.val).card
      = if 0 < j.val then 1 else 0 := by
    rcases Nat.eq_zero_or_pos j.val with hz | hp
    · rw [if_neg (by omega)]
      have : (univ.filter fun i : Fin n => i.val + 1 = j.val) = ∅ := by
        ext i; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]; omega
      rw [this, Finset.card_empty]
    · rw [if_pos hp]
      have hlt : j.val - 1 < n := by have := j.isLt; omega
      have : (univ.filter fun i : Fin n => i.val + 1 = j.val) = {⟨j.val - 1, hlt⟩} := by
        ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]; omega
      rw [this, Finset.card_singleton]
  rw [hup, hdn, add_comm]

theorem pathGraph_degree_interior {j : Fin n} (h0 : 0 < j.val) (h1 : j.val + 1 < n) :
    (pathGraph n).degree j = 2 := by
  rw [pathGraph_degree, if_pos h0, if_pos h1]

theorem pathGraph_degree_first (hn : 2 ≤ n) (h : (0 : ℕ) < n) :
    (pathGraph n).degree ⟨0, h⟩ = 1 := by
  rw [pathGraph_degree]
  simp only [lt_irrefl, if_false, zero_add]
  rw [if_pos (by omega)]

theorem pathGraph_degree_last (hn : 2 ≤ n) (h : n - 1 < n) :
    (pathGraph n).degree ⟨n - 1, h⟩ = 1 := by
  have h0 : (0 : ℕ) < (⟨n - 1, h⟩ : Fin n).val := by change 0 < n - 1; omega
  have h1 : ¬ ((⟨n - 1, h⟩ : Fin n).val + 1 < n) := by change ¬ (n - 1 + 1 < n); omega
  rw [pathGraph_degree, if_pos h0, if_neg h1]

/-! ## 2. The Laplacian as the Dirichlet one minus a boundary term -/

/-- **THE ITEM'S OBSTRUCTION AS AN EQUATION.** `L = (2·I − A) − diagonal (2 − deg)`, and the
subtracted matrix is `0` at every interior vertex. -/
theorem lapMatrix_eq_dirichlet_sub_boundary :
    (pathGraph n).lapMatrix ℝ
      = ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - (pathGraph n).adjMatrix ℝ)
        - Matrix.diagonal fun j => 2 - ((pathGraph n).degree j : ℝ) := by
  classical
  rw [SimpleGraph.lapMatrix, SimpleGraph.degMatrix]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
  · simp [Matrix.one_apply_ne hij, hij]

/-- **AND THE CORRECTION IS SUPPORTED ON THE BOUNDARY.** At an interior vertex it vanishes. -/
theorem boundary_defect_interior {j : Fin n} (h0 : 0 < j.val) (h1 : j.val + 1 < n) :
    2 - ((pathGraph n).degree j : ℝ) = 0 := by
  rw [pathGraph_degree_interior h0 h1]
  norm_num

end PathDegreeBoundary
