import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The path graph's adjacency spectrum: sine vectors, eigenvalue `2 cos(kπ/(n+1))`

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item names the fact a box spectrum would need
first — *"the one-dimensional path's Dirichlet Laplacian has sine eigenvectors rather than
exponential ones"* — and records that it is not formalised here. `BoxGraphPath` probed for it and
found **nothing**: no name pairs `pathGraph` or `cycleGraph` with `eigen` or `spectr` in the pinned
dump, and `Matrix.tridiagonal` is `0`. This file proves it, for the **adjacency** matrix.

> **`svec`** — `svec n k t = sin (t · kπ/(n+1))`, an ordinary function of a natural number, and
> **`pathVec n k j = svec n k (j + 1)`**, its restriction to the path's vertices.
>
> **`svec_zero`, `svec_top`** — it vanishes at **both** phantom endpoints: at `t = 0` because
> `sin 0 = 0`, and at `t = n + 1` because the angle is then `kπ` (`Real.sin_nat_mul_pi`).
>
> **`sum_neighborFinset_pathVec`** — hence the neighbour sum has **one formula at every vertex**,
> boundary or not: `∑ over neighbours = svec j + svec (j + 2)`. A vertex at either end has one
> neighbour rather than two, and the missing term is exactly a phantom endpoint, which is `0`.
> **That is the whole reason the boundary costs nothing here.**
>
> **`adjMatrix_mulVec_pathVec`** — so `A · v = 2 cos(kπ/(n+1)) · v`, by `Real.sin_add_sin`.

## What this is NOT

**It is not the path's Laplacian spectrum, and the difference is the point.** The estate's
`GraphLaplacian.massive` is `D − A + m²` with `D` the **true degree**, which on a path is `1` at
the ends and `2` inside. The sine vectors are eigenvectors of `A`, hence of `2I − A + m²` — the
**Dirichlet** Laplacian, with constant `2` — and **not** of `D − A + m²`. Nothing here claims
otherwise, and the gap is exactly the item's *"a box has a boundary and its degree is not
constant"*.

**It is not a basis.** That these `n` vectors span, or are independent, or exhaust the spectrum, is
**not proved**: `k` ranges over whatever the caller supplies, `k = 0` gives the zero vector, and no
orthogonality is established. As of 31 August 2026 the estate has none of that, and no cost is
offered (`ERRATUM 194`, `ERRATUM 246`).

**It is not the box.** `BoxGraphPath.boxGraph_adj_pathGraph` names the estate's box as a box product
of paths; the spectrum of a box product is a separate theorem, absent from Mathlib (probed), and
not attempted here.
-/

namespace PathAdjSpectrum

open Finset Matrix SimpleGraph

/-- Mathlib defines `pathGraph` through `hasse` and gives it no decidability instance, so the
neighbour finset does not exist without this. -/
instance pathGraphDecidableAdj (n : ℕ) : DecidableRel (pathGraph n).Adj :=
  fun _ _ => decidable_of_iff _ pathGraph_adj.symm

/-! ## 1. The sine vector and its two phantom zeros -/

/-- `sin (t · kπ/(n+1))`, as a function of a natural number. -/
noncomputable def svec (n k t : ℕ) : ℝ := Real.sin (t * (k * Real.pi / (n + 1)))

/-- The path's eigenvector: `svec` shifted so the first vertex carries `t = 1`. -/
noncomputable def pathVec (n k : ℕ) (j : Fin n) : ℝ := svec n k (j.val + 1)

@[simp] theorem svec_zero (n k : ℕ) : svec n k 0 = 0 := by simp [svec]

/-- **AND IT VANISHES AT THE FAR PHANTOM ENDPOINT TOO**, which is what the angle was chosen for. -/
theorem svec_top (n k : ℕ) : svec n k (n + 1) = 0 := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have : ((n : ℝ) + 1) * (k * Real.pi / ((n : ℝ) + 1)) = k * Real.pi := by
    field_simp
  simp only [svec]
  push_cast
  rw [this]
  exact Real.sin_nat_mul_pi k

/-! ## 2. The neighbour sum, with one formula at every vertex -/

/-- The path's neighbours of `j`, as a filter. -/
theorem neighborFinset_pathGraph {n : ℕ} (j : Fin n) :
    (pathGraph n).neighborFinset j
      = univ.filter fun i : Fin n => j.val + 1 = i.val ∨ i.val + 1 = j.val := by
  ext i
  simp only [mem_neighborFinset, mem_filter, mem_univ, true_and, pathGraph_adj]

/-- **ONE FORMULA AT EVERY VERTEX, BOUNDARY OR NOT.** An end vertex has one neighbour and the
missing term is a phantom endpoint, which `svec_zero` and `svec_top` make `0`. -/
theorem sum_neighborFinset_pathVec (n k : ℕ) (j : Fin n) :
    ∑ i ∈ (pathGraph n).neighborFinset j, pathVec n k i
      = svec n k j.val + svec n k (j.val + 2) := by
  classical
  rw [neighborFinset_pathGraph, Finset.filter_or, Finset.sum_union]
  · have hup : (univ.filter fun i : Fin n => j.val + 1 = i.val).sum (pathVec n k)
        = svec n k (j.val + 2) := by
      by_cases hj : j.val + 1 < n
      · have : (univ.filter fun i : Fin n => j.val + 1 = i.val) = {⟨j.val + 1, hj⟩} := by
          ext i; simp [Fin.ext_iff, eq_comm]
        rw [this, Finset.sum_singleton, pathVec]
      · have : (univ.filter fun i : Fin n => j.val + 1 = i.val) = ∅ := by
          ext i; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          intro h; exact hj (h ▸ i.isLt)
        have hjn : j.val + 2 = n + 1 := by have := j.isLt; omega
        rw [this, Finset.sum_empty, hjn, svec_top]
    have hdn : (univ.filter fun i : Fin n => i.val + 1 = j.val).sum (pathVec n k)
        = svec n k j.val := by
      rcases Nat.eq_zero_or_pos j.val with hz | hp
      · have : (univ.filter fun i : Fin n => i.val + 1 = j.val) = ∅ := by
          ext i; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          omega
        rw [this, Finset.sum_empty, hz, svec_zero]
      · have hlt : j.val - 1 < n := by have := j.isLt; omega
        have : (univ.filter fun i : Fin n => i.val + 1 = j.val) = {⟨j.val - 1, hlt⟩} := by
          ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]
          omega
        rw [this, Finset.sum_singleton, pathVec]
        congr 1
        change j.val - 1 + 1 = j.val
        omega
    rw [hup, hdn, add_comm]
  · refine Finset.disjoint_filter.2 fun i _ h1 h2 => ?_
    omega

/-! ## 3. The eigenvector identity -/

/-- **THE SINE VECTOR IS AN EIGENVECTOR OF THE PATH'S ADJACENCY MATRIX**, with eigenvalue
`2 cos(kπ/(n+1))`. -/
theorem adjMatrix_mulVec_pathVec (n k : ℕ) :
    (pathGraph n).adjMatrix ℝ *ᵥ pathVec n k
      = (2 * Real.cos (k * Real.pi / (n + 1))) • pathVec n k := by
  funext j
  rw [adjMatrix_mulVec_apply, sum_neighborFinset_pathVec]
  set θ : ℝ := k * Real.pi / ((n : ℝ) + 1) with hθ
  have hsum : svec n k j.val + svec n k (j.val + 2)
      = 2 * Real.sin ((j.val + 1) * θ) * Real.cos θ := by
    simp only [svec, ← hθ]
    push_cast
    rw [Real.sin_add_sin]
    congr 1
    · congr 1
      ring
    · rw [show (↑j.val * θ - (↑j.val + 2) * θ) / 2 = -θ by ring, Real.cos_neg]
  rw [hsum]
  simp only [Pi.smul_apply, smul_eq_mul, pathVec, svec, ← hθ]
  push_cast
  ring

end PathAdjSpectrum
