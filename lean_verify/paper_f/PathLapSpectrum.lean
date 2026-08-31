import PathAdjSpectrum
import PathDegreeBoundary

/-!
# The path's FREE-BOUNDARY Laplacian has cosine eigenvectors — exactly

`UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item states its obstruction as: *"a box has a
BOUNDARY and its degree is not constant … so no character is an eigenvector."* **That sentence is
true and it is about characters.** `PathAdjSpectrum` answered the neighbouring question for the
**adjacency** matrix with sine vectors, which are the Dirichlet modes; every unit since has carried
the fence *"still the adjacency matrix, `massive` is `D − A + m²` with the true degree"*.

**The free-boundary Laplacian has exact eigenvectors too, and they are cosines offset by a half
step.** They are not characters, so the item's sentence is not contradicted — it is routed around.

> **`cs n k t = cos((2t+1)·kπ/(2n))`** — the cosine sampled at the **half-integer** points
> `t + ½`, which is exactly what makes the reflection at the left end automatic.
>
> **`lapMatrix_mulVec_cosMode`** — `L_{pathGraph n} · cosMode n k`
> `= (2 − 2·cos(kπ/n))·cosMode n k`, for **every** `k` and every `n ≥ 1`, with the **true**
> free-boundary degree `1, 2, …, 2, 1`.

## The two boundary identities, and only one of them costs anything

Writing `c_t` for `cs n k t`, the recurrence `c_{t} + c_{t+2} = 2cos(θ)·c_{t+1}` with `θ = kπ/n` is
`Real.cos_add_cos` and holds for every `θ`. At an **interior** vertex that is the whole
computation.

* **At the left end** the missing term is `c_{−1} = cos(−θ/2) = cos(θ/2) = c_0`, so the deficient
  degree `1` and the missing neighbour cancel **identically** — `cs_base`, again just
  `Real.cos_add_cos`, with no condition on `θ`. **The half-step offset is what buys this**: sampling
  at integers instead would leave a genuine boundary term.
* **At the right end** the same cancellation needs `c_n = c_{n−1}`, and *that* is where
  `θ = kπ/n` is spent: `(2n+1)θ/2 = kπ + θ/2` and `(2n−1)θ/2 = kπ − θ/2`, which agree because
  `sin(kπ) = 0`. **`cs_top` is the only place the quantisation enters.**

## What this is NOT

**It is not a basis.** That the `n` vectors `cosMode n k`, `k = 0 … n−1`, are independent is **not**
proved here; the eigenvalues `2 − 2cos(kπ/n)` are distinct on that range but the argument is not
written. **That independence argument is not attempted in this file, and as of 31 Aug 2026 no cost
is offered for it** (`ERRATUM 194`, `ERRATUM 246`).

**It is not the box.** `boxGraph d n`'s Laplacian is not treated here; that needs the Laplacian to
add across `SimpleGraph.boxProd` — an analogue of `BoxProdAdjSpectrum.adjMatrix_mulVec_prodVec` for
`lapMatrix` — and an induction. Not done here.

**It is not `massive`.** `GraphLaplacian.massive` is `L + m²`, so an eigenvector of `L` is one of
`massive` with the eigenvalue shifted by `m²`; that shift is **not stated here**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace PathLapSpectrum

open Finset Matrix SimpleGraph PathAdjSpectrum

/-! ## 1. The half-step cosine and its two identities -/

/-- Half the angle: `kπ/(2n)`. The vectors are sampled at odd multiples of this, i.e. at the
half-integer points `t + ½`. -/
noncomputable def half (n k : ℕ) : ℝ := (k : ℝ) * Real.pi / (2 * n)

/-- **THE HALF-STEP COSINE**, `c_t = cos((t + ½)·θ)` with `θ = kπ/n`. -/
noncomputable def cs (n k t : ℕ) : ℝ := Real.cos ((2 * t + 1) * half n k)

/-- The mode as a vector on the path's vertices. **Named `cosMode` and not `cvec`**:
`cvec` is taken three times over in this estate — a `Fin 4` witness, entrywise conjugation, a
`Fin 7` half-supported vector — and none is this (`newnames_scan`, 31 Aug 2026). -/
noncomputable def cosMode (n k : ℕ) (j : Fin n) : ℝ := cs n k j.val

/-- **THE THREE-TERM RECURRENCE**, one `cos_add`/`cos_sub` expansion. -/
theorem cs_rec (n k t : ℕ) :
    cs n k t + cs n k (t + 2) = 2 * Real.cos (2 * half n k) * cs n k (t + 1) := by
  simp only [cs]
  have e1 : (2 * ((t : ℕ) : ℝ) + 1) * half n k
      = (2 * (((t + 1 : ℕ)) : ℝ) + 1) * half n k - 2 * half n k := by push_cast; ring
  have e2 : (2 * (((t + 2 : ℕ)) : ℝ) + 1) * half n k
      = (2 * (((t + 1 : ℕ)) : ℝ) + 1) * half n k + 2 * half n k := by push_cast; ring
  rw [e1, e2, Real.cos_sub, Real.cos_add]
  ring

/-- **THE LEFT END NEEDS NO QUANTISATION.** `c_{−1} = c_0` because cosine is even, so the reflected
form of the recurrence at `t = 0` reads `c_0 + c_1 = 2cos(θ)·c_0` — for **every** `θ`. -/
theorem cs_base (n k : ℕ) :
    cs n k 0 + cs n k 1 = 2 * Real.cos (2 * half n k) * cs n k 0 := by
  simp only [cs]
  have e0 : (2 * (((0 : ℕ)) : ℝ) + 1) * half n k = half n k := by push_cast; ring
  have e1 : (2 * (((1 : ℕ)) : ℝ) + 1) * half n k = 2 * half n k + half n k := by push_cast; ring
  rw [e0, e1, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (-2 * Real.cos (half n k)) * Real.sin_sq_add_cos_sq (half n k)

/-- **THE RIGHT END IS WHERE `θ = kπ/n` IS SPENT.** `c_n = c_{n−1}`, because
`(2n±1)·θ/2 = kπ ± θ/2` and `sin(kπ) = 0`. -/
theorem cs_top (k m : ℕ) : cs (m + 1) k (m + 1) = cs (m + 1) k m := by
  have h2 : (2 : ℝ) * ((m : ℝ) + 1) ≠ 0 := by positivity
  have hH : (2 * ((m : ℝ) + 1)) * half (m + 1) k = (k : ℝ) * Real.pi := by
    rw [half]; push_cast; field_simp
  simp only [cs]
  have e1 : (2 * (((m + 1 : ℕ)) : ℝ) + 1) * half (m + 1) k
      = (k : ℝ) * Real.pi + half (m + 1) k := by
    rw [← hH]; push_cast; ring
  have e2 : (2 * ((m : ℕ) : ℝ) + 1) * half (m + 1) k
      = (k : ℝ) * Real.pi - half (m + 1) k := by
    rw [← hH]; ring
  rw [e1, e2, Real.cos_add, Real.cos_sub, Real.sin_nat_mul_pi]
  ring

/-! ## 2. The neighbour sum on a path, for an arbitrary vector -/

/-- **ONE FORMULA AT EVERY VERTEX**, with the two ends showing as missing terms rather than as
phantom values. -/
theorem sum_neighborFinset (n : ℕ) (v : ℕ → ℝ) (j : Fin n) :
    ∑ i ∈ (pathGraph n).neighborFinset j, v i.val
      = (if 0 < j.val then v (j.val - 1) else 0)
        + (if j.val + 1 < n then v (j.val + 1) else 0) := by
  classical
  rw [neighborFinset_pathGraph, Finset.filter_or, Finset.sum_union]
  · have hup : (univ.filter fun i : Fin n => j.val + 1 = i.val).sum (fun i => v i.val)
        = (if j.val + 1 < n then v (j.val + 1) else 0) := by
      by_cases hj : j.val + 1 < n
      · have hset : (univ.filter fun i : Fin n => j.val + 1 = i.val) = {⟨j.val + 1, hj⟩} := by
          ext i; simp [Fin.ext_iff, eq_comm]
        rw [hset, Finset.sum_singleton, if_pos hj]
      · have hset : (univ.filter fun i : Fin n => j.val + 1 = i.val) = ∅ := by
          ext i; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
          intro h; exact hj (h ▸ i.isLt)
        rw [hset, Finset.sum_empty, if_neg hj]
    have hdn : (univ.filter fun i : Fin n => i.val + 1 = j.val).sum (fun i => v i.val)
        = (if 0 < j.val then v (j.val - 1) else 0) := by
      rcases Nat.eq_zero_or_pos j.val with hz | hp
      · have hset : (univ.filter fun i : Fin n => i.val + 1 = j.val) = ∅ := by
          ext i; simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]; omega
        rw [hset, Finset.sum_empty, if_neg (by omega)]
      · have hlt : j.val - 1 < n := by have := j.isLt; omega
        have hset : (univ.filter fun i : Fin n => i.val + 1 = j.val) = {⟨j.val - 1, hlt⟩} := by
          ext i; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff]; omega
        rw [hset, Finset.sum_singleton, if_pos hp]
    rw [hup, hdn, add_comm]
  · refine Finset.disjoint_filter.2 fun i _ h1 h2 => ?_
    omega

/-! ## 3. The eigenvector identity, with the true degree -/

/-- **THE HALF-STEP COSINE IS AN EIGENVECTOR OF THE FREE-BOUNDARY LAPLACIAN**, eigenvalue
`2 − 2·cos(kπ/n)`. -/
theorem lapMatrix_mulVec_cosMode (m k : ℕ) :
    (pathGraph (m + 1)).lapMatrix ℝ *ᵥ cosMode (m + 1) k
      = (2 - 2 * Real.cos (2 * half (m + 1) k)) • cosMode (m + 1) k := by
  funext j
  have hsum : ∑ i ∈ (pathGraph (m + 1)).neighborFinset j, cosMode (m + 1) k i
      = (if 0 < j.val then cs (m + 1) k (j.val - 1) else 0)
        + (if j.val + 1 < m + 1 then cs (m + 1) k (j.val + 1) else 0) :=
    sum_neighborFinset (m + 1) (cs (m + 1) k) j
  rw [SimpleGraph.lapMatrix_mulVec_apply, hsum, Pi.smul_apply, smul_eq_mul,
    PathDegreeBoundary.pathGraph_degree]
  push_cast
  change ((if 0 < j.val then (1 : ℝ) else 0) + (if j.val + 1 < m + 1 then (1 : ℝ) else 0))
      * cosMode (m + 1) k j
      - ((if 0 < j.val then cs (m + 1) k (j.val - 1) else 0)
        + (if j.val + 1 < m + 1 then cs (m + 1) k (j.val + 1) else 0))
      = (2 - 2 * Real.cos (2 * half (m + 1) k)) * cosMode (m + 1) k j
  rw [cosMode]
  by_cases h0 : 0 < j.val
  · rw [if_pos h0, if_pos h0]
    have hrec := cs_rec (m + 1) k (j.val - 1)
    rw [show j.val - 1 + 1 = j.val from by omega, show j.val - 1 + 2 = j.val + 1 from by omega]
      at hrec
    by_cases h1 : j.val + 1 < m + 1
    · rw [if_pos h1, if_pos h1]
      linarith
    · rw [if_neg h1, if_neg h1]
      have hj : j.val = m := by have := j.isLt; omega
      have htop : cs (m + 1) k (j.val + 1) = cs (m + 1) k j.val := by
        rw [hj]; exact cs_top k m
      rw [htop] at hrec
      linarith
  · rw [if_neg h0, if_neg h0]
    have hz : j.val = 0 := by omega
    by_cases h1 : j.val + 1 < m + 1
    · rw [if_pos h1, if_pos h1, hz]
      have hb := cs_base (m + 1) k
      linarith
    · rw [if_neg h1, if_neg h1, hz]
      have hm : m = 0 := by omega
      subst hm
      have hb := cs_base 1 k
      have ht : cs 1 k 1 = cs 1 k 0 := cs_top k 0
      rw [ht] at hb
      linarith

end PathLapSpectrum
