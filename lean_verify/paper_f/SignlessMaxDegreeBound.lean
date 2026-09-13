import SignlessTopDegreeBounds

/-!
# The top of the signless spectrum is at least the maximum degree plus one

**THE SHARPENING `SignlessTopDegreeBounds` NAMED AND DECLINED.** That file bracketed the top of
`Q`'s spectrum between twice the average degree and twice the maximum, and wrote: *the classical
sharpening `topEigen ≥ Δ + 1` is true and is not proved here — it needs a test vector supported on a
vertex and its neighbourhood rather than the all-ones vector, and nothing here builds one.* **This
builds one.**

**THE VECTOR IS THE STAR AT A VERTEX OF MAXIMUM DEGREE**, weighted `1` at the centre and `1/Δ` at
each neighbour and `0` elsewhere. Rayleigh's easy half turns it into
`Δ(1 + 1/Δ)² ≤ topEigen · (1 + 1/Δ)`, and `Δ(1 + 1/Δ) = Δ + 1` exactly — **the weight `1/Δ` is the
one that makes the two sides cancel**, which is why the bound comes out clean rather than
asymptotic.

**AND THE ESTATE HAD THE SAME ARGUMENT FOR THE OTHER LAPLACIAN, WHICH THAT FENCE DID NOT KNOW**
(`ERRATUM 531`). `paper_f/LaplacianDeltaPlusOne.lean` proves `Δ + 1 ≤ ‖G.lapMatrix ℝ‖` with the
vector `Δ·e_v − ∑_{u ∼ v} e_u`, and its header states the method — *every term of the Laplacian's
edge sum is a square, so throwing terms away is free*. **This is not a duplicate of it and the
differences are load-bearing**: a different matrix, whose spectra genuinely differ off the
two-colourable case (`SignlessColourableNecessary`); a different vector, its neighbours **positive
and small** because `(xᵢ + xⱼ)²` wants that where `(xᵢ − xⱼ)²` wants them negative; and a bound at
the maximum degree rather than at each vertex.

**AND THE TWO LOWER BOUNDS ARE INCOMPARABLE, WHICH IS WHY BOTH ARE KEPT.** On a `k`-regular graph
the average bound gives `2k`, which the previous file showed is exact, while this one gives only
`k + 1`. On a star `K_{1,n}` the average bound gives under `4` and this one gives `n + 1`.
**Neither dominates**, and a reader picking one should pick by the graph.

## What is proved

**`two_row_le_double_sum`** — a symmetric non-negative kernel with zero diagonal has double sum at
least twice any one of its rows. Stated in general because the graph plays no part in it.

**`sum_ite_adj`** — a constant summed over the neighbours is the degree times the constant.

**`testVec`, `testVec_self`, `testVec_adj`, `dot_testVec`** — the star vector and its norm.

> ⚠ **A BULLET STOOD HERE CLAIMING A BRIDGE THE ESTATE ALREADY HAD, AND BOTH ITS DECLARATIONS ARE
> DELETED** (`ERRATUM 532`, 2026-09-13). It read: *`inner_eq_dot`, `quadForm_le_topEig` — Rayleigh's
> easy half in `dotProduct` form. The estate had it only on `EuclideanSpace`, and the bridge is what
> made the previous file's lower bound awkward and this one's possible.* **The second sentence is
> false.** `RayleighVariational.quadForm_le_topEigen` reads `x ⬝ᵥ A *ᵥ x ≤ topEigen hA * (x ⬝ᵥ x)`
> — the `dotProduct` form, at this pin, proved 2026-09-03 — and it was in this file's import
> closure. `quadForm_le_topEigen` is deleted and its one use now calls that file; `inner_eq_dot`
> went with it, having had no other consumer. The main theorem is unchanged, and so is its proof
> below the first line.

**`maxDegree_add_one_le_topEigen`** — **THE FILE'S THEOREM**, on any finite graph with an edge.

## What is NOT here

* **NO UPPER SHARPENING, as of 2026-09-13 (entry 19).** `2Δ` stands from the previous file, and the
  classical improvements (Merris, and the maximum over edges of `deg u + deg v`) are **not**
  proved: each needs a different argument and none is attempted (`ERRATUM 246`).
* **NO EQUALITY CASE.** `Δ + 1` is attained exactly on a star, which is **not shown here**; the
  file exhibits no graph where this bound is tight.
* **NO CONNECTEDNESS, again.** The bound needs only that some vertex has a neighbour.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and adjacency, `Nonempty V`, and `0 < G.maxDegree` — that is, at least one edge.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessMaxDegreeBound

open Matrix SimpleGraph LaplacianSignless RayleighMatrix SignlessPerronSimple
open RayleighVariational

/-! ## 1. Two facts about matrices, with no graph in them -/

section Matrices
variable {V : Type*} [Fintype V]

/-- The double sum of a symmetric non-negative kernel is at least twice one of its rows. -/
theorem two_row_le_double_sum (T : V → V → ℝ) (hT : ∀ i j, 0 ≤ T i j)
    (hsymm : ∀ i j, T i j = T j i) (hdiag : ∀ i, T i i = 0) (v : V) :
    2 * (∑ j, T v j) ≤ ∑ i, ∑ j, T i j := by
  classical
  have hsplit : ∑ i, ∑ j, T i j = (∑ j, T v j) + ∑ i ∈ Finset.univ.erase v, ∑ j, T i j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have hrest : ∑ j, T v j ≤ ∑ i ∈ Finset.univ.erase v, ∑ j, T i j := by
    have hle : ∑ i ∈ Finset.univ.erase v, T i v ≤ ∑ i ∈ Finset.univ.erase v, ∑ j, T i j :=
      Finset.sum_le_sum fun i _ => Finset.single_le_sum (fun j _ => hT i j) (Finset.mem_univ v)
    refine le_trans (le_of_eq ?_) hle
    have hfull : ∑ i, T i v = T v v + ∑ i ∈ Finset.univ.erase v, T i v :=
      (Finset.add_sum_erase _ (fun i => T i v) (Finset.mem_univ v)).symm
    rw [hdiag v, zero_add] at hfull
    rw [← hfull]
    exact Finset.sum_congr rfl fun i _ => hsymm v i
  rw [hsplit]; linarith

end Matrices

/-! ## 2. The star vector at a vertex -/

section Star
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def testVec (v : V) (d : ℝ) : V → ℝ :=
  fun u => if u = v then 1 else if G.Adj v u then 1 / d else 0

theorem testVec_self (v : V) (d : ℝ) : testVec G v d v = 1 := by simp [testVec]

theorem testVec_adj {v u : V} (d : ℝ) (h : G.Adj v u) : testVec G v d u = 1 / d := by
  have hne : u ≠ v := h.ne'
  simp [testVec, hne, h]

end Star

/-! ## 3. Its norm, and the neighbour sum -/

section Counting
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem sum_ite_adj (c : ℝ) (v : V) :
    ∑ j, (if G.Adj v j then c else 0) = (G.degree v : ℝ) * c := by
  classical
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
  have hf : (Finset.univ.filter fun j => G.Adj v j) = G.neighborFinset v := by
    ext j; simp [SimpleGraph.mem_neighborFinset]
  rw [hf, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]

end Counting

section Norm
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem dot_testVec (v : V) {d : ℝ} (hd : d ≠ 0) :
    testVec G v d ⬝ᵥ testVec G v d = 1 + (G.degree v : ℝ) / d ^ 2 := by
  classical
  rw [dotProduct]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), testVec_self]
  have : ∑ u ∈ Finset.univ.erase v, testVec G v d u * testVec G v d u
      = ∑ u, (if G.Adj v u then (1 / d) * (1 / d) else 0) := by
    rw [← Finset.add_sum_erase _ (fun u => if G.Adj v u then (1/d)*(1/d) else 0)
      (Finset.mem_univ v)]
    simp only [G.irrefl, if_false, zero_add]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hne : u ≠ v := (Finset.mem_erase.mp hu).1
    by_cases hadj : G.Adj v u
    · rw [testVec_adj G d hadj]; simp [hadj]
    · simp [testVec, hne, hadj]
  rw [this, sum_ite_adj]
  field_simp

/-! ## 4. So the top of the spectrum clears the maximum degree by one -/

theorem maxDegree_add_one_le_topEigen [Nonempty V] (hΔ : 0 < G.maxDegree) :
    (G.maxDegree : ℝ) + 1
      ≤ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
  classical
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  set d : ℝ := (G.maxDegree : ℝ) with hddef
  have hd : (0 : ℝ) < d := by rw [hddef]; exact_mod_cast hΔ
  set x := testVec G v d with hx
  have hdegv : (G.degree v : ℝ) = d := by rw [hddef, hv]
  -- the quadratic form, bounded below by the star at `v`
  have hquad : d * (1 + 1 / d) ^ 2 ≤ x ⬝ᵥ (signlessLap G) *ᵥ x := by
    rw [dotProduct_signlessLap]
    have hrow : ∑ j, (if G.Adj v j then (x v + x j) ^ 2 else 0) = d * (1 + 1 / d) ^ 2 := by
      rw [show (fun j => if G.Adj v j then (x v + x j) ^ 2 else 0)
          = (fun j => if G.Adj v j then (1 + 1 / d) ^ 2 else 0) from funext fun j => by
        by_cases h : G.Adj v j
        · rw [if_pos h, if_pos h, hx, testVec_self, testVec_adj G d h]
        · rw [if_neg h, if_neg h]]
      rw [sum_ite_adj, hdegv]
    have := two_row_le_double_sum (fun i j => if G.Adj i j then (x i + x j) ^ 2 else 0)
      (fun i j => by by_cases h : G.Adj i j <;> simp [h, sq_nonneg]) (fun i j => by
        by_cases h : G.Adj i j
        · simp [h, h.symm]; ring
        · have h' : ¬ G.Adj j i := fun hh => h hh.symm
          simp [h, h'])
      (fun i => by simp) v
    rw [hrow] at this
    linarith
  have hnorm : x ⬝ᵥ x = 1 + 1 / d := by
    rw [hx, dot_testVec G v hd.ne', hdegv]
    field_simp
  have hray := RayleighVariational.quadForm_le_topEigen
    (LaplacianSignlessDefinite.signlessLap_isHermitian G) x
  rw [hnorm] at hray
  have hstep : d * (1 + 1 / d) ^ 2
      ≤ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) * (1 + 1 / d) :=
    le_trans hquad hray
  have hpos : (0 : ℝ) < 1 + 1 / d := by positivity
  have hkey : d * (1 + 1 / d) ≤ topEigen (LaplacianSignlessDefinite.signlessLap_isHermitian G) := by
    refine le_of_mul_le_mul_right ?_ hpos
    nlinarith [hstep]
  have : d * (1 + 1 / d) = d + 1 := by field_simp
  linarith [hkey, this.symm.le, this.le]

end Norm

end SignlessMaxDegreeBound
