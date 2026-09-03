import LaplacianNormLowerBound

/-!
# `Δ + 1 ≤ ‖L‖` at every finite graph with an edge

`LaplacianNormLowerBound` got `(deg u + deg v + 2)/2` at every edge and `Δ + 1` only on regular
graphs, and filed the general bound as its own watchlist item with the missing step named:

> the witness `Δ • Pi.single v 1 - ∑_{u ∼ v} Pi.single u 1`, whose quadratic form is
> `Δ³ + 2Δ² + ∑_{u ∼ v} deg u - 2·e(N(v))` against `‖x‖² = Δ² + Δ`, needs
> `2·e(N(v)) ≤ ∑_{u ∼ v} (deg u - 1)`.

**That counting inequality is not needed and the item's own route was the long way round.** Every
term of the Laplacian's edge sum is a square, so **throwing terms away is free**: keeping only the
pairs incident to `v` gives `xᵀLx ≥ Δ(Δ+1)²` outright, with no edge inside the neighbourhood ever
counted and no degree of any neighbour appearing. Against `x ⬝ᵥ x = Δ² + Δ = Δ(Δ+1)` that is
`Δ + 1` exactly.

```
Δ + 1  ≤  ‖G.lapMatrix ℝ‖        whenever G.degree v = Δ and 1 ≤ Δ
```

and `Δ + 1 + m² ≤ ‖massive G m‖`. Taking `v` of maximum degree gives the classical bound; taking any
vertex gives a family of bounds, which is why the statement is at an arbitrary vertex.

## What this closes and what it does not

**It closes the watchlist item ADDED 2026-09-03 (entry 26)** and it **strictly contains**
`LaplacianNormLowerBound.succ_le_norm_lapMatrix_of_regular`, which is this at a regular graph.
The edge bound `(deg u + deg v + 2)/2` is **not** contained: at an edge between two vertices of
degree `Δ` it gives `Δ + 1` too, but where the degrees differ it can beat this one — on the path
`a — b — c` at the edge `ab` it gives `(1 + 2 + 2)/2 = 2.5` where `Δ + 1 = 3` at `b`, and on a
graph with a high-degree vertex adjacent to another high-degree vertex it gives more than `Δ + 1`.
**Neither subsumes the other and both stay.**

**Still not sharp.** `Δ + 1 ≤ ‖L‖ ≤ 2Δ` is exact at both ends — the star attains the left, an even
cycle the right — so no single number is available in general, and this file does not claim one.

**Not an eigenvalue statement.** With `OpNormTopEigenvalue.isGreatest_eigenvalue_opNorm` the bound
reads *the greatest eigenvalue of `L` is at least `Δ + 1`*; that reading is available and is not
drawn here.

**No wall moves**, and no measure or field appears.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianDeltaPlusOne

open Matrix Finset GraphLaplacian SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The witness -/

/-- `Δ` at `v`, `-1` at each neighbour of `v`, `0` elsewhere. -/
noncomputable def starVec (v : V) : V → ℝ :=
  fun p => if p = v then (G.degree v : ℝ) else if G.Adj v p then -1 else 0

variable {G}

theorem starVec_self (v : V) : starVec G v v = (G.degree v : ℝ) := by simp [starVec]

theorem starVec_nbr {v u : V} (h : G.Adj v u) : starVec G v u = -1 := by
  have hne : u ≠ v := (G.ne_of_adj h).symm
  simp [starVec, hne, h]

theorem starVec_ne_zero {v : V} (hdeg : 1 ≤ G.degree v) : starVec G v ≠ 0 := by
  intro h0
  have := congrFun h0 v
  rw [starVec_self] at this
  simp only [Pi.zero_apply, Nat.cast_eq_zero] at this
  omega

/-- **`x ⬝ᵥ x = Δ² + Δ`.** One square at `v` and `Δ` ones on the neighbours. -/
theorem dotProduct_starVec_self (v : V) :
    starVec G v ⬝ᵥ starVec G v = (G.degree v : ℝ) ^ 2 + (G.degree v : ℝ) := by
  classical
  rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  rw [starVec_self]
  have hrest : ∑ p ∈ Finset.univ.erase v, starVec G v p * starVec G v p
      = ∑ p ∈ Finset.univ.erase v, (if G.Adj v p then (1 : ℝ) else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    have hpv : p ≠ v := (Finset.mem_erase.mp hp).1
    by_cases hadj : G.Adj v p
    · rw [starVec_nbr hadj]; simp [hadj]
    · simp [starVec, hpv, hadj]
  rw [hrest]
  have hcount : ∑ p ∈ Finset.univ.erase v, (if G.Adj v p then (1 : ℝ) else 0)
      = ∑ p : V, (if G.Adj v p then (1 : ℝ) else 0) := by
    refine Finset.sum_subset (Finset.erase_subset _ _) ?_
    intro p _ hp
    have hpv : p = v := by simpa [Finset.mem_erase] using hp
    subst hpv
    simp
  rw [hcount, ← G.degree_eq_sum_if_adj (R := ℝ) v]
  ring

/-! ## 2. Throwing terms away is free -/

/-- **`Δ(Δ+1)² ≤ xᵀLx`.** The edge sum is a sum of squares, so keeping only the pairs incident to
`v` — the row `i = v` and the column `j = v` — is a lower bound. No edge inside the neighbourhood
is ever counted and no neighbour's degree appears, which is why the item's counting inequality is
not needed. -/
theorem le_quadForm_starVec (v : V) :
    (G.degree v : ℝ) * ((G.degree v : ℝ) + 1) ^ 2
      ≤ starVec G v ⬝ᵥ (G.lapMatrix ℝ) *ᵥ starVec G v := by
  classical
  set x := starVec G v with hx
  set T : V → V → ℝ := fun i j => if G.Adj i j then (x i - x j) ^ 2 else 0 with hT
  have hq : x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x = (∑ i : V, ∑ j : V, T i j) / 2 := by
    rw [← Matrix.toLinearMap₂'_apply']
    exact G.lapMatrix_toLinearMap₂' ℝ x
  have hnn : ∀ i j : V, 0 ≤ T i j := by
    intro i j; by_cases h : G.Adj i j <;> simp [hT, h, sq_nonneg]
  -- the row at `v`
  have hrow : ∑ j : V, T v j = (G.degree v : ℝ) * ((G.degree v : ℝ) + 1) ^ 2 := by
    have hterm : ∀ j : V, T v j = if G.Adj v j then ((G.degree v : ℝ) + 1) ^ 2 else 0 := by
      intro j
      by_cases h : G.Adj v j
      · rw [hT]
        simp only [if_pos h]
        rw [hx, starVec_self, starVec_nbr h]
        ring_nf
      · simp [hT, h]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    have hfac : ∑ j : V, (if G.Adj v j then ((G.degree v : ℝ) + 1) ^ 2 else 0)
        = (∑ j : V, (if G.Adj v j then (1 : ℝ) else 0)) * ((G.degree v : ℝ) + 1) ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by by_cases h : G.Adj v j <;> simp [h]
    rw [hfac, ← G.degree_eq_sum_if_adj (R := ℝ) v]
  -- the column at `v`, over the neighbours
  have hcol : ∑ i ∈ G.neighborFinset v, T i v
      = (G.degree v : ℝ) * ((G.degree v : ℝ) + 1) ^ 2 := by
    have hterm : ∀ i ∈ G.neighborFinset v, T i v = ((G.degree v : ℝ) + 1) ^ 2 := by
      intro i hi
      have h : G.Adj v i := (SimpleGraph.mem_neighborFinset _ _ _).mp hi
      rw [hT]
      simp only [if_pos h.symm]
      rw [hx, starVec_self, starVec_nbr h]
      ring_nf
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
  -- the double sum dominates the row plus the column
  have hsplit : ∑ i : V, ∑ j : V, T i j
      = (∑ j : V, T v j) + ∑ i ∈ Finset.univ.erase v, ∑ j : V, T i j :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro i hi
    have h : G.Adj v i := (SimpleGraph.mem_neighborFinset _ _ _).mp hi
    exact Finset.mem_erase.mpr ⟨(G.ne_of_adj h).symm, Finset.mem_univ i⟩
  have hcolle : ∑ i ∈ G.neighborFinset v, T i v ≤ ∑ i ∈ Finset.univ.erase v, ∑ j : V, T i j := by
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
    · exact Finset.sum_le_sum fun i _ => Finset.single_le_sum (fun j _ => hnn i j)
        (Finset.mem_univ v)
    · exact fun i _ _ => Finset.sum_nonneg fun j _ => hnn i j
  rw [hq, hsplit, hrow]
  rw [hcol] at hcolle
  linarith

/-! ## 3. The bound -/

/-- **`Δ + 1 ≤ ‖G.lapMatrix ℝ‖` AT EVERY VERTEX OF POSITIVE DEGREE**, hence at a vertex of maximum
degree, which is the classical statement. -/
theorem succ_degree_le_norm_lapMatrix (v : V) (hdeg : 1 ≤ G.degree v) :
    (G.degree v : ℝ) + 1 ≤ ‖G.lapMatrix ℝ‖ := by
  have hT : (G.lapMatrix ℝ)ᵀ = G.lapMatrix ℝ := G.isSymm_lapMatrix (R := ℝ)
  refine LaplacianNormLowerBound.le_opNorm_of_le_quadForm hT (starVec_ne_zero hdeg) ?_
  have hle := le_quadForm_starVec (G := G) v
  rw [dotProduct_starVec_self]
  have hd : (1 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hdeg
  nlinarith [hle, hd]

/-- **AND THE SAME FOR THE MASSIVE OPERATOR**, which is the currency the propagator chain is
stated in. -/
theorem succ_degree_add_sq_le_norm_massive (v : V) (hdeg : 1 ≤ G.degree v) (m : ℝ) :
    (G.degree v : ℝ) + 1 + m ^ 2 ≤ ‖massive G m‖ := by
  have hT : (massive G m)ᵀ = massive G m := massive_isSymm G m
  refine LaplacianNormLowerBound.le_opNorm_of_le_quadForm hT (starVec_ne_zero hdeg) ?_
  rw [LaplacianSharpEquality.dotProduct_massive_mulVec, dotProduct_starVec_self]
  have hle := le_quadForm_starVec (G := G) v
  have hd : (1 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hdeg
  nlinarith [hle, hd]

end LaplacianDeltaPlusOne
