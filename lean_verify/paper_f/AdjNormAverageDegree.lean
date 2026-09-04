import StarAdjNormExact

/-!
# The average degree is also a floor, and neither it nor `√Δ` contains the other

`StarAdjNormExact.le_sqrt_of_universal_degree_bound` proves that **no function of the degree alone**
beats `√(deg v)` as a lower bound on `‖G.adjMatrix ℝ‖`, and that file fences the result carefully:

> *"Not optimality among bounds of a different form. §5 rules out better functions of the degree
> alone. A bound reading the degree and something else — the vertex count, the second-largest
> degree, connectivity — is untouched by it."*

**This file makes that fence a theorem instead of a caveat.** The average degree is such a bound —
it reads every degree and the vertex count — and it is a floor:

```
(∑ v, deg v) / card V ≤ ‖G.adjMatrix ℝ‖        every finite nonempty graph
2 · |E| / card V      ≤ ‖G.adjMatrix ℝ‖        the same, by the degree-sum formula
```

from the all-ones vector, whose Rayleigh quotient is exactly the average degree.

## And the two floors are genuinely incomparable, in both directions, with witnesses

**On a regular graph the average beats the root.** Every degree is `Δ`, so the average IS `Δ`, and
`√Δ < Δ` as soon as `Δ ≥ 2` — `sqrt_lt_avg_of_regular`. On such a graph `AdjNormRegular` says the
average-degree floor is not merely better but **exact**.

**On a star the root beats the average.** The star on `n + 1` vertices has `2n` total degree, so its
average is `2n/(n+1) < 2`, while `√(deg centre) = √n` grows without bound —
`avg_lt_sqrt_star`, at `n ≥ 4`.

`neither_floor_contains_the_other` states both at once. So the optimality proved yesterday is
**exactly as strong as it says and no stronger**, and that is now checkable rather than asserted.

## Why this is worth a file

The earlier units in this chain each produced a bound or a value. This one produces neither: it
exhibits the *limits of a quantifier*. **A statement that a bound is optimal is only as informative
as the class of competitors it ranges over**, and yesterday's optimality ranges over functions of
the degree alone — a restriction stated in that file's own header and, until now, taken on trust.
Here it is witnessed by counterexample in both directions, so a reader can see the boundary rather
than reconstruct it.

## What is NOT here

**Not a best floor.** Neither bound is optimal among *all* floors — the maximum of the two is a
better floor than either, trivially, and nothing here says what the optimal one is.

**And not a claim that `‖A‖` is the top eigenvalue.** `RayleighVariational.isGreatest_rayleigh`
characterises `topEigen` variationally, but that is the largest eigenvalue, while `‖A‖` is the
largest eigenvalue *in absolute value*. For an adjacency matrix the two coincide — a nonnegative
matrix's Perron root dominates — and **this estate does not prove that**:
`OpNormTopEigenvalue.isGreatest_eigenvalue_opNorm` needs `0 ≤ A`, which an adjacency matrix is not.
So every bound in this chain is a floor on the NORM, and reading it as a floor on the top
eigenvalue borrows a fact from Perron–Frobenius that is not here (`ERRATUM 246`: not attempted,
not costed).

**Not a bound on the second eigenvalue**, which is what the Ising sub-top-ratio item needs and what
no file in this chain touches.

**Not `2|E|/card V ≤ Δ`.** That the average degree is at most the maximum degree is true and is not
proved here; it is not needed, since the incomparability is witnessed at the level of the FLOORS,
not of the quantities they bound.

**No wall moves.** `W1`'s open part is `OS0`/`OS1`/`OS4` (`ERRATUM 441`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace AdjNormAverageDegree

open Matrix Finset SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The all-ones vector's Rayleigh quotient is the average degree -/

omit [DecidableEq V] in
/-- `A *ᵥ 1` is the degree sequence. -/
theorem adjMatrix_mulVec_one (v : V) :
    ((G.adjMatrix ℝ) *ᵥ (fun _ : V => (1 : ℝ))) v = (G.degree v : ℝ) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, mul_one]

omit [DecidableEq V] in
/-- **`1ᵀA1 = ∑ deg v`**, the degree sum. -/
theorem quadForm_one :
    (fun _ : V => (1 : ℝ)) ⬝ᵥ ((G.adjMatrix ℝ) *ᵥ (fun _ : V => (1 : ℝ)))
      = ∑ v : V, (G.degree v : ℝ) := by
  rw [dotProduct]
  exact Finset.sum_congr rfl fun v _ => by rw [adjMatrix_mulVec_one G v, one_mul]

omit [DecidableEq V] in
/-- `1ᵀ1 = card V`. -/
theorem dotProduct_one_one :
    (fun _ : V => (1 : ℝ)) ⬝ᵥ (fun _ : V => (1 : ℝ)) = (Fintype.card V : ℝ) := by
  rw [dotProduct]
  simp [Finset.card_univ]

omit [Fintype V] [DecidableEq V] in
theorem one_ne_zero_fun [Nonempty V] : (fun _ : V => (1 : ℝ)) ≠ (0 : V → ℝ) := by
  intro h
  have := congrFun h (Classical.arbitrary V)
  simp at this

/-! ## 2. The floor -/

/-- **`(∑ deg v)/card V ≤ ‖G.adjMatrix ℝ‖` AT EVERY FINITE NONEMPTY GRAPH.** The all-ones vector's
Rayleigh quotient is exactly the average degree, so one witness gives the bound — no regularity,
no connectivity. -/
theorem avg_degree_le_norm_adjMatrix [Nonempty V] :
    (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ) ≤ ‖G.adjMatrix ℝ‖ := by
  have hT : (G.adjMatrix ℝ)ᵀ = G.adjMatrix ℝ := G.transpose_adjMatrix (α := ℝ)
  refine LaplacianNormLowerBound.le_opNorm_of_le_quadForm hT (one_ne_zero_fun (V := V)) ?_
  rw [dotProduct_one_one (V := V), quadForm_one]
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty V›
  rw [div_mul_cancel₀ _ (ne_of_gt hcard)]

/-- **The same in edges**: `2|E|/card V ≤ ‖A‖`, by the degree-sum formula. -/
theorem two_card_edges_div_le_norm_adjMatrix [Nonempty V] :
    2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ) ≤ ‖G.adjMatrix ℝ‖ := by
  have h := avg_degree_le_norm_adjMatrix G
  have hsum : (∑ v : V, (G.degree v : ℝ)) = 2 * (G.edgeFinset.card : ℝ) := by
    have := G.sum_degrees_eq_twice_card_edges
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  rwa [hsum] at h

/-! ## 3. On a regular graph the average floor beats the root -/

omit [DecidableEq V] in
/-- On a `Δ`-regular graph the average degree IS `Δ`. -/
theorem avg_degree_of_regular [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ) = (Δ : ℝ) := by
  have hcard : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty V›
  have hsum : (∑ v : V, (G.degree v : ℝ)) = (Fintype.card V : ℝ) * (Δ : ℝ) := by
    rw [Finset.sum_congr rfl fun v _ => by rw [hreg v], Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hsum, mul_comm, mul_div_assoc, div_self (ne_of_gt hcard), mul_one]

omit [DecidableEq V] in
/-- **`√Δ < (∑ deg)/card V` on a `Δ`-regular graph with `Δ ≥ 2`.** The average floor is strictly
better there, and `AdjNormRegular.norm_adjMatrix_eq_of_regular` says it is in fact exact. -/
theorem sqrt_lt_avg_of_regular [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hΔ : 2 ≤ Δ) :
    Real.sqrt Δ < (∑ v : V, (G.degree v : ℝ)) / (Fintype.card V : ℝ) := by
  rw [avg_degree_of_regular G hreg]
  have h2 : (2 : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ
  have hnn : (0 : ℝ) ≤ (Δ : ℝ) := by linarith
  have hsq : Real.sqrt Δ ^ 2 = (Δ : ℝ) := Real.sq_sqrt hnn
  nlinarith [Real.sqrt_nonneg (Δ : ℝ), hsq, h2]

/-! ## 4. On a star the root beats the average floor -/

/-- The star on `n + 1` vertices has total degree `2n`: `n` at the centre and one at each leaf. -/
theorem sum_degrees_star (n : ℕ) :
    ∑ v : Fin (n + 1), (StarAdjNormExact.starGraph (0 : Fin (n + 1))).degree v = 2 * n := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (n + 1)))]
  rw [StarAdjNormExact.degree_centre_fin n]
  have hleaf : ∀ v ∈ Finset.univ.erase (0 : Fin (n + 1)),
      (StarAdjNormExact.starGraph (0 : Fin (n + 1))).degree v = 1 := by
    intro v hv
    exact StarAdjNormExact.degree_leaf (Finset.mem_erase.mp hv).1
  rw [Finset.sum_congr rfl hleaf, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel, smul_eq_mul, mul_one]
  ring

/-- **`(∑ deg)/card V < √(deg centre)` on the star at `n ≥ 4`.** The average is `2n/(n+1) < 2`
while the root at the centre is `√n ≥ 2`, so the root floor is strictly better there. -/
theorem avg_lt_sqrt_star (n : ℕ) (hn : 4 ≤ n) :
    (∑ v : Fin (n + 1), ((StarAdjNormExact.starGraph (0 : Fin (n + 1))).degree v : ℝ))
        / (Fintype.card (Fin (n + 1)) : ℝ)
      < Real.sqrt ((StarAdjNormExact.starGraph (0 : Fin (n + 1))).degree 0) := by
  have hsum : (∑ v : Fin (n + 1),
      ((StarAdjNormExact.starGraph (0 : Fin (n + 1))).degree v : ℝ)) = 2 * (n : ℝ) := by
    have := sum_degrees_star n
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) this
  rw [hsum, Fintype.card_fin, StarAdjNormExact.degree_centre_fin n]
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have h2 : (2 : ℝ) ≤ Real.sqrt n := by
    nlinarith [Real.sqrt_nonneg (n : ℝ), hsq, hn4]
  have havg : 2 * (n : ℝ) / ((n : ℝ) + 1) < 2 := by
    rw [div_lt_iff₀ hpos]
    linarith
  push_cast
  linarith

/-! ## 5. Neither floor contains the other -/

/-- **THE FENCE `StarAdjNormExact` WROTE, AS A THEOREM.** There is a graph where the average-degree
floor is strictly better than the degree-root floor, and a graph where the reverse holds. So
`le_sqrt_of_universal_degree_bound`'s optimality is **exactly as strong as its quantifier**: `√` is
unbeatable among functions of the degree alone, and beaten by a function that reads more. -/
theorem neither_floor_contains_the_other :
    (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (_ : Nonempty W) (H : SimpleGraph W)
        (_ : DecidableRel H.Adj) (v : W),
        Real.sqrt (H.degree v)
          < (∑ u : W, (H.degree u : ℝ)) / (Fintype.card W : ℝ))
    ∧ (∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (_ : Nonempty W) (H : SimpleGraph W)
        (_ : DecidableRel H.Adj) (v : W),
        (∑ u : W, (H.degree u : ℝ)) / (Fintype.card W : ℝ)
          < Real.sqrt (H.degree v)) := by
  classical
  constructor
  · -- the 2-regular triangle
    refine ⟨Fin 3, inferInstance, inferInstance, inferInstance, ⊤, inferInstance, 0, ?_⟩
    have hreg : (⊤ : SimpleGraph (Fin 3)).IsRegularOfDegree 2 := by
      have h := SimpleGraph.IsRegularOfDegree.top (V := Fin 3)
      rwa [Fintype.card_fin] at h
    have hdeg : (⊤ : SimpleGraph (Fin 3)).degree 0 = 2 := hreg 0
    rw [hdeg]
    exact sqrt_lt_avg_of_regular (⊤ : SimpleGraph (Fin 3)) hreg le_rfl
  · -- the star on five vertices
    exact ⟨Fin 5, inferInstance, inferInstance, inferInstance,
      StarAdjNormExact.starGraph (0 : Fin 5), inferInstance, 0, avg_lt_sqrt_star 4 le_rfl⟩

end AdjNormAverageDegree
