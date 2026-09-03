import NeumannTailBound

/-!
# The tail constant was crude in one factor, and the factor has an exact value

`NeumannTailBound.norm_neumann_tail_le` bounds the Neumann tail by `Δ²/(m²)³`, through five factor
bounds. **One of them throws away everything Mathlib gives.** `Matrix.l2_opNorm_diagonal` is an
**equality** — the operator norm of a diagonal matrix *is* the sup-norm of its diagonal — and
`norm_Dinv_le` extracts from it only `‖Dinv G m‖ ≤ (m²)⁻¹`, which is the value at degree **zero**.
The diagonal of `Dinv` is `(deg p + m²)⁻¹`, decreasing in the degree, so its supremum sits at the
**smallest** degree, and every vertex of positive degree makes the used bound strictly loose.

```
‖Dinv G m‖ ≤ (δ + m²)⁻¹                         whenever δ ≤ deg p for all p
‖tail‖     ≤ Δ² / (m² · (δ + m²)²)              in place of  Δ² / (m²)³
```

and on a `Δ`-regular graph the first is an **equality**, `‖Dinv G m‖ = (Δ + m²)⁻¹`.

**On the periodic lattice** — `2d`-regular at side length ≥ 3 — the tail constant improves from
`4d²/(m²)³` to `4d²/(m² (2d + m²)²)`, a factor of `(m²/(2d + m²))²`, which for small mass is the
whole content of the bound.

## What this does and does not touch

**It does not change any existing statement.** `norm_neumann_tail_le` and `norm_sub_two_terms_le`
keep their constants and their consumers (`ERRATUM 337`); this file adds the sharper forms beside
them, with the minimum degree as an extra hypothesis, and derives them the same way.

**IT WOULD SHARPEN THE W1 CHAIN'S THRESHOLD AND THAT IS NOT DONE HERE.**
`ReflectionFailureCriterion.remainder_le` carries `Δ²/(m²)³` into
`reflectedForm_neg_of_crossForm_gt` and thence into
`CrossBlockTopEigenvalue.topEigen_twistedCross_le`, so every one of those thresholds is loose by the
same factor on a graph with no isolated vertex. **Threading it through is a separate unit and is
not attempted as of 2026-09-03**, with no cost claimed (`ERRATUM 246`) and no estimate offered
(`ERRATUM 194`). Sharpening a *necessary*
condition makes it harder to satisfy and so **strengthens** those statements; it moves no wall,
because `W1`'s open part is `OS0`/`OS1`/`OS4` (`ERRATUM 441`).

**It is not the exact tail norm.** Two of the five factors stay inequalities: `‖adjMatrix‖ ≤ Δ` is
the adjacency spectral radius bounded by the maximum degree, not computed, and the product bound
`Matrix.l2_opNorm_mul` is an inequality for any non-commuting pair. Only `‖green‖` — exactly
`(m²)⁻¹`, `GreenNormExact.norm_green_eq` — and now `‖Dinv‖` are exact.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace NeumannTailSharper

open Matrix GraphLaplacian GreenExpansion
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The diagonal factor, at the minimum degree -/

/-- **`‖Dinv G m‖ ≤ (δ + m²)⁻¹` WHEN EVERY DEGREE IS AT LEAST `δ`.** The mirror of
`NeumannTailBound.norm_Dinv_le`, which is this at `δ = 0`. -/
theorem norm_Dinv_le_of_min_degree {δ m : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ p : V, δ ≤ (G.degree p : ℝ)) (hm : m ≠ 0) :
    ‖Dinv G m‖ ≤ (δ + m ^ 2)⁻¹ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hδm : (0 : ℝ) < δ + m ^ 2 := by linarith
  rw [Dinv, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  have hp : (0 : ℝ) < (G.degree p : ℝ) + m ^ 2 := by
    have := hδ p; linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  exact inv_anti₀ hδm (by have := hδ p; linarith)

/-- **AND ON A `Δ`-REGULAR GRAPH IT IS AN EQUALITY**, because the diagonal is constant. -/
theorem norm_Dinv_eq_of_regular [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) {m : ℝ}
    (hm : m ≠ 0) : ‖Dinv G m‖ = ((Δ : ℝ) + m ^ 2)⁻¹ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hΔm : (0 : ℝ) < (Δ : ℝ) + m ^ 2 := by positivity
  have hconst : (fun p : V => ((G.degree p : ℝ) + m ^ 2)⁻¹)
      = fun _ : V => ((Δ : ℝ) + m ^ 2)⁻¹ := by
    ext p
    rw [hreg p]
  rw [Dinv, Matrix.l2_opNorm_diagonal, hconst, pi_norm_const,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΔm)]

/-! ## 2. The tail, with the sharper factor -/

/-- **THE TAIL AT THE MINIMUM DEGREE.** `NeumannTailBound.norm_neumann_tail_le` is this at
`δ = 0`, and every vertex of positive degree makes that one strictly loose. -/
theorem norm_neumann_tail_le_of_min_degree [Nonempty V] {δ Δ m : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ p : V, δ ≤ (G.degree p : ℝ)) (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) :
    ‖green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m‖
      ≤ Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hδm : (0 : ℝ) < δ + m ^ 2 := by linarith
  have hG := LaplacianOpNorm.norm_green_le G hm
  have hA := SymmetricOpNorm.norm_adjMatrix_le G hΔ
  have hD := norm_Dinv_le_of_min_degree G hδ0 hδ hm
  have hΔ0 : 0 ≤ Δ := le_trans (Nat.cast_nonneg _) (hΔ (Classical.arbitrary V))
  have hstep : ‖green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m‖
      ≤ ((((m ^ 2)⁻¹ * Δ) * (δ + m ^ 2)⁻¹) * Δ) * (δ + m ^ 2)⁻¹ := by
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    refine mul_le_mul ?_ hD (norm_nonneg _) (by positivity)
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    refine mul_le_mul ?_ hA (norm_nonneg _) (by positivity)
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    refine mul_le_mul ?_ hD (norm_nonneg _) (by positivity)
    exact le_trans (Matrix.l2_opNorm_mul _ _) (mul_le_mul hG hA (norm_nonneg _) (by positivity))
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **THE SAME WITH THE PRODUCT NAMED**, mirroring `NeumannTailBound.norm_sub_two_terms_le`. -/
theorem norm_sub_two_terms_le_of_min_degree [Nonempty V] {δ Δ m : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ p : V, δ ≤ (G.degree p : ℝ)) (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) :
    ‖green G m - (Dinv G m + Dinv G m * G.adjMatrix ℝ * Dinv G m)‖
      ≤ Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) := by
  have h := GreenExpansion.green_eq_two_terms (G := G) (m := m) hm
  have hid : green G m - (Dinv G m + Dinv G m * G.adjMatrix ℝ * Dinv G m)
      = green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m := by
    conv_lhs => rw [h]
    abel
  rw [hid]
  exact norm_neumann_tail_le_of_min_degree G hδ0 hδ hΔ hm

end NeumannTailSharper
