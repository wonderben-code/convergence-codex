import SymmetricOpNorm
import GreenExpansion

/-!
# The Neumann tail, bounded — and the wall still asks for something else

`WALLS.md`'s W1 block states its remaining need in its own words: *"a bound on the **Neumann tail of
the Green function**, of which `green_eq_two_terms` is now the exact closed form."* That tail is
`green · A · Dinv · A · Dinv`. This file bounds it.

**⚠ THE LAST SENTENCE READS AS A FIRST AND IS NOT ONE; THE PARAGRAPH IS KEPT AS WRITTEN**
(`ERRATUM 94`, **`ERRATUM 427`**). `GreenLargeMass.generalRemainder_abs_le` bounds **the same
matrix** entrywise, **by the same constant `Δ²/(m²)³`**, at the same generality and with no
regularity — and did so before this file existed. What is new here is the currency, an operator norm
where that is an entrywise bound. **`paper_f/EntrywiseFromOpNorm.lean` folds it back by proving
more**: `|M x q| ≤ ‖M‖`, so this file's bound IMPLIES that one with the same constant, on a nonempty
vertex type — which is the hypothesis this route carries and that one does not.

**IT COSTS NOTHING NEW.** Each factor already has a norm bound: `LaplacianOpNorm.norm_green_le`
gives `‖green G m‖ ≤ (m²)⁻¹`, `SymmetricOpNorm.norm_adjMatrix_le` gives `‖G.adjMatrix ℝ‖ ≤ Δ`, and
`norm_Dinv_le` below reads `‖Dinv G m‖ ≤ (m²)⁻¹` straight off `Matrix.l2_opNorm_diagonal`, since
every diagonal entry is `(deg p + m²)⁻¹ ≤ (m²)⁻¹`. Submultiplicativity does the rest, so the whole
of §2 is bookkeeping over four applications of `Matrix.l2_opNorm_mul`.

**WHAT IT SETTLES, AND IT IS SMALLER THAN IT LOOKS.**
* **The bound does not see the volume.** `Δ² / (m²)³` names a degree bound and a mass and nothing
  else, so on `boxGraph d n` it is `4d² / m⁶` **at every side length** — which is the property this
  chain has been chasing everywhere else.
* **AND IT IS ONLY AN IMPROVEMENT IN A LARGE-MASS REGIME, WHICH IS SAID HERE RATHER THAN LEFT TO BE
  DISCOVERED.** `‖green‖ ≤ (m²)⁻¹` bounds the whole of `green` already, so a tail bound is worth
  having only when it beats that: `Δ² / (m²)³ < (m²)⁻¹` exactly when `Δ < m²`
  (`tail_lt_green_bound_of_lt`). **That is the same threshold `LaplacianOpNorm`'s Neumann criterion
  produced**, arrived at along a different route, which is a check on both.

**WHAT IT IS NOT, AND THIS IS THE SENTENCE THAT MATTERS.** **W1 DOES NOT MOVE.** The wall asks for
the tail to be **smaller than the cross form's negative direction** — a COMPARISON — and nothing
here computes a cross form or compares anything to one. **A bound is not the comparison.** What has
changed is that the wall's `WHAT WOULD HAVE TO EXIST` is now half-answered in a checkable way: the
quantity it names has an explicit, volume-free bound, and what is still missing is a LOWER bound on
the other side. That is a sharper statement of the same gap and not a step across it — not
attempted, not costed (`ERRATUM 246`), not estimated (`ERRATUM 183`).

**Nothing here is sharp.** `‖adjMatrix‖ ≤ Δ` is the standard degree bound, `‖Dinv‖ ≤ (m²)⁻¹`
discards every degree, and submultiplicativity is lossy at every step. No claim of sharpness is
made and no loss is quantified. **No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace NeumannTailBound

open Matrix GraphLaplacian GreenExpansion
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The reciprocal diagonal -/

/-- **`‖Dinv G m‖ ≤ (m²)⁻¹`.** `Matrix.l2_opNorm_diagonal` turns the operator norm of a diagonal
matrix into the supremum of its entries, and every entry is `(deg p + m²)⁻¹ ≤ (m²)⁻¹` because the
degree is non-negative. **No positivity theorem is needed and `V` may be empty.** -/
theorem norm_Dinv_le {m : ℝ} (hm : m ≠ 0) : ‖Dinv G m‖ ≤ (m ^ 2)⁻¹ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  rw [Dinv, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p => ?_
  have hp : (0 : ℝ) < (G.degree p : ℝ) + m ^ 2 := by
    have : (0 : ℝ) ≤ (G.degree p : ℝ) := Nat.cast_nonneg _
    linarith
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
  exact inv_anti₀ hm2 (by have : (0 : ℝ) ≤ (G.degree p : ℝ) := Nat.cast_nonneg _; linarith)

/-! ## 2. The tail -/

/-- **THE BOUND W1 ASKS FOR**: the tail of `GreenExpansion.green_eq_two_terms` has operator norm at
most `Δ² / (m²)³`, which names a degree bound and a mass and **not the number of vertices**. Four
applications of `Matrix.l2_opNorm_mul` over three factor bounds already proved elsewhere. -/
theorem norm_neumann_tail_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ}
    (hm : m ≠ 0) :
    ‖green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m‖
      ≤ Δ ^ 2 / (m ^ 2) ^ 3 := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hG := LaplacianOpNorm.norm_green_le G hm
  have hA := SymmetricOpNorm.norm_adjMatrix_le G hΔ
  have hD := norm_Dinv_le G hm
  have hΔ0 : 0 ≤ Δ := le_trans (Nat.cast_nonneg _) (hΔ (Classical.arbitrary V))
  have hstep : ‖green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m‖
      ≤ ((((m ^ 2)⁻¹ * Δ) * (m ^ 2)⁻¹) * Δ) * (m ^ 2)⁻¹ := by
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    refine mul_le_mul ?_ hD (norm_nonneg _) (by positivity)
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    refine mul_le_mul ?_ hA (norm_nonneg _) (by positivity)
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    refine mul_le_mul ?_ hD (norm_nonneg _) (by positivity)
    exact le_trans (Matrix.l2_opNorm_mul _ _) (mul_le_mul hG hA (norm_nonneg _) (by positivity))
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **WHAT THE TAIL BOUND ACTUALLY SAYS**, with the anonymous product replaced by the quantity it
measures: `Dinv + Dinv · A · Dinv` approximates the propagator to within `Δ² / (m²)³`, **uniformly
in the number of vertices**. This is also the check that §2's product is the right one — it is
`GreenExpansion.green_eq_two_terms` rearranged, so Lean and not the reader confirms that the term
bounded above is that theorem's tail. -/
theorem norm_sub_two_terms_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ}
    (hm : m ≠ 0) :
    ‖green G m - (Dinv G m + Dinv G m * G.adjMatrix ℝ * Dinv G m)‖ ≤ Δ ^ 2 / (m ^ 2) ^ 3 := by
  have h := GreenExpansion.green_eq_two_terms (G := G) (m := m) hm
  have hid : green G m - (Dinv G m + Dinv G m * G.adjMatrix ℝ * Dinv G m)
      = green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m := by
    conv_lhs => rw [h]
    abel
  rw [hid]
  exact norm_neumann_tail_le G hΔ hm

/-! ## 3. The regime in which the bound is worth having -/

/-- **THE TAIL BOUND BEATS THE TRIVIAL ONE EXACTLY WHEN `Δ < m²`.** `‖green‖ ≤ (m²)⁻¹` already
bounds the whole propagator, so a tail bound earns its place only below that number. **This is the
same threshold `LaplacianOpNorm.norm_lapMatrix_lt_of_lt` produces from the Neumann convergence
criterion**, reached by a different route — a check on both, and not a coincidence, since `2Δ` and
`Δ` differ only by the factor the two routes count edges with. -/
theorem tail_lt_green_bound_of_lt {Δ : ℝ} (hΔ0 : 0 ≤ Δ) {m : ℝ} (hm : m ≠ 0) (hlt : Δ < m ^ 2) :
    Δ ^ 2 / (m ^ 2) ^ 3 < (m ^ 2)⁻¹ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hsq : Δ ^ 2 < (m ^ 2) ^ 2 := by nlinarith [hΔ0, hlt, hm2]
  rw [div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ hm2]
  calc Δ ^ 2 * m ^ 2 < (m ^ 2) ^ 2 * m ^ 2 := mul_lt_mul_of_pos_right hsq hm2
    _ = (m ^ 2) ^ 3 := by ring

end NeumannTailBound
