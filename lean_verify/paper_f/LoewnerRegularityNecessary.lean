import PrismReflection
import LaplacianLoewnerDisconnected

/-!
# Regularity is necessary in the Loewner statements, and the reason is a three-vertex path

`LaplacianSignless` explains why the sharpness chain's **order** statements keep
`IsRegularOfDegree` when its **equality** statements do not:

> *"Without regularity the bound `massive ≼ c·1` is not governed by a single constant — the
> degree-weighted sum does not collapse — which is why `RegularBipartiteSharp` has only the averaged
> statement. What generalises is the EQUALITY CASE, not the ORDER statement, and the difference is
> exactly the collapse."*

**That is an argument, and until now it was only an argument.** `ConnectivityNecessary` did the same
job for connectivity one unit earlier, and its closing note named this as the next hypothesis whose
necessity was asserted rather than proved. This is that.

> **`regularity_necessary`** — `LaplacianLoewnerDisconnected
> .massive_le_smul_one_iff_exists_component_colorable` with `IsRegularOfDegree Δ` weakened to the
> degree **bound** `∀ p, G.degree p ≤ Δ` is **false**.

**THE WITNESS IS THE ESTATE'S OWN `path3`.** `PrismReflection` built the three-vertex path on
2026-08-2x to show that its prism criterion reaches outside the lattice, and proved
`path3_not_regular` there. Nothing is rebuilt here: this file imports that graph and adds what the
Loewner question needs.

**WHY A DEGREE BOUND IS THE RIGHT WEAKENING TO TEST.** Deleting regularity outright leaves `Δ`
undefined, so the statement does not typecheck; the honest weakening replaces *every degree is `Δ`*
by *every degree is at most `Δ`*, which is what `LaplacianDegreeBound` already uses and what makes
`massive_le_smul_one` general. **The biconditional fails at the first non-regular graph.**

**AND THE NUMBERS SAY EXACTLY WHERE IT FAILS.** `path3` has degrees `1, 2, 1`, so `Δ = 2` and the
regular statement's constant would be `4 + m²`. But `massive path3 m ≼ (3 + m²)·1` — the Laplacian's
largest eigenvalue is `3`, not `2Δ = 4` — while `path3` **is** two-colourable, so the right-hand
side of the biconditional holds. **The constant can be lowered and the colouring exists**: the two
sides disagree, and the gap is `1`, which is exactly `2Δ` minus the true spectral radius.

**THE PSD STEP IS A SUM OF TWO SQUARES AND IS WRITTEN OUT.** `3‖x‖² − xᵀLx` is
`½(2x₀ + x₁)² + ½(2x₂ + x₁)²`, so the bound comes from `nlinarith` on two explicit squares rather
than from any eigenvalue computation. **No spectrum of `path3` is computed in this file**, and
the header's "largest eigenvalue is 3" above is a remark about why `3` is the right constant to try,
not a claim this file proves.

## What this does NOT do

**It does not weaken anything.** `massive_le_smul_one_iff_exists_component_colorable` is untouched
and true; what is refuted is the statement obtained by weakening its hypothesis, which is what
"necessary" means.

**It does not show `3 + m²` is optimal for `path3`.** Only that it is below `4 + m²`, which is all
the refutation needs. The exact Loewner threshold for `path3` is not computed and no cost is claimed
for computing it (`ERRATUM 246`).

**It says nothing about the averaged statement.** `RegularBipartiteSharp`'s averaged form is what
survives without regularity, and this file does not touch it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LoewnerRegularityNecessary

open Matrix SimpleGraph GraphLaplacian PrismReflection
open scoped MatrixOrder

/-! ## 1. `path3` is bipartite and its degrees are bounded by two -/

/-- The alternating vector on the path: it flips sign across both edges. -/
def pvec : Fin 3 → ℝ := ![1, -1, 1]

theorem pvec_ne_zero : pvec ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [pvec] at this

theorem pvec_flip : ∀ u v : Fin 3, path3.Adj u v → pvec v = - pvec u := by
  intro u v h
  fin_cases u <;> fin_cases v <;>
    first
      | exact absurd h (by decide)
      | norm_num [pvec]

/-- **`path3` HAS A TWO-COLOURABLE COMPONENT**, through the same route
`ConnectivityNecessary` used: a sign-flipping vector is one. -/
theorem path3_has_colorable_component :
    ∃ C : path3.ConnectedComponent, (path3.induce C.supp).Colorable 2 :=
  LaplacianSharpDisconnected.exists_component_colorable_of_neg_adj path3 pvec_ne_zero pvec_flip

theorem path3_degree_le : ∀ p : Fin 3, path3.degree p ≤ 2 := by decide

/-! ## 2. But its massive operator is bounded by `3 + m²`, not by `2Δ + m² = 4 + m²` -/

theorem path3_quadForm (x : Fin 3 → ℝ) :
    x ⬝ᵥ (path3.lapMatrix ℝ) *ᵥ x = (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 := by
  have h : x ⬝ᵥ (path3.lapMatrix ℝ) *ᵥ x
      = (∑ i : Fin 3, ∑ j : Fin 3, if path3.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
    rw [← star_trivial x, ← Matrix.toLinearMap₂'_apply', SimpleGraph.lapMatrix_toLinearMap₂']
  rw [h, Fin.sum_univ_three]
  norm_num [Fin.sum_univ_three, path3]
  ring

/-- **`L ≼ 3·1` ON THE PATH**, by two explicit squares and no eigenvalue. -/
theorem lapMatrix_path3_le : path3.lapMatrix ℝ ≤ (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_))
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ?_ (path3.isSymm_lapMatrix (R := ℝ))
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have h1 : x ⬝ᵥ ((3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ x = 3 * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [h1, path3_quadForm, dotProduct, Fin.sum_univ_three]
    nlinarith [sq_nonneg (2 * x 0 + x 1), sq_nonneg (2 * x 2 + x 1)]

theorem massive_path3_le (m : ℝ) :
    massive path3 m ≤ (3 + m ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  have h2 : ((3 + m ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
      = (3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) + Matrix.diagonal (fun _ : Fin 3 => m ^ 2) := by
    rw [add_smul]
    congr 1
    exact Matrix.smul_one_eq_diagonal _
  rw [massive, h2]
  exact add_le_add lapMatrix_path3_le le_rfl

/-! ## 3. So the hypothesis cannot be weakened to a degree bound -/

/-- **REGULARITY IS NECESSARY IN THE LOEWNER STATEMENT.** Weakening `IsRegularOfDegree Δ` to
`∀ p, degree p ≤ Δ` — the weakening `LaplacianDegreeBound` uses everywhere, and the only one under
which the statement still typechecks — makes it false. -/
theorem regularity_necessary :
    ¬ ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W)
        (_ : DecidableRel G.Adj) (_ : Nonempty W) (Δ : ℕ) (_ : ∀ p, G.degree p ≤ Δ) (m : ℝ),
        ((∀ c : ℝ, massive G m ≤ c • (1 : Matrix W W ℝ) → 2 * (Δ : ℝ) + m ^ 2 ≤ c)
          ↔ ∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2) := by
  intro h
  have hiff := h (Fin 3) inferInstance inferInstance path3 inferInstance inferInstance 2
    path3_degree_le 0
  have hle : 2 * ((2 : ℕ) : ℝ) + (0 : ℝ) ^ 2 ≤ 3 + (0 : ℝ) ^ 2 := by
    refine hiff.mpr path3_has_colorable_component (3 + (0 : ℝ) ^ 2) ?_
    exact massive_path3_le 0
  norm_num at hle

end LoewnerRegularityNecessary
