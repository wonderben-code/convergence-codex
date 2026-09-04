import LaplacianOpNorm
import LaplacianSignlessDefinite

/-!
# A two-sided Loewner bound is a norm bound, and the adjacency matrix gets one

`PosSemidefNormBound.l2_opNorm_le` needs `0 ≤ A`. `LaplacianOpNorm`'s header records the price of
that hypothesis in the one place it bites: the third factor of W1's Neumann tail is
`‖G.adjMatrix ℝ‖`, and **an adjacency matrix has negative directions**, so that theorem does not
reach it. This file removes the hypothesis and then reaches it.

> **THE OBSERVATION, AND IT COSTS NO NEW MACHINERY.** If `−r • 1 ≼ A ≼ r • 1` then `B := A + r • 1`
> satisfies `0 ≼ B ≼ 2r • 1`, so `PosSemidefNormBound.sq_le_smul_of_le_smul_one` gives
> `B·B ≼ 2r·B`. Substituting `B = A + r • 1` and cancelling, **every term in `A` disappears** and
> what is left is `A·A ≼ r² • 1`. **Yesterday's conjugation argument is doing all the work, one
> translation away.**

**AND SYMMETRY IS NOT A HYPOTHESIS HERE.** `isHermitian_of_abs_le`: `A ≼ r • 1` already says
`r • 1 − A` is positive semidefinite, and a positive semidefinite matrix is Hermitian, so `A` is.
The two-sided statement therefore needs no `Aᵀ = A` and does not ask for one.

**WHAT IT SUBSUMES, SAID PLAINLY RATHER THAN LEFT TO BE NOTICED.** `l2_opNorm_le_of_abs_le`
**implies** `PosSemidefNormBound.l2_opNorm_le`: a positive semidefinite `A` below `r • 1` is above
`−r • 1` for free, and §4 proves that implication rather than asserting it. The older theorem is
**kept and not deleted** (`ERRATUM 94`, `ERRATUM 176`): three files cite it, its hypothesis is the
natural one at each of them, and a caller who has `0 ≤ A` should not have to produce a lower bound
it does not care about.

**WHAT THIS IS NOT.**
* **It is not W1's step, and it is not even the tail bound.** §5 supplies the third factor of
  `GreenExpansion.green_eq_two_terms`'s tail; the product of the three is not formed here, and the
  wall asks for a COMPARISON — the tail against the cross form's negative direction — which nothing
  in this file computes. **A factor is not the bound and a bound is not the comparison**, exactly as
  `LaplacianOpNorm` says of its own factor.
* **It is not sharp and does not claim to be.** `‖G.adjMatrix ℝ‖ ≤ Δ` is the standard degree bound
  on the spectral radius; nothing here says it is attained, and the graphs where it is are not
  identified (not attempted, not costed — `ERRATUM 246`).

  **⚠ A CLASS IS IDENTIFIED SINCE 2026-09-03 AND THE BULLET IS KEPT AS WRITTEN** (`ERRATUM 94`).
  `AdjNormRegular.norm_adjMatrix_eq_of_regular`: on a `Δ`-regular graph with a vertex the bound is
  an **equality**, because the all-ones vector is an eigenvector at `Δ`; the periodic lattice is
  the instance. **The bullet stays true off that class** — on the star `K_{1,n}` the norm is `√n`
  against `Δ = n` — and the converse, that a *connected* graph attaining it must be regular, is
  classical Perron–Frobenius and is still **not proved here**.

  **⚠ AND SINCE 2026-09-04 THE BOUND IS TWO-SIDED** (`ERRATUM 94`).
  `AdjNormSqrtDegree.sqrt_degree_le_norm_adjMatrix` gives `√(deg v) ≤ ‖A‖` at every vertex of every
  finite graph — no regularity, no connectivity — so read at a maximum-degree vertex this bullet's
  `‖A‖ ≤ Δ` is bracketed from below by `√Δ`. **The bullet still stands**: `√Δ` is not `Δ`, the gap
  is the whole distance between the star and the regular class, and neither endpoint says which
  graphs attain the upper one.

  **⚠⚠ AND THE STAR IN THIS BULLET IS NOW A THEOREM, LATER THE SAME DAY** (`ERRATUM 94`).
  `StarAdjNormExact.norm_adjMatrix_starGraph_eq`: `‖A‖ = √(card V − 1)` on the star, and
  `norm_lt_degree`: `‖A‖ < Δ` strictly once it has two leaves. **This bullet's own example stopped
  being an assertion and became a computation**, and that file's
  `le_sqrt_of_universal_degree_bound` shows the star forces `√` on any bound written as a function
  of the degree alone. **The bullet
  still stands where it stands**: it says the graphs ATTAINING `‖A‖ = Δ` are not identified, and
  they are still not — a graph where the bound fails is not a characterisation of where it holds.
* **No wall moves and no published tag moves.** No measure, no limit, no compactness.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SymmetricOpNorm

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Symmetry comes free with the upper bound -/

omit [Fintype V] in
/-- **A MATRIX BELOW `r • 1` IS ALREADY HERMITIAN.** `r • 1 − A` is positive semidefinite and a
positive semidefinite matrix is Hermitian, so `A = r • 1 − (r • 1 − A)` is too. -/
theorem isHermitian_of_abs_le {A : Matrix V V ℝ} {r : ℝ}
    (hhi : A ≤ r • (1 : Matrix V V ℝ)) : A.IsHermitian := by
  have h := (Matrix.le_iff.mp hhi).isHermitian
  have hone : (r • (1 : Matrix V V ℝ)).IsHermitian := by
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isHermitian_diagonal_iff.mpr fun _ => isSelfAdjoint_iff.mpr rfl
  have : A = r • (1 : Matrix V V ℝ) - (r • (1 : Matrix V V ℝ) - A) := by abel
  rw [this]
  exact hone.sub h

/-! ## 2. The square bound, from the positive semidefinite case by one translation -/

/-- **`−r • 1 ≼ A ≼ r • 1` GIVES `A·A ≼ r² • 1`.** The translate `A + r • 1` is positive
semidefinite and below `2r • 1`, so `PosSemidefNormBound.sq_le_smul_of_le_smul_one` applies to it,
and expanding the conclusion leaves no term in `A`. -/
theorem sq_le_smul_one_of_abs_le {A : Matrix V V ℝ} {r : ℝ}
    (hlo : -(r • (1 : Matrix V V ℝ)) ≤ A) (hhi : A ≤ r • (1 : Matrix V V ℝ)) :
    A * A ≤ (r * r) • (1 : Matrix V V ℝ) := by
  have hB0 : (0 : Matrix V V ℝ) ≤ A + r • (1 : Matrix V V ℝ) := by
    refine Matrix.le_iff.mpr ?_
    have h := Matrix.le_iff.mp hlo
    have hid : A - -(r • (1 : Matrix V V ℝ)) = A + r • (1 : Matrix V V ℝ) - 0 := by abel
    rwa [hid] at h
  have hB1 : A + r • (1 : Matrix V V ℝ) ≤ (2 * r) • (1 : Matrix V V ℝ) := by
    refine Matrix.le_iff.mpr ?_
    have h := Matrix.le_iff.mp hhi
    have hid : r • (1 : Matrix V V ℝ) - A
        = (2 * r) • (1 : Matrix V V ℝ) - (A + r • (1 : Matrix V V ℝ)) := by module
    rwa [hid] at h
  have hsq := PosSemidefNormBound.sq_le_smul_of_le_smul_one hB0 hB1
  refine Matrix.le_iff.mpr ?_
  have h := Matrix.le_iff.mp hsq
  have hexp : (2 * r) • (A + r • (1 : Matrix V V ℝ))
      - (A + r • (1 : Matrix V V ℝ)) * (A + r • (1 : Matrix V V ℝ))
      = (r * r) • (1 : Matrix V V ℝ) - A * A := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  rwa [hexp] at h

/-! ## 3. The norm bound -/

/-- **`−r • 1 ≼ A ≼ r • 1` GIVES `‖A‖ ≤ r`**, with no positivity hypothesis. `A` is symmetric by
§1, so `‖A x‖²` is the quadratic form of `A·A`, which §2 bounds by `r²` times the squared length. -/
theorem l2_opNorm_le_of_abs_le [Nonempty V] {A : Matrix V V ℝ} {r : ℝ}
    (hlo : -(r • (1 : Matrix V V ℝ)) ≤ A) (hhi : A ≤ r • (1 : Matrix V V ℝ)) : ‖A‖ ≤ r := by
  have hT : Aᵀ = A := by
    have h := isHermitian_of_abs_le hhi
    simpa [Matrix.conjTranspose, Matrix.map] using h
  have hr : 0 ≤ r := by
    have h0 : (0 : Matrix V V ℝ) ≤ A + r • (1 : Matrix V V ℝ) := by
      refine Matrix.le_iff.mpr ?_
      have h := Matrix.le_iff.mp hlo
      have hid : A - -(r • (1 : Matrix V V ℝ)) = A + r • (1 : Matrix V V ℝ) - 0 := by abel
      rwa [hid] at h
    have h1 : A + r • (1 : Matrix V V ℝ) ≤ (2 * r) • (1 : Matrix V V ℝ) := by
      refine Matrix.le_iff.mpr ?_
      have h := Matrix.le_iff.mp hhi
      have hid : r • (1 : Matrix V V ℝ) - A
          = (2 * r) • (1 : Matrix V V ℝ) - (A + r • (1 : Matrix V V ℝ)) := by module
      rwa [hid] at h
    have := PosSemidefNormBound.nonneg_of_le_smul_one h0 h1
    linarith
  have hsq := sq_le_smul_one_of_abs_le hlo hhi
  rw [← Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) A]
  refine ContinuousLinearMap.opNorm_le_bound _ hr fun x => ?_
  have hsplit : (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) = x.ofLp ⬝ᵥ (A * A) *ᵥ x.ofLp := by
    calc (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp)
        = (Aᵀ *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by rw [hT]
      _ = (x.ofLp ᵥ* A) ⬝ᵥ (A *ᵥ x.ofLp) := by rw [Matrix.mulVec_transpose]
      _ = x.ofLp ⬝ᵥ A *ᵥ (A *ᵥ x.ofLp) := (Matrix.dotProduct_mulVec x.ofLp A (A *ᵥ x.ofLp)).symm
      _ = x.ofLp ⬝ᵥ (A * A) *ᵥ x.ofLp := by rw [Matrix.mulVec_mulVec]
  have hbound : x.ofLp ⬝ᵥ (A * A) *ᵥ x.ofLp ≤ (r * r) * (x.ofLp ⬝ᵥ x.ofLp) := by
    have h := PosSemidefNormBound.dotProduct_mono hsq x.ofLp
    simpa [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] using h
  have hn : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    have h1 : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) x‖ ^ 2 = (A *ᵥ x.ofLp) ⬝ᵥ (A *ᵥ x.ofLp) := by
      rw [PosSemidefNormBound.norm_sq_eq_dotProduct, Matrix.ofLp_toEuclideanCLM]
    rw [h1, mul_pow, PosSemidefNormBound.norm_sq_eq_dotProduct, pow_two r, hsplit]
    exact hbound
  have h := Real.sqrt_le_sqrt hn
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hr (norm_nonneg x))] at h

/-! ## 4. It subsumes the positive semidefinite case, proved and not asserted -/

/-- **THE OLDER THEOREM IS A COROLLARY**, since `0 ≤ A` puts `A` above `−r • 1` once `0 ≤ r`, which
`PosSemidefNormBound.nonneg_of_le_smul_one` supplies. `PosSemidefNormBound.l2_opNorm_le` is kept
and cited unchanged; this only records the relationship. -/
example [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hle : A ≤ r • (1 : Matrix V V ℝ)) : ‖A‖ ≤ r := by
  have hr : 0 ≤ r := PosSemidefNormBound.nonneg_of_le_smul_one hA hle
  refine l2_opNorm_le_of_abs_le ?_ hle
  refine le_trans ?_ hA
  refine Matrix.le_iff.mpr ?_
  have h : (0 : Matrix V V ℝ) - -(r • (1 : Matrix V V ℝ)) = r • (1 : Matrix V V ℝ) := by abel
  rw [h, Matrix.smul_one_eq_diagonal]
  exact Matrix.PosSemidef.diagonal fun _ => hr

/-! ## 5. The factor `LaplacianOpNorm` said was out of reach -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `degMatrix ℝ G ≼ Δ • 1` from a degree bound: both sides are diagonal. -/
theorem degMatrix_le_smul_one {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) :
    G.degMatrix ℝ ≤ Δ • (1 : Matrix V V ℝ) := by
  refine Matrix.le_iff.mpr ?_
  have hid : Δ • (1 : Matrix V V ℝ) - G.degMatrix ℝ
      = Matrix.diagonal fun v => Δ - (G.degree v : ℝ) := by
    rw [Matrix.smul_one_eq_diagonal, SimpleGraph.degMatrix, ← Matrix.diagonal_sub]
  rw [hid]
  exact Matrix.PosSemidef.diagonal fun v => sub_nonneg.mpr (hΔ v)

/-- **`‖G.adjMatrix ℝ‖ ≤ Δ`.** The Laplacian's positivity gives `A ≼ D` and the signless
Laplacian's gives `−D ≼ A`, and `D ≼ Δ • 1` closes both ends. -/
theorem norm_adjMatrix_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) :
    ‖G.adjMatrix ℝ‖ ≤ Δ := by
  have hD := degMatrix_le_smul_one G hΔ
  have hhi : G.adjMatrix ℝ ≤ Δ • (1 : Matrix V V ℝ) := by
    refine le_trans (Matrix.le_iff.mpr ?_) hD
    have hid : G.degMatrix ℝ - G.adjMatrix ℝ = G.lapMatrix ℝ := rfl
    rw [hid]
    exact SimpleGraph.posSemidef_lapMatrix ℝ G
  have h1 : -(Δ • (1 : Matrix V V ℝ)) ≤ -(G.degMatrix ℝ) := by
    refine Matrix.le_iff.mpr ?_
    have hid : -(G.degMatrix ℝ) - -(Δ • (1 : Matrix V V ℝ))
        = Δ • (1 : Matrix V V ℝ) - G.degMatrix ℝ := by abel
    rw [hid]
    exact Matrix.le_iff.mp hD
  have h2 : -(G.degMatrix ℝ) ≤ G.adjMatrix ℝ := by
    refine Matrix.le_iff.mpr ?_
    have h := LaplacianSignlessDefinite.signlessLap_posSemidef G
    have hid : LaplacianSignless.signlessLap G = G.adjMatrix ℝ - -(G.degMatrix ℝ) := by
      simp only [LaplacianSignless.signlessLap]
      abel
    rwa [hid] at h
  exact l2_opNorm_le_of_abs_le (le_trans h1 h2) hhi

end SymmetricOpNorm
