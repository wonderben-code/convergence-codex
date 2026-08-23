/-
  IsingFieldPositive.lean — at one site the magnetisation in a field is STRICTLY POSITIVE, at
  every finite length, by an induction on two entries.

  WHY. `IsingFieldOdd` refuted the route the watchlist item named and proved the symmetry
  underneath it — the magnetisation is an odd function of the field — while saying plainly that
  oddness bounds nothing away from zero. **This bounds it away from zero, at one site.**

  WHAT WAS THERE ALREADY, AND WHY THIS IS NOT IT. `IsingFieldNonzero.field_spinEigen_diag_ne_zero`
  settles the one-site case for the **eigenvector pivot**, by pinning a number with two traces, and
  `IsingGibbsMagnetisation.field_expectG_spin_tendsto_ne_zero` for the **limit**. Neither is a
  statement about the Gibbs expectation at a finite length, and the difference matters: a limit
  being nonzero says nothing about any particular term, and `spinEigenG` is an eigenvector entry
  rather than an average. **`expectG_field_pos` is about the average, at every `M`.**

  THE PROOF IS TWO INDUCTIONS AND NO SPECTRAL THEORY. At one site the transfer matrix is
  symmetric two-by-two with entries `a = exp(β(1+h))`, `b = exp(β(1−h))` on the diagonal and
  `c = exp(−β)` off it, and `a > b` exactly when `βh > 0`. Then

  * `transferG_field_pow_nonneg` — every entry of every power is `≥ 0`, one induction;
  * **`transferG_field_pow_diag_lt`** — `(Tᵏ)_{↓↓} < (Tᵏ)_{↑↑}` for `k ≥ 1`, the other. The step is
    one line once the matrix is known symmetric: the two off-diagonal contributions are equal and
    cancel, leaving `(Tᵏ)_{↑↑} a − (Tᵏ)_{↓↓} b`, and `a > b > 0` with `(Tᵏ)_{↑↑} > (Tᵏ)_{↓↓} > 0`
    finishes it;
  * **`expectG_field_pos`** — hence the Gibbs expectation of the spin is strictly positive at every
    `β > 0`, every `h > 0` and every length.

  WHY IT DOES NOT GENERALISE, STATED SO NOBODY EXPECTS IT TO — AND WITH THE LABELS RIGHT
  (`ERRATUM 250`). The induction works because at one site `spin` separates the only two
  configurations, so the numerator **is** the difference of two diagonal entries. At more sites the
  numerator is a signed sum over `2^k` configurations and no such difference appears, so the
  induction has nothing to run on. That much is a fact about the shape of the statement and needs
  no probe.

  **What is NOT claimed here**: that the corresponding domination at more sites is false. The
  entrywise version is refuted — `IsingFieldOdd.exists_field_entry_lt` — but
  `(T_hᵏ)_{σσ} ≥ (T_{−h}ᵏ)_{σσ}` is a statement about diagonal entries of POWERS, which the
  entrywise witness does not settle, and **it has not been probed**. The watchlist item's question
  is about the cross-section; this file is the case it excludes, and it says nothing about the case
  it asks about.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingFieldOdd
import IsingFieldNonzero

namespace IsingFieldPositive

open Finset Real Matrix
open IsingTransfer2D IsingSlabTransfer IsingSlabFlip IsingSlabConfig IsingSlabField
open IsingGibbsMagnetisation IsingFieldNonzero

noncomputable section

/-! ## 1. The four entries -/

/-- The one-site transfer matrix in a field. -/
def T (β h : ℝ) : Matrix (Cross (Fin 1)) (Cross (Fin 1)) ℝ := transferG β (fieldE (V := Fin 1) h)

theorem T_up_up (β h : ℝ) : T β h up up = exp (β * (1 + h)) := by
  rw [T, transferG_apply]
  norm_num [fieldE, interG, up, spin, Fin.sum_univ_one, ← Real.exp_add]
  ring_nf

theorem T_down_down (β h : ℝ) : T β h down down = exp (β * (1 - h)) := by
  rw [T, transferG_apply]
  norm_num [fieldE, interG, down, spin, Fin.sum_univ_one, ← Real.exp_add]
  ring_nf

theorem T_nonneg (β h : ℝ) (σ τ : Cross (Fin 1)) : 0 ≤ T β h σ τ :=
  (transferG_pos β (fieldE (V := Fin 1) h) σ τ).le

theorem T_isSymm (β h : ℝ) : (T β h).IsSymm := by
  ext σ τ
  simp only [Matrix.transpose_apply, T, transferG_apply, interG_comm σ τ]
  ring

/-- **THE DIAGONAL IS ORDERED EXACTLY WHEN THE FIELD IS ON.** -/
theorem T_diag_lt {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) : T β h down down < T β h up up := by
  rw [T_up_up, T_down_down]
  exact exp_lt_exp.mpr (by nlinarith)

/-! ## 2. Two inductions -/

theorem T_pow_nonneg (β h : ℝ) : ∀ (k : ℕ) (σ τ : Cross (Fin 1)), 0 ≤ (T β h ^ k) σ τ := by
  intro k
  induction k with
  | zero =>
      intro σ τ
      rw [pow_zero, Matrix.one_apply]
      split <;> norm_num
  | succ k ih =>
      intro σ τ
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun ρ _ => mul_nonneg (ih σ ρ) (T_nonneg β h ρ τ)

/-- **THE UP DIAGONAL BEATS THE DOWN DIAGONAL AT EVERY POSITIVE POWER.** The two off-diagonal
contributions to the step are equal — the matrix is symmetric and so is every power of it — so
they cancel, and what is left is `(Tᵏ)_{↑↑} a − (Tᵏ)_{↓↓} b` with `a > b > 0`. -/
theorem T_pow_diag_lt {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    ∀ k : ℕ, 0 < (T β h ^ (k + 1)) down down ∧
      (T β h ^ (k + 1)) down down < (T β h ^ (k + 1)) up up := by
  intro k
  induction k with
  | zero =>
      exact ⟨by rw [pow_one, T_down_down]; exact exp_pos _, by rw [pow_one]; exact T_diag_lt hβ hh⟩
  | succ k ih =>
      obtain ⟨hpos, hlt⟩ := ih
      have hsym : (T β h ^ (k + 1)) up down = (T β h ^ (k + 1)) down up :=
        (congrFun (congrFun ((T_isSymm β h).pow (k + 1)) up) down).symm
      have hexp : ∀ σ : Cross (Fin 1), (T β h ^ (k + 2)) σ σ
          = (T β h ^ (k + 1)) σ up * T β h up σ + (T β h ^ (k + 1)) σ down * T β h down σ := by
        intro σ
        rw [pow_succ, Matrix.mul_apply, sum_cross_one]
      have ha : (0 : ℝ) < T β h up up := by rw [T_up_up]; exact exp_pos _
      have hb : (0 : ℝ) < T β h down down := by rw [T_down_down]; exact exp_pos _
      have hab : T β h down down < T β h up up := T_diag_lt hβ hh
      have hud : (0 : ℝ) ≤ (T β h ^ (k + 1)) down up := T_pow_nonneg β h _ _ _
      have hdu : T β h up down = T β h down up :=
        (congrFun (congrFun (T_isSymm β h) up) down).symm
      refine ⟨?_, ?_⟩
      · rw [hexp down]
        have : (0 : ℝ) ≤ (T β h ^ (k + 1)) down up * T β h up down :=
          mul_nonneg hud (T_nonneg β h _ _)
        nlinarith [T_nonneg β h up down]
      · rw [hexp up, hexp down, ← hsym, hdu]
        nlinarith

/-! ## 3. The magnetisation -/

/-- **THE MAGNETISATION AT ONE SITE, IN A FIELD, IS STRICTLY POSITIVE AT EVERY FINITE LENGTH.** -/
theorem expectG_field_pos {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) (M : ℕ) :
    0 < expectG β (fieldE (V := Fin 1) h) M (fun σ => spin (σ 0)) := by
  obtain ⟨hpos, hlt⟩ := T_pow_diag_lt hβ hh M
  set A := T β h ^ (M + 1) with hA
  have hnum : (Matrix.diagonal (fun σ : Cross (Fin 1) => spin (σ 0)) * A).trace
      = A up up - A down down := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.diagonal_mul]
    rw [sum_cross_one]
    have h1 : spin ((up : Cross (Fin 1)) 0) = 1 := rfl
    have h2 : spin ((down : Cross (Fin 1)) 0) = -1 := rfl
    rw [h1, h2]
    ring
  have hden : A.trace = A up up + A down down := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply]
    rw [sum_cross_one]
  rw [expectG_eq_sym_trace_div, show transferG β (fieldE (V := Fin 1) h) = T β h from rfl, ← hA,
    hnum, hden]
  have h1 : 0 < A up up := hpos.trans hlt
  exact div_pos (by linarith) (by linarith)

end

end IsingFieldPositive
