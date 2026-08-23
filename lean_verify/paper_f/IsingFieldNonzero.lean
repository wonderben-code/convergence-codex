/-
  IsingFieldNonzero.lean — in a field the magnetisation at the top eigenvector is
  NOT zero, and no eigenvector is computed to prove it.

  WHY. `IsingSlabField` showed that a magnetic field breaks the one hypothesis
  the decay chain asks of the cross-section energy, and opened an item for what
  it deliberately did not show: **a broken proof step is not a false conclusion.**
  That item named two routes, both going through the top eigenvector, and offered
  no estimate.

  BOTH ROUTES WERE UNNECESSARY, WHICH IS THIS FILE. The quantity in question,
  `B_{p₀p₀}` with `B = UᴴDU`, is pinned by two traces and nothing else:

  * `trace B = trace D = ∑_σ spin (σ v)`, because conjugation does not move a
    trace — **zero**, since the up and down configurations contribute `+1` and
    `-1`;
  * `trace (B · Λ) = trace (D · T) = ∑_σ spin (σ v) · T_{σσ}`, by the same
    conjugation cancelling in the middle.

  At a ONE-SITE cross-section `Cross (Fin 1)` has exactly two elements, so the
  first identity says `B_{qq} = -B_{p₀p₀}` and the second becomes
  `B_{p₀p₀}·(λ_{p₀} - λ_q)`. The eigenvalues differ because the top value occurs
  once. So `B_{p₀p₀} = 0` would force `∑_σ spin (σ v) · T_{σσ} = 0`, and in the
  unit field at `β = 1` that sum is `exp 2 - 1`.

  **`field_spinEigen_top_ne_zero`.** The item is closed, in the direction it
  expected, by an argument it did not foresee — and its ESTIMATE line refused to
  guess, which was right, while its BLOCKED ON line named a blocker that was not
  one. That is the third estimate in two days to be wrong about cost rather than
  about outcome, and the cheap direction each time.

  WHAT THIS IS NOT. It is one site. Nothing here says the magnetisation fails to
  vanish at a larger cross-section — the two-trace argument pins ONE number only
  when there are two indices, and at `2^k` indices it constrains a sum. That is
  written into the item rather than glossed.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabField

namespace IsingFieldNonzero

open Finset Matrix Real
open IsingTransfer2D IsingTwoPointSpectral IsingSlabTransfer IsingSlabFlip
open IsingSlabMagnetisation IsingSlabField

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Two traces, at an arbitrary cross-section

Neither identity mentions an eigenvector, and both hold with no hypothesis on `E`. -/

/-- **CONJUGATION DOES NOT MOVE A TRACE**, so the observable in the eigenbasis has the same trace
as the observable: `∑_σ spin (σ v)`. -/
theorem trace_spinEigenG (β : ℝ) (E : Cross V → ℝ) (v : V) :
    (spinEigenG β E v).trace = ∑ σ : Cross V, spin (σ v) := by
  have hUs := eigU_conjTranspose_mul β E
  rw [spinEigenG, Matrix.trace_mul_cycle, mul_eq_one_comm.mp hUs, Matrix.one_mul,
    Matrix.trace_diagonal]

/-- **AND THE SAME CANCELLATION AGAINST THE DIAGONAL OF EIGENVALUES.** `B · Λ` is the conjugate of
`D · T`, so its trace is `∑_σ spin (σ v) · T_{σσ}` — a sum of matrix ENTRIES, with no spectral data
in it at all. -/
theorem trace_spinEigenG_mul_diagonal (β : ℝ) (E : Cross V → ℝ) (v : V) :
    (spinEigenG β E v
        * Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q).trace
      = ∑ σ : Cross V, spin (σ v) * transferG β E σ σ := by
  have hUs := eigU_conjTranspose_mul β E
  have hU := mul_eq_one_comm.mp hUs
  rw [← conj_transferG β E, spinEigenG, conj_mul_conj _ _ _ _ hU, Matrix.trace_mul_cycle, hU,
    Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single σ (fun τ _ hτ => by rw [if_neg (Ne.symm hτ), zero_mul])
    (fun hσ => absurd (mem_univ σ) hσ), if_pos rfl]

/-! ## 2. One site, where two indices make the two traces enough -/

/-- The two configurations of a one-site cross-section, as an equivalence with `Bool`. -/
def crossEquivBool : Cross (Fin 1) ≃ Bool where
  toFun σ := σ 0
  invFun b := fun _ => b
  left_inv σ := by funext i; fin_cases i; rfl
  right_inv b := rfl

theorem sum_cross_one (f : Cross (Fin 1) → ℝ) : ∑ σ : Cross (Fin 1), f σ = f up + f down := by
  have hcong : ∀ σ : Cross (Fin 1), f σ = f (fun _ => σ 0) := by
    intro σ; congr 1; funext i; fin_cases i; rfl
  rw [Fintype.sum_equiv crossEquivBool f (fun b => f (fun _ => b)) hcong, Fintype.sum_bool]
  rfl

/-- Whichever configuration `p₀` is, the two of them are `p₀` and its flip. -/
theorem sum_cross_one_split (p₀ : Cross (Fin 1)) (f : Cross (Fin 1) → ℝ) :
    ∑ σ : Cross (Fin 1), f σ = f p₀ + f (flipCross p₀) := by
  rcases (crossEquivBool.symm_apply_apply p₀).symm.trans
      (congrArg (fun b => (fun _ => b : Cross (Fin 1))) rfl) with _
  have hcases : p₀ = up ∨ p₀ = down := by
    rcases hb : p₀ 0 with _ | _
    · right; funext i; fin_cases i; exact hb
    · left; funext i; fin_cases i; exact hb
  rcases hcases with h | h
  · subst h; rw [sum_cross_one]; rfl
  · subst h; rw [sum_cross_one]; rw [flipCross_down]; ring

/-! ## 3. The magnetisation in a unit field at one site -/

/-- **THE TWO-TRACE IDENTITY AT ONE SITE.** `B_{p₀p₀}` times the eigenvalue gap is the entry sum,
and nothing else was needed. -/
theorem spinEigen_top_mul_gap (β : ℝ) (E : Cross (Fin 1) → ℝ) (p₀ : Cross (Fin 1)) :
    spinEigenG β E 0 p₀ p₀
        * ((transferG_isHermitian β E).eigenvalues p₀
            - (transferG_isHermitian β E).eigenvalues (flipCross p₀))
      = ∑ σ : Cross (Fin 1), spin (σ 0) * transferG β E σ σ := by
  have htr := trace_spinEigenG β E 0
  have hzero : ∑ σ : Cross (Fin 1), spin (σ 0) = 0 := by
    rw [sum_cross_one]; norm_num [up, down, spin]
  rw [hzero] at htr
  have hsplit : (spinEigenG β E 0).trace
      = spinEigenG β E 0 p₀ p₀ + spinEigenG β E 0 (flipCross p₀) (flipCross p₀) := by
    simpa only [Matrix.trace, Matrix.diag] using
      sum_cross_one_split p₀ (fun σ => spinEigenG β E 0 σ σ)
  have hopp : spinEigenG β E 0 (flipCross p₀) (flipCross p₀) = -spinEigenG β E 0 p₀ p₀ := by
    rw [htr] at hsplit; linarith
  have hmul := trace_spinEigenG_mul_diagonal β E 0
  rw [show (spinEigenG β E 0
        * Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q).trace
      = spinEigenG β E 0 p₀ p₀ * (transferG_isHermitian β E).eigenvalues p₀
        + spinEigenG β E 0 (flipCross p₀) (flipCross p₀)
          * (transferG_isHermitian β E).eigenvalues (flipCross p₀) from by
    simpa only [Matrix.trace, Matrix.diag, Matrix.mul_diagonal] using
      sum_cross_one_split p₀ (fun σ => spinEigenG β E 0 σ σ
        * (transferG_isHermitian β E).eigenvalues σ)] at hmul
  rw [hopp] at hmul
  linarith [hmul]

/-- **THE ENTRY SUM IN THE UNIT FIELD IS `exp 2 - 1`**, from the two diagonal entries already
computed in `IsingSlabField`. -/
theorem field_entry_sum :
    ∑ σ : Cross (Fin 1), spin (σ 0) * transferG 1 (fieldE (V := Fin 1) 1) σ σ = exp 2 - 1 := by
  rw [sum_cross_one, transferG_field_up_up, transferG_field_down_down]
  norm_num [up, down, spin]
  ring

/-- **SO THE MAGNETISATION IS NOT ZERO IN A FIELD**, at the top eigenvector and — as it turns out —
at every other index too. This is the item `IsingSlabField` opened, closed in the direction it
expected and by an argument it did not foresee: no eigenvector is produced and no two-by-two
spectral machinery is used.

**AND THE ARGMAX HYPOTHESIS IS NOT NEEDED.** The first draft carried
`hp₀ : ∀ j, λ_j ≤ λ_{p₀}` because the item is about the TOP eigenvector, and Lean's unused-variable
linter reported it unused. It is: the product `B_{p₀p₀}·(λ_{p₀} - λ_{flip p₀})` being the nonzero
number `exp 2 - 1` already forces both factors nonzero, whichever index `p₀` is. The statement is
therefore about every diagonal entry, and the top one is a case of it.

**It is one site.** At a larger cross-section the two traces constrain a SUM of `2^k` entries
rather than pinning one, and nothing here says anything about that case. -/
theorem field_spinEigen_diag_ne_zero (p₀ : Cross (Fin 1)) :
    spinEigenG 1 (fieldE (V := Fin 1) 1) 0 p₀ p₀ ≠ 0 := by
  intro h0
  have hkey := spinEigen_top_mul_gap 1 (fieldE (V := Fin 1) 1) p₀
  rw [h0, zero_mul, field_entry_sum] at hkey
  have hlt : (1 : ℝ) < exp 2 := by nlinarith [Real.add_one_le_exp (2 : ℝ)]
  linarith

end IsingFieldNonzero
