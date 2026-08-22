import IsingFlipSymmetry
import IsingTwoPointLimit

/-!
# The leftover term is zero, and the strip's correlations decay to nothing

`IsingTwoPointLimit.corr2SepInf_tendsto_diag` says the infinite strip's two-point function tends to
`‖B_{p₀p₀}‖²` as the separation grows, and `corr2SepInf_connected_le` bounds the difference by
`rᵏ`. Neither says that constant is zero. `IsingFlipSymmetry` supplied the symmetry that should
force it to be. This file spends it.

## The route is not the one `IsingFlipSymmetry`'s header names

That header describes the classical eigenvector argument: the flip carries a top eigenvector to a
top eigenvector, simplicity plus strict positivity forces it to be *fixed* rather than negated,
and then a bridge to the observable in the eigenbasis. **None of that is used below.** Conjugating
the flip matrix into the eigenbasis gives `Q = Uᴴ·P·U`, and the three laws survive conjugation
unchanged: `Q² = 1`, `Q` anticommutes with `B = spinEigen`, and `Q` **commutes with a diagonal
matrix** — the eigenvalues. A matrix commuting with a diagonal one vanishes off the diagonal at
every index whose eigenvalue occurs **once** in the list, and the top index is exactly such an
index (`TransferPowerSum.index_eq_of_eigenvalues_eq_top`). So `Q` and `B` meet in a single entry
each, those two numbers anticommute, and one of them squares to `1`.

**No eigenvector is produced, no positivity of one is used, and
`PerronSimple.top_eigenspace_dim_one` is not invoked.** What replaces them is simplicity **in the
eigenvalue list**, which is a weaker fact and was already proved.

## What is proved

* **`conj_transferSym`** — `Uᴴ·transferSym·U` is the diagonal matrix of eigenvalues, from
  `Matrix.IsHermitian.spectral_theorem` and unitarity;
* **`flipEigen`** — the flip in the eigenbasis — with `flipEigen_mul_self`,
  **`flipEigen_comm_diagonal`** and **`flipEigen_anticomm_spinEigen`**;
* **`flipEigen_apply_eq_zero_of_ne`** — it vanishes off the top index, in both directions;
* **`spinEigen_top_eq_zero`** — **`B_{p₀p₀} = 0`**;
* **`corr2SepInf_tendsto_zero`** and **`corr2SepInf_abs_le`** — hence the infinite strip's
  two-point function tends to **zero**, and `|⟨σ₀σ_κ⟩_∞| ≤ rᵏ` with `r < 1`: **exponential decay,
  not merely exponential clustering.**

## What this is NOT

**It is not a mass gap and `WALLS` §W4 does not move.** `r` is built from one width's eigenvalues
and nothing says it stays below one as the width grows; that sentence is item 3 and is untouched.

**And it is not a surprise.** At fixed width the strip is a one-dimensional system, where no
spontaneous magnetisation is expected; the content is that the estate can now say so, and that the
decay statement it had was clustering to an unknown constant until this file identified the
constant.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace IsingMagnetisationVanishes

open Filter Topology Finset
open IsingTransfer2D IsingTransferSym IsingTwoPoint IsingTwoPointSpectral IsingTwoPointLimit
open IsingFlipSymmetry

open scoped Matrix

variable {n : ℕ}

/-! ## 1. The transfer matrix in its own eigenbasis -/

/-- **`Uᴴ·S·U` IS THE DIAGONAL MATRIX OF EIGENVALUES.** `spectral_theorem` states the factorisation
the other way round; this is it solved for the diagonal, which is the form a commutation argument
uses. -/
theorem conj_transferSym (β : ℝ) (n : ℕ) :
    ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)ᴴ
        * transferSym β n
        * ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)
      = Matrix.diagonal fun q => (transferSym_isHermitian β n).eigenvalues q := by
  have hUs := eigenvectorUnitary_conjTranspose_mul β n
  have hS : transferSym β n
      = ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)
        * (Matrix.diagonal fun q => (transferSym_isHermitian β n).eigenvalues q)
        * ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)ᴴ := by
    conv_lhs => rw [(transferSym_isHermitian β n).spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  rw [congrArg (fun M : Matrix (Col n) (Col n) ℝ =>
    ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)ᴴ * M
      * ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)) hS]
  simp only [Matrix.mul_assoc]
  rw [hUs, Matrix.mul_one, ← Matrix.mul_assoc, hUs, Matrix.one_mul]

/-! ## 2. The flip in the eigenbasis, and its three laws -/

/-- **THE FLIP, CONJUGATED INTO THE EIGENBASIS.** -/
noncomputable def flipEigen (β : ℝ) (n : ℕ) : Matrix (Col n) (Col n) ℝ :=
  ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)ᴴ
    * flipMat n
    * ((transferSym_isHermitian β n).eigenvectorUnitary : Matrix (Col n) (Col n) ℝ)

theorem flipEigen_mul_self (β : ℝ) (n : ℕ) : flipEigen β n * flipEigen β n = 1 := by
  have hUs := eigenvectorUnitary_conjTranspose_mul β n
  rw [flipEigen, conj_mul_conj _ _ _ _ (mul_eq_one_comm.mp hUs), flipMat_mul_flipMat,
    Matrix.mul_one, hUs]

/-- **IT COMMUTES WITH THE DIAGONAL OF EIGENVALUES**, because the flip commutes with the transfer
matrix. -/
theorem flipEigen_comm_diagonal (β : ℝ) (n : ℕ) :
    flipEigen β n * (Matrix.diagonal fun q => (transferSym_isHermitian β n).eigenvalues q)
      = (Matrix.diagonal fun q => (transferSym_isHermitian β n).eigenvalues q) * flipEigen β n := by
  have hUs := eigenvectorUnitary_conjTranspose_mul β n
  have hU := mul_eq_one_comm.mp hUs
  rw [← conj_transferSym β n, flipEigen]
  rw [conj_mul_conj _ _ _ _ hU, conj_mul_conj _ _ _ _ hU, flipMat_mul_transferSym]

/-- **AND ANTICOMMUTES WITH THE OBSERVABLE IN THE EIGENBASIS**, because the flip anticommutes with
the observable. -/
theorem flipEigen_anticomm_spinEigen (β : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    flipEigen β n * spinEigen β n i = -(spinEigen β n i * flipEigen β n) := by
  have hUs := eigenvectorUnitary_conjTranspose_mul β n
  have hU := mul_eq_one_comm.mp hUs
  rw [flipEigen, spinEigen, conj_mul_conj _ _ _ _ hU, conj_mul_conj _ _ _ _ hU,
    flipMat_mul_spinDiag, Matrix.mul_neg, Matrix.neg_mul]

/-! ## 3. Vanishing off the top index, and the conclusion -/

/-- **A MATRIX COMMUTING WITH A DIAGONAL ONE VANISHES WHERE THE DIAGONAL ENTRIES DIFFER.** -/
theorem eq_zero_of_comm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Matrix ι ι ℝ} {d : ι → ℝ} (h : Q * Matrix.diagonal d = Matrix.diagonal d * Q)
    {p q : ι} (hd : d q ≠ d p) : Q p q = 0 := by
  have hpq := congrArg (fun X : Matrix ι ι ℝ => X p q) h
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hpq
  have hfac : Q p q * (d q - d p) = 0 := by linear_combination hpq
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0) hd

/-- The flip in the eigenbasis is supported on the top index alone, in both directions. -/
theorem flipEigen_apply_eq_zero_of_ne (β : ℝ) (n : ℕ) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) {q : Col n} (hq : q ≠ p₀) :
    flipEigen β n p₀ q = 0 ∧ flipEigen β n q p₀ = 0 := by
  have hpos : ∀ a b : Col n, 0 < transferSym β n a b := transferSym_entries_pos β n
  have hne : (transferSym_isHermitian β n).eigenvalues q
      ≠ (transferSym_isHermitian β n).eigenvalues p₀ := fun h =>
    hq (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ hpos hp₀ h)
  exact ⟨eq_zero_of_comm_diagonal (flipEigen_comm_diagonal β n) hne,
    eq_zero_of_comm_diagonal (flipEigen_comm_diagonal β n) (Ne.symm hne)⟩

/-- **THE OBSERVABLE'S TOP DIAGONAL ENTRY IS ZERO.** `Q` and `B` each meet the top index in one
entry; those two numbers anticommute, and `Q`'s squares to `1`. -/
theorem spinEigen_top_eq_zero (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    spinEigen β n i p₀ p₀ = 0 := by
  classical
  have hoff : ∀ q : Col n, q ≠ p₀ →
      flipEigen β n p₀ q = 0 ∧ flipEigen β n q p₀ = 0 := fun q hq =>
    flipEigen_apply_eq_zero_of_ne β n hp₀ hq
  have hsq : flipEigen β n p₀ p₀ * flipEigen β n p₀ p₀ = 1 := by
    have h := congrArg (fun X : Matrix (Col n) (Col n) ℝ => X p₀ p₀) (flipEigen_mul_self β n)
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [← h, Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).1, zero_mul])
      (fun hp => absurd (mem_univ p₀) hp)]
  have hQne : flipEigen β n p₀ p₀ ≠ 0 := fun h0 => by simp [h0] at hsq
  have hanti := congrArg (fun X : Matrix (Col n) (Col n) ℝ => X p₀ p₀)
    (flipEigen_anticomm_spinEigen β n i)
  simp only [Matrix.mul_apply, Matrix.neg_apply] at hanti
  rw [Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).1, zero_mul])
      (fun hp => absurd (mem_univ p₀) hp),
    Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).2, mul_zero])
      (fun hp => absurd (mem_univ p₀) hp)] at hanti
  have hz : flipEigen β n p₀ p₀ * (spinEigen β n i p₀ p₀ + spinEigen β n i p₀ p₀) = 0 := by
    linear_combination hanti
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hQne
  · linarith [h0]

/-! ## 4. So the correlations decay to nothing -/

/-- **THE INFINITE STRIP'S TWO-POINT FUNCTION TENDS TO ZERO** as the separation grows. -/
theorem corr2SepInf_tendsto_zero (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    Tendsto (fun κ : ℕ => corr2SepInf β n i p₀ κ) atTop (𝓝 0) := by
  have h := corr2SepInf_tendsto_diag β n i hp₀
  rwa [spinEigen_top_eq_zero β n i hp₀, norm_zero, zero_pow (by norm_num)] at h

/-- **AND IT DECAYS EXPONENTIALLY**: `|⟨σ₀σ_κ⟩_∞| ≤ rᵏ` with `r < 1`. `corr2SepInf_connected_le`
bounded the distance to a constant this file has now shown to be `0`, so clustering becomes
decay. -/
theorem corr2SepInf_abs_le (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ κ : ℕ, |corr2SepInf β n i p₀ κ| ≤ r ^ κ := by
  obtain ⟨r, hr0, hr1, hle⟩ := corr2SepInf_connected_le β n i hp₀
  refine ⟨r, hr0, hr1, fun κ => ?_⟩
  have h := hle κ
  rwa [spinEigen_top_eq_zero β n i hp₀, norm_zero, zero_pow (by norm_num), sub_zero] at h

end IsingMagnetisationVanishes
