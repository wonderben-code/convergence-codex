/-
  IsingSlabMagnetisation.lean — the flip conjugated into the eigenbasis, at an
  arbitrary cross-section, and the vanishing of the top diagonal entry of the
  spin observable.

  WHY. `IsingSlabFlip` was rung 1 of the retry `PROOF_STRATEGY` §3 demands after
  `IsingSlabTransfer` produced a slab with a gap and no decay theorem. It closed
  by naming the two rungs still to climb. **This is rung 2.** Rung 3, the
  estimate itself, is still ahead and is still written about the strip.

  WHAT THIS IS. `IsingMagnetisationVanishes` proves, for the strip's column,
  that the spin observable read in the transfer matrix's own eigenbasis has a
  ZERO entry at the top index — which is what turns "correlations cluster to
  some constant" into "correlations decay to nothing". Every step of that
  argument is repeated here **with `Col n` replaced by an arbitrary finite
  cross-section**. It carries because everything it consumed is already general:
  the two identities `IsingSlabFlip` proved — the flip COMMUTES with the transfer
  matrix and ANTICOMMUTES with a single spin — together with `transferG_pos`,
  since an exponential is positive at any cross-section, and the uniqueness of
  the argmax index, which `TransferPowerSum` proves for ANY Hermitian matrix with
  positive entries and never knew about strips. **Four facts, not two**: the
  first draft of this header said two, and a reader trying to push the argument
  further would have gone looking for the wrong hypotheses.

  WHAT THIS IS NOT. It is not a decay theorem for the slab, and `WALLS` §W4 does
  not move. The passage from "the constant is zero" to a bound of the shape
  `r ^ κ` is `IsingTwoPointLimit`'s and has not been carried across; and `r`
  itself is still built from ONE cross-section's eigenvalues, with nothing said
  about what happens as the cross-section grows. That sentence is `WALLS` §W4
  item 3 and is untouched by this file.

  WHAT IT DOES SAY, THREE-DIMENSIONALLY. `slabSpinEigen_top_eq_zero` is the
  statement at the square cross-section. Said without the matrix: **the top
  eigenvector's expectation of the spin at any single site is zero**, since
  `(UᴴDU) p₀ p₀` is the sum of `U σ p₀ ^ 2 * spin (σ v)`. That is the slab's
  magnetisation in the transfer-matrix sense, and the estate's three-dimensional
  object now has it alongside the spectral gap. It is NOT
  `IsingFlipSymmetry.expect_spin_eq_zero`, which is the finite-volume Gibbs
  expectation and is elementary; the content here is the statement AT THE TOP
  EIGENVECTOR, which is what a limit of correlations sees.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabFlip
import IsingMagnetisationVanishes

namespace IsingSlabMagnetisation

open Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingTwoPointSpectral IsingFlipSymmetry
open IsingSlabTransfer IsingSlabFlip IsingMagnetisationVanishes

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The eigenbasis of the general transfer matrix -/

/-- The eigenvector unitary of `transferG`, as a plain matrix. Naming it keeps every statement
below inside the line limit; it is a `def` and unfolds by `rfl`. -/
noncomputable def eigU (β : ℝ) (E : Cross V → ℝ) : Matrix (Cross V) (Cross V) ℝ :=
  ((transferG_isHermitian β E).eigenvectorUnitary : Matrix (Cross V) (Cross V) ℝ)

theorem eigU_conjTranspose_mul (β : ℝ) (E : Cross V → ℝ) :
    (eigU β E)ᴴ * eigU β E = 1 := by
  have h := Matrix.UnitaryGroup.star_mul_self (transferG_isHermitian β E).eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose] at h

/-- **`Uᴴ·T·U` IS THE DIAGONAL MATRIX OF EIGENVALUES**, at any cross-section. `spectral_theorem`
states the factorisation the other way round; this is it solved for the diagonal, which is the
form a commutation argument uses. -/
theorem conj_transferG (β : ℝ) (E : Cross V → ℝ) :
    (eigU β E)ᴴ * transferG β E * eigU β E
      = Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q := by
  have hUs := eigU_conjTranspose_mul β E
  have hS : transferG β E
      = eigU β E * (Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q)
        * (eigU β E)ᴴ := by
    conv_lhs => rw [(transferG_isHermitian β E).spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    rfl
  rw [congrArg (fun M : Matrix (Cross V) (Cross V) ℝ => (eigU β E)ᴴ * M * eigU β E) hS]
  simp only [Matrix.mul_assoc]
  rw [hUs, Matrix.mul_one, ← Matrix.mul_assoc, hUs, Matrix.one_mul]

/-! ## 2. The flip and the observable in that basis, and the three laws -/

/-- **THE FLIP, CONJUGATED INTO THE EIGENBASIS**, at an arbitrary cross-section. -/
noncomputable def flipEigenG (β : ℝ) (E : Cross V → ℝ) : Matrix (Cross V) (Cross V) ℝ :=
  (eigU β E)ᴴ * flipMatG V * eigU β E

/-- **THE SPIN AT ONE SITE, READ IN THE EIGENBASIS.** -/
noncomputable def spinEigenG (β : ℝ) (E : Cross V → ℝ) (v : V) :
    Matrix (Cross V) (Cross V) ℝ :=
  (eigU β E)ᴴ * (Matrix.diagonal fun σ : Cross V => spin (σ v)) * eigU β E

/-- Law one: it squares to `1`, because the flip does. -/
theorem flipEigenG_mul_self (β : ℝ) (E : Cross V → ℝ) :
    flipEigenG β E * flipEigenG β E = 1 := by
  have hUs := eigU_conjTranspose_mul β E
  rw [flipEigenG, conj_mul_conj _ _ _ _ (mul_eq_one_comm.mp hUs), flipMatG_mul_flipMatG,
    Matrix.mul_one, hUs]

/-- Law two: **IT COMMUTES WITH THE DIAGONAL OF EIGENVALUES**, because the flip commutes with the
transfer matrix. This is the step that needs the hypothesis on the cross-section's own energy, and
`IsingSlabFlip` §4 discharges it for both cross-sections the estate has. -/
theorem flipEigenG_comm_diagonal {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ) (β : ℝ) :
    flipEigenG β E * (Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q)
      = (Matrix.diagonal fun q => (transferG_isHermitian β E).eigenvalues q)
        * flipEigenG β E := by
  have hUs := eigU_conjTranspose_mul β E
  have hU := mul_eq_one_comm.mp hUs
  rw [← conj_transferG β E, flipEigenG]
  rw [conj_mul_conj _ _ _ _ hU, conj_mul_conj _ _ _ _ hU, flipMatG_mul_transferG hE]

/-- Law three: **AND ANTICOMMUTES WITH THE OBSERVABLE**, with no hypothesis at all, because a
single spin changes sign where a bond does not. -/
theorem flipEigenG_anticomm_spinEigenG (β : ℝ) (E : Cross V → ℝ) (v : V) :
    flipEigenG β E * spinEigenG β E v = -(spinEigenG β E v * flipEigenG β E) := by
  have hUs := eigU_conjTranspose_mul β E
  have hU := mul_eq_one_comm.mp hUs
  rw [flipEigenG, spinEigenG, conj_mul_conj _ _ _ _ hU, conj_mul_conj _ _ _ _ hU,
    flipMatG_mul_spinDiag, Matrix.mul_neg, Matrix.neg_mul]

/-! ## 3. Vanishing off the top index, and the conclusion -/

/-- The flip in the eigenbasis is supported on the top index alone, in both directions. The
uniqueness of the argmax is `TransferPowerSum.index_eq_of_eigenvalues_eq_top`, whose hypothesis is
strict positivity of the matrix entries — which `transferG_pos` supplies at every cross-section,
because an exponential is positive. -/
theorem flipEigenG_apply_eq_zero_of_ne {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ)
    (β : ℝ) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
        ≤ (transferG_isHermitian β E).eigenvalues p₀) {q : Cross V} (hq : q ≠ p₀) :
    flipEigenG β E p₀ q = 0 ∧ flipEigenG β E q p₀ = 0 := by
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hne : (transferG_isHermitian β E).eigenvalues q
      ≠ (transferG_isHermitian β E).eigenvalues p₀ := fun h =>
    hq (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ hpos hp₀ h)
  exact ⟨eq_zero_of_comm_diagonal (flipEigenG_comm_diagonal hE β) hne,
    eq_zero_of_comm_diagonal (flipEigenG_comm_diagonal hE β) (Ne.symm hne)⟩

/-- **THE OBSERVABLE'S TOP DIAGONAL ENTRY IS ZERO**, at every site of every cross-section. `Q` and
`B` each meet the top index in a single entry; those two numbers anticommute, and `Q`'s squares
to `1`. -/
theorem spinEigenG_top_eq_zero {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ) (β : ℝ)
    (v : V) {p₀ : Cross V}
    (hp₀ : ∀ j, (transferG_isHermitian β E).eigenvalues j
        ≤ (transferG_isHermitian β E).eigenvalues p₀) :
    spinEigenG β E v p₀ p₀ = 0 := by
  classical
  have hoff : ∀ q : Cross V, q ≠ p₀ →
      flipEigenG β E p₀ q = 0 ∧ flipEigenG β E q p₀ = 0 := fun q hq =>
    flipEigenG_apply_eq_zero_of_ne hE β hp₀ hq
  have hsq : flipEigenG β E p₀ p₀ * flipEigenG β E p₀ p₀ = 1 := by
    have h := congrArg (fun X : Matrix (Cross V) (Cross V) ℝ => X p₀ p₀)
      (flipEigenG_mul_self β E)
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [← h, Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).1, zero_mul])
      (fun hp => absurd (mem_univ p₀) hp)]
  have hQne : flipEigenG β E p₀ p₀ ≠ 0 := fun h0 => by simp [h0] at hsq
  have hanti := congrArg (fun X : Matrix (Cross V) (Cross V) ℝ => X p₀ p₀)
    (flipEigenG_anticomm_spinEigenG β E v)
  simp only [Matrix.mul_apply, Matrix.neg_apply] at hanti
  rw [Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).1, zero_mul])
      (fun hp => absurd (mem_univ p₀) hp),
    Finset.sum_eq_single p₀ (fun q _ hq => by rw [(hoff q hq).2, mul_zero])
      (fun hp => absurd (mem_univ p₀) hp)] at hanti
  have hz : flipEigenG β E p₀ p₀ * (spinEigenG β E v p₀ p₀ + spinEigenG β E v p₀ p₀) = 0 := by
    linear_combination hanti
  rcases mul_eq_zero.mp hz with h0 | h0
  · exact absurd h0 hQne
  · linarith [h0]

/-! ## 4. Both instances

`ERRATUM 201`: a generalisation that is never instantiated is a claim about nothing in particular.
The strip is the first instance and the theorem above **recovers** the one this file generalised;
the square cross-section is the second, and it is the three-dimensional one. -/

/-- The strip's observable in the eigenbasis IS the general one at `E = intra`, by `rfl` — the two
transfer matrices are definitionally equal (`transferSym_eq_transferG`) and `IsHermitian` is a
proposition. -/
theorem spinEigen_eq_spinEigenG (β : ℝ) (n : ℕ) (i : Fin (n + 1)) :
    spinEigen β n i = spinEigenG β (intra (n := n)) i := rfl

/-- **INSTANCE ONE — the strip**, `IsingMagnetisationVanishes.spinEigen_top_eq_zero` obtained from
the general theorem instead of from its own proof. The strip's own proof is left standing rather
than deleted, because this file imports that one for `eq_zero_of_comm_diagonal`; the duplication is
deliberate and is recorded here rather than removed. -/
theorem strip_spinEigen_top_eq_zero (β : ℝ) (n : ℕ) (i : Fin (n + 1)) {p₀ : Col n}
    (hp₀ : ∀ j, (transferSym_isHermitian β n).eigenvalues j
        ≤ (transferSym_isHermitian β n).eigenvalues p₀) :
    spinEigen β n i p₀ p₀ = 0 :=
  spinEigenG_top_eq_zero intra_flipCross β i hp₀

/-- **INSTANCE TWO — the three-dimensional slab.** At the top index of the slab's transfer matrix
the spin observable has a zero diagonal entry, at every site of the square cross-section. -/
theorem slabSpinEigen_top_eq_zero (β : ℝ) (a b : ℕ) (v : Fin (a + 1) × Fin (b + 1))
    {p₀ : Cross (Fin (a + 1) × Fin (b + 1))}
    (hp₀ : ∀ j, (slabTransfer_isHermitian β a b).eigenvalues j
        ≤ (slabTransfer_isHermitian β a b).eigenvalues p₀) :
    spinEigenG β (slabIntra (a := a) (b := b)) v p₀ p₀ = 0 :=
  spinEigenG_top_eq_zero slabIntra_flipCross β v hp₀

end IsingSlabMagnetisation
