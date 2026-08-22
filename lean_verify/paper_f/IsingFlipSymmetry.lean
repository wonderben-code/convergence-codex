import IsingTwoPoint
import IsingTransferSym

/-!
# The global spin flip, and the magnetisation of the strip is exactly zero

`IsingTwoPointLimit`'s header names one route it does not take: the two-point function of the
infinite strip tends to `‖B_{p₀p₀}‖²`, the observable's quadratic form at the top eigenvector, and
*"flipping every spin leaves the energy unchanged and negates the observable"* would force that to
vanish. **The flip invariance was checked to be absent from this estate and was therefore not
used.** This file supplies it, and takes the finite-volume consequence, which needs no spectral
theory at all.

## What is proved

* **`flipCol`** — flip every spin of a column — with `spin_not` and `spin_flipCol`;
* **`intra_flipCol`, `inter_flipCol`, `energy_flipCol`** — both bond sums and hence the energy of
  a whole configuration are invariant. Each bond is a **product of two** spins, so the two signs
  cancel; that is the entire content, and it is why a term linear in the spins is not invariant;
* **`transfer2_flipCol`, `transferSym_flipCol`** — so both transfer matrices are;
* **`expect_spin_eq_zero`** — **THE MAGNETISATION OF THE FINITE STRIP IS EXACTLY ZERO**, at every
  inverse temperature, every width and every length. The flip is a bijection of configurations
  that preserves the weight and negates the observable, so the numerator equals its own negative;
* **`flipMat`** and its three laws — `flipMat² = 1`, **`flipMat` COMMUTES with `transferSym`**,
  and **ANTICOMMUTES with the spin observable**. This is the same symmetry as a matrix identity,
  which is the form the eigenvector argument consumes.

## What this is NOT

**It does not prove `‖B_{p₀p₀}‖² = 0`.** That is the statement about the **top eigenvector**, and
it needs three more steps this file does not take: that `flipMat` maps a top eigenvector to a top
eigenvector, that simplicity (`PerronSimple.top_eigenspace_dim_one`) plus strict positivity forces
the top eigenvector to be *fixed* rather than negated, and a bridge from `spinEigen p₀ p₀` to the
quadratic form at that vector. **`expect_spin_eq_zero` is not that statement**: it is the average
over a finite strip, and the limit `M → ∞` at fixed width is where the two would meet.

**And zero magnetisation is not a mass gap and does not move `WALLS` §W4.** At fixed width the
strip is a one-dimensional system and its magnetisation vanishing is expected rather than
surprising; what makes it worth proving is that `IsingTwoPointLimit` names it as an unproved
input.

**`spin_not` here is about `IsingTransfer2D.spin`.** `IsingFiniteVolume` defines its own `spin`
with the same body and proves its own `spin_not`; the two constants are distinct and neither
lemma applies to the other's. That duplication predates this file and is recorded rather than
repaired here — it is a rename across `IsingFiniteVolume` and its dependents, which is broadening.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace IsingFlipSymmetry

open Finset Real IsingTransfer2D IsingTransferSym IsingTwoPoint

variable {n : ℕ}

/-! ## 1. The flip, and what a single spin does under it -/

/-- **THE GLOBAL SPIN FLIP** on a column. -/
def flipCol (σ : Col n) : Col n := fun i => !(σ i)

theorem flipCol_involutive (σ : Col n) : flipCol (flipCol σ) = σ := by
  funext i; simp [flipCol]

/-- A spin changes sign. This is the asymmetry the whole file turns on: bonds are **products of
two** spins and are therefore invariant, while the observable is a single spin and is not. -/
theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> norm_num [spin]

theorem spin_flipCol (σ : Col n) (i : Fin (n + 1)) : spin (flipCol σ i) = -spin (σ i) := by
  rw [flipCol, spin_not]

theorem flipCol_eq_comm (σ τ : Col n) : (τ = flipCol σ) ↔ (σ = flipCol τ) := by
  constructor <;> (rintro rfl; rw [flipCol_involutive])

/-! ## 2. Both bond sums, and hence the energy, are invariant -/

theorem intra_flipCol (σ : Col n) : intra (flipCol σ) = intra σ := by
  simp only [intra]
  exact Finset.sum_congr rfl fun i _ => by rw [spin_flipCol, spin_flipCol, neg_mul_neg]

theorem inter_flipCol (σ τ : Col n) : inter (flipCol σ) (flipCol τ) = inter σ τ := by
  simp only [inter]
  exact Finset.sum_congr rfl fun i _ => by rw [spin_flipCol, spin_flipCol, neg_mul_neg]

/-- The flip applied to a whole configuration, column by column. -/
def flipConf (M : ℕ) (s : Fin (M + 1) → Col n) : Fin (M + 1) → Col n := fun j => flipCol (s j)

theorem flipConf_involutive (M : ℕ) (s : Fin (M + 1) → Col n) :
    flipConf M (flipConf M s) = s := by
  funext j; exact flipCol_involutive (s j)

/-- **THE ENERGY IS INVARIANT UNDER FLIPPING EVERY SPIN OF EVERY COLUMN.** -/
theorem energy_flipCol (M : ℕ) (s : Fin (M + 1) → Col n) :
    energy M (flipConf M s) = energy M s := by
  simp only [energy, flipConf]
  exact Finset.sum_congr rfl fun j _ => by rw [intra_flipCol, inter_flipCol]

theorem transfer2_flipCol (β : ℝ) (σ τ : Col n) :
    transfer2 β n (flipCol σ) (flipCol τ) = transfer2 β n σ τ := by
  simp only [transfer2]
  rw [intra_flipCol, inter_flipCol]

theorem transferSym_flipCol (β : ℝ) (σ τ : Col n) :
    transferSym β n (flipCol σ) (flipCol τ) = transferSym β n σ τ := by
  rw [transferSym_apply, transferSym_apply, intra_flipCol, intra_flipCol, inter_flipCol]

/-! ## 3. The magnetisation, and it is zero -/

/-- **THE MAGNETISATION OF THE FINITE STRIP IS EXACTLY ZERO**, at every inverse temperature, every
width and every length. No positivity, no spectral theory and no limit: the flip is a bijection of
configurations that preserves the Boltzmann weight and negates the observable, so the numerator is
its own negative. -/
theorem expect_spin_eq_zero (β : ℝ) (n M : ℕ) (i : Fin (n + 1)) :
    expect β n M (fun σ : Col n => spin (σ i)) = 0 := by
  have hnum : (∑ s : Fin (M + 1) → Col n, spin (s 0 i) * exp (β * energy M s)) = 0 := by
    set N := ∑ s : Fin (M + 1) → Col n, spin (s 0 i) * exp (β * energy M s) with hN
    have hre : N = ∑ s : Fin (M + 1) → Col n,
        spin (flipConf M s 0 i) * exp (β * energy M (flipConf M s)) := by
      rw [hN]
      refine Fintype.sum_equiv
        ((Function.Involutive.toPerm (flipConf (n := n) M) (flipConf_involutive M))) _ _ ?_
      intro s
      simp only [Function.Involutive.coe_toPerm, flipConf_involutive]
    have hneg : (∑ s : Fin (M + 1) → Col n,
        spin (flipConf M s 0 i) * exp (β * energy M (flipConf M s))) = -N := by
      rw [hN, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [energy_flipCol, flipConf, spin_flipCol, neg_mul]
    rw [hre, hneg] at hN
    linarith [hN]
  have hdef : expect β n M (fun σ : Col n => spin (σ i))
      = (∑ s : Fin (M + 1) → Col n, spin (s 0 i) * exp (β * energy M s))
        / partition2 β n M := rfl
  rw [hdef, hnum, zero_div]

/-! ## 4. The same symmetry as a matrix identity -/

/-- **THE FLIP AS A MATRIX**, written down rather than obtained from `Equiv.Perm`. -/
def flipMat (n : ℕ) : Matrix (Col n) (Col n) ℝ :=
  Matrix.of fun σ τ => if τ = flipCol σ then 1 else 0

theorem flipMat_apply' (σ τ : Col n) : flipMat n σ τ = if σ = flipCol τ then 1 else 0 := by
  simp only [flipMat, Matrix.of_apply]
  exact if_congr (flipCol_eq_comm σ τ) rfl rfl

theorem flipMat_mul_apply (A : Matrix (Col n) (Col n) ℝ) (σ ρ : Col n) :
    (flipMat n * A) σ ρ = A (flipCol σ) ρ := by
  rw [Matrix.mul_apply]
  have h : ∀ τ : Col n, flipMat n σ τ * A τ ρ = if τ = flipCol σ then A τ ρ else 0 := by
    intro τ; simp only [flipMat, Matrix.of_apply]; split <;> simp
  rw [Finset.sum_congr rfl fun τ _ => h τ, Finset.sum_ite_eq' univ (flipCol σ) fun τ => A τ ρ,
    if_pos (mem_univ _)]

theorem mul_flipMat_apply (A : Matrix (Col n) (Col n) ℝ) (σ ρ : Col n) :
    (A * flipMat n) σ ρ = A σ (flipCol ρ) := by
  rw [Matrix.mul_apply]
  have h : ∀ τ : Col n, A σ τ * flipMat n τ ρ = if τ = flipCol ρ then A σ τ else 0 := by
    intro τ; rw [flipMat_apply']; split <;> simp
  rw [Finset.sum_congr rfl fun τ _ => h τ, Finset.sum_ite_eq' univ (flipCol ρ) fun τ => A σ τ,
    if_pos (mem_univ _)]

theorem flipMat_mul_flipMat (n : ℕ) : flipMat n * flipMat n = 1 := by
  ext σ ρ
  rw [flipMat_mul_apply, flipMat, Matrix.of_apply, flipCol_involutive, Matrix.one_apply]
  exact if_congr eq_comm rfl rfl

/-- **THE FLIP COMMUTES WITH THE SYMMETRISED TRANSFER MATRIX.** -/
theorem flipMat_mul_transferSym (β : ℝ) (n : ℕ) :
    flipMat n * transferSym β n = transferSym β n * flipMat n := by
  ext σ ρ
  rw [flipMat_mul_apply, mul_flipMat_apply, ← transferSym_flipCol β σ (flipCol ρ),
    flipCol_involutive]

/-- **AND ANTICOMMUTES WITH THE SPIN OBSERVABLE.** The two facts together are what a symmetry
argument about the top eigenvector consumes, and the difference between them is the difference
between a bond and a single spin. -/
theorem flipMat_mul_spinDiag (n : ℕ) (i : Fin (n + 1)) :
    flipMat n * Matrix.diagonal (fun σ : Col n => spin (σ i))
      = -(Matrix.diagonal (fun σ : Col n => spin (σ i)) * flipMat n) := by
  ext σ ρ
  rw [flipMat_mul_apply, Matrix.neg_apply, mul_flipMat_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases h : flipCol σ = ρ
  · subst h
    rw [if_pos rfl, if_pos ((flipCol_eq_comm σ (flipCol σ)).mp rfl), spin_flipCol]
  · rw [if_neg h, if_neg fun hc => h ((flipCol_eq_comm σ ρ).mpr hc).symm, neg_zero]

end IsingFlipSymmetry
