/-
  IsingSlabFlip.lean — the global spin flip at an arbitrary cross-section, and
  the two matrix identities the decay argument consumes.

  WHY. `IsingSlabTransfer` removed the dimension fence from the transfer matrix
  and closed with a `slab_gap` for the three-dimensional slab — and said, in
  terms, that **the decay chain above the gap was NOT transported**, so the slab
  had a gap and no decay theorem. `PROOF_STRATEGY` §3: that made it a **B**, and
  a B is retried immediately rather than banked. This is the first rung of the
  retry.

  **What the decay argument actually needs from the flip** is two matrix
  identities and nothing else: the flip permutation COMMUTES with the transfer
  matrix and ANTICOMMUTES with the spin observable. `IsingFlipSymmetry` proves
  both at `Col n`. Neither proof uses the column's structure; both use only that
  the flip is an involution, that the transfer matrix is invariant under flipping
  both arguments, and that a single spin negates.

  **And the invariance splits in two, which is the content of this file.** The
  BOND term is invariant for free — `interG_flipCross` needs no hypothesis at
  all, because each bond is a product of two spins and both change sign. The
  INTRA-section term is not: `E (flipCross σ) = E σ` is a genuine hypothesis on
  the cross-section's own energy, carried explicitly here as `hE`. At `d = 2` it
  is `IsingTransfer2D.intra_flipCol` and at the slab it is `slabIntra_flipCross`,
  both proved below, and both for the same reason as the bonds — a sum of
  products of PAIRS of spins.

  WHAT THIS FILE PROVES:
  1. **`flipCross`** and its involutivity, `spin_flipCross`, `interG_flipCross`
     (no hypothesis), and **`transferG_flipCross`** under `hE`.
  2. **`flipMatG`**, the permutation matrix of the flip, with the two apply
     lemmas the identities are proved through.
  3. **`flipMatG_mul_transferG`** — it commutes with the transfer matrix.
  4. **`flipMatG_mul_spinDiag`** — and anticommutes with the spin observable.
     The difference between them is the difference between a bond and a single
     spin, which is the whole of why the magnetisation vanishes.
  5. **`intra_flipCross`** and **`slabIntra_flipCross`** — the hypothesis `hE`
     discharged at the two cross-sections that matter, so §3 and §4 are not
     statements about an empty class.
  6. **`flipMatG_mul_slabTransfer`** and **`flipMatG_mul_slabSpinDiag`** — the
     three-dimensional slab instances, which is what the next rung consumes.

  WHAT THIS IS NOT.
  **It is not the decay theorem and the wall does not move.** The remaining rungs
  are the eigenbasis step (conjugate the flip into the eigenbasis, where the
  commuting law forces vanishing off the top index) and the estimate. Both are
  stated at `Col n` in `IsingMagnetisationVanishes` and `IsingTopRatio` and are
  **not** transported here. `WALLS` §W4's open question — the cross-section
  limit — is untouched and unchanged.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingSlabTransfer

namespace IsingSlabFlip

open Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingFlipSymmetry IsingSlabTransfer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The flip, and what is invariant under it for free -/

/-- **THE GLOBAL SPIN FLIP** on a cross-section. -/
def flipCross (σ : Cross V) : Cross V := fun v => !(σ v)

omit [Fintype V] [DecidableEq V] in
theorem flipCross_involutive (σ : Cross V) : flipCross (flipCross σ) = σ := by
  funext v; simp [flipCross]

omit [Fintype V] [DecidableEq V] in
theorem spin_flipCross (σ : Cross V) (v : V) : spin (flipCross σ v) = -spin (σ v) :=
  IsingFlipSymmetry.spin_not (σ v)

omit [Fintype V] [DecidableEq V] in
theorem flipCross_eq_comm (σ τ : Cross V) : (τ = flipCross σ) ↔ (σ = flipCross τ) := by
  constructor <;> · rintro rfl; exact (flipCross_involutive _).symm

omit [DecidableEq V] in
/-- **THE BONDS ARE INVARIANT WITH NO HYPOTHESIS**, because each is a product of TWO spins and
both change sign. This is the half of the argument that is free at every cross-section. -/
theorem interG_flipCross (σ τ : Cross V) : interG (flipCross σ) (flipCross τ) = interG σ τ := by
  simp only [interG, spin_flipCross]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **THE TRANSFER MATRIX IS INVARIANT UNDER FLIPPING BOTH ARGUMENTS**, given that the
cross-section's own energy is. That hypothesis is the only thing the flip argument asks of `E`. -/
theorem transferG_flipCross {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ) (β : ℝ)
    (σ τ : Cross V) : transferG β E (flipCross σ) (flipCross τ) = transferG β E σ τ := by
  rw [transferG_apply, transferG_apply, hE, hE, interG_flipCross]

/-! ## 2. The flip as a matrix -/

/-- The permutation matrix of the flip. -/
def flipMatG (V : Type*) [Fintype V] [DecidableEq V] : Matrix (Cross V) (Cross V) ℝ :=
  Matrix.of fun σ τ => if τ = flipCross σ then 1 else 0

theorem flipMatG_mul_apply (A : Matrix (Cross V) (Cross V) ℝ) (σ ρ : Cross V) :
    (flipMatG V * A) σ ρ = A (flipCross σ) ρ := by
  rw [Matrix.mul_apply]
  have h : ∀ τ : Cross V, flipMatG V σ τ * A τ ρ = if τ = flipCross σ then A τ ρ else 0 := by
    intro τ; simp only [flipMatG, Matrix.of_apply]; split <;> simp
  rw [Finset.sum_congr rfl fun τ _ => h τ,
    Finset.sum_ite_eq' univ (flipCross σ) fun τ => A τ ρ, if_pos (mem_univ _)]

theorem mul_flipMatG_apply (A : Matrix (Cross V) (Cross V) ℝ) (σ ρ : Cross V) :
    (A * flipMatG V) σ ρ = A σ (flipCross ρ) := by
  rw [Matrix.mul_apply]
  have h : ∀ τ : Cross V, A σ τ * flipMatG V τ ρ = if τ = flipCross ρ then A σ τ else 0 := by
    intro τ
    simp only [flipMatG, Matrix.of_apply]
    by_cases hc : ρ = flipCross τ
    · rw [if_pos hc, if_pos ((flipCross_eq_comm ρ τ).mpr hc), mul_one]
    · rw [if_neg hc, if_neg fun hd => hc ((flipCross_eq_comm ρ τ).mp hd), mul_zero]
  rw [Finset.sum_congr rfl fun τ _ => h τ,
    Finset.sum_ite_eq' univ (flipCross ρ) fun τ => A σ τ, if_pos (mem_univ _)]

/-! ## 3. The two identities the decay argument consumes -/

/-- **THE FLIP COMMUTES WITH THE TRANSFER MATRIX.** -/
theorem flipMatG_mul_transferG {E : Cross V → ℝ} (hE : ∀ σ, E (flipCross σ) = E σ) (β : ℝ) :
    flipMatG V * transferG β E = transferG β E * flipMatG V := by
  ext σ ρ
  rw [flipMatG_mul_apply, mul_flipMatG_apply, ← transferG_flipCross hE β σ (flipCross ρ),
    flipCross_involutive]

/-- **AND ANTICOMMUTES WITH THE SPIN OBSERVABLE**, at every site of every cross-section, with no
hypothesis on `E` at all. The difference between this and §3's commuting law is the difference
between a bond and a single spin, and it is the whole of why the magnetisation vanishes. -/
theorem flipMatG_mul_spinDiag (v : V) :
    flipMatG V * Matrix.diagonal (fun σ : Cross V => spin (σ v))
      = -(Matrix.diagonal (fun σ : Cross V => spin (σ v)) * flipMatG V) := by
  ext σ ρ
  rw [flipMatG_mul_apply, Matrix.neg_apply, mul_flipMatG_apply, Matrix.diagonal_apply,
    Matrix.diagonal_apply]
  by_cases h : flipCross σ = ρ
  · subst h
    rw [if_pos rfl, if_pos ((flipCross_eq_comm σ (flipCross σ)).mp rfl), spin_flipCross]
  · rw [if_neg h, if_neg fun hc => h ((flipCross_eq_comm σ ρ).mpr hc).symm, neg_zero]

/-! ## 4. The hypothesis discharged, at both cross-sections that matter

`ERRATUM 48`: a hypothesis nothing satisfies makes the theorems above statements about an empty
class. Both energies in this estate are sums of products of PAIRS of spins, which is exactly the
reason the bonds were free in §1. -/

theorem intra_flipCross {n : ℕ} (σ : Cross (Fin (n + 1))) : intra (flipCross σ) = intra σ :=
  IsingFlipSymmetry.intra_flipCol σ

theorem slabIntra_flipCross {a b : ℕ} (σ : Cross (Fin (a + 1) × Fin (b + 1))) :
    slabIntra (flipCross σ) = slabIntra σ := by
  simp only [slabIntra, spin_flipCross]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## 5. The three-dimensional slab instances -/

theorem flipMatG_mul_slabTransfer (β : ℝ) (a b : ℕ) :
    flipMatG (Fin (a + 1) × Fin (b + 1)) * slabTransfer β a b
      = slabTransfer β a b * flipMatG (Fin (a + 1) × Fin (b + 1)) :=
  flipMatG_mul_transferG slabIntra_flipCross β

theorem flipMatG_mul_slabSpinDiag (a b : ℕ) (v : Fin (a + 1) × Fin (b + 1)) :
    flipMatG (Fin (a + 1) × Fin (b + 1))
        * Matrix.diagonal (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => spin (σ v))
      = -(Matrix.diagonal (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => spin (σ v))
        * flipMatG (Fin (a + 1) × Fin (b + 1))) :=
  flipMatG_mul_spinDiag v

end IsingSlabFlip
