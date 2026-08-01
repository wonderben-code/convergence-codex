/-
  Herm2Action: the SL₂(ℂ) Action on Herm₂(ℂ), BUNDLED
  ====================================================

  Closes the remaining halves of two partially-fired UNLOCK_WATCHLIST items
  (the ledgers live in the companion repository codex-internal): "Herm₂(ℂ)
  determinant form as a bundled LinearMap / MulAction of SL₂(ℂ)" and the
  MulAction residue of "the O(1,3)/SO⁺(1,3) groups as Mathlib-style
  objects". `MinkowskiHerm2` proved the raw conjugation facts; this file
  packages them the way a downstream user quantifies over them.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `Herm2` — the Hermitian 2×2 matrices as Mathlib's
     `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)`, which carries the ℝ-module
     structure for free, and a genuine `MulAction` INSTANCE of
     `SpecialLinearGroup (Fin 2) ℂ` on it by conjugation H ↦ A·H·Aᴴ
     (`one_smul` and `mul_smul` from `conj_action_one` / `conj_action_mul`).
  2. `det_smul` — THE MINKOWSKI ISOMETRY, in action language: the
     determinant (which IS the Minkowski form on Herm₂, per
     `MinkowskiHerm2`) is invariant under the action.
  3. `conjLinear` — the action of each group element as a bundled
     ℝ-LINEAR map `Herm2 →ₗ[ℝ] Herm2`: conjugation is additive and
     commutes with real scalars. This is the "bundled LinearMap" the
     watchlist item asked for.
  4. `smul_eq_self_iff_pm_one` — the KERNEL of the bundled action:
     an element fixes EVERY Hermitian matrix iff its matrix is ±1 —
     `MinkowskiHerm2.kernel_of_conj_action` (forward) plus the direct
     computation (backward), now stated on the bundled action.
  5. `action_nontrivial` — a unipotent element moves the identity matrix:
     the action is not trivial, so the instance carries content.

  NOT proven here: the identification of SO⁺(1,3) with the identity
  component (topological; nothing downstream needs it — unchanged from the
  watchlist item), and nothing about the cascade.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import MinkowskiHerm2
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Complex.Module

open Matrix

noncomputable section

namespace Herm2Action

/-- The Hermitian 2×2 complex matrices, as Mathlib's `selfAdjoint` — an
    additive subgroup with an ℝ-module structure already in Mathlib. -/
abbrev Herm2 := selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)

/-- SL₂(ℂ), Mathlib's bundled special linear group. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

theorem mem_herm2_iff (H : Matrix (Fin 2) (Fin 2) ℂ) :
    H ∈ selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) ↔ Hᴴ = H := by
  rw [selfAdjoint.mem_iff]
  rw [show star H = Hᴴ from rfl]

/-- **The conjugation `MulAction` of SL₂(ℂ) on Herm₂**: A • H = A·H·Aᴴ. -/
instance : MulAction SL2C Herm2 where
  smul A H := ⟨A.1 * H.1 * A.1ᴴ, by
    rw [mem_herm2_iff]
    exact MinkowskiHerm2.conj_action_hermitian A.1 H.1
      ((mem_herm2_iff H.1).mp H.2)⟩
  one_smul H := Subtype.ext (by
    change ((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * H.1
        * ((1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = H.1
    rw [Matrix.SpecialLinearGroup.coe_one]
    exact MinkowskiHerm2.conj_action_one H.1)
  mul_smul A B H := Subtype.ext (by
    change ((A * B : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * H.1
        * ((A * B : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
      = A.1 * (B.1 * H.1 * B.1ᴴ) * A.1ᴴ
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact MinkowskiHerm2.conj_action_mul A.1 B.1 H.1)

@[simp] theorem smul_coe (A : SL2C) (H : Herm2) :
    ((A • H : Herm2) : Matrix (Fin 2) (Fin 2) ℂ) = A.1 * H.1 * A.1ᴴ := rfl

/-- **The Minkowski isometry, in action language**: the determinant — the
    Minkowski form on Herm₂ — is invariant under the action. -/
theorem det_smul (A : SL2C) (H : Herm2) :
    ((A • H : Herm2) : Matrix (Fin 2) (Fin 2) ℂ).det = (H : Matrix (Fin 2) (Fin 2) ℂ).det := by
  rw [smul_coe]
  exact MinkowskiHerm2.det_conj_invariant A.1 H.1 A.2

/-- **Each group element acts ℝ-LINEARLY**: conjugation as a bundled
    linear map on the real vector space Herm₂. -/
def conjLinear (A : SL2C) : Herm2 →ₗ[ℝ] Herm2 where
  toFun H := A • H
  map_add' H K := Subtype.ext (by
    change A.1 * (H.1 + K.1) * A.1ᴴ = A.1 * H.1 * A.1ᴴ + A.1 * K.1 * A.1ᴴ
    rw [Matrix.mul_add, Matrix.add_mul])
  map_smul' r H := Subtype.ext (by
    change A.1 * (r • H.1) * A.1ᴴ = r • (A.1 * H.1 * A.1ᴴ)
    rw [Matrix.mul_smul, Matrix.smul_mul])

@[simp] theorem conjLinear_apply (A : SL2C) (H : Herm2) :
    conjLinear A H = A • H := rfl

/-- **The kernel of the bundled action is exactly {±1}**: an element of
    SL₂(ℂ) fixes every Hermitian matrix iff its matrix is 1 or −1.
    Forward: `MinkowskiHerm2.kernel_of_conj_action`. Backward: direct
    computation. -/
theorem smul_eq_self_iff_pm_one (A : SL2C) :
    (∀ H : Herm2, A • H = H)
      ↔ ((A : Matrix (Fin 2) (Fin 2) ℂ) = 1
          ∨ (A : Matrix (Fin 2) (Fin 2) ℂ) = -1) := by
  constructor
  · intro hfix
    refine MinkowskiHerm2.kernel_of_conj_action A.1 A.2 fun H hH => ?_
    have h := hfix ⟨H, (mem_herm2_iff H).mpr hH⟩
    exact congrArg Subtype.val h
  · rintro (h1 | h1) <;> intro H <;> refine Subtype.ext ?_
    · change A.1 * H.1 * A.1ᴴ = H.1
      rw [h1]
      exact MinkowskiHerm2.conj_action_one H.1
    · change A.1 * H.1 * A.1ᴴ = H.1
      rw [h1, Matrix.conjTranspose_neg, Matrix.conjTranspose_one,
        Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
      exact neg_neg _

/-- The identity matrix, as a point of Herm₂. -/
def hermOne : Herm2 := ⟨1, (mem_herm2_iff 1).mpr (by simp)⟩

/-- The unipotent element [[1,1],[0,1]] of SL₂(ℂ). -/
def unipotent : SL2C :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- **The action is not trivial**: the unipotent element moves the
    identity matrix (to [[2,1],[1,1]]). The instance carries content. -/
theorem action_nontrivial : unipotent • hermOne ≠ hermOne := by
  intro h
  have h0 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  have hval : ((unipotent • hermOne : Herm2)
      : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 2 := by
    change (unipotent.1 * hermOne.1 * unipotent.1ᴴ) 0 0 = 2
    rw [show hermOne.1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) from rfl,
      Matrix.mul_one]
    rw [show unipotent.1 = !![1, 1; 0, 1] from rfl]
    rw [show (!![(1 : ℂ), 1; 0, 1])ᴴ = !![1, 0; 1, 1] by
      ext i j
      fin_cases i <;> fin_cases j <;> simp]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
  rw [hval] at h0
  have h1 : (hermOne : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := by
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1
    simp
  rw [h1] at h0
  norm_num at h0

end Herm2Action
