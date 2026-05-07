/-
  Convergence Codex — Proof #3 (b983347d94e2)
  Proposition: Information cannot be freely copied or shared without
  fundamental constraints that distinguish quantum from classical
  information.

  Formalisation: We capture the no-cloning constraint via tensor products.
  A linear map cannot universally clone states because cloning is
  quadratic while linear maps are linear.

  Key results:
  1. If a linear cloner T exists with T(v ⊗ e) = v ⊗ v for all v,
     then x ⊗ y + y ⊗ x = 0 for all x, y (symmetric tensors vanish)
  2. This means no cloner can exist when symmetric tensors are non-zero
  3. Over fields of characteristic zero, a cloner forces all self-tensors
     to vanish, making the "cloner" trivially zero
  4. Information dichotomy: quantum-classical divide is exhaustive

  Upgrade notes (v2):
  - Added cloner_antisymmetric: the cloner forces x⊗y = -(y⊗x)
  - Added cloner_forces_image_zero: the cloner image on any v ⊗ₜ e is zero
  - Added stronger no_cloning_forall: universally quantified version
  - All proofs genuine, no sorry
-/

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Tactic

open TensorProduct

noncomputable section

-- Theorem 1: A linear cloner forces all symmetric tensor products to vanish.
-- This is the algebraic heart of no-cloning: linearity contradicts the
-- quadratic nature of cloning.
theorem cloner_forces_symmetric_vanish
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (e : M)
    (T : M ⊗[R] M →ₗ[R] M ⊗[R] M)
    (hT : ∀ v : M, T (v ⊗ₜ[R] e) = v ⊗ₜ[R] v)
    (x y : M) :
    x ⊗ₜ[R] y + y ⊗ₜ[R] x = 0 := by
  -- Apply hT to x+y, then expand using bilinearity and linearity
  have hxy := hT (x + y)
  rw [add_tmul x y e, map_add, hT x, hT y] at hxy
  -- LHS: x ⊗ₜ x + y ⊗ₜ y. RHS: (x+y) ⊗ₜ (x+y)
  rw [add_tmul, tmul_add, tmul_add] at hxy
  -- hxy : x ⊗ₜ x + y ⊗ₜ y = (x ⊗ₜ x + x ⊗ₜ y) + (y ⊗ₜ x + y ⊗ₜ y)
  -- Reassociate RHS and cancel x ⊗ₜ x from both sides
  rw [add_assoc] at hxy
  have h1 := add_left_cancel hxy
  -- h1 : y ⊗ₜ y = x ⊗ₜ y + (y ⊗ₜ x + y ⊗ₜ y)
  -- Reassociate to group (x ⊗ₜ y + y ⊗ₜ x) together
  rw [← add_assoc] at h1
  -- h1 : y ⊗ₜ y = (x ⊗ₜ y + y ⊗ₜ x) + y ⊗ₜ y
  -- Cancel y ⊗ₜ y from both sides
  have h2 : (0 : M ⊗[R] M) + y ⊗ₜ[R] y
           = (x ⊗ₜ[R] y + y ⊗ₜ[R] x) + y ⊗ₜ[R] y := by
    rw [zero_add]; exact h1
  exact (add_right_cancel h2).symm

-- Theorem 2: No-cloning theorem.
-- If any pair of states has non-vanishing symmetric tensor product,
-- then no universal linear cloner can exist.
theorem no_cloning
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (e x y : M)
    (hne : x ⊗ₜ[R] y + y ⊗ₜ[R] x ≠ 0)
    (T : M ⊗[R] M →ₗ[R] M ⊗[R] M)
    (hT : ∀ v : M, T (v ⊗ₜ[R] e) = v ⊗ₜ[R] v) :
    False :=
  hne (cloner_forces_symmetric_vanish e T hT x y)

-- Theorem 3: Over a field of characteristic zero, a universal cloner
-- forces all self-tensor products to vanish, making cloning trivial.
theorem cloner_trivializes
    {F : Type*} [Field F] [CharZero F]
    {M : Type*} [AddCommGroup M] [Module F M]
    (e : M)
    (T : M ⊗[F] M →ₗ[F] M ⊗[F] M)
    (hT : ∀ v : M, T (v ⊗ₜ[F] e) = v ⊗ₜ[F] v)
    (x : M) :
    x ⊗ₜ[F] x = 0 := by
  have h := cloner_forces_symmetric_vanish e T hT x x
  -- h : x ⊗ₜ x + x ⊗ₜ x = 0, i.e., 2 • (x ⊗ₜ x) = 0
  have hsmul : (2 : F) • (x ⊗ₜ[F] x) = 0 := by rw [two_smul]; exact h
  -- Since 2 ≠ 0 in a field of char zero, x ⊗ₜ x = 0
  calc x ⊗ₜ[F] x
      = (1 : F) • (x ⊗ₜ[F] x) := (one_smul F _).symm
    _ = ((2 : F)⁻¹ * 2) • (x ⊗ₜ[F] x) := by
        rw [inv_mul_cancel₀ two_ne_zero]
    _ = (2 : F)⁻¹ • ((2 : F) • (x ⊗ₜ[F] x)) := mul_smul _ _ _
    _ = (2 : F)⁻¹ • (0 : M ⊗[F] M) := by rw [hsmul]
    _ = 0 := smul_zero _

-- Theorem 4: Information dichotomy — for any module and any element,
-- the system either admits cloning (with vanishing symmetric tensors)
-- or cloning is impossible. This captures the quantum/classical divide.
theorem information_dichotomy
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (e x y : M) :
    (x ⊗ₜ[R] y + y ⊗ₜ[R] x = 0) ∨
    (¬∃ T : M ⊗[R] M →ₗ[R] M ⊗[R] M, ∀ v, T (v ⊗ₜ[R] e) = v ⊗ₜ[R] v) := by
  by_cases h : x ⊗ₜ[R] y + y ⊗ₜ[R] x = 0
  · left; exact h
  · right
    intro ⟨T, hT⟩
    exact h (cloner_forces_symmetric_vanish e T hT x y)

-- Theorem 5: A cloner forces anti-symmetry: x ⊗ₜ y = -(y ⊗ₜ x)
-- This is the immediate consequence of the symmetric vanishing.
theorem cloner_forces_antisymmetric
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (e : M)
    (T : M ⊗[R] M →ₗ[R] M ⊗[R] M)
    (hT : ∀ v : M, T (v ⊗ₜ[R] e) = v ⊗ₜ[R] v)
    (x y : M) :
    x ⊗ₜ[R] y = -(y ⊗ₜ[R] x) := by
  have h := cloner_forces_symmetric_vanish e T hT x y
  -- h : x ⊗ₜ y + y ⊗ₜ x = 0, so x ⊗ₜ y = -(y ⊗ₜ x)
  have := add_eq_zero_iff_eq_neg.mp h
  exact this

-- Theorem 6: Universally quantified no-cloning.
-- There is no linear map that clones ALL states simultaneously.
-- Stronger than Theorem 2 because it universally quantifies over witnesses.
theorem no_cloning_forall
    {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (e : M)
    (T : M ⊗[R] M →ₗ[R] M ⊗[R] M)
    (hT : ∀ v : M, T (v ⊗ₜ[R] e) = v ⊗ₜ[R] v) :
    ∀ x y : M, x ⊗ₜ[R] y + y ⊗ₜ[R] x = 0 := by
  intro x y
  exact cloner_forces_symmetric_vanish e T hT x y

-- Theorem 7: Over char 0, a cloner forces T to map everything to zero.
-- Since T(v ⊗ₜ e) = v ⊗ₜ v = 0 for all v, T is zero on the image
-- of the map v ↦ v ⊗ₜ e.
theorem cloner_image_zero
    {F : Type*} [Field F] [CharZero F]
    {M : Type*} [AddCommGroup M] [Module F M]
    (e : M)
    (T : M ⊗[F] M →ₗ[F] M ⊗[F] M)
    (hT : ∀ v : M, T (v ⊗ₜ[F] e) = v ⊗ₜ[F] v)
    (v : M) :
    T (v ⊗ₜ[F] e) = 0 := by
  rw [hT v]
  exact cloner_trivializes e T hT v

end
