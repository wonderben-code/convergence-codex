/-
  Emergence Stage 1: The Lineage Is Concrete
  ==========================================

  Paper E — Emergence of the Standard Model from the Generator Construction

  CLAIM: In FdVect_ℂ (finite-dimensional complex vector spaces, compact closed),
  the iterated internal hom starting from I⊕I = ℂ² produces:

    D₀ = ℂ²                    (dim 2)
    D₁ = [D₀, D₀] = End(ℂ²)    (dim 4)    ≅ M₂(ℂ)
    D₂ = [D₁, D₁] = End²(ℂ²)   (dim 16)   ≅ M₄(ℂ)
    D₃ = [D₂, D₂] = End³(ℂ²)   (dim 256)  ≅ M₁₆(ℂ)
    D₄ = [D₃, D₃] = End⁴(ℂ²)   (dim 65536) ≅ M₂₅₆(ℂ)

  General formula: dim(Dₙ) = 2^(2^n)

  The lineage follows doubly-exponential growth with no free parameters.
  This is the concrete realisation of the Generator construction in the
  category where quantum mechanics lives.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1
  Target: 0 sorry
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic

open Module

/-!
## Part 1: The Dimension Recurrence (Pure Arithmetic)

The endomorphism iteration squares the dimension at each step:
  d₀ = 2
  d_{n+1} = d_n²

This is because dim(End(V)) = (dim V)² for finite-dimensional V.
Starting from dim = 2, the sequence is 2, 4, 16, 256, 65536, ...
We prove this equals 2^(2^n) — doubly-exponential growth.
-/

/-- The dimension at iteration n: d₀ = 2, d_{n+1} = d_n².
    Represents dim(Dₙ) where Dₙ = Endⁿ(ℂ²). -/
def emergenceDim : ℕ → ℕ
  | 0 => 2
  | n + 1 => emergenceDim n ^ 2

/-- D₀ = ℂ² has dimension 2. -/
@[simp] theorem emergenceDim_zero : emergenceDim 0 = 2 := rfl

/-- D₁ = End(ℂ²) = M₂(ℂ) has dimension 4. -/
theorem emergenceDim_one : emergenceDim 1 = 4 := by native_decide

/-- D₂ = End(M₂(ℂ)) = M₄(ℂ) has dimension 16. -/
theorem emergenceDim_two : emergenceDim 2 = 16 := by native_decide

/-- D₃ = End(M₄(ℂ)) = M₁₆(ℂ) has dimension 256. -/
theorem emergenceDim_three : emergenceDim 3 = 256 := by native_decide

/-- D₄ = End(M₁₆(ℂ)) = M₂₅₆(ℂ) has dimension 65536. -/
theorem emergenceDim_four : emergenceDim 4 = 65536 := by native_decide

/-- **Theorem 1.5 (Dimension Formula):** dim(Dₙ) = 2^(2^n).
    The lineage grows doubly-exponentially with no free parameters.
    Proof by induction: if dₙ = 2^(2^n), then
    d_{n+1} = (2^(2^n))² = 2^(2·2^n) = 2^(2^(n+1)). -/
theorem emergenceDim_eq_pow (n : ℕ) : emergenceDim n = 2 ^ 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold emergenceDim
    rw [ih, ← pow_mul]
    congr 1

/-- The dimension is always positive (non-degenerate). -/
theorem emergenceDim_pos (n : ℕ) : 0 < emergenceDim n := by
  simp only [emergenceDim_eq_pow]
  exact pow_pos (by norm_num : (0 : ℕ) < 2) _

/-- The dimension is strictly increasing: each iteration grows.
    The lineage never collapses — it only expands. -/
theorem emergenceDim_strict_mono : StrictMono emergenceDim := by
  intro a b hab
  simp only [emergenceDim_eq_pow]
  exact Nat.pow_lt_pow_right (by norm_num : 1 < 2)
    (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hab)

/-!
## Part 2: Dimension of ℂⁿ

In FdVect_ℂ, the unit object I = ℂ, and the seed I⊕I = ℂ².
We verify dim(ℂⁿ) = n using Mathlib's finrank.
-/

/-- **Theorem 1.1:** dim(ℂⁿ) = n. The standard basis has n elements. -/
theorem finrank_fin_complex (n : ℕ) : finrank ℂ (Fin n → ℂ) = n := by
  simp [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The seed object: dim(I⊕I) = dim(ℂ²) = 2. -/
theorem dim_seed : finrank ℂ (Fin 2 → ℂ) = 2 := finrank_fin_complex 2

/-- The unit object: dim(I) = dim(ℂ) = 1. -/
theorem dim_unit : finrank ℂ ℂ = 1 := finrank_self ℂ

/-!
## Part 3: End(ℂⁿ) ≅ Mₙ(ℂ) — The Matrix Identification

Every endomorphism of ℂⁿ corresponds to an n×n complex matrix.
This is the isomorphism D₁ ≅ M₂(ℂ), D₂ ≅ M₄(ℂ), etc.
The isomorphism is canonical given the standard basis.
-/

/-- **Theorem 1.2-1.4 (Matrix Identification):**
    End(ℂⁿ) ≅ Mₙ(ℂ) as ℂ-linear spaces, via the standard basis.
    This identifies each Dₙ with a matrix algebra. -/
noncomputable def endEquivMatrix (n : ℕ) :
    ((Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))

/-!
## Part 4: dim(End(V)) = (dim V)² — The Squaring Lemma

This is the engine of the lineage: each iteration squares the dimension.
For any finite-dimensional ℂ-vector space V, End(V) = V →ₗ V has
dimension (dim V)². Combined with the recurrence, this gives 2^(2^n).
-/

/-- **Theorem (Dimension Squaring):** For any finite-dimensional ℂ-vector space V,
    dim(End(V)) = (dim V)². This is why the lineage grows doubly-exponentially:
    squaring the dimension is the same as doubling the exponent. -/
theorem finrank_end_sq (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V] :
    finrank ℂ (V →ₗ[ℂ] V) = (finrank ℂ V) ^ 2 := by
  rw [Module.finrank_linearMap, sq]

/-!
## Part 5: The Concrete Lineage Dimensions

Connecting the abstract dimension formula to concrete endomorphism spaces.
-/

/-- **Theorem 1.2:** dim(D₁) = dim(End(ℂ²)) = 4 = 2².
    The first iteration produces a 4-dimensional algebra. -/
theorem dim_D1 : finrank ℂ ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = 4 := by
  rw [finrank_end_sq, finrank_fin_complex]; norm_num

/-- D₁ dimension matches the recurrence. -/
theorem dim_D1_eq_seq :
    finrank ℂ ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = emergenceDim 1 := by
  rw [dim_D1, emergenceDim_one]

/-!
## Part 6: The Lineage Summary

All results combined into a single theorem establishing the
concrete doubly-exponential lineage.
-/

/-- **THE LINEAGE IS CONCRETE:**
    The iterated internal hom [D, D] in FdVect_ℂ starting from ℂ²
    produces a doubly-exponential dimension sequence:
    2, 4, 16, 256, 65536, ...
    equal to 2^(2^n) at each stage.

    Combined with the matrix identification End(ℂⁿ) ≅ Mₙ(ℂ),
    the lineage is: ℂ² → M₂(ℂ) → M₄(ℂ) → M₁₆(ℂ) → M₂₅₆(ℂ) → ...

    No free parameters. The seed I⊕I and the operation [−,−]
    determine the entire sequence. -/
theorem lineage_is_concrete :
    -- The seed
    (emergenceDim 0 = 2) ∧
    -- The first four iterations
    (emergenceDim 1 = 4) ∧
    (emergenceDim 2 = 16) ∧
    (emergenceDim 3 = 256) ∧
    (emergenceDim 4 = 65536) ∧
    -- The general formula
    (∀ n, emergenceDim n = 2 ^ 2 ^ n) ∧
    -- Strict growth (never collapses)
    (StrictMono emergenceDim) ∧
    -- The concrete dimension of ℂ²
    (finrank ℂ (Fin 2 → ℂ) = 2) ∧
    -- The concrete dimension of End(ℂ²)
    (finrank ℂ ((Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) = 4) :=
  ⟨rfl, emergenceDim_one, emergenceDim_two, emergenceDim_three,
   emergenceDim_four, emergenceDim_eq_pow, emergenceDim_strict_mono,
   dim_seed, dim_D1⟩
