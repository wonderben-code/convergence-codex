/-
  F4.1b + F4.1m: Dimension Formula and Trace Cyclicity
  — GENUINE Mathlib-Backed Proofs

  Two foundational results proven with real Lean 4 tactics and Mathlib imports:

  1. DIMENSION FORMULA (F4.1b): dim(Mₙ(ℂ)) = n² for the cascade levels
     D₁ = M₂(ℂ):        dim = 4  = 2²
     D₂ = M₄(ℂ):        dim = 16 = 4²  = 2⁴
     D₃ = M₁₆(ℂ):       dim = 256 = 16² = 2⁸
     General: dim(Mₙ(ℂ)) = n²
     All proven via Module.finrank_matrix (genuine Mathlib finrank).

  2. TRACE CYCLICITY (F4.1m): Tr(AB) = Tr(BA) for finite-dimensional matrices
     Used in: gauge invariance, anomaly cancellation, spectral action
     All proven via Matrix.trace_mul_comm.

  Machine-verified: genuine Mathlib proofs, 0 sorry.
-/

import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

open Matrix

-- ============================================================================
-- SECTION 1: Dimension Formula — dim(Mₙ(ℂ)) = n²
-- ============================================================================

/-- The ℂ-vector space dimension of M₂(ℂ) is 4 = 2².
    This is the dimension of D₁ = End(ℂ²) in the cascade. -/
theorem dim_M2 : Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 4 := by
  simp [Module.finrank_matrix, Fintype.card_fin]

/-- The ℂ-vector space dimension of M₄(ℂ) is 16 = 4².
    This is the dimension of D₂ = End(M₂(ℂ)) in the cascade. -/
theorem dim_M4 : Module.finrank ℂ (Matrix (Fin 4) (Fin 4) ℂ) = 16 := by
  simp [Module.finrank_matrix, Fintype.card_fin]

/-- The ℂ-vector space dimension of M₁₆(ℂ) is 256 = 16².
    This is the dimension of D₃ = End(M₄(ℂ)) in the cascade. -/
theorem dim_M16 : Module.finrank ℂ (Matrix (Fin 16) (Fin 16) ℂ) = 256 := by
  simp [Module.finrank_matrix, Fintype.card_fin]

/-- General dimension formula: dim(Mₙ(ℂ)) = n² for any n.
    This is the foundation of the cascade dimension counting:
    End maps an n-dimensional algebra to an n²-dimensional one. -/
theorem dim_Mn (n : ℕ) : Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) = n * n := by
  simp [Module.finrank_matrix, Fintype.card_fin]

/-- Cascade dimension at D₁: dim = 2² -/
theorem cascade_dim_D1 : Module.finrank ℂ (Matrix (Fin 2) (Fin 2) ℂ) = 2 ^ 2 := by
  simp [Module.finrank_matrix, Fintype.card_fin]

/-- Cascade dimension at D₂: dim = 2⁴ -/
theorem cascade_dim_D2 : Module.finrank ℂ (Matrix (Fin 4) (Fin 4) ℂ) = 2 ^ 4 := by
  simp [Module.finrank_matrix, Fintype.card_fin]

/-- Cascade dimension at D₃: dim = 2⁸ -/
theorem cascade_dim_D3 : Module.finrank ℂ (Matrix (Fin 16) (Fin 16) ℂ) = 2 ^ 8 := by
  simp [Module.finrank_matrix, Fintype.card_fin]

-- ============================================================================
-- SECTION 2: Trace Cyclicity — Tr(AB) = Tr(BA)
-- ============================================================================

/-- Trace cyclicity for M₂(ℂ): Tr(AB) = Tr(BA).
    Foundation of gauge invariance at D₁. -/
theorem trace_cyclic_M2 (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

/-- Trace cyclicity for M₄(ℂ): Tr(AB) = Tr(BA).
    Foundation of gauge invariance at D₂ (Pati-Salam level). -/
theorem trace_cyclic_M4 (A B : Matrix (Fin 4) (Fin 4) ℂ) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

/-- Trace cyclicity for M₁₆(ℂ): Tr(AB) = Tr(BA).
    Foundation of gauge invariance at D₃. -/
theorem trace_cyclic_M16 (A B : Matrix (Fin 16) (Fin 16) ℂ) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

/-- General trace cyclicity: Tr(AB) = Tr(BA) for any Mₙ(ℂ).
    This is the mathematical foundation of:
    - Gauge invariance of the spectral action Tr(f(D²/Λ²))
    - Anomaly cancellation (traces of generator products)
    - Ward identities (quantum gauge invariance) -/
theorem trace_cyclic_general (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

