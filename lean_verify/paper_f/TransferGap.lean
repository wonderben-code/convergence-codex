/-
  TransferGap: A Genuine Spectral Gap from a Genuine Operator
  ===========================================================

  First stair of the L²-spectral-theory gap (tree §11.6, old gap #6; spine
  L23), per the assessment's recommended move: sidestep unbounded operators
  and produce a BOUNDED transfer operator whose spectral gap is DERIVED
  from its spectrum by Mathlib's spectral machinery — in contrast to the
  estate's certificate files (TransferMatrix.lean, F3_9g chain), where
  "gap" is a real-number FIELD supplied by the caller and no operator of
  any kind appears (Phase 0 audit).

  WHAT THIS FILE PROVES (exactly this, nothing more):

  For the diagonal heat-kernel transfer operator T = diag(e^{−Δ·k}),
  k = 0, 1, …, n (a MODEL operator — chosen, not derived; see below):

  1. `transferOp_spectrum` — σ(T) = {e^{−Δ·k} : k = 0…n}, computed by
     Mathlib's eigenvalue machinery (`spectrum_diagonal`), not
     asserted.
  2. `one_mem_spectrum` — 1 ∈ σ(T): the ground-state eigenvalue.
  3. `spectrum_gap` — for Δ > 0, every μ ∈ σ(T) is either the ground
     eigenvalue 1 or satisfies μ ≤ e^{−Δ} < 1: THE SPECTRAL GAP, as a
     statement about the actual spectrum of an actual operator.
  4. `gap_size_pos` — the gap 1 − e^{−Δ} is strictly positive for Δ > 0.

  WHAT IS AND IS NOT ACHIEVED: the step up from the certificate files is
  that the gap is now a DERIVED property of an operator's computed
  spectrum (σ(T) via eigenvalue theory) rather than a stored scalar. What
  remains exactly as open as before: T here is a chosen diagonal MODEL of
  a transfer operator — it is not derived from any field-theoretic
  Hamiltonian, path-integral kernel, or lattice theory. Deriving the
  transfer operator (and hence the physical mass gap) from dynamics is
  the actual content of old gaps #3/#6 and remains open; the published
  [PREDICTED]/[CLAIMED] tags there should not move on account of this
  file. The infinite-dimensional version (lp-space operator, continuous
  functional calculus) is the named next stair.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Data.Complex.Basic

open Matrix Real

noncomputable section

namespace TransferGap

variable (Δ : ℝ) (n : ℕ)

/-- The diagonal heat-kernel transfer operator T = diag(e^{−Δ·k}),
    k = 0, …, n. A model operator: chosen, not derived (see header). -/
def transferOp : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.diagonal (fun k => exp (-Δ * (k : ℕ)))

/-- **The spectrum, computed**: σ(T) is exactly the set of eigenvalues
    {e^{−Δ·k}}, via Mathlib's `spectrum_diagonal` (eigenvalue
    machinery, not assertion). -/
theorem transferOp_spectrum :
    spectrum ℝ (transferOp Δ n)
      = Set.range (fun k : Fin (n + 1) => exp (-Δ * (k : ℕ))) :=
  spectrum_diagonal _

/-- 1 ∈ σ(T): the ground-state eigenvalue (k = 0). -/
theorem one_mem_spectrum : (1 : ℝ) ∈ spectrum ℝ (transferOp Δ n) := by
  rw [transferOp_spectrum]
  exact ⟨0, by simp⟩

/-- **The spectral gap**: for Δ > 0, every spectral point is either the
    ground eigenvalue 1 or lies at or below e^{−Δ} < 1. -/
theorem spectrum_gap (hΔ : 0 < Δ) (μ : ℝ)
    (hμ : μ ∈ spectrum ℝ (transferOp Δ n)) :
    μ = 1 ∨ μ ≤ exp (-Δ) := by
  rw [transferOp_spectrum] at hμ
  obtain ⟨k, rfl⟩ := hμ
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
  · left
    simp [hk]
  · right
    apply exp_le_exp.mpr
    have : (1 : ℝ) ≤ (k : ℕ) := by exact_mod_cast hk
    nlinarith

/-- The gap size 1 − e^{−Δ} is strictly positive for Δ > 0: the excited
    spectrum is uniformly separated from the ground eigenvalue. -/
theorem gap_size_pos (hΔ : 0 < Δ) : 0 < 1 - exp (-Δ) := by
  have h : exp (-Δ) < 1 := exp_lt_one_iff.mpr (by linarith)
  linarith

end TransferGap
