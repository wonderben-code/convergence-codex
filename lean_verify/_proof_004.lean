/-
  Convergence Codex — Proof #4 (972e8755e315)
  Proposition: Phase transitions represent symmetry-breaking events where
  macroscopic order emerges through collective behavior, governed by
  universal principles that transcend microscopic details.

  Formalisation: We model the Landau theory of symmetry breaking via
  the quartic potential V(β, x) = x⁴ - β·x². We prove:
  1. The potential is Z₂-symmetric: V(β, -x) = V(β, x)
  2. Subcritical regime (β ≤ 0): x = 0 is the global minimum (symmetric phase)
  3. Supercritical regime (β > 0): the minimum is NOT at x = 0 (broken phase)
  4. The critical threshold is sharp: β = 0 separates the two regimes
  5. Symmetry-breaking minima come in Z₂-related pairs
  6. The broken-phase potential value is negative (energy gain)
  7. Universality: the rescaled potential is parameter-free

  Upgrade notes (v2):
  - Added broken_phase_pair: Z₂ symmetry gives twin minima
  - Added broken_phase_energy: explicit energy at the minimum
  - Added universality_rescaling: the Landau potential is universal
  - All proofs genuine, no sorry
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

-- The Landau potential: V(β, x) = x⁴ - β·x²
def landau (β x : ℝ) : ℝ := x ^ 4 - β * x ^ 2

-- Theorem 1: Z₂ symmetry — the potential is invariant under x ↦ -x
theorem landau_Z2_symmetric (β x : ℝ) :
    landau β (-x) = landau β x := by
  unfold landau; ring

-- Theorem 2: V(β, 0) = 0 for all β (the symmetric point always exists)
theorem landau_at_origin (β : ℝ) : landau β 0 = 0 := by
  unfold landau; ring

-- Theorem 3: Subcritical regime — for β ≤ 0, x = 0 is the global minimum
-- i.e., V(β, x) ≥ 0 = V(β, 0) for all x
theorem landau_subcritical (β x : ℝ) (hβ : β ≤ 0) :
    0 ≤ landau β x := by
  unfold landau
  -- V(β, x) = x⁴ - β·x² = x⁴ + |β|·x² ≥ 0 since β ≤ 0 means -β ≥ 0
  nlinarith [sq_nonneg x, sq_nonneg (x ^ 2)]

-- Theorem 4: Supercritical regime — for β > 0, the minimum is NOT at x = 0
-- i.e., there exists x ≠ 0 with V(β, x) < 0 = V(β, 0)
theorem landau_supercritical (β : ℝ) (hβ : 0 < β) :
    ∃ x : ℝ, x ≠ 0 ∧ landau β x < 0 := by
  -- Witness: x = Real.sqrt(β/2). Then x² = β/2, x⁴ = β²/4
  -- V = β²/4 - β·(β/2) = β²/4 - β²/2 = -β²/4 < 0
  use Real.sqrt (β / 2)
  refine ⟨?_, ?_⟩
  · -- sqrt(β/2) ≠ 0 since β/2 > 0
    exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  · -- V(β, sqrt(β/2)) = -β²/4 < 0
    unfold landau
    have h1 : Real.sqrt (β / 2) ^ 2 = β / 2 :=
      Real.sq_sqrt (by linarith : (0 : ℝ) ≤ β / 2)
    have h2 : Real.sqrt (β / 2) ^ 4 = (β / 2) ^ 2 := by
      have : Real.sqrt (β / 2) ^ 4 = (Real.sqrt (β / 2) ^ 2) ^ 2 := by ring
      rw [this, h1]
    rw [h2, h1]
    nlinarith [sq_nonneg β]

-- Theorem 5: Sharp critical threshold — the transition occurs exactly at β = 0
-- For β ≤ 0: symmetric phase (minimum at origin)
-- For β > 0: broken phase (minimum away from origin)
theorem landau_critical_threshold :
    (∀ β ≤ (0 : ℝ), ∀ x : ℝ, 0 ≤ landau β x) ∧
    (∀ β > (0 : ℝ), ∃ x : ℝ, x ≠ 0 ∧ landau β x < 0) := by
  exact ⟨fun β hβ x => landau_subcritical β x hβ,
         fun β hβ => landau_supercritical β hβ⟩

-- Theorem 6: Broken-phase minima come in Z₂-related pairs.
-- If x₀ witnesses the broken phase, so does -x₀, at the same energy.
theorem broken_phase_pair (β x₀ : ℝ) (hx : x₀ ≠ 0) (hV : landau β x₀ < 0) :
    (-x₀) ≠ 0 ∧ landau β (-x₀) < 0 := by
  constructor
  · exact neg_ne_zero.mpr hx
  · rw [landau_Z2_symmetric]; exact hV

-- Theorem 7: The potential at the critical point β = 0 is purely quartic.
-- V(0, x) = x⁴ ≥ 0, and V(0, x) = 0 iff x = 0.
theorem landau_at_criticality (x : ℝ) :
    landau 0 x = x ^ 4 := by
  unfold landau; ring

-- Theorem 8: At criticality, V(0, x) = 0 iff x = 0.
-- The unique minimum at criticality is the symmetric point.
theorem landau_critical_unique_min (x : ℝ) :
    landau 0 x = 0 ↔ x = 0 := by
  rw [landau_at_criticality]
  constructor
  · intro h
    -- x⁴ = 0 implies x² = 0 implies x = 0
    have hx2 : x ^ 2 = 0 := by nlinarith [sq_nonneg (x ^ 2)]
    have : x = 0 := by
      have := sq_eq_zero_iff.mp hx2
      exact this
    exact this
  · intro h
    rw [h]; ring

-- Theorem 9: Universality of the Landau potential (for β > 0).
-- V(β, √β · t) = β²(t⁴ - t²): the rescaled potential is parameter-free.
-- This is the mathematical content of universality: all systems in the
-- same universality class have the same rescaled potential shape.
theorem landau_universality (β t : ℝ) (hβ : 0 < β) :
    landau β (Real.sqrt β * t) = β ^ 2 * (t ^ 4 - t ^ 2) := by
  unfold landau
  have hsq : (Real.sqrt β * t) ^ 2 = β * t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hβ)]
  have hfour : (Real.sqrt β * t) ^ 4 = β ^ 2 * t ^ 4 := by
    have : (Real.sqrt β * t) ^ 4 = ((Real.sqrt β * t) ^ 2) ^ 2 := by ring
    rw [this, hsq]; ring
  rw [hfour, hsq]; ring

-- Theorem 10: For β > 0, the energy at the minimum x = √(β/2) is exactly
-- -β²/4, independent of microscopic details. This is the Landau universality:
-- the energy gain from symmetry breaking depends only on β.
theorem broken_phase_energy (β : ℝ) (hβ : 0 < β) :
    landau β (Real.sqrt (β / 2)) = -(β ^ 2 / 4) := by
  unfold landau
  have h1 : Real.sqrt (β / 2) ^ 2 = β / 2 :=
    Real.sq_sqrt (by linarith : (0 : ℝ) ≤ β / 2)
  have h2 : Real.sqrt (β / 2) ^ 4 = (β / 2) ^ 2 := by
    have : Real.sqrt (β / 2) ^ 4 = (Real.sqrt (β / 2) ^ 2) ^ 2 := by ring
    rw [this, h1]
  rw [h2, h1]; ring

-- Theorem 11: The broken-phase energy is always negative and scales as β².
-- The energy gain from ordering grows quadratically with distance from
-- the critical point.
theorem broken_phase_energy_negative (β : ℝ) (hβ : 0 < β) :
    landau β (Real.sqrt (β / 2)) < 0 := by
  rw [broken_phase_energy β hβ]
  nlinarith [sq_nonneg β]

end
