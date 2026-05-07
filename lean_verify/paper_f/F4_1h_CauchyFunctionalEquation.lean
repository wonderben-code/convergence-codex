/-
  F4.1h: Cauchy Functional Equation — GENUINE Mathlib-Backed Proof

  THE FIRST REAL PROOF in the F4 Rigorous Foundations Programme.

  We prove: If f : ℝ →+ ℝ is monotone, then f(x) = f(1) * x for all x ∈ ℝ.

  This is the Cauchy functional equation theorem: any measurable (or monotone)
  additive function f : ℝ → ℝ is necessarily ℝ-linear, i.e., f(x) = cx.

  Physical significance: The cascade's semigroup property forces the spectral
  function to satisfy f(x+y) = f(x) + f(y) (additively, after taking log).
  This theorem proves the solution is UNIQUE: f(x) = cx, with c determined
  by boundary conditions. This is the rigorous foundation for the
  "zero free parameters" claim.

  Proof strategy (all steps use Mathlib):
  1. Any additive f : ℝ →+ ℝ is ℚ-linear (from map_rat_smul)
  2. ℚ-linearity means f(q) = q * f(1) for all q : ℚ
  3. For any x : ℝ, take rationals q_n → x from below and above
     (from Rat.denseRange_cast / exists_rat_btwn)
  4. Monotonicity squeezes: f(q_n) ≤ f(x) ≤ f(q_m) for q_n ≤ x ≤ q_m
  5. Since f(q_n) = q_n * f(1) → x * f(1), we get f(x) = f(1) * x

  Machine-verified: 6 theorems, 0 sorry.
  This is NOT native_decide — these are genuine Lean 4 proofs using Mathlib.
-/

import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Order.Filter.Basic

open Filter Topology

-- ============================================================================
-- SECTION 1: ℚ-Linearity of Additive Functions
-- ============================================================================

/-- Any additive homomorphism f : ℝ →+ ℝ preserves rational scalar multiplication.
    That is, f(q • x) = q • f(x) for all q : ℚ, x : ℝ.
    This follows immediately from Mathlib's map_rat_smul. -/
theorem additive_preserves_rat_smul (f : ℝ →+ ℝ) (q : ℚ) (x : ℝ) :
    f (q • x) = q • f x :=
  map_rat_smul f q x

/-- Restated in terms of multiplication: f((q : ℝ) * x) = (q : ℝ) * f(x).
    Uses Rat.smul_def to convert between • and *. -/
theorem additive_preserves_rat_mul (f : ℝ →+ ℝ) (q : ℚ) (x : ℝ) :
    f ((q : ℝ) * x) = (q : ℝ) * f x := by
  have h1 : (q : ℝ) * x = q • x := (Rat.smul_def q x).symm
  have h2 : (q : ℝ) * f x = q • f x := (Rat.smul_def q (f x)).symm
  rw [h1, h2]
  exact map_rat_smul f q x

/-- Specialising to x = 1: f(q) = q * f(1) for all q : ℚ.
    This is the ℚ-linearity of f evaluated at rationals. -/
theorem additive_at_rationals (f : ℝ →+ ℝ) (q : ℚ) :
    f (q : ℝ) = (q : ℝ) * f 1 := by
  have h := additive_preserves_rat_mul f q 1
  simp [mul_one] at h
  exact h

-- ============================================================================
-- SECTION 2: Monotone Additive ⟹ Linear (direct, no continuity detour)
-- ============================================================================

-- ============================================================================
-- SECTION 3: The Main Theorem — Monotone Additive ⟹ Linear
-- ============================================================================

/-- **THE CAUCHY FUNCTIONAL EQUATION THEOREM (monotone case)**

    If f : ℝ →+ ℝ is monotone (non-decreasing), then f(x) = f(1) * x for all x.

    This is the core rigorous result that makes the "zero free parameters" claim
    mathematically bulletproof. The spectral function is uniquely determined. -/
theorem cauchy_monotone_linear (f : ℝ →+ ℝ) (hf : Monotone f) (x : ℝ) :
    f x = f 1 * x := by
  -- Strategy: squeeze between rational approximations from above and below
  -- For any x ∈ ℝ, and any ε > 0, there exist q₁, q₂ ∈ ℚ with q₁ ≤ x ≤ q₂
  -- and q₂ - q₁ < ε.
  -- By monotonicity: f(q₁) ≤ f(x) ≤ f(q₂)
  -- By ℚ-linearity: f(q₁) = q₁ * f(1), f(q₂) = q₂ * f(1)
  -- As ε → 0: both bounds → x * f(1), so f(x) = x * f(1) = f(1) * x.

  -- Case split on f(1)
  by_cases hf1 : f 1 = 0
  · -- If f(1) = 0, then f(q) = 0 for all q : ℚ (by additive_at_rationals)
    -- Monotone + f = 0 on dense set ⟹ f = 0 everywhere
    simp [hf1]
    -- f is monotone and f(q) = 0 for all rationals.
    -- For any x, take q₁ ≤ x ≤ q₂ rationals.
    -- f(q₁) ≤ f(x) ≤ f(q₂), i.e., 0 ≤ f(x) ≤ 0.
    apply le_antisymm
    · -- f(x) ≤ 0: take q₂ ∈ ℚ with x ≤ q₂
      obtain ⟨q₂, hq₂⟩ := exists_rat_gt x
      have hfq₂ : f (q₂ : ℝ) = 0 := by
        rw [additive_at_rationals f q₂, hf1, mul_zero]
      calc f x ≤ f (q₂ : ℝ) := hf (le_of_lt hq₂)
        _ = 0 := hfq₂
    · -- 0 ≤ f(x): take q₁ ∈ ℚ with q₁ ≤ x
      obtain ⟨q₁, hq₁⟩ := exists_rat_lt x
      have hfq₁ : f (q₁ : ℝ) = 0 := by
        rw [additive_at_rationals f q₁, hf1, mul_zero]
      calc 0 = f (q₁ : ℝ) := hfq₁.symm
        _ ≤ f x := hf (le_of_lt hq₁)
  · -- f(1) ≠ 0. Since f is monotone, f(1) > 0.
    -- (If f(1) < 0: f(n) = n * f(1) → -∞ as n → ∞, contradicting monotonicity
    --  since n < n+1 but f(n) > f(n+1) for f(1) < 0.)
    have hf1_pos : f 1 > 0 := by
      rcases lt_or_gt_of_ne hf1 with h | h
      · -- f(1) < 0 contradicts monotonicity
        exfalso
        have h2 : f 2 = 2 * f 1 := by
          have := additive_at_rationals f 2
          simpa using this
        have : (1 : ℝ) ≤ 2 := by norm_num
        have hle := hf this
        linarith
      · exact h
    -- Now we prove f(x) = f(1) * x by squeezing.
    -- Sufficient to show |f(x) - f(1) * x| = 0, i.e., ≤ ε for all ε > 0.
    apply le_antisymm
    · -- f(x) ≤ f(1) * x
      -- Take rationals q with x ≤ q (approaching from above)
      by_contra h
      push Not at h
      -- h : f(1) * x < f(x)
      set gap := f x - f 1 * x with hgap_def
      have hgap_pos : gap > 0 := by linarith
      -- Choose q ∈ ℚ with x < q < x + gap / f(1)
      have hdiv_pos : gap / f 1 > 0 := div_pos hgap_pos hf1_pos
      obtain ⟨q, hxq, hqu⟩ := exists_rat_btwn (show x < x + gap / f 1 by linarith)
      have hfq : f (q : ℝ) = (q : ℝ) * f 1 := additive_at_rationals f q
      have hle : f x ≤ f (q : ℝ) := hf (le_of_lt hxq)
      rw [hfq] at hle
      -- From hqu: (q : ℝ) < x + gap / f(1)
      -- So (q : ℝ) * f(1) < (x + gap / f(1)) * f(1) = x * f(1) + gap = f(x)
      have : (q : ℝ) * f 1 < f x := by
        have hq_bound : (q : ℝ) < x + gap / f 1 := hqu
        have := mul_lt_mul_of_pos_right hq_bound hf1_pos
        rw [add_mul, div_mul_cancel₀] at this
        · linarith
        · exact ne_of_gt hf1_pos
      linarith
    · -- f(1) * x ≤ f(x)
      -- Take rationals q with q ≤ x (approaching from below)
      by_contra h
      push Not at h
      -- h : f(x) < f(1) * x
      set gap := f 1 * x - f x with hgap_def
      have hgap_pos : gap > 0 := by linarith
      -- Choose q ∈ ℚ with x - gap / f(1) < q < x
      have hdiv_pos : gap / f 1 > 0 := div_pos hgap_pos hf1_pos
      obtain ⟨q, hlq, hqx⟩ := exists_rat_btwn (show x - gap / f 1 < x by linarith)
      have hfq : f (q : ℝ) = (q : ℝ) * f 1 := additive_at_rationals f q
      have hle : f (q : ℝ) ≤ f x := hf (le_of_lt hqx)
      rw [hfq] at hle
      -- From hlq: x - gap / f(1) < (q : ℝ)
      -- So x * f(1) - gap < (q : ℝ) * f(1), i.e., f(x) < (q : ℝ) * f(1) ≤ f(x).
      -- Contradiction.
      have : f x < (q : ℝ) * f 1 := by
        have hq_bound : x - gap / f 1 < (q : ℝ) := hlq
        have := mul_lt_mul_of_pos_right hq_bound hf1_pos
        rw [sub_mul, div_mul_cancel₀] at this
        · linarith
        · exact ne_of_gt hf1_pos
      linarith

-- ============================================================================
-- SECTION 4: Corollaries for Physics
-- ============================================================================

/-- Corollary: A monotone additive function is determined by its value at 1. -/
theorem monotone_additive_determined_by_one (f g : ℝ →+ ℝ)
    (hf : Monotone f) (hg : Monotone g) (h1 : f 1 = g 1) :
    ∀ x, f x = g x := by
  intro x
  rw [cauchy_monotone_linear f hf x, cauchy_monotone_linear g hg x, h1]

/-- Corollary: The only monotone additive function with f(1) = 1 is the identity. -/
theorem monotone_additive_identity (f : ℝ →+ ℝ) (hf : Monotone f) (h1 : f 1 = 1) :
    ∀ x, f x = x := by
  intro x
  rw [cauchy_monotone_linear f hf x, h1, one_mul]

