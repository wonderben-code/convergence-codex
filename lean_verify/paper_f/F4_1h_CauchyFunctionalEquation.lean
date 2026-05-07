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

  Machine-verified: 14 declarations (13 theorems/lemmas + 1 def), 0 sorry.
  Includes: Cauchy monotone→linear (67-line proof), semigroup→exponential
  (via log composition + Cauchy), zero-free-parameters (additive + multiplicative).
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Topology Real

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

-- ============================================================================
-- SECTION 5: The Semigroup → Exponential Theorem
-- ============================================================================

-- The semigroup version: if g : ℝ → ℝ satisfies g(x+y) = g(x) * g(y),
-- g is everywhere positive, and g is monotone, then g(x) = exp(log(g(1)) * x).
--
-- This follows from the additive version by taking log:
-- log(g(x+y)) = log(g(x)) + log(g(y)), so f := log ∘ g is additive and monotone.
-- Then cauchy_monotone_linear gives f(x) = f(1) * x, so g(x) = exp(f(1) * x).
--
-- The physical constraint g(0) = 1 is automatic (g(0) = g(0+0) = g(0)²
-- so g(0) = 1 since g > 0), and positivity + decay force the sign of c.
-- Normalising Λ absorbs |c|, giving the canonical form g(x) = e^{-x}.

-- Caesar decomposition: build the proof in stages.

/-- Lemma: A positive multiplicative function satisfies g(0) = 1. -/
lemma mult_pos_at_zero (g : ℝ → ℝ) (hpos : ∀ x, 0 < g x)
    (hmul : ∀ x y, g (x + y) = g x * g y) : g 0 = 1 := by
  have h0 := hmul 0 0
  simp at h0
  -- h0 : g 0 = g 0 * g 0, i.e. g(0) = g(0)²
  -- Since g(0) > 0, we can divide both sides by g(0)
  have hg0_pos : g 0 > 0 := hpos 0
  have hg0_ne : g 0 ≠ 0 := ne_of_gt hg0_pos
  nlinarith [sq_nonneg (g 0 - 1)]

/-- Lemma: log ∘ g is additive when g is positive and multiplicative. -/
lemma log_of_mult_is_additive (g : ℝ → ℝ) (hpos : ∀ x, 0 < g x)
    (hmul : ∀ x y, g (x + y) = g x * g y) (x y : ℝ) :
    log (g (x + y)) = log (g x) + log (g y) := by
  rw [hmul x y]
  exact log_mul (ne_of_gt (hpos x)) (ne_of_gt (hpos y))

/-- Lemma: If g is monotone and positive, then log ∘ g is monotone. -/
lemma log_of_monotone_pos_is_monotone (g : ℝ → ℝ) (hpos : ∀ x, 0 < g x)
    (hmon : Monotone g) : Monotone (fun x => log (g x)) := by
  intro a b hab
  exact log_le_log (hpos a) (hmon hab)

/-- Package log ∘ g as an AddMonoidHom when g is positive and multiplicative. -/
noncomputable def logOfMultHom (g : ℝ → ℝ) (hpos : ∀ x, 0 < g x)
    (hmul : ∀ x y, g (x + y) = g x * g y) : ℝ →+ ℝ where
  toFun := fun x => log (g x)
  map_zero' := by
    rw [mult_pos_at_zero g hpos hmul]
    exact log_one
  map_add' := fun x y => log_of_mult_is_additive g hpos hmul x y

/-- **SEMIGROUP EXPONENTIAL FORM THEOREM**

    If g : ℝ → ℝ is positive, multiplicative (g(x+y) = g(x)·g(y)), and monotone,
    then g(x) = exp(log(g(1)) · x) for all x.

    This is the multiplicative analogue of cauchy_monotone_linear. It proves that
    any monotone solution to the multiplicative Cauchy equation is necessarily
    an exponential function. -/
theorem semigroup_exponential_form (g : ℝ → ℝ) (hpos : ∀ x, 0 < g x)
    (hmul : ∀ x y, g (x + y) = g x * g y) (hmon : Monotone g) (x : ℝ) :
    g x = exp (log (g 1) * x) := by
  -- Step 1: Build h = log ∘ g as an AddMonoidHom
  let h := logOfMultHom g hpos hmul
  -- Step 2: h is monotone
  have hh_mon : Monotone h := log_of_monotone_pos_is_monotone g hpos hmon
  -- Step 3: By cauchy_monotone_linear, h(x) = h(1) * x
  have hh_linear := cauchy_monotone_linear h hh_mon x
  -- hh_linear : h x = h 1 * x, i.e., log(g(x)) = log(g(1)) * x
  -- Step 4: Exponentiate both sides
  have hgx_pos : 0 < g x := hpos x
  -- log(g(x)) = log(g(1)) * x
  change log (g x) = log (g 1) * x at hh_linear
  -- Therefore g(x) = exp(log(g(1)) * x)
  rw [← exp_log hgx_pos, hh_linear]

-- ============================================================================
-- SECTION 6: Zero Free Parameters
-- ============================================================================

-- PHYSICAL CONCLUSION: Zero Free Parameters
--
-- The cascade forces f(x+y) = f(x)·f(y) (multiplicative semigroup property).
-- Taking logarithms: log f(x+y) = log f(x) + log f(y) (additive).
-- The cascade's ordering forces monotonicity.
-- By cauchy_monotone_linear: log f(x) = c·x, hence f(x) = e^{cx}.
-- Physical constraints (f(0)=1, f>0, f→0) force c<0.
-- Absorbed into the cutoff Λ: the canonical form is f(x) = e^{-x}.

/-- Any two monotone additive functions with the same value at 1 are identical
    everywhere. This is the additive "zero free parameters" result:
    monotonicity + additivity + one boundary value determines the function
    completely. -/
theorem zero_free_parameters_additive (f g : ℝ →+ ℝ)
    (hf : Monotone f) (hg : Monotone g) (h1 : f 1 = g 1) :
    ∀ x, f x = g x :=
  monotone_additive_determined_by_one f g hf hg h1

/-- Any two monotone positive multiplicative functions with the same value at 1
    are identical everywhere. This is the multiplicative "zero free parameters"
    result: the semigroup property + monotonicity + one normalisation condition
    leaves zero degrees of freedom.

    Proof: by semigroup_exponential_form, both are exp(log(g(1)) * x), and since
    g(1) = h(1), they are the same function. -/
theorem zero_free_parameters_multiplicative
    (g h : ℝ → ℝ)
    (hg_pos : ∀ x, 0 < g x) (hh_pos : ∀ x, 0 < h x)
    (hg_mul : ∀ x y, g (x + y) = g x * g y) (hh_mul : ∀ x y, h (x + y) = h x * h y)
    (hg_mon : Monotone g) (hh_mon : Monotone h)
    (h1 : g 1 = h 1) :
    ∀ x, g x = h x := by
  intro x
  rw [semigroup_exponential_form g hg_pos hg_mul hg_mon x,
      semigroup_exponential_form h hh_pos hh_mul hh_mon x, h1]

/-- The spectral function is uniquely determined: if f is a monotone additive
    function with f(1) = 1, then f is the identity. This is the strongest
    form of "zero free parameters" — the normalisation f(1) = 1 leaves
    literally no freedom in the function.

    Applied to the cascade: the spectral function satisfies the Cauchy equation
    (from the semigroup property after taking log), monotonicity comes from the
    cascade ordering, and the boundary condition f(1) = 1 comes from physical
    normalisation. Therefore f = id is the unique solution. -/
theorem zero_free_parameters_from_cauchy (f : ℝ →+ ℝ)
    (hf : Monotone f) (h1 : f 1 = 1) :
    ∀ x, f x = x :=
  monotone_additive_identity f hf h1
