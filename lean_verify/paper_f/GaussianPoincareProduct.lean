/-
  GaussianPoincareProduct: Tensorising the Gaussian Poincaré Inequality
  ====================================================================

  Campaign-3 unit 1. `GaussianPoincare.lean` proved Var_γ(p) ≤ E_γ[(p′)²] in
  ONE dimension for polynomial test functions, and listed tensorisation as
  the next stair — it is the stair the cascade actually needs, since the
  space there is Herm₄(ℂ) ≅ ℝ¹⁶.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  **The tensorisation step**, `poincare_two`: for a bivariate polynomial q,

      Var(q) ≤ E[(∂_y q)²] + E[(∂_x q)²]

  where E is the iterated Gaussian expectation E_x[E_y[·]], and
  `poincare_two_integral` states the same thing with every expectation
  written as an actual integral against Mathlib's `gaussianReal 0 1`, taken
  iteratedly. The argument is the classical one, and each of its three joints
  is now a theorem rather than a gesture:

  * the inner variance is controlled by the 1-d inequality POINTWISE in x and
    then integrated — which needs positivity of the Gaussian functional
    (`gmean_nonneg`, `gmean_mono`), proven here for the first time;
  * the outer variance is controlled by the 1-d inequality applied to the
    inner expectation, which is a genuine polynomial in x (`Ey`, `eval_Ey`);
  * differentiating under the inner expectation (`Ey_dX`) is EXACT here, not
    an analytic interchange, because the inner expectation is a
    moment-weighted sum of coefficients;
  * the two halves are joined by Cauchy–Schwarz in the form
    (E h)² ≤ E[h²], i.e. `gvar_nonneg`.

  NOT proven here:

  * **Dimension n.** This is the induction STEP (2 = 1 + 1), not the
    induction. Reaching ℝ¹⁶ ≅ Herm₄(ℂ) means iterating it, which requires
    the base structure (functional + positivity + the inequality) to be
    abstracted over an arbitrary coefficient ring — the next unit. Nothing
    here says anything about 16 variables.
  * **The product MEASURE.** `poincare_two_integral` is stated with ITERATED
    integrals. Identifying that with a single integral against
    `Measure.prod` is Fubini, and needs integrability of the polynomial on
    the product; it is not done here, so no theorem in this file mentions a
    two-dimensional measure.
  * Everything the 1-d file already disclaimed: polynomial test functions
    only, and this is the standard Gaussian, not a spectral-action measure.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import GaussianPoincare

open Polynomial MeasureTheory

noncomputable section

namespace GaussianPoincareProduct

open GaussianPoincare

/-! ## 1. Positivity of the Gaussian functional

    The 1-d file built `gmean` and proved the Poincaré inequality for it, but
    never needed positivity. Tensorisation does: the inner inequality has to
    be integrated over the outer variable, which requires that `gmean`
    respects ≤. -/

theorem gmean_sub (p q : ℝ[X]) : gmean (p - q) = gmean p - gmean q := by
  unfold gmean
  rw [I_sub, sub_div]

theorem gmean_C (c : ℝ) : gmean (C c) = c := by
  have h : (C c : ℝ[X]) = c • 1 := by
    rw [smul_eq_C_mul, mul_one]
  rw [h, gmean_smul, gmean_one, mul_one]

theorem gmean_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    gmean (∑ i ∈ s, f i) = ∑ i ∈ s, gmean (f i) := by
  unfold gmean
  rw [I_sum, Finset.sum_div]

/-- **Positivity**: a polynomial that is nonnegative on the whole line has
    nonnegative Gaussian mean. -/
theorem gmean_nonneg {p : ℝ[X]} (hp : ∀ x : ℝ, 0 ≤ p.eval x) : 0 ≤ gmean p := by
  unfold gmean I
  apply div_nonneg _ (le_of_lt Z_pos)
  apply integral_nonneg
  intro x
  exact mul_nonneg (hp x) (le_of_lt (W_pos x))

/-- Monotonicity of the Gaussian mean. -/
theorem gmean_mono {p q : ℝ[X]} (h : ∀ x : ℝ, p.eval x ≤ q.eval x) :
    gmean p ≤ gmean q := by
  have hd : 0 ≤ gmean (q - p) := by
    apply gmean_nonneg
    intro x
    rw [Polynomial.eval_sub]
    linarith [h x]
  rw [gmean_sub] at hd
  linarith

/-- **The variance is nonnegative** — equivalently (E p)² ≤ E[p²], which is
    the Cauchy–Schwarz step tensorisation needs. -/
theorem gvar_nonneg (p : ℝ[X]) : 0 ≤ gvar p := by
  have hexp : gmean ((p - C (gmean p)) * (p - C (gmean p)))
      = gmean (p * p) - (gmean p) ^ 2 := by
    have hring : (p - C (gmean p)) * (p - C (gmean p))
        = p * p - (gmean p) • p - (gmean p) • p + ((gmean p) * (gmean p)) • 1 := by
      simp only [smul_eq_C_mul, C_mul, mul_one]
      ring
    rw [hring, gmean_add, gmean_sub, gmean_sub, gmean_smul, gmean_smul,
      gmean_one]
    ring
  have hnn : 0 ≤ gmean ((p - C (gmean p)) * (p - C (gmean p))) := by
    apply gmean_nonneg
    intro x
    rw [Polynomial.eval_mul]
    exact mul_self_nonneg _
  unfold gvar
  rw [← hexp]
  exact hnn

/-- Squares have nonnegative Gaussian mean. -/
theorem gmean_mul_self_nonneg (p : ℝ[X]) : 0 ≤ gmean (p * p) := by
  apply gmean_nonneg
  intro x
  rw [Polynomial.eval_mul]
  exact mul_self_nonneg _

/-! ## 2. The Gaussian mean as a coefficient sum

    To integrate a bivariate polynomial in one variable and keep a POLYNOMIAL
    in the other, the mean has to be computed coefficientwise. -/

/-- The Gaussian moments m₍ₙ₎ = E[xⁿ], as values of `gmean` on monomials. -/
def mom (n : ℕ) : ℝ := gmean ((X : ℝ[X]) ^ n)

/-- The Gaussian mean is the moment-weighted sum of the coefficients. -/
theorem gmean_eq_sum_range {p : ℝ[X]} {N : ℕ} (hN : p.natDegree < N + 1) :
    gmean p = ∑ n ∈ Finset.range (N + 1), p.coeff n * mom n := by
  conv_lhs => rw [Polynomial.as_sum_range' p (N + 1) hN]
  rw [gmean_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, gmean_smul, mom]

/-! ## 3. Bivariate polynomials and the iterated expectation

    A bivariate polynomial is `q : ℝ[X][Y]`; the value at (x, y) is obtained
    by evaluating the coefficients at x and then the outer variable at y. -/

/-- The value of a bivariate polynomial at (x, y). -/
def bval (q : Polynomial (Polynomial ℝ)) (x y : ℝ) : ℝ :=
  (q.map (Polynomial.evalRingHom x)).eval y

/-- **The inner (y) expectation**, as a polynomial in x. -/
def Ey (q : Polynomial (Polynomial ℝ)) : ℝ[X] :=
  ∑ n ∈ Finset.range (q.natDegree + 1), mom n • q.coeff n

/-- The inner expectation is computed by the 1-d functional, pointwise in x:
    (Ey q)(x) = E_y[q(x, ·)]. -/
theorem eval_Ey (q : Polynomial (Polynomial ℝ)) (x : ℝ) :
    (Ey q).eval x = gmean (q.map (Polynomial.evalRingHom x)) := by
  have hdeg : (q.map (Polynomial.evalRingHom x)).natDegree < q.natDegree + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_map_le)
  rw [gmean_eq_sum_range hdeg, Ey, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Polynomial.coeff_map, smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
  simp [mul_comm]

/-- The coefficientwise derivative: differentiation in the x variable. -/
def dX (q : Polynomial (Polynomial ℝ)) : Polynomial (Polynomial ℝ) :=
  ∑ n ∈ Finset.range (q.natDegree + 1),
    Polynomial.monomial n (Polynomial.derivative (q.coeff n))

theorem coeff_dX (q : Polynomial (Polynomial ℝ)) (k : ℕ) :
    (dX q).coeff k = Polynomial.derivative (q.coeff k) := by
  rw [dX, Polynomial.finset_sum_coeff]
  by_cases hk : k ∈ Finset.range (q.natDegree + 1)
  · rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _ hbk
      rw [Polynomial.coeff_monomial, if_neg hbk]
    · intro h
      exact absurd hk h
  · have hzero : q.coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simp only [Finset.mem_range, not_lt] at hk
      omega
    rw [hzero, Polynomial.derivative_zero]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Polynomial.coeff_monomial, if_neg]
    intro h
    subst h
    exact hk hb

theorem natDegree_dX_le (q : Polynomial (Polynomial ℝ)) :
    (dX q).natDegree ≤ q.natDegree := by
  rw [dX]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  refine le_trans (Polynomial.natDegree_monomial_le _) ?_
  simp only [Finset.mem_range] at hn
  omega

/-- **Differentiating under the inner expectation** — purely algebraic here,
    because the inner expectation is a moment-weighted sum of coefficients. -/
theorem Ey_dX (q : Polynomial (Polynomial ℝ)) :
    Ey (dX q) = Polynomial.derivative (Ey q) := by
  have hEy : ∀ (r : Polynomial (Polynomial ℝ)) (N : ℕ), r.natDegree ≤ N →
      Ey r = ∑ n ∈ Finset.range (N + 1), mom n • r.coeff n := by
    intro r N hN
    rw [Ey]
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range] at hn ⊢
      omega
    · intro n _ hn
      simp only [Finset.mem_range, not_lt] at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]
  rw [hEy (dX q) q.natDegree (natDegree_dX_le q), Ey, Polynomial.derivative_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [coeff_dX, Polynomial.derivative_smul]

/-- The full two-dimensional Gaussian expectation, as an iterated one. -/
def E2 (q : Polynomial (Polynomial ℝ)) : ℝ := gmean (Ey q)

/-- Ey turns products into products pointwise, so `E2` of a square is the
    iterated expectation of the square. -/
theorem eval_Ey_mul (q r : Polynomial (Polynomial ℝ)) (x : ℝ) :
    (Ey (q * r)).eval x
      = gmean ((q.map (Polynomial.evalRingHom x))
          * (r.map (Polynomial.evalRingHom x))) := by
  rw [eval_Ey, Polynomial.map_mul]

/-! ## 4. The two-dimensional Poincaré inequality -/

/-- **TENSORISATION, THE INDUCTION STEP**: for a bivariate polynomial q,

      Var(q) ≤ E[(∂_y q)²] + E[(∂_x q)²]

    with all expectations the iterated Gaussian expectation E_x[E_y[·]].
    This is the standard tensorisation argument made explicit: the inner
    variance is controlled by the 1-d inequality pointwise in x and then
    integrated (which needs `gmean_mono`), the outer variance is controlled by
    the 1-d inequality applied to the inner expectation, and the two are
    joined by Cauchy–Schwarz in the form `gvar_nonneg`. -/
theorem poincare_two (q : Polynomial (Polynomial ℝ)) :
    E2 (q * q) - (E2 q) ^ 2
      ≤ E2 (Polynomial.derivative q * Polynomial.derivative q)
        + E2 (dX q * dX q) := by
  -- Step 1: the inner inequality, pointwise in x, integrated over x.
  have hinner : gmean (Ey (q * q)) - gmean (Ey q * Ey q)
      ≤ gmean (Ey (Polynomial.derivative q * Polynomial.derivative q)) := by
    have hpt : ∀ x : ℝ,
        (Ey (q * q) - Ey q * Ey q).eval x
          ≤ (Ey (Polynomial.derivative q * Polynomial.derivative q)).eval x := by
      intro x
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, eval_Ey]
      rw [Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map]
      have h1d := poincare_polynomial (q.map (Polynomial.evalRingHom x))
      unfold gvar at h1d
      rw [pow_two] at h1d
      linarith
    have := gmean_mono hpt
    rw [gmean_sub] at this
    exact this
  -- Step 2: the outer inequality, applied to the inner expectation.
  have houter : gmean (Ey q * Ey q) - (gmean (Ey q)) ^ 2
      ≤ gmean (Polynomial.derivative (Ey q) * Polynomial.derivative (Ey q)) := by
    have h := poincare_polynomial (Ey q)
    unfold gvar at h
    exact h
  -- Step 3: differentiate under the inner expectation.
  rw [← Ey_dX] at houter
  -- Step 4: Cauchy–Schwarz, pointwise in x, integrated over x.
  have hcs : gmean (Ey (dX q) * Ey (dX q)) ≤ gmean (Ey (dX q * dX q)) := by
    apply gmean_mono
    intro x
    rw [Polynomial.eval_mul, eval_Ey, eval_Ey_mul]
    have hv := gvar_nonneg ((dX q).map (Polynomial.evalRingHom x))
    unfold gvar at hv
    rw [pow_two] at hv
    linarith
  unfold E2
  linarith

/-- **The inequality in the vocabulary of iterated integrals**: for every
    bivariate polynomial q,

      ∫∫ q² − (∫∫ q)² ≤ ∫∫ (∂_y q)² + ∫∫ (∂_x q)²,

    where every integral is against Mathlib's `gaussianReal 0 1` in each
    variable, taken iteratedly. -/
theorem poincare_two_integral (q : Polynomial (Polynomial ℝ)) :
    (∫ x : ℝ, (∫ y : ℝ, bval (q * q) x y
        ∂(ProbabilityTheory.gaussianReal 0 1)) ∂(ProbabilityTheory.gaussianReal 0 1))
      - (∫ x : ℝ, (∫ y : ℝ, bval q x y
          ∂(ProbabilityTheory.gaussianReal 0 1)) ∂(ProbabilityTheory.gaussianReal 0 1)) ^ 2
      ≤ (∫ x : ℝ, (∫ y : ℝ, bval (Polynomial.derivative q * Polynomial.derivative q) x y
          ∂(ProbabilityTheory.gaussianReal 0 1)) ∂(ProbabilityTheory.gaussianReal 0 1))
        + (∫ x : ℝ, (∫ y : ℝ, bval (dX q * dX q) x y
            ∂(ProbabilityTheory.gaussianReal 0 1)) ∂(ProbabilityTheory.gaussianReal 0 1)) := by
  have key : ∀ r : Polynomial (Polynomial ℝ),
      (∫ x : ℝ, (∫ y : ℝ, bval r x y
        ∂(ProbabilityTheory.gaussianReal 0 1)) ∂(ProbabilityTheory.gaussianReal 0 1))
        = E2 r := by
    intro r
    have hinner : ∀ x : ℝ, (∫ y : ℝ, bval r x y
        ∂(ProbabilityTheory.gaussianReal 0 1)) = (Ey r).eval x := by
      intro x
      rw [eval_Ey, gmean_eq_integral]
      rfl
    simp_rw [hinner]
    rw [E2, gmean_eq_integral]
  rw [key, key, key, key]
  exact poincare_two q

end GaussianPoincareProduct
