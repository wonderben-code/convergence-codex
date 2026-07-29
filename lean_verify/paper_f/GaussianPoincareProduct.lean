/-
  GaussianPoincareProduct: Tensorising the Gaussian Poincaré Inequality
  ====================================================================

  Campaign-3 unit 1. `GaussianPoincare.lean` proved Var_γ(p) ≤ E_γ[(p′)²] in
  ONE dimension for polynomial test functions, and listed tensorisation as
  the next stair — it is the stair the cascade actually needs, since the
  space there is Herm₄(ℂ) ≅ ℝ¹⁶.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  **The n-dimensional Gaussian Poincaré inequality for polynomial test
  functions**, `poincare_MV`: for every `p : MvPolynomial (Fin n) ℝ`,

      E[p²] − (E[p])² ≤ Σᵢ E[(∂ᵢp)²]

  with E the n-fold iterated standard Gaussian expectation — and
  `poincare_R16`, the case n = 16, which is ℝ¹⁶ ≅ Herm₄(ℂ), the dimension
  the cascade needs. The route: §4 does the tensorisation step in two
  variables concretely, §5–§8 rebuild it over `MvPolynomial (Fin n) ℝ` and
  run the induction, peeling one variable at a time with
  `MvPolynomial.finSuccEquiv`.

  Two bridges the induction needs do not exist in Mathlib and are proven
  here: `finSuccEquiv_pderiv_zero` (the partial derivative in the peeled
  variable is the polynomial derivative) and `finSuccEquiv_pderiv_succ` (the
  other partials act coefficientwise). A route that does NOT work, recorded
  so it is not retried: a recursively defined tower of nested polynomial
  types — the type-level recursion cannot carry the `CommRing` instance.

  **The tensorisation step in two variables**, `poincare_two`: for a
  bivariate polynomial q,

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
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Funext

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

/-! ## 5. Toward n dimensions: the first bridge

    Iterating §4 to ℝ¹⁶ cannot be done with a recursively defined tower of
    nested polynomial types — the type-level recursion cannot carry the
    `CommRing` instance it needs (tried, and it fails at the definition).
    The workable route is Mathlib's `MvPolynomial (Fin n) ℝ` with
    `MvPolynomial.finSuccEquiv`, peeling one variable at a time. That route
    needs bridges between `MvPolynomial.pderiv` and the polynomial structure
    on the peeled variable, and Mathlib has none of them.

    Here is the first, and the one that looked hardest: the equivalence
    carries the partial derivative in the peeled variable to the ordinary
    polynomial derivative. -/

/-- The equivalence sends constants to constants. -/
theorem finSuccEquiv_C_apply {n : ℕ} (a : ℝ) :
    MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := by
  simp [MvPolynomial.finSuccEquiv_apply]

/-- **The pderiv bridge**: under `finSuccEquiv`, the partial derivative in the
    peeled variable IS the polynomial derivative,

      finSuccEquiv (∂₀ p) = derivative (finSuccEquiv p).

    Mathlib has no lemma relating `pderiv` to `finSuccEquiv`; this is the
    first of the two such bridges the n-dimensional induction needs (the
    second, for the remaining variables, is stated as open in §6). -/
theorem finSuccEquiv_pderiv_zero {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv 0 p)
      = Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ n p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_C_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      refine Fin.cases ?_ ?_ i
      · simp [Derivation.leibniz, hp, MvPolynomial.finSuccEquiv_X_zero]
        ring
      · intro j
        simp [Derivation.leibniz, hp, MvPolynomial.finSuccEquiv_X_succ]
        ring

/-- **The second pderiv bridge**, in the coefficient form the induction
    needs: differentiating in one of the REMAINING variables acts
    coefficientwise after peeling. -/
theorem finSuccEquiv_pderiv_succ {n : ℕ} (j : Fin n)
    (p : MvPolynomial (Fin (n + 1)) ℝ) (k : ℕ) :
    ((MvPolynomial.finSuccEquiv ℝ n) (MvPolynomial.pderiv j.succ p)).coeff k
      = MvPolynomial.pderiv j (((MvPolynomial.finSuccEquiv ℝ n) p).coeff k) := by
  induction p using MvPolynomial.induction_on generalizing k with
  | C a =>
      simp [finSuccEquiv_C_apply, Polynomial.coeff_C,
        apply_ite (MvPolynomial.pderiv j)]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      refine Fin.cases ?_ ?_ i
      · have hz : MvPolynomial.pderiv j.succ
            (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) ℝ) = 0 :=
          MvPolynomial.pderiv_X_of_ne (Fin.succ_ne_zero j).symm
        cases k with
        | zero => simp [Derivation.leibniz, hz, MvPolynomial.finSuccEquiv_X_zero]
        | succ m =>
            simp [Derivation.leibniz, hz, MvPolynomial.finSuccEquiv_X_zero, hp]
      · intro j'
        by_cases hjj : j' = j
        · subst hjj
          simp [Derivation.leibniz, MvPolynomial.finSuccEquiv_X_succ,
            Polynomial.coeff_mul_C, hp]
        · have h1 : MvPolynomial.pderiv j.succ
              (MvPolynomial.X j'.succ : MvPolynomial (Fin (n + 1)) ℝ) = 0 :=
            MvPolynomial.pderiv_X_of_ne (fun h => hjj (Fin.succ_injective n h))
          have h2 : MvPolynomial.pderiv j
              (MvPolynomial.X j' : MvPolynomial (Fin n) ℝ) = 0 :=
            MvPolynomial.pderiv_X_of_ne hjj
          simp [Derivation.leibniz, MvPolynomial.finSuccEquiv_X_succ,
            Polynomial.coeff_mul_C, hp, h1, h2]

/-! ## 6. The n-variable tower: expectation and positivity -/

/-- The inner expectation on the peeled variable, valued in the remaining
    variables. -/
def EyM (n : ℕ) (q : Polynomial (MvPolynomial (Fin n) ℝ)) : MvPolynomial (Fin n) ℝ :=
  ∑ k ∈ Finset.range (q.natDegree + 1), mom k • q.coeff k

/-- **The n-fold iterated Gaussian expectation.** -/
def EN : (n : ℕ) → MvPolynomial (Fin n) ℝ → ℝ
  | 0, p => MvPolynomial.eval (fun i => Fin.elim0 i) p
  | (n + 1), p => EN n (EyM n (MvPolynomial.finSuccEquiv ℝ n p))

theorem EN_zero (p : MvPolynomial (Fin 0) ℝ) :
    EN 0 p = MvPolynomial.eval (fun i => Fin.elim0 i) p := rfl

theorem EN_succ (n : ℕ) (p : MvPolynomial (Fin (n + 1)) ℝ) :
    EN (n + 1) p = EN n (EyM n (MvPolynomial.finSuccEquiv ℝ n p)) := rfl

/-- The inner expectation, computed pointwise in the remaining variables by
    the 1-d functional — the n-variable analogue of `eval_Ey`. -/
theorem eval_EyM (n : ℕ) (q : Polynomial (MvPolynomial (Fin n) ℝ))
    (w : Fin n → ℝ) :
    MvPolynomial.eval w (EyM n q) = gmean (q.map (MvPolynomial.eval w)) := by
  have hdeg : (q.map (MvPolynomial.eval w)).natDegree < q.natDegree + 1 :=
    Nat.lt_succ_of_le Polynomial.natDegree_map_le
  rw [gmean_eq_sum_range hdeg, EyM, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_map, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.eval_C]
  ring

/-- **Positivity of the n-fold expectation**: a polynomial nonnegative at
    every point of ℝⁿ has nonnegative expectation. Proven by induction, with
    Mathlib's `eval_eq_eval_mv_eval'` as the bridge between the peeled
    variable and the rest. -/
theorem EN_nonneg : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
    (∀ v : Fin n → ℝ, 0 ≤ MvPolynomial.eval v p) → 0 ≤ EN n p
  | 0, p, hp => hp _
  | (n + 1), p, hp => by
      rw [EN_succ]
      refine EN_nonneg n _ fun w => ?_
      rw [eval_EyM]
      apply gmean_nonneg
      intro x
      have h := hp (Fin.cons x w)
      rwa [MvPolynomial.eval_eq_eval_mv_eval'] at h

/-- Monotonicity of the n-fold expectation, by the same induction. -/
theorem EN_mono : ∀ (n : ℕ) {p q : MvPolynomial (Fin n) ℝ},
    (∀ v : Fin n → ℝ, MvPolynomial.eval v p ≤ MvPolynomial.eval v q) →
      EN n p ≤ EN n q
  | 0, _, _, h => h _
  | (n + 1), p, q, h => by
      rw [EN_succ, EN_succ]
      refine EN_mono n fun w => ?_
      rw [eval_EyM, eval_EyM]
      apply gmean_mono
      intro x
      have hx := h (Fin.cons x w)
      rwa [MvPolynomial.eval_eq_eval_mv_eval',
        MvPolynomial.eval_eq_eval_mv_eval'] at hx

/-! ## 7. Linearity of the n-fold expectation -/

theorem EyM_add (n : ℕ) (a b : Polynomial (MvPolynomial (Fin n) ℝ)) :
    EyM n (a + b) = EyM n a + EyM n b := by
  apply MvPolynomial.funext
  intro v
  rw [map_add, eval_EyM, eval_EyM, eval_EyM, Polynomial.map_add, gmean_add]

theorem EyM_sub (n : ℕ) (a b : Polynomial (MvPolynomial (Fin n) ℝ)) :
    EyM n (a - b) = EyM n a - EyM n b := by
  apply MvPolynomial.funext
  intro v
  rw [map_sub, eval_EyM, eval_EyM, eval_EyM, Polynomial.map_sub, gmean_sub]

theorem EyM_eq_sum_range (n N : ℕ) (q : Polynomial (MvPolynomial (Fin n) ℝ))
    (hq : q.natDegree ≤ N) :
    EyM n q = ∑ k ∈ Finset.range (N + 1), mom k • q.coeff k := by
  rw [EyM]
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]

theorem EyM_smul (n : ℕ) (c : ℝ) (a : Polynomial (MvPolynomial (Fin n) ℝ)) :
    EyM n (c • a) = c • EyM n a := by
  rw [EyM_eq_sum_range n a.natDegree (c • a) (Polynomial.natDegree_smul_le c a),
    EyM, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.coeff_smul, smul_comm]

theorem EyM_one (n : ℕ) : EyM n 1 = 1 := by
  apply MvPolynomial.funext
  intro v
  rw [eval_EyM, Polynomial.map_one, map_one, gmean_one]

theorem EN_add : ∀ (n : ℕ) (p q : MvPolynomial (Fin n) ℝ),
    EN n (p + q) = EN n p + EN n q
  | 0, p, q => by simp [EN_zero]
  | (n + 1), p, q => by
      rw [EN_succ, EN_succ, EN_succ, map_add, EyM_add, EN_add]

theorem EN_sub : ∀ (n : ℕ) (p q : MvPolynomial (Fin n) ℝ),
    EN n (p - q) = EN n p - EN n q
  | 0, p, q => by simp [EN_zero]
  | (n + 1), p, q => by
      rw [EN_succ, EN_succ, EN_succ, map_sub, EyM_sub, EN_sub]

theorem EN_smul : ∀ (n : ℕ) (c : ℝ) (p : MvPolynomial (Fin n) ℝ),
    EN n (c • p) = c * EN n p
  | 0, c, p => by simp [EN_zero]
  | (n + 1), c, p => by
      rw [EN_succ, EN_succ, map_smul, EyM_smul, EN_smul]

theorem EN_one : ∀ n : ℕ, EN n (1 : MvPolynomial (Fin n) ℝ) = 1
  | 0 => by simp [EN_zero]
  | (n + 1) => by rw [EN_succ, map_one, EyM_one, EN_one]

theorem EN_C (n : ℕ) (c : ℝ) : EN n (MvPolynomial.C c) = c := by
  have h : (MvPolynomial.C c : MvPolynomial (Fin n) ℝ) = c • 1 := by
    rw [MvPolynomial.smul_eq_C_mul, mul_one]
  rw [h, EN_smul, EN_one, mul_one]

/-- **Cauchy–Schwarz at level n**: (E p)² ≤ E[p²]. -/
theorem EN_sq_le (n : ℕ) (p : MvPolynomial (Fin n) ℝ) :
    (EN n p) ^ 2 ≤ EN n (p * p) := by
  have hring : (p - MvPolynomial.C (EN n p)) * (p - MvPolynomial.C (EN n p))
      = p * p - (EN n p) • p - (EN n p) • p
        + ((EN n p) * (EN n p)) • (1 : MvPolynomial (Fin n) ℝ) := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, mul_one]
    ring
  have hnn : 0 ≤ EN n ((p - MvPolynomial.C (EN n p)) * (p - MvPolynomial.C (EN n p))) := by
    refine EN_nonneg n _ fun v => ?_
    rw [map_mul]
    exact mul_self_nonneg _
  rw [hring, EN_add, EN_sub, EN_sub, EN_smul, EN_smul, EN_one] at hnn
  nlinarith [hnn]

/-! ## 8. The n-dimensional Poincaré inequality -/

/-- Differentiating in a remaining variable commutes with the inner
    expectation — the n-variable form of `Ey_dX`, via the second bridge. -/
theorem pderiv_EyM (n : ℕ) (j : Fin n) (p : MvPolynomial (Fin (n + 1)) ℝ) :
    MvPolynomial.pderiv j (EyM n (MvPolynomial.finSuccEquiv ℝ n p))
      = EyM n (MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv j.succ p)) := by
  have hdeg : (MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv j.succ p)).natDegree
      ≤ (MvPolynomial.finSuccEquiv ℝ n p).natDegree := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [finSuccEquiv_pderiv_succ,
      Polynomial.coeff_eq_zero_of_natDegree_lt hm, map_zero]
  rw [EyM_eq_sum_range n _ _ hdeg, EyM, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.pderiv_C_mul, finSuccEquiv_pderiv_succ]

/-- **THE n-DIMENSIONAL GAUSSIAN POINCARÉ INEQUALITY** for polynomial test
    functions: for every `p : MvPolynomial (Fin n) ℝ`,

      E[p²] − (E[p])² ≤ Σᵢ E[(∂ᵢp)²],

    with E the n-fold iterated standard Gaussian expectation. At n = 16 this
    is the statement on ℝ¹⁶ ≅ Herm₄(ℂ). -/
theorem poincare_MV : ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℝ),
    EN n (p * p) - (EN n p) ^ 2
      ≤ ∑ i : Fin n, EN n (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p)
  | 0, p => by
      rw [EN_zero, EN_zero]
      simp [map_mul, sq]
  | (n + 1), p => by
      rw [EN_succ, EN_succ, map_mul]
      -- inner: the 1-d inequality pointwise in the remaining variables
      have hinner : EN n (EyM n (MvPolynomial.finSuccEquiv ℝ n p
            * MvPolynomial.finSuccEquiv ℝ n p))
          - EN n (EyM n (MvPolynomial.finSuccEquiv ℝ n p)
            * EyM n (MvPolynomial.finSuccEquiv ℝ n p))
          ≤ EN n (EyM n (Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ n p)
            * Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ n p))) := by
        rw [← EN_sub]
        refine EN_mono n fun v => ?_
        rw [map_sub, map_mul, eval_EyM, eval_EyM, eval_EyM,
          Polynomial.map_mul, Polynomial.map_mul, ← Polynomial.derivative_map]
        have h1d := poincare_polynomial
          ((MvPolynomial.finSuccEquiv ℝ n p).map (MvPolynomial.eval v))
        unfold gvar at h1d
        rw [pow_two] at h1d
        linarith
      -- outer: the induction hypothesis at the inner expectation
      have houter := poincare_MV n (EyM n (MvPolynomial.finSuccEquiv ℝ n p))
      -- the ∂₀ term, via the first bridge
      have h0 : Polynomial.derivative (MvPolynomial.finSuccEquiv ℝ n p)
          = MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv 0 p) := by
        rw [finSuccEquiv_pderiv_zero]
      -- the remaining terms, via the second bridge and Cauchy–Schwarz
      have hcs : ∀ j : Fin n,
          EN n (MvPolynomial.pderiv j (EyM n (MvPolynomial.finSuccEquiv ℝ n p))
            * MvPolynomial.pderiv j (EyM n (MvPolynomial.finSuccEquiv ℝ n p)))
          ≤ EN n (EyM n (MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv j.succ p)
              * MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv j.succ p))) := by
        intro j
        rw [pderiv_EyM]
        refine EN_mono n fun v => ?_
        rw [map_mul, eval_EyM, eval_EyM, Polynomial.map_mul]
        have hv := gvar_nonneg
          ((MvPolynomial.finSuccEquiv ℝ n (MvPolynomial.pderiv j.succ p)).map
            (MvPolynomial.eval v))
        unfold gvar at hv
        rw [pow_two] at hv
        linarith
      rw [Fin.sum_univ_succ]
      have hsum : ∑ j : Fin n, EN n (MvPolynomial.pderiv j
            (EyM n (MvPolynomial.finSuccEquiv ℝ n p))
          * MvPolynomial.pderiv j (EyM n (MvPolynomial.finSuccEquiv ℝ n p)))
          ≤ ∑ j : Fin n, EN (n + 1) (MvPolynomial.pderiv j.succ p
            * MvPolynomial.pderiv j.succ p) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [EN_succ, map_mul]
        exact hcs j
      rw [h0] at hinner
      rw [EN_succ, map_mul]
      linarith

/-- **THE CASCADE CASE**: the Gaussian Poincaré inequality on ℝ¹⁶ ≅ Herm₄(ℂ),
    for polynomial test functions. This is the dimension the cascade needs. -/
theorem poincare_R16 (p : MvPolynomial (Fin 16) ℝ) :
    EN 16 (p * p) - (EN 16 p) ^ 2
      ≤ ∑ i : Fin 16, EN 16 (MvPolynomial.pderiv i p * MvPolynomial.pderiv i p) :=
  poincare_MV 16 p

/-! ## 9. What remains open

    Recorded precisely, so the remaining legs are a build and not a research
    problem. With `EN n : MvPolynomial (Fin n) ℝ → ℝ` defined by recursion —
    `EN 0` is evaluation at the unique point, `EN (n+1) p = EN n (EyM
    (finSuccEquiv ℝ n p))` with `EyM` the moment-weighted coefficient sum of
    §3 — the induction step is §4's argument verbatim. The legs:

    * **(open) the second pderiv bridge**, in coefficient form:
      `((finSuccEquiv ℝ n) (pderiv j.succ p)).coeff k
         = pderiv j (((finSuccEquiv ℝ n) p).coeff k)`.
      Provable by the same `MvPolynomial.induction_on`, with a case split on
      the peeled index and `Polynomial.coeff_mul_X` / `coeff_mul_C`;
      `MvPolynomial.finSuccEquiv_coeff_coeff` is the fallback route. Mathlib
      has no `coeff_pderiv` (checked).
    * **(open) positivity of `EN n`** — the analogue of `gmean_nonneg`, by
      induction, using `MvPolynomial.eval_eq_eval_mv_eval'` (which DOES exist
      in Mathlib and is the key ingredient).
    * **(open) the assembly**, which is §4 with `gmean` replaced by `EN n`.

    Until those land, nothing in this file says anything about 16 variables,
    and no tag may move on account of it. -/

end GaussianPoincareProduct
