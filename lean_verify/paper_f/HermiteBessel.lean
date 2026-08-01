/-
  HermiteBessel: Coefficients, Partial Sums, and the Bessel Inequality
  ====================================================================

  The rung directly above `HermiteCompleteness`. That file proved the Hermite
  system complete in L²(γ); the Poincaré inequality for non-polynomial test
  functions needs the L²-Fourier apparatus ON TOP of completeness. This file
  builds its finite-dimensional half — everything that needs no limit:

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `coeff n f = (∫ f·Hₙ dγ)/n!` — the n-th Hermite coefficient — and
     `SN N f`, the N-th partial sum, as an honest polynomial.
  2. `integral_mul_SN`, `integral_SN_sq` — the two orthogonality
     computations: ⟨f, S_N f⟩ = Σ_{n<N} n!·cₙ² and ‖S_N f‖² = Σ_{n<N} n!·cₙ².
  3. **`remainder_expansion`** — ‖f − S_N f‖² = ‖f‖² − Σ_{n<N} n!·cₙ², an
     EQUALITY: the partial sum is the orthogonal projection, exactly.
  4. **`bessel`** — Σ_{n<N} n!·cₙ² ≤ ‖f‖² for every N, and
     `summable_coeff_sq` — the coefficient series Σ n!·cₙ² converges.
  5. `remainder_orthogonal` — f − S_N f ⊥ Hₘ for every m < N.
  6. `sn_cauchy` — the partial sums are L²-CAUCHY:
     ‖S_M f − S_N f‖² = Σ_{N≤n<M} n!·cₙ², which tends to 0. The limit
     object is the next rung, not this one.

  NOT proven here — the remaining legs to Poincaré-beyond-polynomials,
  in order:

  * **Riesz–Fischer / Parseval**: that S_N f converges to f in L²(γ). The
    Cauchy property is item 6 and completeness of the system is the previous
    file; what is missing is completeness of the SPACE — the limit exists in
    L² (Mathlib has `Lp` complete; connecting it to these unbundled
    statements is the plumbing), equals f by `hermite_complete` applied to
    the difference. Then ‖f‖² = Σ n!·cₙ².
  * The derivative recursion cₙ(f′) ↔ cₙ₊₁(f) on a Sobolev class, and the
    termwise limit that yields Poincaré for W^{1,2}(γ).
  * Everything the previous files disclaim (no spectral action, etc.).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import HermiteCompleteness

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace HermiteBessel

open GaussianPoincare HermiteCompleteness

/-! ## 1. Coefficients and partial sums -/

/-- The n-th Hermite coefficient of f. -/
def coeff (n : ℕ) (f : ℝ → ℝ) : ℝ :=
  (∫ x, f x * (H n).eval x ∂gauss) / (n.factorial : ℝ)

/-- The N-th Hermite partial sum, as a polynomial. -/
def SNpoly (N : ℕ) (f : ℝ → ℝ) : ℝ[X] :=
  ∑ n ∈ Finset.range N, coeff n f • H n

theorem eval_SNpoly (N : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (SNpoly N f).eval x = ∑ n ∈ Finset.range N, coeff n f * (H n).eval x := by
  rw [SNpoly, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_eq_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

/-- ∫ f·Hₙ dγ = n!·cₙ — the coefficient definition, solved for the
    integral. -/
theorem integral_mul_H (f : ℝ → ℝ) (n : ℕ) :
    ∫ x, f x * (H n).eval x ∂gauss = (n.factorial : ℝ) * coeff n f := by
  rw [coeff]
  field_simp

/-! ## 2. The two orthogonality computations -/

theorem integrable_f_mul_poly (f : ℝ → ℝ) (hf : MemLp f 2 gauss) (p : ℝ[X]) :
    Integrable (fun x => f x * p.eval x) gauss :=
  MemLp.integrable_mul hf (GaussianPoincare.memLp_polynomial_gaussianReal p 0 1)

theorem integrable_poly_mul_poly (p q : ℝ[X]) :
    Integrable (fun x => p.eval x * q.eval x) gauss :=
  MemLp.integrable_mul (GaussianPoincare.memLp_polynomial_gaussianReal p 0 1)
    (GaussianPoincare.memLp_polynomial_gaussianReal q 0 1)

/-- **⟨f, S_N f⟩ = Σ n!·cₙ²**. -/
theorem integral_mul_SN (f : ℝ → ℝ) (hf : MemLp f 2 gauss) (N : ℕ) :
    ∫ x, f x * (SNpoly N f).eval x ∂gauss
      = ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2 := by
  have hpt : (fun x => f x * (SNpoly N f).eval x)
      = fun x => ∑ n ∈ Finset.range N, coeff n f * (f x * (H n).eval x) := by
    funext x
    rw [eval_SNpoly, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hint : ∀ n : ℕ, Integrable (fun x => coeff n f * (f x * (H n).eval x)) gauss :=
    fun n => (integrable_f_mul_poly f hf (H n)).const_mul _
  rw [hpt, integral_finset_sum _ (fun n _ => hint n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul, integral_mul_H]
  ring

/-- **‖S_N f‖² = Σ n!·cₙ²**: the partial sum's own norm, by double
    orthogonality. -/
theorem integral_SN_sq (f : ℝ → ℝ) (N : ℕ) :
    ∫ x, (SNpoly N f).eval x * (SNpoly N f).eval x ∂gauss
      = ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2 := by
  have hpt : (fun x => (SNpoly N f).eval x * (SNpoly N f).eval x)
      = fun x => ∑ n ∈ Finset.range N,
          coeff n f * ((H n).eval x * (SNpoly N f).eval x) := by
    funext x
    rw [eval_SNpoly, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hint : ∀ n : ℕ,
      Integrable (fun x => coeff n f * ((H n).eval x * (SNpoly N f).eval x)) gauss :=
    fun n => (integrable_poly_mul_poly (H n) (SNpoly N f)).const_mul _
  rw [hpt, integral_finset_sum _ (fun n _ => hint n)]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [integral_const_mul]
  -- inner sum:: ∫ Hₙ·S_N = cₙ·n!, orthogonality killing every other term
  have hinner : ∫ x, (H n).eval x * (SNpoly N f).eval x ∂gauss
      = coeff n f * (n.factorial : ℝ) := by
    have hpt2 : (fun x => (H n).eval x * (SNpoly N f).eval x)
        = fun x => ∑ m ∈ Finset.range N,
            coeff m f * ((H n).eval x * (H m).eval x) := by
      funext x
      rw [eval_SNpoly, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hint2 : ∀ m : ℕ,
        Integrable (fun x => coeff m f * ((H n).eval x * (H m).eval x)) gauss :=
      fun m => (integrable_poly_mul_poly (H n) (H m)).const_mul _
    rw [hpt2, integral_finset_sum _ (fun m _ => hint2 m)]
    rw [Finset.sum_eq_single n]
    · rw [integral_const_mul, hermite_orthogonal_gauss, if_pos rfl]
    · intro m _ hmn
      rw [integral_const_mul, hermite_orthogonal_gauss,
        if_neg (fun h => hmn h.symm), mul_zero]
    · intro hn'
      exact absurd hn hn'
  rw [hinner]
  ring

/-! ## 3. The remainder expansion, Bessel, and summability -/

theorem integrable_sq (f : ℝ → ℝ) (hf : MemLp f 2 gauss) :
    Integrable (fun x => f x ^ 2) gauss :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf

/-- **The remainder expansion, an EQUALITY**:
    ‖f − S_N f‖² = ‖f‖² − Σ_{n<N} n!·cₙ². The partial sum is exactly the
    orthogonal projection onto the first N Hermite modes. -/
theorem remainder_expansion (f : ℝ → ℝ) (hf : MemLp f 2 gauss) (N : ℕ) :
    ∫ x, (f x - (SNpoly N f).eval x) ^ 2 ∂gauss
      = (∫ x, f x ^ 2 ∂gauss)
        - ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2 := by
  have hfS := integrable_f_mul_poly f hf (SNpoly N f)
  have hSS := integrable_poly_mul_poly (SNpoly N f) (SNpoly N f)
  have hff := integrable_sq f hf
  have hpt : (fun x => (f x - (SNpoly N f).eval x) ^ 2)
      = fun x => f x ^ 2
          - 2 * (f x * (SNpoly N f).eval x)
          + (SNpoly N f).eval x * (SNpoly N f).eval x := by
    funext x
    ring
  have hB : Integrable (fun x => 2 * (f x * (SNpoly N f).eval x)) gauss :=
    hfS.const_mul 2
  have hA : Integrable
      (fun x => f x ^ 2 - 2 * (f x * (SNpoly N f).eval x)) gauss :=
    hff.sub hB
  rw [hpt, integral_add hA hSS, integral_sub hff hB, integral_const_mul,
    integral_mul_SN f hf N, integral_SN_sq f N]
  ring

/-- **The Bessel inequality.** -/
theorem bessel (f : ℝ → ℝ) (hf : MemLp f 2 gauss) (N : ℕ) :
    ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2
      ≤ ∫ x, f x ^ 2 ∂gauss := by
  have h := remainder_expansion f hf N
  have hpos : 0 ≤ ∫ x, (f x - (SNpoly N f).eval x) ^ 2 ∂gauss :=
    integral_nonneg fun x => sq_nonneg _
  linarith [h, hpos]

/-- **The coefficient series converges** — Bessel plus nonnegativity. -/
theorem summable_coeff_sq (f : ℝ → ℝ) (hf : MemLp f 2 gauss) :
    Summable (fun n => (n.factorial : ℝ) * coeff n f ^ 2) :=
  summable_of_sum_range_le
    (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (fun N => bessel f hf N)

/-! ## 4. Remainder orthogonality and the Cauchy property -/

/-- The remainder is orthogonal to every mode it has already used. -/
theorem remainder_orthogonal (f : ℝ → ℝ) (hf : MemLp f 2 gauss) (N m : ℕ)
    (hm : m < N) :
    ∫ x, (f x - (SNpoly N f).eval x) * (H m).eval x ∂gauss = 0 := by
  have h1 := integrable_f_mul_poly f hf (H m)
  have h2 := integrable_poly_mul_poly (SNpoly N f) (H m)
  have hpt : (fun x => (f x - (SNpoly N f).eval x) * (H m).eval x)
      = fun x => f x * (H m).eval x
          - (SNpoly N f).eval x * (H m).eval x := by
    funext x
    ring
  rw [hpt, integral_sub h1 h2, integral_mul_H]
  -- ∫ S_N·Hₘ = cₘ·m! by the same single-survivor computation
  have hS : ∫ x, (SNpoly N f).eval x * (H m).eval x ∂gauss
      = coeff m f * (m.factorial : ℝ) := by
    have hpt2 : (fun x => (SNpoly N f).eval x * (H m).eval x)
        = fun x => ∑ n ∈ Finset.range N,
            coeff n f * ((H n).eval x * (H m).eval x) := by
      funext x
      rw [eval_SNpoly, Finset.sum_mul]
      exact Finset.sum_congr rfl fun n _ => by ring
    have hint2 : ∀ n : ℕ,
        Integrable (fun x => coeff n f * ((H n).eval x * (H m).eval x)) gauss :=
      fun n => (integrable_poly_mul_poly (H n) (H m)).const_mul _
    rw [hpt2, integral_finset_sum _ (fun n _ => hint2 n)]
    rw [Finset.sum_eq_single m]
    · rw [integral_const_mul, hermite_orthogonal_gauss, if_pos rfl]
    · intro n _ hnm
      rw [integral_const_mul, hermite_orthogonal_gauss, if_neg hnm, mul_zero]
    · intro hm'
      exact absurd (Finset.mem_range.mpr hm) hm'
  rw [hS]
  ring

/-- The difference of two partial sums, evaluated: only the new modes. -/
theorem eval_SN_sub (f : ℝ → ℝ) {N M : ℕ} (hNM : N ≤ M) (x : ℝ) :
    (SNpoly M f).eval x - (SNpoly N f).eval x
      = ∑ n ∈ Finset.Ico N M, coeff n f * (H n).eval x := by
  rw [eval_SNpoly, eval_SNpoly, ← Finset.sum_range_add_sum_Ico _ hNM]
  ring

/-- **The partial sums are L²-Cauchy**: the distance between two of them is
    exactly the tail of a convergent series. The limit object — Riesz–Fischer
    — is the next rung, recorded in the header. -/
theorem sn_cauchy (f : ℝ → ℝ) {N M : ℕ} (hNM : N ≤ M) :
    ∫ x, ((SNpoly M f).eval x - (SNpoly N f).eval x) ^ 2 ∂gauss
      = (∑ n ∈ Finset.range M, (n.factorial : ℝ) * coeff n f ^ 2)
        - ∑ n ∈ Finset.range N, (n.factorial : ℝ) * coeff n f ^ 2 := by
  -- (S_M − S_N)² = (f − S_N)² − (f − S_M)² + 2(f − S_M)(S_M − S_N)... the
  -- clean route: expand ∫(S_M − S_N)² directly by double orthogonality on
  -- the Ico block.
  have hpt : (fun x => ((SNpoly M f).eval x - (SNpoly N f).eval x) ^ 2)
      = fun x => (∑ n ∈ Finset.Ico N M, coeff n f * (H n).eval x)
          * ∑ n ∈ Finset.Ico N M, coeff n f * (H n).eval x := by
    funext x
    rw [← eval_SN_sub f hNM]
    ring
  have hterm : ∀ n : ℕ, Integrable
      (fun x => coeff n f * ((H n).eval x
        * ∑ m ∈ Finset.Ico N M, coeff m f * (H m).eval x)) gauss := by
    intro n
    have h3 : Integrable (fun x => (H n).eval x * (SNpoly M f).eval x
        - (H n).eval x * (SNpoly N f).eval x) gauss :=
      (integrable_poly_mul_poly (H n) (SNpoly M f)).sub
        (integrable_poly_mul_poly (H n) (SNpoly N f))
    have h4 : Integrable (fun x => coeff n f
        * ((H n).eval x * ((SNpoly M f).eval x - (SNpoly N f).eval x))) gauss :=
      ((h3.congr (by filter_upwards with x; ring)).const_mul _)
    refine h4.congr ?_
    filter_upwards with x
    rw [eval_SN_sub f hNM x]
  have hexp : (fun x => (∑ n ∈ Finset.Ico N M, coeff n f * (H n).eval x)
      * ∑ m ∈ Finset.Ico N M, coeff m f * (H m).eval x)
      = fun x => ∑ n ∈ Finset.Ico N M, coeff n f * ((H n).eval x
          * ∑ m ∈ Finset.Ico N M, coeff m f * (H m).eval x) := by
    funext x
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hpt, hexp, integral_finset_sum _ (fun n _ => hterm n)]
  have hsingle : ∀ n ∈ Finset.Ico N M,
      (∫ x, coeff n f * ((H n).eval x
        * ∑ m ∈ Finset.Ico N M, coeff m f * (H m).eval x) ∂gauss)
      = (n.factorial : ℝ) * coeff n f ^ 2 := by
    intro n hn
    rw [integral_const_mul]
    have hin : (fun x => (H n).eval x
        * ∑ m ∈ Finset.Ico N M, coeff m f * (H m).eval x)
        = fun x => ∑ m ∈ Finset.Ico N M,
            coeff m f * ((H n).eval x * (H m).eval x) := by
      funext x
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hin, integral_finset_sum _ (fun m _ =>
      (integrable_poly_mul_poly (H n) (H m)).const_mul _)]
    rw [Finset.sum_eq_single n]
    · rw [integral_const_mul, hermite_orthogonal_gauss, if_pos rfl]
      ring
    · intro m _ hmn
      rw [integral_const_mul, hermite_orthogonal_gauss,
        if_neg (fun h => hmn h.symm), mul_zero]
    · intro hn'
      exact absurd hn hn'
  rw [Finset.sum_congr rfl hsingle, ← Finset.sum_range_add_sum_Ico
    (fun n => (n.factorial : ℝ) * coeff n f ^ 2) hNM]
  ring

end HermiteBessel
