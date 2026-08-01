/-
  OS2Exponential: Reflection Positivity for EXPONENTIAL Observables
  =================================================================

  The closing unit of the exponential-algebra OS2 item (UNLOCK_WATCHLIST).
  `OS2MeasureLevel` proved measure-level OS2 for LINEAR observables; the
  full OS axiom works with the exponentials e^{iφ(t)}, and this file
  delivers exactly that, at finitely many sites:

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `vfun` / `freqVec` / `inner_freqVec` — the frequency vector of a
     pairing term: t on the positive-time block, −s on the reflected
     block, with its inner product against a field configuration
     evaluated.
  2. `prodCov_symm`, `qform`, `bform`, **`Q_expand`** — the quadratic form
     of the difference vector expands as q(t) + q(s) − 2·b(t,s), using the
     θ-isometry of the kernel (`prodCov_doubled_inr_inr`) to fold the
     reflected block onto the positive one.
  3. **`charFun_freqVec`** — the characteristic function of the field at a
     frequency difference: E[e^{i(φ(t) − φθ(s))}] =
     e^{−q(t)/2 − q(s)/2 + b(t,s)}, a positive real, via Mathlib's
     `charFun_multivariateGaussian`.
  4. `integrable_charTerm` — pairing terms are integrable (norm 1 against
     a probability measure).
  5. **`os2_exponential`** — OS2 FOR EXPONENTIAL OBSERVABLES: for any
     complex coefficients c, frequency families t, positive-time sites z,
     and nonnegative rates,

       0 ≤ ∫ (Σᵢ cᵢ e^{iφ_ω(tᵢ)}) · conj(Σⱼ cⱼ e^{iφ_Θω(tⱼ)}) dμ

     in the complex order (the integral is real and nonnegative) — the
     pairing of an exponential observable of the positive-time fields
     against its time reflection. The kernel positivity is
     `OS2ExpKernel.gaussKernel_complex_nonneg` fed by
     `frequencyForm_posSemidef`; the Gaussian identity is
     `charFun_multivariateGaussian`.

  WHAT THIS IS AND IS NOT (the honesty box):

  * This closes the finite-site OS2 programme at its strongest form: the
    span of exponentials is dense in every reasonable observable algebra
    over a finite site family, and both the linear pairing
    (`OS2MeasureLevel.os2_measure_level`) and the exponential pairing
    (here) are now theorems. Still FINITE sites: no projective limit, no
    continuum field, no OS reconstruction.
  * OU-PRODUCT covariance, NOT the lattice-Laplacian Green function — the
    same boundary as the whole staircase, unchanged.
  * The time rate needs 0 ≤ Δ 0 (the field measure exists only then);
    positive times are needed exactly where they were at covariance level.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import OS2ExpKernel

open MeasureTheory ProbabilityTheory Matrix Real Finset OS2ProductField OS2MeasureLevel OS2ExpKernel
open scoped ComplexOrder RealInnerProductSpace ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace OS2Exponential

variable {m : ℕ} {N : ℕ}

/-- The frequency function on the doubled index: t on the positive block,
    −s on the reflected block. -/
def vfun (t s : Fin N → ℝ) : (Fin N ⊕ Fin N) → ℝ :=
  Sum.elim t (fun a => -(s a))

/-- The same, as a point of the Euclidean space. -/
def freqVec (t s : Fin N → ℝ) : EuclideanSpace ℝ (Fin N ⊕ Fin N) :=
  WithLp.toLp 2 (vfun t s)

theorem inner_freqVec (t s : Fin N → ℝ) (ω : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    ⟪ω, freqVec t s⟫
      = (∑ a, t a * ω (Sum.inl a)) - ∑ a, s a * ω (Sum.inr a) := by
  rw [PiLp.inner_apply]
  simp only [freqVec, vfun, RCLike.inner_apply, starRingEnd_apply, star_trivial,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, WithLp.ofLp_toLp]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  all_goals exact Finset.sum_congr rfl fun a _ => by ring

/-- The doubled covariance matrix is symmetric. -/
theorem prodCov_symm (Δ : Fin (m + 1) → ℝ) {ι : Type*}
    (s : ι → Fin (m + 1) → ℝ) (x y : ι) :
    OS2MeasureLevel.prodCov Δ s x y = OS2MeasureLevel.prodCov Δ s y x := by
  simp only [OS2MeasureLevel.prodCov, Matrix.of_apply]
  exact Finset.prod_congr rfl fun k _ => by rw [abs_sub_comm]

/-- The single-block quadratic form of a frequency family. -/
def qform (Δ : Fin (m + 1) → ℝ) (z : Fin N → Fin (m + 1) → ℝ)
    (t : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, t a * t b
    * OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inl a) (Sum.inl b)

/-- The cross form: the (i,j) covariance data of exponential observables. -/
def bform (Δ : Fin (m + 1) → ℝ) (z : Fin N → Fin (m + 1) → ℝ)
    (t s : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, t a * s b
    * OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inl a) (Sum.inr b)

/-- **The quadratic form of the difference vector expands**: with θ an
    isometry of the kernel (the RR block equals the LL block) and the
    covariance symmetric, v ⬝ S v = q(t) + q(s) − 2·b(t,s). -/
theorem Q_expand (Δ : Fin (m + 1) → ℝ) (z : Fin N → Fin (m + 1) → ℝ)
    (t s : Fin N → ℝ) :
    vfun t s ⬝ᵥ (OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z)) *ᵥ vfun t s
      = qform Δ z t + qform Δ z s - 2 * bform Δ z t s := by
  have hexp : vfun t s ⬝ᵥ (OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z)) *ᵥ vfun t s
      = ∑ x, ∑ y, vfun t s x
          * OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) x y
          * vfun t s y := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [hexp]
  simp only [Fintype.sum_sum_type, vfun, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hLL : ∑ a, ∑ b, t a
      * OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inl a) (Sum.inl b)
      * t b = qform Δ z t := by
    rw [qform]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hLR : ∑ a, ∑ b, t a
      * OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inl a) (Sum.inr b)
      * -(s b) = -bform Δ z t s := by
    rw [bform, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hRL : ∑ a, ∑ b, -(s a)
      * OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inr a) (Sum.inl b)
      * t b = -bform Δ z t s := by
    rw [bform, Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [prodCov_symm Δ _ (Sum.inr a) (Sum.inl b)]
    ring
  have hRR : ∑ a, ∑ b, -(s a)
      * OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inr a) (Sum.inr b)
      * -(s b) = qform Δ z s := by
    rw [qform]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [prodCov_doubled_inr_inr Δ z a b]
    ring
  rw [hLL, hLR, hRL, hRR]
  ring

/-! ## The per-term characteristic-function evaluation -/

/-- The characteristic function of the field at a frequency difference
    vector: e^{−q(t)/2 − q(s)/2 + b(t,s)}, a positive real. -/
theorem charFun_freqVec (Δ : Fin (m + 1) → ℝ) (hΔ : ∀ k, 0 ≤ Δ k)
    (z : Fin N → Fin (m + 1) → ℝ) (t s : Fin N → ℝ) :
    charFun (fieldMeasure Δ (OS2MeasureLevel.doubled z)) (freqVec t s)
      = Complex.ofReal (Real.exp
          (-(qform Δ z t) / 2 + -(qform Δ z s) / 2 + bform Δ z t s)) := by
  rw [fieldMeasure,
    charFun_multivariateGaussian (OS2MeasureLevel.prodCov_posSemidef Δ hΔ _)]
  rw [inner_zero_right]
  have hQ : (freqVec t s : EuclideanSpace ℝ (Fin N ⊕ Fin N)) ⬝ᵥ
      (OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z)) *ᵥ
        (freqVec t s : EuclideanSpace ℝ (Fin N ⊕ Fin N))
      = qform Δ z t + qform Δ z s - 2 * bform Δ z t s :=
    Q_expand Δ z t s
  rw [hQ]
  rw [show ((qform Δ z t + qform Δ z s - 2 * bform Δ z t s : ℝ) : ℂ) / 2
      = ((qform Δ z t / 2 + qform Δ z s / 2 - bform Δ z t s : ℝ) : ℂ) by
    push_cast
    ring]
  rw [Complex.ofReal_zero, zero_mul, zero_sub, ← Complex.ofReal_neg,
    ← Complex.ofReal_exp]
  congr 1
  ring

/-! ## Integrability of the pairing terms -/

theorem integrable_charTerm (Δ : Fin (m + 1) → ℝ)
    (z : Fin N → Fin (m + 1) → ℝ) (v : EuclideanSpace ℝ (Fin N ⊕ Fin N)) :
    Integrable (fun ω : EuclideanSpace ℝ (Fin N ⊕ Fin N) =>
      Complex.exp ((⟪ω, v⟫ : ℝ) * Complex.I))
      (fieldMeasure Δ (OS2MeasureLevel.doubled z)) := by
  have hmeas : AEStronglyMeasurable (fun ω : EuclideanSpace ℝ (Fin N ⊕ Fin N) =>
      Complex.exp ((⟪ω, v⟫ : ℝ) * Complex.I))
      (fieldMeasure Δ (OS2MeasureLevel.doubled z)) := by
    fun_prop
  refine (integrable_const (1 : ℝ)).mono' hmeas ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Complex.norm_exp_ofReal_mul_I]

/-! ## The theorem: exponential-observable reflection positivity -/

/-- **OS2 FOR EXPONENTIAL OBSERVABLES**: pairing a finite complex-linear
    combination of exponentials of the positive-time fields with the
    conjugate of its time reflection gives a NONNEGATIVE integral (in the
    complex order: real and ≥ 0) against the OU-product field measure. -/
theorem os2_exponential (Δ : Fin (m + 1) → ℝ) (hΔ : ∀ k, 0 ≤ Δ k)
    (z : Fin N → Fin (m + 1) → ℝ) (hpos : ∀ i, 0 ≤ z i 0)
    {M : ℕ} (t : Fin M → Fin N → ℝ) (c : Fin M → ℂ) :
    0 ≤ ∫ ω, (∑ i, c i * Complex.exp
          ((∑ a, t i a * ω (Sum.inl a) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ j, c j * Complex.exp
          ((∑ a, t j a * ω (Sum.inr a) : ℝ) * Complex.I))
        ∂(fieldMeasure Δ (OS2MeasureLevel.doubled z)) := by
  have hpt : ∀ ω : EuclideanSpace ℝ (Fin N ⊕ Fin N),
      (∑ i, c i * Complex.exp
          ((∑ a, t i a * ω (Sum.inl a) : ℝ) * Complex.I))
        * (starRingEnd ℂ) (∑ j, c j * Complex.exp
          ((∑ a, t j a * ω (Sum.inr a) : ℝ) * Complex.I))
      = ∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j))
          * Complex.exp ((⟪ω, freqVec (t i) (t j)⟫ : ℝ) * Complex.I) := by
    intro ω
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rw [show (starRingEnd ℂ) (Complex.exp
        ((∑ a, t j a * ω (Sum.inr a) : ℝ) * Complex.I))
        = Complex.exp (-((∑ a, t j a * ω (Sum.inr a) : ℝ) * Complex.I)) by
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring]
    rw [inner_freqVec]
    have hE : Complex.exp ((∑ a, t i a * ω (Sum.inl a) : ℝ) * Complex.I)
        * Complex.exp (-((∑ a, t j a * ω (Sum.inr a) : ℝ) * Complex.I))
        = Complex.exp
            ((∑ a, t i a * ω (Sum.inl a) - ∑ a, t j a * ω (Sum.inr a) : ℝ)
              * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc c i * Complex.exp ((∑ a, t i a * ω (Sum.inl a) : ℝ) * Complex.I)
          * ((starRingEnd ℂ) (c j)
            * Complex.exp (-((∑ a, t j a * ω (Sum.inr a) : ℝ) * Complex.I)))
        = c i * (starRingEnd ℂ) (c j)
            * (Complex.exp ((∑ a, t i a * ω (Sum.inl a) : ℝ) * Complex.I)
              * Complex.exp (-((∑ a, t j a * ω (Sum.inr a) : ℝ) * Complex.I))) := by
          ring
      _ = _ := by rw [hE]
  simp_rw [hpt]
  have hint : ∀ (i j : Fin M),
      Integrable (fun ω : EuclideanSpace ℝ (Fin N ⊕ Fin N) =>
        (c i * (starRingEnd ℂ) (c j))
          * Complex.exp ((⟪ω, freqVec (t i) (t j)⟫ : ℝ) * Complex.I))
        (fieldMeasure Δ (OS2MeasureLevel.doubled z)) :=
    fun i j => (integrable_charTerm Δ z (freqVec (t i) (t j))).const_mul _
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => hint i j))]
  have hterm : ∀ i j : Fin M,
      ∫ ω, (c i * (starRingEnd ℂ) (c j))
          * Complex.exp ((⟪ω, freqVec (t i) (t j)⟫ : ℝ) * Complex.I)
        ∂(fieldMeasure Δ (OS2MeasureLevel.doubled z))
      = (c i * (starRingEnd ℂ) (c j))
          * Complex.ofReal (Real.exp
              (-(qform Δ z (t i)) / 2 + -(qform Δ z (t j)) / 2
                + bform Δ z (t i) (t j))) := by
    intro i j
    rw [integral_const_mul]
    congr 1
    rw [← charFun_freqVec Δ hΔ z (t i) (t j), charFun_apply]
  simp_rw [integral_finset_sum _ (fun j _ => hint _ j), hterm]
  have hB : ∀ i j : Fin M, bform Δ z (t i) (t j)
      = ((Matrix.of fun i a => t i a) * reflKernel Δ z
          * (Matrix.of fun i a => t i a)ᴴ) i j := by
    intro i j
    rw [Matrix.mul_apply]
    rw [bform]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Matrix.of_apply, Matrix.conjTranspose_apply, star_trivial,
      reflKernel, OS2MeasureLevel.prodCov, OS2MeasureLevel.doubled,
      Sum.elim_inl, Sum.elim_inr]
    ring
  have hd : ∀ i j : Fin M,
      -(qform Δ z (t i)) / 2 + -(qform Δ z (t j)) / 2 + bform Δ z (t i) (t j)
      = (fun i => -(qform Δ z (t i)) / 2) i + (fun i => -(qform Δ z (t i)) / 2) j
        + ((Matrix.of fun i a => t i a) * reflKernel Δ z
            * (Matrix.of fun i a => t i a)ᴴ) i j := by
    intro i j
    rw [← hB]
  simp_rw [hd]
  exact gaussKernel_complex_nonneg (fun i => -(qform Δ z (t i)) / 2)
    (frequencyForm_posSemidef Δ (fun k _ => hΔ k) z hpos _) c

end OS2Exponential
