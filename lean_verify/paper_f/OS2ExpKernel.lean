/-
  OS2ExpKernel: the Reflected Kernel Matrix, and Kernel Positivity with
  COMPLEX Coefficients
  =====================================================================

  The matrix-side half of the exponential-algebra OS2 assembly
  (UNLOCK_WATCHLIST item "OS2 for the EXPONENTIAL algebra"). The integral
  half will pair exponential observables through the Gaussian
  characteristic function; what it needs from linear algebra is exactly
  this file:

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `theta_sub_abs` — the time reflection preserves every coordinate
     distance: |θx(k) − θy(k)| = |x(k) − y(k)|. Hence
     `prodCov_doubled_inr_inr`: the covariance between two REFLECTED sites
     equals the covariance between the sites themselves — θ is an isometry
     of the OU-product kernel.
  2. `reflKernel` — the CROSS-BLOCK kernel K(a,b) = C(zₐ, θ z_b) as a
     matrix on the positive-time index; `reflKernel_symm` (the reflected
     kernel is symmetric) and **`reflKernel_posSemidef`** — the packaging
     of `OS2ProductField.os2_reflection` as a `Matrix.PosSemidef`
     statement.
  3. **`frequencyForm_posSemidef`** — the frequency-conjugated kernel
     T·K·Tᵀ is PSD for ANY frequency matrix T: the matrix whose (i,j)
     entry is Σₐ_b tᵢ(a)·tⱼ(b)·C(zₐ, θz_b), which is precisely the
     covariance data of exponential observables.
  4. **`posSemidef_map_ofReal`** — the ℝ → ℂ bridge: a real PSD matrix is
     PSD over ℂ (entrywise `Complex.ofReal`). Proven by transporting a
     Gram decomposition, not by re/im coordinate algebra.
  5. **`gaussKernel_complex_nonneg`** — what the integral assembly will
     consume verbatim: for any exponents d, PSD B, and COMPLEX
     coefficients c,

        0 ≤ Σᵢⱼ cᵢ·conj(cⱼ)·e^{dᵢ + dⱼ + Bᵢⱼ}

     in the complex order (real and nonnegative) — the Schur-exponential
     kernel positivity with the coefficients the OS pairing actually has.

  Scope honesty: matrices only. No integral, no measure, no observable is
  paired here; the assembly that connects this to
  `OS2MeasureLevel.fieldMeasure` through `charFun_multivariateGaussian` is
  the next unit, and the watchlist item stays open until it lands.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import OS2MeasureLevel
import SchurExponential

open Matrix Real Finset OS2ProductField
open scoped ComplexOrder

noncomputable section

namespace OS2ExpKernel

/-! ## 1. The reflection is an isometry of the kernel -/

/-- The time reflection preserves every coordinate distance. -/
theorem theta_sub_abs {m : ℕ} (x y : Fin (m + 1) → ℝ) (k : Fin (m + 1)) :
    |theta x k - theta y k| = |x k - y k| := by
  refine Fin.cases ?_ ?_ k
  · rw [theta_zero, theta_zero, show -x 0 - -y 0 = -(x 0 - y 0) by ring,
      abs_neg]
  · intro l
    rw [theta_succ, theta_succ]

/-- The covariance between two reflected sites equals the covariance
    between the sites: θ is an isometry of the OU-product kernel. -/
theorem prodCov_doubled_inr_inr {m : ℕ} (Δ : Fin (m + 1) → ℝ) {N : ℕ}
    (z : Fin N → Fin (m + 1) → ℝ) (a b : Fin N) :
    OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inr a) (Sum.inr b)
      = OS2MeasureLevel.prodCov Δ (OS2MeasureLevel.doubled z) (Sum.inl a) (Sum.inl b) := by
  simp only [OS2MeasureLevel.prodCov, Matrix.of_apply, OS2MeasureLevel.doubled,
    Sum.elim_inl, Sum.elim_inr]
  exact Finset.prod_congr rfl fun k _ => by rw [theta_sub_abs]

/-! ## 2. The cross-block (reflected) kernel matrix is PSD -/

/-- The reflected kernel: K(a,b) = C(zₐ, θ z_b), the cross-block of the
    doubled covariance. -/
def reflKernel {m : ℕ} (Δ : Fin (m + 1) → ℝ) {N : ℕ}
    (z : Fin N → Fin (m + 1) → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun a b => ∏ k, Real.exp (-(Δ k) * |z a k - theta (z b) k|)

/-- The reflected kernel is symmetric: C(zₐ, θz_b) = C(z_b, θzₐ) —
    UNCONDITIONALLY: coordinate 0 gives |zₐ₀ + z_b₀|, symmetric with no
    sign hypothesis, and the spatial coordinates are symmetric by
    `abs_sub_comm`. (An adversarial review caught an earlier version
    carrying an unnecessary positivity hypothesis; it is needed only for
    positive SEMIDEFINITENESS below, not for symmetry.) -/
theorem reflKernel_symm {m : ℕ} (Δ : Fin (m + 1) → ℝ) {N : ℕ}
    (z : Fin N → Fin (m + 1) → ℝ) (a b : Fin N) :
    reflKernel Δ z a b = reflKernel Δ z b a := by
  simp only [reflKernel, Matrix.of_apply]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  congr 1
  refine Fin.cases ?_ ?_ k
  · rw [theta_zero, theta_zero, sub_neg_eq_add, sub_neg_eq_add, add_comm]
  · intro l
    rw [theta_succ, theta_succ, abs_sub_comm]

/-- **The reflected kernel matrix is PSD** — `os2_reflection`, packaged. -/
theorem reflKernel_posSemidef {m : ℕ} (Δ : Fin (m + 1) → ℝ)
    (hΔ : ∀ k, k ≠ 0 → 0 ≤ Δ k) {N : ℕ} (z : Fin N → Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 ≤ z i 0) :
    (reflKernel Δ z).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact reflKernel_symm Δ z b a
  · intro x
    have h := os2_reflection Δ hΔ z hpos x
    have heq : star x ⬝ᵥ reflKernel Δ z *ᵥ x
        = ∑ i, ∑ j, x i * x j
            * ∏ k, Real.exp (-(Δ k) * |z i k - theta (z j) k|) := by
      simp only [dotProduct, Matrix.mulVec, reflKernel, Matrix.of_apply,
        Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    exact h

/-! ## 3. Frequency conjugation -/

/-- The frequency-conjugated kernel T·K·Tᵀ — entry (i,j) is
    Σₐ_b tᵢ(a)·tⱼ(b)·C(zₐ, θz_b), the covariance data of exponential
    observables with frequency vectors tᵢ. PSD for ANY T. -/
theorem frequencyForm_posSemidef {m : ℕ} (Δ : Fin (m + 1) → ℝ)
    (hΔ : ∀ k, k ≠ 0 → 0 ≤ Δ k) {N M : ℕ} (z : Fin N → Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 ≤ z i 0) (T : Matrix (Fin M) (Fin N) ℝ) :
    (T * reflKernel Δ z * Tᴴ).PosSemidef :=
  (reflKernel_posSemidef Δ hΔ z hpos).mul_mul_conjTranspose_same T

/-! ## 4. The ℝ → ℂ bridge -/

/-- **A real PSD matrix is PSD over ℂ** (entrywise `Complex.ofReal`).
    Proven by transporting a Gram decomposition M = Pᵀ·P through the
    coefficient embedding — no real/imaginary coordinate algebra. -/
theorem posSemidef_map_ofReal {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosSemidef) :
    (A.map (Complex.ofReal)).PosSemidef := by
  obtain ⟨P, rfl⟩ := SchurProduct.exists_gram hA
  have heq : (Pᴴ * P).map (Complex.ofReal)
      = (P.map (Complex.ofReal))ᴴ * P.map (Complex.ofReal) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.map_apply, star_trivial, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.ofReal_mul]
    congr 1
    exact (Complex.conj_ofReal _).symm
  rw [heq]
  exact posSemidef_conjTranspose_mul_self _

/-! ## 5. Kernel positivity with complex coefficients -/

/-- **The Gaussian kernel form with COMPLEX coefficients is nonnegative**:
    for any exponents d, PSD B, and c : Fin M → ℂ, the Hermitian form
    Σᵢⱼ cᵢ·conj(cⱼ)·e^{dᵢ+dⱼ+Bᵢⱼ} is a nonnegative real — in the complex
    order. This is the statement the exponential OS pairing reduces to. -/
theorem gaussKernel_complex_nonneg {M : ℕ} (d : Fin M → ℝ)
    {B : Matrix (Fin M) (Fin M) ℝ} (hB : B.PosSemidef) (c : Fin M → ℂ) :
    0 ≤ ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j)
        * (Real.exp (d i + d j + B i j) : ℂ) := by
  have hker := SchurExponential.posSemidef_gaussian_kernel d hB
  have hkerC := posSemidef_map_ofReal hker
  have h := hkerC.dotProduct_mulVec_nonneg (star c)
  have heq : star (star c) ⬝ᵥ ((Matrix.of fun i j =>
      Real.exp (d i + d j + B i j)).map (Complex.ofReal)) *ᵥ (star c)
      = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j)
          * (Real.exp (d i + d j + B i j) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.of_apply,
      Pi.star_apply, RCLike.star_def]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.conj_conj]
    ring
  rwa [heq] at h

end OS2ExpKernel
