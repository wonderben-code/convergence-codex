/-
  OS2ProductField: Reflection Positivity in EVERY Dimension for the
  OU-Product Covariance — Stair S3, the Assembly
  =================================================================

  The top of the OS2 staircase mapped on UNLOCK_WATCHLIST. With stair S2
  (`OS2HigherDim.quadForm_nonneg`, the unreflected exponential covariance on
  monotone sites) and stair S1 (`SchurProduct.posSemidef_hadamard` /
  `posSemidef_entrywise_prod`, PSD closed under entrywise products) both
  climbed, this file performs the assembly:

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `quadForm_perm` / `quadForm_nonneg_all` / `ouCov_posSemidef_all` —
     the MONOTONICITY HYPOTHESIS of stair S2 is REMOVED: the exponential
     (Ornstein–Uhlenbeck) covariance matrix [exp(−Δ|tᵢ−tⱼ|)] is positive
     semidefinite for ARBITRARY site vectors t, by sorting the sites
     (`Tuple.sort`) and transporting the quadratic form along the
     permutation. This discharges the "enumeration choice" caveat written
     into `OS2HigherDim`'s header — the reindexing lemma is now formalised.
  2. `timeGram_posSemidef` — the reflected time factor
     [exp(−Δₜ(xᵢ+xⱼ))] is a rank-one Gram matrix (`vecMulVec`), hence PSD
     for ANY rate Δₜ — no sign hypothesis on the time rate is needed,
     and none is assumed.
  3. `prodCov_posSemidef` — the reflected covariance of the OU-PRODUCT
     field in dimension d = m + 1: the entrywise product of the reflected
     time factor with m spatial OU factors is PSD — one binary Schur
     product against the iterated Schur product of the spatial family.
  4. **`os2_product_field`** — REFLECTION POSITIVITY IN EVERY DIMENSION,
     explicit-sum form: for arbitrary spatial sites (no ordering), times
     xᵢ ≥ 0, and any test vector c,

        0 ≤ Σᵢⱼ cᵢcⱼ · e^{−Δₜ(xᵢ+xⱼ)} · Πₖ e^{−Δₛₖ|yₖᵢ−yₖⱼ|}.

  5. `reflectedProdCov_eq` — THE REFLECTION RESOLVES: the covariance
     between a site and a time-reflected site equals the rank-one time
     factor times the unreflected spatial factors (the every-dimension
     counterpart of `LatticeOS2.reflectedCov_eq`), and
     **`os2_reflection`** — the positivity statement with the REFLECTION
     LITERAL:
     sites s i : Fin (m+1) → ℝ with time coordinate s i 0 ≥ 0, the
     reflection θ flipping coordinate 0 (`theta`), and the pairing

        0 ≤ Σᵢⱼ cᵢcⱼ · Πₖ e^{−Δₖ|s i k − (θ (s j)) k|}

     — the quadratic form ⟨f, C Θf⟩ of a point-supported test functional
     against its time reflection.
  6. **`os2_four_dim`** — the named d = 4 instance: reflection positivity
     of the OU-product covariance in the physical dimension, four.
  7. `os2_two_dim_all` — the d = 2 statement of `OS2HigherDim.os2_two_dim`
     with its monotonicity hypothesis removed.
  8. `os2_reflection_attained` / `os2_reflection_pos` — non-vacuity: at a
     single site the form EQUALS e^{−2Δ₀x}·c², and is PROVEN strictly
     positive for c ≠ 0 — not a degenerate 0 ≤ 0.

  WHAT THIS IS AND IS NOT (the honesty box, unchanged from d = 2):

  * This is the OU-PRODUCT field — exponential covariance separately in
    each coordinate, C = Πₖ e^{−Δₖ|·|} — a genuine reflection-positive
    Gaussian covariance in every dimension, and the d-dimensional closure
    of the staircase's covariance-level programme. It is NOT the massive
    lattice Green's function (lattice-Laplacian) field the physics
    ultimately wants; no header downstream may blur that distinction.
  * COVARIANCE level: matrices and quadratic forms. The measure-level
    packaging (the Gaussian field with THIS covariance, OS2 as an integral
    statement) and the split of the `_proof_004_logos` sorry remain on
    UNLOCK_WATCHLIST and should be attempted in that order.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import OS2HigherDim
import SchurProduct
import Mathlib.Data.Fin.Tuple.Sort

open Matrix Real Finset

noncomputable section

namespace OS2ProductField

/-! ## 1. Removing the monotonicity hypothesis from stair S2 -/

/-- The exponential-covariance quadratic form is invariant under a
    simultaneous permutation of sites and test values. -/
theorem quadForm_perm (Δ : ℝ) {n : ℕ} (t c : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    OS2HigherDim.quadForm Δ (t ∘ σ) (c ∘ σ) = OS2HigherDim.quadForm Δ t c := by
  unfold OS2HigherDim.quadForm
  calc ∑ i, ∑ j, (c ∘ σ) i * (c ∘ σ) j * Real.exp (-Δ * |(t ∘ σ) i - (t ∘ σ) j|)
      = ∑ i, ∑ j, c i * (c ∘ σ) j * Real.exp (-Δ * |t i - (t ∘ σ) j|) :=
        Equiv.sum_comp σ
          (fun i => ∑ j, c i * (c ∘ σ) j * Real.exp (-Δ * |t i - (t ∘ σ) j|))
    _ = ∑ i, ∑ j, c i * c j * Real.exp (-Δ * |t i - t j|) :=
        Finset.sum_congr rfl fun i _ =>
          Equiv.sum_comp σ (fun j => c i * c j * Real.exp (-Δ * |t i - t j|))

/-- **Stair S2 without the ordering hypothesis**: the exponential-covariance
    quadratic form is nonnegative for ARBITRARY sites — sort the sites with
    `Tuple.sort` and transport along `quadForm_perm`. -/
theorem quadForm_nonneg_all (Δ : ℝ) (hΔ : 0 ≤ Δ) {n : ℕ} (t c : Fin n → ℝ) :
    0 ≤ OS2HigherDim.quadForm Δ t c := by
  have h := OS2HigherDim.quadForm_nonneg Δ hΔ n (t ∘ Tuple.sort t)
    (Tuple.monotone_sort t) (c ∘ Tuple.sort t)
  rwa [quadForm_perm] at h

/-- The exponential (OU) covariance matrix is PSD on ARBITRARY sites. -/
theorem ouCov_posSemidef_all (Δ : ℝ) (hΔ : 0 ≤ Δ) {n : ℕ} (t : Fin n → ℝ) :
    (Matrix.of fun i j => Real.exp (-Δ * |t i - t j|)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [abs_sub_comm]
  · intro x
    have h := quadForm_nonneg_all Δ hΔ t x
    rw [OS2HigherDim.quadForm] at h
    have heq : star x ⬝ᵥ (Matrix.of fun i j =>
        Real.exp (-Δ * |t i - t j|)) *ᵥ x
        = ∑ i, ∑ j, x i * x j * Real.exp (-Δ * |t i - t j|) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
        star_trivial]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [heq]
    exact h

/-! ## 2. The reflected time factor is a rank-one Gram matrix -/

/-- [exp(−Δₜ(xᵢ+xⱼ))] = g gᵀ with gᵢ = exp(−Δₜxᵢ): PSD for ANY rate Δₜ. -/
theorem timeGram_posSemidef (Δt : ℝ) {n : ℕ} (x : Fin n → ℝ) :
    (Matrix.of fun i j => Real.exp (-Δt * (x i + x j))).PosSemidef := by
  have h := posSemidef_vecMulVec_star_self (fun i => Real.exp (-Δt * x i))
  have hg : star (fun i => Real.exp (-Δt * x i)) = fun i => Real.exp (-Δt * x i) := by
    ext i
    simp
  rw [hg] at h
  have heq : (Matrix.of fun i j => Real.exp (-Δt * (x i + x j)))
      = vecMulVec (fun i => Real.exp (-Δt * x i)) (fun i => Real.exp (-Δt * x i)) := by
    ext i j
    simp only [Matrix.of_apply, vecMulVec_apply, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact h

/-! ## 3. The assembly: Schur products of the factors -/

/-- The reflected covariance of the OU-product field in dimension m + 1 is
    PSD: rank-one time factor ⊙ (entrywise product of m spatial OU factors). -/
theorem prodCov_posSemidef (Δt : ℝ) {m : ℕ} (Δs : Fin m → ℝ)
    (hΔs : ∀ k, 0 ≤ Δs k) {n : ℕ} (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ) :
    (Matrix.of fun i j => Real.exp (-Δt * (x i + x j))
        * ∏ k, Real.exp (-(Δs k) * |y k i - y k j|)).PosSemidef := by
  have hspat : (Matrix.of fun i j : Fin n =>
      ∏ k, Real.exp (-(Δs k) * |y k i - y k j|)).PosSemidef := by
    have h := SchurProduct.posSemidef_entrywise_prod
      (fun k => Matrix.of fun i j : Fin n => Real.exp (-(Δs k) * |y k i - y k j|))
      (fun k => ouCov_posSemidef_all (Δs k) (hΔs k) (y k))
    simpa only [Matrix.of_apply] using h
  have h := SchurProduct.posSemidef_hadamard (timeGram_posSemidef Δt x) hspat
  simpa only [Matrix.hadamard, Matrix.of_apply] using h

/-! ## 4. Reflection positivity in every dimension -/

/-- **OS2 FOR THE OU-PRODUCT FIELD IN EVERY DIMENSION d = m + 1**
    (explicit-sum form): times xᵢ ≥ 0 are reflected (xᵢ + xⱼ in the
    exponent), the m spatial site families are ARBITRARY (no ordering),
    the spatial rates are nonnegative, and the time rate is arbitrary. -/
theorem os2_product_field (Δt : ℝ) {m : ℕ} (Δs : Fin m → ℝ)
    (hΔs : ∀ k, 0 ≤ Δs k) {n : ℕ} (x : Fin n → ℝ) (y : Fin m → Fin n → ℝ)
    (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      (Real.exp (-Δt * (x i + x j)) * ∏ k, Real.exp (-(Δs k) * |y k i - y k j|)) := by
  have h := (prodCov_posSemidef Δt Δs hΔs x y).dotProduct_mulVec_nonneg c
  have heq : star c ⬝ᵥ (Matrix.of fun i j => Real.exp (-Δt * (x i + x j))
      * ∏ k, Real.exp (-(Δs k) * |y k i - y k j|)) *ᵥ c
      = ∑ i, ∑ j, c i * c j *
        (Real.exp (-Δt * (x i + x j))
          * ∏ k, Real.exp (-(Δs k) * |y k i - y k j|)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply,
      star_trivial]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heq] at h
  exact h

/-- Time reflection on sites in dimension m + 1: flip coordinate 0. -/
def theta {m : ℕ} (s : Fin (m + 1) → ℝ) : Fin (m + 1) → ℝ :=
  Function.update s 0 (-(s 0))

@[simp] theorem theta_zero {m : ℕ} (s : Fin (m + 1) → ℝ) : theta s 0 = -(s 0) :=
  Function.update_self ..

@[simp] theorem theta_succ {m : ℕ} (s : Fin (m + 1) → ℝ) (k : Fin m) :
    theta s k.succ = s k.succ :=
  Function.update_of_ne (Fin.succ_ne_zero k) ..

/-- **The reflection resolves**: for sites a, b with nonnegative time
    coordinates, the product covariance between a and the TIME-REFLECTED b
    is the rank-one time factor times the unreflected spatial factors —
    the formal counterpart of `LatticeOS2.reflectedCov_eq` in every
    dimension. This identity is where |a₀ − (−b₀)| = a₀ + b₀ happens. -/
theorem reflectedProdCov_eq {m : ℕ} (Δ : Fin (m + 1) → ℝ)
    (a b : Fin (m + 1) → ℝ) (ha : 0 ≤ a 0) (hb : 0 ≤ b 0) :
    (∏ k, Real.exp (-(Δ k) * |a k - theta b k|))
      = Real.exp (-(Δ 0) * (a 0 + b 0))
        * ∏ k : Fin m, Real.exp (-(Δ k.succ) * |a k.succ - b k.succ|) := by
  rw [Fin.prod_univ_succ]
  congr 1
  · congr 1
    rw [theta_zero]
    have habs : |a 0 - -(b 0)| = a 0 + b 0 := by
      rw [sub_neg_eq_add, abs_of_nonneg (by linarith)]
    rw [habs]

/-- **OS2 with the reflection literal**: sites sᵢ in dimension m + 1 with
    time coordinate sᵢ(0) ≥ 0, paired against their time reflections
    θ(sⱼ). The rate hypothesis is needed only for the SPATIAL coordinates —
    the time factor is rank-one for any rate. -/
theorem os2_reflection {m : ℕ} (Δ : Fin (m + 1) → ℝ)
    (hΔ : ∀ k, k ≠ 0 → 0 ≤ Δ k) {n : ℕ} (s : Fin n → Fin (m + 1) → ℝ)
    (hpos : ∀ i, 0 ≤ s i 0) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      ∏ k, Real.exp (-(Δ k) * |s i k - theta (s j) k|) := by
  have hfac : ∀ i j : Fin n,
      (∏ k, Real.exp (-(Δ k) * |s i k - theta (s j) k|))
        = Real.exp (-(Δ 0) * (s i 0 + s j 0))
          * ∏ k : Fin m, Real.exp (-(Δ k.succ) * |s i k.succ - s j k.succ|) :=
    fun i j => reflectedProdCov_eq Δ (s i) (s j) (hpos i) (hpos j)
  simp_rw [hfac]
  exact os2_product_field (Δ 0) (fun k => Δ k.succ)
    (fun k => hΔ k.succ (Fin.succ_ne_zero k)) (fun i => s i 0)
    (fun k i => s i k.succ) c

/-- **REFLECTION POSITIVITY IN FOUR DIMENSIONS** — the named physical
    instance (m = 3 spatial coordinates): the reflected OU-product
    covariance on ℝ⁴ has nonnegative quadratic form. -/
theorem os2_four_dim (Δ : Fin 4 → ℝ) (hΔ : ∀ k, k ≠ 0 → 0 ≤ Δ k) {n : ℕ}
    (s : Fin n → Fin 4 → ℝ) (hpos : ∀ i, 0 ≤ s i 0) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      ∏ k, Real.exp (-(Δ k) * |s i k - theta (s j) k|) :=
  os2_reflection (m := 3) Δ hΔ s hpos c

/-- The d = 2 statement of `OS2HigherDim.os2_two_dim`, with its
    monotonicity hypothesis on the spatial coordinates REMOVED. -/
theorem os2_two_dim_all (Δt Δs : ℝ) (hΔs : 0 ≤ Δs) {n : ℕ}
    (x y : Fin n → ℝ) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j
        * (Real.exp (-Δt * (x i + x j)) * Real.exp (-Δs * |y i - y j|)) := by
  have hfac : ∀ i j : Fin n,
      c i * c j * (Real.exp (-Δt * (x i + x j)) * Real.exp (-Δs * |y i - y j|))
        = (c i * Real.exp (-Δt * x i)) * (c j * Real.exp (-Δt * x j))
            * Real.exp (-Δs * |y i - y j|) := by
    intro i j
    rw [show -Δt * (x i + x j) = (-Δt * x i) + (-Δt * x j) by ring, Real.exp_add]
    ring
  simp_rw [hfac]
  exact quadForm_nonneg_all Δs hΔs y (fun i => c i * Real.exp (-Δt * x i))

/-! ## 5. Non-vacuity -/

/-- At a single site the reflected form is e^{−2Δ₀x}·c² — strictly positive
    for c ≠ 0, not an empty or degenerate statement. -/
theorem os2_reflection_attained {m : ℕ} (Δ : Fin (m + 1) → ℝ)
    (s : Fin 1 → Fin (m + 1) → ℝ) (h0 : 0 ≤ s 0 0) (c : Fin 1 → ℝ) :
    (∑ i, ∑ j, c i * c j *
        ∏ k, Real.exp (-(Δ k) * |s i k - theta (s j) k|))
      = Real.exp (-(Δ 0) * (2 * s 0 0)) * (c 0 * c 0) := by
  rw [Fin.sum_univ_one, Fin.sum_univ_one, Fin.prod_univ_succ]
  have h1 : |s 0 0 - theta (s 0) 0| = 2 * s 0 0 := by
    rw [theta_zero, sub_neg_eq_add, abs_of_nonneg (by linarith)]
    ring
  have h2 : (∏ k : Fin m, Real.exp (-(Δ k.succ) * |s 0 k.succ - theta (s 0) k.succ|))
      = 1 := by
    refine Finset.prod_eq_one fun k _ => ?_
    rw [theta_succ, sub_self, abs_zero, mul_zero, Real.exp_zero]
  rw [h1, h2]
  ring

/-- Strict positivity at a single site with c ≠ 0: the form is > 0, so the
    reflection-positivity statements are not degenerate 0 ≤ 0 facts. -/
theorem os2_reflection_pos {m : ℕ} (Δ : Fin (m + 1) → ℝ)
    (s : Fin 1 → Fin (m + 1) → ℝ) (h0 : 0 ≤ s 0 0) (c : Fin 1 → ℝ)
    (hc : c 0 ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j *
        ∏ k, Real.exp (-(Δ k) * |s i k - theta (s j) k|) := by
  rw [os2_reflection_attained Δ s h0 c]
  exact mul_pos (Real.exp_pos _) (mul_self_pos.mpr hc)

end OS2ProductField
