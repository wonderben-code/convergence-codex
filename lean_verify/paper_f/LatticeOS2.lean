/-
  LatticeOS2: Reflection Positivity for the 1-d Exponential Kernel
  ================================================================

  First stair of the OS2 gap (tree §11.6, old gap #4; spine L23). What
  existed before (Phase 0 audit, HOLLOW): the RP content of
  ReflectionPositivity.lean / F3_9d is exp_add and sq_nonneg over bare
  reals — no reflection map, no covariance function, no matrix. (Those
  files' Phase-7 sections do contain genuine 4×4 NCG matrix identities;
  the hollowness verdict is about their reflection-positivity content.)

  WHAT THIS FILE PROVES (exactly this, nothing more):

  Setting: the exponential kernel C(s,s') = exp(−Δ·|s−s'|) on the real
  line — proportional to (not identical to: normalisation differs) the
  standard 1-d lattice propagator; time reflection θ(s) = −s; ARBITRARY
  finitely many positive-time sites t : Fin n → ℝ with 0 < tᵢ.

  1. `cov_semigroup` — the semigroup/Markov identity of the kernel:
     for s ≤ u ≤ v, C(s,v) = C(s,u)·C(u,v). (This is the 1-d Markov
     factorisation property, now a theorem rather than a gloss.)
  2. `reflectedCov_eq` — for positive-time sites the reflected covariance
     M i j = C(θ(tᵢ), tⱼ) equals exp(−Δ·(tᵢ + tⱼ)) (the |·| resolved from
     site positivity — proven, not assumed).
  3. `reflectedCov_eq_gram` — M is the rank-one Gram matrix vᴴ·v with
     v i = exp(−Δ·tᵢ).
  4. `reflectedCov_posSemidef`, `os2_inequality` — M is PSD; equivalently
     0 ≤ Σᵢⱼ cᵢcⱼ·C(θ(tᵢ), tⱼ) for every real test vector c on arbitrary
     positive-time sites.
  5. `os2_eq_sq` — FULL TRANSPARENCY about how easy the 1-d case is: the
     OS2 quadratic form IS the perfect square (Σᵢ cᵢ·e^{−Δtᵢ})². In one
     dimension the cross-boundary block is rank one, so its positivity is
     a scalar square in matrix costume. The value of this file over the
     predecessors is DEFINITIONAL, not analytic: reflection, covariance,
     sites, and the OS2 statement exist as objects and the |·| resolution
     and semigroup identity are real (small) proofs — but the positivity
     itself is elementary, and this file says so.
  6. `reflectedCov_nonzero` — non-vacuity.

  PHYSICAL REGIME: every theorem above holds for ALL Δ ∈ ℝ (the proofs
  only use the product structure of the cross-boundary block). The
  INTERPRETATION of C as a covariance of a nondegenerate Gaussian field
  requires Δ > 0: for Δ < 0 the same-side kernel is not even positive
  semidefinite, so no Gaussian field exists at all; at Δ = 0 the kernel is
  the all-ones matrix — PSD, but only a degenerate field (one Gaussian
  copied to every site). "Correlation" language applies in the Δ > 0
  regime.

  NOT proven here: OS2 for a measure on a field configuration space (no
  measure appears); the ℤᵈ (d > 1) case, where the reflected block is not
  rank one and the genuine Markov decomposition is needed; the continuum
  limit; anything about Yang–Mills. The published [PREDICTED] tag for full
  OS2 should stand until at least the measure-level statement exists.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.StarOrdered

open Matrix Real

noncomputable section

namespace LatticeOS2

variable {n : ℕ} (Δ : ℝ) (t : Fin n → ℝ)

/-! ## 1. Kernel, reflection, and the semigroup identity -/

/-- Time reflection θ(s) = −s. -/
def reflect (s : ℝ) : ℝ := -s

/-- The exponential kernel C(s,s') = exp(−Δ·|s−s'|) (proportional to the
    standard 1-d lattice propagator; the normalisation constant is omitted
    and irrelevant to positivity). -/
def cov (s s' : ℝ) : ℝ := exp (-Δ * |s - s'|)

/-- **The semigroup (Markov factorisation) identity** of the exponential
    kernel: for ordered times s ≤ u ≤ v, C(s,v) = C(s,u)·C(u,v). This is
    the exactness behind the rank-one structure of the 1-d reflected block. -/
theorem cov_semigroup {s u v : ℝ} (hsu : s ≤ u) (huv : u ≤ v) :
    cov Δ s v = cov Δ s u * cov Δ u v := by
  unfold cov
  rw [← Real.exp_add]
  congr 1
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith),
    abs_of_nonpos (by linarith)]
  ring

/-! ## 2. The reflected covariance on arbitrary positive-time sites -/

/-- The reflected covariance matrix on sites t: M i j = C(θ(tᵢ), tⱼ). -/
def reflectedCov : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov Δ (reflect (t i)) (t j)

/-- For positive-time sites the |·| resolves:
    C(θ(tᵢ), tⱼ) = exp(−Δ·(tᵢ + tⱼ)) — from site positivity, not assumed. -/
theorem reflectedCov_eq (ht : ∀ i, 0 < t i) (i j : Fin n) :
    reflectedCov Δ t i j = exp (-Δ * (t i + t j)) := by
  unfold reflectedCov cov reflect
  congr 1
  have hi := ht i
  have hj := ht j
  rw [abs_of_nonpos (by linarith)]
  ring

/-- The Gram vector v i = exp(−Δ·tᵢ), as a 1×n matrix. -/
def gramVec : Matrix (Fin 1) (Fin n) ℝ :=
  fun _ i => exp (-Δ * t i)

/-- **The rank-one Gram factorisation**: M = vᴴ·v entrywise. -/
theorem reflectedCov_eq_gram (ht : ∀ i, 0 < t i) :
    reflectedCov Δ t = (gramVec Δ t)ᴴ * gramVec Δ t := by
  ext i j
  rw [reflectedCov_eq Δ t ht, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, gramVec, star_trivial,
    Fin.sum_univ_one]
  rw [← Real.exp_add]
  congr 1
  ring

/-! ## 3. OS2: positivity of the reflected covariance -/

/-- **Reflection positivity (OS2), finite-dimensional**: the reflected
    covariance matrix on arbitrary positive-time sites is positive
    semidefinite (Gram ⇒ PSD). See `os2_eq_sq` for how elementary the 1-d
    case is. -/
theorem reflectedCov_posSemidef (ht : ∀ i, 0 < t i) :
    (reflectedCov Δ t).PosSemidef := by
  rw [reflectedCov_eq_gram Δ t ht]
  exact Matrix.posSemidef_conjTranspose_mul_self (gramVec Δ t)

/-- The OS inequality in test-function form, on arbitrary positive-time
    sites: 0 ≤ Σᵢⱼ cᵢ·cⱼ·C(θ(tᵢ), tⱼ). -/
theorem os2_inequality (ht : ∀ i, 0 < t i) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * reflectedCov Δ t i j := by
  have h := (reflectedCov_posSemidef Δ t ht).dotProduct_mulVec_nonneg c
  calc (0 : ℝ) ≤ star c ⬝ᵥ (reflectedCov Δ t *ᵥ c) := h
    _ = ∑ i, ∑ j, c i * c j * reflectedCov Δ t i j := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, Pi.star_apply]
        congr 1
        funext i
        rw [Finset.mul_sum]
        congr 1
        funext j
        ring

/-- **Full transparency**: in one dimension the OS2 quadratic form IS a
    perfect square, (Σᵢ cᵢ·e^{−Δtᵢ})² — the rank-one structure makes the
    positivity elementary. This theorem states it so the file cannot be
    read as claiming analytic depth it does not have. -/
theorem os2_eq_sq (ht : ∀ i, 0 < t i) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * reflectedCov Δ t i j
      = (∑ i, c i * exp (-Δ * t i)) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  congr 1
  funext i
  congr 1
  funext j
  rw [reflectedCov_eq Δ t ht,
    show -Δ * (t i + t j) = -Δ * t i + -Δ * t j by ring, Real.exp_add]
  ring

/-! ## 4. Non-vacuity -/

/-- The reflected covariance is not the zero matrix for nonempty site sets
    (entries are positive exponentials). -/
theorem reflectedCov_nonzero (ht : ∀ i, 0 < t i) (hn : 0 < n) :
    reflectedCov Δ t ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  rw [reflectedCov_eq Δ t ht] at h00
  exact absurd h00 (ne_of_gt (exp_pos _))

/-! ## 5. The integer chain as an instance -/

/-- The original chain sites tᵢ = i+1. -/
def chainSite (i : Fin n) : ℝ := (i : ℝ) + 1

theorem chainSite_pos (i : Fin n) : 0 < chainSite i := by
  unfold chainSite
  positivity

/-- OS2 for the integer chain, as an instance of the general statement. -/
theorem chain_os2 (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * reflectedCov Δ chainSite i j :=
  os2_inequality Δ chainSite (fun i => chainSite_pos i) c

end LatticeOS2
