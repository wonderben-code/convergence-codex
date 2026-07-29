/-
  LatticeOS2: Genuine Reflection Positivity for the 1-d Massive Chain
  ===================================================================

  First genuine stair of the OS2 gap (tree §11.6, old gap #4; spine L23).
  What existed before: ReflectionPositivity.lean / F3_9d render OS2 as
  arithmetic over bare reals — `action_decomposes` is literally exp_add,
  positivity is exp_pos, the "inner product" is sq_nonneg; no reflection
  map, no covariance, no matrix appears (Phase 0 audit, verdict HOLLOW).

  WHAT THIS FILE PROVES (exactly this, nothing more):

  Setting: the 1-d massive lattice chain with covariance
  C(s, s') = exp(−Δ·|s − s'|) (the standard 1-d lattice propagator), sites
  at positive times tᵢ = i+1 for i : Fin n, time reflection θ(s) = −s.

  1. `reflectedCov` — the reflected covariance matrix
     M i j = C(θ(tᵢ), tⱼ) = exp(−Δ·(tᵢ + tⱼ)) (the |·| resolves because
     θ(tᵢ) < 0 < tⱼ always — proven, not assumed: `reflectedCov_eq`).
  2. `reflectedCov_eq_gram` — M factorises as the rank-one Gram matrix
     vᵀ·v with v i = exp(−Δ·tᵢ): the 1-d Markov property in exact form.
  3. `reflectedCov_posSemidef` — **OS2, finite-dimensional, genuine**: the
     reflected covariance matrix is positive semidefinite
     (`Matrix.posSemidef_conjTranspose_mul_self` applied to the Gram
     factor — a real PSD certificate, not a scalar identity).
  4. `os2_inequality` — the Osterwalder–Schrader inequality in test-function
     form: for every real test vector c,
     0 ≤ Σᵢⱼ cᵢ·cⱼ·C(θ(tᵢ), tⱼ), derived from 3 (dot-product form of PSD).
  5. `reflectedCov_nonzero` — non-vacuity: the matrix is not zero (its
     (0,0) entry is exp(−2Δ) > 0), so the PSD statement has content.

  WHAT THIS IS AND IS NOT (the honest frame): this is reflection positivity
  for the GAUSSIAN LATTICE COVARIANCE in one dimension, at the level of
  finite covariance matrices — the standard first stair (cf. Glimm–Jaffe
  §6.2, Osterwalder–Seiler). It is NOT: OS2 for a measure on a field
  configuration space (no measure appears); the ℤᵈ (d > 1) case, where the
  reflected covariance is PSD but not rank-one and needs the genuine Markov
  decomposition; the continuum limit; or any statement about Yang–Mills.
  Those stay open — the published [PREDICTED] tag for full OS2 should
  remain until at least the measure-level statement exists.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.StarOrdered

open Matrix Real

noncomputable section

namespace LatticeOS2

variable (n : ℕ) (Δ : ℝ)

/-! ## 1. Sites, reflection, covariance -/

/-- The positive-time sites: tᵢ = i + 1 > 0. -/
def site (i : Fin n) : ℝ := (i : ℝ) + 1

/-- Time reflection θ(s) = −s. -/
def reflect (s : ℝ) : ℝ := -s

/-- The 1-d massive lattice covariance C(s,s') = exp(−Δ·|s−s'|). -/
def cov (s s' : ℝ) : ℝ := exp (-Δ * |s - s'|)

theorem site_pos (i : Fin n) : 0 < site n i := by
  unfold site
  positivity

/-- The reflected covariance matrix: M i j = C(θ(tᵢ), tⱼ). -/
def reflectedCov : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => cov Δ (reflect (site n i)) (site n j)

/-- The absolute value resolves: since θ(tᵢ) < 0 < tⱼ,
    C(θ(tᵢ), tⱼ) = exp(−Δ·(tᵢ + tⱼ)) — proven from site positivity,
    not assumed. -/
theorem reflectedCov_eq (i j : Fin n) :
    reflectedCov n Δ i j = exp (-Δ * (site n i + site n j)) := by
  unfold reflectedCov cov reflect
  congr 1
  have hi := site_pos n i
  have hj := site_pos n j
  rw [abs_of_nonpos (by linarith)]
  ring

/-! ## 2. The Gram factorisation (the 1-d Markov property, exact form) -/

/-- The Gram vector v i = exp(−Δ·tᵢ), as a 1×n matrix. -/
def gramVec : Matrix (Fin 1) (Fin n) ℝ :=
  fun _ i => exp (-Δ * site n i)

/-- **The rank-one Gram factorisation**: M = vᵀ·v entrywise —
    M i j = exp(−Δ·tᵢ)·exp(−Δ·tⱼ). This is the exact 1-d form of the
    Markov property of the massive chain. -/
theorem reflectedCov_eq_gram :
    reflectedCov n Δ = (gramVec n Δ)ᴴ * gramVec n Δ := by
  ext i j
  rw [reflectedCov_eq, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, gramVec, star_trivial,
    Fin.sum_univ_one]
  rw [← Real.exp_add]
  congr 1
  ring

/-! ## 3. OS2: the reflected covariance is positive semidefinite -/

/-- **Reflection positivity (OS2), finite-dimensional, genuine**: the
    reflected covariance matrix of the 1-d massive chain is positive
    semidefinite. Proof: it IS a Gram matrix (`reflectedCov_eq_gram`), and
    Gram matrices are PSD (`Matrix.posSemidef_conjTranspose_mul_self`). -/
theorem reflectedCov_posSemidef : (reflectedCov n Δ).PosSemidef := by
  rw [reflectedCov_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self (gramVec n Δ)

/-- **The OS inequality in test-function form**: for every real test vector
    c on the positive-time sites,
    0 ≤ Σᵢⱼ cᵢ·cⱼ·C(θ(tᵢ), tⱼ). This is the shape in which OS2 is used:
    reflected correlations of arbitrary positive-time observables are
    nonnegative. -/
theorem os2_inequality (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * reflectedCov n Δ i j := by
  have h := (reflectedCov_posSemidef n Δ).dotProduct_mulVec_nonneg c
  calc (0 : ℝ) ≤ star c ⬝ᵥ (reflectedCov n Δ *ᵥ c) := h
    _ = ∑ i, ∑ j, c i * c j * reflectedCov n Δ i j := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, Pi.star_apply]
        congr 1
        funext i
        rw [Finset.mul_sum]
        congr 1
        funext j
        ring

/-! ## 4. Non-vacuity -/

/-- The reflected covariance is not the zero matrix (for n ≥ 1 its (0,0)
    entry exp(−2Δ) is strictly positive), so PSD is a statement with
    content here. -/
theorem reflectedCov_nonzero (hn : 0 < n) : reflectedCov n Δ ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h ⟨0, hn⟩) ⟨0, hn⟩
  rw [reflectedCov_eq] at h00
  exact absurd h00 (ne_of_gt (exp_pos _))

end LatticeOS2
