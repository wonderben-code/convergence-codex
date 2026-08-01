/-
  OS2HigherDim: Reflection Positivity Above One Dimension — the d = 2 Case
  ========================================================================

  The queue's last item: measure-level OS2 in d > 1, the trigger for
  splitting the estate's one honest `sorry`. `LatticeOS2` proved it in one
  dimension, where the reflected covariance is a rank-one Gram matrix. In
  d ≥ 2 the reflected covariance is a rank-one factor TIMES the spectator
  covariance, so two new facts are needed: positive semidefiniteness of the
  UNREFLECTED exponential covariance (this file, stair S2 of the mapped
  staircase), and — for d > 2 — the Schur product theorem (absent from
  Mathlib when this header was written; since PROVEN downstream in
  `SchurProduct.lean`). At d = 2 exactly one spectator coordinate survives
  and Schur is not needed. This file therefore proves the d = 2 case
  outright, AT COVARIANCE LEVEL — the measure-level packaging remains on
  the watchlist.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `bilinear_bump` — expanding a quadratic form at a test function bumped
     at one point: the bookkeeping lemma the induction lives on.
  2. **`quadForm_nonneg` / `ouCov_posSemidef`** — for Δ ≥ 0 and MONOTONE
     sites t₁ ≤ … ≤ tₙ, the exponential (Ornstein–Uhlenbeck) covariance
     matrix [exp(−Δ|tᵢ−tⱼ|)] is positive semidefinite. The proof is the
     conditional-variance completion: peeling the largest site costs
     (1 − ρ²)·c² ≥ 0, with ρ ≤ 1 the transition weight to its neighbour —
     pure algebra plus the semigroup identity, no Fourier, no Bochner. The
     monotonicity hypothesis is an ENUMERATION choice, not a physical
     restriction (a finite site set can always be listed in order); the
     reindexing lemma IS formalised downstream and the hypothesis REMOVED:
     `OS2ProductField.quadForm_nonneg_all` / `ouCov_posSemidef_all`.
  3. **`os2_two_dim`** — REFLECTION POSITIVITY IN TWO DIMENSIONS: for sites
     (xᵢ, yᵢ) with time xᵢ > 0 and monotone spatial coordinates, the
     time-reflected product covariance

        R(i,j) = e^{−Δₜ(xᵢ+xⱼ)} · e^{−Δₛ|yᵢ−yⱼ|}

     has nonnegative quadratic form: 0 ≤ Σᵢⱼ cᵢcⱼ R(i,j). The reflected
     time factor is rank-one (e^{−Δₜxᵢ}·e^{−Δₜxⱼ}), so the whole form is
     the spatial form evaluated at the rescaled test function — PSD by
     item 2, no Schur needed. NOTE (adversarial review round 3, F1, folded
     downstream): in THIS file the resolution |xᵢ−(−xⱼ)| = xᵢ+xⱼ lives in
     prose, not code. The reflection AS AN OBJECT — the map θ and the named
     identity C(zᵢ, θzⱼ) = rank-one × spatial — is formalised in
     `OS2ProductField.theta` / `reflectedProdCov_eq` / `os2_reflection`.
  4. `os2_two_dim_attained` / `os2_two_dim_pos` — non-vacuity: at a single
     site the form equals e^{−2Δₜx₀}·c², and is PROVEN strictly positive
     for c ≠ 0.

  NOT proven here, each recorded on UNLOCK_WATCHLIST:

  * **d > 2.** CLOSED DOWNSTREAM since this header was written: the Schur
    product theorem is now `SchurProduct.posSemidef_hadamard` (stair S1),
    and the every-dimension assembly — d = 4 included — is
    `OS2ProductField.os2_product_field` / `os2_reflection` /
    `os2_four_dim` (stair S3).
  * **The lattice-Laplacian field.** This covariance is the OU PRODUCT
    field — exponential covariance separately in each coordinate — a
    genuine reflection-positive Gaussian structure in d dimensions but NOT
    the massive lattice Green's function the physics ultimately wants. No
    header downstream may blur that distinction.
  * The measure-level packaging (the Gaussian measure with THIS covariance,
    OS2 as an integral statement), and the split of the `_proof_004_logos`
    sorry, which should be attempted only after the above.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp

open Matrix Real Finset

noncomputable section

namespace OS2HigherDim

/-! ## 1. The bump-expansion bookkeeping -/

/-- Expanding Σᵢⱼ c′ᵢ c′ⱼ Mᵢⱼ where c′ is c bumped by β at one index L, for
    symmetric M. -/
theorem bilinear_bump {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, M i j = M j i) (a : Fin n → ℝ) (L : Fin n) (β : ℝ) :
    (∑ i, ∑ j, (a i + if i = L then β else 0) * (a j + if j = L then β else 0)
        * M i j)
      = (∑ i, ∑ j, a i * a j * M i j)
        + 2 * (β * ∑ i, a i * M i L) + β * β * M L L := by
  have hexp : ∀ i j : Fin n,
      (a i + if i = L then β else 0) * (a j + if j = L then β else 0) * M i j
        = a i * a j * M i j
          + a i * (if j = L then β else 0) * M i j
          + (if i = L then β else 0) * a j * M i j
          + (if i = L then β else 0) * (if j = L then β else 0) * M i j := by
    intro i j
    ring
  simp_rw [hexp, Finset.sum_add_distrib]
  have h2 : ∀ i : Fin n,
      (∑ j, a i * (if j = L then β else 0) * M i j) = a i * β * M i L := by
    intro i
    rw [Finset.sum_eq_single L]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb]
      ring
    · intro h
      exact absurd (Finset.mem_univ L) h
  have h3 : (∑ i, ∑ j, (if i = L then β else 0) * a j * M i j)
      = ∑ j, β * a j * M L j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single L]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg hb]
      ring
    · intro h
      exact absurd (Finset.mem_univ L) h
  have h4 : (∑ i, ∑ j, (if i = L then β else 0) * (if j = L then β else 0) * M i j)
      = β * β * M L L := by
    rw [Finset.sum_eq_single L]
    · rw [if_pos rfl]
      rw [Finset.sum_eq_single L]
      · rw [if_pos rfl]
      · intro b _ hb
        rw [if_neg hb]
        ring
      · intro h
        exact absurd (Finset.mem_univ L) h
    · intro b _ hb
      rw [if_neg hb]
      simp
    · intro h
      exact absurd (Finset.mem_univ L) h
  simp_rw [h2]
  rw [h3, h4]
  have h5 : (∑ j, β * a j * M L j) = ∑ i, a i * β * M i L := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsym L i]
    ring
  rw [h5]
  have h6 : (∑ i, a i * β * M i L) = β * ∑ i, a i * M i L := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h6]
  ring

/-! ## 2. The exponential covariance on ordered sites -/

/-- The quadratic form of the exponential covariance. -/
def quadForm (Δ : ℝ) {n : ℕ} (t : Fin n → ℝ) (c : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * c j * Real.exp (-Δ * |t i - t j|)

/-- The semigroup identity: for a ≤ b ≤ d,
    e^{−Δ|a−d|} = e^{−Δ|a−b|}·e^{−Δ(d−b)}. -/
theorem semigroup_step (Δ a b d : ℝ) (hab : a ≤ b) (hbd : b ≤ d) :
    Real.exp (-Δ * |a - d|)
      = Real.exp (-Δ * |a - b|) * Real.exp (-Δ * (d - b)) := by
  rw [← Real.exp_add]
  congr 1
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

/-- **The completion induction**: the exponential-covariance quadratic form
    on monotone sites is nonnegative. -/
theorem quadForm_nonneg (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ∀ (n : ℕ) (t : Fin n → ℝ), Monotone t → ∀ c : Fin n → ℝ,
      0 ≤ quadForm Δ t c := by
  intro n
  induction n with
  | zero =>
      intro t _ c
      simp [quadForm]
  | succ k ih =>
      intro t hmono c
      cases k with
      | zero =>
          have h : quadForm Δ t c = c 0 * c 0 := by
            simp [quadForm]
          rw [h]
          exact mul_self_nonneg _
      | succ m =>
          have htPL : t ((Fin.last m).castSucc) ≤ t (Fin.last (m + 1)) :=
            hmono (Fin.le_last _)
          set ρ : ℝ := Real.exp (-Δ * (t (Fin.last (m + 1))
            - t ((Fin.last m).castSucc))) with hρ
          have hρpos : 0 < ρ := Real.exp_pos _
          have hρle : ρ ≤ 1 := by
            rw [hρ, Real.exp_le_one_iff]
            nlinarith [htPL]
          have hmono' : Monotone (t ∘ Fin.castSucc) :=
            hmono.comp Fin.strictMono_castSucc.monotone
          -- the semigroup identity against the peeled site
          have hkey : ∀ i : Fin (m + 1),
              Real.exp (-Δ * |t i.castSucc - t (Fin.last (m + 1))|)
                = Real.exp (-Δ * |t i.castSucc - t ((Fin.last m).castSucc)|)
                    * ρ := by
            intro i
            have h1 : t i.castSucc ≤ t ((Fin.last m).castSucc) :=
              hmono (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last i))
            rw [semigroup_step Δ _ _ _ h1 htPL, hρ]
          -- shorthand for the reduced covariance, only to feed bilinear_bump
          have hbump := bilinear_bump
            (Matrix.of fun i j : Fin (m + 1) =>
              Real.exp (-Δ * |t i.castSucc - t j.castSucc|))
            (fun i j => by
              simp only [Matrix.of_apply]
              rw [abs_sub_comm])
            (fun i => c i.castSucc) (Fin.last m) (ρ * c (Fin.last (m + 1)))
          simp only [Matrix.of_apply] at hbump
          -- peel the last row and column of the full form
          have hsplit : quadForm Δ t c
              = (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
                  c i.castSucc * c j.castSucc
                    * Real.exp (-Δ * |t i.castSucc - t j.castSucc|))
                + 2 * ((ρ * c (Fin.last (m + 1)))
                    * ∑ i : Fin (m + 1), c i.castSucc
                        * Real.exp (-Δ * |t i.castSucc - t ((Fin.last m).castSucc)|))
                + c (Fin.last (m + 1)) * c (Fin.last (m + 1)) := by
            rw [quadForm, Fin.sum_univ_castSucc]
            have hrow : ∀ i : Fin (m + 1),
                (∑ j : Fin (m + 2),
                    c i.castSucc * c j * Real.exp (-Δ * |t i.castSucc - t j|))
                  = (∑ j : Fin (m + 1), c i.castSucc * c j.castSucc
                      * Real.exp (-Δ * |t i.castSucc - t j.castSucc|))
                    + c i.castSucc * c (Fin.last (m + 1))
                        * (Real.exp (-Δ * |t i.castSucc - t ((Fin.last m).castSucc)|)
                            * ρ) := by
              intro i
              rw [Fin.sum_univ_castSucc, hkey i]
            have hlast : (∑ j : Fin (m + 2),
                c (Fin.last (m + 1)) * c j
                  * Real.exp (-Δ * |t (Fin.last (m + 1)) - t j|))
                = (∑ j : Fin (m + 1), c j.castSucc * c (Fin.last (m + 1))
                    * (Real.exp (-Δ * |t j.castSucc - t ((Fin.last m).castSucc)|)
                        * ρ))
                  + c (Fin.last (m + 1)) * c (Fin.last (m + 1)) := by
              rw [Fin.sum_univ_castSucc]
              congr 1
              · refine Finset.sum_congr rfl fun j _ => ?_
                rw [abs_sub_comm, hkey j]
                ring
              · rw [sub_self, abs_zero, mul_zero, Real.exp_zero, mul_one]
            simp_rw [hrow]
            rw [Finset.sum_add_distrib, hlast]
            have hc1 : (∑ i : Fin (m + 1), c i.castSucc * c (Fin.last (m + 1))
                * (Real.exp (-Δ * |t i.castSucc - t ((Fin.last m).castSucc)|) * ρ))
                = (ρ * c (Fin.last (m + 1))) * ∑ i : Fin (m + 1), c i.castSucc
                    * Real.exp (-Δ * |t i.castSucc - t ((Fin.last m).castSucc)|) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
            rw [hc1]
            ring
          -- the reduced form at the bumped test function is the bump expansion
          have hreduced : quadForm Δ (t ∘ Fin.castSucc)
              (fun i => c i.castSucc
                + if i = Fin.last m then ρ * c (Fin.last (m + 1)) else 0)
              = (∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
                  c i.castSucc * c j.castSucc
                    * Real.exp (-Δ * |t i.castSucc - t j.castSucc|))
                + 2 * ((ρ * c (Fin.last (m + 1)))
                    * ∑ i : Fin (m + 1), c i.castSucc
                        * Real.exp (-Δ * |t i.castSucc - t ((Fin.last m).castSucc)|))
                + (ρ * c (Fin.last (m + 1))) * (ρ * c (Fin.last (m + 1)))
                    * Real.exp (-Δ * |t ((Fin.last m).castSucc)
                        - t ((Fin.last m).castSucc)|) := by
            rw [quadForm]
            exact hbump
          rw [sub_self, abs_zero, mul_zero, Real.exp_zero, mul_one] at hreduced
          -- the completion identity
          have hcomplete : quadForm Δ t c
              = quadForm Δ (t ∘ Fin.castSucc)
                  (fun i => c i.castSucc
                    + if i = Fin.last m then ρ * c (Fin.last (m + 1)) else 0)
                + (1 - ρ ^ 2)
                    * (c (Fin.last (m + 1)) * c (Fin.last (m + 1))) := by
            rw [hsplit, hreduced]
            ring
          rw [hcomplete]
          have hind := ih (t ∘ Fin.castSucc) hmono'
            (fun i => c i.castSucc
              + if i = Fin.last m then ρ * c (Fin.last (m + 1)) else 0)
          have hfac : 0 ≤ (1 - ρ ^ 2)
              * (c (Fin.last (m + 1)) * c (Fin.last (m + 1))) := by
            refine mul_nonneg ?_ (mul_self_nonneg _)
            nlinarith [hρpos, hρle]
          linarith

/-- **The exponential covariance matrix is PSD** on monotone sites. -/
theorem ouCov_posSemidef (Δ : ℝ) (hΔ : 0 ≤ Δ) {n : ℕ} (t : Fin n → ℝ)
    (hmono : Monotone t) :
    (Matrix.of fun i j => Real.exp (-Δ * |t i - t j|)).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [abs_sub_comm]
  · intro x
    have h := quadForm_nonneg Δ hΔ n t hmono x
    rw [quadForm] at h
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

/-! ## 3. Reflection positivity in two dimensions -/

/-- **OS2 IN d = 2**: for sites (xᵢ, yᵢ) with positive times and monotone
    spatial coordinates, the time-reflected product covariance has
    nonnegative quadratic form. The reflected time factor is rank-one, so
    the form is the spatial form at the rescaled test function — no Schur
    product theorem needed at d = 2. -/
theorem os2_two_dim (Δt Δs : ℝ) (hΔs : 0 ≤ Δs) {n : ℕ}
    (x y : Fin n → ℝ) (hmono : Monotone y) (c : Fin n → ℝ) :
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
  exact quadForm_nonneg Δs hΔs n y hmono (fun i => c i * Real.exp (-Δt * x i))

/-- Non-vacuity: at a single site the reflected form is e^{−2Δₜx₀}·c² — a
    genuine positive quantity, not an empty sum. -/
theorem os2_two_dim_attained (Δt Δs : ℝ) (x y c : Fin 1 → ℝ) :
    (∑ i, ∑ j, c i * c j
        * (Real.exp (-Δt * (x i + x j)) * Real.exp (-Δs * |y i - y j|)))
      = Real.exp (-Δt * (x 0 + x 0)) * (c 0 * c 0) := by
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  simp only [sub_self, abs_zero, mul_zero, Real.exp_zero]
  ring

/-- Strict positivity of the single-site reflected form for c ≠ 0 — the
    claim the header makes, now a theorem rather than a remark. -/
theorem os2_two_dim_pos (Δt Δs : ℝ) (x y c : Fin 1 → ℝ) (hc : c 0 ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j
        * (Real.exp (-Δt * (x i + x j)) * Real.exp (-Δs * |y i - y j|)) := by
  rw [os2_two_dim_attained]
  exact mul_pos (Real.exp_pos _) (mul_self_pos.mpr hc)

end OS2HigherDim
