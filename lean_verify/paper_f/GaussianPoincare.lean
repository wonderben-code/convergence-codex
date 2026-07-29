/-
  GaussianPoincare: Towards the 1-d Gaussian Poincaré Inequality
  ==============================================================

  Frontier unit (tree §11.4/§11.6, spine L23; wall #1 of the honest wall
  map). TARGET: Var_γ(f) ≤ E_γ[(f′)²] for the standard Gaussian γ and
  polynomial test functions f — the Bakry-Émery spectral gap at its first
  honest stair. What the estate has today (Phase 0 audit): the spec doc
  tags "Bakry-Émery spectral gap (gap = 2/Λ²)" as PROVED ★, but in Lean
  the gap is a DEFINITION and the criterion field is discharged by
  `le_refl` — no measure, no variance, no test function appears.

  STATUS OF THIS FILE: work in progress, built in stairs. Section 1 (this
  commit) is the ALGEBRAIC core: the probabilists' Hermite polynomials over
  ℝ, their derivative identity Hₙ′ = n·Hₙ₋₁ (which Mathlib does NOT have —
  Mathlib supplies only the recurrence Hₙ₊₁ = X·Hₙ − Hₙ′ and the Rodrigues
  formula), and the fact that they form a basis: every real polynomial is a
  finite ℝ-combination of Hermite polynomials, with an explicit degree
  bound. Nothing here is analytic yet, and nothing here is claimed to be
  the Poincaré inequality: the measure-theoretic stairs (Gaussian
  integration by parts, L²(γ)-orthogonality, the variance identity) are
  named at the bottom of this file and are NOT proven yet.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Linarith

open Polynomial

noncomputable section

namespace GaussianPoincare

/-! ## 1. The Hermite polynomials over ℝ

    Mathlib defines `Polynomial.hermite : ℕ → ℤ[X]` (probabilists'
    convention, monic) by the recurrence Hₙ₊₁ = X·Hₙ − Hₙ′. We work over ℝ,
    where the test functions live. -/

/-- The n-th probabilists' Hermite polynomial with real coefficients. -/
def H (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

@[simp] theorem H_zero : H 0 = 1 := by
  simp [H, hermite_zero]

@[simp] theorem H_one : H 1 = X := by
  simp [H]

/-- The defining recurrence, transported to ℝ. -/
theorem H_succ (n : ℕ) : H (n + 1) = X * H n - derivative (H n) := by
  unfold H
  rw [hermite_succ, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X,
    derivative_map]

theorem H_monic (n : ℕ) : (H n).Monic :=
  (hermite_monic n).map _

@[simp] theorem natDegree_H (n : ℕ) : (H n).natDegree = n := by
  unfold H
  rw [natDegree_map_eq_of_injective (Int.cast_injective) _, natDegree_hermite]

@[simp] theorem degree_H (n : ℕ) : (H n).degree = n := by
  have := (H_monic n).ne_zero
  rw [degree_eq_natDegree this, natDegree_H]

/-- Evaluation agrees with Mathlib's `aeval` on the integral Hermite
    polynomials, so the Rodrigues-type lemmas in
    `Mathlib.RingTheory.Polynomial.Hermite.Gaussian` apply verbatim to `H`. -/
theorem eval_H (n : ℕ) (x : ℝ) : (H n).eval x = aeval x (hermite n) := by
  simp [H, aeval_def, eval_map]

/-! ## 2. The derivative identity Hₙ′ = n·Hₙ₋₁

    This is the fact that makes Hermite polynomials the eigenbasis of the
    Ornstein-Uhlenbeck operator, and it is **not** in Mathlib: Mathlib has
    the recurrence and the Rodrigues formula only. It is what will turn the
    Poincaré inequality into a statement about the coefficient index. -/

/-- **The derivative identity**: Hₙ₊₁′ = (n+1)·Hₙ. Proven by induction from
    the recurrence alone (no Rodrigues formula, no analysis). -/
theorem derivative_H_succ (n : ℕ) :
    derivative (H (n + 1)) = ((n : ℝ) + 1) • H n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [H_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul,
        ih, derivative_smul, mul_smul_comm, add_sub_assoc, ← smul_sub,
        ← H_succ n]
      push_cast
      module

/-- The derivative identity in the form Hₙ′ = n·Hₙ₋₁ (for n ≥ 1). -/
theorem derivative_H (n : ℕ) (hn : 0 < n) :
    derivative (H n) = (n : ℝ) • H (n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simpa using derivative_H_succ m

/-- The derivative lowers the index, so it lowers the degree by exactly one
    (non-vacuity of the identity above). -/
theorem natDegree_derivative_H_succ (n : ℕ) :
    (derivative (H (n + 1))).natDegree = n := by
  have hc : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [derivative_H_succ, smul_eq_C_mul,
    natDegree_mul (C_ne_zero.mpr hc) (H_monic n).ne_zero, natDegree_C,
    natDegree_H, zero_add]

/-- **The three-term recurrence** X·Hₙ₊₁ = Hₙ₊₂ + (n+1)·Hₙ, obtained by
    feeding the derivative identity into the defining recurrence. This is the
    form in which the Hermite family will drive the orthogonality induction:
    multiplication by X raises the index by one and adds a multiple of the
    index below. -/
theorem X_mul_H_succ (n : ℕ) :
    X * H (n + 1) = H (n + 2) + ((n : ℝ) + 1) • H n := by
  rw [H_succ (n + 1), derivative_H_succ]
  ring

/-- The base case of the three-term recurrence: X·H₀ = H₁. -/
theorem X_mul_H_zero : X * H 0 = H 1 := by
  simp

theorem H_ne_zero (n : ℕ) : H n ≠ 0 := (H_monic n).ne_zero

/-! ## 3. The Hermite polynomials are a basis

    Every real polynomial of degree ≤ N is a finite ℝ-combination of
    H₀, …, H_N. This is pure algebra (the Hₙ are monic of degree n), but it
    is what lets a Poincaré statement about "all polynomials" be reduced to
    a statement about coefficients. -/

/-- **Hermite expansion with a degree bound**: any polynomial of degree ≤ N
    is Σ_{k ≤ N} aₖ·Hₖ for real coefficients aₖ. -/
theorem exists_hermite_repr :
    ∀ (N : ℕ) (p : ℝ[X]), p.natDegree ≤ N →
      ∃ a : ℕ → ℝ, p = ∑ k ∈ Finset.range (N + 1), a k • H k := by
  intro N
  induction N with
  | zero =>
      intro p hp
      refine ⟨fun _ => p.coeff 0, ?_⟩
      simpa [smul_eq_C_mul] using eq_C_of_natDegree_le_zero hp
  | succ N ih =>
      intro p hp
      by_cases hdeg : p.natDegree ≤ N
      · obtain ⟨a, ha⟩ := ih p hdeg
        refine ⟨fun k => if k = N + 1 then 0 else a k, ?_⟩
        have hcong : ∀ k ∈ Finset.range (N + 1),
            (if k = N + 1 then (0 : ℝ) else a k) • H k = a k • H k := by
          intro k hk
          simp only [Finset.mem_range] at hk
          rw [if_neg (by omega : k ≠ N + 1)]
        rw [Finset.sum_range_succ, Finset.sum_congr rfl hcong, ← ha]
        simp
      · rw [not_le] at hdeg
        have hpdeg : p.natDegree = N + 1 := le_antisymm hp hdeg
        have hp0 : p ≠ 0 := by
          intro h
          rw [h, natDegree_zero] at hpdeg
          omega
        have hc0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
        have hdegq : (C p.leadingCoeff * H (N + 1)).degree = p.degree := by
          rw [degree_mul, degree_C hc0, degree_H, zero_add,
            degree_eq_natDegree hp0, hpdeg]
        have hlc : (C p.leadingCoeff * H (N + 1)).leadingCoeff = p.leadingCoeff := by
          rw [leadingCoeff_mul, leadingCoeff_C, (H_monic (N + 1)).leadingCoeff,
            mul_one]
        have hsub : (p - C p.leadingCoeff * H (N + 1)).natDegree ≤ N := by
          by_cases hz : p - C p.leadingCoeff * H (N + 1) = 0
          · simp [hz]
          · have hlt : (p - C p.leadingCoeff * H (N + 1)).degree < p.degree :=
              degree_sub_lt hdegq.symm hp0 hlc.symm
            have hnd := natDegree_lt_natDegree hz hlt
            omega
        obtain ⟨a, ha⟩ := ih _ hsub
        refine ⟨fun k => if k = N + 1 then p.leadingCoeff else a k, ?_⟩
        have hcong : ∀ k ∈ Finset.range (N + 1),
            (if k = N + 1 then p.leadingCoeff else a k) • H k = a k • H k := by
          intro k hk
          simp only [Finset.mem_range] at hk
          rw [if_neg (by omega : k ≠ N + 1)]
        rw [Finset.sum_range_succ, Finset.sum_congr rfl hcong, ← ha]
        simp [smul_eq_C_mul]

/-- Every real polynomial has a Hermite expansion. -/
theorem exists_hermite_repr' (p : ℝ[X]) :
    ∃ (N : ℕ) (a : ℕ → ℝ), p = ∑ k ∈ Finset.range (N + 1), a k • H k :=
  ⟨p.natDegree, (exists_hermite_repr p.natDegree p le_rfl).choose,
    (exists_hermite_repr p.natDegree p le_rfl).choose_spec⟩

/-! ## 4. What is NOT proven here

    This file currently contains NO analysis and NO measure theory, and
    therefore does not contain the Poincaré inequality or any part of it.
    The remaining stairs, in dependency order:

    1. **Gaussian integration by parts (Stein's identity)** for polynomials:
       ∫ x·f(x) dγ = ∫ f′(x) dγ. Requires an integration-by-parts theorem
       on the whole line plus decay of p(x)·e^{−x²/2} at ±∞.
    2. **L²(γ)-orthogonality** ∫ Hₘ·Hₙ dγ = n!·δₘₙ, by induction from
       Stein's identity and the recurrence. Mathlib has no Gaussian-L²
       theory of Hermite polynomials at all.
    3. **The variance identity** Var_γ(Σ aₖHₖ) = Σ_{k≥1} aₖ²·k!.
    4. **The Poincaré inequality** itself, which is then the index
       comparison k! ≤ k·k! for k ≥ 1 — i.e. all the difficulty is in
       stairs 1–3, none of it in the final step.
    5. Tensorisation to ℝ¹⁶ (the cascade's Herm₄(ℂ) ≅ ℝ¹⁶), which is what
       the tree actually needs.

    Until stair 4 exists, the published Bakry-Émery tags must NOT move on
    account of this file. -/

end GaussianPoincare
