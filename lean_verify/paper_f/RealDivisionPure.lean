import RealDivisionQuadratic

/-!
# The pure part: every element is a real scalar plus one whose square is `≤ 0`

`RealDivisionQuadratic` is rung one of Frobenius's theorem and names its own next leg: *the pure
part `V = {d | d * d = b • 1 with b ≤ 0}` is an `ℝ`-subspace and `D = ℝ ∙ 1 ⊕ V`*.
`PROOF_STRATEGY` §6 question 3 says a rung is retried immediately rather than banked, so this is
that leg — **and it is the half of it that does not need `V` to be closed under addition.**

> **`discrim_lt_of_not_scalar`** — if `d` is not a real scalar, then **every** real quadratic
> annihilating it has negative discriminant. This is where the division ring is used and it is the
> only place: a non-negative discriminant factors the quadratic over `ℝ`, and `(d - r₁)(d - r₂) = 0`
> in a ring with no zero divisors forces `d` to be one of the roots.
>
> **`isPure_add_half`** — hence completing the square lands in the pure part: `(d + (a/2) • 1)²` is
> `((a² − 4b)/4) • 1`, and that coefficient is negative.
>
> **`exists_scalar_add_pure`** — **every** element is `r • 1 + v` with `v` pure. The scalars are
> the case `v = 0`; everything else completes the square.
>
> **`isPure_scalar_iff`** — and the sum is direct at the element level: a real scalar is pure only
> if it is `0`, because `r² ≤ 0` and `r² ≥ 0`.

## What is proved and what is left of this leg

**`D = ℝ ∙ 1 + V` as a statement about elements, and `ℝ ∙ 1 ∩ V = 0`.** What is **not** here is that
`V` is closed under addition, which is what would make `V` a submodule and the sum a direct sum of
subspaces. That is a genuinely different argument — for `u, v` pure one shows `uv + vu` is a real
scalar, by applying the quadratic to `u + v` and to `u − v` and using that `1, u, v` are
independent when they are — **and it is not attempted here; no cost is claimed** (`ERRATUM 194`,
`ERRATUM 246`).

**So Frobenius's leg (a) is half done and the half that is done is the half rung one was for.**
The remaining ladder is unchanged: `V` a subspace, then the negative-definite form on it, then
`dim V ∈ {0, 1, 3}`.

## One thing this file does NOT assume

**Nothing here needs `d` to generate a commutative subalgebra**, and nothing here says the
decomposition is unique as a *function* of `d` — `exists_scalar_add_pure` is an existential.
Uniqueness follows from `isPure_scalar_iff` once `V` is a subspace and not before, because
subtracting two decompositions produces a difference of two pure elements.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionPure

open RealDivisionQuadratic

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]

/-! **`Module.Finite` sits on ONE theorem in this file, not on the section.** Only
`exists_scalar_add_pure` needs it, and only because it calls `RealDivisionQuadratic
.exists_quadratic`; everything else here is algebra in a division ring and would carry the
hypothesis for nothing. The linter said so and the response is to state the true generality rather
than `omit` the binder — `ERRATUM 274`, `ERRATUM 278`, and the same move
`TraceMomentsSpectrum.exists_fin_map` made earlier today. -/

/-- The pure part: elements whose square is a non-positive real scalar. -/
def IsPure (d : D) : Prop := ∃ c : ℝ, c ≤ 0 ∧ d * d = c • (1 : D)

theorem isPure_zero : IsPure (0 : D) := ⟨0, le_refl 0, by simp⟩

/-- Completing the square, as an identity: if `d * d + a • d + b • 1 = 0` then
`(d + (a/2) • 1)² = ((a² − 4b)/4) • 1`. Everything else in this file reads off this one line. -/
theorem sq_add_half {d : D} {a b : ℝ} (h : d * d + a • d + b • (1 : D) = 0) :
    (d + (a / 2) • (1 : D)) * (d + (a / 2) • (1 : D)) = ((a ^ 2 - 4 * b) / 4) • (1 : D) := by
  have h1 : d * ((a / 2) • (1 : D)) = (a / 2) • d := by rw [mul_smul_comm, mul_one]
  have h2 : ((a / 2) • (1 : D)) * d = (a / 2) • d := by rw [smul_mul_assoc, one_mul]
  have h3 : ((a / 2) • (1 : D)) * ((a / 2) • (1 : D)) = ((a / 2) * (a / 2)) • (1 : D) := by
    rw [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
  have hdd : d * d = -(a • d) - b • (1 : D) := by
    linear_combination (norm := module) h
  rw [add_mul, mul_add, mul_add, h1, h2, h3, hdd]
  match_scalars <;> ring

/-- **Where the division ring is used, and the only place it is.** If a square is a non-negative
real scalar, the element is a real scalar: `(u − √c)(u + √c) = 0` and there are no zero divisors.
Stated for an abstract `u` rather than inline, because `set` on `d + (a/2) • 1` lets `mul_add`
rewrite the wrong occurrence — the first draft did exactly that. -/
theorem eq_scalar_of_sq_eq_nonneg {u : D} {c : ℝ} (hc : 0 ≤ c) (hu : u * u = c • (1 : D)) :
    ∃ t : ℝ, u = t • (1 : D) := by
  have hs2 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
  have e1 : u * (Real.sqrt c • (1 : D)) = Real.sqrt c • u := by rw [mul_smul_comm, mul_one]
  have e2 : (Real.sqrt c • (1 : D)) * u = Real.sqrt c • u := by rw [smul_mul_assoc, one_mul]
  have e3 : (Real.sqrt c • (1 : D)) * (Real.sqrt c • (1 : D))
      = (Real.sqrt c * Real.sqrt c) • (1 : D) := by
    rw [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
  have hfac : (u - Real.sqrt c • (1 : D)) * (u + Real.sqrt c • (1 : D)) = 0 := by
    rw [sub_mul, mul_add, mul_add, e1, e2, e3, hu, hs2]
    module
  rcases mul_eq_zero.mp hfac with h₁ | h₂
  · exact ⟨Real.sqrt c, sub_eq_zero.mp h₁⟩
  · exact ⟨-Real.sqrt c, by rw [add_eq_zero_iff_eq_neg.mp h₂, neg_smul]⟩

/-- **Hence a non-scalar has negative discriminant**, for every real quadratic that annihilates it.
-/
theorem discrim_lt_of_not_scalar {d : D} (hd : ∀ r : ℝ, d ≠ r • (1 : D)) {a b : ℝ}
    (h : d * d + a • d + b • (1 : D) = 0) : a ^ 2 < 4 * b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht⟩ := eq_scalar_of_sq_eq_nonneg (c := (a ^ 2 - 4 * b) / 4) (by linarith)
    (sq_add_half h)
  refine hd (t - a / 2) ?_
  have : d = t • (1 : D) - (a / 2) • (1 : D) := by rw [← ht]; abel
  rw [this, sub_smul]

/-- **Completing the square lands in the pure part.** -/
theorem isPure_add_half {d : D} (hd : ∀ r : ℝ, d ≠ r • (1 : D)) {a b : ℝ}
    (h : d * d + a • d + b • (1 : D) = 0) : IsPure (d + (a / 2) • (1 : D)) :=
  ⟨(a ^ 2 - 4 * b) / 4, by
    have := discrim_lt_of_not_scalar hd h
    linarith, sq_add_half h⟩

/-- **Every element is a real scalar plus a pure element.** The scalars are the case `v = 0`;
everything else completes the square. -/
theorem exists_scalar_add_pure [Module.Finite ℝ D] (d : D) :
    ∃ (r : ℝ) (v : D), IsPure v ∧ d = r • (1 : D) + v := by
  by_cases hd : ∃ r : ℝ, d = r • (1 : D)
  · obtain ⟨r, hr⟩ := hd
    exact ⟨r, 0, isPure_zero, by rw [hr, add_zero]⟩
  · push Not at hd
    obtain ⟨a, b, h⟩ := exists_quadratic d
    refine ⟨-(a / 2), d + (a / 2) • (1 : D), isPure_add_half hd h, ?_⟩
    rw [neg_smul]
    abel

/-- **And the sum is direct at the element level**: a real scalar is pure only if it is zero. -/
theorem isPure_scalar_iff (r : ℝ) : IsPure (r • (1 : D)) ↔ r = 0 := by
  constructor
  · rintro ⟨c, hc, hsq⟩
    have hinj : Function.Injective (algebraMap ℝ D) := (algebraMap ℝ D).injective
    have h1 : (r • (1 : D)) * (r • (1 : D)) = (r * r) • (1 : D) := by
      rw [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
    have h2 : (r * r) • (1 : D) = c • (1 : D) := by rw [← h1, hsq]
    have h3 : r * r = c := by
      have := h2
      rw [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at this
      exact hinj this
    nlinarith [mul_self_nonneg r]
  · rintro rfl
    simpa using isPure_zero

end RealDivisionPure
