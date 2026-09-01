import RealDivisionPureAdd

/-!
# The form on the pure part is negative definite, and orthogonal pure elements multiply to pure ones

`RealDivisionPureAdd` finished Frobenius's leg (a) and named leg (b): *the pure part carries a
negative-definite quadratic form and the multiplication makes `D` a quotient of a Clifford
algebra*. `PROOF_STRATEGY` §6 question 3 says a rung is retried at once. This is leg (b)'s
content, stated as theorems about elements rather than as a `QuadraticForm` object.

> **`sq_scalar_unique`** — the real scalar a square equals is unique, so *the* square of a pure
> element is well defined and the polarisation identity below says something.
>
> **`anticomm_scalar_of_isPure`** — `u * v + v * u` is a real scalar for **any** two pure elements.
> `RealDivisionPureAdd.anticomm_scalar` needed `1`, `u`, `v` independent; that hypothesis is
> removed here, which is what a bilinear form needs and what `PROOF_STRATEGY` §7 rule 3 asks for.
>
> **`sq_neg_of_ne_zero`** — a **nonzero** pure element has a **strictly** negative square. That is
> the *definite* in negative definite, and it is where the division ring enters: `u * u = 0` forces
> `u = 0`.
>
> **`polarisation`** — `c₃ = c₁ + c₂ + k`, tying the square of `u + v` to the squares of `u` and
> `v` and the anticommutator. With the sign convention `⟪u,v⟫ = −k/2` this is the parallelogram law.
>
> **`anticomm_add_left`**, **`anticomm_smul_left`**, **`anticomm_comm`** — the form is **bilinear**
> and symmetric. Without these "form" would be a word for a function whose values happen to be
> real, which is all the first draft of this file proved.
>
> **`sq_mul_of_anticomm`** — **the Clifford relation, as an identity**: anticommuting elements
> whose squares are real scalars have `(uv)² = −c₁c₂`. Purity is not needed and is not assumed.
>
> **`isPure_mul_of_anticomm`** — and with purity, so with `c₁ ≤ 0` and `c₂ ≤ 0`, the product is
> itself pure. This is the fact leg (c) runs on.

## What is not built, and it is a definition rather than a theorem

**No `QuadraticForm ℝ V` and no `Submodule` are constructed.** Both are packaging: the pure part
would have to be bundled as a submodule first (`RealDivisionPureAdd` proves the closure properties
and deliberately does not bundle them), and the form would then be `fun u => −(the scalar)`, whose
definition needs `Classical.choose` on `IsPure`. Nothing consumes either yet, and building an object
no theorem needs is what `ERRATUM 201` is about in the other direction.

**Leg (c) is untouched**: that `dim V ∈ {0, 1, 3}`, and hence that `D` is `ℝ`, `ℂ` or `ℍ`, does not
follow from anything here. Not attempted, not costed (`ERRATUM 194`, `ERRATUM 246`).

**And the Clifford statement is the RELATION, not the algebra.** Nothing here constructs a map from
a Clifford algebra to `D` or shows one is surjective; what is proved is the identity that such a map
would need. Calling this "`D` is a quotient of a Clifford algebra" would be the overclaim.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionPureForm

open RealDivisionPure RealDivisionPureAdd RealDivisionQuadratic

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]

/-- The scalar a square equals is unique, since `algebraMap ℝ D` is injective. -/
theorem sq_scalar_unique {w : D} {c c' : ℝ} (h : w * w = c • (1 : D))
    (h' : w * w = c' • (1 : D)) : c = c' := by
  have : (algebraMap ℝ D) c = (algebraMap ℝ D) c' := by
    have hc : c • (1 : D) = c' • (1 : D) := by rw [← h, h']
    rwa [Algebra.smul_def, Algebra.smul_def, mul_one, mul_one] at hc
  exact (algebraMap ℝ D).injective this

/-- **A nonzero pure element has a strictly negative square**, which is where the division ring
enters: a zero square would make the element zero. -/
theorem sq_neg_of_ne_zero {u : D} (hu : IsPure u) (hne : u ≠ 0) {c : ℝ}
    (h : u * u = c • (1 : D)) : c < 0 := by
  obtain ⟨c₀, hc₀, h₀⟩ := hu
  have hcc : c = c₀ := sq_scalar_unique h h₀
  subst hcc
  rcases lt_or_eq_of_le hc₀ with hlt | heq
  · exact hlt
  · exact absurd (mul_self_eq_zero.mp (by rw [h, heq, zero_smul])) hne

/-- **The anticommutator of two pure elements is a real scalar, with no independence hypothesis.**
`RealDivisionPureAdd.anticomm_scalar` needs `1`, `u`, `v` independent; the dependent case is
`v = s • u`, where the anticommutator is `2s` times the square. -/
theorem anticomm_scalar_of_isPure [Module.Finite ℝ D] {u v : D} (hu : IsPure u) (hv : IsPure v) :
    ∃ k : ℝ, u * v + v * u = k • (1 : D) := by
  rcases eq_or_ne u 0 with rfl | hune
  · exact ⟨0, by simp⟩
  by_cases hdep : ∃ s t : ℝ, v = s • u + t • (1 : D)
  · obtain ⟨s, t, rfl⟩ := hdep
    obtain ⟨c₁, _, hu2⟩ := hu
    have ht : t = 0 := by
      rcases mul_eq_zero.mp (mul_eq_zero_of_isPure_span ⟨c₁, ‹c₁ ≤ 0›, hu2⟩ hune hv) with hs | ht
      · subst hs
        rw [zero_smul, zero_add] at hv
        exact (isPure_scalar_iff t).mp hv
      · exact ht
    subst ht
    refine ⟨2 * s * c₁, ?_⟩
    rw [zero_smul, add_zero, mul_smul_comm, smul_mul_assoc, hu2]
    module
  · push Not at hdep
    refine anticomm_scalar hu hv ?_
    intro α β γ h
    by_cases hb : β = 0
    · subst hb
      rw [zero_smul, add_zero] at h
      by_cases ha : α = 0
      · exact ⟨ha, rfl⟩
      · exact absurd (show u = (-γ / α) • (1 : D) by
          calc u = (α⁻¹ * α) • u := by rw [inv_mul_cancel₀ ha, one_smul]
            _ = α⁻¹ • (α • u) := by rw [smul_smul]
            _ = α⁻¹ • (-(γ • (1 : D))) := by
                  rw [show α • u = -(γ • (1 : D)) by linear_combination (norm := module) h]
            _ = (-γ / α) • (1 : D) := by module)
          (not_scalar_of_isPure hu hune _)
    · exact absurd (hdep (-α / β) (-γ / β)) (by
        push Not
        calc v = (β⁻¹ * β) • v := by rw [inv_mul_cancel₀ hb, one_smul]
          _ = β⁻¹ • (β • v) := by rw [smul_smul]
          _ = β⁻¹ • (-(α • u) - γ • (1 : D)) := by
                rw [show β • v = -(α • u) - γ • (1 : D) by linear_combination (norm := module) h]
          _ = (-α / β) • u + (-γ / β) • (1 : D) := by
                rw [smul_sub, smul_neg, smul_smul, smul_smul]; module)

/-- **Polarisation.** The square of a sum is the sum of the squares plus the anticommutator, read
as an identity between the three real scalars. -/
theorem polarisation {u v : D} {c₁ c₂ c₃ k : ℝ} (hu : u * u = c₁ • (1 : D))
    (hv : v * v = c₂ • (1 : D)) (huv : (u + v) * (u + v) = c₃ • (1 : D))
    (hk : u * v + v * u = k • (1 : D)) : c₃ = c₁ + c₂ + k := by
  refine sq_scalar_unique huv ?_
  rw [sq_add, hu, hv, hk]
  module


/-! ## The form is bilinear

Additivity and homogeneity in the first argument; the anticommutator is visibly symmetric, so the
second argument follows. **These are what make "form" the right word**, and the first draft of this
file asserted a form existed while proving only that its values are real — the gap is closed by
proving rather than by fencing. Both are ring identities plus `sq_scalar_unique`-style rigidity;
neither needs purity, and neither is stated with it. -/

theorem anticomm_add_left {u w v : D} {k₁ k₂ : ℝ} (h₁ : u * v + v * u = k₁ • (1 : D))
    (h₂ : w * v + v * w = k₂ • (1 : D)) :
    (u + w) * v + v * (u + w) = (k₁ + k₂) • (1 : D) := by
  have hexp : (u + w) * v + v * (u + w) = (u * v + v * u) + (w * v + v * w) := by noncomm_ring
  rw [hexp, h₁, h₂, add_smul]

theorem anticomm_smul_left {u v : D} {k : ℝ} (h : u * v + v * u = k • (1 : D)) (t : ℝ) :
    (t • u) * v + v * (t • u) = (t * k) • (1 : D) := by
  have hexp : (t • u) * v + v * (t • u) = t • (u * v + v * u) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_add]
  rw [hexp, h, smul_smul]

/-- Symmetry, which is `add_comm` and is stated so the word "bilinear" above is not carried by
three of its four clauses. **Over an arbitrary ring**: the linter reported `[Algebra ℝ D]` unused
and this is the true generality (`ERRATUM 274`, `ERRATUM 278`). -/
theorem anticomm_comm {R : Type*} [Ring R] (u v : R) : u * v + v * u = v * u + u * v :=
  add_comm _ _

/-- **The Clifford relation, as an identity.** If `u` and `v` anticommute and both squares are
real scalars then `(uv)² = −c₁c₂`. **Purity is not needed for this and is not assumed**: the first
draft carried `IsPure u` and `IsPure v` here, the linter reported both unused, and the response is
the true generality rather than an `omit` (`ERRATUM 274`, `ERRATUM 278`). Purity enters only in the
corollary below, and only to fix the sign. -/
theorem sq_mul_of_anticomm {u v : D} (h : u * v + v * u = 0) {c₁ c₂ : ℝ}
    (h₁ : u * u = c₁ • (1 : D)) (h₂ : v * v = c₂ • (1 : D)) :
    (u * v) * (u * v) = (-(c₁ * c₂)) • (1 : D) := by
  have hvu : v * u = -(u * v) := by linear_combination (norm := noncomm_ring) h
  calc (u * v) * (u * v) = u * (v * u) * v := by noncomm_ring
    _ = u * (-(u * v)) * v := by rw [hvu]
    _ = -((u * u) * (v * v)) := by noncomm_ring
    _ = -((c₁ • (1 : D)) * (c₂ • (1 : D))) := by rw [h₁, h₂]
    _ = (-(c₁ * c₂)) • (1 : D) := by
          rw [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul, ← neg_smul]


/-- **And the product is pure**, which is what leg (c) runs on: `c₁ ≤ 0` and `c₂ ≤ 0` make
`−c₁c₂ ≤ 0`. The first draft gave this theorem's NAME to the identity above, whose conclusion is a
square and not a purity statement; the name now sits on the statement it describes. -/
theorem isPure_mul_of_anticomm {u v : D} (hu : IsPure u) (hv : IsPure v)
    (h : u * v + v * u = 0) : IsPure (u * v) := by
  obtain ⟨c₁, hc₁, h₁⟩ := hu
  obtain ⟨c₂, hc₂, h₂⟩ := hv
  exact ⟨-(c₁ * c₂), by nlinarith, sq_mul_of_anticomm h h₁ h₂⟩

end RealDivisionPureForm
