import RealDivisionPure

/-!
# The pure part is closed under addition, so it is a subspace

`RealDivisionPure` proved half of Frobenius's leg (a) — every element is a real scalar plus a pure
one, and the two overlap only at `0` — and named the other half as the harder one: **the pure
elements are closed under addition**, without which they are a set and not a subspace.
`PROOF_STRATEGY` §6 question 3 says a rung is retried at once, so this is that half.

> **`mul_eq_zero_of_isPure_span`** — if `s • u + t • 1` is pure and `u` is pure and nonzero, then
> `s * t = 0`. **A pure element has no scalar part**, and this is the whole of the easy case.
>
> **`anticomm_scalar`** — for pure `u`, `v` with `1`, `u`, `v` independent, `u * v + v * u` is a
> real scalar. This is the content: apply the quadratic to `u + v` **and** to `u − v`, add, and the
> anticommutators cancel, leaving a relation among `u`, `v`, `1` whose coefficients independence
> kills.
>
> **`isPure_add`** — hence the sum of two pure elements is pure. The only hypothesis beyond the
> two being pure is `Module.Finite ℝ D`, and it is there because the proof calls
> `exists_quadratic`; the first draft of this bullet said *"no hypothesis beyond the two being
> pure"*, which was false, and it is corrected rather than left (`ERRATUM 94`).
>
> **`scalar_pure_unique`** — and the decomposition of `RealDivisionPure.exists_scalar_add_pure` is
> **unique**, which needed closure under subtraction and so could not be stated there.

## Why the two-quadratic trick is needed and a single one will not do

`(u + v)²` is `(c₁ + c₂) • 1 + (uv + vu)`, and the quadratic for `u + v` gives
`(u + v)² = −a • (u + v) − b • 1`. That alone leaves `uv + vu` equal to a scalar **plus `a •
(u+v)`** — no better than where it started. Running the same computation on `u − v` produces the
anticommutator with the opposite sign, so adding the two eliminates it and leaves a pure
relation among `u`, `v` and `1`. **The relation is what independence is for**, and it is the
only place independence is used.

## What is proved, and what this finishes

Together with `RealDivisionPure`, Frobenius's **leg (a) is complete**: the pure part is closed
under addition and under real scalars, and every element is **uniquely** a scalar plus a pure
element — `scalar_pure_unique`, proved here because the uniqueness half needs closure under
subtraction and `RealDivisionPure` did not have it. Legs (b) and (c) — the
negative-definite form on the pure part with the Clifford structure, and `dim V ∈ {0, 1, 3}` — are
**untouched, not attempted, and not costed** (`ERRATUM 194`, `ERRATUM 246`).

**No submodule object is constructed here.** The statement proved is closure under addition and
under real scalars (`RealDivisionPure.isPure_smul` is in this file, not that one); bundling those
into a `Submodule ℝ D` is a definition, not a theorem, and nothing consumes it yet.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RealDivisionPureAdd

open RealDivisionPure RealDivisionQuadratic

variable {D : Type*} [DivisionRing D] [Algebra ℝ D]

theorem smul_one_mul (t : ℝ) (x : D) : (t • (1 : D)) * x = t • x := by
  rw [smul_mul_assoc, one_mul]

theorem mul_smul_one (t : ℝ) (x : D) : x * (t • (1 : D)) = t • x := by
  rw [mul_smul_comm, mul_one]

/-- A nonzero pure element is not a real scalar. -/
theorem not_scalar_of_isPure {u : D} (hu : IsPure u) (hne : u ≠ 0) (t : ℝ) :
    u ≠ t • (1 : D) := by
  intro ht
  exact hne (by rw [ht, (isPure_scalar_iff t).mp (ht ▸ hu), zero_smul])

/-- A real multiple of a pure element is pure. -/
theorem isPure_smul {u : D} (hu : IsPure u) (t : ℝ) : IsPure (t • u) := by
  obtain ⟨c, hc, h⟩ := hu
  refine ⟨t * t * c, by nlinarith [mul_self_nonneg t], ?_⟩
  rw [smul_mul_assoc, mul_smul_comm, h, smul_smul, smul_smul]

/-- If a square is a real scalar and the element is not a scalar, the element is pure. -/
theorem isPure_of_sq_scalar {w : D} {c : ℝ} (h : w * w = c • (1 : D))
    (hns : ∀ t : ℝ, w ≠ t • (1 : D)) : IsPure w := by
  refine ⟨c, ?_, h⟩
  by_contra hc
  push Not at hc
  obtain ⟨t, ht⟩ := eq_scalar_of_sq_eq_nonneg (le_of_lt hc) h
  exact hns t ht

/-! **The two expansions are ring identities and are stated for an arbitrary ring.** The linter
reported `[Algebra ℝ D]` unused in both, and the response is the true generality rather than an
`omit` (`ERRATUM 274`, `ERRATUM 278`). Nothing about `ℝ`, a division ring or commutativity is
involved: `noncomm_ring` proves them because `u * v` and `v * u` are kept apart. -/
section RingIdentities

variable {R : Type*} [Ring R]

/-- The expansion of a square in a possibly noncommutative ring. -/
theorem sq_add (u v : R) : (u + v) * (u + v) = u * u + (u * v + v * u) + v * v := by
  noncomm_ring

/-- And with the anticommutator entering with the opposite sign, which is the whole trick below. -/
theorem sq_sub (u v : R) : (u - v) * (u - v) = u * u - (u * v + v * u) + v * v := by
  noncomm_ring

end RingIdentities

/-- **A pure element has no scalar part.** If `s • u + t • 1` is pure with `u` pure and nonzero
then `s * t = 0`: the cross term is `2st • u`, and a nonzero multiple of `u` cannot be a scalar. -/
theorem mul_eq_zero_of_isPure_span {u : D} (hu : IsPure u) (hne : u ≠ 0) {s t : ℝ}
    (hw : IsPure (s • u + t • (1 : D))) : s * t = 0 := by
  obtain ⟨c₁, _, hu2⟩ := hu
  obtain ⟨c, _, hw2⟩ := hw
  by_contra hst
  have hexp : (s • u + t • (1 : D)) * (s • u + t • (1 : D))
      = (s * s * c₁ + t * t) • (1 : D) + (2 * (s * t)) • u := by
    rw [sq_add, smul_mul_assoc, mul_smul_comm, hu2, smul_mul_assoc, mul_smul_comm,
      mul_smul_one, smul_one_mul, mul_one, smul_smul, smul_smul, smul_smul]
    match_scalars <;> ring
  rw [hw2] at hexp
  have hu_scalar : u = ((c - (s * s * c₁ + t * t)) / (2 * (s * t))) • (1 : D) := by
    have h2 : (2 * (s * t)) • u = (c - (s * s * c₁ + t * t)) • (1 : D) := by
      linear_combination (norm := module) -hexp
    have hne2 : (2 : ℝ) * (s * t) ≠ 0 := by
      simpa using hst
    calc u = ((2 * (s * t))⁻¹ * (2 * (s * t))) • u := by rw [inv_mul_cancel₀ hne2, one_smul]
      _ = (2 * (s * t))⁻¹ • ((2 * (s * t)) • u) := by rw [smul_smul]
      _ = (2 * (s * t))⁻¹ • ((c - (s * s * c₁ + t * t)) • (1 : D)) := by rw [h2]
      _ = ((c - (s * s * c₁ + t * t)) / (2 * (s * t))) • (1 : D) := by
            rw [smul_smul]; ring_nf
  exact not_scalar_of_isPure ⟨c₁, ‹c₁ ≤ 0›, hu2⟩ hne _ hu_scalar


/-- **The content.** For pure `u`, `v` with `1`, `u`, `v` independent, the anticommutator is a real
scalar. Apply the quadratic to `u + v` and to `u − v`: the anticommutator enters with opposite
signs, so adding the two eliminates it and leaves a relation among `u`, `v` and `1`, whose `u` and
`v` coefficients independence forces to zero. -/
theorem anticomm_scalar [Module.Finite ℝ D] {u v : D} (hu : IsPure u) (hv : IsPure v)
    (hind : ∀ α β γ : ℝ, α • u + β • v + γ • (1 : D) = 0 → α = 0 ∧ β = 0) :
    ∃ k : ℝ, u * v + v * u = k • (1 : D) := by
  obtain ⟨c₁, _, hu2⟩ := hu
  obtain ⟨c₂, _, hv2⟩ := hv
  obtain ⟨a, b, hx⟩ := exists_quadratic (u + v)
  obtain ⟨a', b', hy⟩ := exists_quadratic (u - v)
  rw [sq_add, hu2, hv2] at hx
  rw [sq_sub, hu2, hv2] at hy
  have hrel : (a + a') • u + (a - a') • v
      + (b + b' + (c₁ + c₁) + (c₂ + c₂)) • (1 : D) = 0 := by
    linear_combination (norm := module) hx + hy
  obtain ⟨h1, h2⟩ := hind _ _ _ hrel
  have ha : a = 0 := by linarith
  subst ha
  exact ⟨-(c₁ + c₂ + b), by linear_combination (norm := module) hx⟩

/-- **The pure part is closed under addition.** With `isPure_smul` this makes it an `ℝ`-subspace,
which is the second half of Frobenius's leg (a). -/
theorem isPure_add [Module.Finite ℝ D] {u v : D} (hu : IsPure u) (hv : IsPure v) :
    IsPure (u + v) := by
  rcases eq_or_ne u 0 with rfl | hune
  · simpa using hv
  rcases eq_or_ne v 0 with rfl | hvne
  · simpa using hu
  by_cases hdep : ∃ s t : ℝ, v = s • u + t • (1 : D)
  · obtain ⟨s, t, rfl⟩ := hdep
    rcases mul_eq_zero.mp (mul_eq_zero_of_isPure_span hu hune hv) with hs | ht
    · exfalso
      subst hs
      rw [zero_smul, zero_add] at hv hvne
      exact hvne (by rw [(isPure_scalar_iff t).mp hv, zero_smul])
    · subst ht
      rw [zero_smul, add_zero] at hv ⊢
      have hcollect : u + s • u = (1 + s) • u := by module
      rw [hcollect]
      exact isPure_smul hu (1 + s)
  · push Not at hdep
    have hind : ∀ α β γ : ℝ, α • u + β • v + γ • (1 : D) = 0 → α = 0 ∧ β = 0 := by
      intro α β γ h
      by_cases hb : β = 0
      · subst hb
        rw [zero_smul, add_zero] at h
        by_cases ha : α = 0
        · exact ⟨ha, rfl⟩
        · exfalso
          refine not_scalar_of_isPure hu hune (-γ / α) ?_
          have hα : (α : ℝ) ≠ 0 := ha
          calc u = (α⁻¹ * α) • u := by rw [inv_mul_cancel₀ hα, one_smul]
            _ = α⁻¹ • (α • u) := by rw [smul_smul]
            _ = α⁻¹ • (-(γ • (1 : D))) := by
                  rw [show α • u = -(γ • (1 : D)) by linear_combination (norm := module) h]
            _ = (-γ / α) • (1 : D) := by module
      · exact absurd (hdep (-α / β) (-γ / β)) (by
          push Not
          have hβ : (β : ℝ) ≠ 0 := hb
          calc v = (β⁻¹ * β) • v := by rw [inv_mul_cancel₀ hβ, one_smul]
            _ = β⁻¹ • (β • v) := by rw [smul_smul]
            _ = β⁻¹ • (-(α • u) - γ • (1 : D)) := by
                  rw [show β • v = -(α • u) - γ • (1 : D) by
                    linear_combination (norm := module) h]
            _ = (-α / β) • u + (-γ / β) • (1 : D) := by
                  rw [smul_sub, smul_neg, smul_smul, smul_smul]; module)
    obtain ⟨k, hk⟩ := anticomm_scalar hu hv hind
    obtain ⟨c₁, _, hu2⟩ := hu
    obtain ⟨c₂, _, hv2⟩ := hv
    refine isPure_of_sq_scalar (c := c₁ + c₂ + k) ?_ ?_
    · rw [sq_add, hu2, hv2, hk]; module
    · intro t ht
      exact one_ne_zero (hind 1 1 (-t) (by
        rw [one_smul, one_smul, neg_smul, ht]; abel)).1


/-- Closure under negation, which is `isPure_smul` at `-1`. -/
theorem isPure_neg {u : D} (hu : IsPure u) : IsPure (-u) := by
  have h : -u = (-1 : ℝ) • u := by module
  rw [h]
  exact isPure_smul hu (-1)

/-- Closure under subtraction. -/
theorem isPure_sub [Module.Finite ℝ D] {u v : D} (hu : IsPure u) (hv : IsPure v) :
    IsPure (u - v) := by
  have h : u - v = u + -v := by abel
  rw [h]
  exact isPure_add hu (isPure_neg hv)

/-- **The decomposition is unique.** `RealDivisionPure.exists_scalar_add_pure` gives existence and
could not give this: subtracting two decompositions produces a difference of pure elements, which
is pure only once the part is closed under subtraction. -/
theorem scalar_pure_unique [Module.Finite ℝ D] {r r' : ℝ} {v v' : D} (hv : IsPure v)
    (hv' : IsPure v') (h : r • (1 : D) + v = r' • (1 : D) + v') : r = r' ∧ v = v' := by
  have hdiff : (r - r') • (1 : D) = v' - v := by
    rw [sub_smul]
    linear_combination (norm := module) h
  have hpure : IsPure ((r - r') • (1 : D)) := by
    rw [hdiff]
    exact isPure_sub hv' hv
  have hzero : r - r' = 0 := (isPure_scalar_iff (r - r')).mp hpure
  refine ⟨by linarith, ?_⟩
  have : v' - v = 0 := by rw [← hdiff, hzero, zero_smul]
  exact (sub_eq_zero.mp this).symm

end RealDivisionPureAdd
