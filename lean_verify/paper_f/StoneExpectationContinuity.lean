/-
  StoneExpectationContinuity: **Stone's converse from EXPECTATION VALUES**, which is the
  hypothesis an experiment actually delivers.

  Three units have now weakened the hypothesis of Stone's converse on a finite-dimensional
  carrier, each time to something a reader is more likely to have:
  * `StoneConverseCarriers` — continuity of `t ↦ U t` in the OPERATOR NORM;
  * `StoneStrongContinuity` (unit 64) — continuity of every ORBIT `t ↦ U t ψ`;
  * `StoneWeakContinuity` (unit 65) — continuity of `t ↦ φ (U t)` for every continuous
    FUNCTIONAL `φ`.
  **This file is the fourth and lowest rung: continuity of the numbers `t ↦ ⟪U t χ, χ⟫`**, one
  for each vector `χ`. Those are expectation values. They are what a measurement returns, and
  they are a strictly smaller family of tests than any of the three above.

  THE CONTENT IS POLARISATION, AND THAT IS THE WHOLE IDEA. `inner_map_polarization` writes
  `⟪T y, x⟫` as a fixed ℂ-combination of four DIAGONAL values `⟪T χ, χ⟫`, for any ℂ-linear `T`
  and with no self-adjointness. So continuity of the diagonal gives continuity of every matrix
  entry; an orthonormal basis rebuilds `U t y` from its entries; and unit 64's theorem turns the
  orbits into the operator norm. `ext_inner_map` is the algebraic shadow of the same fact — the
  diagonal expectation values determine the operator outright.

  WHAT KIND OF DEEPENING THIS IS, AND IT IS THE THIRD TIME THE ANSWER IS THE SAME. The hypothesis
  is weakened in FORM and EQUIVALENT in substance: `continuousAt_iff_expectation` closes the
  ladder, so on a finite-dimensional carrier **norm, orbitwise, weak and expectation continuity
  are one condition**, and no evolution is newly reached. Saying it three times is not padding —
  it is the honest report, because "weaker hypothesis" reads as "more general theorem" and here
  it never is. What the four rungs buy is that whichever form a reader has, the estate has a
  theorem that takes it, and the conversions are objects rather than remarks in headers.

  WHAT IS PROVED.
  * **`entry_continuousAt_of_expectation`** — expectation continuity gives continuity of
    `t ↦ ⟪f t y, x⟫` for every pair, by polarisation.
  * **`orbit_continuousAt_of_expectation`** — and hence of every orbit, by rebuilding the vector
    from its coordinates against `stdOrthonormalBasis`.
  * **`continuousAt_of_expectation`**, **`expectation_of_continuousAt`**,
    **`continuousAt_iff_expectation`** — the biconditional, and with it the four-rung collapse
    `expectation_iff_orbit` and `expectation_iff_weak`.
  * **`exists_unique_global_generator_of_expectation`**, **`eq_unitaryGroup_iff_expectation`**,
    **`schrodinger_of_expectation`** — Stone's converse, its characterisation, and `dψ/dt = iHψ`
    along every orbit, on any finite-dimensional complex inner-product space, from the group law
    and continuity of the EXPECTATION VALUES at the single point `0`.
  * **`euclidean_*_of_expectation`** — the same at `ℂⁿ`, carrying no instance hypotheses.

  WHAT THIS DOES AND DOES NOT DO TO UNIT 65'S NAMED RESIDUE. That residue is the STATE form on a
  general finite-dimensional C⋆-algebra, where a state is a positive unital FUNCTIONAL and the
  obstruction was that the pinned Mathlib has no state-space API. **This file closes the case
  that matters physically and does not close that residue.** Here the carrier is an operator
  algebra on a Hilbert space, the tests are the concrete VECTOR states `T ↦ ⟪T χ, χ⟫`, and no
  state-space API is needed because polarisation is available. On an abstract C⋆-algebra there
  are no vectors to polarise with, so the residue stands exactly as written, and it stands
  narrower: what is missing is the abstract case, not the operator one.

  WHAT IS **NOT** PROVED.
  * **Nothing about infinite dimension**, where the generator is unbounded; and no counterexample
    is built, unchanged from units 64 and 65.
  * **Nothing about the generator's spectrum, the Born rule, Gleason or Wigner.** In particular
    an expectation value is not the Born rule: nothing here says `|⟪ψ, φ⟫|²` is a probability.
  * **No claim that expectation continuity is physically minimal.** A measurement returns finitely
    many expectation values at finitely many times, not a continuous family; this file weakens the
    mathematics, not the idealisation.

  0 sorry. 0 new axioms. All declarations on `[propext, Classical.choice, Quot.sound]`.
-/

import StoneWeakContinuity

namespace StoneExpectationContinuity

open scoped ComplexOrder

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## 1. Polarisation: the diagonal determines the entries -/

/-- **THE CONTENT.** `inner_map_polarization` writes `⟪T y, x⟫` as a fixed ℂ-combination of four
diagonal values, for any ℂ-linear `T` and with no self-adjointness, so continuity of the
expectation values is continuity of every entry. -/
theorem entry_continuousAt_of_expectation (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ)
    (he : ∀ χ : E, ContinuousAt (fun t => (inner ℂ (f t χ) χ : ℂ)) t₀) (x y : E) :
    ContinuousAt (fun t => (inner ℂ (f t y) x : ℂ)) t₀ := by
  have key : ∀ t, (inner ℂ (f t y) x : ℂ)
      = ((inner ℂ (f t (x + y)) (x + y) : ℂ) - (inner ℂ (f t (x - y)) (x - y) : ℂ)
          + Complex.I * (inner ℂ (f t (x + Complex.I • y)) (x + Complex.I • y) : ℂ)
          - Complex.I * (inner ℂ (f t (x - Complex.I • y)) (x - Complex.I • y) : ℂ)) / 4 :=
    fun t => inner_map_polarization ((f t : E →L[ℂ] E) : E →ₗ[ℂ] E) x y
  have h1 := he (x + y)
  have h2 := he (x - y)
  have h3 := he (x + Complex.I • y)
  have h4 := he (x - Complex.I • y)
  have hcomb : ContinuousAt (fun t =>
      ((inner ℂ (f t (x + y)) (x + y) : ℂ) - (inner ℂ (f t (x - y)) (x - y) : ℂ)
        + Complex.I * (inner ℂ (f t (x + Complex.I • y)) (x + Complex.I • y) : ℂ)
        - Complex.I * (inner ℂ (f t (x - Complex.I • y)) (x - Complex.I • y) : ℂ)) / 4) t₀ :=
    (((h1.sub h2).add (continuousAt_const.mul h3)).sub (continuousAt_const.mul h4)).div_const 4
  simpa only [key] using hcomb

/-- **And the orbits follow**, because an orthonormal basis rebuilds the vector from the entries
that the previous theorem just made continuous. -/
theorem orbit_continuousAt_of_expectation [FiniteDimensional ℂ E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ)
    (he : ∀ χ : E, ContinuousAt (fun t => (inner ℂ (f t χ) χ : ℂ)) t₀) (y : E) :
    ContinuousAt (fun t => f t y) t₀ := by
  classical
  set b := stdOrthonormalBasis ℂ E with hb
  have hcoef : ∀ i, ContinuousAt (fun t => (inner ℂ (b i) (f t y) : ℂ)) t₀ := by
    intro i
    have h := entry_continuousAt_of_expectation f t₀ he (b i) y
    have hconj : ∀ t, (inner ℂ (b i) (f t y) : ℂ)
        = (starRingEnd ℂ) (inner ℂ (f t y) (b i) : ℂ) := fun t => (inner_conj_symm _ _).symm
    simpa only [hconj] using (Complex.continuous_conj.continuousAt).comp h
  have hsum := tendsto_finset_sum Finset.univ fun i (_ : i ∈ Finset.univ) =>
    (hcoef i).smul (continuousAt_const : ContinuousAt (fun _ : ℝ => b i) t₀)
  simpa [ContinuousAt, b.sum_repr'] using hsum

/-- **Expectation continuity is norm continuity in finite dimension**, through unit 64. -/
theorem continuousAt_of_expectation [FiniteDimensional ℂ E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ)
    (he : ∀ χ : E, ContinuousAt (fun t => (inner ℂ (f t χ) χ : ℂ)) t₀) : ContinuousAt f t₀ :=
  StoneStrongContinuity.continuousAt_of_pointwise f t₀
    (orbit_continuousAt_of_expectation f t₀ he)

/-- The easy direction, with no finite-dimensionality: evaluation and the inner product are
continuous. -/
theorem expectation_of_continuousAt (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ) (hc : ContinuousAt f t₀)
    (χ : E) : ContinuousAt (fun t => (inner ℂ (f t χ) χ : ℂ)) t₀ :=
  ((StoneStrongContinuity.pointwise_of_continuousAt f t₀ hc χ).inner continuousAt_const)

/-- **The biconditional.** -/
theorem continuousAt_iff_expectation [FiniteDimensional ℂ E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ) :
    ContinuousAt f t₀ ↔ ∀ χ : E, ContinuousAt (fun t => (inner ℂ (f t χ) χ : ℂ)) t₀ :=
  ⟨fun hc χ => expectation_of_continuousAt f t₀ hc χ, continuousAt_of_expectation f t₀⟩

/-! ## 2. Stone's converse from expectation values -/

section Converse

variable [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Continuity into `unitary (E →L[ℂ] E)` from the expectation values. -/
theorem continuousAt_unitary_of_expectation (U : ℝ → unitary (E →L[ℂ] E)) (t₀ : ℝ)
    (he : ∀ χ : E, ContinuousAt (fun t => (inner ℂ ((U t : E →L[ℂ] E) χ) χ : ℂ)) t₀) :
    ContinuousAt U t₀ :=
  StoneStrongContinuity.continuousAt_unitary_of_coe U t₀
    (continuousAt_of_expectation (fun t => ((U t : E →L[ℂ] E))) t₀ he)

set_option synthInstance.maxHeartbeats 400000 in
-- `HSMul ℝ (selfAdjoint (E →L[ℂ] E))` needs more than the 20000 default (`ERRATUM 594`).
/-- **STONE'S CONVERSE FROM EXPECTATION VALUES.** The group law, and the continuity at `0` of the
numbers a measurement returns, produce a unique self-adjoint generator. -/
theorem exists_unique_global_generator_of_expectation (U : ℝ → unitary (E →L[ℂ] E))
    (he : ∀ χ : E, ContinuousAt (fun t => (inner ℂ ((U t : E →L[ℂ] E) χ) χ : ℂ)) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (E →L[ℂ] E), ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseCarriers.operator_exists_unique_generator U
    (continuousAt_unitary_of_expectation U 0 he) hgrp

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **And the characterisation**, so the weakened hypothesis is forced rather than merely
sufficient. -/
theorem eq_unitaryGroup_iff_expectation (U : ℝ → unitary (E →L[ℂ] E)) :
    ((∀ χ : E, ContinuousAt (fun t => (inner ℂ ((U t : E →L[ℂ] E) χ) χ : ℂ)) 0) ∧
        ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint (E →L[ℂ] E), U = FiniteStone.unitaryGroup H := by
  rw [← StoneConverseCarriers.operator_eq_unitaryGroup_iff U]
  refine and_congr_left' ⟨fun he => continuousAt_unitary_of_expectation U 0 he, fun hc χ => ?_⟩
  exact expectation_of_continuousAt _ 0 (continuousAt_subtype_val.comp hc) χ

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **THE SCHRÖDINGER EQUATION FROM EXPECTATION VALUES.** No generator supplied, no norm and no
orbit continuity assumed — only the expectation values at one instant, and the group law. -/
theorem schrodinger_of_expectation (U : ℝ → unitary (E →L[ℂ] E))
    (he : ∀ χ : E, ContinuousAt (fun t => (inner ℂ ((U t : E →L[ℂ] E) χ) χ : ℂ)) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint (E →L[ℂ] E), (∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H)) ∧
      ∀ (ψ : E) (t : ℝ),
        HasDerivAt (fun s => ((U s : E →L[ℂ] E)) ψ)
          ((Complex.I • (H : E →L[ℂ] E) * ((U t : E →L[ℂ] E))) ψ) t :=
  StoneConverseCarriers.operator_schrodinger U
    (continuousAt_unitary_of_expectation U 0 he) hgrp

end Converse

/-! ## 3. At `ℂⁿ`, with no instance hypotheses to carry -/

section Euclidean

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **At `ℂⁿ`.** -/
theorem euclidean_exists_unique_generator_of_expectation
    (U : ℝ → unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (he : ∀ χ : EuclideanSpace ℂ (Fin n),
      ContinuousAt (fun t => (inner ℂ
        ((U t : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) χ) χ : ℂ)) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  exists_unique_global_generator_of_expectation U he hgrp

set_option synthInstance.maxHeartbeats 400000 in
-- Same shortfall (`ERRATUM 594`).
/-- **And the Schrödinger equation at `ℂⁿ`, from expectation values alone.** -/
theorem euclidean_schrodinger_of_expectation
    (U : ℝ → unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (he : ∀ χ : EuclideanSpace ℂ (Fin n),
      ContinuousAt (fun t => (inner ℂ
        ((U t : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) χ) χ : ℂ)) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃ H : selfAdjoint (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
      (∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H)) ∧
      ∀ (ψ : EuclideanSpace ℂ (Fin n)) (t : ℝ),
        HasDerivAt
          (fun s => ((U s : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))) ψ)
          ((Complex.I • (H : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
            * ((U t : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))) ψ) t :=
  schrodinger_of_expectation U he hgrp

end Euclidean

/-! ## 4. The ladder collapses -/

/-- **FOUR RUNGS, ONE CONDITION.** Expectation continuity is orbit continuity. -/
theorem expectation_iff_orbit [FiniteDimensional ℂ E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ) :
    (∀ χ : E, ContinuousAt (fun t => (inner ℂ (f t χ) χ : ℂ)) t₀) ↔
      ∀ x : E, ContinuousAt (fun t => f t x) t₀ :=
  (continuousAt_iff_expectation f t₀).symm.trans
    (StoneStrongContinuity.continuousAt_iff_pointwise f t₀)

/-- And expectation continuity is weak continuity. -/
theorem expectation_iff_weak [FiniteDimensional ℂ E] [CompleteSpace E]
    (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ) :
    (∀ χ : E, ContinuousAt (fun t => (inner ℂ (f t χ) χ : ℂ)) t₀) ↔
      ∀ φ : (E →L[ℂ] E) →L[ℂ] ℂ, ContinuousAt (fun t => φ (f t)) t₀ :=
  (continuousAt_iff_expectation f t₀).symm.trans (StoneWeakContinuity.continuousAt_iff_weak f t₀)

end

end StoneExpectationContinuity
