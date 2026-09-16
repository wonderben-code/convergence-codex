/-
  StoneWeakContinuity: **the C⋆ carriers' turn, and the watchlist item unit 64 opened.**

  Unit 64 weakened Stone's converse on the OPERATOR carriers from continuity in the operator norm
  to continuity of the orbits `t ↦ U t ψ`, through one inequality over an orthonormal basis of the
  space. Its header said plainly that the same weakening was available on the C⋆ carriers —
  `Mₙ(ℂ)` and `CascadeGNS.M4` are finite dimensional too — but that the hypothesis a functional
  supplies is about the DUAL, so `opNorm_le_sum_basis` does not reach it, and it opened a
  watchlist item rather than claiming the route. **This is that item, with the route run.**

  THE BRIDGE, and it is shorter than unit 64's. A finite-dimensional normed space is
  linearly HOMEOMORPHIC to `ι → ℂ` by `Module.Basis.equivFunL`, whose components are the
  coordinate functionals `Module.Basis.coord`, each continuous because every linear map out of a
  finite-dimensional space is (`LinearMap.continuous_of_finiteDimensional`). So convergence
  against every continuous functional IS convergence in norm: `continuousAt_of_weak` needs no
  estimate at all, only that the coordinate maps are among the functionals being tested.

  WHAT IS PROVED.
  * **`continuousAt_iff_weak`** — for a finite-dimensional complex normed space, `t ↦ f t` is
    continuous at `t₀` in NORM exactly when `t ↦ φ (f t)` is for every continuous linear
    functional `φ`.
  * **`instFiniteDimensionalCStarMatrix`** — `FiniteDimensional ℂ (CStarMatrix m n ℂ)`, which the
    pinned Mathlib does NOT provide: measured, `infer_instance` fails on it and on
    `CascadeGNS.M4`. Supplied here through `CStarMatrix.ofMatrixₗ` and
    `LinearEquiv.finiteDimensional`, under `[Finite]` rather than `[Fintype]` — the `Fintype`
    data is used only in the proof, and `linter.unusedFintypeInType` said so under `lake build`
    after the single-file check had passed clean (`ERRATUM 587`). **Unlike the bundled C⋆
    instance `ERRATUM 594` discusses, this one imposes no choice on importers** —
    finite-dimensionality is a fact about the module and says nothing about which norm the type
    carries.
  * **`exists_unique_global_generator_of_weak`**, **`eq_unitaryGroup_iff_weak`** — Stone's
    converse and its characterisation on ANY finite-dimensional C⋆-algebra, from the group law and
    weak continuity at the single point `0`.
  * **`matrix_*_of_weak`**, **`cascade_*_of_weak`** — the same at `Mₙ(ℂ)` for every finite index
    type and at `CascadeGNS.M4`, the cascade's own spacetime-level algebra. These are the two
    carriers unit 64 could not reach.
  * **`pointwise_iff_weak`** — and on `E →L[ℂ] E` with `E` finite dimensional the three
    hypotheses this estate now has are ONE hypothesis: norm, orbitwise (unit 64) and weak
    continuity agree. That is worth stating because three names for one condition is exactly how
    a reader ends up proving the same thing twice.

  WHAT IS **NOT** PROVED, and the first item is a genuinely weaker theorem that this file does not
  reach.
  * **The STATE form, which is the one a physicist would write.** The hypothesis here is
    quantified over ALL continuous linear functionals, which is a STRONGER requirement than
    continuity against states alone, so `∀ state, continuous → generator` would be a better
    theorem and is not proved. It needs every bounded functional on a C⋆-algebra to decompose
    into states, and **measured against the pinned environment: there is no state-space API to
    phrase it with** — zero names match `(is)?[Ss]tate` among the `CStar`/`Star`/positive
    families in the 471478-constant dump. So the estate would have to define states and prove the
    decomposition first; that is a separate unit and a design decision about how states are
    carried, not a gap in this one.
  * **Nothing about infinite dimension.** Unchanged, and for the same reason as unit 64: the
    generator is unbounded there and no counterexample is built here either.
  * **Nothing about the generator's spectrum, the Born rule, Gleason or Wigner.**

  0 sorry. 0 new axioms. All declarations on `[propext, Classical.choice, Quot.sound]`.
-/

import StoneStrongContinuity

namespace StoneWeakContinuity

open scoped ComplexOrder

noncomputable section

/-! ## 1. Weak continuity is norm continuity in finite dimension -/

section Bridge

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- **THE BRIDGE.** Convergence against every continuous linear functional is convergence in
norm, on a finite-dimensional space. The coordinate functionals of a basis are among the
functionals tested, and they determine the point. -/
theorem continuousAt_of_weak [FiniteDimensional ℂ A] (f : ℝ → A) (t₀ : ℝ)
    (hw : ∀ φ : A →L[ℂ] ℂ, ContinuousAt (fun t => φ (f t)) t₀) : ContinuousAt f t₀ := by
  classical
  set b := Module.finBasis ℂ A with hb
  have key : ContinuousAt (fun t => b.equivFunL (f t)) t₀ := by
    refine continuousAt_pi.2 fun i => ?_
    have h := hw (LinearMap.toContinuousLinearMap (b.coord i))
    simpa [Module.Basis.equivFunL_apply, Module.Basis.coord_apply] using h
  exact (b.equivFunL.toHomeomorph.comp_continuousAt_iff f t₀).1 key

/-- The easy direction: a continuous functional composed with a norm-continuous curve. No finite
dimensionality. -/
theorem weak_of_continuousAt (f : ℝ → A) (t₀ : ℝ) (hc : ContinuousAt f t₀)
    (φ : A →L[ℂ] ℂ) : ContinuousAt (fun t => φ (f t)) t₀ :=
  (φ.continuous.continuousAt).comp hc

/-- **The biconditional.** -/
theorem continuousAt_iff_weak [FiniteDimensional ℂ A] (f : ℝ → A) (t₀ : ℝ) :
    ContinuousAt f t₀ ↔ ∀ φ : A →L[ℂ] ℂ, ContinuousAt (fun t => φ (f t)) t₀ :=
  ⟨fun hc φ => weak_of_continuousAt f t₀ hc φ, continuousAt_of_weak f t₀⟩

end Bridge

/-- **`FiniteDimensional ℂ (CStarMatrix m n ℂ)`, WHICH THE PINNED MATHLIB DOES NOT PROVIDE.**
Measured before writing it: `infer_instance` fails for this and for `CascadeGNS.M4`, because
`CStarMatrix` is a type synonym and the `Matrix` instance does not transport through it. The
transport is one line off `CStarMatrix.ofMatrixₗ`. **This instance imposes nothing on importers**,
which is the difference between it and the bundled-norm instance `ERRATUM 594` declined to
assemble: finite-dimensionality is a statement about the module and fixes no norm. -/
instance instFiniteDimensionalCStarMatrix {m n : Type*} [Finite m] [Finite n] :
    FiniteDimensional ℂ (CStarMatrix m n ℂ) := by
  -- `[Finite]` rather than `[Fintype]` on the linter's advice, which is also the weaker
  -- hypothesis: the `Fintype` data is used only inside the proof, never in the statement.
  -- `linter.unusedFintypeInType` fires only under `lake build` and not under
  -- `lake env lean` on the single file (`ERRATUM 587`), so the warning baseline caught it.
  classical
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  exact LinearEquiv.finiteDimensional (CStarMatrix.ofMatrixₗ (R := ℂ) (m := m) (n := n))

/-! ## 2. Stone's converse under weak continuity -/

section Converse

variable {A : Type*} [CStarAlgebra A] [FiniteDimensional ℂ A]

/-- Continuity into `unitary A` from weak continuity of the coercion. -/
theorem continuousAt_unitary_of_weak (U : ℝ → unitary A) (t₀ : ℝ)
    (hw : ∀ φ : A →L[ℂ] ℂ, ContinuousAt (fun t => φ ((U t : A))) t₀) : ContinuousAt U t₀ :=
  StoneStrongContinuity.continuousAt_unitary_of_coe U t₀
    (continuousAt_of_weak (fun t => ((U t : A))) t₀ hw)

/-- And the biconditional for a family of unitaries. -/
theorem continuousAt_unitary_iff_weak (U : ℝ → unitary A) (t₀ : ℝ) :
    ContinuousAt U t₀ ↔ ∀ φ : A →L[ℂ] ℂ, ContinuousAt (fun t => φ ((U t : A))) t₀ := by
  refine ⟨fun hc φ => ?_, fun hw => continuousAt_unitary_of_weak U t₀ hw⟩
  exact weak_of_continuousAt _ t₀ (continuousAt_subtype_val.comp hc) φ

/-- **STONE'S CONVERSE FROM WEAK CONTINUITY, ON ANY FINITE-DIMENSIONAL C⋆-ALGEBRA.** -/
theorem exists_unique_global_generator_of_weak (U : ℝ → unitary A)
    (hw : ∀ φ : A →L[ℂ] ℂ, ContinuousAt (fun t => φ ((U t : A))) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint A, ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  StoneConverseLocal.exists_unique_global_generator U
    (continuousAt_unitary_of_weak U 0 hw) hgrp

/-- **And the characterisation**, so the weakened hypothesis is forced and not merely
sufficient. -/
theorem eq_unitaryGroup_iff_weak (U : ℝ → unitary A) :
    ((∀ φ : A →L[ℂ] ℂ, ContinuousAt (fun t => φ ((U t : A))) 0) ∧
        ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint A, U = FiniteStone.unitaryGroup H := by
  rw [← StoneConverseLocal.eq_unitaryGroup_iff U]
  exact and_congr_left' (continuousAt_unitary_iff_weak U 0).symm

end Converse

/-! ## 3. The two named C⋆ carriers unit 64 could not reach -/

section Carriers

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **At `Mₙ(ℂ)`, for every finite index type.** -/
theorem matrix_exists_unique_generator_of_weak (U : ℝ → unitary (CStarMatrix n n ℂ))
    (hw : ∀ φ : CStarMatrix n n ℂ →L[ℂ] ℂ,
      ContinuousAt (fun t => φ ((U t : CStarMatrix n n ℂ))) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint (CStarMatrix n n ℂ),
      ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  exists_unique_global_generator_of_weak U hw hgrp

/-- And the characterisation there. -/
theorem matrix_eq_unitaryGroup_iff_weak (U : ℝ → unitary (CStarMatrix n n ℂ)) :
    ((∀ φ : CStarMatrix n n ℂ →L[ℂ] ℂ,
        ContinuousAt (fun t => φ ((U t : CStarMatrix n n ℂ))) 0) ∧
        ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint (CStarMatrix n n ℂ), U = FiniteStone.unitaryGroup H :=
  eq_unitaryGroup_iff_weak U

/-- **At `CascadeGNS.M4`**, the cascade's own spacetime-level algebra. -/
theorem cascade_exists_unique_generator_of_weak (U : ℝ → unitary CascadeGNS.M4)
    (hw : ∀ φ : CascadeGNS.M4 →L[ℂ] ℂ, ContinuousAt (fun t => φ ((U t : CascadeGNS.M4))) 0)
    (hgrp : ∀ s t, U (s + t) = U s * U t) :
    ∃! H : selfAdjoint CascadeGNS.M4, ∀ t : ℝ, U t = selfAdjoint.expUnitary (t • H) :=
  exists_unique_global_generator_of_weak U hw hgrp

/-- And the characterisation there. -/
theorem cascade_eq_unitaryGroup_iff_weak (U : ℝ → unitary CascadeGNS.M4) :
    ((∀ φ : CascadeGNS.M4 →L[ℂ] ℂ, ContinuousAt (fun t => φ ((U t : CascadeGNS.M4))) 0) ∧
        ∀ s t, U (s + t) = U s * U t)
      ↔ ∃ H : selfAdjoint CascadeGNS.M4, U = FiniteStone.unitaryGroup H :=
  eq_unitaryGroup_iff_weak U

end Carriers

/-! ## 4. Three names for one hypothesis -/

/-- **ON A FINITE-DIMENSIONAL OPERATOR ALGEBRA THE THREE CONTINUITY HYPOTHESES COINCIDE.** Norm
continuity, continuity of every orbit (unit 64) and weak continuity are the same condition. Stated
because three names for one condition is how a reader ends up proving the same thing twice. -/
theorem pointwise_iff_weak {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [CompleteSpace E] (f : ℝ → (E →L[ℂ] E)) (t₀ : ℝ) :
    (∀ x : E, ContinuousAt (fun t => f t x) t₀) ↔
      ∀ φ : (E →L[ℂ] E) →L[ℂ] ℂ, ContinuousAt (fun t => φ (f t)) t₀ :=
  (StoneStrongContinuity.continuousAt_iff_pointwise f t₀).symm.trans
    (continuousAt_iff_weak f t₀)

end

end StoneWeakContinuity
