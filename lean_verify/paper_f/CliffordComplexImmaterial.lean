import CliffordEvenLadder
import CliffordIso

/-!
# The signature of `Q₄` is provably immaterial over ℂ

`F4_1e_CliffordMatrix` defines the concrete Clifford model on a form of **signature `(2,2)`** and
its docstring says:

> *"Over ℂ, equivalent to any non-degenerate quadratic form on `ℂ⁴`."*

That sentence is the justification for a modelling choice — `ASSUMPTIONS_LEDGER` entry 22 records
the `(2,2)` signature and calls it *"immaterial over ℂ"* — and until now it appeared **only** as
prose, in a docstring and in an audit note. `CliffordEvenLadder.clifford_iso_of_nondegenerate`
quantifies over every nondegenerate complex form of a given even rank, so the sentence is provable.
This file proves it.

## What is proved

> **`clifford_iso_Q₄_of_nondegenerate`** — for **every** nondegenerate complex quadratic form `Q` on
> a 4-dimensional space, `Cl(Q) ≃ₐ[ℂ] Cl(Q₄)`. The choice of signature `(2,2)` costs nothing.

> **`Q₄_separating`** — `Q₄` is nondegenerate. Nothing in the estate had this, and the quantified
> statement cannot be applied without it.

The step that made them reachable is the general nondegeneracy of an orthogonal sum, which Mathlib
does not state:

> **`separatingLeft_prod`** — if `Q₁` and `Q₂` are nondegenerate then so is `Q₁ ⊥ Q₂`.

Mathlib has `QuadraticMap.associated_prod` (the bilinear form of a product splits) but nothing that
carries nondegeneracy across; the proof is to evaluate against `(y, 0)` and `(0, y)`.

## What this does NOT do

**It does not reprove `Cl(Q₄) ≅ M₄(ℂ)`, and an earlier draft of this file did.** That draft stated
it as a `Nonempty`, derived from rank 4 plus `Q₄_separating` with no gamma matrices — and it was
**deleted in adversarial review**, because `CliffordIso.cliffordMatrixEquiv` already gives the
actual `≃ₐ`, which is strictly stronger than a `Nonempty` of one. Keeping a weaker restatement
beside its own generalisation is what `ERRATUM 176` forbids. The theorem below cites
`cliffordMatrixEquiv` instead.

What survives that deletion is an observation and is recorded as one, with `ERRATUM 48`'s rule in
mind — **it produces no member the estate could not already produce**: the isomorphism at `Q₄` does
not *need* the four explicit matrices, four `decide`d squares, six anticommutators and roughly three
hundred lines of surjectivity and injectivity. Rank 4 and nondegeneracy suffice for *existence*.
`F4_1e` and `CliffordIso` remain necessary for the *explicit* isomorphism, whose named generator
images `cliffordMatrixEquiv_e₁ … _e₄` nothing here supplies.

**It does not touch what `ASSUMPTIONS 22` is actually about**, which is that spacetime is read at
cascade level D₂ while `F1_6` locates Pati–Salam at D₃. That is a modelling conflict and no theorem
about quadratic forms addresses it. What this discharges is one *supporting* clause of that entry.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordComplexImmaterial

open QuadraticForm QuadraticMap

noncomputable section

/-! ## Nondegeneracy of an orthogonal sum -/

variable {R M₁ M₂ : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]

/-- **An orthogonal sum of nondegenerate forms is nondegenerate.** Mathlib has
`QuadraticMap.associated_prod`, which splits the bilinear form of a product, but nothing that
carries nondegeneracy across it. -/
theorem separatingLeft_prod {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (h₁ : (QuadraticMap.associated (R := R) Q₁).SeparatingLeft)
    (h₂ : (QuadraticMap.associated (R := R) Q₂).SeparatingLeft) :
    (QuadraticMap.associated (R := R) (Q₁.prod Q₂)).SeparatingLeft := by
  intro x hx
  have hfst : x.1 = 0 := by
    refine h₁ x.1 fun y => ?_
    have := hx (y, 0)
    simpa using this
  have hsnd : x.2 = 0 := by
    refine h₂ x.2 fun y => ?_
    have := hx (0, y)
    simpa using this
  exact Prod.ext hfst hsnd

/-! ## The line, and the quaternionic two-variable form

Stated over ℂ, which is where the claim this file is about lives. `QuadraticMap.associated_sq`
gives `associated sq = mul`, so a nonzero multiple of `x²` has bilinear form `c · x · y`. -/

/-- A nonzero multiple of `x²` on the line is nondegenerate. -/
theorem separatingLeft_smul_sq {c : ℂ} (hc : c ≠ 0) :
    (QuadraticMap.associated (R := ℂ)
      (c • (QuadraticMap.sq : QuadraticForm ℂ ℂ))).SeparatingLeft := by
  intro x hx
  have h := hx 1
  rw [map_smul] at h
  simp only [LinearMap.smul_apply, QuadraticMap.associated_sq, LinearMap.mul_apply',
    smul_eq_mul, mul_one] at h
  exact (mul_eq_zero.mp h).resolve_left hc

/-- `CliffordAlgebraQuaternion.Q c₁ c₂` is nondegenerate when neither coefficient vanishes. It is
*defined* as an orthogonal sum of two lines, so this is `separatingLeft_prod` applied once. -/
theorem separatingLeft_quaternionQ {c₁ c₂ : ℂ} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    (QuadraticMap.associated (R := ℂ) (CliffordAlgebraQuaternion.Q c₁ c₂)).SeparatingLeft :=
  separatingLeft_prod (separatingLeft_smul_sq h₁) (separatingLeft_smul_sq h₂)

/-! ## `Q₄`, and the sentence in its docstring -/

/-- `Q₄` is nondegenerate: it is `Q(1,1) ⊥ Q(−1,−1)` and all four coefficients are nonzero. -/
theorem Q₄_separating :
    (QuadraticMap.associated (R := ℂ) Q₄).SeparatingLeft :=
  separatingLeft_prod (separatingLeft_quaternionQ one_ne_zero one_ne_zero)
    (separatingLeft_quaternionQ (by norm_num) (by norm_num))

/-- **The docstring's sentence, proved.** *"Over ℂ, equivalent to any non-degenerate quadratic form
on `ℂ⁴`"* — for every nondegenerate complex form on a 4-dimensional space, the Clifford algebra is
the same as `Q₄`'s. The `(2,2)` signature `ASSUMPTIONS 22` records is provably a free choice. -/
theorem clifford_iso_Q₄_of_nondegenerate {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 4) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] CliffordAlgebra Q₄) := by
  obtain ⟨e⟩ := CliffordEvenLadder.clifford_iso_of_nondegenerate 2
    (by omega : Module.finrank ℂ V = 2 * 2) Q hQ
  exact ⟨e.trans CliffordIso.cliffordMatrixEquiv.symm⟩

end

end CliffordComplexImmaterial
