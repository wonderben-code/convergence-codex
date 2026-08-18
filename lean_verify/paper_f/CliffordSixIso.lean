import CliffordIso
import CliffordPeriodicity

/-!
# `Cl₆(ℂ) ≅ M₈(ℂ)`

`WALLS §W7.1` records this as the open half of the complex Clifford table:
`F1_7_SpacetimeForced.clifford_complex_even_dims` writes `Cl₆(ℂ) ≅ M₈(ℂ)` over its 6D conjunct,
`clifford6_finrank` supplies the **dimension**, and
`CliffordDimension.finrank_cliffordAlgebra_congr` proves the dimension **cannot** supply the
isomorphism — it is the same for every quadratic form on the space, the zero form included.

> **`equivM8`** — `CliffordAlgebra Q₆ ≃ₐ[ℂ] Matrix (Fin 8) (Fin 8) ℂ`, where
> `Q₆ = Q₄ ⊥ ⟨1,1⟩` on a space `finrank_V6` proves six-dimensional.

## This file is now four lines of mathematics and a transport

**REWRITTEN THE SAME DAY IT WAS WRITTEN.** The first version built the representation here, by hand,
for this one form. Its own record then predicted that *"the same construction should apply with
`Cl₆` in place of `Cl₄`"* and labelled that a prediction about difficulty (`ERRATUM 194`).
`CliffordPeriodicity` discharges the prediction instead of repeating the construction: nothing in
it used anything about `Q₄`, so it is stated once for every `Q`. **What is left here is the
instance and the transport**, and the duplicate proof is deleted rather than kept beside its
generalisation (`ERRATUM 176`).

`CliffordPeriodicity.periodicityEquiv Q₄` gives `Cl₆ ≅ M₂(Cl₄)`; `AlgEquiv.mapMatrix` applied to
`CliffordIso.cliffordMatrixEquiv` replaces `Cl₄` by `M₄(ℂ)`; `Matrix.compAlgEquiv` flattens
`M₂(M₄(ℂ))`; `Matrix.reindexAlgEquiv` along `finProdFinEquiv` lands in `M₈(ℂ)`.

**This is built on `CliffordIso`, not independent of it.** Without the `n = 4` isomorphism this
file would produce `Cl₆(ℂ) ≅ M₂(Cl₄(ℂ))` and stop.

## What is NOT proved, and the restriction is real rather than pedantic

**It is not proved for every nondegenerate six-dimensional complex form.** `Q₆` is one specific
form. Getting to *the* classification entry needs a normal-form theorem for complex quadratic forms
(any two of the same rank are equivalent), which **this estate does not have and this file does not
supply**.

**And the gap is not a technicality**: `CliffordDimension.finrank_cliffordAlgebra_congr` shows every
form on this space gives dimension `64`, while the zero form gives the exterior algebra, which is
not `M₈(ℂ)`. So *"`Cl(Q) ≅ M₈(ℂ)` for a six-dimensional `Q`"* is **false in general** and the
hypothesis on `Q` is doing real work.

**No published tag moves**, and nothing here is about the cascade, spinors or physics.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordSixIso

open Matrix CliffordAlgebra

noncomputable section

/-- the six-dimensional space: `Q₄`'s carrier with a plane adjoined. -/
abbrev V6 := ((ℂ × ℂ) × (ℂ × ℂ)) × (ℂ × ℂ)

/-- `Q₆ = Q₄ ⊥ ⟨1,1⟩`. -/
abbrev Q₆ : QuadraticForm ℂ V6 := CliffordPeriodicity.Qext Q₄

theorem finrank_V6 : Module.finrank ℂ V6 = 6 := by
  simp [Module.finrank_prod]

/-- The dimension agrees with the general formula — a check, not a new fact. -/
theorem finrank_clifford_Q6 : Module.finrank ℂ (CliffordAlgebra Q₆) = 64 := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  rw [CliffordDimension.finrank_cliffordAlgebra ℂ V6 Q₆, finrank_V6]
  norm_num

/-- **`Cl₆(ℂ) ≅ M₂(M₄(ℂ))`** — the periodicity step with `Cl₄` replaced by its matrix form. -/
def equivM2M4 : CliffordAlgebra Q₆ ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) ℂ) :=
  (CliffordPeriodicity.periodicityEquiv Q₄).trans
    (AlgEquiv.mapMatrix CliffordIso.cliffordMatrixEquiv)

/-- **`Cl₆(ℂ) ≅ M₈(ℂ)`.** -/
def equivM8 : CliffordAlgebra Q₆ ≃ₐ[ℂ] Matrix (Fin 8) (Fin 8) ℂ :=
  equivM2M4.trans
    ((Matrix.compAlgEquiv (Fin 2) (Fin 4) ℂ ℂ).trans
      (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv))

end

end CliffordSixIso
