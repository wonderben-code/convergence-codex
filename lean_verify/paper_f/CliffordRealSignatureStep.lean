import CliffordPeriodicityHyperbolic
import CliffordRealMinkowski
import CliffordRealMajorana

/-!
# Two new real signatures, from the hyperbolic step and the estate's own base cases

`CliffordPeriodicityHyperbolic.periodicityEquivHyp` is a tool, and `ERRATUM 48` is the standing
objection to tools: *a criterion producing no member it could not produce before is a criterion
whose usefulness is **asserted***. This file supplies members.

The estate has exactly two real Clifford isomorphisms — `CliffordRealMinkowski` at signature
`(1,3)` and `CliffordRealMajorana` at `(3,1)`. Adjoining a hyperbolic plane moves `(p,q)` to
`(p+1,q+1)`, so those two become:

> **`equivM4H`** — `Cl(2,4;ℝ) ≃ₐ[ℝ] M₄(ℍ)`, from `Cl(1,3;ℝ) ≅ M₂(ℍ)`.
> **`equivM8R`** — `Cl(4,2;ℝ) ≃ₐ[ℝ] M₈(ℝ)`, from `Cl(3,1;ℝ) ≅ M₄(ℝ)`.

**Neither was available to this estate before**, and both are six-dimensional real Clifford
algebras, where `CliffordEvenLadder` says nothing — that ladder is over `ℂ`, where signature does
not exist.

## What this does NOT do

**It does not give the eight-fold way.** The hyperbolic step moves along the diagonal and **never
changes `p − q`**, which is the invariant the real classification is graded by. From `(1,3)` it
reaches `(2,4), (3,5), …` and **nothing else**; from `(3,1)`, `(4,2), (5,3), …`. Two diagonals out
of the eight residue classes, and the estate has base cases on exactly those two.

**So the remaining wall is unchanged in kind**: `Cl_{p,0}` and `Cl_{0,q}` for small `p, q`, or the
mod-8 periodicity itself. **This adds members, not reach.**

**No published tag moves**; nothing here is about spacetime signature as physics.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealSignatureStep

open Matrix CliffordAlgebra
open scoped Quaternion

noncomputable section

/-- signature `(2,4)`: Minkowski's form with a hyperbolic plane adjoined. -/
abbrev Q₂₄ : QuadraticForm ℝ (((ℝ × ℝ) × (ℝ × ℝ)) × (ℝ × ℝ)) :=
  CliffordPeriodicityHyperbolic.QextHyp CliffordRealMinkowski.Q₁₃

/-- signature `(4,2)`: the Majorana form with a hyperbolic plane adjoined. -/
abbrev Q₄₂ : QuadraticForm ℝ (((ℝ × ℝ) × (ℝ × ℝ)) × (ℝ × ℝ)) :=
  CliffordPeriodicityHyperbolic.QextHyp CliffordRealMajorana.Q₃₁

/-- **`Cl(2,4;ℝ) ≅ M₄(ℍ)`.** -/
def equivM4H : CliffordAlgebra Q₂₄ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℍ[ℝ] := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact (CliffordPeriodicityHyperbolic.periodicityEquivHyp CliffordRealMinkowski.Q₁₃).trans
    ((AlgEquiv.mapMatrix CliffordRealMinkowski.cliffordRealMinkowskiEquiv).trans
      ((Matrix.compAlgEquiv (Fin 2) (Fin 2) ℍ[ℝ] ℝ).trans
        (Matrix.reindexAlgEquiv ℝ ℍ[ℝ] finProdFinEquiv)))

/-- **`Cl(4,2;ℝ) ≅ M₈(ℝ)`.** -/
def equivM8R : CliffordAlgebra Q₄₂ ≃ₐ[ℝ] Matrix (Fin 8) (Fin 8) ℝ := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact (CliffordPeriodicityHyperbolic.periodicityEquivHyp CliffordRealMajorana.Q₃₁).trans
    ((AlgEquiv.mapMatrix CliffordRealMajorana.cliffordMajoranaEquiv).trans
      ((Matrix.compAlgEquiv (Fin 2) (Fin 4) ℝ ℝ).trans
        (Matrix.reindexAlgEquiv ℝ ℝ finProdFinEquiv)))

end

end CliffordRealSignatureStep
