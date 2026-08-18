import CliffordPeriodicityHyperbolic
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

/-!
# Two more real diagonals, from Mathlib's base cases and the hyperbolic step

`WALLS §W7.2` records the hyperbolic step and the reason it does not break the real wall: it moves
`(p,q) → (p+1,q+1)` and **never changes `p − q`**, so it walks one diagonal and the estate had base
cases on only two of the eight residue classes — `p − q ≡ 2` (`Cl(3,1)`) and `≡ −2` (`Cl(1,3)`).

The watchlist item that section opened named a second check, and said it had to be a move rather
than a note: **what does Mathlib have?** It has three real base cases, none of which this estate had
looked at:

| Mathlib | signature | diagonal |
|---|---|---|
| `CliffordAlgebraRing.equiv : Cl(0 : QuadraticForm ℝ Unit) ≃ₐ ℝ` | `(0,0)` | `p − q ≡ 0` |
| `CliffordAlgebraComplex.equiv : Cl(−x²) ≃ₐ ℂ` | `(0,1)` | `p − q ≡ −1` |
| `CliffordAlgebraQuaternion.equiv` at `c₁ = c₂ = −1` | `(0,2)` | `p − q ≡ −2` |

> **`equivM2R`** — `Cl(1,1;ℝ) ≃ₐ[ℝ] M₂(ℝ)`, a diagonal the estate did not have.
> **`equivM2C`** — `Cl(1,2;ℝ) ≃ₐ[ℝ] M₂(ℂ)`, likewise.

**Reach goes from two diagonals to four.** The `(0,2)` base sits on the same diagonal as the
estate's own `Cl(1,3)`, so it adds no class; `(0,0)` and `(0,1)` are new.

## What this does NOT do

**Four of eight is not eight.** The classes `p − q ≡ 1, 3, 4, 5` have no base case here, and the
hyperbolic step cannot reach them from the four that do. **The wall is exactly the missing base
cases, or the mod-8 periodicity `Cl_{p+8,q} ≅ M₁₆(Cl_{p,q})` that would supply them all.**

**No signature is computed.** These are isomorphisms at named forms. That `QextHyp` of Mathlib's
`(0,1)` form *has* signature `(1,2)` is arithmetic on the construction, **not proved here** — and
saying *"every real form of signature `(1,2)`"* would need Sylvester's law, which Mathlib **does**
have (`QuadraticForm.equivalent_one_neg_one_weighted_sum_squared`, with `sigPos`/`sigNeg` for
uniqueness) and which is **not applied here**. Recorded so the next reader knows the normal-form
half is available and only the quantification is missing.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealDiagonals

open Matrix CliffordAlgebra

noncomputable section

/-- signature `(1,1)`: the zero form on a point, with a hyperbolic plane adjoined. -/
abbrev Q₁₁ : QuadraticForm ℝ (Unit × (ℝ × ℝ)) :=
  CliffordPeriodicityHyperbolic.QextHyp (0 : QuadraticForm ℝ Unit)

/-- signature `(1,2)`: Mathlib's `−x²` with a hyperbolic plane adjoined. -/
abbrev Q₁₂ : QuadraticForm ℝ (ℝ × (ℝ × ℝ)) :=
  CliffordPeriodicityHyperbolic.QextHyp CliffordAlgebraComplex.Q

/-- **`Cl(1,1;ℝ) ≅ M₂(ℝ)`** — the `p − q ≡ 0` diagonal. -/
def equivM2R : CliffordAlgebra Q₁₁ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact (CliffordPeriodicityHyperbolic.periodicityEquivHyp (0 : QuadraticForm ℝ Unit)).trans
    (AlgEquiv.mapMatrix CliffordAlgebraRing.equiv)

/-- **`Cl(1,2;ℝ) ≅ M₂(ℂ)`** — the `p − q ≡ −1` diagonal. -/
def equivM2C : CliffordAlgebra Q₁₂ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  exact (CliffordPeriodicityHyperbolic.periodicityEquivHyp CliffordAlgebraComplex.Q).trans
    (AlgEquiv.mapMatrix CliffordAlgebraComplex.equiv)

end

end CliffordRealDiagonals
