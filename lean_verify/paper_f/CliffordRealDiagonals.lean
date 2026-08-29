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

**⚠ HALF SUPERSEDED 2026-08-27, kept as written (`ERRATUM 94`, found by `ERRATUM 309`), and WHICH
half matters.** *"Not applied here"* is answered: `CliffordRealQuantified` applies Sylvester's law,
proves its converse (`equivalent_of_sigPos_eq`, which Mathlib does not supply) and gives
`cliffordEquiv_of_sigPos_eq` — the isomorphism class depends only on dimension and signature. **The
FIRST clause stands**: that `QExtHyp` of Mathlib's `(0,1)` form *has* signature `(1,2)` is still
computed nowhere, and that file says so itself in its own *"does not compute the signature of any
named form"*. So the paragraph is half dead and half live, and reading it as wholly open — which is
how it reads without this note — costs a search.

**⚠ AND THE LIVE HALF WAS ALREADY DEAD WHEN THAT NOTE WAS WRITTEN — 2026-08-29 (`ERRATUM 329`).**
*"The FIRST clause stands"* is **false**. `CliffordRealSignatures.sigPos_Q₁₂ = 1` and
`sigNeg_Q₁₂ = 2` compute the signature of **this file's own `Q₁₂`**, which is
`QextHyp CliffordAlgebraComplex.Q` — precisely *"`QextHyp` of Mathlib's `(0,1)` form"*. They go
through `SignatureArithmetic.sigPos_QextHyp` / `sigNeg_QextHyp` (general in `Q`) and
`sigPos_smul_sq` after rewriting Mathlib's `Q` as `(-1 : ℝ) • QuadraticMap.sq`. **That file is
dated 18 August, nine days BEFORE the note above**, and its own header table has a row reading
`| CliffordRealDiagonals.Q₁₂ | QextHyp (−x²) | (1,2) |` — **it names this file and this
abbreviation.** This file mentions it nowhere. **Both sentences above are kept as written
(`ERRATUM 94`)**: the original *"not proved here"* was true of THIS file when written and is still
true of this file, and the 27 August note is correct that the paragraph was half dead. What is
corrected is only *which* half — it is now wholly dead, and a note written to stop a reader
searching sent them searching for something that was already on the shelf.

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
