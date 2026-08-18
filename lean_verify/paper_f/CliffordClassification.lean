import CliffordEightIso
import CliffordEvenLadder

/-!
# The complex classification at ranks 6 and 8, quantified over every nondegenerate form

`CliffordSixIso` and `CliffordEightIso` prove `Cl(Q) ≅ M₈(ℂ)` and `Cl(Q) ≅ M₁₆(ℂ)` at **two
specific forms**, and both of their records — and `WALLS §W7.1`, three times — say the same thing
about what was missing:

> *"The classification table quantifies over **every** nondegenerate form of each rank, and that
> needs a normal-form theorem for complex quadratic forms. The estate does not have it, **and
> Mathlib was not searched for it here**, which is stated as an absence of search rather than an
> absence of the result."*

**The search was the missing step, and Mathlib has the theorem.**
`QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed`: over an algebraically closed field
with `2` invertible, every nondegenerate form is equivalent to the sum of `finrank` squares. With
`CliffordAlgebra.equivOfIsometry` to carry an isometry into the algebras, the quantified statements
follow from the two specific ones.

> **`clifford_iso_M8_of_nondegenerate`** — for **every** `6`-dimensional complex space and **every**
> nondegenerate `Q` on it, `CliffordAlgebra Q ≃ₐ[ℂ] M₈(ℂ)`. And the same at `8`/`M₁₆(ℂ)`.

## The only real work was nondegeneracy of the reference forms

`Q₆_separating` and `Q₈_separating`: the associated bilinear form of `Q₆` is
`x₁y₁ + x₂y₂ − x₃y₃ − x₄y₄ + x₅y₅ + x₆y₆` once unfolded, so feeding it the six coordinate vectors
forces `x = 0`. Everything else is composition.

## What this does NOT prove, and one of these is a correction of my own record

**Odd dimensions are untouched.** There the classification is `Cl_{2k+1}(ℂ) ≅ M ⊕ M`, a different
statement, and nothing here reaches it.

**Even ranks other than 2, 4, 6, 8 are untouched.** `CliffordPeriodicity` supplies the step for
every `Q`, so the ladder *should* continue — **that is a prediction about difficulty and is labelled
one** (`ERRATUM 194`). What would be needed is a family of reference forms of each even rank
together with **an induction proving each nondegenerate**, and this file builds neither.

**The nondegeneracy hypothesis is not removable and is not decoration.**
`CliffordDimension.finrank_cliffordAlgebra_congr` gives the same dimension for *every* form on the
space, the zero form included, and that one's Clifford algebra is the exterior algebra — not a
matrix algebra. So the statement is **false** without the hypothesis.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordClassification

open QuadraticMap

noncomputable section

/-- `Q₆` is nondegenerate: its associated form is diagonal with entries `1,1,−1,−1,1,1`. -/
theorem Q₆_separating :
    (QuadraticMap.associated (R := ℂ) CliffordSixIso.Q₆).SeparatingLeft := by
  intro x hx
  have h1 := hx (((1, 0), (0, 0)), (0, 0))
  have h2 := hx (((0, 1), (0, 0)), (0, 0))
  have h3 := hx (((0, 0), (1, 0)), (0, 0))
  have h4 := hx (((0, 0), (0, 1)), (0, 0))
  have h5 := hx (((0, 0), (0, 0)), (1, 0))
  have h6 := hx (((0, 0), (0, 0)), (0, 1))
  simp [CliffordSixIso.Q₆, CliffordPeriodicity.Qext, CliffordPeriodicity.Qplane,
    QuadraticMap.associated_apply, CliffordAlgebraQuaternion.Q_apply, Q₄] at h1 h2 h3 h4 h5 h6
  ring_nf at h1 h2 h3 h4 h5 h6
  obtain ⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩ := x
  simp_all

/-- `Q₈` is nondegenerate, by the same argument with two more coordinates. -/
theorem Q₈_separating :
    (QuadraticMap.associated (R := ℂ) CliffordEightIso.Q₈).SeparatingLeft := by
  intro x hx
  have h1 := hx ((((1, 0), (0, 0)), (0, 0)), (0, 0))
  have h2 := hx ((((0, 1), (0, 0)), (0, 0)), (0, 0))
  have h3 := hx ((((0, 0), (1, 0)), (0, 0)), (0, 0))
  have h4 := hx ((((0, 0), (0, 1)), (0, 0)), (0, 0))
  have h5 := hx ((((0, 0), (0, 0)), (1, 0)), (0, 0))
  have h6 := hx ((((0, 0), (0, 0)), (0, 1)), (0, 0))
  have h7 := hx ((((0, 0), (0, 0)), (0, 0)), (1, 0))
  have h8 := hx ((((0, 0), (0, 0)), (0, 0)), (0, 1))
  simp [CliffordEightIso.Q₈, CliffordSixIso.Q₆, CliffordPeriodicity.Qext,
    CliffordPeriodicity.Qplane, QuadraticMap.associated_apply,
    CliffordAlgebraQuaternion.Q_apply, Q₄] at h1 h2 h3 h4 h5 h6 h7 h8
  ring_nf at h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨⟨⟨⟨a, b⟩, ⟨c, d⟩⟩, ⟨e, f⟩⟩, ⟨g, h⟩⟩ := x
  simp_all

/-- **THE CLASSIFICATION ENTRY AT RANK 6.** Every nondegenerate quadratic form on every
six-dimensional complex space has Clifford algebra `M₈(ℂ)`.

**REWRITTEN THE SAME DAY TO CITE `CliffordEvenLadder`.** The first version proved this and
the rank-8 twin directly, each from the corresponding concrete isomorphism. The ladder proves
it at **every** even rank, so these are its cases `k = 3` and `k = 4`, and their own proofs are
**deleted rather than kept beside the generalisation** (`ERRATUM 176`). -/
theorem clifford_iso_M8_of_nondegenerate {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 6) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin 8) (Fin 8) ℂ) :=
  CliffordEvenLadder.clifford_iso_of_nondegenerate 3 (by rw [hV]) Q hQ

/-- **THE CLASSIFICATION ENTRY AT RANK 8.** -/
theorem clifford_iso_M16_of_nondegenerate {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 8) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin 16) (Fin 16) ℂ) :=
  CliffordEvenLadder.clifford_iso_of_nondegenerate 4 (by rw [hV]) Q hQ

/-- **AND THE LADDER REPROVES THE CONCRETE CASE, WHICH IS WHY `Q₆_separating` IS STILL LIVE.**
`CliffordSixIso.equivM8` builds `Cl(Q₆) ≃ₐ M₈(ℂ)` by an elementary route — periodicity on top of
`CliffordIso`, with no appeal to the fundamental theorem of algebra. This obtains the same
conclusion from the ladder instead, which **demonstrates** the subsumption rather than asserting it
(`ERRATUM 201`). **The concrete files are kept deliberately**: their route is independent of
`IsAlgClosed ℂ`, so they are not a weaker restatement of this. -/
theorem clifford_Q₆_iso_M8_via_ladder :
    Nonempty (CliffordAlgebra CliffordSixIso.Q₆ ≃ₐ[ℂ] Matrix (Fin 8) (Fin 8) ℂ) :=
  clifford_iso_M8_of_nondegenerate CliffordSixIso.finrank_V6 _ Q₆_separating

/-- The same at rank 8. -/
theorem clifford_Q₈_iso_M16_via_ladder :
    Nonempty (CliffordAlgebra CliffordEightIso.Q₈ ≃ₐ[ℂ] Matrix (Fin 16) (Fin 16) ℂ) :=
  clifford_iso_M16_of_nondegenerate CliffordEightIso.finrank_V8 _ Q₈_separating

end

end CliffordClassification
