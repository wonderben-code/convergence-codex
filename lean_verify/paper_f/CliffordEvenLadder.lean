import CliffordPeriodicity
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.QuadraticForm.AlgClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The complex classification in every even rank

`CliffordClassification` closes the table at ranks 6 and 8, and its record — like
`WALLS §W7.1` and two file headers before it — ends with the same sentence:

> *"Even ranks other than 2, 4, 6, 8 are untouched. `CliffordPeriodicity` supplies the step for
> every `Q`, so the ladder **should** continue — a prediction about difficulty and labelled one."*

**`ERRATUM 203` says the next writing of a deferral must be an attempt.** That entry was written
about a library search restated three times; this is the same rule applied to the sentence above,
which had by then been written twice.

> **`clifford_iso_of_nondegenerate`** — for every `k`, every complex space of dimension `2k` and
> every nondegenerate `Q` on it, `CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ`.

## The three pieces

**`Rf n`** is the sum of `n` squares on `Fin n → ℂ`, and `Rf_sep` says it is nondegenerate —
`radical_weightedSumSquares` gives its radical as the span of the coordinates with zero weight,
which is empty.

**`splitIso`** peels off two coordinates: `Rf (n+2) ≃ Rf n ⊥ ⟨1,1⟩`, by
`finSumFinEquiv`, `sumArrowLequivProdArrow` and `finTwoArrow`. This is the only index bookkeeping
in the file.

**`cliffordRf`** is the ladder, by induction on `k`. The base is rank `0`, where the space is
trivial, every element of the Clifford algebra is a scalar (`CliffordAlgebra.induction`), and both
sides are one-dimensional. The step is `splitIso`, then `CliffordPeriodicity.periodicityEquiv`, then
the inductive hypothesis under `AlgEquiv.mapMatrix`, then `Matrix.compAlgEquiv` and a reindex.

The general statement then follows as at ranks 6 and 8:
`QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed` on both `Q` and `Rf (2k)`, and
`CliffordAlgebra.equivOfIsometry`.

## What is NOT proved

**Odd dimensions.** There `Cl_{2k+1}(ℂ) ≅ M ⊕ M` — the algebra is **not** simple — and nothing here
reaches it. This is a different theorem, not a missing case of this one.

**The nondegeneracy hypothesis is not removable.**
`CliffordDimension.finrank_cliffordAlgebra_congr` gives dimension `2 ^ (2k)` for *every* form on the
space, the zero form included, whose Clifford algebra is the exterior algebra and is not a matrix
algebra. The statement is **false** without the hypothesis.

**Nothing about real forms**, where signature is an invariant and the classification is the
eight-fold way; that is `WALLS §W7.0`'s subject and is untouched.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordEvenLadder

open QuadraticMap Module CliffordAlgebra

noncomputable section

/-- the sum of `n` squares on `Fin n → ℂ`. -/
abbrev Rf (n : ℕ) : QuadraticForm ℂ (Fin n → ℂ) := weightedSumSquares ℂ (1 : Fin n → ℂ)

theorem Rf_sep (n : ℕ) : (QuadraticMap.associated (R := ℂ) (Rf n)).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, ← QuadraticMap.radical_eq_ker_associated,
    QuadraticForm.radical_weightedSumSquares]
  simp [Pi.spanSubset]

theorem finrank_Rf_space (n : ℕ) : Module.finrank ℂ (Fin n → ℂ) = n := by simp

/-- peeling two coordinates off `Fin (n+2) → ℂ`. -/
def split (n : ℕ) : (Fin (n + 2) → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (ℂ × ℂ) :=
  (LinearEquiv.funCongrLeft ℂ ℂ (finSumFinEquiv (m := n) (n := 2)).symm).symm.trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin 2) ℂ ℂ).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl ℂ _) (LinearEquiv.finTwoArrow ℂ ℂ)))

/-- **`Rf (n+2)` IS `Rf n` WITH A PLANE ADJOINED**, which is what makes the periodicity step
applicable to this family. -/
def splitIso (n : ℕ) : (Rf (n + 2)).IsometryEquiv (CliffordPeriodicity.Qext (Rf n)) where
  __ := split n
  map_app' v := by
    simp [split, Rf, weightedSumSquares_apply, CliffordPeriodicity.Qext,
      CliffordPeriodicity.Qplane, QuadraticMap.prod_apply, CliffordAlgebraQuaternion.Q_apply,
      LinearEquiv.funCongrLeft, LinearEquiv.sumArrowLequivProdArrow, LinearEquiv.finTwoArrow,
      ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_two]

/-! ### The base of the ladder: a Clifford algebra over a zero-dimensional space -/

theorem algebraMap_surjective_of_subsingleton {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Subsingleton V] (Q : QuadraticForm ℂ V) :
    Function.Surjective (algebraMap ℂ (CliffordAlgebra Q)) := by
  intro x
  induction x using CliffordAlgebra.induction with
  | algebraMap r => exact ⟨r, rfl⟩
  | ι v => exact ⟨0, by rw [map_zero, Subsingleton.elim v 0, map_zero]⟩
  | mul a b ha hb =>
      obtain ⟨p, hp⟩ := ha; obtain ⟨q, hq⟩ := hb
      exact ⟨p * q, by rw [map_mul, hp, hq]⟩
  | add a b ha hb =>
      obtain ⟨p, hp⟩ := ha; obtain ⟨q, hq⟩ := hb
      exact ⟨p + q, by rw [map_add, hp, hq]⟩

theorem algebraMap_matrix_one_surjective :
    Function.Surjective (algebraMap ℂ (Matrix (Fin 1) (Fin 1) ℂ)) := by
  intro M
  refine ⟨M 0 0, ?_⟩
  ext i j
  fin_cases i; fin_cases j; simp [Matrix.algebraMap_matrix_apply]

/-- **THE LADDER.** `Cl` of the sum of `2k` squares is `M_{2^k}(ℂ)`. -/
theorem cliffordRf (k : ℕ) :
    Nonempty (CliffordAlgebra (Rf (2 * k)) ≃ₐ[ℂ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) := by
  induction k with
  | zero =>
      haveI : Subsingleton (Fin 0 → ℂ) := by
        rw [← Module.finrank_zero_iff (R := ℂ)]; simp
      have h1 : Module.finrank ℂ ℂ = Module.finrank ℂ (CliffordAlgebra (Rf 0)) := by
        haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
        rw [CliffordDimension.finrank_cliffordAlgebra ℂ (Fin 0 → ℂ) (Rf 0), finrank_Rf_space]
        simp
      have h2 : Module.finrank ℂ ℂ = Module.finrank ℂ (Matrix (Fin 1) (Fin 1) ℂ) := by
        rw [Module.finrank_matrix ℂ ℂ (Fin 1) (Fin 1)]; simp
      exact ⟨(CliffordDimension.algEquivOfSurjectiveOfFinrankEq (Algebra.ofId ℂ _)
          (algebraMap_surjective_of_subsingleton (Rf 0)) h1).symm.trans
        (CliffordDimension.algEquivOfSurjectiveOfFinrankEq (Algebra.ofId ℂ _)
          algebraMap_matrix_one_surjective h2)⟩
  | succ k ih =>
      obtain ⟨g⟩ := ih
      refine ⟨?_⟩
      refine (CliffordAlgebra.equivOfIsometry (splitIso (2 * k))).trans ?_
      refine (CliffordPeriodicity.periodicityEquiv (Rf (2 * k))).trans ?_
      refine (AlgEquiv.mapMatrix g).trans ?_
      refine (Matrix.compAlgEquiv (Fin 2) (Fin (2 ^ k)) ℂ ℂ).trans ?_
      exact (Matrix.reindexAlgEquiv ℂ ℂ
        (finProdFinEquiv.trans (finCongr (by ring : 2 * 2 ^ k = 2 ^ (k + 1)))))

/-- **THE COMPLEX CLASSIFICATION IN EVERY EVEN RANK.** -/
theorem clifford_iso_of_nondegenerate (k : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 2 * k) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ) := by
  have e1 := QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed Q hQ
  have e2 := QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed (Rf (2 * k)) (Rf_sep _)
  rw [hV] at e1
  rw [finrank_Rf_space] at e2
  obtain ⟨i1⟩ := e1
  obtain ⟨i2⟩ := e2
  obtain ⟨g⟩ := cliffordRf k
  exact ⟨(CliffordAlgebra.equivOfIsometry (i1.trans i2.symm)).trans g⟩

end

end CliffordEvenLadder
