import CliffordEvenLadder

/-!
# The complex classification in every ODD rank

`WALLS §W7.1`, after the even ladder closed, recorded one thing left under the complex half:

> *"Odd dimensions, where `Cl_{2k+1}(ℂ) ≅ M ⊕ M` — the algebra is **not simple**, so this is a
> different theorem rather than a missing case. Difficulty not estimated; the first move is a
> library search."*

**The search found the answer inside this estate rather than in Mathlib**, and it makes the odd case
the *same* ladder. `CliffordPeriodicity.periodicityEquiv` was proved for **every** quadratic form —
nothing in it asks for an even-dimensional one. So `Cl(Rf (2k+1)) ≅ M₂(Cl(Rf (2k−1)))` exactly as in
the even case, and the odd tower is the even tower started one rung lower.

> **`clifford_iso_of_nondegenerate_odd`** — for every `k`, every complex space of dimension `2k+1`
> and every nondegenerate `Q` on it,
> `CliffordAlgebra Q ≃ₐ[ℂ] Matrix (Fin (2^k)) (Fin (2^k)) ℂ × Matrix (Fin (2^k)) (Fin (2^k)) ℂ`.

## What was actually missing, and it was small

**The base.** `Cl` of a single square is `ℂ × ℂ`: send the generator to `(1, −1)`, which squares to
`(1,1)`. That is where the direct sum enters, and it is the only place — every rung above it just
carries the splitting along.

**`matrixProd`.** `Matrix n n (A × B) ≃ₐ[ℂ] Matrix n n A × Matrix n n B`, which Mathlib does not
have. Entrywise, three routine field checks.

**Nothing else.** No volume element, no central idempotent, no computation of the centre — the
textbook route for the odd case, and `WALLS §W7.1` was right that Mathlib has none of it. It is not
needed, because the direct sum is already present at rank 1 and periodicity is indifferent to it.

## What this does NOT prove

**The algebra is not claimed simple or non-simple.** `M ⊕ M` is visibly not a matrix algebra, but
this file proves an isomorphism, not an invariant-theoretic statement, and **no non-isomorphism to
`M_{2^k}(ℂ)` of the right size is proved here** — that would need an invariant, and
`CliffordDimension.finrank_cliffordAlgebra_congr` is the standing reminder that dimension is
not one.

**The nondegeneracy hypothesis is not removable**, for the same reason as in the even case: the
zero form has a Clifford algebra of the same dimension which is the exterior algebra.

**Real forms are untouched** — `WALLS §W7.0`'s subject, a different invariant theory.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordOddLadder

open QuadraticMap Module CliffordAlgebra CliffordEvenLadder

noncomputable section

section MatrixProd

variable (n : Type*) [Fintype n] [DecidableEq n]
variable (A B : Type*) [Semiring A] [Semiring B] [Algebra ℂ A] [Algebra ℂ B]

/-- **MATRICES OVER A PRODUCT ARE A PRODUCT OF MATRICES.** Not in Mathlib; entrywise. -/
def matrixProd : Matrix n n (A × B) ≃ₐ[ℂ] Matrix n n A × Matrix n n B where
  toFun M := (M.map Prod.fst, M.map Prod.snd)
  invFun p := Matrix.of fun i j => (p.1 i j, p.2 i j)
  left_inv M := by ext i j <;> simp
  right_inv p := by ext i j <;> simp
  map_mul' M N := by
    ext i j <;> simp [Matrix.mul_apply, Prod.fst_sum, Prod.snd_sum, Matrix.map_apply]
  map_add' M N := by ext i j <;> simp
  commutes' c := by
    ext i j <;>
      simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, Prod.algebraMap_apply,
        apply_ite Prod.fst, apply_ite Prod.snd]

end MatrixProd

/-! ### The base: `Cl` of one square is `ℂ × ℂ` -/

/-- the generator goes to `(1, −1)`. -/
def cl1Map : (Fin 1 → ℂ) →ₗ[ℂ] ℂ × ℂ where
  toFun v := (v 0, -(v 0))
  map_add' x y := by simp; ring
  map_smul' c x := by simp

theorem cl1Map_sq (v : Fin 1 → ℂ) :
    cl1Map v * cl1Map v = algebraMap ℂ (ℂ × ℂ) (Rf 1 v) := by
  simp [cl1Map, Rf, weightedSumSquares_apply, Prod.algebraMap_apply]

/-- the induced algebra map. -/
def toProd : CliffordAlgebra (Rf 1) →ₐ[ℂ] ℂ × ℂ :=
  CliffordAlgebra.lift (Rf 1) ⟨cl1Map, cl1Map_sq⟩

@[simp] theorem toProd_ι (v : Fin 1 → ℂ) : toProd (ι (Rf 1) v) = cl1Map v :=
  CliffordAlgebra.lift_ι_apply _ _ v

theorem toProd_surjective : Function.Surjective toProd := by
  intro p
  have h1 : ((1 : ℂ), (-1 : ℂ)) ∈ toProd.range :=
    ⟨ι (Rf 1) (fun _ => 1), by simp [cl1Map]⟩
  have hmem : p ∈ toProd.range := by
    have : p = ((2 : ℂ)⁻¹ * (p.1 + p.2)) • (1 : ℂ × ℂ)
        + ((2 : ℂ)⁻¹ * (p.1 - p.2)) • ((1 : ℂ), (-1 : ℂ)) := by
      ext <;> · simp [Prod.smul_def]; ring
    rw [this]
    exact add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.smul_mem _ h1 _)
  exact hmem

/-- **`Cl(⟨1⟩) ≅ ℂ × ℂ`.** This is where the direct sum enters the odd tower, and the only place. -/
def equivBase : CliffordAlgebra (Rf 1) ≃ₐ[ℂ] ℂ × ℂ := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  refine CliffordDimension.cliffordAlgEquivOfSurjective ℂ (Fin 1 → ℂ) (Rf 1) toProd
    toProd_surjective ?_
  rw [finrank_Rf_space]
  simp

/-- `M₁(ℂ) ≅ ℂ`. -/
def matrixOneEquiv : Matrix (Fin 1) (Fin 1) ℂ ≃ₐ[ℂ] ℂ :=
  (CliffordDimension.algEquivOfSurjectiveOfFinrankEq (Algebra.ofId ℂ _)
    algebraMap_matrix_one_surjective (by rw [Module.finrank_matrix ℂ ℂ (Fin 1) (Fin 1)]; simp)).symm

/-! ### The odd ladder -/

/-- **`Cl` OF THE SUM OF `2k+1` SQUARES IS TWO COPIES OF `M_{2^k}(ℂ)`.** -/
theorem cliffordRfOdd (k : ℕ) :
    Nonempty (CliffordAlgebra (Rf (2 * k + 1)) ≃ₐ[ℂ]
      (Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ × Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)) := by
  induction k with
  | zero =>
      exact ⟨equivBase.trans (AlgEquiv.prodCongr matrixOneEquiv.symm matrixOneEquiv.symm)⟩
  | succ k ih =>
      obtain ⟨g⟩ := ih
      refine ⟨?_⟩
      refine (CliffordAlgebra.equivOfIsometry (splitIso (2 * k + 1))).trans ?_
      refine (CliffordPeriodicity.periodicityEquiv (Rf (2 * k + 1))).trans ?_
      refine (AlgEquiv.mapMatrix g).trans ?_
      refine (matrixProd (Fin 2) _ _).trans ?_
      exact AlgEquiv.prodCongr
        ((Matrix.compAlgEquiv (Fin 2) (Fin (2 ^ k)) ℂ ℂ).trans
          (Matrix.reindexAlgEquiv ℂ ℂ
            (finProdFinEquiv.trans (finCongr (by ring : 2 * 2 ^ k = 2 ^ (k + 1))))))
        ((Matrix.compAlgEquiv (Fin 2) (Fin (2 ^ k)) ℂ ℂ).trans
          (Matrix.reindexAlgEquiv ℂ ℂ
            (finProdFinEquiv.trans (finCongr (by ring : 2 * 2 ^ k = 2 ^ (k + 1))))))

/-- **THE COMPLEX CLASSIFICATION IN EVERY ODD RANK.** -/
theorem clifford_iso_of_nondegenerate_odd (k : ℕ) {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V = 2 * k + 1) (Q : QuadraticForm ℂ V)
    (hQ : (QuadraticMap.associated (R := ℂ) Q).SeparatingLeft) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℂ]
      (Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ × Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) ℂ)) := by
  have e1 := QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed Q hQ
  have e2 := QuadraticForm.equivalent_weightedSumSquares_of_isAlgClosed (Rf (2 * k + 1)) (Rf_sep _)
  rw [hV] at e1
  rw [finrank_Rf_space] at e2
  obtain ⟨i1⟩ := e1
  obtain ⟨i2⟩ := e2
  obtain ⟨g⟩ := cliffordRfOdd k
  exact ⟨(CliffordAlgebra.equivOfIsometry (i1.trans i2.symm)).trans g⟩

end

end CliffordOddLadder
