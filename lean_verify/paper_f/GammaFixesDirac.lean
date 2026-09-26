/-
  GammaFixesDirac.lean — with the estate's grading, CCM's three conditions on the regular bimodule
  of `M₂(ℂ)` determine the Dirac operator up to a real scale: an operator on `Hw` satisfies
  order-one, commutes with `Jprod` and anticommutes with `gammaCcm` iff it is `t • Dccm` for a real
  `t`. The witness file's docstring said the last step by hand — *"solution space two-dimensional
  over `ℝ`, spanned by `A = i·1` and `A = σ₃`"* — and this file proves it, with the `A = i·1`
  direction contributing nothing to `D`.

  SPINE L6 / `WALLS` §W9 rung 2, second half (§W9.9), completed for the estate's witness class.
  Hardening unit 170, 2026-09-20.

  WHY. Units 168 and 169 proved the first two clauses of the `Dsym` docstring's derivation:
  order-one forces `D = C ⊗ 1 + 1 ⊗ B`, and `JDJ = D` then forces `D = A ⊗ 1 + 1 ⊗ Ā` for a free
  `A`. The third clause is the grading. Reading `Dγ = −γD` at three entries of the `4 × 4`
  identity gives `A₀₁ = i Ā₁₀` and `Ā₁₀ i = −A₀₁` — so `2i Ā₁₀ = 0` and both off-diagonal entries
  vanish — and `A₀₀ + Ā₁₁ = −Ā₁₁ − A₀₀`, so `A₁₁ = −Ā₀₀`. Hence
  `A = diag(a, −ā) = (Re a) σ₃ + i (Im a) 1`, and `A ⊗ 1 + 1 ⊗ Ā = (Re a)(σ₃ ⊗ 1 + 1 ⊗ σ₃) =
  (Re a) • Dsym`: the imaginary part of `a` is exactly
  the fibre of `A ↦ D` that unit 169 left unstated, and it drops out. Conversely `t • Dccm`
  satisfies all three conditions, each by linearity from `Dccm`'s own. So on this space the
  Dirac operator is not chosen: given the algebra action, the real structure and the grading, it
  is `Dccm` up to one real number.

  WHAT IS PROVED.
  * `piW_add_piOpW_star_eq` — the matrix of `piW A + piOpW (op (star A))` is `A ⊗ 1 + 1 ⊗ Ā`;
    `anticomm_gammaCcm_iff` — anticommutation with `gammaCcm` as the matrix identity
    `M γ = −γ M`.
  * **`entries_of_anticomm`** — for `M = A ⊗ 1 + 1 ⊗ Ā`, `Mγ = −γM` gives `A₀₁ = 0`, `A₁₀ = 0`,
    `A₁₁ = −Ā₀₀` (three entries of the identity; `2i ≠ 0`).
  * **`kron_eq_re_smul_Dsym`** — under those three equations `A ⊗ 1 + 1 ⊗ Ā = (Re A₀₀) • Dsym`
    (sixteen entries, `fin_cases`).
  * `lie_smul_left`; **`ccm_fixes_dirac`** — order-one ∧ `Jprod`-invariance ∧
    `gammaCcm`-anticommutation ⟺ `∃ t : ℝ, D = (t : ℂ) • Dccm`.
  * `Dsym_star`, `Dccm_selfAdjoint` — the fixed operator is self-adjoint.

  WHAT IS **NOT** PROVED, said exactly.
  * That `gammaCcm` is the only grading. `RealSpectralWitness` found four monomial `γ`s and took
    one; the theorem is for THAT `γ`. For a different admissible grading the solution set could
    differ, and nothing here says how.
  * Anything off the regular bimodule of `M₂(ℂ)`: CCM's conditions on `A_F` acting on `H_F`, a
    factor list, `n ≠ 2`, real or quaternionic factors — none of it. The wall does not move; the
    witness class is, however, now completely understood: `π` fixes the star (unit 166),
    order-one fixes the shape (168), `J` fixes the second factor (169), `γ` fixes everything but a
    real scale (this unit).
    ⚠ 26 September 2026 (hardening unit 228, `paper_f/OrderOneBlockDiagonal.lean`): off
    the one factor, order-one alone is solved for a product of matrix algebras with every pair of
    factors once (`OrderOneBlockDiagonal.orderOne_iff`); `J`, `γ`, multiplicities, the choice of
    CCM's factor list and real or quaternionic factors are not.
    ⚠ 26 September 2026 (hardening unit 230, `paper_f/OrderOneRealBlock.lean`): `J` on
    such a product is done there (`OrderOneRealBlock.orderOne_exchConj_iff`); `γ` is not.
    ⚠ 26 September 2026 (hardening unit 232, `paper_f/OrderOneCommutant.lean`): order-one
    alone with multiplicities and on sub-bimodules, `ℍ` inside `M₂(ℂ)` among the test sets, is
    written there in commutant form (`OrderOneCommutant.orderOne_iff_commutant`) and computed for
    full matrix algebras with a multiplicity (`orderOne_multiplicity_iff`); the other
    commutants, `J`, `γ` and the factor list are not.
    ⚠ 26 September 2026 (hardening unit 234, `paper_f/OrderOneRealGenerations.lean`): `J`
    with a generation index, for one full matrix factor, is done there
    (`OrderOneRealGenerations.orderOne_exchConjGen_iff`); `γ` and the factor list are not.
  * What the scale `t` means (a mass, a sign); `Dccm` IS self-adjoint (`Dccm_selfAdjoint`), so
    `t • Dccm` is, but nothing is said about its spectrum.
    ⚠ 26 September 2026 (unit 229, `ERRATUM 698`): in part, by unit 172 the same day:
    `Dsym`, whose `matAlg` is `Dccm`, is the diagonal matrix with entries `2, 0, 0, −2`
    (`OrderOneCutoffFactorises.Dsym_eq_diagonal`). The spectrum of `t • Dccm` as Mathlib's
    `spectrum` is not stated, and what `t` means stands. Kept as written (`ERRATUM 94`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import JSelectsDirac

open Matrix RealSpectralWitness OrderOneNontrivial SpectralTripleBimodule OppositeFromRealStructure
  JSelectsDirac OrderOneRegularBimodule EvenGradingObstruction MulOpposite ConjugatePermutation
open scoped Kronecker

namespace GammaFixesDirac

/-- The matrix of `piW A + piOpW (op (star A))`: `A ⊗ 1 + 1 ⊗ Ā`. -/
theorem piW_add_piOpW_star_eq (A : Matrix (Fin 2) (Fin 2) ℂ) :
    piW A + piOpW (op (star A))
      = matAlg Slots (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
          + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A.map (starRingEnd ℂ)) := by
  change matAlg Slots (kronLeft (Fin 2) (Fin 2) A)
    + matAlg Slots (kronRight (Fin 2) (Fin 2) (op (star A))) = _
  rw [← map_add]; congr 1

/-- Anticommutation with `gammaCcm`, as a matrix identity. -/
theorem anticomm_gammaCcm_iff (M : Matrix Slots Slots ℂ) :
    matAlg Slots M * gammaCcm = -(gammaCcm * matAlg Slots M) ↔ M * gammaMat = -(gammaMat * M) := by
  rw [gammaCcm, ← map_mul, ← map_mul, ← map_neg]
  exact (matAlg_injective Slots).eq_iff

/-- **The three equations `Dγ = −γD` imposes on `A`**: off-diagonal zero, `A₁₁ = −Ā₀₀`. -/
theorem entries_of_anticomm (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
          + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A.map (starRingEnd ℂ)) * gammaMat
      = -(gammaMat * (A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
          + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A.map (starRingEnd ℂ)))) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = -(starRingEnd ℂ) (A 0 0) := by
  have e3 := congrFun (congrFun h (0, 0)) (1, 0)
  have e9 := congrFun (congrFun h (0, 1)) (1, 1)
  have e5 := congrFun (congrFun h (0, 1)) (0, 1)
  simp only [gammaMat, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.add_apply,
    Matrix.neg_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply,
    Matrix.map_apply] at e3 e9 e5
  simp only [Fin.isValue, ↓reduceIte, mul_one, one_mul, Prod.mk.injEq, zero_ne_one, and_false,
    one_ne_zero, and_self, and_true, mul_zero, zero_add, add_zero, zero_mul, mul_neg, neg_inj,
    neg_add_rev] at e3 e9 e5
  have h2 : (2 * Complex.I) * (starRingEnd ℂ) (A 1 0) = 0 := by linear_combination e9 - e3
  have hc : (starRingEnd ℂ) (A 1 0) = 0 :=
    (mul_eq_zero.mp h2).resolve_left (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  have h10 : A 1 0 = 0 := (map_eq_zero _).mp hc
  refine ⟨?_, h10, ?_⟩
  · rw [e3, hc, mul_zero]
  · have h5 : (starRingEnd ℂ) (A 1 1) = -A 0 0 := by linear_combination e5 / 2
    have := congrArg (starRingEnd ℂ) h5
    simpa using this

/-- With those three equations, `A ⊗ 1 + 1 ⊗ Ā = (Re A₀₀) • Dsym`. -/
theorem kron_eq_re_smul_Dsym (A : Matrix (Fin 2) (Fin 2) ℂ) (h01 : A 0 1 = 0) (h10 : A 1 0 = 0)
    (h11 : A 1 1 = -(starRingEnd ℂ) (A 0 0)) :
    A ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ A.map (starRingEnd ℂ)
      = ((A 0 0).re : ℂ) • Dsym := by
  ext ⟨i, p⟩ ⟨k, q⟩
  fin_cases i <;> fin_cases p <;> fin_cases k <;> fin_cases q <;>
    simp [Dsym, pauli3, kroneckerMap_apply, h01, h10, h11, Complex.ext_iff, mul_add]

/-- A scalar comes out of a commutator. -/
theorem lie_smul_left (t : ℂ) (x y : Module.End ℂ Hw) : ⁅t • x, y⁆ = t • ⁅x, y⁆ := by
  simp only [Ring.lie_def, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- **CCM'S THREE CONDITIONS FIX THE DIRAC OPERATOR UP TO A REAL SCALE.** On `Hw` with the estate's
`piW`, `piOpW`, `Jprod`, `gammaCcm`: an operator satisfies order-one, commutes with `Jprod` and
anticommutes with `gammaCcm` iff it is a real multiple of `Dccm`. -/
theorem ccm_fixes_dirac (D : Module.End ℂ Hw) :
    ((∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
        ⁅⁅D, piW a⁆, piOpW b⁆ = 0) ∧ (∀ v : Hw, Jprod (D (Jprod v)) = D v)
      ∧ D * gammaCcm = -(gammaCcm * D)) ↔ ∃ t : ℝ, D = (t : ℂ) • Dccm := by
  constructor
  · rintro ⟨h1, hJ, hγ⟩
    obtain ⟨A, rfl⟩ := (orderOne_jInv_iff D).mp ⟨h1, hJ⟩
    rw [piW_add_piOpW_star_eq] at hγ ⊢
    obtain ⟨h01, h10, h11⟩ := entries_of_anticomm A ((anticomm_gammaCcm_iff _).mp hγ)
    refine ⟨(A 0 0).re, ?_⟩
    rw [kron_eq_re_smul_Dsym A h01 h10 h11, map_smul]
    rfl
  · rintro ⟨t, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      rw [lie_smul_left, lie_smul_left, Dccm_orderOne_jInv.1 a b, smul_zero]
    · intro v
      rw [LinearMap.smul_apply, LinearMap.smul_apply]
      change conjPerm prodSwap ((t : ℂ) • Dccm (conjPerm prodSwap v)) = _
      rw [conjPerm_conj_smul, Complex.conj_ofReal]
      congr 1
      exact Dccm_orderOne_jInv.2 v
    · rw [smul_mul_assoc, mul_smul_comm, Dccm_anticomm_gammaCcm, smul_neg]

/-- `Dsym` is Hermitian: `σ₃` is, and the Kronecker sum of Hermitian matrices is. -/
theorem Dsym_star : star Dsym = Dsym := by
  ext ⟨i, p⟩ ⟨k, q⟩
  fin_cases i <;> fin_cases p <;> fin_cases k <;> fin_cases q <;>
    simp [Dsym, pauli3, kroneckerMap_apply]

/-- **`Dccm` is self-adjoint** for the inner product of `Hw`, so the real scale `t` of
`ccm_fixes_dirac` multiplies a self-adjoint operator. -/
theorem Dccm_selfAdjoint (u v : Hw) : inner ℂ (Dccm u) v = inner ℂ u (Dccm v) := by
  rw [Dccm, matAlg_star, Dsym_star]

end GammaFixesDirac
