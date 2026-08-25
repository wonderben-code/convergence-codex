/-
  CliffordRealEuclid4.lean — the missing base case on `p − q ≡ 4 (mod 8)`, stage 1.

  WHY THIS SIGNATURE AND NOT ANOTHER. `WALLS §W7` is closed except the mod-8 periodicity table, and
  `UNLOCK_WATCHLIST` records the reach as `p − q ≡ 0, 1, 2, 5, 6, 7` with **`≡ 4` alone** left after
  `CliffordRealPauli.equivPauli` took `≡ 3` on 18 August. `(4,0)` has `p − q = 4`, and two rows of
  `F1_7_SpacetimeForced.signature_determination` — `Cl(4,0) ≅ M₂(ℍ)` and `Cl(0,4) ≅ M₂(ℍ)` — are
  exactly what that missing base case blocks. **The splitting technique that took `≡ 1` and `≡ 5`
  provably cannot reach here**: `Cl(4,0)` is simple, so there is no central idempotent to split on.
  What is left is to build a representation and check it, as `CliffordRealMinkowski` and
  `CliffordRealMajorana` did.

  **THE GENERATORS ARE THE MINKOWSKI ONES WITH TWO SIGNS MOVED, AND THAT IS THE WHOLE IDEA.**
  `CliffordRealMinkowski` puts `Γ₁ = !![0, qi; qi, 0]`, whose square is `-1`. Moving one sign gives
  `E₂ = !![0, qi; -qi, 0]`, whose square is `+1`, because `qi * (-qi) = -qi² = 1`. Doing that twice
  and replacing the remaining `qk` row by the plain swap `!![0,1;1,0]` turns signature `(1,3)` into
  `(4,0)` **inside the same algebra `M₂(ℍ)`** — which is the content of the two table rows: the
  Lorentzian and Euclidean forms in four dimensions give the *same* algebra.

  WHAT THIS FILE IS AND IS NOT. It builds the form, the four generators, their sixteen relations,
  the linear map, the Clifford squaring condition, the lift, and the dimension count on both sides.
  **It does not prove the map surjective and does not produce the `AlgEquiv`** — in the Minkowski
  template that is the file's second half and by far its longer one. Not attempted here, cost not
  claimed (`ERRATUM 246`). **So `p − q ≡ 4` is not yet reached and `W7`'s table is unchanged**: this
  is the base of the missing base case, not the base case.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import CliffordRealMinkowski

namespace CliffordRealEuclid4

open Matrix CliffordAlgebra
open scoped Quaternion
open CliffordRealMinkowski

/-! ## 1. The positive definite form in four variables -/

/-- `v₀² + v₁² + v₂² + v₃²`, built as a product of two quaternionic forms so that the Clifford
algebra's dimension comes from Mathlib's own equivalence rather than from a basis count. -/
def Q₄₀ : QuadraticForm ℝ ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ)).prod
    (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))

theorem Q₄₀_apply (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    Q₄₀ v = v.1.1 ^ 2 + v.1.2 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  simp [Q₄₀, CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply]
  ring

/-- **The form is positive definite**, which is the sharp statement here and the mirror of
`CliffordRealMinkowski.Q₁₃_indefinite`: there, the point was that the form is genuinely indefinite;
here it is that no direction is negative. Signature `(4,0)` with teeth. -/
theorem Q₄₀_pos (v : (ℝ × ℝ) × (ℝ × ℝ)) (hv : v ≠ 0) : 0 < Q₄₀ v := by
  rw [Q₄₀_apply]
  rcases eq_or_ne v.1.1 0 with h1 | h1
  · rcases eq_or_ne v.1.2 0 with h2 | h2
    · rcases eq_or_ne v.2.1 0 with h3 | h3
      · rcases eq_or_ne v.2.2 0 with h4 | h4
        · exact absurd (Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)) hv
        · positivity
      · positivity
    · positivity
  · positivity

/-! ## 2. Four generators of `M₂(ℍ)`, each squaring to `+1` -/

/-- Unchanged from the Minkowski file: the diagonal generator already squares to `+1`. -/
def E₀ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![1, 0; 0, -1]

/-- The plain swap. It replaces Minkowski's `Γ₃`, and it is the one generator carrying no
quaternion at all. -/
def E₁ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![0, 1; 1, 0]

/-- Minkowski's `Γ₁` with the lower-left sign flipped: `qi * (-qi) = 1`. -/
def E₂ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![0, qi; -qi, 0]

/-- Minkowski's `Γ₂`, flipped the same way. -/
def E₃ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![0, qj; -qj, 0]

section Relations
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

theorem E₀_sq : E₀ * E₀ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [E₀, Matrix.mul_apply, Fin.sum_univ_two]

theorem E₁_sq : E₁ * E₁ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [E₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem E₂_sq : E₂ * E₂ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₂, qi, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> all_goals simp

theorem E₃_sq : E₃ * E₃ = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₃, qj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> all_goals simp

theorem E₀_E₁_anticomm : E₀ * E₁ = -(E₁ * E₀) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₀, E₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem E₀_E₂_anticomm : E₀ * E₂ = -(E₂ * E₀) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₀, E₂, qi, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> all_goals simp

theorem E₀_E₃_anticomm : E₀ * E₃ = -(E₃ * E₀) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₀, E₃, qj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> all_goals simp

theorem E₁_E₂_anticomm : E₁ * E₂ = -(E₂ * E₁) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₁, E₂, qi, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> all_goals simp

theorem E₁_E₃_anticomm : E₁ * E₃ = -(E₃ * E₁) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₁, E₃, qj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> all_goals simp

theorem E₂_E₃_anticomm : E₂ * E₃ = -(E₃ * E₂) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [E₂, E₃, qi, qj, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> all_goals simp

end Relations

/-! ## 3. The representation -/

def euclidMap :
    ((ℝ × ℝ) × (ℝ × ℝ)) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] where
  toFun v := v.1.1 • E₀ + v.1.2 • E₁ + v.2.1 • E₂ + v.2.2 • E₃
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    module
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    module

section SquaringCondition
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- **The Clifford squaring condition**: `(Σ vμEμ)² = Q₄₀(v)·1`. -/
theorem euclidMap_sq (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    euclidMap v * euclidMap v = algebraMap ℝ _ (Q₄₀ v) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [euclidMap, E₀, E₁, E₂, E₃, qi, qj, qk,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.algebraMap_matrix_apply,
      Q₄₀, CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply,
      Algebra.smul_def] <;>
    ring

end SquaringCondition

/-- **The Clifford representation**: `Cl(4,0;ℝ) →ₐ[ℝ] M₂(ℍ[ℝ])`. -/
noncomputable def euclidToMatrix :
    CliffordAlgebra Q₄₀ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  CliffordAlgebra.lift Q₄₀ ⟨euclidMap, euclidMap_sq⟩

@[simp]
theorem euclidToMatrix_ι (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    euclidToMatrix (ι Q₄₀ v) = euclidMap v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-! ## 4. Both sides have dimension 16

The count is the same one `CliffordRealMinkowski` makes, with `Q 1 1` in place of its two legs — and
that both legs are now the **same** form is the arithmetic behind "the Lorentzian and Euclidean
forms in four dimensions give the same algebra". `M₂(ℍ)`'s side is quoted from that file rather than
re-proved. -/

instance : Module.Finite ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))) :=
  Module.Finite.equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

instance : Module.Free ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))) :=
  Module.Free.of_equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

/-- Each leg `Cl(⟨1,1⟩;ℝ)` has dimension 4 — it is the split quaternion algebra `ℍ[ℝ,1,1]`. -/
theorem clifford2_euclid_finrank :
    Module.finrank ℝ
      (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))) = 4 := by
  rw [LinearEquiv.finrank_eq CliffordAlgebraQuaternion.equiv.toLinearEquiv]
  exact QuaternionAlgebra.finrank_eq_four _ _ _

/-- **Cl(4,0;ℝ) has dimension 16**, by the same product route the Minkowski file uses. -/
theorem cliffordEuclid_finrank :
    Module.finrank ℝ (CliffordAlgebra Q₄₀) = 16 := by
  rw [show Q₄₀ = (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ)).prod
    (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ)) from rfl]
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.prodEquiv _ _).toLinearEquiv]
  unfold GradedTensorProduct
  erw [Module.finrank_tensorProduct, clifford2_euclid_finrank]

/-- **The two sides have equal dimension**, which is what makes surjectivity and injectivity
equivalent for `euclidToMatrix` — and therefore what the remaining half of this base case has to
exploit. -/
theorem finrank_eq :
    Module.finrank ℝ (CliffordAlgebra Q₄₀)
      = Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) := by
  rw [cliffordEuclid_finrank, CliffordRealMinkowski.matrix2H_finrank]

end CliffordRealEuclid4
