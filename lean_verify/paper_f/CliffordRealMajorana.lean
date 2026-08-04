/-
  CliffordRealMajorana.lean — the mostly-PLUS real Clifford algebra
  Cl(3,1;ℝ): a real 4×4 Majorana representation, with the dimensions
  matched. STAGE 1 of the W7 twin.

  `CliffordRealMinkowski` proved Cl(1,3;ℝ) ≅ M₂(ℍ) at the mostly-MINUS
  form. WALLS.md's W7 account names the mostly-PLUS twin
  Cl(3,1;ℝ) ≅ M₄(ℝ) as the next stair and maps its route; this file
  takes the first half of that route.

  WHAT THIS FILE PROVES (exactly this, nothing more):
  1. `mgamma_sq` family — the four real 4×4 Majorana gammas square
     correctly: Γ₀² = −1 (the ONE timelike direction) and Γ₁² = Γ₂² =
     Γ₃² = +1. Entrywise in exact real arithmetic.
  2. `mgamma_anticomm` family — all six pairs anticommute.
  3. `Q₃₁_apply` — the form IS −v₀² + v₁² + v₂² + v₃²: signature (3,1),
     mostly-plus, displayed rather than asserted. `Q₃₁_indefinite`
     gives it teeth (it takes a strictly negative value on the time
     direction and strictly positive ones on all three space
     directions, so no definite form satisfies the same identity).
  4. **`cliffordMajoranaToMatrix`** — the AlgHom Cl(Q₃₁) →ₐ[ℝ] M₄(ℝ)
     via `CliffordAlgebra.lift`, with `cliffordMajoranaToMatrix_ι`
     tracking generators.
  5. `cliffordMajorana_finrank` (= 16) and `matrix4R_finrank` (= 16),
     hence **`majorana_dimensions_match`**.

  NOT proven here, stated plainly so nobody reads past the bar: THIS
  FILE DOES NOT CLAIM AN ISOMORPHISM. A dimension-matched algebra map
  is not an iso — surjectivity is a separate obligation and is stage 2
  of this unit (the route is in WALLS.md W7: generate M₂⊗1 and 1⊗M₂
  separately, then every Kronecker product, then the matrix units as
  quarter-combinations). Until that lands, the honest statement is
  exactly what item 5 says: a representation whose source and target
  have the same dimension. Also NOT here: the mod-8 periodicity table;
  the non-isomorphism of Cl(1,3;ℝ) and Cl(3,1;ℝ) (a cited fact, and
  separating M₂(ℍ) from M₄(ℝ) needs its own invariant — see W7); any
  spin-group statement; any physics.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Matrix CliffordAlgebra

noncomputable section

namespace CliffordRealMajorana

/-! ## 1. The real Majorana gamma matrices

Built as Kronecker products of the real 2×2 matrices
σ₁ = !![0,1;1,0], σ₃ = !![1,0;0,−1] and ε = !![0,1;−1,0]:
Γ₀ = ε⊗σ₁ (squares to −1), Γ₁ = σ₁⊗I, Γ₂ = σ₃⊗I, Γ₃ = ε⊗ε (each
squaring to +1). Written out as explicit 4×4 literals so every
identity below is a finite real computation. -/

/-- Γ₀ = ε ⊗ σ₁: the timelike gamma, squaring to −1. -/
def mΓ₀ : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,0,1; 0,0,1,0; 0,-1,0,0; -1,0,0,0]

/-- Γ₁ = σ₁ ⊗ I: squares to +1. -/
def mΓ₁ : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

/-- Γ₂ = σ₃ ⊗ I: squares to +1. -/
def mΓ₂ : Matrix (Fin 4) (Fin 4) ℝ := !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

/-- Γ₃ = ε ⊗ ε: squares to +1. -/
def mΓ₃ : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,0,1; 0,0,-1,0; 0,-1,0,0; 1,0,0,0]

section CliffordRelations

/- The ten Clifford relations share one uniform entrywise tactic; the
unused-argument linter is silenced for this block only, as in
`CliffordIso` and `CliffordRealMinkowski`. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem mΓ₀_sq : mΓ₀ * mΓ₀ = -1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₀, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem mΓ₁_sq : mΓ₁ * mΓ₁ = 1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₁, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem mΓ₂_sq : mΓ₂ * mΓ₂ = 1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₂, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem mΓ₃_sq : mΓ₃ * mΓ₃ = 1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₃, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem mΓ₀_mΓ₁_anticomm : mΓ₀ * mΓ₁ = -(mΓ₁ * mΓ₀) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₀, mΓ₁, Matrix.mul_apply, Fin.sum_univ_four]

theorem mΓ₀_mΓ₂_anticomm : mΓ₀ * mΓ₂ = -(mΓ₂ * mΓ₀) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₀, mΓ₂, Matrix.mul_apply, Fin.sum_univ_four]

theorem mΓ₀_mΓ₃_anticomm : mΓ₀ * mΓ₃ = -(mΓ₃ * mΓ₀) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₀, mΓ₃, Matrix.mul_apply, Fin.sum_univ_four]

theorem mΓ₁_mΓ₂_anticomm : mΓ₁ * mΓ₂ = -(mΓ₂ * mΓ₁) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₁, mΓ₂, Matrix.mul_apply, Fin.sum_univ_four]

theorem mΓ₁_mΓ₃_anticomm : mΓ₁ * mΓ₃ = -(mΓ₃ * mΓ₁) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₁, mΓ₃, Matrix.mul_apply, Fin.sum_univ_four]

theorem mΓ₂_mΓ₃_anticomm : mΓ₂ * mΓ₃ = -(mΓ₃ * mΓ₂) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₂, mΓ₃, Matrix.mul_apply, Fin.sum_univ_four]

end CliffordRelations

/-! ## 2. The mostly-plus form of signature (3,1) -/

/-- The Minkowski form in the mostly-PLUS convention, assembled from
    the same two quaternion-algebra legs the estate uses elsewhere —
    so the dimension computation transports verbatim — but with the
    MINUS on the first coordinate. -/
def Q₃₁ : QuadraticForm ℝ ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (CliffordAlgebraQuaternion.Q (-1 : ℝ) (1 : ℝ)).prod
    (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))

/-- The form IS −v₀² + v₁² + v₂² + v₃². -/
theorem Q₃₁_apply (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    Q₃₁ v = -v.1.1 ^ 2 + v.1.2 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by
  simp [Q₃₁, CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply]
  ring

/-- **The form is genuinely indefinite**, with exactly the opposite
    sign pattern to `CliffordRealMinkowski.Q₁₃`: strictly negative on
    the time direction, strictly positive on all three space
    directions. The identity alone would not rule out a definite
    form; this does. -/
theorem Q₃₁_indefinite :
    Q₃₁ ((1, 0), (0, 0)) < 0 ∧ 0 < Q₃₁ ((0, 1), (0, 0))
      ∧ 0 < Q₃₁ ((0, 0), (1, 0)) ∧ 0 < Q₃₁ ((0, 0), (0, 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Q₃₁_apply] <;> norm_num

/-! ## 3. The representation -/

/-- v ↦ v₀Γ₀ + v₁Γ₁ + v₂Γ₂ + v₃Γ₃, with v₀ the timelike coordinate. -/
def cliffordMajoranaMap :
    ((ℝ × ℝ) × (ℝ × ℝ)) →ₗ[ℝ] Matrix (Fin 4) (Fin 4) ℝ where
  toFun v := v.1.1 • mΓ₀ + v.1.2 • mΓ₁ + v.2.1 • mΓ₂ + v.2.2 • mΓ₃
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    module
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    module

section SquaringCondition

/- One uniform entrywise simp set over all sixteen component branches;
linters silenced for the block. -/
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-- **The Clifford squaring condition**: (Σ vμΓμ)² = Q₃₁(v)·1. -/
theorem cliffordMajoranaMap_sq (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordMajoranaMap v * cliffordMajoranaMap v = algebraMap ℝ _ (Q₃₁ v) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cliffordMajoranaMap, mΓ₀, mΓ₁, mΓ₂, mΓ₃,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.smul_apply,
      Matrix.add_apply, Matrix.algebraMap_matrix_apply,
      Q₃₁, CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply,
      smul_eq_mul] <;>
    ring

end SquaringCondition

/-- **The Majorana representation**: Cl(3,1;ℝ) →ₐ[ℝ] M₄(ℝ). -/
def cliffordMajoranaToMatrix :
    CliffordAlgebra Q₃₁ →ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  CliffordAlgebra.lift Q₃₁ ⟨cliffordMajoranaMap, cliffordMajoranaMap_sq⟩

@[simp]
theorem cliffordMajoranaToMatrix_ι (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordMajoranaToMatrix (ι Q₃₁ v) = cliffordMajoranaMap v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-! ## 4. Both sides have dimension 16 -/

instance : Module.Finite ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (-1 : ℝ) (1 : ℝ))) :=
  Module.Finite.equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

instance : Module.Free ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (-1 : ℝ) (1 : ℝ))) :=
  Module.Free.of_equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

instance : Module.Finite ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))) :=
  Module.Finite.equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

instance : Module.Free ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))) :=
  Module.Free.of_equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

/-- The timelike leg Cl(⟨−1,1⟩;ℝ) has dimension 4. -/
theorem clifford2_time_finrank :
    Module.finrank ℝ
      (CliffordAlgebra (CliffordAlgebraQuaternion.Q (-1 : ℝ) (1 : ℝ))) = 4 := by
  rw [LinearEquiv.finrank_eq CliffordAlgebraQuaternion.equiv.toLinearEquiv]
  exact QuaternionAlgebra.finrank_eq_four _ _ _

/-- The spacelike leg Cl(⟨1,1⟩;ℝ) has dimension 4. -/
theorem clifford2_space_finrank :
    Module.finrank ℝ
      (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ))) = 4 := by
  rw [LinearEquiv.finrank_eq CliffordAlgebraQuaternion.equiv.toLinearEquiv]
  exact QuaternionAlgebra.finrank_eq_four _ _ _

/-- **Cl(3,1;ℝ) has dimension 16**, by the product/graded-tensor route. -/
theorem cliffordMajorana_finrank :
    Module.finrank ℝ (CliffordAlgebra Q₃₁) = 16 := by
  rw [show Q₃₁ = (CliffordAlgebraQuaternion.Q (-1 : ℝ) (1 : ℝ)).prod
    (CliffordAlgebraQuaternion.Q (1 : ℝ) (1 : ℝ)) from rfl]
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.prodEquiv _ _).toLinearEquiv]
  unfold GradedTensorProduct
  erw [Module.finrank_tensorProduct, clifford2_time_finrank,
    clifford2_space_finrank]

/-- M₄(ℝ) has dimension 16. -/
theorem matrix4R_finrank :
    Module.finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) = 16 := by
  simp [Module.finrank_matrix]

/-- **The dimensions match** — and that is ALL this stage claims. A
    dimension-matched algebra map is not an isomorphism: surjectivity
    is a separate obligation (stage 2, route in WALLS.md W7). Stated
    as its own theorem so the gap is visible rather than implied. -/
theorem majorana_dimensions_match :
    Module.finrank ℝ (CliffordAlgebra Q₃₁)
      = Module.finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [cliffordMajorana_finrank, matrix4R_finrank]

end CliffordRealMajorana
