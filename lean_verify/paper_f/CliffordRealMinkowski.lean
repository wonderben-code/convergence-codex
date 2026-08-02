/-
  CliffordRealMinkowski.lean — Cl(1,3;ℝ) ≅ M₂(ℍ) as a bundled ℝ-AlgEquiv

  WALL W7's own account named this construction "borderline buildable and
  the most likely of the walls to fall next". This file builds it: the REAL
  Clifford algebra of the Minkowski quadratic form of signature (1,3), in
  the mostly-minus convention Q(v) = v₀² − v₁² − v₂² − v₃², is isomorphic
  as an ℝ-algebra to the 2×2 matrices over the quaternions.

  The route mirrors `CliffordIso` (the complex case, review round 7):
  1. Explicit gamma matrices over ℍ[ℝ]:
       Γ₀ = diag(1,−1),  Γᵢ = offdiag(qᵢ, qᵢ)  for qᵢ ∈ {i, j, k},
     with the Clifford relations proven entrywise in exact quaternion
     arithmetic (Γ₀² = 1, Γᵢ² = −1, all pairs anticommute).
  2. `CliffordAlgebra.lift` on the squaring condition gives the AlgHom.
  3. Surjectivity: all sixteen ℝ-basis elements of M₂(ℍ) — the four
     matrix positions times the four quaternion units — are explicit
     (±1/2)-combinations of gamma words, each verified entrywise; a
     general matrix is reassembled by real-linear combination.
  4. Injectivity by rank: both sides have ℝ-dimension 16 — the domain by
     the same product/graded-tensor route the estate used for Cl₄(ℂ)
     (two quaternion-algebra legs of dimension 4), the codomain by
     finrank(M₂) × finrank(ℍ) = 4 × 4.

  WHAT THIS FILE PROVES (exactly this, nothing more):
  1. `quat_units` — the multiplication table of i, j, k in ℍ[ℝ], as
     explicit lemmas (i² = j² = k² = −1, ij = k and cyclic, ji = −k and
     cyclic).
  2. `gamma_sq`/`gamma_anticomm` families — the ten Clifford relations
     for the four gammas, entrywise over ℍ.
  3. `Q₁₃_apply` — the form IS v₀² − v₁² − v₂² − v₃²: signature (1,3)
     in the mostly-minus convention, displayed, not asserted.
  4. **`cliffordRealToMatrix`** — the AlgHom Cl(Q₁₃) →ₐ[ℝ] M₂(ℍ[ℝ]) via
     `CliffordAlgebra.lift`, with `cliffordRealToMatrix_ι` tracking
     generators.
  5. `cliffordReal_finrank` (= 16) and `matrix2H_finrank` (= 16).
  6. `single_unit_mem` — all sixteen basis matrices of M₂(ℍ) lie in the
     range, by the explicit combinations.
  7. **`cliffordRealMinkowskiEquiv`** — the bundled AlgEquiv
     Cl(1,3;ℝ) ≃ₐ[ℝ] M₂(ℍ[ℝ]), with generator corollaries
     `cliffordRealMinkowskiEquiv_e₀ .. _e₃`.

  NOT proven here, stated so nobody reads past the bar: the mod-8
  periodicity table of real Clifford algebras (this is ONE entry of it);
  the mostly-PLUS convention Cl(3,1;ℝ) ≅ M₄(ℝ) — a DIFFERENT algebra;
  any spin-group statement (the identification of the estate's SL₂(ℂ)
  with Mathlib's spinGroup stays open exactly as W7 records); and any
  physics. The convention dependence is real mathematics: (1,3) and
  (3,1) real Clifford algebras are NOT isomorphic, which is why the
  header fixes the form explicitly.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import Mathlib.Algebra.Quaternion
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open Matrix CliffordAlgebra
open scoped Quaternion

noncomputable section

namespace CliffordRealMinkowski

/-! ## 1. Quaternion units and their multiplication table -/

/-- The quaternion unit i. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The quaternion unit j. -/
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

/-- The quaternion unit k. -/
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem qi_sq : qi * qi = -1 := by ext <;> simp [qi]
theorem qj_sq : qj * qj = -1 := by ext <;> simp [qj]
theorem qk_sq : qk * qk = -1 := by ext <;> simp [qk]

theorem qi_mul_qj : qi * qj = qk := by ext <;> simp [qi, qj, qk]
theorem qj_mul_qi : qj * qi = -qk := by ext <;> simp [qi, qj, qk]
theorem qj_mul_qk : qj * qk = qi := by ext <;> simp [qi, qj, qk]
theorem qk_mul_qj : qk * qj = -qi := by ext <;> simp [qi, qj, qk]
theorem qk_mul_qi : qk * qi = qj := by ext <;> simp [qi, qj, qk]
theorem qi_mul_qk : qi * qk = -qj := by ext <;> simp [qi, qj, qk]

/-- Every quaternion is the real combination of the four units. -/
theorem quat_decompose (q : ℍ[ℝ]) :
    q = q.re • (1 : ℍ[ℝ]) + q.imI • qi + q.imJ • qj + q.imK • qk := by
  ext <;> simp [qi, qj, qk]

/- The ℝ-scalar action on ℍ[ℝ] is componentwise BY DEFINITION; these four
rfl lemmas keep every entry computation at the level of real arithmetic,
never quaternion division-ring arithmetic (where simp would otherwise
rewrite ↑(1/2) to the quaternion inverse (↑2)⁻¹). -/
@[simp] theorem smul_re (r : ℝ) (q : ℍ[ℝ]) : (r • q).re = r * q.re := rfl
@[simp] theorem smul_imI (r : ℝ) (q : ℍ[ℝ]) : (r • q).imI = r * q.imI := rfl
@[simp] theorem smul_imJ (r : ℝ) (q : ℍ[ℝ]) : (r • q).imJ = r * q.imJ := rfl
@[simp] theorem smul_imK (r : ℝ) (q : ℍ[ℝ]) : (r • q).imK = r * q.imK := rfl

/-! ## 2. The gamma matrices and the Clifford relations -/

/-- Γ₀ = diag(1, −1): squares to +1. -/
def Γ₀ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![1, 0; 0, -1]

/-- Γ₁ = offdiag(i, i): squares to −1. -/
def Γ₁ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![0, qi; qi, 0]

/-- Γ₂ = offdiag(j, j): squares to −1. -/
def Γ₂ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![0, qj; qj, 0]

/-- Γ₃ = offdiag(k, k): squares to −1. -/
def Γ₃ : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![0, qk; qk, 0]

section CliffordRelations

/- The Clifford relations share one uniform entrywise tactic; the
unused-argument linter is silenced for this block only, as in
`CliffordIso`. -/
set_option linter.unusedSimpArgs false

theorem Γ₀_sq : Γ₀ * Γ₀ = 1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₀, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem Γ₁_sq : Γ₁ * Γ₁ = -1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₁, qi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem Γ₂_sq : Γ₂ * Γ₂ = -1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₂, qj, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem Γ₃_sq : Γ₃ * Γ₃ = -1 := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₃, qk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem Γ₀_Γ₁_anticomm : Γ₀ * Γ₁ = -(Γ₁ * Γ₀) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₀, Γ₁, qi, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀_Γ₂_anticomm : Γ₀ * Γ₂ = -(Γ₂ * Γ₀) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₀, Γ₂, qj, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀_Γ₃_anticomm : Γ₀ * Γ₃ = -(Γ₃ * Γ₀) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₀, Γ₃, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₁_Γ₂_anticomm : Γ₁ * Γ₂ = -(Γ₂ * Γ₁) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₁, Γ₂, qi, qj, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₁_Γ₃_anticomm : Γ₁ * Γ₃ = -(Γ₃ * Γ₁) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₁, Γ₃, qi, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₂_Γ₃_anticomm : Γ₂ * Γ₃ = -(Γ₃ * Γ₂) := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₂, Γ₃, qj, qk, Matrix.mul_apply, Fin.sum_univ_two]

end CliffordRelations

section ProductLiterals

/- Gamma words in literal matrix form: each proof is a single two-matrix
entrywise computation, so the sixteen basis identities below never expand
a nested product. Uniform simp set; linters silenced as above. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem Γ₀Γ₁_eq : Γ₀ * Γ₁ = !![0, qi; -qi, 0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₀, Γ₁, qi, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀Γ₂_eq : Γ₀ * Γ₂ = !![0, qj; -qj, 0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₀, Γ₂, qj, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀Γ₃_eq : Γ₀ * Γ₃ = !![0, qk; -qk, 0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₀, Γ₃, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₂Γ₃_eq : Γ₂ * Γ₃ = !![qi, 0; 0, qi] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₂, Γ₃, qi, qj, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₃Γ₁_eq : Γ₃ * Γ₁ = !![qj, 0; 0, qj] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₁, Γ₃, qi, qj, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₁Γ₂_eq : Γ₁ * Γ₂ = !![qk, 0; 0, qk] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₁, Γ₂, qi, qj, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀Γ₂Γ₃_eq : Γ₀ * Γ₂ * Γ₃ = !![qi, 0; 0, -qi] := by
  rw [Γ₀Γ₂_eq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₃, qi, qj, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀Γ₃Γ₁_eq : Γ₀ * Γ₃ * Γ₁ = !![qj, 0; 0, -qj] := by
  rw [Γ₀Γ₃_eq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₁, qi, qj, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀Γ₁Γ₂_eq : Γ₀ * Γ₁ * Γ₂ = !![qk, 0; 0, -qk] := by
  rw [Γ₀Γ₁_eq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₂, qi, qj, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₁Γ₂Γ₃_eq : Γ₁ * Γ₂ * Γ₃ = !![0, -1; -1, 0] := by
  rw [Γ₁Γ₂_eq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₃, qi, qk, Matrix.mul_apply, Fin.sum_univ_two]

theorem Γ₀Γ₁Γ₂Γ₃_eq : Γ₀ * Γ₁ * Γ₂ * Γ₃ = !![0, -1; 1, 0] := by
  rw [Γ₀Γ₁Γ₂_eq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [Γ₃, qk, Matrix.mul_apply, Fin.sum_univ_two]

end ProductLiterals

/-! ## 3. The quadratic form of signature (1, 3) -/

/-- The Minkowski form, mostly-minus, assembled from two 2-dimensional
    legs exactly as the estate assembled Q₄ over ℂ — so the same
    product/graded-tensor dimension route applies verbatim. -/
def Q₁₃ : QuadraticForm ℝ ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (CliffordAlgebraQuaternion.Q (1 : ℝ) (-1 : ℝ)).prod
    (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ))

/-- The form IS v₀² − v₁² − v₂² − v₃²: the signature is displayed. -/
theorem Q₁₃_apply (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    Q₁₃ v = v.1.1 ^ 2 - v.1.2 ^ 2 - v.2.1 ^ 2 - v.2.2 ^ 2 := by
  simp [Q₁₃, CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply]
  ring

/-! ## 4. The representation -/

/-- The linear map v ↦ v₀Γ₀ + v₁Γ₁ + v₂Γ₂ + v₃Γ₃. -/
def cliffordRealMap :
    ((ℝ × ℝ) × (ℝ × ℝ)) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] where
  toFun v := v.1.1 • Γ₀ + v.1.2 • Γ₁ + v.2.1 • Γ₂ + v.2.2 • Γ₃
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add]
    module
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    module

section SquaringCondition

/- One uniform entrywise simp set over all 64 component branches; the
unused-argument and dead-closer linters are silenced for the block. -/
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- **The Clifford squaring condition**: (Σ vμΓμ)² = Q₁₃(v)·1. -/
theorem cliffordRealMap_sq (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordRealMap v * cliffordRealMap v = algebraMap ℝ _ (Q₁₃ v) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [cliffordRealMap, Γ₀, Γ₁, Γ₂, Γ₃, qi, qj, qk,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.add_apply, Matrix.algebraMap_matrix_apply,
      Q₁₃, CliffordAlgebraQuaternion.Q_apply, QuadraticMap.prod_apply,
      Algebra.smul_def] <;>
    ring

end SquaringCondition

/-- **The Clifford representation**: Cl(1,3;ℝ) →ₐ[ℝ] M₂(ℍ[ℝ]). -/
def cliffordRealToMatrix :
    CliffordAlgebra Q₁₃ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  CliffordAlgebra.lift Q₁₃ ⟨cliffordRealMap, cliffordRealMap_sq⟩

@[simp]
theorem cliffordRealToMatrix_ι (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordRealToMatrix (ι Q₁₃ v) = cliffordRealMap v :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-! ## 5. Both sides have dimension 16 -/

instance : Module.Finite ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (-1 : ℝ))) :=
  Module.Finite.equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

instance : Module.Free ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (-1 : ℝ))) :=
  Module.Free.of_equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

instance : Module.Finite ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ))) :=
  Module.Finite.equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

instance : Module.Free ℝ
    (CliffordAlgebra (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ))) :=
  Module.Free.of_equiv CliffordAlgebraQuaternion.equiv.symm.toLinearEquiv

/-- The positive leg Cl(⟨1,−1⟩;ℝ) has dimension 4 (it is the split
    quaternion algebra ℍ[ℝ,1,−1]). -/
theorem clifford2_pos_finrank :
    Module.finrank ℝ
      (CliffordAlgebra (CliffordAlgebraQuaternion.Q (1 : ℝ) (-1 : ℝ))) = 4 := by
  rw [LinearEquiv.finrank_eq CliffordAlgebraQuaternion.equiv.toLinearEquiv]
  exact QuaternionAlgebra.finrank_eq_four _ _ _

/-- The negative leg Cl(⟨−1,−1⟩;ℝ) has dimension 4 (it is ℍ itself). -/
theorem clifford2_neg_finrank :
    Module.finrank ℝ
      (CliffordAlgebra (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ))) = 4 := by
  rw [LinearEquiv.finrank_eq CliffordAlgebraQuaternion.equiv.toLinearEquiv]
  exact QuaternionAlgebra.finrank_eq_four _ _ _

/-- **Cl(1,3;ℝ) has dimension 16**, by the product/graded-tensor route. -/
theorem cliffordReal_finrank :
    Module.finrank ℝ (CliffordAlgebra Q₁₃) = 16 := by
  rw [show Q₁₃ = (CliffordAlgebraQuaternion.Q (1 : ℝ) (-1 : ℝ)).prod
    (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1 : ℝ)) from rfl]
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.prodEquiv _ _).toLinearEquiv]
  unfold GradedTensorProduct
  erw [Module.finrank_tensorProduct, clifford2_pos_finrank,
    clifford2_neg_finrank]

/-- M₂(ℍ[ℝ]) has dimension 16 = 4 positions × 4 quaternion units. -/
theorem matrix2H_finrank :
    Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) = 16 := by
  have h4 : Module.finrank ℝ ℍ[ℝ] = 4 := Quaternion.finrank_eq_four
  rw [Module.finrank_matrix]
  simp [h4]

/-! ## 6. Surjectivity: the sixteen basis elements of M₂(ℍ) -/

theorem Γ₀_mem : Γ₀ ∈ cliffordRealToMatrix.range := by
  refine ⟨ι Q₁₃ ((1, 0), (0, 0)), ?_⟩
  change cliffordRealToMatrix (ι Q₁₃ ((1, 0), (0, 0))) = Γ₀
  rw [cliffordRealToMatrix_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem Γ₁_mem : Γ₁ ∈ cliffordRealToMatrix.range := by
  refine ⟨ι Q₁₃ ((0, 1), (0, 0)), ?_⟩
  change cliffordRealToMatrix (ι Q₁₃ ((0, 1), (0, 0))) = Γ₁
  rw [cliffordRealToMatrix_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem Γ₂_mem : Γ₂ ∈ cliffordRealToMatrix.range := by
  refine ⟨ι Q₁₃ ((0, 0), (1, 0)), ?_⟩
  change cliffordRealToMatrix (ι Q₁₃ ((0, 0), (1, 0))) = Γ₂
  rw [cliffordRealToMatrix_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem Γ₃_mem : Γ₃ ∈ cliffordRealToMatrix.range := by
  refine ⟨ι Q₁₃ ((0, 0), (0, 1)), ?_⟩
  change cliffordRealToMatrix (ι Q₁₃ ((0, 0), (0, 1))) = Γ₃
  rw [cliffordRealToMatrix_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

private theorem m01 : Γ₀ * Γ₁ ∈ cliffordRealToMatrix.range :=
  mul_mem Γ₀_mem Γ₁_mem
private theorem m02 : Γ₀ * Γ₂ ∈ cliffordRealToMatrix.range :=
  mul_mem Γ₀_mem Γ₂_mem
private theorem m03 : Γ₀ * Γ₃ ∈ cliffordRealToMatrix.range :=
  mul_mem Γ₀_mem Γ₃_mem
private theorem m12 : Γ₁ * Γ₂ ∈ cliffordRealToMatrix.range :=
  mul_mem Γ₁_mem Γ₂_mem
private theorem m23 : Γ₂ * Γ₃ ∈ cliffordRealToMatrix.range :=
  mul_mem Γ₂_mem Γ₃_mem
private theorem m31 : Γ₃ * Γ₁ ∈ cliffordRealToMatrix.range :=
  mul_mem Γ₃_mem Γ₁_mem
private theorem m023 : Γ₀ * Γ₂ * Γ₃ ∈ cliffordRealToMatrix.range :=
  mul_mem m02 Γ₃_mem
private theorem m031 : Γ₀ * Γ₃ * Γ₁ ∈ cliffordRealToMatrix.range :=
  mul_mem m03 Γ₁_mem
private theorem m012 : Γ₀ * Γ₁ * Γ₂ ∈ cliffordRealToMatrix.range :=
  mul_mem m01 Γ₂_mem
private theorem m123 : Γ₁ * Γ₂ * Γ₃ ∈ cliffordRealToMatrix.range :=
  mul_mem m12 Γ₃_mem
private theorem m0123 : Γ₀ * Γ₁ * Γ₂ * Γ₃ ∈ cliffordRealToMatrix.range :=
  mul_mem m012 Γ₃_mem

section SixteenUnits

/- The sixteen identities: rewrite the gamma words to their literal forms,
then check entrywise at depth one. Uniform simp set; linters silenced. -/
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

private theorem E00_one_mem :
    Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℍ[ℝ])
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℍ[ℝ])
      = (1/2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) + Γ₀) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₀, Matrix.single, Matrix.one_apply] <;>
      norm_num]
  exact Subalgebra.smul_mem _ (add_mem (one_mem _) Γ₀_mem) _

private theorem E11_one_mem :
    Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℍ[ℝ])
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℍ[ℝ])
      = (1/2 : ℝ) • ((1 : Matrix (Fin 2) (Fin 2) ℍ[ℝ]) - Γ₀) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₀, Matrix.single, Matrix.one_apply] <;>
      norm_num]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _) Γ₀_mem) _

private theorem E00_qi_mem :
    Matrix.single (0 : Fin 2) (0 : Fin 2) qi
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (0 : Fin 2) qi
      = (1/2 : ℝ) • (Γ₂ * Γ₃ + Γ₀ * Γ₂ * Γ₃) by
    rw [Γ₂Γ₃_eq, Γ₀Γ₂Γ₃_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [qi, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem m23 m023) _

private theorem E11_qi_mem :
    Matrix.single (1 : Fin 2) (1 : Fin 2) qi
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (1 : Fin 2) qi
      = (1/2 : ℝ) • (Γ₂ * Γ₃ - Γ₀ * Γ₂ * Γ₃) by
    rw [Γ₂Γ₃_eq, Γ₀Γ₂Γ₃_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [qi, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem m23 m023) _

private theorem E00_qj_mem :
    Matrix.single (0 : Fin 2) (0 : Fin 2) qj
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (0 : Fin 2) qj
      = (1/2 : ℝ) • (Γ₃ * Γ₁ + Γ₀ * Γ₃ * Γ₁) by
    rw [Γ₃Γ₁_eq, Γ₀Γ₃Γ₁_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [qj, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem m31 m031) _

private theorem E11_qj_mem :
    Matrix.single (1 : Fin 2) (1 : Fin 2) qj
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (1 : Fin 2) qj
      = (1/2 : ℝ) • (Γ₃ * Γ₁ - Γ₀ * Γ₃ * Γ₁) by
    rw [Γ₃Γ₁_eq, Γ₀Γ₃Γ₁_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [qj, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem m31 m031) _

private theorem E00_qk_mem :
    Matrix.single (0 : Fin 2) (0 : Fin 2) qk
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (0 : Fin 2) qk
      = (1/2 : ℝ) • (Γ₁ * Γ₂ + Γ₀ * Γ₁ * Γ₂) by
    rw [Γ₁Γ₂_eq, Γ₀Γ₁Γ₂_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [qk, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem m12 m012) _

private theorem E11_qk_mem :
    Matrix.single (1 : Fin 2) (1 : Fin 2) qk
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (1 : Fin 2) qk
      = (1/2 : ℝ) • (Γ₁ * Γ₂ - Γ₀ * Γ₁ * Γ₂) by
    rw [Γ₁Γ₂_eq, Γ₀Γ₁Γ₂_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [qk, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem m12 m012) _

private theorem E01_qi_mem :
    Matrix.single (0 : Fin 2) (1 : Fin 2) qi
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (1 : Fin 2) qi
      = (1/2 : ℝ) • (Γ₁ + Γ₀ * Γ₁) by
    rw [Γ₀Γ₁_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₁, qi, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem Γ₁_mem m01) _

private theorem E10_qi_mem :
    Matrix.single (1 : Fin 2) (0 : Fin 2) qi
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (0 : Fin 2) qi
      = (1/2 : ℝ) • (Γ₁ - Γ₀ * Γ₁) by
    rw [Γ₀Γ₁_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₁, qi, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem Γ₁_mem m01) _

private theorem E01_qj_mem :
    Matrix.single (0 : Fin 2) (1 : Fin 2) qj
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (1 : Fin 2) qj
      = (1/2 : ℝ) • (Γ₂ + Γ₀ * Γ₂) by
    rw [Γ₀Γ₂_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₂, qj, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem Γ₂_mem m02) _

private theorem E10_qj_mem :
    Matrix.single (1 : Fin 2) (0 : Fin 2) qj
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (0 : Fin 2) qj
      = (1/2 : ℝ) • (Γ₂ - Γ₀ * Γ₂) by
    rw [Γ₀Γ₂_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₂, qj, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem Γ₂_mem m02) _

private theorem E01_qk_mem :
    Matrix.single (0 : Fin 2) (1 : Fin 2) qk
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (1 : Fin 2) qk
      = (1/2 : ℝ) • (Γ₃ + Γ₀ * Γ₃) by
    rw [Γ₀Γ₃_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₃, qk, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem Γ₃_mem m03) _

private theorem E10_qk_mem :
    Matrix.single (1 : Fin 2) (0 : Fin 2) qk
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (0 : Fin 2) qk
      = (1/2 : ℝ) • (Γ₃ - Γ₀ * Γ₃) by
    rw [Γ₀Γ₃_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Γ₃, qk, Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem Γ₃_mem m03) _

private theorem E01_one_mem :
    Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℍ[ℝ])
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℍ[ℝ])
      = -((1/2 : ℝ) • (Γ₁ * Γ₂ * Γ₃ + Γ₀ * Γ₁ * Γ₂ * Γ₃)) by
    rw [Γ₁Γ₂Γ₃_eq, Γ₀Γ₁Γ₂Γ₃_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single] <;> norm_num]
  exact neg_mem (Subalgebra.smul_mem _ (add_mem m123 m0123) _)

private theorem E10_one_mem :
    Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℍ[ℝ])
      ∈ cliffordRealToMatrix.range := by
  rw [show Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : ℍ[ℝ])
      = (1/2 : ℝ) • (Γ₀ * Γ₁ * Γ₂ * Γ₃ - Γ₁ * Γ₂ * Γ₃) by
    rw [Γ₁Γ₂Γ₃_eq, Γ₀Γ₁Γ₂Γ₃_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem m0123 m123) _

end SixteenUnits

/-- All sixteen ℝ-basis elements of M₂(ℍ) — four positions times four
    quaternion units — lie in the range. -/
theorem single_unit_mem (a b : Fin 2) :
    Matrix.single a b (1 : ℍ[ℝ]) ∈ cliffordRealToMatrix.range
      ∧ Matrix.single a b qi ∈ cliffordRealToMatrix.range
      ∧ Matrix.single a b qj ∈ cliffordRealToMatrix.range
      ∧ Matrix.single a b qk ∈ cliffordRealToMatrix.range := by
  fin_cases a <;> fin_cases b
  exacts [⟨E00_one_mem, E00_qi_mem, E00_qj_mem, E00_qk_mem⟩,
    ⟨E01_one_mem, E01_qi_mem, E01_qj_mem, E01_qk_mem⟩,
    ⟨E10_one_mem, E10_qi_mem, E10_qj_mem, E10_qk_mem⟩,
    ⟨E11_one_mem, E11_qi_mem, E11_qj_mem, E11_qk_mem⟩]

/-- A single entry with an ARBITRARY quaternion value lies in the range:
    decompose the value over the four units and use real-linearity. -/
theorem single_mem (a b : Fin 2) (q : ℍ[ℝ]) :
    Matrix.single a b q ∈ cliffordRealToMatrix.range := by
  obtain ⟨h1, hi, hj, hk⟩ := single_unit_mem a b
  rw [show q = q.re • (1 : ℍ[ℝ]) + q.imI • qi + q.imJ • qj + q.imK • qk
    from quat_decompose q]
  rw [Matrix.single_add, Matrix.single_add, Matrix.single_add,
    ← Matrix.smul_single, ← Matrix.smul_single, ← Matrix.smul_single,
    ← Matrix.smul_single]
  exact add_mem (add_mem (add_mem (Subalgebra.smul_mem _ h1 _)
    (Subalgebra.smul_mem _ hi _)) (Subalgebra.smul_mem _ hj _))
    (Subalgebra.smul_mem _ hk _)

/-- **The gammas generate M₂(ℍ)**: the representation is surjective. -/
theorem cliffordRealToMatrix_surjective :
    Function.Surjective cliffordRealToMatrix := by
  intro A
  have hA : A = ∑ i, ∑ j, Matrix.single i j (A i j) :=
    (Matrix.sum_sum_single fun i j => A i j).symm
  have hmem : A ∈ cliffordRealToMatrix.range := by
    rw [hA]
    exact sum_mem fun i _ => sum_mem fun j _ => single_mem i j (A i j)
  exact hmem

/-! ## 7. Injectivity by rank, and the isomorphism -/

/-- **Injectivity by rank**: both sides have finrank 16 and the map is
    surjective, so the kernel has finrank zero. -/
theorem cliffordRealToMatrix_injective :
    Function.Injective cliffordRealToMatrix := by
  haveI : FiniteDimensional ℝ (CliffordAlgebra Q₁₃) :=
    FiniteDimensional.of_finrank_pos (by rw [cliffordReal_finrank]; norm_num)
  have hrk := LinearMap.finrank_range_add_finrank_ker
    cliffordRealToMatrix.toLinearMap
  have hr : LinearMap.range cliffordRealToMatrix.toLinearMap = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact cliffordRealToMatrix_surjective
  rw [hr, finrank_top, matrix2H_finrank, cliffordReal_finrank] at hrk
  have hk : Module.finrank ℝ
      (LinearMap.ker cliffordRealToMatrix.toLinearMap) = 0 := by omega
  have hbot : LinearMap.ker cliffordRealToMatrix.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp hk
  exact LinearMap.ker_eq_bot.mp hbot

/-- **Cl(1,3;ℝ) ≅ M₂(ℍ)** — the W7 stair the walls file named "most
    likely to fall next", fallen: the gamma representation is an
    isomorphism of ℝ-algebras. -/
def cliffordRealMinkowskiEquiv :
    CliffordAlgebra Q₁₃ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  AlgEquiv.ofBijective cliffordRealToMatrix
    ⟨cliffordRealToMatrix_injective, cliffordRealToMatrix_surjective⟩

/-- The isomorphism IS the gamma representation on generators. -/
theorem cliffordRealMinkowskiEquiv_ι (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordRealMinkowskiEquiv (ι Q₁₃ v) = cliffordRealMap v :=
  cliffordRealToMatrix_ι v

theorem cliffordRealMinkowskiEquiv_e₀ :
    cliffordRealMinkowskiEquiv (ι Q₁₃ ((1, 0), (0, 0))) = Γ₀ := by
  rw [cliffordRealMinkowskiEquiv_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem cliffordRealMinkowskiEquiv_e₁ :
    cliffordRealMinkowskiEquiv (ι Q₁₃ ((0, 1), (0, 0))) = Γ₁ := by
  rw [cliffordRealMinkowskiEquiv_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem cliffordRealMinkowskiEquiv_e₂ :
    cliffordRealMinkowskiEquiv (ι Q₁₃ ((0, 0), (1, 0))) = Γ₂ := by
  rw [cliffordRealMinkowskiEquiv_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem cliffordRealMinkowskiEquiv_e₃ :
    cliffordRealMinkowskiEquiv (ι Q₁₃ ((0, 0), (0, 1))) = Γ₃ := by
  rw [cliffordRealMinkowskiEquiv_ι]
  simp only [cliffordRealMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

end CliffordRealMinkowski
