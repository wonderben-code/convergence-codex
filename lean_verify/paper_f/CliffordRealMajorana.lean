/-
  CliffordRealMajorana.lean — Cl(3,1;ℝ) ≅ M₄(ℝ) as a bundled ℝ-AlgEquiv:
  the mostly-PLUS twin, via a real 4×4 Majorana representation.

  `CliffordRealMinkowski` proved Cl(1,3;ℝ) ≅ M₂(ℍ) at the mostly-MINUS
  form. WALLS.md's W7 account names the mostly-PLUS twin
  Cl(3,1;ℝ) ≅ M₄(ℝ) as the next stair and maps its route; this file
  walks it. Both Minkowski conventions are now isomorphism theorems
  rather than one theorem and one citation.

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
     hence `majorana_dimensions_match` — kept as its own theorem
     because a dimension match is NOT an isomorphism, and the file was
     first landed green at exactly that bar, before surjectivity
     existed.
  6. `single_mem` — all sixteen matrix units of M₄(ℝ) lie in the
     range, hence **`cliffordMajoranaToMatrix_surjective`**. The route
     is the one WALLS.md W7 maps: the range contains four
     row-projectors e·⊗1 and four column-projectors 1⊗e·, and every
     matrix unit is ONE product of one of each — so no nested gamma
     word is ever expanded.
  7. **`cliffordMajoranaEquiv`** — the bundled AlgEquiv
     Cl(3,1;ℝ) ≃ₐ[ℝ] M₄(ℝ) (injectivity by rank at equal finrank 16),
     with generator corollaries `cliffordMajoranaEquiv_e₀ .. _e₃`.
  8. `Q₃₁_eq_neg_Q₁₃` and `Q₃₁_ne_Q₁₃` — this file's form is the exact
     pointwise negative of `CliffordRealMinkowski.Q₁₃`, and differs
     from it at all four coordinate directions. So "the two Minkowski
     conventions" is a proven relation between the two isomorphism
     theorems, not a turn of phrase. (Added folding review round 12,
     which had checked it only in the probe.)

  NOT proven here, stated plainly so nobody reads past the bar: the
  mod-8 periodicity table (Cl(1,3) and Cl(3,1) are two of its
  entries, not the table); any spin-group statement; any physics. And
  the one a reader is most likely to supply for themselves: having
  Cl(1,3;ℝ) ≅ M₂(ℍ) and Cl(3,1;ℝ) ≅ M₄(ℝ) side by side does NOT
  prove the two Clifford algebras inequivalent — that needs
  M₂(ℍ) ≇ M₄(ℝ), which is not implied by the two isomorphisms and is
  not proven in this file. It IS proven in the estate:
  `IdempotentRankInvariant` supplies the invariant W7 named (the count
  of pairwise-orthogonal nonzero idempotents summing to 1) and derives
  **`clifford13_not_ringEquiv_clifford31`**. The non-implication above
  stands as stated; what has changed is that the missing half now
  exists elsewhere rather than nowhere.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms (all 51 public declarations probed at review round 12). That
  round also ran seven corruption tests — Γ₀ squaring to +1, Γ₁ to −1,
  the gammas commuting, a sign-flipped projector, a mismatched
  projector pairing, the form being positive semidefinite, the form
  being the mostly-minus one — each stated as a NEGATION and proven,
  so the file's uniform entrywise tactics are certified unable to
  prove the corrupted variants.
-/

import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs
import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import CliffordRealMinkowski

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

/-- **The dimensions match** — kept as its own theorem because a
    dimension-matched algebra map is NOT an isomorphism. This file was
    first landed green stopping exactly here, with surjectivity still
    owed; §5–6 below discharge that obligation. The theorem stays so a
    reader can see which step supplies which half. -/
theorem majorana_dimensions_match :
    Module.finrank ℝ (CliffordAlgebra Q₃₁)
      = Module.finrank ℝ (Matrix (Fin 4) (Fin 4) ℝ) := by
  rw [cliffordMajorana_finrank, matrix4R_finrank]

/-! ## 5. Surjectivity (stage 2)

The route from WALLS.md W7, which avoids expanding sixteen nested
gamma words. Writing the gammas as Kronecker products, the range
contains σ₁⊗I and σ₃⊗I outright, and two short words supply I⊗σ₁ and
I⊗σ₃. Halving sums of those gives the FOUR row-projectors e·⊗I and
the FOUR column-projectors I⊗e·, and every one of the sixteen matrix
units is a single product of one of each — depth one, not four. -/

section Surjectivity

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

/-- ε⊗I, up to sign: the third element of M₂⊗I. -/
theorem mΓ₁mΓ₂_eq :
    mΓ₁ * mΓ₂ = !![0,0,-1,0; 0,0,0,-1; 1,0,0,0; 0,1,0,0] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₁, mΓ₂, Matrix.mul_apply, Fin.sum_univ_four]

/-- I⊗σ₁, as a two-step word. -/
theorem S_eq :
    mΓ₁ * mΓ₂ * mΓ₀ = !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0] := by
  rw [mΓ₁mΓ₂_eq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₀, Matrix.mul_apply, Fin.sum_univ_four]

/-- I⊗σ₃. -/
theorem T_eq :
    mΓ₀ * mΓ₃ = !![1,0,0,0; 0,-1,0,0; 0,0,1,0; 0,0,0,-1] := by
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₀, mΓ₃, Matrix.mul_apply, Fin.sum_univ_four]

/-- I⊗ε. -/
theorem U_eq :
    mΓ₁ * mΓ₂ * mΓ₃ = !![0,1,0,0; -1,0,0,0; 0,0,0,1; 0,0,-1,0] := by
  rw [mΓ₁mΓ₂_eq]
  ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [mΓ₃, Matrix.mul_apply, Fin.sum_univ_four]

/-! ### The generators lie in the range -/

theorem mΓ₀_mem : mΓ₀ ∈ cliffordMajoranaToMatrix.range := by
  refine ⟨ι Q₃₁ ((1, 0), (0, 0)), ?_⟩
  change cliffordMajoranaToMatrix (ι Q₃₁ ((1, 0), (0, 0))) = mΓ₀
  rw [cliffordMajoranaToMatrix_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem mΓ₁_mem : mΓ₁ ∈ cliffordMajoranaToMatrix.range := by
  refine ⟨ι Q₃₁ ((0, 1), (0, 0)), ?_⟩
  change cliffordMajoranaToMatrix (ι Q₃₁ ((0, 1), (0, 0))) = mΓ₁
  rw [cliffordMajoranaToMatrix_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem mΓ₂_mem : mΓ₂ ∈ cliffordMajoranaToMatrix.range := by
  refine ⟨ι Q₃₁ ((0, 0), (1, 0)), ?_⟩
  change cliffordMajoranaToMatrix (ι Q₃₁ ((0, 0), (1, 0))) = mΓ₂
  rw [cliffordMajoranaToMatrix_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem mΓ₃_mem : mΓ₃ ∈ cliffordMajoranaToMatrix.range := by
  refine ⟨ι Q₃₁ ((0, 0), (0, 1)), ?_⟩
  change cliffordMajoranaToMatrix (ι Q₃₁ ((0, 0), (0, 1))) = mΓ₃
  rw [cliffordMajoranaToMatrix_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

/-! ### The eight projectors -/

/-- Row projector e₀₀⊗I = ½(1 + Γ₂). -/
theorem A0_mem :
    (!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0] :
      Matrix (Fin 4) (Fin 4) ℝ) = (1/2 : ℝ) • (1 + mΓ₂) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [mΓ₂, Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem (one_mem _) mΓ₂_mem) _

/-- Row projector e₁₁⊗I = ½(1 − Γ₂). -/
theorem A1_mem :
    (!![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] :
      Matrix (Fin 4) (Fin 4) ℝ) = (1/2 : ℝ) • (1 - mΓ₂) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [mΓ₂, Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _) mΓ₂_mem) _

/-- Row projector e₀₁⊗I = ½(Γ₁ − Γ₁Γ₂). -/
theorem A2_mem :
    (!![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0] :
      Matrix (Fin 4) (Fin 4) ℝ) = (1/2 : ℝ) • (mΓ₁ - mΓ₁ * mΓ₂) by
    rw [mΓ₁mΓ₂_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [mΓ₁] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem mΓ₁_mem (mul_mem mΓ₁_mem mΓ₂_mem)) _

/-- Row projector e₁₀⊗I = ½(Γ₁ + Γ₁Γ₂). -/
theorem A3_mem :
    (!![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0] :
      Matrix (Fin 4) (Fin 4) ℝ) = (1/2 : ℝ) • (mΓ₁ + mΓ₁ * mΓ₂) by
    rw [mΓ₁mΓ₂_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [mΓ₁] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem mΓ₁_mem (mul_mem mΓ₁_mem mΓ₂_mem)) _

/-- Column projector I⊗e₀₀ = ½(1 + Γ₀Γ₃). -/
theorem B0_mem :
    (!![1,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![1,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,0] :
      Matrix (Fin 4) (Fin 4) ℝ) = (1/2 : ℝ) • (1 + mΓ₀ * mΓ₃) by
    rw [T_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _ (add_mem (one_mem _) (mul_mem mΓ₀_mem mΓ₃_mem)) _

/-- Column projector I⊗e₁₁ = ½(1 − Γ₀Γ₃). -/
theorem B1_mem :
    (!![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] :
      Matrix (Fin 4) (Fin 4) ℝ) = (1/2 : ℝ) • (1 - mΓ₀ * mΓ₃) by
    rw [T_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.one_apply] <;> norm_num]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _) (mul_mem mΓ₀_mem mΓ₃_mem)) _

/-- Column projector I⊗e₀₁ = ½(Γ₁Γ₂Γ₀ + Γ₁Γ₂Γ₃). -/
theorem B2_mem :
    (!![0,1,0,0; 0,0,0,0; 0,0,0,1; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![0,1,0,0; 0,0,0,0; 0,0,0,1; 0,0,0,0] :
      Matrix (Fin 4) (Fin 4) ℝ)
      = (1/2 : ℝ) • (mΓ₁ * mΓ₂ * mΓ₀ + mΓ₁ * mΓ₂ * mΓ₃) by
    rw [S_eq, U_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;> simp <;> norm_num]
  exact Subalgebra.smul_mem _
    (add_mem (mul_mem (mul_mem mΓ₁_mem mΓ₂_mem) mΓ₀_mem)
      (mul_mem (mul_mem mΓ₁_mem mΓ₂_mem) mΓ₃_mem)) _

/-- Column projector I⊗e₁₀ = ½(Γ₁Γ₂Γ₀ − Γ₁Γ₂Γ₃). -/
theorem B3_mem :
    (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0] : Matrix (Fin 4) (Fin 4) ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0] :
      Matrix (Fin 4) (Fin 4) ℝ)
      = (1/2 : ℝ) • (mΓ₁ * mΓ₂ * mΓ₀ - mΓ₁ * mΓ₂ * mΓ₃) by
    rw [S_eq, U_eq]
    ext a b <;> fin_cases a <;> fin_cases b <;> simp <;> norm_num]
  exact Subalgebra.smul_mem _
    (sub_mem (mul_mem (mul_mem mΓ₁_mem mΓ₂_mem) mΓ₀_mem)
      (mul_mem (mul_mem mΓ₁_mem mΓ₂_mem) mΓ₃_mem)) _

end Surjectivity

/-! ### The sixteen matrix units

Each is ONE product of a row-projector and a column-projector:
e_{ik}⊗I times I⊗e_{jl} is e_{ik}⊗e_{jl}. No nested gamma word is ever
expanded here — that is the whole point of the projector route. -/

section MatrixUnits

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

private theorem E00_mem :
    Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (0 : Fin 4) (1 : ℝ)
      = (!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![1,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A0_mem B0_mem

private theorem E11_mem :
    Matrix.single (1 : Fin 4) (1 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (1 : Fin 4) (1 : ℝ)
      = (!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A0_mem B1_mem

private theorem E01_mem :
    Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (1 : Fin 4) (1 : ℝ)
      = (!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,1,0,0; 0,0,0,0; 0,0,0,1; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A0_mem B2_mem

private theorem E10_mem :
    Matrix.single (1 : Fin 4) (0 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (0 : Fin 4) (1 : ℝ)
      = (!![1,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A0_mem B3_mem

private theorem E22_mem :
    Matrix.single (2 : Fin 4) (2 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (2 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![1,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A1_mem B0_mem

private theorem E33_mem :
    Matrix.single (3 : Fin 4) (3 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (3 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A1_mem B1_mem

private theorem E23_mem :
    Matrix.single (2 : Fin 4) (3 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (3 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,1,0,0; 0,0,0,0; 0,0,0,1; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A1_mem B2_mem

private theorem E32_mem :
    Matrix.single (3 : Fin 4) (2 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (2 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A1_mem B3_mem

private theorem E02_mem :
    Matrix.single (0 : Fin 4) (2 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (2 : Fin 4) (1 : ℝ)
      = (!![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![1,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A2_mem B0_mem

private theorem E13_mem :
    Matrix.single (1 : Fin 4) (3 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (3 : Fin 4) (1 : ℝ)
      = (!![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A2_mem B1_mem

private theorem E03_mem :
    Matrix.single (0 : Fin 4) (3 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (0 : Fin 4) (3 : Fin 4) (1 : ℝ)
      = (!![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,1,0,0; 0,0,0,0; 0,0,0,1; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A2_mem B2_mem

private theorem E12_mem :
    Matrix.single (1 : Fin 4) (2 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (1 : Fin 4) (2 : Fin 4) (1 : ℝ)
      = (!![0,0,1,0; 0,0,0,1; 0,0,0,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A2_mem B3_mem

private theorem E20_mem :
    Matrix.single (2 : Fin 4) (0 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (0 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![1,0,0,0; 0,0,0,0; 0,0,1,0; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A3_mem B0_mem

private theorem E31_mem :
    Matrix.single (3 : Fin 4) (1 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (1 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 0,1,0,0; 0,0,0,0; 0,0,0,1] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A3_mem B1_mem

private theorem E21_mem :
    Matrix.single (2 : Fin 4) (1 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (2 : Fin 4) (1 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,1,0,0; 0,0,0,0; 0,0,0,1; 0,0,0,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A3_mem B2_mem

private theorem E30_mem :
    Matrix.single (3 : Fin 4) (0 : Fin 4) (1 : ℝ)
      ∈ cliffordMajoranaToMatrix.range := by
  rw [show Matrix.single (3 : Fin 4) (0 : Fin 4) (1 : ℝ)
      = (!![0,0,0,0; 0,0,0,0; 1,0,0,0; 0,1,0,0] : Matrix (Fin 4) (Fin 4) ℝ)
        * (!![0,0,0,0; 1,0,0,0; 0,0,0,0; 0,0,1,0] : Matrix (Fin 4) (Fin 4) ℝ) by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.single, Matrix.mul_apply, Fin.sum_univ_four]]
  exact mul_mem A3_mem B3_mem

end MatrixUnits

/-- Every standard basis matrix of M₄(ℝ) lies in the range. -/
theorem single_mem (a b : Fin 4) :
    Matrix.single a b (1 : ℝ) ∈ cliffordMajoranaToMatrix.range := by
  fin_cases a <;> fin_cases b
  exacts [E00_mem, E01_mem, E02_mem, E03_mem, E10_mem, E11_mem, E12_mem,
    E13_mem, E20_mem, E21_mem, E22_mem, E23_mem, E30_mem, E31_mem, E32_mem,
    E33_mem]

/-- **The Majorana gammas generate M₄(ℝ)**: the representation is
    surjective. -/
theorem cliffordMajoranaToMatrix_surjective :
    Function.Surjective cliffordMajoranaToMatrix := by
  intro A
  have hA : A = ∑ i, ∑ j, Matrix.single i j (A i j) :=
    (Matrix.sum_sum_single fun i j => A i j).symm
  have hmem : A ∈ cliffordMajoranaToMatrix.range := by
    rw [hA]
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    have hs : Matrix.single i j (A i j)
        = (A i j) • Matrix.single i j (1 : ℝ) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hs]
    exact Subalgebra.smul_mem _ (single_mem i j) _
  exact hmem

/-! ## 6. Injectivity by rank, and the isomorphism -/

/-- **Injectivity by rank**: both sides have finrank 16 and the map is
    surjective, so the kernel has finrank zero. -/
theorem cliffordMajoranaToMatrix_injective :
    Function.Injective cliffordMajoranaToMatrix := by
  haveI : FiniteDimensional ℝ (CliffordAlgebra Q₃₁) :=
    FiniteDimensional.of_finrank_pos (by rw [cliffordMajorana_finrank]; norm_num)
  have hrk := LinearMap.finrank_range_add_finrank_ker
    cliffordMajoranaToMatrix.toLinearMap
  have hr : LinearMap.range cliffordMajoranaToMatrix.toLinearMap = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact cliffordMajoranaToMatrix_surjective
  rw [hr, finrank_top, matrix4R_finrank, cliffordMajorana_finrank] at hrk
  have hk : Module.finrank ℝ
      (LinearMap.ker cliffordMajoranaToMatrix.toLinearMap) = 0 := by omega
  have hbot : LinearMap.ker cliffordMajoranaToMatrix.toLinearMap = ⊥ :=
    Submodule.finrank_eq_zero.mp hk
  exact LinearMap.ker_eq_bot.mp hbot

/-- **Cl(3,1;ℝ) ≅ M₄(ℝ)** — the mostly-PLUS twin, and with it W7's
    named stair complete in both conventions. -/
def cliffordMajoranaEquiv :
    CliffordAlgebra Q₃₁ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  AlgEquiv.ofBijective cliffordMajoranaToMatrix
    ⟨cliffordMajoranaToMatrix_injective, cliffordMajoranaToMatrix_surjective⟩

/-- The isomorphism IS the gamma representation on generators. -/
theorem cliffordMajoranaEquiv_ι (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordMajoranaEquiv (ι Q₃₁ v) = cliffordMajoranaMap v :=
  cliffordMajoranaToMatrix_ι v

theorem cliffordMajoranaEquiv_e₀ :
    cliffordMajoranaEquiv (ι Q₃₁ ((1, 0), (0, 0))) = mΓ₀ := by
  rw [cliffordMajoranaEquiv_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem cliffordMajoranaEquiv_e₁ :
    cliffordMajoranaEquiv (ι Q₃₁ ((0, 1), (0, 0))) = mΓ₁ := by
  rw [cliffordMajoranaEquiv_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem cliffordMajoranaEquiv_e₂ :
    cliffordMajoranaEquiv (ι Q₃₁ ((0, 0), (1, 0))) = mΓ₂ := by
  rw [cliffordMajoranaEquiv_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

theorem cliffordMajoranaEquiv_e₃ :
    cliffordMajoranaEquiv (ι Q₃₁ ((0, 0), (0, 1))) = mΓ₃ := by
  rw [cliffordMajoranaEquiv_ι]
  simp only [cliffordMajoranaMap, LinearMap.coe_mk, AddHom.coe_mk]
  module

/-! ## 7. The two conventions side by side

`CliffordRealMinkowski.Q₁₃` and `Q₃₁` are not merely "the two
Minkowski conventions" as a figure of speech: they are exact negatives
of one another, on the same underlying space, in the same coordinates.
Review round 12 checked this only in the probe file; it is promoted
here so the relation between the two isomorphism theorems is machine
material rather than commentary. -/

/-- **The mostly-plus form is minus the mostly-minus form**, pointwise
    and in the same coordinates — so `cliffordMajoranaEquiv` and
    `CliffordRealMinkowski.cliffordRealMinkowskiEquiv` really are the
    two conventions of one geometry, not two unrelated forms. -/
theorem Q₃₁_eq_neg_Q₁₃ (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    Q₃₁ v = - CliffordRealMinkowski.Q₁₃ v := by
  rw [Q₃₁_apply, CliffordRealMinkowski.Q₁₃_apply]
  ring

/-- The two forms disagree on every nonzero vector where either is
    nonzero — stated at the four coordinate directions, which is what
    the sign-flip actually amounts to. -/
theorem Q₃₁_ne_Q₁₃ :
    Q₃₁ ((1, 0), (0, 0)) ≠ CliffordRealMinkowski.Q₁₃ ((1, 0), (0, 0))
      ∧ Q₃₁ ((0, 1), (0, 0)) ≠ CliffordRealMinkowski.Q₁₃ ((0, 1), (0, 0))
      ∧ Q₃₁ ((0, 0), (1, 0)) ≠ CliffordRealMinkowski.Q₁₃ ((0, 0), (1, 0))
      ∧ Q₃₁ ((0, 0), (0, 1)) ≠ CliffordRealMinkowski.Q₁₃ ((0, 0), (0, 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [Q₃₁_apply, CliffordRealMinkowski.Q₁₃_apply] <;> norm_num

end CliffordRealMajorana


