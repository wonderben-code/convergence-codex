import F4_1e_CliffordMatrix
import CliffordIso
import CliffordDimension

/-!
# `Cl₆(ℂ) ≅ M₈(ℂ)`, by the periodicity step done concretely

`WALLS §W7.1`, written yesterday, records this as the open half of the complex Clifford table:
`F1_7_SpacetimeForced.clifford_complex_even_dims` writes `Cl₆(ℂ) ≅ M₈(ℂ)` over its 6D conjunct,
`clifford6_finrank` supplies the **dimension**, and
`CliffordDimension.finrank_cliffordAlgebra_congr` proves the dimension **cannot** supply the
isomorphism — it is the same for every quadratic form on the space, the zero form included.

> **`equivM8`** — `CliffordAlgebra Q₆ ≃ₐ[ℂ] Matrix (Fin 8) (Fin 8) ℂ`, where
> `Q₆ = Q₄ ⊥ (x² + y²)` on a space `§finrank_V6` proves is six-dimensional.

## The route, and it is the one `§W7.1` said was the only one available

That account counted the library: `Mathlib/LinearAlgebra/CliffordAlgebra/` contains **no**
occurrence of `Matrix`, and the decomposition it does have, `CliffordAlgebra.prodEquiv`, lands in
the **graded** tensor product, for which there is no ordinary-tensor conversion. So the route had
to be a representation. **What was not obvious, and is the reason this cost one file rather than a
campaign, is that the representation does not have to be by `8 × 8` matrices.**

`CliffordIso` built `Cl₄(ℂ) ≅ M₄(ℂ)` by exhibiting four `4 × 4` gammas and then solving **sixteen**
matrix units as explicit `(±1/4)`-combinations of gamma products, each verified entrywise. Copied
to six dimensions that is **sixty-four** units over `8 × 8` matrices. This file does not copy it.

The classical periodicity step `Cl_{n+2} ≅ M₂(Cl_n)` is realised directly: the two new generators
go to `σ₃` and `σ₁` over `Cl₄`, and each old generator `v` goes to `ι v · σ₂`. **Every verification
is then over a `2 × 2` matrix — four entries.** `m6_sq` is four goals; the whole of surjectivity is
`dg_ι` (one product identity) plus `decomp` (one four-entry decomposition), because a `2 × 2` matrix
over `Cl₄` is a `Cl₄`-combination of `1`, `σ₃`, `σ₁`, `σ₁σ₃`, and the diagonal copy of `Cl₄` is
reached from the generators by `CliffordAlgebra.induction`.

Then `AlgEquiv.mapMatrix CliffordIso.cliffordMatrixEquiv` replaces `Cl₄` by `M₄(ℂ)`,
`Matrix.compAlgEquiv` flattens `M₂(M₄(ℂ))` to `M_{2×4}(ℂ)`, and `Matrix.reindexAlgEquiv` along
`finProdFinEquiv` lands in `M₈(ℂ)`. **Injectivity is never proved by hand**: it is
`CliffordDimension.cliffordAlgEquivOfSurjective`, the rung extracted yesterday, so the only
Clifford-specific obligation discharged here is surjectivity.

**This is built on `CliffordIso`, not independent of it.** The `n = 4` isomorphism is an input, and
without it this file would produce `Cl₆(ℂ) ≅ M₂(Cl₄(ℂ))` and stop.

## What is NOT proved, and the restriction is real rather than pedantic

**It is not proved for every nondegenerate six-dimensional complex form.** `Q₆` is one specific
form — the estate's `Q₄` extended the way `Q₄` itself was built. Getting from that to *the*
classification entry needs a normal-form theorem for complex quadratic forms (any two of the same
rank are equivalent), which **this estate does not have and this file does not supply**.

**And the gap is not a technicality**: `finrank_cliffordAlgebra_congr` shows every form on this
space gives dimension `64`, while the zero form gives the exterior algebra, which is not `M₈(ℂ)`.
So *"`Cl(Q) ≅ M₈(ℂ)` for a six-dimensional `Q`"* is **false in general** and the hypothesis on `Q`
is doing real work. What is proved is the statement at the `Q₆` this file names.

**`Cl₈(ℂ) ≅ M₁₆(ℂ)` is untouched.** The same construction should apply with `Cl₆` in place of
`Cl₄` — **that is a prediction about difficulty and is labelled one** (`ERRATUM 194`); nothing here
builds it.

**No published tag moves**, and nothing here is about the cascade, spinors or physics.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordSixIso

open Matrix CliffordAlgebra

noncomputable section

abbrev V6 := ((ℂ × ℂ) × (ℂ × ℂ)) × (ℂ × ℂ)
abbrev C4 := CliffordAlgebra Q₄
abbrev M2C4 := Matrix (Fin 2) (Fin 2) C4

/-- `Q₆ = Q₄ ⊥ (x² + y²)`, a nondegenerate complex quadratic form on a 6-dimensional space. -/
def Q₆ : QuadraticForm ℂ V6 := Q₄.prod (CliffordAlgebraQuaternion.Q (1 : ℂ) (1 : ℂ))

/-- `i · ι v`, the entry that carries the four old generators into the off-diagonal. -/
def entZ (v : (ℂ × ℂ) × (ℂ × ℂ)) : C4 := Complex.I • ι Q₄ v

theorem entZ_sq (v) : entZ v * entZ v = - algebraMap ℂ C4 (Q₄ v) := by
  rw [entZ, smul_mul_smul_comm, CliffordAlgebra.ι_sq_scalar, Complex.I_mul_I]
  simp

/-- The representation of the six generators inside `M₂(Cl₄)`. -/
def m6 (w : V6) : M2C4 :=
  !![w.2.1 • 1,            w.2.2 • 1 - entZ w.1;
     w.2.2 • 1 + entZ w.1, -(w.2.1 • 1)]

theorem m6_sq (w : V6) : m6 w * m6 w = algebraMap ℂ _ (Q₆ w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m6, Matrix.mul_apply, Fin.sum_univ_two, Q₆,
      Matrix.algebraMap_matrix_apply, QuadraticMap.prod_apply,
      CliffordAlgebraQuaternion.Q_apply, sub_mul, mul_add, add_mul, mul_sub,
      entZ_sq, Algebra.smul_def, ← map_mul, Algebra.commutes] <;>
    abel_nf <;> simp [mul_comm]

/-- The same map, bundled as a linear map. -/
def map6 : V6 →ₗ[ℂ] M2C4 where
  toFun := m6
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m6, entZ, add_smul, smul_add] <;> abel
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m6, entZ, smul_smul, mul_comm, smul_sub, smul_add]

/-- **THE REPRESENTATION `Cl₆(ℂ) →ₐ[ℂ] M₂(Cl₄(ℂ))`.** -/
def toM2 : CliffordAlgebra Q₆ →ₐ[ℂ] M2C4 :=
  CliffordAlgebra.lift Q₆ ⟨map6, m6_sq⟩

@[simp] theorem toM2_ι (w : V6) : toM2 (ι Q₆ w) = m6 w :=
  CliffordAlgebra.lift_ι_apply _ _ w

/-! ## Surjectivity -/

/-- `σ₃`, the image of the fifth generator. -/
def s3 : M2C4 := m6 (0, (1, 0))
/-- `σ₁`, the image of the sixth. -/
def s1 : M2C4 := m6 (0, (0, 1))
/-- the image of a vector of the old four-dimensional space. -/
def nv (v : (ℂ × ℂ) × (ℂ × ℂ)) : M2C4 := m6 (v, (0, 0))

theorem s3_mem : s3 ∈ toM2.range := ⟨ι Q₆ _, toM2_ι _⟩
theorem s1_mem : s1 ∈ toM2.range := ⟨ι Q₆ _, toM2_ι _⟩
theorem nv_mem (v) : nv v ∈ toM2.range := ⟨ι Q₆ _, toM2_ι _⟩

theorem s3_eq : s3 = !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [s3, m6, entZ]

theorem s1_eq : s1 = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [s1, m6, entZ]

theorem nv_eq (v) : nv v = !![0, -entZ v; entZ v, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nv, m6, entZ]

/-- the diagonal copy of `Cl₄` inside `M₂(Cl₄)`. -/
def dg (a : C4) : M2C4 := !![a, 0; 0, a]

theorem dg_add (a b : C4) : dg (a + b) = dg a + dg b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg]

theorem dg_mul (a b : C4) : dg (a * b) = dg a * dg b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_algebraMap (r : ℂ) : dg (algebraMap ℂ C4 r) = algebraMap ℂ M2C4 r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.algebraMap_matrix_apply]

theorem dg_smul (c : ℂ) (a : C4) : dg (c • a) = c • dg a := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg]

/-- **THE OLD ALGEBRA SITS DIAGONALLY IN THE IMAGE**, and this is the only computation in the
surjectivity argument: `N(v) · σ₁ · σ₃` is `−i·ι v` on the diagonal. -/
theorem dg_ι (v) : dg (ι Q₄ v) = Complex.I • (nv v * s1 * s3) := by
  rw [nv_eq, s1_eq, s3_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, entZ, smul_smul]

theorem dg_mem (a : C4) : dg a ∈ toM2.range := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [dg_algebraMap]; exact Subalgebra.algebraMap_mem _ r
  | ι v =>
      rw [dg_ι]
      exact Subalgebra.smul_mem _ (mul_mem (mul_mem (nv_mem v) s1_mem) s3_mem) _
  | mul a b ha hb => rw [dg_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [dg_add]; exact add_mem ha hb

/-- **EVERY `2 × 2` MATRIX OVER `Cl₄` IS A `Cl₄`-COMBINATION OF `1`, `σ₃`, `σ₁`, `σ₁σ₃`.** Four
entries, and this is the whole of surjectivity. -/
theorem decomp (M : M2C4) :
    M = dg ((2 : ℂ)⁻¹ • (M 0 0 + M 1 1)) + dg ((2 : ℂ)⁻¹ • (M 0 0 - M 1 1)) * s3
      + dg ((2 : ℂ)⁻¹ • (M 0 1 + M 1 0)) * s1
      + dg ((2 : ℂ)⁻¹ • (M 1 0 - M 0 1)) * (s1 * s3) := by
  rw [s1_eq, s3_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg, smul_sub, smul_add] <;>
    module

theorem toM2_surjective : Function.Surjective toM2 := by
  intro M
  have hmem : M ∈ toM2.range := by
    rw [decomp M]
    exact add_mem (add_mem (add_mem (dg_mem _) (mul_mem (dg_mem _) s3_mem))
      (mul_mem (dg_mem _) s1_mem)) (mul_mem (dg_mem _) (mul_mem s1_mem s3_mem))
  exact hmem

/-! ## The isomorphism -/

abbrev M2M4 := Matrix (Fin 2) (Fin 2) (Matrix (Fin 4) (Fin 4) ℂ)

/-- The representation with `Cl₄` replaced by `M₄(ℂ)` through `CliffordIso.cliffordMatrixEquiv`. -/
def toM2M4 : CliffordAlgebra Q₆ →ₐ[ℂ] M2M4 :=
  (AlgEquiv.mapMatrix CliffordIso.cliffordMatrixEquiv : M2C4 ≃ₐ[ℂ] M2M4).toAlgHom.comp toM2

theorem toM2M4_surjective : Function.Surjective toM2M4 :=
  (AlgEquiv.mapMatrix CliffordIso.cliffordMatrixEquiv :
      M2C4 ≃ₐ[ℂ] M2M4).surjective.comp toM2_surjective

theorem finrank_V6 : Module.finrank ℂ V6 = 6 := by
  simp [Module.finrank_prod]

theorem finrank_M2M4 : Module.finrank ℂ M2M4 = 64 := by
  rw [Module.finrank_matrix ℂ (Matrix (Fin 4) (Fin 4) ℂ) (Fin 2) (Fin 2),
    Module.finrank_matrix ℂ ℂ (Fin 4) (Fin 4)]
  simp

/-- **`Cl₆(ℂ) ≅ M₂(M₄(ℂ))`.** -/
def equivM2M4 : CliffordAlgebra Q₆ ≃ₐ[ℂ] M2M4 := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  exact CliffordDimension.cliffordAlgEquivOfSurjective ℂ V6 Q₆ toM2M4 toM2M4_surjective (by
    rw [finrank_M2M4, finrank_V6]; norm_num)

/-- **THE ISOMORPHISM IS THE REPRESENTATION**, not a repackaged abstract equivalence: it is
`toM2M4` with a proof attached, exactly as `CliffordIso.cliffordMatrixEquiv` is `clifford4ToMatrix`
with one. -/
@[simp] theorem equivM2M4_apply (x : CliffordAlgebra Q₆) : equivM2M4 x = toM2M4 x := rfl

/-- The dimension agrees with the general formula, which is a check rather than a new fact:
`CliffordDimension.finrank_cliffordAlgebra` gives `2 ^ 6 = 64` and `M₈(ℂ)` has `64`. -/
theorem finrank_clifford_Q6 : Module.finrank ℂ (CliffordAlgebra Q₆) = 64 := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  rw [CliffordDimension.finrank_cliffordAlgebra ℂ V6 Q₆, finrank_V6]
  norm_num

/-- **`Cl₆(ℂ) ≅ M₈(ℂ)`.** -/
def equivM8 : CliffordAlgebra Q₆ ≃ₐ[ℂ] Matrix (Fin 8) (Fin 8) ℂ :=
  equivM2M4.trans
    ((Matrix.compAlgEquiv (Fin 2) (Fin 4) ℂ ℂ).trans
      (Matrix.reindexAlgEquiv ℂ ℂ finProdFinEquiv))

end

end CliffordSixIso
