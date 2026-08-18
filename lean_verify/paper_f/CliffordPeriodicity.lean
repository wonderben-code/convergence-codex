import F4_1e_CliffordMatrix
import CliffordDimension

/-!
# The periodicity step `Cl(Q ⊥ ⟨1,1⟩) ≅ M₂(Cl Q)`, for every `Q` at once

`CliffordSixIso` built this at one form, to close the `n = 6` half of `WALLS §W7.1`, and its
record ended with a prediction: *"the same construction should apply with `Cl₆` in place of `Cl₄`
— a prediction about difficulty, labelled one (`ERRATUM 194`)."*

**This is that prediction discharged rather than repeated.** Nothing in the construction used
anything about the particular form: the only property of `ι v` it consumes is
`CliffordAlgebra.ι_sq_scalar`. So it is stated once, for an arbitrary `Q` on an arbitrary
finite-dimensional complex space.

> **`periodicityEquiv`** — `CliffordAlgebra (Q.prod ⟨1,1⟩) ≃ₐ[ℂ]`
> `Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)`.

## The construction

Adjoin two generators `e, f` with `e² = f² = 1`. Send `e ↦ σ₃`, `f ↦ σ₁`, and each old generator
`v ↦ ι v · σ₂`, all as `2 × 2` matrices over `Cl Q`. The three Pauli matrices pairwise anticommute
and square to `1`, which is exactly the Clifford relation for the sum, and **every verification is
therefore a four-entry computation** rather than one over matrices the size of the representation.

Surjectivity: the image contains `σ₃`, `σ₁` and `ι v · σ₂`, hence — one product identity, `dg_ι` —
the diagonal copy of `ι v`; hence, by `CliffordAlgebra.induction`, the diagonal copy of all of
`Cl Q`; and a `2 × 2` matrix over `Cl Q` is a `Cl Q`-combination of `1, σ₃, σ₁, σ₁σ₃` (`decomp`).
Injectivity is never proved by hand — `CliffordDimension.cliffordAlgEquivOfSurjective` supplies it
from the dimension count.

## What this is not

**It is not the classification.** It relates `Cl` of one form to matrices over `Cl` of another; it
says nothing about which forms give matrix algebras, and
`CliffordDimension.finrank_cliffordAlgebra_congr` is the reason that gap cannot be closed by
counting: every form on a space gives the same dimension,
the zero form included, and that one's Clifford algebra is the exterior algebra.

**It is not Mathlib's `CliffordAlgebra.prodEquiv`**, which lands in the *graded* tensor product
`evenOdd Q₁ ᵍ⊗ evenOdd Q₂`. `WALLS §W7.1` records that no ordinary-tensor conversion exists in the
library; this sidesteps the question rather than answering it, by never forming a tensor product.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordPeriodicity

open Matrix CliffordAlgebra

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (Q : QuadraticForm ℂ V)

/-- the plane carrying the two adjoined generators, with `x² + y²`. -/
abbrev Qplane : QuadraticForm ℂ (ℂ × ℂ) := CliffordAlgebraQuaternion.Q (1 : ℂ) (1 : ℂ)

/-- `Q` with two extra square-one generators. -/
abbrev Qext : QuadraticForm ℂ (V × (ℂ × ℂ)) := Q.prod Qplane

/-- `i · ι v`, the entry carrying an old generator into the off-diagonal. -/
def entZ (v : V) : CliffordAlgebra Q := Complex.I • ι Q v

theorem entZ_sq (v : V) : entZ Q v * entZ Q v = - algebraMap ℂ _ (Q v) := by
  rw [entZ, smul_mul_smul_comm, CliffordAlgebra.ι_sq_scalar, Complex.I_mul_I]
  simp

/-- The representation of the extended generating space inside `M₂(Cl Q)`. -/
def m2 (w : V × (ℂ × ℂ)) : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) :=
  !![w.2.1 • 1,              w.2.2 • 1 - entZ Q w.1;
     w.2.2 • 1 + entZ Q w.1, -(w.2.1 • 1)]

theorem m2_sq (w : V × (ℂ × ℂ)) : m2 Q w * m2 Q w = algebraMap ℂ _ (Qext Q w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m2, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.algebraMap_matrix_apply, QuadraticMap.prod_apply,
      CliffordAlgebraQuaternion.Q_apply, sub_mul, mul_add, add_mul, mul_sub,
      entZ_sq, Algebra.smul_def, ← map_mul, Algebra.commutes] <;>
    abel_nf <;> simp [mul_comm]

/-- The same map, bundled. -/
def map2 : (V × (ℂ × ℂ)) →ₗ[ℂ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) where
  toFun := m2 Q
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m2, entZ, add_smul, smul_add] <;> abel
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m2, entZ, smul_smul, mul_comm, smul_sub, smul_add]

/-- **THE REPRESENTATION `Cl(Q ⊥ ⟨1,1⟩) →ₐ[ℂ] M₂(Cl Q)`.** -/
def toM2 : CliffordAlgebra (Qext Q) →ₐ[ℂ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) :=
  CliffordAlgebra.lift (Qext Q) ⟨map2 Q, m2_sq Q⟩

@[simp] theorem toM2_ι (w : V × (ℂ × ℂ)) : toM2 Q (ι (Qext Q) w) = m2 Q w :=
  CliffordAlgebra.lift_ι_apply _ _ w

/-! ## Surjectivity -/

/-- `σ₃`, the image of the first adjoined generator. -/
def s3 : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := m2 Q (0, (1, 0))
/-- `σ₁`, the image of the second. -/
def s1 : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := m2 Q (0, (0, 1))
/-- the image of an old generator. -/
def nv (v : V) : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := m2 Q (v, (0, 0))

theorem s3_mem : s3 Q ∈ (toM2 Q).range := ⟨ι (Qext Q) _, toM2_ι Q _⟩
theorem s1_mem : s1 Q ∈ (toM2 Q).range := ⟨ι (Qext Q) _, toM2_ι Q _⟩
theorem nv_mem (v : V) : nv Q v ∈ (toM2 Q).range := ⟨ι (Qext Q) _, toM2_ι Q _⟩

theorem s3_eq : s3 Q = !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [s3, m2, entZ]

theorem s1_eq : s1 Q = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [s1, m2, entZ]

theorem nv_eq (v : V) : nv Q v = !![0, -entZ Q v; entZ Q v, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nv, m2, entZ]

/-- the diagonal copy of `Cl Q`. -/
def dg (a : CliffordAlgebra Q) : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := !![a, 0; 0, a]

theorem dg_add (a b) : dg Q (a + b) = dg Q a + dg Q b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg]

theorem dg_mul (a b) : dg Q (a * b) = dg Q a * dg Q b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

theorem dg_algebraMap (r : ℂ) :
    dg Q (algebraMap ℂ _ r) = algebraMap ℂ (Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) r := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, Matrix.algebraMap_matrix_apply]

/-- **THE OLD ALGEBRA SITS DIAGONALLY IN THE IMAGE**, and this is the only product computation in
the surjectivity argument. -/
theorem dg_ι (v : V) : dg Q (ι Q v) = Complex.I • (nv Q v * s1 Q * s3 Q) := by
  rw [nv_eq, s1_eq, s3_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, entZ, smul_smul]

theorem dg_mem (a : CliffordAlgebra Q) : dg Q a ∈ (toM2 Q).range := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [dg_algebraMap]; exact Subalgebra.algebraMap_mem _ r
  | ι v =>
      rw [dg_ι]
      exact Subalgebra.smul_mem _ (mul_mem (mul_mem (nv_mem Q v) (s1_mem Q)) (s3_mem Q)) _
  | mul a b ha hb => rw [dg_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [dg_add]; exact add_mem ha hb

/-- **EVERY `2 × 2` MATRIX OVER `Cl Q` IS A `Cl Q`-COMBINATION OF `1, σ₃, σ₁, σ₁σ₃`.** -/
theorem decomp (M : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) :
    M = dg Q ((2 : ℂ)⁻¹ • (M 0 0 + M 1 1)) + dg Q ((2 : ℂ)⁻¹ • (M 0 0 - M 1 1)) * s3 Q
      + dg Q ((2 : ℂ)⁻¹ • (M 0 1 + M 1 0)) * s1 Q
      + dg Q ((2 : ℂ)⁻¹ • (M 1 0 - M 0 1)) * (s1 Q * s3 Q) := by
  rw [s1_eq, s3_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg, smul_sub, smul_add] <;> module

theorem toM2_surjective : Function.Surjective (toM2 Q) := by
  intro M
  have hmem : M ∈ (toM2 Q).range := by
    rw [decomp Q M]
    exact add_mem (add_mem (add_mem (dg_mem Q _) (mul_mem (dg_mem Q _) (s3_mem Q)))
      (mul_mem (dg_mem Q _) (s1_mem Q))) (mul_mem (dg_mem Q _) (mul_mem (s1_mem Q) (s3_mem Q)))
  exact hmem

/-! ## The equivalence -/

variable [FiniteDimensional ℂ V]

theorem finrank_ext : Module.finrank ℂ (V × (ℂ × ℂ)) = Module.finrank ℂ V + 2 := by
  simp [Module.finrank_prod]

theorem finrank_M2 :
    Module.finrank ℂ (Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q))
      = 2 ^ (Module.finrank ℂ V + 2) := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  rw [Module.finrank_matrix ℂ (CliffordAlgebra Q) (Fin 2) (Fin 2),
    CliffordDimension.finrank_cliffordAlgebra ℂ V Q]
  simp [pow_succ]
  ring

/-- **THE PERIODICITY STEP, FOR EVERY `Q`.** -/
def periodicityEquiv :
    CliffordAlgebra (Qext Q) ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := by
  haveI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  exact CliffordDimension.cliffordAlgEquivOfSurjective ℂ (V × (ℂ × ℂ)) (Qext Q)
    (toM2 Q) (toM2_surjective Q) (by rw [finrank_M2 Q, finrank_ext])

/-- The equivalence **is** the representation. -/
@[simp] theorem periodicityEquiv_apply (x : CliffordAlgebra (Qext Q)) :
    periodicityEquiv Q x = toM2 Q x := rfl

end

end CliffordPeriodicity
