import CliffordRealSplitQuat
import MinkowskiHerm2

/-!
# The Pauli representation of `Cl(3,0;ℝ)` — stage 1, and it is **not** an isomorphism yet

`CliffordRealSplit` and `CliffordRealSplitQuat` took `p − q ≡ 1` and `≡ 5` off the real wall by the
same trick twice: find something in the algebra squaring to `+1`, and split. `ERRATUM 211` records
that the wall had been overstated by exactly those two classes.

**The remaining two do not split.** `Cl(3,0) ≅ M₂(ℂ)` and `Cl(4,0) ≅ M₂(ℍ)` are simple algebras, so
no central idempotent exists and the previous technique provably cannot reach them. Getting them
needs a representation **built and checked**, as `CliffordRealMinkowski` and `CliffordRealMajorana`
did — and those were done in two stages, the map first and surjectivity after. **This is stage 1 for
`Cl(3,0)`, and it is labelled as such rather than dressed up as the theorem.**

## What is proved

> **`toPauli`** — an `ℝ`-algebra map `Cl(3,0;ℝ) →ₐ[ℝ] M₂(ℂ)`, from `pauliMap_sq`: the three
> generators go to the Pauli matrices and `(x σ₁ + y σ₂ + z σ₃)² = (x² + y² + z²)·1`.

> **`toPauli_w`** — the volume element `ω = e₁e₂e₃` goes to **`i · 1`**. This is the structural fact
> that distinguishes this case from the two that fell: `ω² = −1` here, not `+1`, so the centre of
> `Cl(3,0)` is a copy of `ℂ` rather than a split pair, **which is exactly why the algebra is simple
> and the splitting technique fails.** The element that would have split it supplies the imaginary
> unit instead.

The Pauli matrices are not new definitions: `MinkowskiHerm2.pauliHerm t x y z` is
`t·1 + x·σ₁ + y·σ₂ + z·σ₃`, and `pauliMap_eq_pauliHerm` records that the map here is its traceless
part, so the two are not two objects.

## What is NOT proved, and it is the whole remaining leg

**Surjectivity, and therefore the isomorphism.** `CliffordDimension.cliffordAlgEquivOfSurjective`
would close it immediately — `finrank ℝ M₂(ℂ) = 8 = 2³` — so the isomorphism is *one theorem away*
and that theorem is `Function.Surjective toPauli`. The route is not in doubt: the eight products
`{1, e₁, e₂, e₃, ω, e₂e₃, e₃e₁, e₁e₂}` map to `{1, σ₁, σ₂, σ₃, i, iσ₁, iσ₂, iσ₃}`, a real basis of
`M₂(ℂ)`, so an explicit preimage can be written down from the four complex entries of a target
matrix. **It is not written down here, and until it is, `p − q ≡ 3` is still on the wall.**

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealPauli

open QuadraticForm QuadraticMap CliffordAlgebra SignatureArithmetic Complex Matrix

noncomputable section

/-- signature `(3,0)`: `x² + y² + z²`. -/
abbrev Q₃₀ : QuadraticForm ℝ ((ℝ × ℝ) × ℝ) :=
  (CliffordAlgebraQuaternion.Q (1 : ℝ) 1).prod ((1 : ℝ) • QuadraticMap.sq)

/-! ### The three Pauli matrices

`MinkowskiHerm2.pauliHerm t x y z` is `t·1 + x·σ₁ + y·σ₂ + z·σ₃`, so the three matrices are already
in the estate; naming them here is bookkeeping, and `pauliMap_eq_pauliHerm` records the identity. -/

/-- `σ₁`. -/ def sig₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- `σ₂`. -/ def sig₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- `σ₃`. -/ def sig₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The generators go to the Pauli matrices. Stated as a linear **combination** rather than
entrywise, so that linearity is a one-line module fact rather than four entry computations. -/
def pauliMap : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun v := v.1.1 • sig₁ + v.1.2 • sig₂ + v.2 • sig₃
  map_add' x y := by simp [add_smul]; abel
  map_smul' c x := by simp [smul_smul, smul_add]

@[simp] theorem pauliMap_apply (v : (ℝ × ℝ) × ℝ) :
    pauliMap v = v.1.1 • sig₁ + v.1.2 • sig₂ + v.2 • sig₃ := rfl

/-- `algebraMap ℝ ℂ` **is** the coercion — definitionally, so this is `rfl` — but `simp` and `ring`
treat the two spellings as different atoms, and every entrywise computation below produces one of
each. Stated once so they stop being two things. -/
@[simp] theorem algebraMap_eq_coe (x : ℝ) : (algebraMap ℝ ℂ) x = (x : ℂ) := rfl

/-- A real scalar on a complex matrix is the coerced complex scalar. Stated once because every
entrywise computation below needs it: with `ℝ`-`smul` the entries carry a scalar action `simp` has
no component lemma for, and with `ℂ`-`smul` they are ordinary complex products. -/
theorem real_smul_matrix (r : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    r • M = (r : ℂ) • M := (algebraMap_smul ℂ r M).symm

/-- `pauliMap` written with complex scalars, which is the form the computations use. -/
theorem pauliMap_eq (v : (ℝ × ℝ) × ℝ) :
    pauliMap v = (v.1.1 : ℂ) • sig₁ + (v.1.2 : ℂ) • sig₂ + (v.2 : ℂ) • sig₃ := by
  rw [pauliMap_apply, real_smul_matrix, real_smul_matrix, real_smul_matrix]

/-- The identity with the estate's existing Hermitian parametrisation, recorded so the two are not
two different objects. -/
theorem pauliMap_eq_pauliHerm (v : (ℝ × ℝ) × ℝ) :
    pauliMap v = MinkowskiHerm2.pauliHerm 0 v.1.1 v.1.2 v.2 := by
  rw [pauliMap_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig₁, sig₂, sig₃, MinkowskiHerm2.pauliHerm]; ring

/-- **The Clifford relation.** `(x σ₁ + y σ₂ + z σ₃)² = (x² + y² + z²)·1`, because the Pauli
matrices square to `1` and anticommute. -/
theorem pauliMap_sq (v : (ℝ × ℝ) × ℝ) :
    pauliMap v * pauliMap v = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℂ) (Q₃₀ v) := by
  rw [pauliMap_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig₁, sig₂, sig₃, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.algebraMap_matrix_apply, QuadraticMap.prod_apply,
      CliffordAlgebraQuaternion.Q_apply, QuadraticMap.sq, Complex.ext_iff] <;>
    ring_nf
  all_goals simp

/-- The algebra map out of `Cl(3,0)`. -/
def toPauli : CliffordAlgebra Q₃₀ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  CliffordAlgebra.lift Q₃₀ ⟨pauliMap, pauliMap_sq⟩

@[simp] theorem toPauli_ι (v : (ℝ × ℝ) × ℝ) :
    toPauli (ι Q₃₀ v) = (v.1.1 : ℂ) • sig₁ + (v.1.2 : ℂ) • sig₂ + (v.2 : ℂ) • sig₃ := by
  rw [← pauliMap_eq]; exact CliffordAlgebra.lift_ι_apply _ _ v

/-- The three generators. -/
def f₁ : CliffordAlgebra Q₃₀ := ι Q₃₀ ((1, 0), 0)
def f₂ : CliffordAlgebra Q₃₀ := ι Q₃₀ ((0, 1), 0)
def f₃ : CliffordAlgebra Q₃₀ := ι Q₃₀ ((0, 0), 1)

/-- The volume element. Kept opaque so `map_mul` cannot recurse into it. -/
def w : CliffordAlgebra Q₃₀ := f₁ * f₂ * f₃

/-- **`ω ↦ i · 1`** — the fact that makes this algebra simple rather than split. -/
theorem toPauli_w : toPauli w = Complex.I • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  simp only [w, f₁, f₂, f₃, map_mul, toPauli_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig₁, sig₂, sig₃, Matrix.mul_apply, Fin.sum_univ_two]

end

end CliffordRealPauli
