import CliffordRealSplitQuat
import MinkowskiHerm2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# `Cl(3,0;ℝ) ≅ M₂(ℂ)` — the third diagonal, and the first that does not split

`CliffordRealSplit` and `CliffordRealSplitQuat` took `p − q ≡ 1` and `≡ 5` off the real wall by the
same trick twice: find something in the algebra squaring to `+1`, and split. `ERRATUM 211` records
that the wall had been overstated by exactly those two classes.

**This one does not split.** `Cl(3,0) ≅ M₂(ℂ)` is a **simple** algebra, so no central idempotent
exists and the previous technique provably cannot reach it. It is done the other way — a
representation **built and checked**, as `CliffordRealMinkowski` and `CliffordRealMajorana` did.

> **`equivPauli`** — `Cl(3,0;ℝ) ≃ₐ[ℝ] M₂(ℂ)`. Signature `(3,0)` proved, so **`p − q = 3`**.

## The construction, and the one fact it turns on

The generators go to the Pauli matrices, which this estate already has:
`MinkowskiHerm2.pauliHerm t x y z` is `t·1 + x·σ₁ + y·σ₂ + z·σ₃`, so the three matrices need no new
definitions and `pauliMap_eq_pauliHerm` records that this map is its traceless part.

**`toPauli_w` is the structural fact.** The volume element `ω = e₁e₂e₃` goes to `i·1`, so `ω² = −1`
rather than `+1`: the centre of `Cl(3,0)` is a copy of `ℂ`, not a split pair. **That is exactly why
this algebra is simple and why the earlier trick fails on it** — the very element that split the
other two supplies the imaginary unit instead. Surjectivity then follows because the eight products
`{1, e₁, e₂, e₃, ω, e₂e₃, e₃e₁, e₁e₂}` land on `{1, σ₁, σ₂, σ₃, i, iσ₁, iσ₂, iσ₃}`, a real basis of
`M₂(ℂ)`, so a preimage can be written from the four complex entries of the target.

`clifford_iso_pauli_of_sig` states it over **every** nondegenerate real form of dimension 3 with
`sigPos 3`, not just the named one.

## Two bridging lemmas, and why they are here

`algebraMap_eq_coe` and `smul_re'`/`smul_im'` are `rfl`-level facts that exist only because the same
scalar appears in three spellings — `algebraMap ℝ ℂ`, the coercion, and a real `•` on a complex
value — which `simp` and `ring` treat as distinct atoms. Mathlib's `Complex.smul_re` does not match
what these goals produce, though it proves the restatement that does. Recording them saved the
second half of this file and they are stated once rather than worked around eight times.

## Where the wall stands after this

Reached: `p − q ≡ 0, 1, 2, 3, 5, 6, 7`. **Missing: `p − q ≡ 4` alone.**

That is `Cl(4,0) ≅ M₂(ℍ)`, and nothing here transfers: it is simple, so it does not split, and its
representation is **quaternionic** rather than complex, so the Pauli construction does not carry
over either. **Not estimated.**

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

/-- The components of a real scalar acting on a complex number. Mathlib's `Complex.smul_re` is
stated for a different `SMul` path and does not match what these goals produce; these are `rfl` and
they do. Every entrywise computation in stage 2 needs them. -/
@[simp] theorem smul_re' (r : ℝ) (z : ℂ) : (r • z).re = r * z.re := Complex.smul_re r z
@[simp] theorem smul_im' (r : ℝ) (z : ℂ) : (r • z).im = r * z.im := Complex.smul_im r z

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

/-! ## Stage 2 — surjectivity, and the isomorphism

The eight products land on a real basis of `M₂(ℂ)`. Each product lemma is the same computation as
`toPauli_w`, and with them a preimage can be written from the four complex entries of the target. -/

@[simp] theorem toPauli_f₂f₃ : toPauli (f₂ * f₃) = Complex.I • sig₁ := by
  simp only [f₂, f₃, map_mul, toPauli_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig₁, sig₂, sig₃, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem toPauli_f₃f₁ : toPauli (f₃ * f₁) = Complex.I • sig₂ := by
  simp only [f₃, f₁, map_mul, toPauli_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig₁, sig₂, sig₃, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem toPauli_f₁f₂ : toPauli (f₁ * f₂) = Complex.I • sig₃ := by
  simp only [f₁, f₂, map_mul, toPauli_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig₁, sig₂, sig₃, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem toPauli_f₁ : toPauli f₁ = sig₁ := by
  simp only [f₁, toPauli_ι]; ext i j; fin_cases i <;> fin_cases j <;> simp [sig₁, sig₂, sig₃]

@[simp] theorem toPauli_f₂ : toPauli f₂ = sig₂ := by
  simp only [f₂, toPauli_ι]; ext i j; fin_cases i <;> fin_cases j <;> simp [sig₁, sig₂, sig₃]

@[simp] theorem toPauli_f₃ : toPauli f₃ = sig₃ := by
  simp only [f₃, toPauli_ι]; ext i j; fin_cases i <;> fin_cases j <;> simp [sig₁, sig₂, sig₃]

/-- **Surjective.** For a target `M`, the coefficients in the basis `{1, σ₁, σ₂, σ₃}` are
`a = (m₀₀+m₁₁)/2`, `b = (m₀₁+m₁₀)/2`, `c = i(m₀₁−m₁₀)/2`, `d = (m₀₀−m₁₁)/2`, and each splits into
its real part (carried by `1, e₁, e₂, e₃`) and its imaginary part (carried by
`ω, e₂e₃, e₃e₁, e₁e₂`). -/
theorem toPauli_surjective : Function.Surjective toPauli := by
  intro M
  refine ⟨((M 0 0 + M 1 1) / 2).re • 1 + ((M 0 0 + M 1 1) / 2).im • w
        + ((M 0 1 + M 1 0) / 2).re • f₁ + ((M 0 1 + M 1 0) / 2).im • (f₂ * f₃)
        + (Complex.I * (M 0 1 - M 1 0) / 2).re • f₂
        + (Complex.I * (M 0 1 - M 1 0) / 2).im • (f₃ * f₁)
        + ((M 0 0 - M 1 1) / 2).re • f₃ + ((M 0 0 - M 1 1) / 2).im • (f₁ * f₂), ?_⟩
  simp only [map_add, map_smul, toPauli_w, toPauli_f₁, toPauli_f₂, toPauli_f₃,
    toPauli_f₂f₃, toPauli_f₃f₁, toPauli_f₁f₂, map_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sig₁, sig₂, sig₃, Complex.ext_iff] <;> ring_nf
  all_goals simp

/-- **`Cl(3,0;ℝ) ≃ₐ[ℝ] M₂(ℂ)`.** -/
def equivPauli : CliffordAlgebra Q₃₀ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  refine CliffordDimension.cliffordAlgEquivOfSurjective ℝ ((ℝ × ℝ) × ℝ) Q₃₀ toPauli
    toPauli_surjective ?_
  simp [Module.finrank_matrix, Complex.finrank_real_complex]

/-! ### Its signature — `p − q ≡ 3` -/

theorem sigPos_Q₃₀ : sigPos Q₃₀ = 3 := by
  rw [Q₃₀, sigPos_prod, CliffordRealSignatures.sigPos_quaternionQ, sigPos_smul_sq]; norm_num

theorem sigNeg_Q₃₀ : sigNeg Q₃₀ = 0 := by
  rw [Q₃₀, sigNeg_prod, CliffordRealSignatures.sigNeg_quaternionQ, sigNeg_smul_sq]; norm_num

/-- **`p − q = 3`**, the third diagonal off the wall. -/
theorem diagonal_three : sigPos Q₃₀ = 3 ∧ sigNeg Q₃₀ = 0 := ⟨sigPos_Q₃₀, sigNeg_Q₃₀⟩

theorem sep_Q₃₀ : (QuadraticMap.associated (R := ℝ) Q₃₀).SeparatingLeft :=
  CliffordRealSignatures.separatingLeft_of_sig (by rw [sigPos_Q₃₀, sigNeg_Q₃₀]; simp)

/-- **Every** nondegenerate real form of dimension 3 with `sigPos = 3` gives `M₂(ℂ)`. -/
theorem clifford_iso_pauli_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 3) (hsig : sigPos Q = 3) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ) := by
  obtain ⟨e⟩ := CliffordRealQuantified.cliffordEquiv_of_sigPos_eq hQ sep_Q₃₀
    (by simp [hdim]) (by rw [hsig, sigPos_Q₃₀])
  exact ⟨e.trans equivPauli⟩

end

end CliffordRealPauli
