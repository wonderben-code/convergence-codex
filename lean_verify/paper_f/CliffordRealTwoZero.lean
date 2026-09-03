import CliffordRealQuatFour

/-!
# `Cl(2,0;ℝ) ≅ M₂(ℝ)` — the hole in the diagonal `p − q = 2`

**This file exists because of an error in the four units before it, and `ERRATUM 212` is the
account.** Those units established base cases on all eight residue classes `mod 8` and concluded
that every `Cl(p,q)` was thereby reachable. **That inference is false.**

## Why, precisely

`SignatureArithmetic.sigPos_sub_sigNeg_QextHyp` proves the hyperbolic step preserves `p − q`
**exactly**, not modulo 8. So a base case at `(p₀, q₀)` reaches exactly `(p₀ + n, q₀ + n)` for
`n ≥ 0`, and the base a target `(p,q)` needs is `(p − q, 0)` when `p ≥ q`, or `(0, q − p)` otherwise
— in either case a form with **`min(p,q) = 0`**.

Of the estate's base cases, those with `min(p,q) = 0` sit at

`p − q ∈ {−3, −2, −1, 0, 1, 3, 4}`.

**`p − q = 2` was missing**: the estate's witness there is `CliffordRealMajorana.Q₃₁`, which is
`Cl(3,1)` with `min(p,q) = 1`, so it reaches `(3+n, 1+n)` and **never `Cl(2,0)` itself**. This file
supplies it.

> **`equivM2Real`** — `Cl(2,0;ℝ) ≃ₐ[ℝ] M₂(ℝ)`. Signature `(2,0)` proved, so `p − q = 2` at
> `min(p,q) = 0`.

## What is now true, stated exactly

**Reachable:** every `Cl(p,q)` with `p − q ∈ {−3, −2, −1, 0, 1, 2, 3, 4}` — eight consecutive
diagonals, each from a `min = 0` base by iterating the step.

**Not reachable, and this is the honest residue:** every `Cl(p,q)` with `p − q ≥ 5` or `p − q ≤ −4`.
Closing those needs the **mod-8 periodicity** `Cl(p+8,q) ≅ M₁₆(Cl(p,q))`, which this estate does not
have and which is the only thing that would convert *"a base case in each residue class"* into
*"a base case for each diagonal"*. **That distinction is exactly what the four previous units
elided.**

**⚠ *"WHICH THIS ESTATE DOES NOT HAVE"* IS FALSE AND THE PARAGRAPH IS KEPT AS WRITTEN**
(`ERRATUM 94`, **`ERRATUM 428`**). `CliffordPeriodicityQuantified.clifford_periodicity_eight` —
*"Adding `8` to the positive index of a nondegenerate real form multiplies its Clifford algebra by
`M₁₆`"*, quantified over every form — was committed at **09:41 on 2026-08-18**, and
`clifford_periodicity_eight_neg` is the mirror. **`paper_f/CliffordRealQuatFour.lean` makes the
identical claim and was corrected on 2026-09-01; this file, its twin, was not** — the correcting
unit read one file of a pair, which is `ERRATUM 416`'s and `ERRATUM 419`'s shape.
**The *"Not reachable"* paragraph above is superseded too**: `CliffordModelPeriodicity.
clifford_model_periodicity` is the induction it says is missing, and `CliffordSignatureStep`'s
header records **3321 states with `p + q ≤ 80`, 0 undetermined**. **This file's own mathematics is
untouched** — it is `Cl(2,0;ℝ) ≃ₐ[ℝ] M₂(ℝ)` and nothing else, and that stands.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealTwoZero

open QuadraticForm QuadraticMap CliffordAlgebra SignatureArithmetic Matrix

noncomputable section

/-- signature `(2,0)`: `x² + y²`. -/
abbrev Q₂₀ : QuadraticForm ℝ (ℝ × ℝ) := CliffordAlgebraQuaternion.Q (1 : ℝ) 1

/-- `e₁ ↦ diag(1,−1)`, `e₂ ↦ swap`. -/
def rMap : (ℝ × ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun v := !![v.1, v.2; v.2, -v.1]
  map_add' x y := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> (simp; try ring)
  map_smul' c x := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp

@[simp] theorem rMap_apply (v : ℝ × ℝ) : rMap v = !![v.1, v.2; v.2, -v.1] := rfl

theorem rMap_sq (v : ℝ × ℝ) :
    rMap v * rMap v = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℝ) (Q₂₀ v) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply,
      CliffordAlgebraQuaternion.Q_apply] <;>
    ring

/-- The algebra map out of `Cl(2,0)`. -/
def toM2R : CliffordAlgebra Q₂₀ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  CliffordAlgebra.lift Q₂₀ ⟨rMap, rMap_sq⟩

@[simp] theorem toM2R_ι (v : ℝ × ℝ) : toM2R (ι Q₂₀ v) = !![v.1, v.2; v.2, -v.1] :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-- The two generators. -/
def h₁ : CliffordAlgebra Q₂₀ := ι Q₂₀ (1, 0)
def h₂ : CliffordAlgebra Q₂₀ := ι Q₂₀ (0, 1)

@[simp] theorem toM2R_h₁ : toM2R h₁ = !![1, 0; 0, -1] := by simp [h₁]

@[simp] theorem toM2R_h₂ : toM2R h₂ = !![0, 1; 1, 0] := by
  simp only [h₂, toM2R_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

@[simp] theorem toM2R_h₁h₂ : toM2R (h₁ * h₂) = !![0, 1; -1, 0] := by
  simp only [h₁, h₂, map_mul, toM2R_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Surjective.** `1, h₁, h₂, h₁h₂` land on a basis of `M₂(ℝ)`. -/
theorem toM2R_surjective : Function.Surjective toM2R := by
  intro M
  refine ⟨((M 0 0 - M 1 1) / 2) • h₁ + ((M 0 1 + M 1 0) / 2) • h₂
        + ((M 0 1 - M 1 0) / 2) • (h₁ * h₂) + ((M 0 0 + M 1 1) / 2) • 1, ?_⟩
  simp only [map_add, map_smul, map_one, toM2R_h₁, toM2R_h₂, toM2R_h₁h₂]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **`Cl(2,0;ℝ) ≅ M₂(ℝ)`.** -/
def equivM2Real : CliffordAlgebra Q₂₀ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  refine CliffordDimension.cliffordAlgEquivOfSurjective ℝ (ℝ × ℝ) Q₂₀ toM2R
    toM2R_surjective ?_
  simp [Module.finrank_matrix]

/-! ### Its signature -/

theorem sigPos_Q₂₀ : sigPos Q₂₀ = 2 := by
  rw [Q₂₀, CliffordRealSignatures.sigPos_quaternionQ]; norm_num

theorem sigNeg_Q₂₀ : sigNeg Q₂₀ = 0 := by
  rw [Q₂₀, CliffordRealSignatures.sigNeg_quaternionQ]; norm_num

/-- **`p − q = 2` at `min(p,q) = 0`** — the hole `ERRATUM 212` records. -/
theorem diagonal_two_at_zero : sigPos Q₂₀ = 2 ∧ sigNeg Q₂₀ = 0 := ⟨sigPos_Q₂₀, sigNeg_Q₂₀⟩

theorem sep_Q₂₀ : (QuadraticMap.associated (R := ℝ) Q₂₀).SeparatingLeft :=
  CliffordRealSignatures.separatingLeft_of_sig (by rw [sigPos_Q₂₀, sigNeg_Q₂₀]; simp)

/-- **Every** nondegenerate real form of dimension 2 with `sigPos = 2` gives `M₂(ℝ)`. -/
theorem clifford_iso_M2Real_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 2) (hsig : sigPos Q = 2) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  obtain ⟨e⟩ := CliffordRealQuantified.cliffordEquiv_of_sigPos_eq hQ sep_Q₂₀
    (by simp [hdim]) (by rw [hsig, sigPos_Q₂₀])
  exact ⟨e.trans equivM2Real⟩

end

end CliffordRealTwoZero
