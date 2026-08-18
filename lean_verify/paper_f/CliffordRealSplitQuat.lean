import CliffordRealSplit

/-!
# `Cl(0,3;ℝ) ≅ ℍ ⊕ ℍ` — a second diagonal the wall said had none

`CliffordRealSplit` took `p − q ≡ 1` off the wall with `Cl(1,0;ℝ) ≅ ℝ × ℝ`, and its
KEY GENERATOR answer named the next step: of the three remaining classes, the one with the same
*shape* is `p − q ≡ 5`, because `Cl(0,3)` splits for the same reason `Cl(1,0)` does — a central
element squaring to `+1`.

> **`equivSplitQuat`** — `Cl(0,3;ℝ) ≃ₐ[ℝ] ℍ × ℍ`. Signature `(0,3)`, so
> **`p − q = −3 ≡ 5 (mod 8)`**.

## The mechanism, which is the same one twice

In `Cl(1,0)` the generator `e` satisfies `e² = 1`, so `(1 ± e)/2` are complementary idempotents and
the algebra splits. In `Cl(0,3)` no *generator* squares to `+1` — all three square to `−1` — but the
**volume element** `ω = e₁e₂e₃` does, and it is central in odd rank. That is the whole content, and
the map that realises it sends

`e₁ ↦ (i, i)`,  `e₂ ↦ (j, j)`,  `e₃ ↦ (k, −k)`,

whence `ω ↦ (ijk, −ijk) = (−1, 1)`, and `(1 − ω)/2 ↦ (1,0)` and `(1 + ω)/2 ↦ (0,1)` are the
idempotents that do the splitting. Surjectivity is then eight explicit elements.

## Where the wall now stands

Base cases reached: `p − q ≡ 0, 1, 2, 5, 6, 7`. **Missing: `p − q ≡ 3` and `≡ 4`.**

Those are `Cl(3,0) ≅ M₂(ℂ)` and `Cl(4,0) ≅ M₂(ℍ)` in the standard table. **Neither splits.** Both
are simple algebras, so no central idempotent exists to split them and the technique used twice here
provably cannot reach them — a matrix representation has to be built and checked, as
`CliffordRealMinkowski` and `CliffordRealMajorana` did for `Cl(1,3)` and `Cl(3,1)`. That is a
different kind of work, not a harder instance of this kind.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealSplitQuat

open QuadraticForm QuadraticMap CliffordAlgebra SignatureArithmetic
open scoped Quaternion

noncomputable section

/-- signature `(0,3)`: `−x² − y² − z²`. -/
abbrev Q₀₃ : QuadraticForm ℝ ((ℝ × ℝ) × ℝ) :=
  (CliffordAlgebraQuaternion.Q (-1 : ℝ) (-1)).prod ((-1 : ℝ) • QuadraticMap.sq)

/-- `e₁ ↦ (i,i)`, `e₂ ↦ (j,j)`, `e₃ ↦ (k,−k)`. The sign on the last coordinate is the whole
construction: it is what makes the volume element `(−1, 1)` rather than central-and-trivial. -/
def quatSplitMap : ((ℝ × ℝ) × ℝ) →ₗ[ℝ] ℍ[ℝ] × ℍ[ℝ] where
  toFun v := (⟨0, v.1.1, v.1.2, v.2⟩, ⟨0, v.1.1, v.1.2, -v.2⟩)
  map_add' x y := by ext <;> simp; ring
  map_smul' c x := by ext <;> simp

@[simp] theorem quatSplitMap_apply (v : (ℝ × ℝ) × ℝ) :
    quatSplitMap v = (⟨0, v.1.1, v.1.2, v.2⟩, ⟨0, v.1.1, v.1.2, -v.2⟩) := rfl

theorem quatSplitMap_sq (v : (ℝ × ℝ) × ℝ) :
    quatSplitMap v * quatSplitMap v = algebraMap ℝ (ℍ[ℝ] × ℍ[ℝ]) (Q₀₃ v) := by
  ext <;>
    simp [Prod.algebraMap_apply, QuadraticMap.prod_apply, CliffordAlgebraQuaternion.Q_apply,
      QuadraticMap.sq] <;>
    ring

/-- The algebra map out of `Cl(0,3)`. -/
def toQuatSplit : CliffordAlgebra Q₀₃ →ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] :=
  CliffordAlgebra.lift Q₀₃ ⟨quatSplitMap, quatSplitMap_sq⟩

@[simp] theorem toQuatSplit_ι (v : (ℝ × ℝ) × ℝ) :
    toQuatSplit (ι Q₀₃ v) = (⟨0, v.1.1, v.1.2, v.2⟩, ⟨0, v.1.1, v.1.2, -v.2⟩) :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-! ### The three generators, and the two idempotents they build -/

/-- `e₁`, `e₂`, `e₃`. -/
def e₁ : CliffordAlgebra Q₀₃ := ι Q₀₃ ((1, 0), 0)
def e₂ : CliffordAlgebra Q₀₃ := ι Q₀₃ ((0, 1), 0)
def e₃ : CliffordAlgebra Q₀₃ := ι Q₀₃ ((0, 0), 1)

/-- The volume element `ω = e₁e₂e₃`. Kept as a definition rather than written out, so that
`map_mul` cannot recurse into it when the theorems below transport along the isomorphism. -/
def vol : CliffordAlgebra Q₀₃ := e₁ * e₂ * e₃

/-- **The volume element goes to `(−1, 1)`**, which is the fact the whole file turns on. -/
theorem toQuatSplit_vol : toQuatSplit vol = (-1, 1) := by
  simp only [vol, e₁, e₂, e₃, map_mul, toQuatSplit_ι, Prod.mk_mul_mk, Prod.mk.injEq]
  constructor <;> ext <;> simp

/-- `P` and `P'`, the complementary idempotents, as elements of the Clifford algebra. -/
def P : CliffordAlgebra Q₀₃ := (2⁻¹ : ℝ) • (1 - vol)
def P' : CliffordAlgebra Q₀₃ := (2⁻¹ : ℝ) • (1 + vol)

theorem toQuatSplit_P : toQuatSplit P = (1, 0) := by
  simp only [P, map_smul, map_sub, map_one, toQuatSplit_vol]
  ext <;> simp; norm_num

theorem toQuatSplit_P' : toQuatSplit P' = (0, 1) := by
  simp only [P', map_smul, map_add, map_one, toQuatSplit_vol]
  ext <;> simp; norm_num

/-- **Surjective.** The eight elements `P·{1,e₁,e₂,e₃}` and `P'·{1,e₁,e₂,e₃}` land on a basis of
`ℍ × ℍ`, so an explicit preimage can be written down coordinate by coordinate. -/
theorem toQuatSplit_surjective : Function.Surjective toQuatSplit := by
  rintro ⟨p, q⟩
  refine ⟨p.re • P + p.imI • (P * e₁) + p.imJ • (P * e₂) + p.imK • (P * e₃)
        + q.re • P' + q.imI • (P' * e₁) + q.imJ • (P' * e₂) - q.imK • (P' * e₃), ?_⟩
  simp only [map_add, map_sub, map_smul, map_mul, toQuatSplit_P, toQuatSplit_P',
    toQuatSplit_ι, e₁, e₂, e₃]
  ext <;> simp

/-- **`Cl(0,3;ℝ) ≅ ℍ × ℍ`.** -/
def equivSplitQuat : CliffordAlgebra Q₀₃ ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ] := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  refine CliffordDimension.cliffordAlgEquivOfSurjective ℝ ((ℝ × ℝ) × ℝ) Q₀₃ toQuatSplit
    toQuatSplit_surjective ?_
  rw [Module.finrank_prod, Quaternion.finrank_eq_four]
  norm_num

/-! ### The mechanism, proved rather than described

The header says the splitting exists because the volume element squares to `+1` and is central.
Both were prose about the *reason*; the construction below never used either, since it goes through
an explicit map. **Adversarial review of this file's own header turned them into theorems**, by
transporting along the isomorphism just built — `ω ↦ (−1, 1)`, which squares to `1` and is central
in `ℍ × ℍ` because `±1` is central in `ℍ`. -/

@[simp] theorem equivSplitQuat_apply (x : CliffordAlgebra Q₀₃) :
    equivSplitQuat x = toQuatSplit x := rfl

/-- **The volume element squares to one.** This is the sentence the whole file turns on, and it is
now a theorem rather than a remark. -/
theorem vol_sq : vol * vol = 1 := by
  apply equivSplitQuat.injective
  simp only [equivSplitQuat_apply, map_mul, map_one, toQuatSplit_vol]
  ext <;> simp

/-- **And it is central**, which is the other half of the stated reason. -/
theorem vol_central (x : CliffordAlgebra Q₀₃) : vol * x = x * vol := by
  apply equivSplitQuat.injective
  simp only [equivSplitQuat_apply, map_mul, toQuatSplit_vol]
  ext <;> simp

/-- `P` and `P'` really are complementary idempotents, which the header called them. -/
theorem P_idem : P * P = P := by
  apply equivSplitQuat.injective
  simp only [map_mul, equivSplitQuat_apply, toQuatSplit_P]
  ext <;> simp

theorem P'_idem : P' * P' = P' := by
  apply equivSplitQuat.injective
  simp only [map_mul, equivSplitQuat_apply, toQuatSplit_P']
  ext <;> simp

theorem P_mul_P' : P * P' = 0 := by
  apply equivSplitQuat.injective
  simp only [map_mul, map_zero, equivSplitQuat_apply, toQuatSplit_P, toQuatSplit_P']
  ext <;> simp

/-! ### Its signature — `p − q ≡ 5` -/

theorem sigPos_Q₀₃ : sigPos Q₀₃ = 0 := by
  rw [Q₀₃, sigPos_prod, CliffordRealSignatures.sigPos_quaternionQ, sigPos_smul_sq]
  norm_num

theorem sigNeg_Q₀₃ : sigNeg Q₀₃ = 3 := by
  rw [Q₀₃, sigNeg_prod, CliffordRealSignatures.sigNeg_quaternionQ, sigNeg_smul_sq]
  norm_num

/-- **`p − q = −3 ≡ 5 (mod 8)`**, the second diagonal taken off the wall. -/
theorem diagonal_five : sigPos Q₀₃ = 0 ∧ sigNeg Q₀₃ = 3 := ⟨sigPos_Q₀₃, sigNeg_Q₀₃⟩

theorem sep_Q₀₃ : (QuadraticMap.associated (R := ℝ) Q₀₃).SeparatingLeft :=
  CliffordRealSignatures.separatingLeft_of_sig (by rw [sigPos_Q₀₃, sigNeg_Q₀₃]; simp)

/-- **Every** nondegenerate real form of dimension 3 with `sigPos = 0` gives `ℍ × ℍ`. -/
theorem clifford_iso_quatSplit_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 3) (hsig : sigPos Q = 0) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] ℍ[ℝ] × ℍ[ℝ]) := by
  obtain ⟨e⟩ := CliffordRealQuantified.cliffordEquiv_of_sigPos_eq hQ sep_Q₀₃
    (by simp [hdim]) (by rw [hsig, sigPos_Q₀₃])
  exact ⟨e.trans equivSplitQuat⟩

end

end CliffordRealSplitQuat
