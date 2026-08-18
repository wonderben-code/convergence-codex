import CliffordRealPauli

/-!
# `Cl(4,0;ℝ) → M₂(ℍ)` — the last class, stage 1

`p − q ≡ 4` is the **only** residue class of the real classification still without a base case.
`CliffordRealSplit` took `≡ 1`, `CliffordRealSplitQuat` took `≡ 5`, `CliffordRealPauli` took `≡ 3`,
and `ERRATUM 211` is the account of how that list began the day at four.

The watchlist item for this class wrote the representation out rather than gesturing at it, and
asked for it in two stages. **This is stage 1: the map and the Clifford relation.** Surjectivity —
and therefore the isomorphism — is stage 2 and is *not* in this file.

## The map, and why it is one line rather than four matrices

The item named four matrices. They are better written as one: a vector `v = (a,b,c,d)` becomes the
quaternion `q = a + b i + c j + d k`, and the matrix is

`hMap v = !![0, q; star q, 0]`.

The conceptual content is one quaternion identity —
`hMap v * hMap v = !![q · star q, 0; 0, star q · q]`, and `q · star q = star q · q = normSq q` —
and `Q₄₀_eq_normSq` records the matching half: **the positive-definite form `a² + b² + c² + d²` IS
`normSq q`.**

**The Lean proof does not go through that identity, and saying so matters.** `hMap_sq` is discharged
entrywise, by `Quaternion.ext_iff` down to real components and `ring_nf` — an adversarial pass on
this file's own header found `Q₄₀_eq_normSq` listed in the `simp` set and **unused**, which is
exactly the prose-ahead-of-proof shape `CliffordRealSplitQuat`'s review caught this morning. It is
kept as a theorem because it is true and it is the reason the construction works; it is no longer
described as the mechanism of a proof that does not use it.

## What is proved

> **`hMap_sq`** — the Clifford relation, hence **`toQuatFour : Cl(4,0;ℝ) →ₐ[ℝ] M₂(ℍ)`**.

> **`toQuatFour_g₁ … _g₄`** — the four generators land on the four matrices the watchlist item
> named, so the abstract map and the worked-out representation are the same object.

## What is NOT proved

**Surjectivity, and therefore the isomorphism.** `finrank ℝ (M₂(ℍ)) = 16 = 2⁴` holds, so
`CliffordDimension.cliffordAlgEquivOfSurjective` closes it the moment surjectivity exists — the same
shape as the three classes that fell today. **Until then `p − q ≡ 4` is still on the wall**, and the
file title says stage 1 for that reason.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordRealQuatFour

open QuadraticForm QuadraticMap CliffordAlgebra SignatureArithmetic Matrix
open scoped Quaternion

noncomputable section

/-- signature `(4,0)`: `a² + b² + c² + d²`. -/
abbrev Q₄₀ : QuadraticForm ℝ ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (CliffordAlgebraQuaternion.Q (1 : ℝ) 1).prod (CliffordAlgebraQuaternion.Q (1 : ℝ) 1)

/-- The four real coordinates as one quaternion. -/
def quatOf (v : (ℝ × ℝ) × (ℝ × ℝ)) : ℍ[ℝ] := ⟨v.1.1, v.1.2, v.2.1, v.2.2⟩

@[simp] theorem quatOf_apply (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    quatOf v = ⟨v.1.1, v.1.2, v.2.1, v.2.2⟩ := rfl

/-- **`Q₄₀` is the quaternion norm.** This is what makes the Clifford relation a one-liner. -/
theorem Q₄₀_eq_normSq (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    Q₄₀ v = Quaternion.normSq (quatOf v) := by
  simp [QuadraticMap.prod_apply, CliffordAlgebraQuaternion.Q_apply, Quaternion.normSq_def']
  ring

/-- The representation: `v ↦ !![0, q; star q, 0]`. -/
def hMap : ((ℝ × ℝ) × (ℝ × ℝ)) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] where
  toFun v := !![0, quatOf v; star (quatOf v), 0]
  map_add' x y := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> (simp [Quaternion.ext_iff]; try ring_nf)
    all_goals simp
  map_smul' c x := by
    refine Matrix.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [Quaternion.ext_iff]

@[simp] theorem hMap_apply (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    hMap v = !![0, quatOf v; star (quatOf v), 0] := rfl

/-- **The Clifford relation**, from `q · star q = star q · q = ‖q‖²`. -/
theorem hMap_sq (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    hMap v * hMap v = algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) (Q₄₀ v) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply,
      Quaternion.ext_iff] <;>
    ring_nf
  all_goals simp

/-- The algebra map out of `Cl(4,0)`. -/
def toQuatFour : CliffordAlgebra Q₄₀ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  CliffordAlgebra.lift Q₄₀ ⟨hMap, hMap_sq⟩

@[simp] theorem toQuatFour_ι (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    toQuatFour (ι Q₄₀ v) = !![0, quatOf v; star (quatOf v), 0] :=
  CliffordAlgebra.lift_ι_apply _ _ v

/-! ### The four generators land where the watchlist item said they would -/

/-- The four generators. -/
def g₁ : CliffordAlgebra Q₄₀ := ι Q₄₀ ((1, 0), (0, 0))
def g₂ : CliffordAlgebra Q₄₀ := ι Q₄₀ ((0, 1), (0, 0))
def g₃ : CliffordAlgebra Q₄₀ := ι Q₄₀ ((0, 0), (1, 0))
def g₄ : CliffordAlgebra Q₄₀ := ι Q₄₀ ((0, 0), (0, 1))

@[simp] theorem toQuatFour_g₁ : toQuatFour g₁ = !![0, 1; 1, 0] := by
  simp only [g₁, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Quaternion.ext_iff]

@[simp] theorem toQuatFour_g₂ :
    toQuatFour g₂ = !![0, ⟨0, 1, 0, 0⟩; ⟨0, -1, 0, 0⟩, 0] := by
  simp only [g₂, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Quaternion.ext_iff]

@[simp] theorem toQuatFour_g₃ :
    toQuatFour g₃ = !![0, ⟨0, 0, 1, 0⟩; ⟨0, 0, -1, 0⟩, 0] := by
  simp only [g₃, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Quaternion.ext_iff]

@[simp] theorem toQuatFour_g₄ :
    toQuatFour g₄ = !![0, ⟨0, 0, 0, 1⟩; ⟨0, 0, 0, -1⟩, 0] := by
  simp only [g₄, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Quaternion.ext_iff]

/-! ### Its signature — `p − q ≡ 4` -/

theorem sigPos_Q₄₀ : sigPos Q₄₀ = 4 := by
  rw [Q₄₀, sigPos_prod, CliffordRealSignatures.sigPos_quaternionQ]
  norm_num

theorem sigNeg_Q₄₀ : sigNeg Q₄₀ = 0 := by
  rw [Q₄₀, sigNeg_prod, CliffordRealSignatures.sigNeg_quaternionQ]
  norm_num

/-- **`p − q = 4`**, the last class. -/
theorem diagonal_four : sigPos Q₄₀ = 4 ∧ sigNeg Q₄₀ = 0 := ⟨sigPos_Q₄₀, sigNeg_Q₄₀⟩

theorem sep_Q₄₀ : (QuadraticMap.associated (R := ℝ) Q₄₀).SeparatingLeft :=
  CliffordRealSignatures.separatingLeft_of_sig (by rw [sigPos_Q₄₀, sigNeg_Q₄₀]; simp)

/-- The dimension count stage 2 will need, recorded now because it is the half that is free. -/
theorem finrank_target : Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) = 2 ^ 4 := by
  simp [Module.finrank_matrix, Quaternion.finrank_eq_four]

end

end CliffordRealQuatFour
