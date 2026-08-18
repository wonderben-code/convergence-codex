import CliffordRealPauli

/-!
# `Cl(4,0;ℝ) ≅ M₂(ℍ)` — the last residue class

`p − q ≡ 4` was the **only** class of the real classification still without a base case.
`CliffordRealSplit` took `≡ 1`, `CliffordRealSplitQuat` took `≡ 5`, `CliffordRealPauli` took `≡ 3`,
and `ERRATUM 211` is the account of how that list began the day at four.

> **`equivQuatFour`** — `Cl(4,0;ℝ) ≃ₐ[ℝ] M₂(ℍ)`. Signature `(4,0)` proved, so **`p − q = 4`**.

**Every residue class `mod 8` now has a base case in this estate.**

## The map, and why it is one line rather than four matrices

The watchlist item for this class named four quaternionic matrices. They are better written as one:
a vector `(a,b,c,d)` becomes the quaternion `q = a + b i + c j + d k`, and the matrix is
`hMap v = !![0, q; star q, 0]`. Writing the four out would have produced sixteen products to check.

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

## Surjectivity, and why it was short

Sixteen real dimensions, but the structure does the work rather than sixteen coefficients. Products
of two generators give the **central** scalars — `g₃g₄ ↦ −i`, `g₂g₄ ↦ j`, `g₂g₃ ↦ −k` — so `sc q`
realises `!![q,0;0,q]` for **every** quaternion at once. `g₁g₂ ↦ diag(−i, i)` breaks the symmetry
between the diagonal entries, giving `!![−p,0;0,p]`; and `g₁` is the swap, turning diagonal into
off-diagonal. Four half-sums of the target's entries then give the preimage outright.

## What this does and does NOT establish

**It establishes base cases on all eight diagonals.** With
`SignatureArithmetic.sigPos_sub_sigNeg_QextHyp` — the hyperbolic step adds `(1,1)` and so preserves
`p − q` — every `Cl(p,q)` is now *reachable in principle* from one of them.

**It does not establish the classification theorem.** Assembling the base cases and the step into a
statement quantified over all `p` and `q` needs an induction that **is not in this estate**, and no
file here should be read as containing it. What exists is eight base cases, a step, and a proof that
the step preserves the diagonal. **That is the material for the theorem, not the theorem.**

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

/-! ## Stage 2 — surjectivity, and the isomorphism

The scalars come from products of two generators — `g₃g₄ ↦ −i`, `g₂g₄ ↦ j`, `g₂g₃ ↦ −k`, all
central — so `sc q` realises `!![q,0;0,q]` for every quaternion. `g₁g₂ ↦ diag(−i, i)` breaks the
symmetry between the two diagonal entries, and `g₁` swaps the diagonal for the off-diagonal. Four
halves of the target's entries then give an explicit preimage. -/

@[simp] theorem toQuatFour_g₃g₄ :
    toQuatFour (g₃ * g₄) = !![⟨0, -1, 0, 0⟩, 0; 0, ⟨0, -1, 0, 0⟩] := by
  simp only [g₃, g₄, map_mul, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Quaternion.ext_iff]

@[simp] theorem toQuatFour_g₂g₄ :
    toQuatFour (g₂ * g₄) = !![⟨0, 0, 1, 0⟩, 0; 0, ⟨0, 0, 1, 0⟩] := by
  simp only [g₂, g₄, map_mul, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Quaternion.ext_iff]

@[simp] theorem toQuatFour_g₂g₃ :
    toQuatFour (g₂ * g₃) = !![⟨0, 0, 0, -1⟩, 0; 0, ⟨0, 0, 0, -1⟩] := by
  simp only [g₂, g₃, map_mul, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Quaternion.ext_iff]

@[simp] theorem toQuatFour_g₁g₂ :
    toQuatFour (g₁ * g₂) = !![⟨0, -1, 0, 0⟩, 0; 0, ⟨0, 1, 0, 0⟩] := by
  simp only [g₁, g₂, map_mul, toQuatFour_ι]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Quaternion.ext_iff]

/-- Every quaternion, as a central scalar matrix in the image. -/
def sc (q : ℍ[ℝ]) : CliffordAlgebra Q₄₀ :=
  q.re • 1 - q.imI • (g₃ * g₄) + q.imJ • (g₂ * g₄) - q.imK • (g₂ * g₃)

theorem toQuatFour_sc (q : ℍ[ℝ]) : toQuatFour (sc q) = !![q, 0; 0, q] := by
  simp only [sc, map_add, map_sub, map_smul, map_one, toQuatFour_g₃g₄, toQuatFour_g₂g₄,
    toQuatFour_g₂g₃]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Quaternion.ext_iff]

/-- The other diagonal shape, `!![−p, 0; 0, p]`, from `g₁g₂`. The right scalar is `−(p·i)`
because `(−(p·i))·i = p`. -/
def dg (p : ℍ[ℝ]) : CliffordAlgebra Q₄₀ := sc (-(p * ⟨0, 1, 0, 0⟩)) * (g₁ * g₂)

theorem toQuatFour_dg (p : ℍ[ℝ]) : toQuatFour (dg p) = !![-p, 0; 0, p] := by
  simp only [dg, map_mul, toQuatFour_sc]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Quaternion.ext_iff]

/-- **Surjective.** With `u,v` the half-sum and half-difference of the diagonal entries and `s,t`
those of the off-diagonal ones, `sc u + dg v + (sc s + dg t) * g₁` maps onto the target. -/
theorem toQuatFour_surjective : Function.Surjective toQuatFour := by
  intro M
  refine ⟨sc ((2:ℝ)⁻¹ • (M 0 0 + M 1 1)) + dg ((2:ℝ)⁻¹ • (M 1 1 - M 0 0))
        + (sc ((2:ℝ)⁻¹ • (M 0 1 + M 1 0)) + dg ((2:ℝ)⁻¹ • (M 1 0 - M 0 1))) * g₁, ?_⟩
  simp only [map_add, map_mul, toQuatFour_sc, toQuatFour_dg, toQuatFour_g₁]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Quaternion.ext_iff] <;> ring_nf
  all_goals simp

/-- **`Cl(4,0;ℝ) ≃ₐ[ℝ] M₂(ℍ)`** — the last residue class. -/
def equivQuatFour : CliffordAlgebra Q₄₀ ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ] := by
  haveI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  refine CliffordDimension.cliffordAlgEquivOfSurjective ℝ ((ℝ × ℝ) × (ℝ × ℝ)) Q₄₀ toQuatFour
    toQuatFour_surjective ?_
  rw [finrank_target]
  norm_num

/-- **Every** nondegenerate real form of dimension 4 with `sigPos = 4` gives `M₂(ℍ)`. -/
theorem clifford_iso_quatFour_of_sig {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V)
    (hQ : (QuadraticMap.associated (R := ℝ) Q).SeparatingLeft)
    (hdim : Module.finrank ℝ V = 4) (hsig : sigPos Q = 4) :
    Nonempty (CliffordAlgebra Q ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℍ[ℝ]) := by
  obtain ⟨e⟩ := CliffordRealQuantified.cliffordEquiv_of_sigPos_eq hQ sep_Q₄₀
    (by simp [hdim]) (by rw [hsig, sigPos_Q₄₀])
  exact ⟨e.trans equivQuatFour⟩

end

end CliffordRealQuatFour
