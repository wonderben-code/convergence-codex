import CliffordDimension
import Mathlib.LinearAlgebra.CliffordAlgebra.Equivs

/-!
# `Cl(Q ⊥ ⟨1,−1⟩) ≅ M₂(Cl Q)` over any field — the hyperbolic periodicity step

`CliffordPeriodicity` proves `Cl(Q ⊥ ⟨1,1⟩) ≅ M₂(Cl Q)` **over ℂ**, and the complex classification
is built on it. `WALLS §W7.1` now records the **real** classification as the remaining wall, and
`ERRATUM 204` supplies the check to run first: *before recording a wall, ask of this estate's recent
results whether their hypotheses actually exclude the wall's case.*

**Run on `periodicityEquiv`, the answer is: only one line of it is complex.** `ℂ` enters at exactly
one point — `entZ v = Complex.I • ι Q v` — and it is needed only because the adjoined plane is
`⟨1,1⟩`, so a square root of `−1` is required to make the off-diagonal entry square correctly.

**Adjoin `⟨1,−1⟩` instead and no square root is needed.**

> **`periodicityEquivHyp`** — for any field `K` with `2` invertible and any `Q`,
> `CliffordAlgebra (Q ⊥ ⟨1,−1⟩) ≃ₐ[K] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)`.

Over `ℝ` this is `Cl_{p+1,q+1} ≅ M₂(Cl_{p,q})`, **the first step of the eight-fold way**.

## The construction, which is the same one and slightly simpler

Send the `+1` generator to `σ₁ = !![0,1;1,0]`, the `−1` generator to `!![0,−1;1,0]` (which squares
to `−1` with **real** entries), and each old generator `v` to `ι v · σ₃`. The image of a general
vector is `!![ι v, x−y; x+y, −ι v]`, whose square is `(Q v + x² − y²) • 1` because the off-diagonal
entries are scalars and therefore central. **Every verification is a four-entry computation**, and
`entZ` disappears entirely.

Surjectivity is the same argument, and one step shorter: `σ₁` times the `−1`-generator's image is
`σ₃` directly, so `dg (ι v)` needs no scalar correction.

## What this is NOT

**It is not the real classification.** It is one step of it. The eight-fold way needs the
periodicity
`Cl_{p+8,q} ≅ M₁₆(Cl_{p,q})`, and this supplies only the `(p,q) → (p+1,q+1)` move, which shifts
along the diagonal and **never changes `p − q`**. The classification is governed by `p − q mod 8`,
so **this step alone cannot reach it** — the base cases `Cl_{p,0}` and `Cl_{0,q}` for small `p, q`
are exactly what it does not give, and this estate has `Cl(1,3)` and `Cl(3,1)` and nothing else.

**No real base case is proved here**, and none is claimed.

**Nothing about ℂ changes.** `CliffordPeriodicity` is untouched and is still what the complex ladder
uses; over `ℂ` the two planes `⟨1,1⟩` and `⟨1,−1⟩` are isometric, so this is not a new complex fact.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CliffordPeriodicityHyperbolic

open Matrix CliffordAlgebra

noncomputable section

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] (Q : QuadraticForm K V)

/-- the hyperbolic plane `x² − y²`. -/
abbrev Qhyp : QuadraticForm K (K × K) := CliffordAlgebraQuaternion.Q (1 : K) (-1 : K)

/-- `Q` with a hyperbolic plane adjoined. -/
abbrev QextHyp : QuadraticForm K (V × (K × K)) := Q.prod Qhyp

/-- The representation of the extended generating space inside `M₂(Cl Q)`. -/
def m2 (w : V × (K × K)) : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) :=
  !![ι Q w.1,                            (w.2.1 - w.2.2) • 1;
     (w.2.1 + w.2.2) • 1,                -(ι Q w.1)]

omit [Invertible (2 : K)] in
theorem m2_sq (w : V × (K × K)) : m2 Q w * m2 Q w = algebraMap K _ (QextHyp Q w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [m2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.algebraMap_matrix_apply,
      QuadraticMap.prod_apply, CliffordAlgebraQuaternion.Q_apply, sub_mul, mul_add, add_mul,
      mul_sub, CliffordAlgebra.ι_sq_scalar, Algebra.smul_def, ← map_mul, Algebra.commutes] <;>
    abel_nf <;> simp [mul_comm]

/-- bundled. -/
def map2 : (V × (K × K)) →ₗ[K] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) where
  toFun := m2 Q
  map_add' x y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m2, add_smul, sub_smul] <;> module
  map_smul' c x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [m2, smul_smul, mul_sub, mul_add]

/-- **THE REPRESENTATION.** -/
def toM2 : CliffordAlgebra (QextHyp Q) →ₐ[K] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) :=
  CliffordAlgebra.lift (QextHyp Q) ⟨map2 Q, m2_sq Q⟩

omit [Invertible (2 : K)] in
@[simp] theorem toM2_ι (w : V × (K × K)) : toM2 Q (ι (QextHyp Q) w) = m2 Q w :=
  CliffordAlgebra.lift_ι_apply _ _ w

/-! ## Surjectivity -/

/-- `σ₁`, the image of the `+1` generator. -/
def s1 : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := m2 Q (0, (1, 0))
/-- the image of the `−1` generator. -/
def sm : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := m2 Q (0, (0, 1))
/-- the image of an old generator. -/
def nv (v : V) : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := m2 Q (v, (0, 0))

omit [Invertible (2 : K)] in
theorem s1_mem : s1 Q ∈ (toM2 Q).range := ⟨ι (QextHyp Q) _, toM2_ι _ _⟩
omit [Invertible (2 : K)] in
theorem sm_mem : sm Q ∈ (toM2 Q).range := ⟨ι (QextHyp Q) _, toM2_ι _ _⟩
omit [Invertible (2 : K)] in
theorem nv_mem (v : V) : nv Q v ∈ (toM2 Q).range := ⟨ι (QextHyp Q) _, toM2_ι _ _⟩

omit [Invertible (2 : K)] in
theorem s1_eq : s1 Q = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [s1, m2]

omit [Invertible (2 : K)] in
theorem sm_eq : sm Q = !![0, -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sm, m2]

omit [Invertible (2 : K)] in
theorem nv_eq (v : V) : nv Q v = !![ι Q v, 0; 0, -(ι Q v)] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [nv, m2]

/-- the diagonal copy of `Cl Q`. -/
def dg (a : CliffordAlgebra Q) : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) := !![a, 0; 0, a]

omit [Invertible (2 : K)] in
theorem dg_add (a b) : dg Q (a + b) = dg Q a + dg Q b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg]

omit [Invertible (2 : K)] in
theorem dg_mul (a b) : dg Q (a * b) = dg Q a * dg Q b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

omit [Invertible (2 : K)] in
theorem dg_algebraMap (r : K) :
    dg Q (algebraMap K _ r) = algebraMap K (Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) r := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg, Matrix.algebraMap_matrix_apply]

omit [Invertible (2 : K)] in
/-- `σ₃` is in the image, as `σ₁` times the `−1` generator. -/
theorem s3_mem :
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) ∈ (toM2 Q).range := by
  have h : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) = s1 Q * sm Q := by
    rw [s1_eq, sm_eq]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h]; exact mul_mem (s1_mem Q) (sm_mem Q)

omit [Invertible (2 : K)] in
/-- **THE OLD ALGEBRA SITS DIAGONALLY**, and here it needs no scalar correction. -/
theorem dg_ι (v : V) : dg Q (ι Q v) = nv Q v * !![1, 0; 0, -1] := by
  rw [nv_eq]
  ext i j; fin_cases i <;> fin_cases j <;> simp [dg, Matrix.mul_apply, Fin.sum_univ_two]

omit [Invertible (2 : K)] in
theorem dg_mem (a : CliffordAlgebra Q) : dg Q a ∈ (toM2 Q).range := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [dg_algebraMap]; exact Subalgebra.algebraMap_mem _ r
  | ι v => rw [dg_ι]; exact mul_mem (nv_mem Q v) (s3_mem Q)
  | mul a b ha hb => rw [dg_mul]; exact mul_mem ha hb
  | add a b ha hb => rw [dg_add]; exact add_mem ha hb

theorem decomp (M : Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q)) :
    M = dg Q (⅟(2 : K) • (M 0 0 + M 1 1))
      + dg Q (⅟(2 : K) • (M 0 0 - M 1 1)) * !![1, 0; 0, -1]
      + dg Q (⅟(2 : K) • (M 0 1 + M 1 0)) * s1 Q
      + dg Q (⅟(2 : K) • (M 1 0 - M 0 1)) * (s1 Q * !![1, 0; 0, -1]) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  rw [s1_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, dg, invOf_eq_inv, smul_add, smul_sub,
      cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
      smul_eq_mul, mul_one, mul_zero, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero,
      mul_neg, neg_sub, zero_add, empty_mul, Equiv.symm_apply_apply, of_add_of, add_cons,
      add_add_sub_cancel, empty_add_empty, one_smul, add_apply, of_apply, cons_val',
      cons_val_zero, cons_val_one, cons_val_fin_one] <;>
    match_scalars <;> field_simp <;> ring

theorem toM2_surjective : Function.Surjective (toM2 Q) := by
  intro M
  have hmem : M ∈ (toM2 Q).range := by
    rw [decomp Q M]
    exact add_mem (add_mem (add_mem (dg_mem Q _) (mul_mem (dg_mem Q _) (s3_mem Q)))
      (mul_mem (dg_mem Q _) (s1_mem Q)))
      (mul_mem (dg_mem Q _) (mul_mem (s1_mem Q) (s3_mem Q)))
  exact hmem

/-! ## The equivalence -/

variable [FiniteDimensional K V]

omit [Invertible (2 : K)] in
theorem finrank_extHyp : Module.finrank K (V × (K × K)) = Module.finrank K V + 2 := by
  simp [Module.finrank_prod]

theorem finrank_M2 :
    Module.finrank K (Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q))
      = 2 ^ (Module.finrank K V + 2) := by
  rw [Module.finrank_matrix K (CliffordAlgebra Q) (Fin 2) (Fin 2),
    CliffordDimension.finrank_cliffordAlgebra K V Q]
  simp [pow_succ]
  ring

/-- **THE HYPERBOLIC PERIODICITY STEP, OVER ANY FIELD WITH `2` INVERTIBLE.** -/
def periodicityEquivHyp :
    CliffordAlgebra (QextHyp Q) ≃ₐ[K] Matrix (Fin 2) (Fin 2) (CliffordAlgebra Q) :=
  CliffordDimension.cliffordAlgEquivOfSurjective K (V × (K × K)) (QextHyp Q)
    (toM2 Q) (toM2_surjective Q) (by rw [finrank_M2 Q, finrank_extHyp])

/-- The equivalence **is** the representation. -/
@[simp] theorem periodicityEquivHyp_apply (x : CliffordAlgebra (QextHyp Q)) :
    periodicityEquivHyp Q x = toM2 Q x := rfl

end

end CliffordPeriodicityHyperbolic
