/-
  LorentzReflection.lean — the determinant of a Minkowski reflection, and
  with it det = 1 on the whole two-reflection family.

  WHY THIS FILE EXISTS, AND IT IS A CORRECTION. Two units ago this project
  probed the route to "the spin image lies in SO⁺(1,3)" and reported the
  obstruction as `det(conjugation by a single ι(v)) = −1` for a general
  non-null `v`, with three blocked routes. Route (a) was the **matrix
  determinant lemma**, `det(1 + u vᵀ) = 1 + v ⬝ᵥ u`, and the probe recorded
  it as **verified ABSENT from Mathlib**, having grepped for
  `det_vecMulVec` and `det_one_add_smul`.

  **That absence claim was false.** Mathlib has the lemma, as
  `Matrix.det_one_add_replicateCol_mul_replicateRow`, in
  `LinearAlgebra/Matrix/SchurComplement.lean` — a file one does not think
  to search for a determinant identity — under the `replicateCol` /
  `replicateRow` spelling. It also has the Weinstein–Aronszajn identity
  `Matrix.det_one_add_mul_comm`, which is the general tool the special case
  is derived from. See ERRATUM 42; this file is the fold-back, by proving
  the thing rather than by amending the sentence.

  WHAT THIS FILE PROVES:
  1. **`det_vecMulVec_sub_one`** — for `u w : ℝ⁴` with `w ⬝ᵥ u = 2`,
     `det (u wᵀ − I) = −1`. The rank-one determinant fact, in the exact
     shape a reflection has. Proved through `det_one_add_mul_comm` rather
     than through the special case, because the special case derives its
     `Fintype ι` instance from `Unique ι` and so does not rewrite against
     `Fin 1`'s own instance.
  2. **`reflMat`** and **`det_reflMat`** — the Minkowski reflection in a
     non-null vector `p`, as an explicit 4×4 matrix, with determinant −1.
  3. **`coord_vreflect`** — that matrix IS the estate's `vreflect`, read in
     coordinates. Without this the previous item is a matrix fact about
     nothing in particular.
  4. **`det_spinToO13_pair = 1`** — hence every element of the `pair`
     family, `ι(v)·ι(w)` with `Q₁₃ v · Q₁₃ w = 1`, has a PROPER Lorentz
     matrix. `SpinToLorentzMat` had `det = 1` for one hand-picked element
     and labelled it "one data point, NOT a statement about the image";
     this replaces the data point with the family.
  5. **`reflMat_e₁`** — added by review round 25, and it is what makes
     item 2 worth having: a determinant is worthless if the matrix is not
     the map it claims to be. The reflection in `e₁` is
     `diag(−1, 1, −1, −1)`, entry by entry. With
     `det_spinToO13_R₁₂_via_pair` and `det_spinToO13_B_via_pair`, which
     recover by this route the two determinants the estate had already
     computed by unrelated ones, and `det_reflMat_null` /
     `coord_vreflect_null_ne`, which show the non-null hypotheses are
     load-bearing rather than technical.

  WHAT THIS DOES NOT DO. The `pair` family is not the spin group: a
  product of four or six vectors is a spin element and is not a `pair`,
  and pinning `det` on all of them needs a parity induction over
  `lipschitzGroup`, which needs the conjugation action defined at
  Lipschitz level rather than at spin level — not built here. And `det = 1`
  is only HALF of "the image lies in SO⁺(1,3)": orthochronicity, `Λ⁰₀ > 0`,
  is untouched and has no route. **W7 step (d) is not closed.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import MinkowskiSignature
import LorentzGroup
import LorentzIsometryEquiv
import SpinPair
import SpinMinkowskiBridge
import SpinToLorentzMat

namespace LorentzReflection

open MinkowskiSignature LorentzGroup SpinVectorRep SpinToOrthogonal
open SpinMinkowskiBridge SpinToLorentzMat SpinPair
open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

/-! ## 1. The rank-one determinant fact

The matrix determinant lemma, in the one shape this file needs. Mathlib's
`det_one_add_replicateCol_mul_replicateRow` states exactly this, but its
`Fintype ι` instance is derived from `Unique ι` and therefore does not
match `Fin 1`'s own `Fintype` instance syntactically, so `rw` fails against
it. Going one step further back, to `det_one_add_mul_comm`, avoids the
mismatch: there the index types carry explicit `Fintype` arguments.
-/

/-- **The rank-one determinant fact.** If `w ⬝ᵥ u = 2` then the matrix
    `u wᵀ − I` has determinant `−1`. In four dimensions the sign flip
    `(−1)⁴ = 1` is free, which is why this is stated at `Fin 4`. -/
theorem det_vecMulVec_sub_one (u w : Fin 4 → ℝ) (h : w ⬝ᵥ u = 2) :
    (Matrix.vecMulVec u w - 1 : Matrix (Fin 4) (Fin 4) ℝ).det = -1 := by
  set A : Matrix (Fin 4) (Fin 1) ℝ := Matrix.of fun i _ => -u i with hA
  set B : Matrix (Fin 1) (Fin 4) ℝ := Matrix.of fun _ j => w j with hB
  have hAB : A * B = -Matrix.vecMulVec u w := by
    ext i j
    simp [hA, hB, Matrix.mul_apply, Matrix.vecMulVec_apply]
  have hBA : B * A = Matrix.of fun _ _ => -(2 : ℝ) := by
    ext i j
    simp [hA, hB, Matrix.mul_apply, ← h, dotProduct]
  have step : (Matrix.vecMulVec u w - 1 : Matrix (Fin 4) (Fin 4) ℝ)
      = -(1 + A * B) := by rw [hAB]; abel
  rw [step, Matrix.det_neg, Matrix.det_one_add_mul_comm, hBA, Matrix.det_fin_one]
  norm_num

/-! ## 2. The Minkowski reflection as a matrix

`reflMat p` is `q ↦ (2⟨p,q⟩/Q(p))·p − q`, written as a rank-one update of
`−I`. It is minus the reflection in the hyperplane `p^⊥`; in four
dimensions the extra minus sign does not change the determinant, which is
why a reflection and its negative are interchangeable here.
-/

/-- The Gram pairing against `p` returns `Q(p)` on `p` itself. -/
theorem gram_dotProduct_self (p : Fin 4 → ℝ) :
    (gram *ᵥ p) ⬝ᵥ p = minkowskiForm p := by
  rw [dotProduct_comm, ← LorentzIsometryEquiv.bil_eq_dotProduct, bil_self]

/-- The Gram pairing is the estate's `bil`, with the arguments in the
    order the reflection formula produces them. -/
theorem gram_dotProduct (p q : Fin 4 → ℝ) : (gram *ᵥ p) ⬝ᵥ q = bil q p := by
  rw [dotProduct_comm, ← LorentzIsometryEquiv.bil_eq_dotProduct]

theorem bil_comm (p q : Fin 4 → ℝ) : bil p q = bil q p := by
  simp only [bil]; ring

/-- **The Minkowski reflection in `p`, as an explicit 4×4 matrix.** -/
def reflMat (p : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.vecMulVec ((2 / minkowskiForm p) • p) (gram *ᵥ p) - 1

/-- **Its determinant is `−1`** — the whole point of §1. -/
theorem det_reflMat {p : Fin 4 → ℝ} (hp : minkowskiForm p ≠ 0) :
    (reflMat p).det = -1 := by
  refine det_vecMulVec_sub_one _ _ ?_
  rw [dotProduct_smul, gram_dotProduct_self, smul_eq_mul]
  field_simp

/-- How it acts, which is what ties it to the reflection formula. -/
theorem reflMat_mulVec (p q : Fin 4 → ℝ) :
    reflMat p *ᵥ q = (2 * bil q p / minkowskiForm p) • p - q := by
  have hv : ∀ a b r : Fin 4 → ℝ, Matrix.vecMulVec a b *ᵥ r = (b ⬝ᵥ r) • a := by
    intro a b r
    ext i
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum,
      mul_comm, mul_left_comm]
  rw [reflMat, Matrix.sub_mulVec, hv, Matrix.one_mulVec, gram_dotProduct,
    smul_smul]
  congr 1
  field_simp

/-! ## 3. That matrix is the estate's `vreflect`, in coordinates

`SpinPair.vreflect` lives on `(ℝ×ℝ)×(ℝ×ℝ)` and is written with
`QuadraticMap.polar`; `reflMat` lives on `Fin 4 → ℝ` and is written with
the Gram matrix. Nothing so far says they are the same map, and §2 is a
fact about nothing in particular until they are.
-/

/-- The coordinate map is an isometry, unfolded to the form the rewrites
    below want. -/
@[simp] theorem minkowskiForm_coordEquiv (v : SpinVectorRep.V) :
    minkowskiForm (coordEquiv v) = Q₁₃ v :=
  Q₁₃IsometryMinkowski.map_app v

/-- …and therefore carries the polar form across as well. -/
theorem polar_coordEquiv (v u : SpinVectorRep.V) :
    QuadraticMap.polar Q₁₃ v u
      = 2 * bil (coordEquiv u) (coordEquiv v) := by
  have e : ∀ x : SpinVectorRep.V, Q₁₃ x = minkowskiForm (coordEquiv x) :=
    fun x => (minkowskiForm_coordEquiv x).symm
  rw [QuadraticMap.polar, e v, e u, e (v + u), map_add]
  simp only [minkowskiForm_apply, bil, Pi.add_apply]
  ring

/-- **`reflMat` IS `vreflect`, read in coordinates.** The hypothesis is not
    decoration: at a null `v` the two sides genuinely disagree, since
    `vreflect v` collapses to `0` while `reflMat (coordEquiv v)` collapses
    to `−I`. -/
theorem coord_vreflect {v : SpinVectorRep.V} (hv : Q₁₃ v ≠ 0)
    (u : SpinVectorRep.V) :
    coordEquiv (vreflect v u) = reflMat (coordEquiv v) *ᵥ coordEquiv u := by
  rw [reflMat_mulVec, minkowskiForm_coordEquiv, ← polar_coordEquiv, vreflect,
    map_smul, map_sub, map_smul, map_smul, smul_sub, smul_smul, smul_smul,
    inv_mul_cancel₀ hv, one_smul, div_eq_inv_mul]

/-! ## 4. Determinant 1 on the whole two-reflection family -/

/-- The Lorentz matrix of a `pair` element is the product of the two
    reflection matrices. -/
theorem spinToO13_pair_matrix {v w : SpinVectorRep.V} (hv : Q₁₃ v ≠ 0)
    (hw : Q₁₃ w ≠ 0) (hprod : Q₁₃ v * Q₁₃ w = 1) :
    ((spinToO13 ⟨(pair hv hw : Cl), pair_mem hv hw hprod⟩ :
        Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)
      = reflMat (coordEquiv v) * reflMat (coordEquiv w) := by
  ext i j
  -- `endo` is indexed by `toUnits g`, `spinToEndo_pair` by the unit `pair hv hw`.
  -- The two units are equal, but only `spinToEndo_congr` gets that under the
  -- membership proof cheaply — comparing them by `rfl` exhausts the whnf budget.
  have hend : endo ⟨(pair hv hw : Cl), pair_mem hv hw hprod⟩
      (coordEquiv.symm (Pi.single j 1))
      = vreflect v (vreflect w (coordEquiv.symm (Pi.single j 1))) := by
    rw [endo, spinToEndo_congr
      (toUnits_mem ⟨(pair hv hw : Cl), pair_mem hv hw hprod⟩)
      (pair_mem hv hw hprod) (Units.ext rfl) _]
    exact spinToEndo_pair hv hw hprod _
  have hcoord : coordEquiv (endo ⟨(pair hv hw : Cl), pair_mem hv hw hprod⟩
        (coordEquiv.symm (Pi.single j 1)))
      = (reflMat (coordEquiv v) * reflMat (coordEquiv w)) *ᵥ Pi.single j 1 := by
    rw [hend, coord_vreflect hv, coord_vreflect hw,
      LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec]
  rw [spinToO13_apply_entry, hcoord]
  simp [Matrix.mulVec_single]

/-- **Every element of the `pair` family has a proper Lorentz matrix.**
    `SpinToLorentzMat.det_spinToO13_R₁₂'` had this for one hand-picked
    element and said so in its docstring; this is the family. -/
theorem det_spinToO13_pair {v w : SpinVectorRep.V} (hv : Q₁₃ v ≠ 0)
    (hw : Q₁₃ w ≠ 0) (hprod : Q₁₃ v * Q₁₃ w = 1) :
    ((spinToO13 ⟨(pair hv hw : Cl), pair_mem hv hw hprod⟩ :
        Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
  rw [spinToO13_pair_matrix hv hw hprod, Matrix.det_mul,
    det_reflMat (by rwa [minkowskiForm_coordEquiv]),
    det_reflMat (by rwa [minkowskiForm_coordEquiv])]
  norm_num

/-! ## 5. Which matrix, and what the hypotheses are doing

Review round 25's fold. §4 is a determinant computation, and a determinant
computation is worthless if the matrix is not the map it claims to be —
that was review round 20's finding one level down, and it applies here
verbatim. §5.1 pins the matrix. §5.2 checks the new general theorem against
the two elements the estate had already computed by unrelated routes.
§5.3 shows the two hypotheses are load-bearing rather than technical.
-/

/-- **Which matrix.** The reflection in the spacelike `e₁` is
    `diag(−1, 1, −1, −1)`: it fixes the x-axis and negates everything
    else, which is minus the reflection in the hyperplane `x = 0`, as
    §2's docstring says. -/
theorem reflMat_e₁ : reflMat (coordEquiv e₁) = Matrix.diagonal ![-1, 1, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflMat, coordEquiv, e₁, minkowskiForm_apply, gram, mw,
      Matrix.mulVec_diagonal]
  norm_num

/-- **The new general theorem agrees with the old hand computation.**
    `SpinToLorentzMat.det_spinToO13_R₁₂'` got `det = 1` for the π-rotation
    from an explicit diagonal matrix and `det_diagonal`; this file gets it
    from two reflection determinants and the matrix determinant lemma. The
    two routes share nothing, so agreement is evidence and disagreement
    would have condemned one of them. -/
private theorem hQ₁₂ : Q₁₃ e₁ * Q₁₃ e₂ = 1 := by rw [Q₁₃_e₁, Q₁₃_e₂]; norm_num

private theorem hQw : Q₁₃ SpinBoost.w ≠ 0 := by rw [SpinBoost.Q₁₃_w]; norm_num

private theorem hQ₀w : Q₁₃ e₀ * Q₁₃ SpinBoost.w = 1 := by
  rw [Q₁₃_e₀, SpinBoost.Q₁₃_w]; norm_num

theorem det_spinToO13_R₁₂_via_pair :
    ((spinToO13 ⟨(pair Q₁₃_e₁_ne Q₁₃_e₂_ne : Cl),
        pair_mem Q₁₃_e₁_ne Q₁₃_e₂_ne hQ₁₂⟩ :
      Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ).det = 1 :=
  det_spinToO13_pair _ _ hQ₁₂

/-- And the same for the boost, whose earlier `det = 1` went through a
    Laplace expansion this route never touches. -/
theorem det_spinToO13_B_via_pair :
    ((spinToO13 ⟨(pair Q₁₃_e₀_ne hQw : Cl), pair_mem Q₁₃_e₀_ne hQw hQ₀w⟩ :
      Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ).det = 1 :=
  det_spinToO13_pair _ _ hQ₀w

/-- At a null `p` the reflection matrix collapses to `−I`. -/
theorem reflMat_null {p : Fin 4 → ℝ} (hp : minkowskiForm p = 0) :
    reflMat p = -1 := by
  rw [reflMat, hp]
  ext i j
  simp

/-- **`det_reflMat`'s hypothesis is load-bearing.** In four dimensions
    `det(−I) = +1`, so a null vector gives the opposite answer. -/
theorem det_reflMat_null {p : Fin 4 → ℝ} (hp : minkowskiForm p = 0) :
    (reflMat p).det ≠ -1 := by
  rw [reflMat_null hp, Matrix.det_neg, Matrix.det_one]
  norm_num

/-- **`coord_vreflect`'s hypothesis is load-bearing too**, and this is the
    theorem its docstring previously only asserted: at a null `v` the two
    sides are `0` and `−q`, which differ. -/
theorem coord_vreflect_null_ne :
    coordEquiv (vreflect (((1, 1), (0, 0)) : SpinVectorRep.V) e₂)
      ≠ reflMat (coordEquiv (((1, 1), (0, 0)) : SpinVectorRep.V)) *ᵥ coordEquiv e₂ := by
  have hz : Q₁₃ (((1, 1), (0, 0)) : SpinVectorRep.V) = 0 := by
    rw [Q₁₃_apply]; norm_num
  have hL : coordEquiv (vreflect (((1, 1), (0, 0)) : SpinVectorRep.V) e₂) = 0 := by
    rw [vreflect, hz]; simp
  have hR : reflMat (coordEquiv (((1, 1), (0, 0)) : SpinVectorRep.V)) *ᵥ coordEquiv e₂
      = -coordEquiv e₂ := by
    rw [reflMat_mulVec, minkowskiForm_coordEquiv, hz]; simp
  rw [hL, hR]
  intro hcon
  have h2 := congrFun hcon 2
  simp [coordEquiv, e₂] at h2

/-- **§1's hypothesis pins the value, not merely the sign.** At
    `w ⬝ᵥ u = 4` the determinant is `−3`, so `det_vecMulVec_sub_one` is
    reading the dot product rather than exploiting the shape. -/
theorem det_vecMulVec_sub_one_corrupt :
    (Matrix.vecMulVec ![2, 0, 0, 0] ![2, 0, 0, 0] - 1 :
      Matrix (Fin 4) (Fin 4) ℝ).det = -3 := by
  have h : (Matrix.vecMulVec ![2, 0, 0, 0] ![2, 0, 0, 0] - 1 :
      Matrix (Fin 4) (Fin 4) ℝ) = Matrix.diagonal ![3, -1, -1, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    norm_num
  rw [h, Matrix.det_diagonal, Fin.prod_univ_four]
  simp

end

end LorentzReflection
