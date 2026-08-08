/-
  CliffordEvenBlock.lean — what the EVEN part of Cl(1,3;ℝ) actually is.

  WHY. W7 step (d) is down to one part: surjectivity of
  `spinToO13 : spinGroup Q₁₃ →* SO⁺(1,3)`. The probe recorded in the
  watchlist found Cartan–Dieudonné absent from Mathlib, so the textbook
  route is closed, and named as the executable first step: **look at
  where `Cl⁰(Q₁₃)` goes under the estate's existing
  `cliffordRealMinkowskiEquiv`, and ask whether the image is a
  recognisable copy of M₂(ℂ).** This file is that step, done in Lean
  rather than on paper — ERRATA 40, 41 and 42 are all the same mistake
  of trusting a computation that was never typechecked.

  WHAT THIS FILE PROVES:
  1. **`cplxBlock`** — the matrices `!![a, b; -b, a]` with `a b : ℍ`
     form an ℝ-subalgebra of M₂(ℍ). The multiplication rule is
     `blk a b * blk c d = blk (ac − bd) (ad + bc)`, which is the
     complex-multiplication pattern with quaternion entries.
  2. **`even_image_mem`** — the image of the even part `evenOdd Q₁₃ 0`
     lands inside it. One `even_induction`, whose only real case is that
     a product of two vectors lands in the block form; that in turn is an
     entrywise computation on `!![t, q; q, −t]`.
  3. **An even preimage for each of the eight ℝ-basis elements** of
     `cplxBlock`: `1`, `ι(e₂)ι(e₃)`, `ι(e₃)ι(e₁)`, `ι(e₁)ι(e₂)` for the
     `a` slot and `−ι(e₀)ι(e₁)ι(e₂)ι(e₃)`, `ι(e₀)ι(e₁)`, `ι(e₀)ι(e₂)`,
     `ι(e₀)ι(e₃)` for the `b` slot. **The reverse inclusion itself is
     NOT proved** — see §5's closing note. What §3 gives is containment.
  4. The seven even products of gammas, computed: **`Γ₁Γ₂ = qk·I`**,
     `Γ₃Γ₁ = qj·I`, `Γ₂Γ₃ = qi·I`, `Γ₀Γ₁ = blk 0 qi` and its two
     partners, and **`Γ₀Γ₁Γ₂Γ₃ = blk 0 (−1)`**.

  SO Cl⁰(1,3;ℝ) IS ℍ ⊗_ℝ ℂ IN THE ONLY SENSE THIS FILE ESTABLISHES: the
  `a` slot is a copy of ℍ, the `b` slot is that copy times a central
  square root of −1 (namely `blk 0 1`, whose square is `blk (−1) 0`), and
  they multiply as ℂ does. **What this file does NOT do is exhibit an
  isomorphism with M₂(ℂ), or say anything about SL₂(ℂ), or about
  surjectivity — nor even prove the reverse inclusion, so "Cl⁰(1,3;ℝ) IS
  the block subalgebra" is not established, only "maps into".** ℍ ⊗ ℂ ≅ M₂(ℂ) is a true theorem and it is not proved
  here. W7 step (d)'s surjectivity is untouched; what has changed is that
  the first of the three unprobed steps is now a theorem instead of a
  paper computation, and the second has a concrete target.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import CliffordRealMinkowski

namespace CliffordEvenBlock

open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix Quaternion

noncomputable section

/-! ## 1. The block subalgebra -/

/-- `blk a b` is the matrix `!![a, b; -b, a]`. -/
def blk (a b : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℍ[ℝ] := !![a, b; -b, a]

@[simp] theorem blk_zero_zero (a b : ℍ[ℝ]) : blk a b 0 0 = a := rfl
@[simp] theorem blk_zero_one (a b : ℍ[ℝ]) : blk a b 0 1 = b := rfl
@[simp] theorem blk_one_zero (a b : ℍ[ℝ]) : blk a b 1 0 = -b := rfl
@[simp] theorem blk_one_one (a b : ℍ[ℝ]) : blk a b 1 1 = a := rfl

theorem blk_add (a b c d : ℍ[ℝ]) : blk a b + blk c d = blk (a + c) (b + d) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [blk, add_comm]

theorem blk_smul (r : ℝ) (a b : ℍ[ℝ]) : r • blk a b = blk (r • a) (r • b) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [blk]

/-- **The multiplication rule**: the complex pattern with quaternion
    entries. This is the whole structural content of the file. -/
theorem blk_mul (a b c d : ℍ[ℝ]) :
    blk a b * blk c d = blk (a * c - b * d) (a * d + b * c) := by
  have h : ∀ i j : Fin 2, (blk a b * blk c d) i j
      = blk a b i 0 * blk c d 0 j + blk a b i 1 * blk c d 1 j := fun i j => by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine Matrix.ext fun i j => ?_
  rw [h]
  fin_cases i <;> fin_cases j <;>
    simp only [blk_zero_zero, blk_zero_one, blk_one_zero, blk_one_one,
      Fin.zero_eta, Fin.mk_one] <;>
    ext <;> simp <;> ring

theorem blk_one : blk 1 0 = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [blk]

theorem smul_one_eq_coe (r : ℝ) : r • (1 : ℍ[ℝ]) = ((r : ℍ[ℝ])) := by
  ext <;> simp

theorem blk_algebraMap (r : ℝ) :
    algebraMap ℝ (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) r = blk ((r : ℍ[ℝ])) 0 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [blk, Algebra.algebraMap_eq_smul_one, smul_one_eq_coe]

/-- **The matrices `!![a, b; -b, a]` are an ℝ-subalgebra of M₂(ℍ).** -/
def cplxBlock : Subalgebra ℝ (Matrix (Fin 2) (Fin 2) ℍ[ℝ]) where
  carrier := {M | ∃ a b : ℍ[ℝ], M = blk a b}
  mul_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a * c - b * d, a * d + b * c, blk_mul a b c d⟩
  one_mem' := ⟨1, 0, blk_one.symm⟩
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, blk_add a b c d⟩
  zero_mem' := ⟨0, 0, Matrix.ext fun i j => by fin_cases i <;> fin_cases j <;> simp [blk]⟩
  algebraMap_mem' r := ⟨(r : ℍ[ℝ]), 0, blk_algebraMap r⟩

theorem mem_cplxBlock (a b : ℍ[ℝ]) : blk a b ∈ cplxBlock := ⟨a, b, rfl⟩

/-! ## 2. A product of two vectors is in block form

`cliffordRealMap v` is `!![t, q; q, −t]` with `t` real and `q` a pure
imaginary quaternion — the ODD shape. Two of those multiply into the
even one, and that single computation is the whole of §3's induction.
-/

/-- The odd shape. -/
def oddMat (t : ℝ) (q : ℍ[ℝ]) : Matrix (Fin 2) (Fin 2) ℍ[ℝ] :=
  !![(t : ℍ[ℝ]), q; q, -(t : ℍ[ℝ])]

theorem cliffordRealMap_eq (v : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordRealMap v
      = oddMat v.1.1 (v.1.2 • qi + v.2.1 • qj + v.2.2 • qk) := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [cliffordRealMap, oddMat, Γ₀, Γ₁, Γ₂, Γ₃, qi, qj, qk,
      smul_one_eq_coe]

@[simp] theorem oddMat_zero_zero (t : ℝ) (q : ℍ[ℝ]) :
    oddMat t q 0 0 = (t : ℍ[ℝ]) := rfl
@[simp] theorem oddMat_zero_one (t : ℝ) (q : ℍ[ℝ]) : oddMat t q 0 1 = q := rfl
@[simp] theorem oddMat_one_zero (t : ℝ) (q : ℍ[ℝ]) : oddMat t q 1 0 = q := rfl
@[simp] theorem oddMat_one_one (t : ℝ) (q : ℍ[ℝ]) :
    oddMat t q 1 1 = -(t : ℍ[ℝ]) := rfl

/-- **Two odd matrices multiply into block form.** -/
theorem oddMat_mul (t s : ℝ) (q p : ℍ[ℝ]) :
    oddMat t q * oddMat s p
      = blk ((t : ℍ[ℝ]) * (s : ℍ[ℝ]) + q * p) ((t : ℍ[ℝ]) * p - q * (s : ℍ[ℝ])) := by
  have h : ∀ i j : Fin 2, (oddMat t q * oddMat s p) i j
      = oddMat t q i 0 * oddMat s p 0 j + oddMat t q i 1 * oddMat s p 1 j :=
    fun i j => by rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine Matrix.ext fun i j => ?_
  rw [h]
  fin_cases i <;> fin_cases j <;>
    simp only [oddMat_zero_zero, oddMat_zero_one, oddMat_one_zero,
      oddMat_one_one, blk_zero_zero, blk_zero_one, blk_one_zero, blk_one_one,
      Fin.zero_eta, Fin.mk_one] <;>
    ext <;> simp <;> ring

theorem cliffordRealMap_mul_mem (v w : (ℝ × ℝ) × (ℝ × ℝ)) :
    cliffordRealMap v * cliffordRealMap w ∈ cplxBlock := by
  rw [cliffordRealMap_eq, cliffordRealMap_eq, oddMat_mul]
  exact mem_cplxBlock _ _

/-! ## 3. The even part lands in the block subalgebra -/

/-- **`Cl⁰(1,3;ℝ)` maps into `cplxBlock`.** One induction; the only case
    with content is §2's product. -/
theorem even_image_mem {x : CliffordAlgebra Q₁₃} (hx : x ∈ evenOdd Q₁₃ 0) :
    cliffordRealMinkowskiEquiv x ∈ cplxBlock := by
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
    rw [AlgEquiv.commutes]
    exact cplxBlock.algebraMap_mem r
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, cliffordRealMinkowskiEquiv_ι, cliffordRealMinkowskiEquiv_ι]
    exact mul_mem (cliffordRealMap_mul_mem m₁ m₂) ih

/-! ## 4. The seven even gamma products, computed

These are the preimage witnesses §5 needs, and they are the concrete
content: the `a` slot carries a copy of ℍ (from the purely spatial
products) and the `b` slot carries the same copy multiplied by the
pseudoscalar.
-/

theorem Γ₂_mul_Γ₃ : Γ₂ * Γ₃ = blk qi 0 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Γ₂, Γ₃, blk, Matrix.mul_apply, Fin.sum_univ_two, qj_mul_qk, qi]

theorem Γ₃_mul_Γ₁ : Γ₃ * Γ₁ = blk qj 0 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Γ₃, Γ₁, blk, Matrix.mul_apply, Fin.sum_univ_two, qk_mul_qi, qj]

theorem Γ₁_mul_Γ₂ : Γ₁ * Γ₂ = blk qk 0 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Γ₁, Γ₂, blk, Matrix.mul_apply, Fin.sum_univ_two, qi_mul_qj, qk]

theorem Γ₀_mul_Γ₁ : Γ₀ * Γ₁ = blk 0 qi := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Γ₀, Γ₁, blk, Matrix.mul_apply, Fin.sum_univ_two, qi] <;>
    ext <;> simp

theorem Γ₀_mul_Γ₂ : Γ₀ * Γ₂ = blk 0 qj := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Γ₀, Γ₂, blk, Matrix.mul_apply, Fin.sum_univ_two, qj] <;>
    ext <;> simp

theorem Γ₀_mul_Γ₃ : Γ₀ * Γ₃ = blk 0 qk := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Γ₀, Γ₃, blk, Matrix.mul_apply, Fin.sum_univ_two, qk] <;>
    ext <;> simp

/-- **The pseudoscalar.** `Γ₀Γ₁Γ₂Γ₃ = blk 0 (−1)`, so `blk 0 1` is a
    central square root of `−1` in the even part — which is why the `b`
    slot behaves as the imaginary direction of a complex structure. -/
theorem Γ₀_mul_Γ₁_mul_Γ₂_mul_Γ₃ : Γ₀ * Γ₁ * Γ₂ * Γ₃ = blk 0 (-1) := by
  have hassoc : Γ₀ * Γ₁ * Γ₂ * Γ₃ = (Γ₀ * Γ₁) * (Γ₂ * Γ₃) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, Γ₀_mul_Γ₁, Γ₂_mul_Γ₃, blk_mul]
  congr 1
  · ext <;> simp
  · ext <;> simp [qi]

/-- And it squares to `−1`, which is the statement that makes "complex"
    the right word. -/
theorem blk_i_sq : blk 0 1 * blk 0 1 = blk (-1) 0 := by
  rw [blk_mul]
  simp

/-! ## 5. The image is exactly the block subalgebra

The reverse inclusion, by exhibiting a preimage for every `blk a b`.
`quat_decompose` turns `a` and `b` into real combinations of the four
units, and §4 supplies an even preimage for each.
-/

/-- The eight even generators, as elements of the Clifford algebra. -/
def g₁ : CliffordAlgebra Q₁₃ := 1
def gI : CliffordAlgebra Q₁₃ := ι Q₁₃ ((0, 0), (1, 0)) * ι Q₁₃ ((0, 0), (0, 1))
def gJ : CliffordAlgebra Q₁₃ := ι Q₁₃ ((0, 0), (0, 1)) * ι Q₁₃ ((0, 1), (0, 0))
def gK : CliffordAlgebra Q₁₃ := ι Q₁₃ ((0, 1), (0, 0)) * ι Q₁₃ ((0, 0), (1, 0))
def hR : CliffordAlgebra Q₁₃ := -(ι Q₁₃ ((1, 0), (0, 0)) * ι Q₁₃ ((0, 1), (0, 0)) * ι Q₁₃ ((0, 0), (1, 0)) * ι Q₁₃ ((0, 0), (0, 1)))
def hI : CliffordAlgebra Q₁₃ := ι Q₁₃ ((1, 0), (0, 0)) * ι Q₁₃ ((0, 1), (0, 0))
def hJ : CliffordAlgebra Q₁₃ := ι Q₁₃ ((1, 0), (0, 0)) * ι Q₁₃ ((0, 0), (1, 0))
def hK : CliffordAlgebra Q₁₃ := ι Q₁₃ ((1, 0), (0, 0)) * ι Q₁₃ ((0, 0), (0, 1))

theorem equiv_gI : cliffordRealMinkowskiEquiv gI = blk qi 0 := by
  rw [gI, map_mul, cliffordRealMinkowskiEquiv_e₂, cliffordRealMinkowskiEquiv_e₃]
  exact Γ₂_mul_Γ₃

theorem equiv_gJ : cliffordRealMinkowskiEquiv gJ = blk qj 0 := by
  rw [gJ, map_mul, cliffordRealMinkowskiEquiv_e₃, cliffordRealMinkowskiEquiv_e₁]
  exact Γ₃_mul_Γ₁

theorem equiv_gK : cliffordRealMinkowskiEquiv gK = blk qk 0 := by
  rw [gK, map_mul, cliffordRealMinkowskiEquiv_e₁, cliffordRealMinkowskiEquiv_e₂]
  exact Γ₁_mul_Γ₂

theorem equiv_hI : cliffordRealMinkowskiEquiv hI = blk 0 qi := by
  rw [hI, map_mul, cliffordRealMinkowskiEquiv_e₀, cliffordRealMinkowskiEquiv_e₁]
  exact Γ₀_mul_Γ₁

theorem equiv_hJ : cliffordRealMinkowskiEquiv hJ = blk 0 qj := by
  rw [hJ, map_mul, cliffordRealMinkowskiEquiv_e₀, cliffordRealMinkowskiEquiv_e₂]
  exact Γ₀_mul_Γ₂

theorem equiv_hK : cliffordRealMinkowskiEquiv hK = blk 0 qk := by
  rw [hK, map_mul, cliffordRealMinkowskiEquiv_e₀, cliffordRealMinkowskiEquiv_e₃]
  exact Γ₀_mul_Γ₃

theorem equiv_hR : cliffordRealMinkowskiEquiv hR = blk 0 1 := by
  rw [hR, map_neg, map_mul, map_mul, map_mul, cliffordRealMinkowskiEquiv_e₀,
    cliffordRealMinkowskiEquiv_e₁, cliffordRealMinkowskiEquiv_e₂,
    cliffordRealMinkowskiEquiv_e₃, Γ₀_mul_Γ₁_mul_Γ₂_mul_Γ₃]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [blk]

/-! ### What is NOT proved here, and it is the reverse inclusion

The eight `equiv_*` lemmas above exhibit an even preimage for each of the
eight ℝ-basis elements of `cplxBlock`, so the image of `evenOdd Q₁₃ 0`
contains a spanning set and the reverse inclusion of §3 is TRUE. It is
not a theorem in this file: assembling it needs
`a.re • g₁ + a.imI • gI + … + b.imK • hK` shown to lie in
`evenOdd Q₁₃ 0` and to map to `blk a b`, and both halves exhausted the
elaborator's budget — the membership because `evenOdd` is a `Submodule`
with no `OneMemClass`, so `1 ∈ evenOdd Q₁₃ 0` needs a named lemma this
file does not have, and the image computation because the eight-term
`map_add`/`map_smul` chain is large.

**So what §3 gives is containment, not equality**, and the statement
"Cl⁰(1,3;ℝ) IS the block subalgebra" is NOT established here. Recorded in
the watchlist rather than papered over.
-/

end

end CliffordEvenBlock
