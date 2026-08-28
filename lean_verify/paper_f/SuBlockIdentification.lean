import SuBlockGrading

/-!
# The compact `9 + 6` is the dimension of the graded pieces

`SuBlockGrading` closed two fences and opened one, in writing:

> *"What is still not done is the identification with `SkewBlockOffDiagonal`'s map: nothing says
> `suOdd` is the range of `skewOffDiagMap` or `suEven` its kernel, no comparison map is built, and
> the `9 + 6` split is still a dimension count that no theorem connects to that grading."*

This file is that connection.

## What is proved

> **`toBlocks₂₁_eq_of_mem_skewSub`** — for a skew-Hermitian matrix the lower-left block is
> `−(upper-right)ᴴ`. This is the one fact the whole comparison turns on, and it is what
> `SkewBlockOffDiagonal`'s header means by *"the lower-left block is not read"*.
>
> **`mem_suOdd_iff`** — `suOdd` is **exactly** the set of `skewOffDiagOf B`, so the odd piece of
> the compact grading is the image of that file's section, not merely a space of the same
> dimension.
>
> **`map_ker_skewOffDiagMap`** — and `suEven` is **exactly** `skewOffDiagMap`'s kernel, carried
> into the matrices along the two inclusions.
>
> **`finrank_suOdd = 2pq`**, from the section being an injective real-linear map out of
> `Matrix (Fin p) (Fin q) ℂ`; **`finrank_suEven = p² + q² − 1`** and **`su_block_splits`**, derived
> from `SuBlockGrading.sup_eq` and `inf_eq_bot` through
> `Submodule.finrank_sup_add_finrank_inf_eq` — **so the split is a consequence of the grading**
> rather than a rank–nullity count that happens to agree with it.
>
> **`su_block_splits_three_one`** — `9` and `6` at `p = 3`, `q = 1`, now as the dimensions of the
> two graded pieces of the compact form.

## What is NOT claimed

**No transport to `SkewBlockOffDiagonal.skew_block_splits`.** That theorem is stated about
`finrank (ker skewOffDiagMap)` and `finrank (range skewOffDiagMap)` — subspaces of the two
subtypes it lives in — and this file's numbers are about `suEven` and `suOdd`, subspaces of the
matrices. `map_ker_skewOffDiagMap` relates the two kernels; **the two theorems are not identified,
no equality between them is asserted, and neither is restated in terms of the other**
(`ERRATUM 316`).

**Nothing about `su(4)` as a group or about Pati–Salam.** At `p = 3`, `q = 1` the numbers are the
ones `PatiSalamOffDiagonal` reads as colour-plus-hypercharge and leptoquarks; **that reading is
fenced there and nothing here touches it**.

**Nothing about maximal tori, rank, roots, Cartan subalgebras or irreducibility.** Four units have
now left those fences where they are.

**The name `su` is not used**, following `F4_1e_SpectralTripleArithmetic`.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SuBlockIdentification

open Matrix SkewBlockOffDiagonal TracelessSkewLie SuBlockGrading

variable {p q : ℕ}

/-! ## 1. Skew-Hermiticity determines the lower-left block -/

/-- **THE FACT THE WHOLE COMPARISON TURNS ON.** -/
theorem toBlocks₂₁_eq_of_mem_skewSub {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (h : M ∈ skewSub (Fin p ⊕ Fin q)) : M.toBlocks₂₁ = -(M.toBlocks₁₂)ᴴ := by
  rw [mem_skewSub_iff] at h
  ext j i
  have hij := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
  simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at hij
  simp only [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.neg_apply,
    Matrix.conjTranspose_apply]
  have hstar := congrArg star hij
  simpa using hstar

/-! ## 2. The odd piece is the image of `skewOffDiagOf` -/

theorem skewOffDiagOf_mem_suOdd (B : Matrix (Fin p) (Fin q) ℂ) :
    skewOffDiagOf B ∈ suOdd p q := by
  have hskew : skewOffDiagOf B ∈ skewSub (Fin p ⊕ Fin q) := by
    rw [mem_skewSub_iff]
    have h := skewOffDiagOf_skew B
    rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose] at h
    exact h
  exact ⟨(mem_oddPartR_iff _).mpr (BlockGrading.fromBlocks_off_mem _ _), hskew,
    skewOffDiagOf_trace B⟩

/-- **`suOdd` IS EXACTLY THE IMAGE OF THE SECTION.** -/
theorem mem_suOdd_iff (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    M ∈ suOdd p q ↔ ∃ B : Matrix (Fin p) (Fin q) ℂ, M = skewOffDiagOf B := by
  constructor
  · intro hM
    refine ⟨M.toBlocks₁₂, ?_⟩
    obtain ⟨B, C, hBC⟩ := BlockGrading.exists_of_mem_oddPart ((mem_oddPartR_iff M).mp hM.1)
    have h21 : M.toBlocks₂₁ = -(M.toBlocks₁₂)ᴴ := toBlocks₂₁_eq_of_mem_skewSub hM.2.1
    rw [skewOffDiagOf, ← h21]
    conv_lhs => rw [hBC]
    rw [hBC]
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁]
  · rintro ⟨B, rfl⟩
    exact skewOffDiagOf_mem_suOdd B

/-! ## 3. The even piece is the kernel of `skewOffDiagMap` -/

/-- The two inclusions of `SkewBlockOffDiagonal`'s domain into the matrices, composed. -/
noncomputable def skewInclTwice (p q : ℕ) :
    tracelessSkewSub (Fin p ⊕ Fin q) →ₗ[ℝ] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  (skewIncl (Fin p ⊕ Fin q)).comp (tracelessSkewSub (Fin p ⊕ Fin q)).subtype

theorem skewInclTwice_apply (X : tracelessSkewSub (Fin p ⊕ Fin q)) :
    skewInclTwice p q X
      = ((X : skewAdjoint (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :
          Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := rfl

/-- **`suEven` IS EXACTLY `skewOffDiagMap`'s KERNEL.** -/
theorem map_ker_skewOffDiagMap :
    Submodule.map (skewInclTwice p q) (LinearMap.ker (skewOffDiagMap (p := p) (q := q)))
      = suEven p q := by
  ext M
  constructor
  · rintro ⟨X, hX, rfl⟩
    have hskew : skewInclTwice p q X ∈ skewSub (Fin p ⊕ Fin q) := by
      rw [mem_skewSub_iff]
      have h := skewAdjoint.mem_iff.mp
        (X : skewAdjoint (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).property
      rwa [Matrix.star_eq_conjTranspose] at h
    have h12 : (skewInclTwice p q X).toBlocks₁₂ = 0 := hX
    have h21 : (skewInclTwice p q X).toBlocks₂₁ = 0 := by
      rw [toBlocks₂₁_eq_of_mem_skewSub hskew, h12]
      simp
    refine ⟨(mem_evenPartR_iff _).mpr ((BlockGrading.mem_evenPart_iff _).mpr ⟨h12, h21⟩),
      hskew, ?_⟩
    exact trace_eq_zero_of_im hskew (LinearMap.mem_ker.mp X.property)
  · intro hM
    have hskew : M ∈ skewAdjoint (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
      skewAdjoint.mem_iff.mpr (by rw [Matrix.star_eq_conjTranspose]; exact hM.2.1)
    have him : (Matrix.trace M).im = 0 := by
      have h : Matrix.trace M = 0 := hM.2.2
      rw [h]
      simp
    refine ⟨⟨⟨M, hskew⟩, him⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
    exact ((BlockGrading.mem_evenPart_iff M).mp ((mem_evenPartR_iff M).mp hM.1)).1

/-! ## 4. The dimensions, derived from the grading -/

/-- The section, as a real-linear map. -/
noncomputable def skewOffDiagSection (p q : ℕ) :
    Matrix (Fin p) (Fin q) ℂ →ₗ[ℝ] Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ where
  toFun := skewOffDiagOf
  map_add' B B' := by
    ext i j
    cases i <;> cases j <;>
      simp [skewOffDiagOf, Matrix.conjTranspose_add, add_comm]
  map_smul' r B := by
    ext i j
    cases i <;> cases j <;>
      simp [skewOffDiagOf, Matrix.conjTranspose_smul]

theorem skewOffDiagSection_injective : Function.Injective (skewOffDiagSection p q) := by
  intro B B' h
  ext i j
  have := congrFun (congrFun h (Sum.inl i)) (Sum.inr j)
  simpa [skewOffDiagSection, skewOffDiagOf] using this

theorem range_skewOffDiagSection : LinearMap.range (skewOffDiagSection p q) = suOdd p q := by
  ext M
  constructor
  · rintro ⟨B, rfl⟩
    exact skewOffDiagOf_mem_suOdd B
  · intro hM
    obtain ⟨B, rfl⟩ := (mem_suOdd_iff M).mp hM
    exact ⟨B, rfl⟩

theorem finrank_suOdd : Module.finrank ℝ (suOdd p q) = 2 * p * q := by
  rw [← range_skewOffDiagSection,
    LinearMap.finrank_range_of_inj skewOffDiagSection_injective,
    Module.finrank_matrix (R := ℝ) (M := ℂ) (Fin p) (Fin q), Complex.finrank_real_complex]
  simp
  ring

/-- **THE SPLIT, DERIVED FROM THE GRADING** rather than from a rank–nullity count that happens to
agree with it. -/
theorem su_block_splits :
    Module.finrank ℝ (tracelessSkewMat (Fin p ⊕ Fin q))
      = Module.finrank ℝ (suEven p q) + Module.finrank ℝ (suOdd p q) := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq (suEven p q) (suOdd p q)
  rw [sup_eq, inf_eq_bot, finrank_bot] at h
  omega

theorem finrank_suEven (hp : 0 < p) :
    Module.finrank ℝ (suEven p q) = p ^ 2 + q ^ 2 - 1 := by
  haveI : Nonempty (Fin p ⊕ Fin q) := ⟨Sum.inl ⟨0, hp⟩⟩
  have h := su_block_splits (p := p) (q := q)
  rw [finrank_tracelessSkewMat, finrank_suOdd] at h
  have hcard : Fintype.card (Fin p ⊕ Fin q) = p + q := by simp
  rw [hcard] at h
  have hsq : (p + q) ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q := by ring
  rw [hsq] at h
  have h1 : 1 ≤ p ^ 2 + q ^ 2 := by nlinarith
  omega

/-- `9` and `6`, as the dimensions of the two graded pieces of the compact form. **No claim that
this is `SkewBlockOffDiagonal.skew_block_splits_three_one`**, which is about subspaces of two
different subtypes (`ERRATUM 316`). -/
theorem su_block_splits_three_one :
    Module.finrank ℝ (suEven 3 1) = 9 ∧ Module.finrank ℝ (suOdd 3 1) = 6 :=
  ⟨by rw [finrank_suEven (by norm_num)]; norm_num, by rw [finrank_suOdd]⟩

end SuBlockIdentification
