import BlockOffDiagonal
import TracelessSkewDimension

/-!
# The real half of the block split: `su(p+q)` is `(p² + q² − 1) + 2pq` too

`BlockOffDiagonal` generalised the complex split `sl(4,ℂ) = 9 + 6` to
`(p+q)² − 1 = (p² + q² − 1) + 2pq`, and said in its header what it had **not** done:

> **§4 IS NOT GENERALISED**: the real skew-Hermitian half is one block whose conjugate is the
> other, so its count is `2pq` real dimensions out of `pq` complex entries — a different
> computation, not attempted here.

**This is that computation.** The unit is the one the last file named as undone.

## Why it is genuinely different

Over `ℂ` the two off-diagonal blocks are independent, and the range is a product of two matrix
spaces. Over `ℝ`, skew-Hermiticity forces the lower block to be `−Bᴴ`, so **only one block is
free** — and it is free over `ℂ`, contributing `2pq` **real** dimensions from `pq` complex entries.
The two counts agree and the reasons do not, which is the whole content of `PatiSalamOffDiagonal`
§4 at `p = 3`, `q = 1`.

## What had to be built first

`TracelessSkewDimension` works at `Fin n`, and a block statement needs an arbitrary index type. §1
supplies that, and the chain is short because `SelfAdjointDimension`'s argument was already
index-generic in everything but its statement:

> **`finrank_skewAdjointSub`** — `finrank ℝ (skewAdjoint (Matrix ι ι ℂ)) = (card ι)²`, from
> `two_mul_finrank_selfAdjoint` and `Module.finrank_matrix`, neither of which mentions `Fin`.
>
> **`finrank_tracelessSkewSub`** — `(card ι)² − 1`, by rank–nullity on the imaginary part of the
> trace, which is onto because `I • single i₀ i₀ 1` is skew-Hermitian with trace `I`.

## What is proved

> **`skewOffDiagMap`** — a traceless skew-Hermitian matrix to its upper-right block, `ℝ`-linearly.
> **Surjective** (`skewOffDiagMap_surjective`): `fromBlocks 0 B (−Bᴴ) 0` is skew-Hermitian, has zero
> diagonal blocks, and so is traceless for free.
>
> **`finrank_range_skewOffDiagMap = 2pq`**, and by rank–nullity
> **`finrank_ker_skewOffDiagMap = p² + q² − 1`**.
>
> **`skew_block_splits`** — `(p + q)² − 1 = (p² + q² − 1) + 2pq` over `ℝ`, with both summands
> exhibited; `skew_block_splits_three_one` is `9` and `6`.

## What is NOT claimed

**No transport to `PatiSalamOffDiagonal` §4, and none is built.** That file is over `Fin 4`; this is
over `Fin p ⊕ Fin q`. Equal dimensions and isomorphic index types are **not** a reason to call the
theorems the same — `ERRATUM 316`, applied here as it was in `BlockOffDiagonal`.

**No relation between this file's split and `BlockOffDiagonal`'s is claimed.** They are the same
arithmetic over different fields for different reasons, one space is not a real form of the other in
any statement proved here, and no comparison map exists.

**No physics, no Lie theory, no group.** The kernel is a subspace of matrices; whether its summands
"are" colour and hypercharge is the reading `PatiSalamOffDiagonal` fences.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace SkewBlockOffDiagonal

open Matrix Complex

/-! ## 1. The skew-Hermitian dimension, at an arbitrary finite index type -/

theorem finrank_real_matrixSub (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (Matrix ι ι ℂ) = 2 * Fintype.card ι ^ 2 := by
  rw [Module.finrank_matrix (R := ℝ) (M := ℂ) ι ι, Complex.finrank_real_complex]
  ring

theorem finrank_selfAdjointSub (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (selfAdjoint (Matrix ι ι ℂ)) = Fintype.card ι ^ 2 := by
  haveI : FiniteDimensional ℝ (Matrix ι ι ℂ) := by
    have hfin : Module.Finite ℝ (ι → ι → ℂ) := inferInstance
    exact hfin
  have h := SelfAdjointDimension.two_mul_finrank_selfAdjoint (A := Matrix ι ι ℂ)
  rw [finrank_real_matrixSub ι] at h
  omega

theorem finrank_skewAdjointSub (ι : Type*) [Fintype ι] :
    Module.finrank ℝ (skewAdjoint (Matrix ι ι ℂ)) = Fintype.card ι ^ 2 := by
  rw [SelfAdjointDimension.finrank_skewAdjoint_eq, finrank_selfAdjointSub ι]

/-- The imaginary part of the trace, on the skew-Hermitian matrices at any index type. -/
noncomputable def traceImSub (ι : Type*) [Fintype ι] :
    skewAdjoint (Matrix ι ι ℂ) →ₗ[ℝ] ℝ where
  toFun A := (Matrix.trace (A : Matrix ι ι ℂ)).im
  map_add' A B := by simp [Matrix.trace_add]
  map_smul' c A := by
    simp only [RingHom.id_apply, skewAdjoint.val_smul, Matrix.trace_smul]
    exact Complex.smul_im c _

/-- The traceless skew-Hermitian matrices at any index type. -/
noncomputable def tracelessSkewSub (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Submodule ℝ (skewAdjoint (Matrix ι ι ℂ)) :=
  LinearMap.ker (traceImSub ι)

theorem traceImSub_surjective (ι : Type*) [Fintype ι] [Nonempty ι] :
    Function.Surjective (traceImSub ι) := by
  classical
  intro r
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨⟨Matrix.diagonal (Pi.single i₀ ((r : ℂ) * Complex.I)), ?_⟩, ?_⟩
  · rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hk : i = i₀
      · subst hk
        simp [Matrix.diagonal_apply_eq, Pi.single_eq_same]
      · simp [Matrix.diagonal_apply_eq, Pi.single_eq_of_ne hk]
    · simp [Matrix.diagonal_apply_ne _ hij]
  · simp [traceImSub, Matrix.trace_diagonal]

theorem finrank_tracelessSkewSub (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Module.finrank ℝ (tracelessSkewSub ι) = Fintype.card ι ^ 2 - 1 := by
  haveI : FiniteDimensional ℝ (Matrix ι ι ℂ) := by
    have hfin : Module.Finite ℝ (ι → ι → ℂ) := inferInstance
    exact hfin
  haveI : Module.Finite ℝ (skewAdjoint (Matrix ι ι ℂ)) :=
    Module.Finite.of_injective (skewAdjoint.submodule ℝ (Matrix ι ι ℂ)).subtype
      Subtype.val_injective
  haveI : Module.Finite ℝ (tracelessSkewSub ι) :=
    Module.Finite.of_injective (tracelessSkewSub ι).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker (traceImSub ι)
  rw [LinearMap.range_eq_top.mpr (traceImSub_surjective ι), finrank_top,
    Module.finrank_self, finrank_skewAdjointSub ι] at h
  have h' : 1 + Module.finrank ℝ (tracelessSkewSub ι) = Fintype.card ι ^ 2 := h
  omega

/-! ## 2. The block map: one block, free over `ℂ` -/

variable {p q : ℕ}

/-- The upper-right block of a traceless skew-Hermitian matrix. **The lower-left block is not
read**: skew-Hermiticity determines it as `−Bᴴ`, which is exactly why the real count is `2pq` from
`pq` complex entries and not `4pq` from two free blocks. -/
noncomputable def skewOffDiagMap :
    tracelessSkewSub (Fin p ⊕ Fin q) →ₗ[ℝ] Matrix (Fin p) (Fin q) ℂ where
  toFun M := (((M : skewAdjoint (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).toBlocks₁₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The skew-Hermitian matrix carrying `B` above the diagonal and `−Bᴴ` below it. -/
noncomputable def skewOffDiagOf (B : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 0 B (-Bᴴ) 0

theorem skewOffDiagOf_skew (B : Matrix (Fin p) (Fin q) ℂ) :
    skewOffDiagOf B ∈ skewAdjoint (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
  rw [skewAdjoint.mem_iff, Matrix.star_eq_conjTranspose]
  ext i j
  cases i <;> cases j <;>
    simp [skewOffDiagOf, Matrix.conjTranspose_apply]

theorem skewOffDiagOf_trace (B : Matrix (Fin p) (Fin q) ℂ) :
    Matrix.trace (skewOffDiagOf B) = 0 := by
  simp [skewOffDiagOf, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem skewOffDiagOf_mem (B : Matrix (Fin p) (Fin q) ℂ) :
    (⟨skewOffDiagOf B, skewOffDiagOf_skew B⟩ : skewAdjoint _)
      ∈ tracelessSkewSub (Fin p ⊕ Fin q) := by
  have h : (Matrix.trace (skewOffDiagOf B)).im = 0 := by rw [skewOffDiagOf_trace B]; simp
  exact h

theorem skewOffDiagMap_surjective : Function.Surjective (skewOffDiagMap (p := p) (q := q)) := by
  intro B
  exact ⟨⟨⟨skewOffDiagOf B, skewOffDiagOf_skew B⟩, skewOffDiagOf_mem B⟩, rfl⟩

theorem finrank_range_skewOffDiagMap :
    Module.finrank ℝ (LinearMap.range (skewOffDiagMap (p := p) (q := q))) = 2 * p * q := by
  rw [LinearMap.range_eq_top.mpr skewOffDiagMap_surjective, finrank_top,
    Module.finrank_matrix (R := ℝ) (M := ℂ) (Fin p) (Fin q), Complex.finrank_real_complex]
  simp
  ring

theorem finrank_ker_skewOffDiagMap (hp : 0 < p) :
    Module.finrank ℝ (LinearMap.ker (skewOffDiagMap (p := p) (q := q)))
      = p ^ 2 + q ^ 2 - 1 := by
  have hne : Nonempty (Fin p ⊕ Fin q) := ⟨Sum.inl ⟨0, hp⟩⟩
  haveI : FiniteDimensional ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    have hfin : Module.Finite ℝ ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ) := inferInstance
    exact hfin
  haveI : Module.Finite ℝ (skewAdjoint (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    Module.Finite.of_injective
      (skewAdjoint.submodule ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).subtype
      Subtype.val_injective
  haveI : Module.Finite ℝ (tracelessSkewSub (Fin p ⊕ Fin q)) :=
    Module.Finite.of_injective (tracelessSkewSub (Fin p ⊕ Fin q)).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker (skewOffDiagMap (p := p) (q := q))
  rw [finrank_range_skewOffDiagMap, finrank_tracelessSkewSub] at h
  have hcard : Fintype.card (Fin p ⊕ Fin q) = p + q := by simp
  rw [hcard] at h
  have hsq : (p + q) ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q := by ring
  rw [hsq] at h
  have h1 : 1 ≤ p ^ 2 + q ^ 2 := by nlinarith
  omega

/-! ## 3. The split, over `ℝ` -/

/-- **`(p + q)² − 1 = (p² + q² − 1) + 2pq`, OVER `ℝ`, WITH BOTH SUMMANDS EXHIBITED.** The same
arithmetic as `BlockOffDiagonal.block_splits` and **not the same computation**: there the two
off-diagonal blocks are independent over `ℂ`, here one block is free and its conjugate transpose is
forced. -/
theorem skew_block_splits (hp : 0 < p) :
    Module.finrank ℝ (tracelessSkewSub (Fin p ⊕ Fin q))
      = Module.finrank ℝ (LinearMap.ker (skewOffDiagMap (p := p) (q := q)))
        + Module.finrank ℝ (LinearMap.range (skewOffDiagMap (p := p) (q := q))) := by
  have hne : Nonempty (Fin p ⊕ Fin q) := ⟨Sum.inl ⟨0, hp⟩⟩
  haveI : FiniteDimensional ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
    have hfin : Module.Finite ℝ ((Fin p ⊕ Fin q) → (Fin p ⊕ Fin q) → ℂ) := inferInstance
    exact hfin
  haveI : Module.Finite ℝ (skewAdjoint (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) :=
    Module.Finite.of_injective
      (skewAdjoint.submodule ℝ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).subtype
      Subtype.val_injective
  haveI : Module.Finite ℝ (tracelessSkewSub (Fin p ⊕ Fin q)) :=
    Module.Finite.of_injective (tracelessSkewSub (Fin p ⊕ Fin q)).subtype Subtype.val_injective
  have h := LinearMap.finrank_range_add_finrank_ker (skewOffDiagMap (p := p) (q := q))
  omega

/-- The Pati–Salam instance over `ℝ`: `9` and `6`. **No claim that this is
`PatiSalamOffDiagonal.su4_real_splits_nine_six`** — that is over `Fin 4`, this over
`Fin 3 ⊕ Fin 1`, and no transport is built (`ERRATUM 316`). -/
theorem skew_block_splits_three_one :
    Module.finrank ℝ (LinearMap.ker (skewOffDiagMap (p := 3) (q := 1))) = 9
      ∧ Module.finrank ℝ (LinearMap.range (skewOffDiagMap (p := 3) (q := 1))) = 6 :=
  ⟨by rw [finrank_ker_skewOffDiagMap (by norm_num)]; norm_num,
   by rw [finrank_range_skewOffDiagMap]⟩

end SkewBlockOffDiagonal
