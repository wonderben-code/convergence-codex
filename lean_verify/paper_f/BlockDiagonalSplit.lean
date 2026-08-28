import BlockOffDiagonal

/-!
# The block-diagonal kernel is `sl(p) ⊕ sl(q) ⊕ ℂ`, exhibited rather than counted

`BlockOffDiagonal` proved `(p + q)² − 1 = (p² + q² − 1) + 2pq` and described the second summand as
a range. **The first was only a number.** `p² + q² − 1` is `(p² − 1) + (q² − 1) + 1`, which reads as
*two traceless blocks and one scalar*, and reading is not proving — this estate's recurring lesson.

**This file exhibits it.** The four-way decomposition of `sl(p+q)` is now
`sl(p) ⊕ sl(q) ⊕ ℂ ⊕ (off-diagonal)`, with every summand the image of a named injection or the
range of a named surjection, and no step asserted about numerals.

## What is proved

> **`blockDiagMap`** — `(A, D, c) ↦ [[A + qc·1, 0], [0, D − pc·1]]`. **The `q` and `p` are what
> make it traceless with no division**: the two scalar contributions are `pqc` and `−qpc`.
>
> **`blockDiagMap_injective`** (for `0 < p`, `0 < q`) and
> **`range_blockDiagMap_eq_ker`** — its range is **exactly** `LinearMap.ker offDiagMap`. The
> forward inclusion is a block computation; the reverse recovers `c = tr X / (pq)`, which is the
> one place a division appears and the one place `p, q ≠ 0` is used for more than injectivity.
>
> **`finrank_ker_eq_sum`** — hence `p² + q² − 1 = (p² − 1) + (q² − 1) + 1` **as a statement about
> three exhibited spaces**, not as arithmetic.

## What is NOT claimed

**No Lie theory.** `tracelessSub` is a submodule of matrices; the summands are called `sl(p)` and
`sl(q)` in this prose and nowhere in the statements. Nothing here says the decomposition respects a
bracket, and no `LieSubalgebra` is built.

**⚠ HALF OF THAT IS NOW FALSE AND THE OTHER HALF IS NAMED, 2026-08-28.**
`BlockGrading.sl_toSubmodule` is `rfl`: `tracelessSub ι` **is** the carrier of Mathlib's
`LieAlgebra.SpecialLinear.sl ι ℂ`, at every `ι` including `Fin p` and `Fin q`. So the summands were
`sl(p)` and `sl(q)` **in the statements** the whole time and the sentence above had simply not
looked; `ERRATUM 313` is the standing record of that error and this is another instance of it.
`BlockGrading` also proves the block decomposition respects the bracket — a ℤ/2-grading of
`gl(p+q)` that restricts to `sl(p+q)` — and builds `BlockGrading.evenLie`, an honest
`LieSubalgebra`. **What is still not proved is the sentence's content at THIS file's own
decomposition**: nothing yet says `blockDiagMap` is a morphism of Lie algebras, i.e. that
`⁅blockDiagMap x, blockDiagMap y⁆ = blockDiagMap ⁅x, y⁆` with the `ℂ` direction central. That is a
different theorem, it is not proved anywhere, and until it is, `sl(p) ⊕ sl(q) ⊕ ℂ` here remains a
decomposition of a **module**.

**No transport to any `Fin n` file**, and none is built — `PatiSalamOffDiagonal`,
`SMEmbeddingHonest` and `ColourCommutant` all work over `Fin 4`.
`SMEmbeddingHonest.colour_bl_finrank` exhibits colour ⊕ `B − L` as a `9`-dimensional subspace
there, and `ERRATUM 317` records the cost of having missed it; **this file is the same shape at
general block size and is not a restatement of it**, the index types being different and no
isomorphism being supplied (`ERRATUM 316`).

**No physics.** Whether the summands "are" colour, weak isospin and hypercharge is the reading
`PatiSalamOffDiagonal` fences; nothing is added to it here.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockDiagonalSplit

open Matrix SlAbelianGeneral BlockOffDiagonal

variable {p q : ℕ}

/-! ## 1. The block-diagonal injection -/

/-- `[[A + qc·1, 0], [0, D − pc·1]]`. The scalar shifts are weighted by the *other* block's size,
so the two trace contributions are `pqc` and `−qpc` and cancel with no division. -/
noncomputable def blockDiagOf (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (c : ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks (A + (q : ℂ) • c • 1) 0 0 (D - (p : ℂ) • c • 1)

/-- The trace of a block-diagonal matrix is the sum of the blocks' traces. -/
theorem trace_fromBlocks_diag (X : Matrix (Fin p) (Fin p) ℂ) (Y : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.trace (Matrix.fromBlocks X 0 0 Y) = Matrix.trace X + Matrix.trace Y := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem blockDiagOf_trace (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) (c : ℂ)
    (hA : Matrix.trace A = 0) (hD : Matrix.trace D = 0) :
    Matrix.trace (blockDiagOf A D c) = 0 := by
  rw [blockDiagOf, trace_fromBlocks_diag, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, Matrix.trace_one, hA, hD]
  simp
  ring

theorem blockDiagOf_mem (A : tracelessSub (Fin p)) (D : tracelessSub (Fin q)) (c : ℂ) :
    blockDiagOf (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) c
      ∈ tracelessSub (Fin p ⊕ Fin q) :=
  LinearMap.mem_ker.mpr
    (blockDiagOf_trace _ _ c (LinearMap.mem_ker.mp A.property) (LinearMap.mem_ker.mp D.property))

noncomputable def blockDiagMap :
    (tracelessSub (Fin p) × tracelessSub (Fin q) × ℂ) →ₗ[ℂ] tracelessSub (Fin p ⊕ Fin q) where
  toFun x := ⟨blockDiagOf (x.1 : Matrix (Fin p) (Fin p) ℂ) (x.2.1 : Matrix (Fin q) (Fin q) ℂ) x.2.2,
    blockDiagOf_mem x.1 x.2.1 x.2.2⟩
  map_add' x y := by
    apply Subtype.ext
    ext i j
    cases i <;> cases j <;>
      · simp only [blockDiagOf, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
          Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
          Submodule.coe_add, Prod.fst_add, Prod.snd_add, smul_eq_mul, mul_ite, mul_zero]
        try split_ifs
        all_goals ring
  map_smul' r x := by
    apply Subtype.ext
    ext i j
    cases i <;> cases j <;>
      · simp only [blockDiagOf, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.add_apply,
          Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.zero_apply,
          Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul,
          mul_ite, mul_zero]
        try split_ifs
        all_goals ring

/-! ## 2. It is injective, and its range is exactly the kernel -/

theorem blockDiagMap_val (A : tracelessSub (Fin p)) (D : tracelessSub (Fin q)) (c : ℂ) :
    ((blockDiagMap (A, D, c) : tracelessSub (Fin p ⊕ Fin q)) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
      = blockDiagOf (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) c := rfl

theorem blockDiagMap_injective (hp : 0 < p) (hq : 0 < q) :
    Function.Injective (blockDiagMap (p := p) (q := q)) := by
  rintro ⟨A, D, c⟩ ⟨A', D', c'⟩ h
  have hval : blockDiagOf (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) c
      = blockDiagOf (A' : Matrix (Fin p) (Fin p) ℂ) (D' : Matrix (Fin q) (Fin q) ℂ) c' :=
    congrArg Subtype.val h
  have hpq : ((p : ℂ) * q) ≠ 0 := by
    have h1 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h2 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact mul_ne_zero h1 h2
  have htop : (A : Matrix (Fin p) (Fin p) ℂ) + (q : ℂ) • c • 1
      = (A' : Matrix (Fin p) (Fin p) ℂ) + (q : ℂ) • c' • 1 := by
    ext i j
    have := congrFun (congrFun hval (Sum.inl i)) (Sum.inl j)
    simpa [blockDiagOf] using this
  have hbot : (D : Matrix (Fin q) (Fin q) ℂ) - (p : ℂ) • c • 1
      = (D' : Matrix (Fin q) (Fin q) ℂ) - (p : ℂ) • c' • 1 := by
    ext i j
    have := congrFun (congrFun hval (Sum.inr i)) (Sum.inr j)
    simpa [blockDiagOf] using this
  have hA0 : Matrix.trace (A : Matrix (Fin p) (Fin p) ℂ) = 0 := LinearMap.mem_ker.mp A.property
  have hA0' : Matrix.trace (A' : Matrix (Fin p) (Fin p) ℂ) = 0 := LinearMap.mem_ker.mp A'.property
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc : c = c' := by
    have h := congrArg Matrix.trace htop
    rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, hA0, hA0'] at h
    simp only [Fintype.card_fin, smul_eq_mul, zero_add] at h
    field_simp at h
    tauto
  subst hc
  have hA : A = A' := Subtype.ext (by
    have := htop
    simpa using congrArg (fun M => M - (q : ℂ) • c • (1 : Matrix (Fin p) (Fin p) ℂ)) this)
  have hD : D = D' := Subtype.ext (by
    have := hbot
    simpa using congrArg (fun M => M + (p : ℂ) • c • (1 : Matrix (Fin q) (Fin q) ℂ)) this)
  simp [hA, hD]

/-! ## 3. The range is exactly the kernel -/

theorem range_blockDiagMap_le_ker :
    LinearMap.range (blockDiagMap (p := p) (q := q))
      ≤ LinearMap.ker (offDiagMap (p := p) (q := q)) := by
  rintro _ ⟨⟨A, D, c⟩, rfl⟩
  refine LinearMap.mem_ker.mpr (Prod.ext ?_ ?_) <;>
    · ext i j
      simp [offDiagMap, blockDiagMap_val, blockDiagOf, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁]

theorem ker_le_range_blockDiagMap (hp : 0 < p) (hq : 0 < q) :
    LinearMap.ker (offDiagMap (p := p) (q := q))
      ≤ LinearMap.range (blockDiagMap (p := p) (q := q)) := by
  intro M hM
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hqne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set N : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hN
  set X : Matrix (Fin p) (Fin p) ℂ := N.toBlocks₁₁ with hX
  set Y : Matrix (Fin q) (Fin q) ℂ := N.toBlocks₂₂ with hY
  have h12 : N.toBlocks₁₂ = 0 := congrArg Prod.fst (LinearMap.mem_ker.mp hM)
  have h21 : N.toBlocks₂₁ = 0 := congrArg Prod.snd (LinearMap.mem_ker.mp hM)
  have hblocks : N = Matrix.fromBlocks X 0 0 Y := by
    rw [hX, hY, ← h12, ← h21, Matrix.fromBlocks_toBlocks]
  have htr : Matrix.trace X + Matrix.trace Y = 0 := by
    have h : Matrix.trace N = 0 := LinearMap.mem_ker.mp M.property
    rw [hblocks, trace_fromBlocks_diag] at h
    exact h
  set c : ℂ := Matrix.trace X / ((p : ℂ) * q) with hc
  have hpq : ((p : ℂ) * q) ≠ 0 := mul_ne_zero hpne hqne
  have hkey : (p : ℂ) * q * c = Matrix.trace X := by
    rw [hc]; field_simp
  have hAtr : Matrix.trace (X - (q : ℂ) • c • (1 : Matrix (Fin p) (Fin p) ℂ)) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    linear_combination -hkey
  have hDtr : Matrix.trace (Y + (p : ℂ) • c • (1 : Matrix (Fin q) (Fin q) ℂ)) = 0 := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin, smul_eq_mul]
    linear_combination hkey + htr
  refine ⟨(⟨X - (q : ℂ) • c • 1, LinearMap.mem_ker.mpr hAtr⟩,
          ⟨Y + (p : ℂ) • c • 1, LinearMap.mem_ker.mpr hDtr⟩, c), ?_⟩
  apply Subtype.ext
  rw [blockDiagMap_val, blockDiagOf, ← hN, hblocks]
  congr 1 <;> simp

/-- **THE RANGE IS EXACTLY THE KERNEL**, so `p² + q² − 1` is `sl(p) ⊕ sl(q) ⊕ ℂ` and not a
subtraction. -/
theorem range_blockDiagMap_eq_ker (hp : 0 < p) (hq : 0 < q) :
    LinearMap.range (blockDiagMap (p := p) (q := q))
      = LinearMap.ker (offDiagMap (p := p) (q := q)) :=
  le_antisymm range_blockDiagMap_le_ker (ker_le_range_blockDiagMap hp hq)

/-- **`p² + q² − 1 = (p² − 1) + (q² − 1) + 1`, AS THREE EXHIBITED SPACES.** -/
theorem finrank_ker_eq_sum (hp : 0 < p) (hq : 0 < q) :
    Module.finrank ℂ (LinearMap.ker (offDiagMap (p := p) (q := q)))
      = (p ^ 2 - 1) + (q ^ 2 - 1) + 1 := by
  haveI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  rw [← range_blockDiagMap_eq_ker hp hq,
    LinearMap.finrank_range_of_inj (blockDiagMap_injective hp hq),
    Module.finrank_prod, Module.finrank_prod, Module.finrank_self,
    TracelessDimension.finrank_tracelessSub, TracelessDimension.finrank_tracelessSub,
    Fintype.card_fin, Fintype.card_fin]
  omega

end BlockDiagonalSplit
