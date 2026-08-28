import TracelessDimension

/-!
# The `15 = 9 + 6` of `PatiSalamOffDiagonal` is `(p+q)² − 1 = (p² + q² − 1) + 2pq`

`PatiSalamOffDiagonal` splits `sl(4,ℂ)` as `9 + 6` by reading a traceless `4 × 4` matrix's last
column and last row on the first three indices, and `SlAbelianGeneral` and `TracelessDimension`
have since built the two things needed to say that at any block size: the traceless matrices at an
arbitrary finite index type, and their dimension.

**`PROOF_STRATEGY` §7 rule 3, third consecutive unit.** The restriction removed here is the block
size: `4 = 3 + 1` becomes `p + q`.

## What is proved

Over `Fin p ⊕ Fin q`, so the blocks are `Matrix.toBlocks₁₂` and `toBlocks₂₁` rather than index
arithmetic:

> **`offDiagMap`** — a traceless matrix to its two off-diagonal blocks, `(p × q, q × p)`.
> **Surjective** (`offDiagMap_surjective`), because `fromBlocks 0 B C 0` has zero diagonal blocks
> and so is traceless for free — the same accounting that made the `4 × 4` case work, and the
> reason the count comes out as it does.
>
> **`finrank_range_offDiagMap = 2 * p * q`** and, by rank–nullity against
> `TracelessDimension.finrank_tracelessSub`, **`finrank_ker_offDiagMap = p² + q² − 1`**.
>
> **`block_splits`** — `(p + q)² − 1 = (p² + q² − 1) + 2pq`, **derived from a map whose kernel and
> range are both described** rather than asserted about numerals.

At `p = 3`, `q = 1` the two summands are `9` and `6`, which is the Pati–Salam split; at `p = q = 2`
they are `7` and `8` in `sl(4,ℂ)`, so the same space splits differently at a different block
structure — the decomposition is a property of the **partition**, not of the dimension.

## What is NOT claimed

**No transport to `PatiSalamOffDiagonal` is claimed.** That file works over `Fin 4`; this one over
`Fin 3 ⊕ Fin 1` at the instance. The two index types are isomorphic and the dimensions agree, and
**this file does not build the isomorphism, does not restate that file's theorems, and does not
assert they are the same object.** `ERRATUM 316` is the record of what asserting that on the
strength of a matching numeral costs.

**Nothing about `su(n)`.** `TracelessSkewDimension` is not imported. `PatiSalamOffDiagonal` §4 is
the real, skew-Hermitian version at `n = 4`, and generalising *that* would be a different unit with
a different argument — the real off-diagonal part is one block whose conjugate is the other, so the
count is `2pq` real dimensions from `pq` complex entries, not the same computation.

**⚠ THAT UNIT IS DONE, 2026-08-28 — `SkewBlockOffDiagonal`, and the prediction above held exactly.**
`skew_block_splits` is `(p + q)² − 1 = (p² + q² − 1) + 2pq` over `ℝ`, and it needed the different
argument this paragraph named: `skewOffDiagMap` reads **one** block, `skewOffDiagOf B = fromBlocks 0
B (−Bᴴ) 0` is the section, and the `2pq` real dimensions come from `pq` complex entries rather than
from two independent blocks. It also needed the skew-Hermitian dimension at an arbitrary index type,
which did not exist and is proved there. **The two splits are the same arithmetic and are not the
same theorem**, no comparison map between them is built, and neither file claims one.

**No physics.** The kernel here is the block-diagonal traceless matrices as a subspace; whether its
summands "are" colour and hypercharge is the reading `PatiSalamOffDiagonal` fences, and this file
adds nothing to it.

**No Lie theory.** `tracelessSub` is a submodule of matrices; no bracket, no `LieSubalgebra`.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockOffDiagonal

open Matrix SlAbelianGeneral

variable {p q : ℕ}

/-! ## 1. The two off-diagonal blocks, as a linear map -/

/-- A traceless matrix to its two off-diagonal blocks. The diagonal blocks are deliberately not
read: their traces are determined by each other. -/
noncomputable def offDiagMap :
    tracelessSub (Fin p ⊕ Fin q) →ₗ[ℂ]
      (Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin p) ℂ) where
  toFun M := ((M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂,
              (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The matrix carrying `B` and `C` off the diagonal and nothing else. -/
def offDiagOf (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 0 B C 0

/-- **ITS TRACE IS ZERO**, because both diagonal blocks are — which is why the map below is
surjective: the off-diagonal directions cost nothing against the trace condition. -/
theorem offDiagOf_trace (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    Matrix.trace (offDiagOf B C) = 0 := by
  simp [offDiagOf, Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem offDiagOf_mem (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    offDiagOf B C ∈ tracelessSub (Fin p ⊕ Fin q) :=
  LinearMap.mem_ker.mpr (offDiagOf_trace B C)

theorem offDiagMap_surjective : Function.Surjective (offDiagMap (p := p) (q := q)) := by
  rintro ⟨B, C⟩
  exact ⟨⟨offDiagOf B C, offDiagOf_mem B C⟩, rfl⟩

/-! ## 2. The two dimensions -/

theorem finrank_range_offDiagMap :
    Module.finrank ℂ (LinearMap.range (offDiagMap (p := p) (q := q))) = 2 * p * q := by
  rw [LinearMap.range_eq_top.mpr offDiagMap_surjective, finrank_top, Module.finrank_prod,
    Module.finrank_matrix, Module.finrank_matrix]
  simp
  ring

theorem finrank_ker_offDiagMap (hp : 0 < p) :
    Module.finrank ℂ (LinearMap.ker (offDiagMap (p := p) (q := q))) = p ^ 2 + q ^ 2 - 1 := by
  have hne : Nonempty (Fin p ⊕ Fin q) := ⟨Sum.inl ⟨0, hp⟩⟩
  have h := LinearMap.finrank_range_add_finrank_ker (offDiagMap (p := p) (q := q))
  rw [finrank_range_offDiagMap, TracelessDimension.finrank_tracelessSub] at h
  have hcard : Fintype.card (Fin p ⊕ Fin q) = p + q := by simp
  rw [hcard] at h
  have hsq : (p + q) ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q := by ring
  rw [hsq] at h
  have h1 : 1 ≤ p ^ 2 + q ^ 2 := by nlinarith
  omega

/-! ## 3. The split -/

/-- **`(p + q)² − 1 = (p² + q² − 1) + 2pq`, WITH BOTH SUMMANDS EXHIBITED.** The kernel is the
block-diagonal traceless part and the range is the pair of off-diagonal blocks; the identity is
derived from a map, not asserted about numerals.

At `p = 3`, `q = 1` this is `15 = 9 + 6`, the Pati–Salam split. At `p = q = 2` it is `15 = 7 + 8`:
**the same space splits differently at a different block structure**, so the decomposition is a
property of the partition and not of the dimension. -/
theorem block_splits (hp : 0 < p) :
    Module.finrank ℂ (tracelessSub (Fin p ⊕ Fin q))
      = Module.finrank ℂ (LinearMap.ker (offDiagMap (p := p) (q := q)))
        + Module.finrank ℂ (LinearMap.range (offDiagMap (p := p) (q := q))) := by
  have hne : Nonempty (Fin p ⊕ Fin q) := ⟨Sum.inl ⟨0, hp⟩⟩
  have h := LinearMap.finrank_range_add_finrank_ker (offDiagMap (p := p) (q := q))
  omega

/-- The Pati–Salam instance, as arithmetic in this file's own objects. **No claim is made that this
is `PatiSalamOffDiagonal.su4_splits_nine_six`**: that theorem is over `Fin 4`, this is over
`Fin 3 ⊕ Fin 1`, and no isomorphism between them is built here (`ERRATUM 316`). -/
theorem block_splits_three_one :
    Module.finrank ℂ (LinearMap.ker (offDiagMap (p := 3) (q := 1))) = 9
      ∧ Module.finrank ℂ (LinearMap.range (offDiagMap (p := 3) (q := 1))) = 6 :=
  ⟨by rw [finrank_ker_offDiagMap (by norm_num)]; norm_num,
   by rw [finrank_range_offDiagMap]⟩

/-- And the same total splits `7 + 8` at `p = q = 2`. -/
theorem block_splits_two_two :
    Module.finrank ℂ (LinearMap.ker (offDiagMap (p := 2) (q := 2))) = 7
      ∧ Module.finrank ℂ (LinearMap.range (offDiagMap (p := 2) (q := 2))) = 8 :=
  ⟨by rw [finrank_ker_offDiagMap (by norm_num)]; norm_num,
   by rw [finrank_range_offDiagMap]⟩

end BlockOffDiagonal
