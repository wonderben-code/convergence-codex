import BlockGrading

/-!
# `blockDiagMap` is a morphism of Lie algebras, and the `ℂ` direction is the grading element

`BlockDiagonalSplit` decomposed `sl(p+q)` four ways — `sl(p) ⊕ sl(q) ⊕ ℂ ⊕ (off-diagonal)` — and
its header said, twice, that nothing made this a statement about brackets. `BlockGrading` closed
half of that: the coarse even/odd split is a ℤ/2-grading, and `GradedLieAlgebra` is instantiated.
**The half left open was the fine one**, and it is this file: the four-way splitting respects the
bracket, and the scalar direction is not merely a line but a distinguished one.

## What is proved

> **`lie_blockDiagOf`** — `⁅blockDiagOf A D c, blockDiagOf A' D' c'⁆ = blockDiagOf ⁅A,A'⁆ ⁅D,D'⁆ 0`.
> The scalar shifts cancel out of both corners, so **the bracket does not see `c` at all**, and the
> `ℂ` component of every bracket is `0`.
>
> **`blockDiagMap_lie`** — the same statement about the injection of `BlockDiagonalSplit`:
> `blockDiagMap` intertwines `prodBracket`, the componentwise bracket on
> `sl(p) × sl(q) × ℂ` **with the `ℂ` factor central**, with the bracket on matrices. This is the
> sentence `BlockDiagonalSplit` recorded as unproved, and it is now a theorem.
>
> **`lie_centreOf_blockDiagOf`** — the scalar direction is central **in the even part**.
>
> **`lie_centreOf_offDiagOf`** — and on the odd part its adjoint action is multiplication by
> `±(p+q)c`: `⁅centreOf c, offDiagOf B C⁆ = offDiagOf ((p+q)c • B) (−(p+q)c • C)`. **So the scalar
> direction is the grading element of `BlockGrading`'s ℤ/2-grading**, up to the nonzero factor
> `(p+q)c` — the even part is its kernel and the odd part is where it acts.
>
> **`centreOf_not_central`** — hence it is *not* central in `sl(p+q)` for `c ≠ 0` and both blocks
> nonempty. Without this, "the `ℂ` direction is central" would read as a claim about the whole
> algebra, which is false.
>
> **`evenSlLie`** — the even part of `sl(p+q)` as a `LieSubalgebra`, and
> **`map_range_blockDiagMap`**: the image of `sl(p) × sl(q) × ℂ` under `blockDiagMap` is exactly
> its carrier. So the decomposition `BlockDiagonalSplit` built is a decomposition **of a Lie
> subalgebra, by a bracket-preserving map**.

## What is NOT claimed

**No `LieAlgebra` structure is put on the product `sl(p) × sl(q) × ℂ`.** `prodBracket` is a
function, not a `LieRing` instance: making it one would need the Jacobi identity and the
alternating law verified for the product, which is routine and is **not done here**. Every
statement below is about matrices, where the bracket is Mathlib's, and `prodBracket` appears only
as the thing `blockDiagMap` is shown to intertwine.

**`blockDiagMap` is not exhibited here as a `LieHom`.** The intertwining equation is proved; the
bundled morphism is not built, because as of 2026-08-28 nothing in the estate puts a Lie structure
on its domain to bundle it over. **Counted, not assumed** (`ERRATUM 324`):
`grep -rn "LieRing\|LieHom" paper_f/` returns **7 lines that day, all of them prose in this
chain's three headers and none of them a declaration**. Mathlib's `LieHom` exists
(`Mathlib/Algebra/Lie/Basic.lean`) and is not the obstacle; the missing input is the `LieRing` on
`sl(p) × sl(q) × ℂ`.

**Nothing about `su(n)` and nothing over `ℝ`.** The grading element here is a complex multiple of a
block-scalar matrix and is **not** skew-adjoint unless `c` is imaginary; no real form is taken and
`SkewBlockOffDiagonal` is not imported. In the physics reading the corresponding generator is
`i`-times this one, and **that reading is not formalised anywhere in this chain**.

**No physics.** That `(p+q)c` is a hypercharge-like eigenvalue, or that the odd part is a
leptoquark sector, is the reading `PatiSalamOffDiagonal` fences. This file adds a bracket
computation and adds nothing to that reading.

**No roots, no Cartan subalgebra, no semisimplicity, no Killing form**, and no claim that the even
part is `gl(p) ⊕ gl(q)` or reductive.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockLieMorphism

open Matrix SlAbelianGeneral BlockOffDiagonal BlockDiagonalSplit BlockGrading

variable {p q : ℕ}

/-! ## 1. A scalar shift is invisible to the bracket -/

/-- `z • 1` is central, so shifting either argument by a multiple of the identity changes
nothing. -/
theorem lie_add_smul_one {n : Type*} [Fintype n] [DecidableEq n] (A A' : Matrix n n ℂ) (z z' : ℂ) :
    ⁅A + z • (1 : Matrix n n ℂ), A' + z' • (1 : Matrix n n ℂ)⁆ = ⁅A, A'⁆ := by
  simp only [Ring.lie_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_one, Matrix.one_mul, smul_add, smul_smul, mul_comm]
  abel

theorem lie_sub_smul_one {n : Type*} [Fintype n] [DecidableEq n] (A A' : Matrix n n ℂ) (z z' : ℂ) :
    ⁅A - z • (1 : Matrix n n ℂ), A' - z' • (1 : Matrix n n ℂ)⁆ = ⁅A, A'⁆ := by
  have h := lie_add_smul_one A A' (-z) (-z')
  simpa [sub_eq_add_neg, neg_smul] using h

/-! ## 2. Differences of blocks -/

theorem fromBlocks_diag_sub (X X' : Matrix (Fin p) (Fin p) ℂ) (Y Y' : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromBlocks X 0 0 Y - Matrix.fromBlocks X' 0 0 Y'
      = Matrix.fromBlocks (X - X') 0 0 (Y - Y') := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.sub_apply]

theorem fromBlocks_off_sub (B B' : Matrix (Fin p) (Fin q) ℂ) (C C' : Matrix (Fin q) (Fin p) ℂ) :
    Matrix.fromBlocks 0 B C 0 - Matrix.fromBlocks 0 B' C' 0
      = Matrix.fromBlocks 0 (B - B') (C - C') 0 := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.sub_apply]

/-! ## 3. The bracket of two block-diagonal elements loses the scalar -/

/-- **THE BRACKET DOES NOT SEE `c`.** Both shifts are multiples of the identity in their own
corner, so both cancel, and the scalar component of the result is `0`. -/
theorem lie_blockDiagOf (A A' : Matrix (Fin p) (Fin p) ℂ) (D D' : Matrix (Fin q) (Fin q) ℂ)
    (c c' : ℂ) :
    ⁅blockDiagOf A D c, blockDiagOf A' D' c'⁆ = blockDiagOf ⁅A, A'⁆ ⁅D, D'⁆ 0 := by
  have htop : ⁅A + (q : ℂ) • c • (1 : Matrix (Fin p) (Fin p) ℂ),
      A' + (q : ℂ) • c' • (1 : Matrix (Fin p) (Fin p) ℂ)⁆ = ⁅A, A'⁆ := by
    rw [smul_smul, smul_smul]
    exact lie_add_smul_one A A' _ _
  have hbot : ⁅D - (p : ℂ) • c • (1 : Matrix (Fin q) (Fin q) ℂ),
      D' - (p : ℂ) • c' • (1 : Matrix (Fin q) (Fin q) ℂ)⁆ = ⁅D, D'⁆ := by
    rw [smul_smul, smul_smul]
    exact lie_sub_smul_one D D' _ _
  simp only [Ring.lie_def] at htop hbot ⊢
  rw [blockDiagOf, blockDiagOf, diag_mul_diag, diag_mul_diag, fromBlocks_diag_sub, htop, hbot,
    blockDiagOf]
  simp

/-! ## 4. `blockDiagMap` intertwines the brackets -/

/-- The componentwise bracket on `sl(p) × sl(q) × ℂ`, **with the `ℂ` factor central**. This is a
function, not a `LieRing` instance: see the header. -/
noncomputable def prodBracket (x y : tracelessSub (Fin p) × tracelessSub (Fin q) × ℂ) :
    tracelessSub (Fin p) × tracelessSub (Fin q) × ℂ :=
  (⟨⁅(x.1 : Matrix (Fin p) (Fin p) ℂ), (y.1 : Matrix (Fin p) (Fin p) ℂ)⁆,
      lie_mem_tracelessSub _ x.1.property y.1.property⟩,
   ⟨⁅(x.2.1 : Matrix (Fin q) (Fin q) ℂ), (y.2.1 : Matrix (Fin q) (Fin q) ℂ)⁆,
      lie_mem_tracelessSub _ x.2.1.property y.2.1.property⟩,
   0)

/-- **THE SCALAR COMPONENT OF EVERY BRACKET IS ZERO** — the `ℂ` direction is central for this
bracket, which is what makes `sl(p) ⊕ sl(q) ⊕ ℂ` the right reading of the first summand. -/
theorem prodBracket_scalar (x y : tracelessSub (Fin p) × tracelessSub (Fin q) × ℂ) :
    (prodBracket x y).2.2 = 0 := rfl

/-- **`blockDiagMap` RESPECTS THE BRACKET.** This is the theorem `BlockDiagonalSplit`'s header
named as missing. -/
theorem blockDiagMap_lie (x y : tracelessSub (Fin p) × tracelessSub (Fin q) × ℂ) :
    ⁅((blockDiagMap x : tracelessSub (Fin p ⊕ Fin q)) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ),
      ((blockDiagMap y : tracelessSub (Fin p ⊕ Fin q)) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)⁆
      = ((blockDiagMap (prodBracket x y) : tracelessSub (Fin p ⊕ Fin q)) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) := by
  obtain ⟨A, D, c⟩ := x
  obtain ⟨A', D', c'⟩ := y
  rw [prodBracket, blockDiagMap_val, blockDiagMap_val, blockDiagMap_val, lie_blockDiagOf]

/-! ## 5. The scalar direction is the grading element -/

/-- The scalar direction of `BlockDiagonalSplit`'s decomposition, on its own. -/
noncomputable def centreOf (p q : ℕ) (c : ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  blockDiagOf (0 : Matrix (Fin p) (Fin p) ℂ) (0 : Matrix (Fin q) (Fin q) ℂ) c

theorem centreOf_eq (c : ℂ) :
    centreOf p q c
      = Matrix.fromBlocks ((q : ℂ) • c • 1) 0 0
          (-((p : ℂ) • c • (1 : Matrix (Fin q) (Fin q) ℂ))) := by
  rw [centreOf, blockDiagOf]
  simp

/-- **CENTRAL IN THE EVEN PART.** -/
theorem lie_centreOf_blockDiagOf (c : ℂ) (A : Matrix (Fin p) (Fin p) ℂ)
    (D : Matrix (Fin q) (Fin q) ℂ) (c' : ℂ) : ⁅centreOf p q c, blockDiagOf A D c'⁆ = 0 := by
  rw [centreOf, lie_blockDiagOf]
  simp [blockDiagOf, Ring.lie_def]

/-- **AND THE GRADING ELEMENT ON THE ODD PART.** Its adjoint action multiplies the upper block by
`(p+q)c` and the lower by `−(p+q)c`; `BlockGrading`'s two graded pieces are its `0`- and
`±(p+q)c`-eigenspaces. -/
theorem lie_centreOf_offDiagOf (c : ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) :
    ⁅centreOf p q c, offDiagOf B C⁆
      = offDiagOf ((((p : ℂ) + q) * c) • B) ((-(((p : ℂ) + q) * c)) • C) := by
  have hB : ((q : ℂ) • c • (1 : Matrix (Fin p) (Fin p) ℂ)) * B
      - B * (-((p : ℂ) • c • (1 : Matrix (Fin q) (Fin q) ℂ))) = (((p : ℂ) + q) * c) • B := by
    rw [Matrix.mul_neg, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one, sub_neg_eq_add, smul_smul, smul_smul, ← add_smul]
    congr 1
    ring
  have hC : (-((p : ℂ) • c • (1 : Matrix (Fin q) (Fin q) ℂ))) * C
      - C * ((q : ℂ) • c • (1 : Matrix (Fin p) (Fin p) ℂ)) = (-(((p : ℂ) + q) * c)) • C := by
    rw [Matrix.neg_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul, ← neg_smul, ← sub_smul]
    congr 1
    ring
  rw [centreOf_eq, offDiagOf, Ring.lie_def, diag_mul_off, off_mul_diag, fromBlocks_off_sub,
    offDiagOf, hB, hC]

/-- **SO IT IS NOT CENTRAL IN `sl(p+q)`.** The previous theorem says the `ℂ` direction commutes
with the even part; this one says the qualifier is load-bearing. -/
theorem centreOf_not_central (hp : 0 < p) (hq : 0 < q) {c : ℂ} (hc : c ≠ 0) :
    ∃ X ∈ oddPart p q, ⁅centreOf p q c, X⁆ ≠ 0 := by
  have hpq : ((p : ℂ) + q) ≠ 0 := by
    have h : (p : ℂ) + q = ((p + q : ℕ) : ℂ) := by push_cast; ring
    rw [h]
    exact Nat.cast_ne_zero.mpr (by omega)
  refine ⟨offDiagOf (allOnes p q) 0, fromBlocks_off_mem _ _, ?_⟩
  intro hzero
  rw [lie_centreOf_offDiagOf] at hzero
  have hval := congrFun (congrFun hzero (Sum.inl ⟨0, hp⟩)) (Sum.inr ⟨0, hq⟩)
  simp only [offDiagOf, Matrix.fromBlocks_apply₁₂, Matrix.smul_apply, allOnes, Matrix.of_apply,
    smul_eq_mul, mul_one, Matrix.zero_apply] at hval
  exact (mul_ne_zero hpq hc) hval

/-! ## 6. The even part of `sl(p+q)` as a Lie subalgebra -/

/-- **THE FIRST SUMMAND, AS A `LieSubalgebra`.** `BlockDiagonalSplit` decomposed this space; it is
a Lie subalgebra of `gl(p+q)`, being the intersection of two things closed under the bracket. -/
noncomputable def evenSlLie (p q : ℕ) :
    LieSubalgebra ℂ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  toSubmodule := evenPart p q ⊓ tracelessSub (Fin p ⊕ Fin q)
  lie_mem' hx hy :=
    ⟨lie_evenPart_evenPart hx.1 hy.1, lie_mem_tracelessSub _ hx.2 hy.2⟩

/-- **AND `blockDiagMap`'S IMAGE IS EXACTLY ITS CARRIER.** With `blockDiagMap_lie`, the four-way
decomposition is a decomposition of a Lie subalgebra by a bracket-preserving injection. -/
theorem map_range_blockDiagMap (hp : 0 < p) (hq : 0 < q) :
    Submodule.map (tracelessSub (Fin p ⊕ Fin q)).subtype
        (LinearMap.range (blockDiagMap (p := p) (q := q)))
      = (evenSlLie p q).toSubmodule := by
  rw [range_blockDiagMap_eq_ker hp hq]
  exact map_ker_offDiagMap

end BlockLieMorphism
