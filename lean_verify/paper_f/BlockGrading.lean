import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.Graded
import BlockDiagonalSplit

/-!
# The block decomposition respects the bracket: a ℤ/2-grading of `sl(p+q)`

`BlockDiagonalSplit` ended with an explicit admission: *"Nothing here says the decomposition
respects a bracket, and no `LieSubalgebra` is built."* This file removes that sentence's force in
the two ways available — by finding the bracket that was already there, and by proving the
decomposition respects it.

## The identification that was already true

**`(LieAlgebra.SpecialLinear.sl ι ℂ).toSubmodule = SlAbelianGeneral.tracelessSub ι`, by `rfl`.**
Mathlib defines `sl n R` as a `LieSubalgebra` whose underlying submodule is
`LinearMap.ker (Matrix.traceLinearMap n R R)`, and that is, character for character, the definition
`SlAbelianGeneral.tracelessSub` was given. The two are the same object; nothing is transported and
nothing is constructed.

This is worth a line of its own because of what it does to the chain behind it. Every dimension
result proved about `tracelessSub` — `TracelessDimension.finrank_tracelessSub`,
`BlockOffDiagonal.block_splits`, `BlockDiagonalSplit.finrank_ker_eq_sum` — is, without reproof, a
statement about **Mathlib's special linear Lie algebra**. `finrank_sl` below is
`finrank_tracelessSub` with no proof at all: the term is copied across.

**`ERRATUM 313` is why this file exists in this shape.** The plan for this unit was to build `sl`
as a `LieSubalgebra` by hand. A probe run before writing any of it found the Mathlib definition,
and the `rfl` above is the whole of what that construction would have been worth.

**AND THE SAME MISTAKE THEN HAPPENED INSIDE THIS FILE.** The paragraph on the bracket rules first
read *"stated as four theorems rather than as an instance because Mathlib has no
`LieAlgebra.IsGraded` to instantiate"*. **That name does not exist and neither does the absence.**
`GradedLieAlgebra` is in `Mathlib/Algebra/Lie/Graded.lean`, and the sentence had been written from
a failed `#check` of a **guessed** name inside a narrow import — the identical error the paragraph
above congratulates itself for avoiding, one screen later. It was caught by
`check_ledger.py --cites-lean`, which reads every qualified name in every Lean comment in the
estate and reported this one UNREAD. `ERRATUM 324` is the record; §7 is the repair — an instance
rather than a correction of wording.

## What is proved

Over `Fin p ⊕ Fin q`, in the **matrix algebra** `Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ` — that
is, in `gl(p+q)` — with Mathlib's bracket `⁅X, Y⁆ = X * Y - Y * X` (`Ring.lie_def`), not a private
commutator defined here:

> **`evenPart`** (block-diagonal) and **`oddPart`** (block-off-diagonal) are complementary:
> `isCompl_evenPart_oddPart`.
>
> **The four bracket rules.** `⁅even, even⁆ ⊆ even`, `⁅even, odd⁆ ⊆ odd`, `⁅odd, even⁆ ⊆ odd`,
> `⁅odd, odd⁆ ⊆ even`.
>
> **`GradedLieAlgebra (gradePart p q)`** — Mathlib's own class, instantiated at `ZMod 2`, so the
> phrase "ℤ/2-grading" below is **the library's predicate and not this file's prose**. Its two
> halves are `SetLike.GradedBracket` (the four rules, repackaged as `i + j = k`) and
> `DirectSum.Decomposition` (`isCompl_evenPart_oddPart` through
> `DirectSum.isInternal_submodule_iff_isCompl`).
>
> **`evenLie`** — the even part packaged as an honest `LieSubalgebra ℂ`, which the four rules now
> license.
>
> **The odd part is not a subalgebra** (`oddPart_not_lie_closed`, for `0 < p` and `0 < q`): two
> explicit off-diagonal matrices whose bracket has a nonzero diagonal block. Without this the word
> "grading" could be read as "two subalgebras", which is false.
>
> **The restriction to `sl`.** `oddPart ≤ tracelessSub` with no hypothesis at all — the
> off-diagonal directions are traceless for free — and
> `(evenPart ⊓ tracelessSub) ⊔ oddPart = tracelessSub` with
> `(evenPart ⊓ tracelessSub) ⊓ oddPart = ⊥`: **`sl(p+q)` is the internal direct sum of its two
> graded pieces**, not merely a space whose dimension is a sum of two numbers.
>
> **`map_ker_offDiagMap`** ties that back to the previous two files: the kernel `BlockOffDiagonal`
> counted and `BlockDiagonalSplit` exhibited is exactly `evenPart ⊓ tracelessSub`, so
> `block_splits` and `finrank_ker_eq_sum` are statements about the graded pieces.

## What is NOT claimed

**No Lie algebra isomorphism.** `BlockDiagonalSplit.blockDiagMap` is a **linear** isomorphism onto
the kernel; this file does not claim it is a morphism of Lie algebras, and `evenLie` is not
identified with `sl(p) ⊕ sl(q) ⊕ ℂ` as a Lie algebra. `diag_mul_diag` is the fact that would drive
such a proof and it is proved here, but the morphism is not built and the statement is not made.

**⚠ THE PREDICTION HELD AND THE STATEMENT IS NOW MADE ELSEWHERE, 2026-08-28.** `BlockLieMorphism`
proves `blockDiagMap_lie` from `lie_blockDiagOf`, which is `diag_mul_diag` plus the fact that a
scalar shift is invisible to the bracket — the route this paragraph named. **This file still makes
no such claim**, and neither file bundles a `LieHom` or puts a `LieRing` on the product.

**No Lie module structure on the odd part.** `lie_evenPart_oddPart` says the bracket lands back in
`oddPart`; it does not build a `LieRingModule` or a `LieModule` instance, and no theorem here says
the odd part is a representation of the even part.

**⚠ SUPERSEDED THE SAME DAY, `BlockOddModule`.** `oddMod` is the odd part as a
`LieSubmodule ℂ ↥(evenLie p q) (Matrix …)`, and the `LieRingModule`/`LieModule` instances come
from `LieSubalgebra.lieRingModule` and `LieSubalgebra.lieModule` with **nothing verified there
either** — the only input is `lie_evenPart_oddPart` above. That file also computes the action:
`⁅fromBlocks A 0 0 D, fromBlocks 0 B C 0⁆ = fromBlocks 0 (A·B − B·D) (D·C − C·A) 0`, and proves
the two pieces complementary **in the lattice of `evenLie`-submodules**, which is what makes the
grading a decomposition of representations. **Irreducibility is not proved there and is not
begun.** This file's own statements are unchanged.

**No root space decomposition, no Cartan subalgebra, no semisimplicity, no Killing form.** The
grading is a two-step filtration by block position and nothing more. `SlFourAbelian` and
`SlAbelianGeneral` remain the estate's only statements about abelian subspaces of `sl`, and they
are about **subspaces**, not subalgebras.

**Nothing over `ℝ` and nothing skew-Hermitian.** `SkewBlockOffDiagonal` is not imported. The
bracket rules below would restrict to the skew-adjoint real form — `⁅X, Y⁆` of two skew-adjoint
matrices is skew-adjoint — but **that is not proved here and `su(n)` is not mentioned in any
statement**.

**No physics.** Whether the even part "is" colour-plus-hypercharge and the odd part "is" the
leptoquark sector is the reading `PatiSalamOffDiagonal` fences; this file adds a bracket to the
mathematics and adds nothing to that reading.

**No transport to `Fin 4`.** As in `BlockOffDiagonal`, everything is over `Fin p ⊕ Fin q` and no
isomorphism to `Fin (p + q)` is built (`ERRATUM 316`).

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockGrading

open Matrix SlAbelianGeneral BlockOffDiagonal

variable {p q : ℕ}

/-! ## 1. `tracelessSub` is Mathlib's `sl`, by `rfl` -/

/-- **THE CHAIN'S TRACELESS SUBSPACE IS MATHLIB'S SPECIAL LINEAR LIE ALGEBRA.** Both are
`LinearMap.ker (Matrix.traceLinearMap ι ℂ ℂ)`; this is not a transport. -/
theorem sl_toSubmodule (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (LieAlgebra.SpecialLinear.sl ι ℂ).toSubmodule = tracelessSub ι := rfl

theorem mem_sl_iff (ι : Type*) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    M ∈ LieAlgebra.SpecialLinear.sl ι ℂ ↔ M ∈ tracelessSub ι := Iff.rfl

/-- **`dim sl(n) = n² − 1` FOR MATHLIB'S `sl`, with no proof of its own**: the term is
`TracelessDimension.finrank_tracelessSub`, accepted at this type because the two carriers are the
same. -/
theorem finrank_sl (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Module.finrank ℂ (LieAlgebra.SpecialLinear.sl ι ℂ) = Fintype.card ι ^ 2 - 1 :=
  TracelessDimension.finrank_tracelessSub ι

theorem finrank_sl_fin (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (LieAlgebra.SpecialLinear.sl (Fin n) ℂ) = n ^ 2 - 1 :=
  TracelessDimension.finrank_tracelessMatrix n hn

/-- The trace condition is closed under the bracket — **cited from Mathlib, not reproved**. This
is the fact `BlockDiagonalSplit` said it did not have. -/
theorem lie_mem_tracelessSub (ι : Type*) [Fintype ι] [DecidableEq ι] {X Y : Matrix ι ι ℂ}
    (hX : X ∈ tracelessSub ι) (hY : Y ∈ tracelessSub ι) : ⁅X, Y⁆ ∈ tracelessSub ι :=
  (LieAlgebra.SpecialLinear.sl ι ℂ).lie_mem hX hY

/-! ## 2. The two graded pieces of `gl(p+q)` -/

/-- The two off-diagonal blocks of an arbitrary matrix — the unrestricted version of
`BlockOffDiagonal.offDiagMap`, which is defined only on the traceless subspace. -/
noncomputable def offBlocks : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℂ]
    (Matrix (Fin p) (Fin q) ℂ × Matrix (Fin q) (Fin p) ℂ) where
  toFun M := (M.toBlocks₁₂, M.toBlocks₂₁)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The two diagonal blocks of an arbitrary matrix. -/
noncomputable def diagBlocks : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ →ₗ[ℂ]
    (Matrix (Fin p) (Fin p) ℂ × Matrix (Fin q) (Fin q) ℂ) where
  toFun M := (M.toBlocks₁₁, M.toBlocks₂₂)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree `0`: the block-diagonal matrices. -/
noncomputable def evenPart (p q : ℕ) : Submodule ℂ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  LinearMap.ker (offBlocks (p := p) (q := q))

/-- Degree `1`: the block-off-diagonal matrices. -/
noncomputable def oddPart (p q : ℕ) : Submodule ℂ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  LinearMap.ker (diagBlocks (p := p) (q := q))

theorem mem_evenPart_iff (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    M ∈ evenPart p q ↔ M.toBlocks₁₂ = 0 ∧ M.toBlocks₂₁ = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst (LinearMap.mem_ker.mp h), congrArg Prod.snd (LinearMap.mem_ker.mp h)⟩
  · rintro ⟨h1, h2⟩
    exact LinearMap.mem_ker.mpr (Prod.ext h1 h2)

theorem mem_oddPart_iff (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    M ∈ oddPart p q ↔ M.toBlocks₁₁ = 0 ∧ M.toBlocks₂₂ = 0 := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst (LinearMap.mem_ker.mp h), congrArg Prod.snd (LinearMap.mem_ker.mp h)⟩
  · rintro ⟨h1, h2⟩
    exact LinearMap.mem_ker.mpr (Prod.ext h1 h2)

theorem fromBlocks_diag_mem (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromBlocks A 0 0 D ∈ evenPart p q := by
  refine (mem_evenPart_iff _).mpr ⟨?_, ?_⟩ <;>
    · ext i j
      simp [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁]

theorem fromBlocks_off_mem (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    Matrix.fromBlocks 0 B C 0 ∈ oddPart p q := by
  refine (mem_oddPart_iff _).mpr ⟨?_, ?_⟩ <;>
    · ext i j
      simp [Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

theorem exists_of_mem_evenPart {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (h : M ∈ evenPart p q) :
    ∃ (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ),
      M = Matrix.fromBlocks A 0 0 D := by
  obtain ⟨h12, h21⟩ := (mem_evenPart_iff M).mp h
  exact ⟨M.toBlocks₁₁, M.toBlocks₂₂, by rw [← h12, ← h21, Matrix.fromBlocks_toBlocks]⟩

theorem exists_of_mem_oddPart {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (h : M ∈ oddPart p q) :
    ∃ (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ),
      M = Matrix.fromBlocks 0 B C 0 := by
  obtain ⟨h11, h22⟩ := (mem_oddPart_iff M).mp h
  exact ⟨M.toBlocks₁₂, M.toBlocks₂₁, by rw [← h11, ← h22, Matrix.fromBlocks_toBlocks]⟩

/-- Every matrix is its block-diagonal part plus its block-off-diagonal part. -/
theorem eq_diag_add_off (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    M = Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂
      + Matrix.fromBlocks 0 M.toBlocks₁₂ M.toBlocks₂₁ 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

/-- **THE TWO PIECES ARE COMPLEMENTARY IN `gl(p+q)`.** -/
theorem isCompl_evenPart_oddPart : IsCompl (evenPart p q) (oddPart p q) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro M hM hM'
    obtain ⟨A, D, rfl⟩ := exists_of_mem_evenPart hM
    obtain ⟨h11, h22⟩ := (mem_oddPart_iff _).mp hM'
    have hA : A = 0 := by
      ext i j
      have := congrFun (congrFun h11 i) j
      simpa [Matrix.toBlocks₁₁] using this
    have hD : D = 0 := by
      ext i j
      have := congrFun (congrFun h22 i) j
      simpa [Matrix.toBlocks₂₂] using this
    rw [hA, hD, Matrix.fromBlocks_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro M _
    rw [eq_diag_add_off M]
    exact Submodule.add_mem_sup (fromBlocks_diag_mem _ _) (fromBlocks_off_mem _ _)

/-! ## 3. The four block-multiplication laws -/

theorem diag_mul_diag (A A' : Matrix (Fin p) (Fin p) ℂ) (D D' : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks A' 0 0 D'
      = Matrix.fromBlocks (A * A') 0 0 (D * D') := by
  rw [Matrix.fromBlocks_multiply]
  simp

theorem diag_mul_off (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    Matrix.fromBlocks A 0 0 D * Matrix.fromBlocks 0 B C 0
      = Matrix.fromBlocks 0 (A * B) (D * C) 0 := by
  rw [Matrix.fromBlocks_multiply]
  simp

theorem off_mul_diag (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromBlocks 0 B C 0 * Matrix.fromBlocks A 0 0 D
      = Matrix.fromBlocks 0 (B * D) (C * A) 0 := by
  rw [Matrix.fromBlocks_multiply]
  simp

theorem off_mul_off (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ)
    (B' : Matrix (Fin p) (Fin q) ℂ) (C' : Matrix (Fin q) (Fin p) ℂ) :
    Matrix.fromBlocks 0 B C 0 * Matrix.fromBlocks 0 B' C' 0
      = Matrix.fromBlocks (B * C') 0 0 (C * B') := by
  rw [Matrix.fromBlocks_multiply]
  simp

/-! ## 4. The ℤ/2-grading -/

/-- `⁅even, even⁆ ⊆ even`. -/
theorem lie_evenPart_evenPart {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ evenPart p q) (hY : Y ∈ evenPart p q) : ⁅X, Y⁆ ∈ evenPart p q := by
  obtain ⟨A, D, rfl⟩ := exists_of_mem_evenPart hX
  obtain ⟨A', D', rfl⟩ := exists_of_mem_evenPart hY
  rw [Ring.lie_def, diag_mul_diag, diag_mul_diag]
  exact sub_mem (fromBlocks_diag_mem _ _) (fromBlocks_diag_mem _ _)

/-- `⁅even, odd⁆ ⊆ odd`. -/
theorem lie_evenPart_oddPart {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ evenPart p q) (hY : Y ∈ oddPart p q) : ⁅X, Y⁆ ∈ oddPart p q := by
  obtain ⟨A, D, rfl⟩ := exists_of_mem_evenPart hX
  obtain ⟨B, C, rfl⟩ := exists_of_mem_oddPart hY
  rw [Ring.lie_def, diag_mul_off, off_mul_diag]
  exact sub_mem (fromBlocks_off_mem _ _) (fromBlocks_off_mem _ _)

/-- `⁅odd, even⁆ ⊆ odd`. -/
theorem lie_oddPart_evenPart {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ oddPart p q) (hY : Y ∈ evenPart p q) : ⁅X, Y⁆ ∈ oddPart p q := by
  obtain ⟨B, C, rfl⟩ := exists_of_mem_oddPart hX
  obtain ⟨A, D, rfl⟩ := exists_of_mem_evenPart hY
  rw [Ring.lie_def, off_mul_diag, diag_mul_off]
  exact sub_mem (fromBlocks_off_mem _ _) (fromBlocks_off_mem _ _)

/-- `⁅odd, odd⁆ ⊆ even` — **the rule that makes this a grading rather than a filtration**. -/
theorem lie_oddPart_oddPart {X Y : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hX : X ∈ oddPart p q) (hY : Y ∈ oddPart p q) : ⁅X, Y⁆ ∈ evenPart p q := by
  obtain ⟨B, C, rfl⟩ := exists_of_mem_oddPart hX
  obtain ⟨B', C', rfl⟩ := exists_of_mem_oddPart hY
  rw [Ring.lie_def, off_mul_off, off_mul_off]
  exact sub_mem (fromBlocks_diag_mem _ _) (fromBlocks_diag_mem _ _)

/-- **THE EVEN PART IS A LIE SUBALGEBRA**, which is what `BlockDiagonalSplit` recorded as absent.
No claim is made that it is isomorphic to `gl(p) ⊕ gl(q)` as a Lie algebra. -/
noncomputable def evenLie (p q : ℕ) :
    LieSubalgebra ℂ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) where
  toSubmodule := evenPart p q
  lie_mem' hx hy := lie_evenPart_evenPart hx hy

theorem evenLie_toSubmodule : (evenLie p q).toSubmodule = evenPart p q := rfl

/-! ## 5. The odd part is not a subalgebra -/

/-- The all-ones rectangular matrix, used only as a witness below. -/
def allOnes (m n : ℕ) : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun _ _ => 1

theorem allOnes_mul_allOnes_apply (i j : Fin p) :
    (allOnes p q * allOnes q p) i j = (q : ℂ) := by
  simp [allOnes, Matrix.mul_apply]

/-- All-ones in the lower off-diagonal block. -/
def oddWitnessLower (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 0 0 (allOnes q p) 0

/-- All-ones in the upper off-diagonal block. -/
def oddWitnessUpper (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 0 (allOnes p q) 0 0

theorem oddWitnessLower_mem : oddWitnessLower p q ∈ oddPart p q :=
  fromBlocks_off_mem 0 (allOnes q p)

theorem oddWitnessUpper_mem : oddWitnessUpper p q ∈ oddPart p q :=
  fromBlocks_off_mem (allOnes p q) 0

theorem lie_oddWitness :
    ⁅oddWitnessLower p q, oddWitnessUpper p q⁆
      = Matrix.fromBlocks (-(allOnes p q * allOnes q p)) 0 0 (allOnes q p * allOnes p q) := by
  rw [Ring.lie_def, oddWitnessLower, oddWitnessUpper, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;> simp [Matrix.sub_apply]

/-- **THE ODD PART IS NOT CLOSED UNDER THE BRACKET.** Two off-diagonal matrices whose bracket has
diagonal entry `−q ≠ 0`, so "grading" here does not mean "two subalgebras". -/
theorem oddPart_not_lie_closed (hp : 0 < p) (hq : 0 < q) :
    ⁅oddWitnessLower p q, oddWitnessUpper p q⁆ ∉ oddPart p q := by
  intro hmem
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨h11, -⟩ := (mem_oddPart_iff _).mp hmem
  have key := congrFun (congrFun h11 ⟨0, hp⟩) ⟨0, hp⟩
  rw [lie_oddWitness] at key
  simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, Matrix.neg_apply,
    allOnes_mul_allOnes_apply, Matrix.zero_apply] at key
  exact hq' (neg_eq_zero.mp key)

/-! ## 6. Restricting the grading to `sl(p+q)` -/

theorem trace_eq_trace_blocks (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    Matrix.trace M = Matrix.trace M.toBlocks₁₁ + Matrix.trace M.toBlocks₂₂ := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂]

/-- **THE ODD PART IS ALREADY TRACELESS**, with no hypothesis — the same accounting that made
`BlockOffDiagonal.offDiagMap` surjective, now as an inequality of submodules. -/
theorem oddPart_le_tracelessSub : oddPart p q ≤ tracelessSub (Fin p ⊕ Fin q) := by
  intro M hM
  obtain ⟨B, C, rfl⟩ := exists_of_mem_oddPart hM
  exact BlockOffDiagonal.offDiagOf_mem B C

/-- The even part of a traceless matrix is traceless. -/
theorem diag_part_mem_tracelessSub {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ}
    (hM : M ∈ tracelessSub (Fin p ⊕ Fin q)) :
    Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ ∈ tracelessSub (Fin p ⊕ Fin q) := by
  have h : Matrix.trace (Matrix.fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂) = 0 := by
    rw [BlockDiagonalSplit.trace_fromBlocks_diag, ← trace_eq_trace_blocks]
    exact LinearMap.mem_ker.mp hM
  exact LinearMap.mem_ker.mpr h

/-- **`sl(p+q)` IS THE SUM OF ITS TWO GRADED PIECES.** -/
theorem sup_eq_tracelessSub :
    (evenPart p q ⊓ tracelessSub (Fin p ⊕ Fin q)) ⊔ oddPart p q
      = tracelessSub (Fin p ⊕ Fin q) := by
  refine le_antisymm (sup_le inf_le_right oddPart_le_tracelessSub) ?_
  intro M hM
  rw [eq_diag_add_off M]
  exact Submodule.add_mem_sup ⟨fromBlocks_diag_mem _ _, diag_part_mem_tracelessSub hM⟩
    (fromBlocks_off_mem _ _)

/-- **AND THE SUM IS DIRECT.** -/
theorem inf_eq_bot : (evenPart p q ⊓ tracelessSub (Fin p ⊕ Fin q)) ⊓ oddPart p q = ⊥ := by
  rw [← le_bot_iff, ← disjoint_iff.mp (isCompl_evenPart_oddPart (p := p) (q := q)).disjoint]
  exact inf_le_inf_right _ inf_le_left

/-- **THE KERNEL THE PREVIOUS TWO FILES COUNTED AND EXHIBITED IS THE EVEN PART OF `sl`**, so
`BlockOffDiagonal.block_splits` and `BlockDiagonalSplit.finrank_ker_eq_sum` are statements about
the graded pieces and not only about a kernel. -/
theorem map_ker_offDiagMap :
    Submodule.map (tracelessSub (Fin p ⊕ Fin q)).subtype
        (LinearMap.ker (BlockOffDiagonal.offDiagMap (p := p) (q := q)))
      = evenPart p q ⊓ tracelessSub (Fin p ⊕ Fin q) := by
  ext M
  constructor
  · rintro ⟨N, hN, rfl⟩
    refine ⟨(mem_evenPart_iff _).mpr ⟨?_, ?_⟩, N.property⟩
    · exact congrArg Prod.fst (LinearMap.mem_ker.mp hN)
    · exact congrArg Prod.snd (LinearMap.mem_ker.mp hN)
  · rintro ⟨hev, htr⟩
    obtain ⟨h12, h21⟩ := (mem_evenPart_iff M).mp hev
    exact ⟨⟨M, htr⟩, LinearMap.mem_ker.mpr (Prod.ext h12 h21), rfl⟩

/-- The grading, as one statement: complementary in `gl`, direct-summing to `sl`, and closed under
the bracket in the four ways a ℤ/2-grading requires. -/
theorem sl_graded (hp : 0 < p) (hq : 0 < q) :
    IsCompl (evenPart p q) (oddPart p q)
      ∧ (evenPart p q ⊓ tracelessSub (Fin p ⊕ Fin q)) ⊔ oddPart p q
          = tracelessSub (Fin p ⊕ Fin q)
      ∧ (evenPart p q ⊓ tracelessSub (Fin p ⊕ Fin q)) ⊓ oddPart p q = ⊥
      ∧ ⁅oddWitnessLower p q, oddWitnessUpper p q⁆ ∉ oddPart p q :=
  ⟨isCompl_evenPart_oddPart, sup_eq_tracelessSub, inf_eq_bot, oddPart_not_lie_closed hp hq⟩

/-! ## 7. Mathlib's `GradedLieAlgebra`, instantiated -/

/-- The two pieces as a family indexed by `ZMod 2`, which is what Mathlib's grading classes take. -/
noncomputable def gradePart (p q : ℕ) (i : ZMod 2) :
    Submodule ℂ (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :=
  if i = 0 then evenPart p q else oddPart p q

@[simp] theorem gradePart_zero : gradePart p q 0 = evenPart p q := by
  simp [gradePart]

@[simp] theorem gradePart_one : gradePart p q 1 = oddPart p q := by
  simp [gradePart]

theorem zmod_two_eq (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem univ_zmod_two : (Set.univ : Set (ZMod 2)) = {0, 1} := by
  ext x
  simp only [Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff]
  exact zmod_two_eq x

/-- **THE DECOMPOSITION HALF**: `IsCompl` is exactly `DirectSum.IsInternal` at two indices. -/
theorem isInternal_gradePart : DirectSum.IsInternal (gradePart p q) := by
  rw [DirectSum.isInternal_submodule_iff_isCompl (gradePart p q) (i := 0) (j := 1)
    (by decide) univ_zmod_two, gradePart_zero, gradePart_one]
  exact isCompl_evenPart_oddPart

/-- **THE BRACKET HALF**: the four rules of §4, repackaged as `i + j = k` in `ZMod 2`. -/
instance gradedBracket_gradePart : SetLike.GradedBracket (gradePart p q) where
  bracket_mem := by
    rintro i j k gi gj hsum hgi hgj
    rcases zmod_two_eq i with rfl | rfl <;> rcases zmod_two_eq j with rfl | rfl
    · have hk : k = 0 := by rw [← hsum]; decide
      subst hk
      rw [gradePart_zero] at hgi hgj ⊢
      exact lie_evenPart_evenPart hgi hgj
    · have hk : k = 1 := by rw [← hsum]; decide
      subst hk
      rw [gradePart_zero] at hgi
      rw [gradePart_one] at hgj ⊢
      exact lie_evenPart_oddPart hgi hgj
    · have hk : k = 1 := by rw [← hsum]; decide
      subst hk
      rw [gradePart_one] at hgi ⊢
      rw [gradePart_zero] at hgj
      exact lie_oddPart_evenPart hgi hgj
    · have hk : k = 0 := by rw [← hsum]; decide
      subst hk
      rw [gradePart_one] at hgi hgj
      rw [gradePart_zero]
      exact lie_oddPart_oddPart hgi hgj

noncomputable instance decomposition_gradePart : DirectSum.Decomposition (gradePart p q) :=
  isInternal_gradePart.chooseDecomposition

/-- **`gl(p+q)` IS A `GradedLieAlgebra` OVER `ZMod 2` IN MATHLIB'S OWN SENSE.** Every word of the
phrase "ℤ/2-grading" in this file's header is discharged by this instance; none of it is prose. -/
noncomputable instance gradedLieAlgebra_gradePart : GradedLieAlgebra (gradePart p q) where
  __ := gradedBracket_gradePart
  __ := decomposition_gradePart

end BlockGrading
