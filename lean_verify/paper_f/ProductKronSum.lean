/-
  ProductKronSum.lean — order-one forces the tensor-sum shape on a product of matrix algebras
  exactly when the product has one factor. Unit 228 solved order-one for a finite product of
  matrix algebras sitting block-diagonally in `M_N`, every pair of factors occurring once — the
  regular bimodule of `M_N` restricted to the product: the solutions are `blockKron β C B`, a
  left multiplication that may depend on the right block plus a right multiplication that may
  depend on the left block. Here it is decided which of them are tensor sums `C' ⊗ 1 + 1 ⊗ B'`:
  exactly those whose left parts agree off the diagonal across the blocks, whose right parts do
  likewise, and whose diagonal is a function of the left point plus a function of the right
  point. So order-one forces the shape for every operator iff all points lie in one block — one
  full matrix algebra, unit 168's case — and with the real structure `J` the same; as soon as two
  blocks occur a self-adjoint witness exists, the smallest on `ℂ ⊕ ℂ` acting on `ℂ² ⊗ ℂ²`. With
  unit 242, order-one on the estate's models forces the tensor-sum shape exactly for one full
  matrix algebra at multiplicity one, the trivial `M₁` aside.

  SPINE L19 / `ASSUMPTIONS_LEDGER` 12 — the tensor-sum premise of unit 172's factorisation, on a
  product; SPINE L6 / `WALLS` §W9 rung 2, second half. Hardening unit 243, 26 September 2026.

  WHY. Unit 242 decided the shape for one full matrix algebra on each slot with a generation
  index: forced exactly at multiplicity one. CCM's `A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)` is a product, and in the
  estate's product model, unit 228's, the left multiplication may depend on the right block.
  Unit 228's header records the one-block case as a tensor sum (`blockKron_const`) and does not
  ask about two blocks or more, so whether a product keeps the shape at multiplicity one was
  open.

  WHAT IS PROVED (`K` any field, `ι` any finite type, the blocks the fibres of any `β : ι → κ`).
  (1) `blockDiag β C B x p`: the diagonal entry of `blockKron β C B` at `(x, p)`;
      `blockKron_apply`. **`isKronSum_blockKron_iff`**: `blockKron β C B` is a Kronecker sum iff
      `C (β p) x y` does not depend on `p` for `x ≠ y`, `B (β x) p q` does not depend on `x` for
      `p ≠ q`, and the diagonal is additively separable, `F x p + F x' p' = F x p' + F x' p` for
      `F = blockDiag β C B`.
  (2) `unitAt β x₀`: the diagonal matrix unit at `x₀` in the block of `x₀`, zero in the others
      (`unitAt_self`, `unitAt_of_ne`, `unitAt_diag_of_ne`).
      **`blockOrderOne_forces_isKronSum_iff`**: every operator satisfying unit 228's order-one
      condition is a tensor sum iff `β` takes one value on `ι` — all points in one block.
  (3) With `J`, over `ℂ`. `blockKron_conj_isHermitian`: `blockKron β A Ā` is self-adjoint when
      every `A k` is; `unitAt_isHermitian`, `blockDiag_unitAt_conj`.
      **`blockOrderOne_jInv_forces_isKronSum_iff`**: every operator satisfying order-one and unit
      230's `J`-invariance is a tensor sum iff `β` takes one value;
      **`exists_blockOrderOne_jInv_not_kronSum`**: with two points in different blocks, a
      self-adjoint one that is not.

  NOT PROVED, said exactly.
  • A generation index on a product — unit 228's `blockKron` with a multiplicity — is not
    computed; nor the compression to a sub-bimodule, where CCM's `H_F` lives, since it contains
    some pairs of factors and not others.
  • The grading and the KO signs on a product, `ℍ` as a factor, and CCM's `A_F` on `H_F`.
  • The trace of the exponential where the shape fails: whether it factorises for another reason
    is not asked.
  • The cascade's `D` (the watchlist item *the cascade's `D` AS A TENSOR SUM*, `L40927` today),
    the factor list, a tag: rung 2 is not climbed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `unitAt_of_ne` takes `k ≠ β x₀`;
  `unitAt_diag_of_ne` takes `x ≠ x₀`; `blockKron_conj_isHermitian` takes every `A k` self-adjoint;
  `blockDiag_unitAt_conj` and `exists_blockOrderOne_jInv_not_kronSum` take `β x₀ ≠ β x₁`. The
  declarations that name `unitAt` take `DecidableEq κ`. Everything else takes elements of its
  types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 13 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: none is taken — three first drafts were, by unit 242's and unit
  234's versions with a generation index, and were renamed. The nearest statements are unit 228's
  `blockKron`, `blockKron_const` (one block: a tensor sum) and `orderOne_iff`; unit 230's
  `orderOne_exchConj_iff`; and unit 242's `IsKronSum`, `forall_isKronSum_iff`,
  `orderOne_forces_isKronSum_iff` and `orderOne_jInv_forces_isKronSum_iff`, of which (2) and (3)
  are the versions on a product.

  `#print axioms` on all 13 declarations below: `[propext, Classical.choice, Quot.sound]`.
-/

import KronSumCriterion
import OrderOneRealBlock

open Matrix
open scoped Kronecker

namespace ProductKronSum

open OrderOneBlockDiagonal OrderOneRealBlock KronSumCriterion

/-! ## 1. When `blockKron` is a tensor sum -/

section Criterion

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The diagonal of `blockKron β C B`, as a function of the left point and the right point. -/
def blockDiag (β : ι → κ) (C B : κ → Matrix ι ι K) (x p : ι) : K :=
  C (β p) x x + B (β x) p p

omit [Fintype ι] in
theorem blockKron_apply (β : ι → κ) (C B : κ → Matrix ι ι K) (x p y q : ι) :
    blockKron β C B (x, p) (y, q) =
      (if p = q then C (β p) x y else 0) + (if x = y then B (β x) p q else 0) := rfl

omit [Fintype ι] in
/-- **WHEN A PRODUCT'S ORDER-ONE OPERATOR IS A TENSOR SUM**: `blockKron β C B` is
`C' ⊗ 1 + 1 ⊗ B'` iff the left parts agree off the diagonal across the blocks that occur, the right
parts likewise, and the diagonal is a function of the left point plus a function of the right
point. -/
theorem isKronSum_blockKron_iff (β : ι → κ) (C B : κ → Matrix ι ι K) :
    IsKronSum (blockKron β C B) ↔
      (∀ p p' x y, x ≠ y → C (β p) x y = C (β p') x y) ∧
      (∀ x x' p q, p ≠ q → B (β x) p q = B (β x') p q) ∧
      (∀ x x' p p', blockDiag β C B x p + blockDiag β C B x' p' =
        blockDiag β C B x p' + blockDiag β C B x' p) := by
  constructor
  · rintro ⟨C', B', h⟩
    have e : ∀ x p y q, blockKron β C B (x, p) (y, q) =
        C' x y * (if p = q then 1 else 0) + (if x = y then 1 else 0) * B' p q := by
      intro x p y q
      rw [h]
      simp [kroneckerMap_apply, one_apply]
    refine ⟨fun p p' x y hxy => ?_, fun x x' p q hpq => ?_, fun x x' p p' => ?_⟩
    · have h1 := e x p y p
      have h2 := e x p' y p'
      simp only [blockKron_apply, if_true, hxy, if_false, add_zero, mul_one, zero_mul] at h1 h2
      rw [h1, h2]
    · have h1 := e x p x q
      have h2 := e x' p x' q
      simp only [blockKron_apply, if_true, hpq, if_false, zero_add, mul_zero, one_mul] at h1 h2
      rw [h1, h2]
    · have h1 := e x p x p
      have h2 := e x' p' x' p'
      have h3 := e x p' x p'
      have h4 := e x' p x' p
      simp only [blockKron_apply, if_true, mul_one, one_mul] at h1 h2 h3 h4
      simp only [blockDiag]
      linear_combination h1 + h2 - h3 - h4
  · rintro ⟨h1, h2, h3⟩
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨x₀⟩⟩
    · exact ⟨0, 0, Matrix.ext fun a _ => hι.elim a.1⟩
    refine ⟨Matrix.of fun x y => if x = y then blockDiag β C B x x₀ else C (β x₀) x y,
      Matrix.of fun p q => if p = q then blockDiag β C B x₀ p - blockDiag β C B x₀ x₀
        else B (β x₀) p q, ?_⟩
    ext ⟨x, p⟩ ⟨y, q⟩
    simp only [blockKron_apply, add_apply, kroneckerMap_apply, one_apply, of_apply]
    rcases eq_or_ne x y with rfl | hxy <;> rcases eq_or_ne p q with rfl | hpq
    · have := h3 x x₀ p x₀
      simp only [blockDiag, if_true, mul_one, one_mul] at this ⊢
      linear_combination this
    · simp only [if_true, hpq, if_false, zero_add, mul_zero, one_mul]
      exact h2 x x₀ p q hpq
    · simp only [if_true, hxy, if_false, add_zero, mul_one, zero_mul]
      exact h1 p x₀ x y hxy
    · simp only [hxy, hpq, if_false, add_zero, mul_zero, zero_mul]

end Criterion

/-! ## 2. The witness, and the dichotomy: order-one against a product forces the shape exactly at
one factor -/

section Dichotomy

variable {ι κ K : Type*} [DecidableEq ι] [DecidableEq κ] [Field K]

/-- The witness: the diagonal matrix unit at `x₀` in the block of `x₀`, and zero in every other
block. -/
def unitAt (β : ι → κ) (x₀ : ι) (k : κ) : Matrix ι ι K :=
  if k = β x₀ then single x₀ x₀ 1 else 0

theorem unitAt_self (β : ι → κ) (x₀ : ι) : unitAt (K := K) β x₀ (β x₀) x₀ x₀ = 1 := by
  simp [unitAt]

theorem unitAt_of_ne {β : ι → κ} {x₀ : ι} {k : κ} (h : k ≠ β x₀) (x y : ι) :
    unitAt (K := K) β x₀ k x y = 0 := by
  simp [unitAt, h]

theorem unitAt_diag_of_ne {β : ι → κ} {x₀ x : ι} (h : x ≠ x₀) (k : κ) :
    unitAt (K := K) β x₀ k x x = 0 := by
  unfold unitAt
  split_ifs <;> simp [Ne.symm h]

variable [Fintype ι]

omit [DecidableEq κ] in
/-- **ORDER-ONE AGAINST A PRODUCT FORCES THE TENSOR-SUM SHAPE EXACTLY WHEN THE PRODUCT HAS ONE
FACTOR**: every operator satisfying order-one against the block-diagonal matrices is
`C ⊗ 1 + 1 ⊗ B` iff all points of `ι` lie in one block. -/
theorem blockOrderOne_forces_isKronSum_iff (β : ι → κ) :
    (∀ M : Matrix (ι × ι) (ι × ι) K, OrderOne β M → IsKronSum M) ↔ ∀ x y : ι, β x = β y := by
  classical
  constructor
  · intro h x₀ x₁
    by_contra hne
    have hx : x₁ ≠ x₀ := fun e => hne (e ▸ rfl)
    obtain ⟨-, -, h3⟩ := (isKronSum_blockKron_iff β _ _).mp
      (h _ (orderOne_blockKron β (unitAt β x₀) 0))
    have := h3 x₀ x₁ x₀ x₁
    simp only [blockDiag, Pi.zero_apply, zero_apply, add_zero, unitAt_self,
      unitAt_of_ne (Ne.symm hne), unitAt_diag_of_ne hx] at this
    exact one_ne_zero this
  · intro h M hM
    obtain ⟨C, B, rfl⟩ := (orderOne_iff β M).mp hM
    refine (isKronSum_blockKron_iff β C B).mpr ⟨fun p p' x y _ => by rw [h p p'],
      fun x x' p q _ => by rw [h x x'], fun x x' p p' => ?_⟩
    simp only [blockDiag]
    rw [h p x, h p' x, h x' x]
    ring

end Dichotomy

/-! ## 3. With the real structure `J` -/

section Real

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq κ] in
/-- `blockKron β A Ā` is self-adjoint when every `A k` is. -/
theorem blockKron_conj_isHermitian {β : ι → κ} {A : κ → Matrix ι ι ℂ}
    (hA : ∀ k, (A k).IsHermitian) :
    (blockKron β A fun j => (A j).map (starRingEnd ℂ)).IsHermitian := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [conjTranspose_apply, blockKron_apply, map_apply, starRingEnd_apply]
  by_cases hpq : p = q <;> by_cases hxy : x = y
  · subst hpq hxy
    simp [(hA _).apply]
  · subst hpq
    simp [hxy, Ne.symm hxy, (hA _).apply]
  · subst hxy
    simp [hpq, Ne.symm hpq, (hA _).apply]
  · simp [hpq, hxy, Ne.symm hpq, Ne.symm hxy]

omit [Fintype ι] in
theorem unitAt_isHermitian (β : ι → κ) (x₀ : ι) (k : κ) :
    (unitAt (K := ℂ) β x₀ k).IsHermitian := by
  unfold unitAt
  split_ifs
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_single, star_one]
  · exact Matrix.isHermitian_zero

omit [Fintype ι] in
theorem blockDiag_unitAt_conj {β : ι → κ} {x₀ x₁ : ι} (hne : β x₀ ≠ β x₁) :
    blockDiag β (unitAt β x₀) (fun j => (unitAt (K := ℂ) β x₀ j).map (starRingEnd ℂ)) x₀ x₀ +
        blockDiag β (unitAt β x₀) (fun j => (unitAt β x₀ j).map (starRingEnd ℂ)) x₁ x₁ ≠
      blockDiag β (unitAt β x₀) (fun j => (unitAt β x₀ j).map (starRingEnd ℂ)) x₀ x₁ +
        blockDiag β (unitAt β x₀) (fun j => (unitAt β x₀ j).map (starRingEnd ℂ)) x₁ x₀ := by
  have hx : x₁ ≠ x₀ := fun e => hne (e ▸ rfl)
  simp only [blockDiag, map_apply, unitAt_self, unitAt_of_ne (Ne.symm hne),
    unitAt_diag_of_ne hx, map_one, map_zero, add_zero]
  norm_num

omit [DecidableEq κ] in
/-- **AND WITH `J`**: every operator satisfying order-one against the block-diagonal matrices and
`J`-invariance is a tensor sum iff all points of `ι` lie in one block. -/
theorem blockOrderOne_jInv_forces_isKronSum_iff (β : ι → κ) :
    (∀ M : Matrix (ι × ι) (ι × ι) ℂ, OrderOne β M ∧ exchConj M = M → IsKronSum M) ↔
      ∀ x y : ι, β x = β y := by
  classical
  constructor
  · intro h x₀ x₁
    by_contra hne
    obtain ⟨-, -, h3⟩ := (isKronSum_blockKron_iff β _ _).mp
      (h _ ((orderOne_exchConj_iff β _).mpr ⟨unitAt β x₀, rfl⟩))
    exact blockDiag_unitAt_conj hne (h3 x₀ x₁ x₀ x₁)
  · intro h M hM
    exact (blockOrderOne_forces_isKronSum_iff β).mpr h M hM.1

omit [DecidableEq κ] in
/-- **A SELF-ADJOINT WITNESS**: once two points of `ι` lie in different blocks, some self-adjoint
operator satisfying order-one against the block-diagonal matrices and `J`-invariance is not a
tensor sum. The smallest case is `ι = Fin 2`, `β = id`: the product `ℂ ⊕ ℂ`, acting on
`ℂ² ⊗ ℂ²` from both sides. -/
theorem exists_blockOrderOne_jInv_not_kronSum {β : ι → κ} {x₀ x₁ : ι} (hne : β x₀ ≠ β x₁) :
    ∃ M : Matrix (ι × ι) (ι × ι) ℂ, M.IsHermitian ∧ OrderOne β M ∧ exchConj M = M ∧
      ¬ IsKronSum M := by
  classical
  have hJ := (orderOne_exchConj_iff β
    (blockKron β (unitAt β x₀) fun j => (unitAt β x₀ j).map (starRingEnd ℂ))).mpr
    ⟨unitAt β x₀, rfl⟩
  refine ⟨_, blockKron_conj_isHermitian (unitAt_isHermitian β x₀), hJ.1, hJ.2, fun h => ?_⟩
  obtain ⟨-, -, h3⟩ := (isKronSum_blockKron_iff β _ _).mp h
  exact blockDiag_unitAt_conj hne (h3 x₀ x₁ x₀ x₁)

end Real

end ProductKronSum
