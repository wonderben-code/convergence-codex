/-
  OrderOneRegularBimodule.lean — the order-one condition on the regular bimodule of `Mₙ(ℂ)` is
  SOLVED: an operator `D` satisfies it iff `D = C ⊗ 1 + 1 ⊗ B`, a left multiplication plus a
  right multiplication. At every `n`, over any commutative ring at the matrix level; on the
  estate's witness `Hw` the Dirac operator `Dccm = σ₃ ⊗ 1 + 1 ⊗ σ₃` is an instance.

  SPINE L6 / `WALLS` §W9 rung 2, SECOND half in §W9.8's words — *what the order-one condition
  does to the pair `(A, A°)` acting on `H`* — answered on the regular bimodule of a single
  matrix factor. Hardening unit 168, 2026-09-20.

  WHY. §§W9.2–W9.7 located the failing step of the CCM classification at the order-one condition
  and built a witness where it is not vacuous (`OrderOneNontrivial`, `RealSpectralWitness`). What
  no unit had asked is what order-one FORCES. `RealSpectralWitness.lean`'s docstring on `Dsym`
  says it in passing — *"`JDJ = D` and order-one together force `D = A ⊗ 1 + 1 ⊗ Ā`"* — as the
  method by which `σ₃` was found, and no theorem in the estate said so. The order-one half is
  this file: write `D` in `n × n` blocks and read `⁅⁅D, e_{kl} ⊗ 1⁆, 1 ⊗ e_{rs}⁆ = 0` entrywise;
  one family of identities falls out (`orderOne_entry`), and its four specialisations say the
  off-diagonal blocks are scalars, the diagonal blocks differ by scalars, and the common part is
  one matrix — so `D = C ⊗ 1 + 1 ⊗ B`, with `C` and `B` written down. The converse is two lines.
  So on the regular bimodule the order-one condition is not a constraint to be checked witness by
  witness; it is a description of the whole solution set, and `Dccm` is the point of it that `J`
  and `γ` then pick out. The `J` half of the docstring's sentence (`B = Ā`) is not proved here.
  ⚠ 26 September 2026 (unit 229, `ERRATUM 698`): proved the same day by unit 169 —
  order-one and `Jprod`-invariance hold iff `D = A ⊗ 1 + 1 ⊗ Ā` (`JSelectsDirac.orderOne_jInv_iff`).
  Kept as written (`ERRATUM 94`).

  WHAT IS PROVED (matrix level: `R` any commutative ring; `n ≥ 1` where `0 : Fin n` is used).
  * `mul_single_kron_one_apply`, `single_kron_one_mul_apply`, `mul_one_kron_single_apply`,
    `one_kron_single_mul_apply` — the entries of `M · (e_{kl} ⊗ 1)`, `(e_{kl} ⊗ 1) · M`,
    `M · (1 ⊗ e_{rs})`, `(1 ⊗ e_{rs}) · M`.
  * **`orderOne_entry`** — order-one at matrix units, entrywise; `entry_offdiag_offdiag`,
    `entry_offdiag_diag`, `entry_diag_offdiag`, `entry_diag_diag` — its four consequences.
  * **`exists_kron_of_orderOne`** — order-one ⟹ `M = C ⊗ 1 + 1 ⊗ B`, with `C_{ik} = M_{(i,0),(k,0)}`
    off the diagonal and `M_{(i,0),(i,0)} − M_{(0,0),(0,0)}` on it, and `B` the `(0,0)` block;
    `sub_kronecker'`, `lie_kron_left`, `lie_kron_right`, **`orderOne_of_kron`** — the converse;
    **`orderOne_iff_kron`** — the characterisation.
  * (over `ℂ`, on the estate's objects) `map_lie_lie`, `matAlg_surjective'` (every index type);
    **`orderOne_matAlg_iff`** — for `π = matAlg ∘ kronLeft`, `πOp = matAlg ∘ kronRight` on
    `ℂ^{n × n}`, order-one iff `D = π C + πOp (op B)`; **`orderOne_Hw_iff`** — the same on `Hw`
    against `piW`/`piOpW`; `oneForm_piW` — the one-form of such a `D` is `piW ⁅C, a⁆`;
    **`Dccm_eq_piW_add_piOpW`** — the witness's Dirac operator is `piW σ₃ + piOpW (op σ₃)`.

  WHAT IS **NOT** PROVED, said exactly.
  * The `J` half of the docstring's sentence — that `Jprod D Jprod = D` forces `B = Ā` up to the
    scalar the two slots share. Not here.
    ⚠ 26 September 2026 (unit 229, `ERRATUM 698`): proved the same day by unit 169
    (`JSelectsDirac.orderOne_jInv_iff`; the shared scalar is real and absorbed into `A`). Kept as
    written (`ERRATUM 94`).
  * Anything off the REGULAR bimodule. CCM imposes order-one on `A_F` acting on the fermion space
    `H_F`, not on `A` acting on itself, and nothing here transfers. No factor list is cut; two
    factors, `ℝ`/`ℍ`, unequal sizes, the cascade — none of it. Rung 2 is not climbed; its second
    half is answered for one class of bimodule.
    ⚠ 26 September 2026 (hardening unit 228, `paper_f/OrderOneBlockDiagonal.lean`): *two factors …
    unequal sizes* — `M_N` as a bimodule over a product of matrix algebras of any sizes sitting
    block-diagonally in it, every pair of factors occurring once, is solved there: order-one against
    the block-diagonal matrices holds iff the operator is a left multiplication depending on the
    right block plus a right multiplication depending on the left block
    (`OrderOneBlockDiagonal.orderOne_iff`), and this file's `orderOne_iff_kron` is derived there as
    its one-block case, for every finite index type
    (`OrderOneBlockDiagonal.orderOne_iff_kron_of_const`). Multiplicities, sub-bimodules, `ℝ`/`ℍ` and
    the cascade stand; rung 2 is not climbed.
  * Uniqueness of `(C, B)`: the pair is determined only up to `(C + λ·1, B − λ·1)`, and that is
    not stated.
    ⚠ 26 September 2026 (hardening unit 228, `paper_f/OrderOneBlockDiagonal.lean`): stated
    there, for every nonempty finite index type and any commutative ring — `C ⊗ 1 + 1 ⊗ B`
    determines `(C, B)` exactly up to `(C + c • 1, B − c • 1)`
    (`OrderOneBlockDiagonal.kron_eq_kron_iff`), and on a product of blocks up to block-scalars
    moved between the parts (`blockKron_eq_blockKron_iff`).
  * `n = 0` is excluded where `0 : Fin n` is used (`[NeZero n]`); the entry lemmas hold at every
    `n`.
    ⚠ 26 September 2026 (hardening unit 228, `paper_f/OrderOneBlockDiagonal.lean`):
    `orderOne_iff_kron` is derived there for every finite index type, the empty one included
    (`OrderOneBlockDiagonal.orderOne_iff_kron_of_const`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import EvenGradingObstruction
import RealSpectralWitness

open Matrix
open scoped Kronecker

namespace OrderOneRegularBimodule

variable {n : ℕ} {R : Type*} [CommRing R]

/-- The entry of `M * (single k l 1 ⊗ₖ 1)`. -/
theorem mul_single_kron_one_apply (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (k l i p j q : Fin n) :
    (M * (single k l (1 : R) ⊗ₖ (1 : Matrix (Fin n) (Fin n) R))) (i, p) (j, q)
      = if l = j then M (i, p) (k, q) else 0 := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and, mul_ite]

/-- The entry of `(single k l 1 ⊗ₖ 1) * M`. -/
theorem single_kron_one_mul_apply (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (k l i p j q : Fin n) :
    ((single k l (1 : R) ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)) * M) (i, p) (j, q)
      = if i = k then M (l, p) (j, q) else 0 := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all

theorem mul_one_kron_single_apply (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (r s i p j q : Fin n) :
    (M * ((1 : Matrix (Fin n) (Fin n) R) ⊗ₖ single r s (1 : R))) (i, p) (j, q)
      = if s = q then M (i, p) (j, r) else 0 := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq', ite_and, mul_ite]

theorem one_kron_single_mul_apply (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (r s i p j q : Fin n) :
    (((1 : Matrix (Fin n) (Fin n) R) ⊗ₖ single r s (1 : R)) * M) (i, p) (j, q)
      = if p = r then M (i, s) (j, q) else 0 := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_ite_eq, ite_and, mul_ite, ite_mul]
  split_ifs <;> simp_all

/-- **Order-one at matrix units, entrywise.** `L a := a ⊗ₖ 1`, `R b := 1 ⊗ₖ b`. -/
theorem orderOne_entry (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (h : ∀ a b : Matrix (Fin n) (Fin n) R,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0)
    (i p j q k l r : Fin n) :
    (if l = j then M (i, p) (k, r) else 0) - (if i = k then M (l, p) (j, r) else 0)
      - ((if p = r then (if l = j then M (i, q) (k, q) else 0) else 0)
        - (if p = r then (if i = k then M (l, q) (j, q) else 0) else 0)) = 0 := by
  have := congrFun (congrFun (h (single k l 1) (single r q 1)) (i, p)) (j, q)
  simp only [Ring.lie_def, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply, Matrix.zero_apply,
    mul_one_kron_single_apply, one_kron_single_mul_apply, mul_single_kron_one_apply,
    single_kron_one_mul_apply] at this
  simpa using this

/-- The four consequences, with `l = j`. -/
theorem entry_offdiag_offdiag (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (h : ∀ a b : Matrix (Fin n) (Fin n) R,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0)
    {i k p q : Fin n} (hik : i ≠ k) (hpq : p ≠ q) : M (i, p) (k, q) = 0 := by
  have e := orderOne_entry M h i p k q k k q
  simp only [↓reduceIte, hik, sub_zero, hpq, sub_self] at e
  exact e

theorem entry_offdiag_diag (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (h : ∀ a b : Matrix (Fin n) (Fin n) R,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0)
    {i k : Fin n} (hik : i ≠ k) (p q : Fin n) : M (i, p) (k, p) = M (i, q) (k, q) := by
  have e := orderOne_entry M h i p k q k k p
  simp only [↓reduceIte, hik, sub_zero] at e
  exact sub_eq_zero.mp e

theorem entry_diag_offdiag (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (h : ∀ a b : Matrix (Fin n) (Fin n) R,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0)
    (i j : Fin n) {p q : Fin n} (hpq : p ≠ q) : M (i, p) (i, q) = M (j, p) (j, q) := by
  have e := orderOne_entry M h i p j q i j q
  simp only [↓reduceIte, hpq, sub_self, sub_zero] at e
  exact sub_eq_zero.mp e

theorem entry_diag_diag (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (h : ∀ a b : Matrix (Fin n) (Fin n) R,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0)
    (i j p q : Fin n) : M (i, p) (i, p) - M (j, p) (j, p) = M (i, q) (i, q) - M (j, q) (j, q) := by
  have e := orderOne_entry M h i p j q i j p
  simp only [↓reduceIte] at e
  exact sub_eq_zero.mp e

/-- **THE CLASSIFICATION.** Order-one on the regular bimodule forces `M = C ⊗ 1 + 1 ⊗ B`. -/
theorem exists_kron_of_orderOne [NeZero n] (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R)
    (h : ∀ a b : Matrix (Fin n) (Fin n) R,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0) :
    ∃ C B : Matrix (Fin n) (Fin n) R,
      M = C ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) + (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ B := by
  refine ⟨Matrix.of fun i k => if i = k then M (i, 0) (i, 0) - M (0, 0) (0, 0) else M (i, 0) (k, 0),
    Matrix.of fun p q => M (0, p) (0, q), ?_⟩
  ext ⟨i, p⟩ ⟨k, q⟩
  simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.of_apply, Matrix.one_apply]
  by_cases hik : i = k
  · subst hik
    by_cases hpq : p = q
    · subst hpq
      have e := entry_diag_diag M h i 0 p 0
      simp only [if_true, mul_one, one_mul]
      linear_combination e
    · have e := entry_diag_offdiag M h i 0 hpq
      simp only [if_true, hpq, if_false, mul_zero, one_mul, zero_add]
      exact e
  · by_cases hpq : p = q
    · subst hpq
      have e := entry_offdiag_diag M h hik p 0
      simp only [hik, if_false, if_true, mul_one, zero_mul, add_zero]
      exact e
    · have e := entry_offdiag_offdiag M h hik hpq
      simp only [hik, hpq, if_false, mul_zero, zero_mul, add_zero]
      exact e

/-- Kronecker is additive in the left factor, subtraction form (Mathlib has `add_kronecker`). -/
theorem sub_kronecker' (A₁ A₂ : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin n) (Fin n) R) :
    (A₁ - A₂) ⊗ₖ B = A₁ ⊗ₖ B - A₂ ⊗ₖ B := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp [kroneckerMap_apply, sub_mul]

/-- `⁅C ⊗ 1 + 1 ⊗ B, a ⊗ 1⁆ = ⁅C, a⁆ ⊗ 1`: the right factor drops out of the one-form. -/
theorem lie_kron_left (C B a : Matrix (Fin n) (Fin n) R) :
    ⁅C ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) + (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ B,
      a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆ = (C * a - a * C) ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) := by
  simp only [Ring.lie_def, Matrix.add_mul, Matrix.mul_add, ← mul_kronecker_mul, one_mul, mul_one]
  rw [sub_kronecker']
  abel

/-- A left-slot Kronecker commutes with every right-slot one. -/
theorem lie_kron_right (X b : Matrix (Fin n) (Fin n) R) :
    ⁅X ⊗ₖ (1 : Matrix (Fin n) (Fin n) R), (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0 := by
  simp only [Ring.lie_def, ← mul_kronecker_mul, one_mul, mul_one, sub_self]

/-- **The converse**: every `C ⊗ 1 + 1 ⊗ B` satisfies order-one. -/
theorem orderOne_of_kron (C B a b : Matrix (Fin n) (Fin n) R) :
    ⁅⁅C ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) + (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ B,
      a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0 := by
  rw [lie_kron_left, lie_kron_right]

/-- **Order-one on the regular bimodule, characterised.** -/
theorem orderOne_iff_kron [NeZero n] (M : Matrix (Fin n × Fin n) (Fin n × Fin n) R) :
    (∀ a b : Matrix (Fin n) (Fin n) R,
      ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) R)⁆, (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ b⁆ = 0) ↔
    ∃ C B : Matrix (Fin n) (Fin n) R,
      M = C ⊗ₖ (1 : Matrix (Fin n) (Fin n) R) + (1 : Matrix (Fin n) (Fin n) R) ⊗ₖ B := by
  constructor
  · exact exists_kron_of_orderOne M
  · rintro ⟨C, B, rfl⟩ a b
    exact orderOne_of_kron C B a b

/-! ## 4. On the estate's regular bimodules, at every `n` and on the witness `Hw` -/

open OrderOneNontrivial EvenGradingObstruction MulOpposite SpectralTripleBimodule

/-- An algebra map carries the double commutator. -/
theorem map_lie_lie {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (x y z : A) : f ⁅⁅x, y⁆, z⁆ = ⁅⁅f x, f y⁆, f z⁆ := by
  simp only [Ring.lie_def, map_sub, map_mul]

/-- `matAlg ι` is onto — `EvenGradingObstruction.matAlg_surjective` at every index type. -/
theorem matAlg_surjective' (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Function.Surjective (matAlg ι) := by
  intro f
  refine ⟨(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).symm
    (LinearMap.toContinuousLinearMap f), ?_⟩
  refine LinearMap.ext fun v => ?_
  rw [matAlg_apply]
  simp

/-- **ORDER-ONE ON THE REGULAR BIMODULE OF `Mₙ(ℂ)`, CHARACTERISED.** With `π = matAlg ∘ kronLeft`
(`a ↦ a ⊗ 1`) and `πOp = matAlg ∘ kronRight` (`op b ↦ 1 ⊗ bᵀ`) on `ℂ^{n × n}`, an operator `D`
satisfies the order-one condition iff it is a left multiplication plus a right multiplication. -/
theorem orderOne_matAlg_iff [NeZero n] (D : Module.End ℂ (EuclideanSpace ℂ (Fin n × Fin n))) :
    (∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ),
      ⁅⁅D, matAlg _ (kronLeft (Fin n) (Fin n) a)⁆, matAlg _ (kronRight (Fin n) (Fin n) b)⁆ = 0) ↔
    ∃ C B : Matrix (Fin n) (Fin n) ℂ,
      D = matAlg _ (kronLeft (Fin n) (Fin n) C) + matAlg _ (kronRight (Fin n) (Fin n) (op B)) := by
  obtain ⟨M, rfl⟩ := matAlg_surjective' (Fin n × Fin n) D
  have key : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ),
      ⁅⁅matAlg _ M, matAlg _ (kronLeft (Fin n) (Fin n) a)⁆,
        matAlg _ (kronRight (Fin n) (Fin n) b)⁆ = 0 ↔
        ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)⁆,
          (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ (unop b)ᵀ⁆ = 0 := by
    intro a b
    rw [← map_lie_lie, kronLeft_apply, kronRight_apply]
    constructor
    · intro h; exact (matAlg_injective _) (by rw [h, map_zero])
    · intro h; rw [h, map_zero]
  constructor
  · intro h
    have h' : ∀ a b : Matrix (Fin n) (Fin n) ℂ,
        ⁅⁅M, a ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)⁆, (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ b⁆ = 0 := by
      intro a b
      have := (key a (op bᵀ)).mp (h a (op bᵀ))
      simpa using this
    obtain ⟨C, B, hM⟩ := exists_kron_of_orderOne M h'
    refine ⟨C, Bᵀ, ?_⟩
    rw [← map_add, kronLeft_apply, kronRight_apply, unop_op, Matrix.transpose_transpose, hM]
  · rintro ⟨C, B, hD⟩ a b
    rw [key]
    have : M = C ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) + (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ Bᵀ := by
      apply matAlg_injective
      rw [map_add, hD, kronLeft_apply, kronRight_apply, unop_op]
    rw [this]
    exact orderOne_of_kron C Bᵀ a (unop b)ᵀ

/-- **On the witness `Hw`** (`n = 2`): order-one against `piW`/`piOpW` iff
`D = piW C + piOpW (op B)`. -/
theorem orderOne_Hw_iff (D : Module.End ℂ Hw) :
    (∀ (a : Matrix (Fin 2) (Fin 2) ℂ) (b : (Matrix (Fin 2) (Fin 2) ℂ)ᵐᵒᵖ),
      ⁅⁅D, piW a⁆, piOpW b⁆ = 0) ↔
    ∃ C B : Matrix (Fin 2) (Fin 2) ℂ, D = piW C + piOpW (op B) :=
  orderOne_matAlg_iff (n := 2) D

/-- The one-form of `piW C + piOpW (op B)` is `piW ⁅C, a⁆`: the right slot drops out. -/
theorem oneForm_piW (C B a : Matrix (Fin 2) (Fin 2) ℂ) :
    ⁅piW C + piOpW (op B), piW a⁆ = piW ⁅C, a⁆ := by
  change ⁅matAlg Slots (kronLeft (Fin 2) (Fin 2) C)
      + matAlg Slots (kronRight (Fin 2) (Fin 2) (op B)),
      matAlg Slots (kronLeft (Fin 2) (Fin 2) a)⁆ = matAlg Slots (kronLeft (Fin 2) (Fin 2) ⁅C, a⁆)
  rw [← map_add, Ring.lie_def, ← map_mul, ← map_mul, ← map_sub, Ring.lie_def]
  congr 1
  rw [kronLeft_apply, kronRight_apply, unop_op, kronLeft_apply]
  have := lie_kron_left C Bᵀ a
  rw [Ring.lie_def] at this
  exact this

/-- **The witness's Dirac operator is an instance**:
`Dccm = σ₃ ⊗ 1 + 1 ⊗ σ₃ = piW σ₃ + piOpW (op σ₃)`. -/
theorem Dccm_eq_piW_add_piOpW :
    RealSpectralWitness.Dccm = piW pauli3 + piOpW (op pauli3) := by
  change matAlg Slots RealSpectralWitness.Dsym
    = matAlg Slots (kronLeft (Fin 2) (Fin 2) pauli3)
      + matAlg Slots (kronRight (Fin 2) (Fin 2) (op pauli3))
  rw [← map_add, kronLeft_apply, kronRight_apply, unop_op, pauli3_transpose]
  rfl

end OrderOneRegularBimodule
