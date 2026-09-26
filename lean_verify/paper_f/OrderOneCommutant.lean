/-
  OrderOneCommutant.lean — the order-one condition on a tensor-product bimodule, in general and
  with a repeated piece. On `K^ι ⊗ K^κ`, with left action `a ⊗ 1` and right action `1 ⊗ b` by ANY
  sets of matrices over ANY field, an operator satisfies `⁅⁅D, a ⊗ 1⁆, 1 ⊗ b⁆ = 0` iff it is an
  operator commuting with the right action plus an operator commuting with the left; the split is
  unique exactly up to the operators commuting with both, and it holds on every sub-bimodule cut
  out by an idempotent commuting with both actions. For full matrix algebras with the right one
  acting with a multiplicity, both commutants are computed: `D` is an operator on the left factor
  and the multiplicity space plus an operator on the right factor and the multiplicity space. With
  no multiplicity that is the tensor-sum shape `C ⊗ 1 + 1 ⊗ B`, at any sizes; with a multiplicity
  of two the shape is not forced.

  SPINE L6 / `WALLS` §W9 rung 2, second clause — from every pair of factors once (unit 228) to any
  test sets, multiplicities and sub-bimodules; and SPINE L19 / `ASSUMPTIONS_LEDGER` 12 — the
  tensor-sum shape that unit 172's factorisation of the spectral action starts from is forced by
  order-one when no piece repeats, and not when one repeats twice. Hardening unit 232,
  26 September 2026.

  WHY. Unit 228 solved order-one for `M_N` over a product of matrix algebras with every pair of
  factors once (`OrderOneBlockDiagonal.orderOne_iff`), and its NOT list says *"The statement for a
  sum with multiplicities, and for the compression to a sub-bimodule, is not written."* CCM's `H_F`
  has some pieces three times over — one copy per generation, the algebra acting on each copy
  alike — and others not at all. Unit 228's proof reads the condition at the matrix units inside
  the blocks (`entry_of_orderOne`), and with multiplicities those are no longer test matrices: for
  `m ≥ 2` the image of `a ↦ a ⊗ 1ₘ` contains no matrix unit at all. The route here uses none: the
  blocks of `⁅D, a ⊗ 1⁆` are linear combinations of the blocks of `D`, so a complement of the right
  action's centralizer splits every block of `D` at once. And unit 172 (`OrderOneCutoffFactorises`)
  drew `trace (exp (t • D)) = trace (exp (t • C)) · trace (exp (t • B))` from order-one on the
  regular bimodule, where order-one forces `D = C ⊗ 1 + 1 ⊗ B` (unit 168); `SPINE` L19 and
  `ASSUMPTIONS_LEDGER` 12 record that as the premise's one theorem-level source. Whether order-one
  still forces the shape once a piece repeats decides whether that source can reach a space with
  generations.

  WHAT IS PROVED (`ι`, `κ`, `μ` any finite types, `K` any field, `S_L`, `S_R` any sets of
  matrices).
  (1) `blockAt D x y`: the `(x, y)` block of `D`, a `κ × κ` matrix. **`commute_one_kron_iff`**:
      `D` commutes with `1 ⊗ b` iff every block of `D` commutes with `b`;
      **`blockAt_lie_kron_one`**: the `(x, y)` block of `⁅D, a ⊗ 1⁆` is
      `∑ z, a z y • blockAt D x z − ∑ z, a x z • blockAt D z y`.
  (2) **`orderOne_iff_commutant`**: `⁅⁅D, a ⊗ 1⁆, 1 ⊗ b⁆ = 0` for all `a ∈ S_L`, `b ∈ S_R` iff
      `D = X + Y` with `X` commuting with every `1 ⊗ b` and `Y` with every `a ⊗ 1`. `X`'s blocks
      are the projections of `D`'s onto the centralizer of `S_R` along a complement `Q`; the
      blocks of `⁅D − X, a ⊗ 1⁆` then lie in `Q`, and in the centralizer — `⁅D, a ⊗ 1⁆`'s by
      order-one, `⁅X, a ⊗ 1⁆`'s as combinations of `X`'s — so they vanish.
  (3) **`decomposition_fibre`**: given one split `X + Y`, the others are exactly `(X + Z, Y − Z)`
      with `Z` commuting with both actions.
  (4) **`orderOne_blockDiag_iff_commutant`**: unit 228's `OrderOne β` is the instance
      `S_L = S_R = blockDiagSet β`; there unit 228's `blockKron` writes the solutions out, a
      left-multiplication part commuting with the right action plus a right-multiplication part
      commuting with the left (`lie_leftMulPart_one_kron`, `lie_rightMulPart_kron_one`).
  (5) **`orderOne_iff_commutant_compress`**: for an idempotent `P` commuting with both actions and
      an operator `D` with `P D P = D` — an operator on the sub-bimodule `P` cuts out — order-one
      holds iff `D = X + Y` as in (2) with `P X P = X` and `P Y P = Y`.
  A representation with multiplicity is one choice of set: `S_L = {a ⊗ 1ₘ}` on `ι = ι₀ × Fin m`.
  So is a real algebra acting by complex matrices — `ℍ` inside `M₂(ℂ)` — at `K = ℂ`.
  (6) The commutant of a full matrix algebra acting with multiplicity. `fibreAt N i j`: the
      `(i, j)` fibre of a matrix on `κ × μ` over the multiplicity index;
      **`commute_kron_one_iff`**: `N` commutes with `b ⊗ 1` iff every fibre commutes with `b`;
      **`commute_all_kron_one_iff`**: `N` commutes with every `b ⊗ 1`, `b ∈ M_κ`, iff `N = 1 ⊗ G`
      — the commutant is the matrix algebra of the multiplicity space (fibrewise, by Mathlib's
      `Matrix.mem_range_scalar_of_commute_single`).
  (7) `genPart C`, for `C` on `ι × μ`: `C` acting on the left factor and the multiplicity space,
      trivially on `κ`; **`commute_genPart_iff`**: the operators commuting with every
      `1 ⊗ (b ⊗ 1)` are exactly the `genPart C`; **`orderOne_multiplicity_iff`**: against all of
      `M_ι` on the left and `M_κ ⊗ 1` on the right, order-one holds iff `D = genPart C + 1 ⊗ B`,
      `B` on `κ × μ` — (2) with both commutants computed. The two parts share the multiplicity
      space.
  (8) **`orderOne_iff_kronSum_of_unique`**: with `μ` a one-point type, iff `D = C ⊗ 1 + 1 ⊗ B` —
      unit 168's shape, at any sizes `ι`, `κ`. **`exists_orderOne_not_kronSum`**: at
      `ι = κ = μ = Fin 2`, `genPart (single (0, 0) (0, 0) 1) + 1 ⊗ single (0, 0) (0, 1) 1`
      satisfies order-one and is neither `C ⊗ 1 + 1 ⊗ B` nor `genPart C + 1 ⊗ (B ⊗ 1)` for any
      `C`, `B`: with a multiplicity of two, order-one does not force the tensor-sum shape in
      either grouping that keeps the multiplicity with one factor.

  NOT PROVED, said exactly.
  • That CCM's `H_F`, or any given bimodule, is such a compression of a tensor product of a left
    module and a right module. For finite-dimensional modules over semisimple algebras this is
    standard representation theory; it is not written here, and nothing here names `H_F`.
  • The commutants for other test sets. (6)–(7) compute them for full matrix algebras with the
    multiplicity on the right factor; for block-diagonal test sets with multiplicities, for `ℍ`, or
    for CCM's `A_F`, which `X` and `Y` occur is not computed, so no analogue of `blockKron` or of
    unit 228's support theorem (`entry_eq_zero_of_orderOne`) is stated for them.
  • That the trace of the exponential fails to factorise for an operator as in (8). (8) says the
    SHAPE unit 172's derivation starts from is not forced; whether `trace (exp (t • D))` factorises
    for some other reason is not asked, and nothing here computes a spectrum. The grouping
    `(ι × κ) ⊗ μ`, with the multiplicity split off as its own factor, is not tested; nor is (8)
    carried to `A_F` or to a multiplicity of three.
  • The real structure `J`, the grading `γ` and the KO signs: unit 230 did `J` with every pair of
    factors once; nothing here.
  • `UNLOCK_WATCHLIST` 262 — whether the doubled algebra acts faithfully in the real case — is
    untouched: the test sets here are sets of matrices over one field, and `ℍ` enters only as one.
  • Nothing about the cascade, its `D` (`L40433`), the factor list, or a tag: rung 2 is not
    climbed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `decomposition_fibre` takes `X` commuting with
  every `1 ⊗ b`, `b ∈ S_R`, and `Y` with every `a ⊗ 1`, `a ∈ S_L`;
  `orderOne_iff_commutant_compress` takes `P * P = P`, `P` commuting with every `a ⊗ 1` and every
  `1 ⊗ b`, and `P * D * P = D`; `orderOne_iff_kronSum_of_unique` takes `[Unique μ]`. The rest take
  elements of their types and nothing else. `K` is a field because (2) takes a complement of a
  subspace (`Submodule.exists_isCompl`).

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 23 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: `blk` was taken twice (`CrossPosSemidef`, `CliffordEvenBlock`),
  so the block map is `blockAt`; none of the twenty-three is taken. The nearest statements are
  unit 228's `orderOne_iff` and `orderOne_blockKron`, of which (2) is the commutant form at any
  test sets; unit 168's `orderOne_iff_kron` and unit 228's `orderOne_iff_kron_of_const`, which are
  (8)'s first theorem on `ι × ι` with no multiplicity index; and
  `SpectralTripleBimodule.orderOne_of_commute_D` (a `D` commuting with `π` satisfies order-one),
  in this model the converse of (2) at `X = 0`. Unit 228's `mul_kron_one_apply` and its three
  companions compute single entries on `ι × ι`; `blockAt_mul_kron_one`, `blockAt_kron_one_mul`
  and the two `fibreAt` product lemmas compute whole blocks and fibres.

  `#print axioms` on all 23 declarations below: `blockAt` and `fibreAt` depend on `[Quot.sound]`,
  `blockAt_sub` on `[propext, Quot.sound]`, the other twenty on
  `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Lie.OfAssociative
import OrderOneBlockDiagonal

open Matrix
open scoped Kronecker

namespace OrderOneCommutant

variable {ι κ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Field K]

/-! ## 1. Blocks, and commuting with the right action -/

/-- The `(x, y)` block of a matrix on `ι × κ`: a `κ × κ` matrix. -/
def blockAt (M : Matrix (ι × κ) (ι × κ) K) (x y : ι) : Matrix κ κ K :=
  Matrix.of fun p q => M (x, p) (y, q)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem blockAt_sub (M N : Matrix (ι × κ) (ι × κ) K) (x y : ι) :
    blockAt (M - N) x y = blockAt M x y - blockAt N x y := by
  ext p q; rfl

omit [DecidableEq κ] in
theorem one_kron_mul_apply_blockAt (b : Matrix κ κ K) (M : Matrix (ι × κ) (ι × κ) K) (x p y q) :
    (((1 : Matrix ι ι K) ⊗ₖ b) * M) (x, p) (y, q) = (b * blockAt M x y) p q := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, blockAt,
    Matrix.of_apply]
  rw [Finset.sum_eq_single x]
  · simp
  · intro z _ hz; simp [Ne.symm hz]
  · simp

omit [DecidableEq κ] in
theorem mul_one_kron_apply_blockAt (b : Matrix κ κ K) (M : Matrix (ι × κ) (ι × κ) K) (x p y q) :
    (M * ((1 : Matrix ι ι K) ⊗ₖ b)) (x, p) (y, q) = (blockAt M x y * b) p q := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, blockAt,
    Matrix.of_apply]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz; simp [hz]
  · simp

omit [DecidableEq κ] in
/-- `M` commutes with `1 ⊗ b` iff every block of `M` commutes with `b`. -/
theorem commute_one_kron_iff (b : Matrix κ κ K) (M : Matrix (ι × κ) (ι × κ) K) :
    Commute M ((1 : Matrix ι ι K) ⊗ₖ b) ↔ ∀ x y, Commute (blockAt M x y) b := by
  constructor
  · intro h x y
    ext p q
    have := congrFun (congrFun h.eq (x, p)) (y, q)
    rw [mul_one_kron_apply_blockAt, one_kron_mul_apply_blockAt] at this
    exact this
  · intro h
    ext ⟨x, p⟩ ⟨y, q⟩
    rw [mul_one_kron_apply_blockAt, one_kron_mul_apply_blockAt, (h x y).eq]

omit [DecidableEq ι] in
theorem blockAt_mul_kron_one (a : Matrix ι ι K) (M : Matrix (ι × κ) (ι × κ) K) (x y : ι) :
    blockAt (M * (a ⊗ₖ (1 : Matrix κ κ K))) x y = ∑ z, a z y • blockAt M x z := by
  ext p q
  simp only [blockAt, Matrix.of_apply, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single q]
  · simp [mul_comm]
  · intro s _ hs; simp [hs]
  · simp

omit [DecidableEq ι] in
theorem blockAt_kron_one_mul (a : Matrix ι ι K) (M : Matrix (ι × κ) (ι × κ) K) (x y : ι) :
    blockAt ((a ⊗ₖ (1 : Matrix κ κ K)) * M) x y = ∑ z, a x z • blockAt M z y := by
  ext p q
  simp only [blockAt, Matrix.of_apply, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_eq_single p]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

/-- The blocks of `⁅M, a ⊗ 1⁆` are linear combinations of the blocks of `M`. -/
theorem blockAt_lie_kron_one (a : Matrix ι ι K) (M : Matrix (ι × κ) (ι × κ) K) (x y : ι) :
    blockAt ⁅M, a ⊗ₖ (1 : Matrix κ κ K)⁆ x y =
      ∑ z, a z y • blockAt M x z - ∑ z, a x z • blockAt M z y := by
  rw [Ring.lie_def, blockAt_sub, blockAt_mul_kron_one, blockAt_kron_one_mul]

/-! ## 2. Order-one is the sum of the two commutants -/

/-- **ORDER-ONE IS THE SUM OF THE TWO COMMUTANTS**, over any field, for any sets of test
matrices on the two factors: `⁅⁅M, a ⊗ 1⁆, 1 ⊗ b⁆ = 0` for all `a ∈ S_L`, `b ∈ S_R` iff `M` is an
operator commuting with the right action plus an operator commuting with the left action. -/
theorem orderOne_iff_commutant (S_L : Set (Matrix ι ι K)) (S_R : Set (Matrix κ κ K))
    (M : Matrix (ι × κ) (ι × κ) K) :
    (∀ a ∈ S_L, ∀ b ∈ S_R, ⁅⁅M, a ⊗ₖ (1 : Matrix κ κ K)⁆, (1 : Matrix ι ι K) ⊗ₖ b⁆ = 0) ↔
      ∃ X Y : Matrix (ι × κ) (ι × κ) K, M = X + Y ∧
        (∀ b ∈ S_R, Commute X ((1 : Matrix ι ι K) ⊗ₖ b)) ∧
        (∀ a ∈ S_L, Commute Y (a ⊗ₖ (1 : Matrix κ κ K))) := by
  classical
  constructor
  · intro h
    set C : Submodule K (Matrix κ κ K) := (Subalgebra.centralizer K S_R).toSubmodule with hC
    obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl C
    let X : Matrix (ι × κ) (ι × κ) K :=
      Matrix.of fun xp yq => Submodule.IsCompl.projection hQ (blockAt M xp.1 yq.1) xp.2 yq.2
    have hXblk : ∀ x y, blockAt X x y = Submodule.IsCompl.projection hQ (blockAt M x y) :=
      fun x y => by ext p q; rfl
    have hXmem : ∀ x y, blockAt X x y ∈ C := fun x y => by
      rw [hXblk]; exact Submodule.IsCompl.projection_apply_mem hQ _
    have hYmem : ∀ x y, blockAt (M - X) x y ∈ Q := fun x y => by
      have e := Submodule.IsCompl.projection_add_projection_eq_self hQ (blockAt M x y)
      rw [blockAt_sub, hXblk, sub_eq_iff_eq_add'.mpr e.symm]
      exact Submodule.IsCompl.projection_apply_mem hQ.symm _
    have hcomm : ∀ (N : Matrix (ι × κ) (ι × κ) K), (∀ x y, blockAt N x y ∈ C) →
        ∀ b ∈ S_R, Commute N ((1 : Matrix ι ι K) ⊗ₖ b) := fun N hN b hb => by
      rw [commute_one_kron_iff]
      intro x y
      exact (((Subalgebra.mem_centralizer_iff K).mp (hN x y)) b hb).symm
    refine ⟨X, M - X, by abel, hcomm X hXmem, ?_⟩
    intro a ha
    have hlie : ⁅M - X, a ⊗ₖ (1 : Matrix κ κ K)⁆ = 0 := by
      ext ⟨x, p⟩ ⟨y, q⟩
      have hQm : blockAt ⁅M - X, a ⊗ₖ (1 : Matrix κ κ K)⁆ x y ∈ Q := by
        rw [blockAt_lie_kron_one]
        exact Q.sub_mem (Q.sum_mem fun z _ => Q.smul_mem _ (hYmem x z))
          (Q.sum_mem fun z _ => Q.smul_mem _ (hYmem z y))
      have hCm : blockAt ⁅M - X, a ⊗ₖ (1 : Matrix κ κ K)⁆ x y ∈ C := by
        have hMC : ∀ x y, blockAt ⁅M, a ⊗ₖ (1 : Matrix κ κ K)⁆ x y ∈ C := fun x y => by
          rw [hC, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
          intro b hb
          have := (commute_one_kron_iff b ⁅M, a ⊗ₖ (1 : Matrix κ κ K)⁆).mp
            (by rw [commute_iff_eq, ← sub_eq_zero, ← Ring.lie_def]; exact h a ha b hb) x y
          exact this.eq.symm
        rw [sub_lie, blockAt_sub]
        refine C.sub_mem (hMC x y) ?_
        rw [blockAt_lie_kron_one]
        exact C.sub_mem (C.sum_mem fun z _ => C.smul_mem _ (hXmem x z))
          (C.sum_mem fun z _ => C.smul_mem _ (hXmem z y))
      have h0 : blockAt ⁅M - X, a ⊗ₖ (1 : Matrix κ κ K)⁆ x y = 0 :=
        (Submodule.disjoint_def.mp hQ.disjoint) _ hCm hQm
      have := congrFun (congrFun h0 p) q
      simpa [blockAt] using this
    rw [Ring.lie_def, sub_eq_zero] at hlie
    exact hlie
  · rintro ⟨X, Y, rfl, hX, hY⟩ a ha b hb
    have hab : Commute (a ⊗ₖ (1 : Matrix κ κ K)) ((1 : Matrix ι ι K) ⊗ₖ b) := by
      rw [commute_iff_eq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
      simp
    rw [add_lie, (hY a ha).lie_eq, add_zero, lie_lie, (hX b hb).lie_eq, hab.lie_eq, lie_zero,
      lie_zero, sub_zero]

/-- **The fibre**: the decomposition is unique up to the intersection of the two commutants — if
`X + Y` is one, the others are exactly `(X + Z, Y − Z)` with `Z` commuting with both actions. -/
theorem decomposition_fibre (S_L : Set (Matrix ι ι K)) (S_R : Set (Matrix κ κ K))
    {X Y : Matrix (ι × κ) (ι × κ) K} (hX : ∀ b ∈ S_R, Commute X ((1 : Matrix ι ι K) ⊗ₖ b))
    (hY : ∀ a ∈ S_L, Commute Y (a ⊗ₖ (1 : Matrix κ κ K))) (X' Y' : Matrix (ι × κ) (ι × κ) K) :
    (X' + Y' = X + Y ∧ (∀ b ∈ S_R, Commute X' ((1 : Matrix ι ι K) ⊗ₖ b)) ∧
        (∀ a ∈ S_L, Commute Y' (a ⊗ₖ (1 : Matrix κ κ K)))) ↔
      ∃ Z : Matrix (ι × κ) (ι × κ) K, X' = X + Z ∧ Y' = Y - Z ∧
        (∀ b ∈ S_R, Commute Z ((1 : Matrix ι ι K) ⊗ₖ b)) ∧
        (∀ a ∈ S_L, Commute Z (a ⊗ₖ (1 : Matrix κ κ K))) := by
  constructor
  · rintro ⟨h, hX', hY'⟩
    have hZ : X' - X = Y - Y' := by
      rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
    refine ⟨X' - X, by abel, by rw [hZ, sub_sub_cancel], fun b hb => (hX' b hb).sub_left (hX b hb),
      fun a ha => ?_⟩
    rw [hZ]
    exact (hY a ha).sub_left (hY' a ha)
  · rintro ⟨Z, rfl, rfl, hZR, hZL⟩
    exact ⟨by abel, fun b hb => (hX b hb).add_left (hZR b hb),
      fun a ha => (hY a ha).sub_left (hZL a ha)⟩

/-- Unit 228's `OrderOne` is the instance `S_L = S_R = blockDiagSet β`: the block-diagonal
condition is the sum of the two commutants of the block-diagonal multiplications. -/
theorem orderOne_blockDiag_iff_commutant {ν : Type*} (β : ι → ν) (M : Matrix (ι × ι) (ι × ι) K) :
    OrderOneBlockDiagonal.OrderOne β M ↔ ∃ X Y : Matrix (ι × ι) (ι × ι) K, M = X + Y ∧
      (∀ b ∈ OrderOneBlockDiagonal.blockDiagSet β, Commute X ((1 : Matrix ι ι K) ⊗ₖ b)) ∧
      (∀ a ∈ OrderOneBlockDiagonal.blockDiagSet β, Commute Y (a ⊗ₖ (1 : Matrix ι ι K))) :=
  orderOne_iff_commutant _ _ M

/-! ## 3. Sub-bimodules -/

/-- **Sub-bimodules**: for an idempotent `P` commuting with both actions, an operator living on
`P` (`P D P = D`) satisfies order-one iff it is `X + Y` with both parts living on `P`, `X`
commuting with the right action and `Y` with the left. -/
theorem orderOne_iff_commutant_compress (S_L : Set (Matrix ι ι K)) (S_R : Set (Matrix κ κ K))
    (P : Matrix (ι × κ) (ι × κ) K) (hPP : P * P = P)
    (hPL : ∀ a ∈ S_L, Commute P (a ⊗ₖ (1 : Matrix κ κ K)))
    (hPR : ∀ b ∈ S_R, Commute P ((1 : Matrix ι ι K) ⊗ₖ b))
    (D : Matrix (ι × κ) (ι × κ) K) (hD : P * D * P = D) :
    (∀ a ∈ S_L, ∀ b ∈ S_R, ⁅⁅D, a ⊗ₖ (1 : Matrix κ κ K)⁆, (1 : Matrix ι ι K) ⊗ₖ b⁆ = 0) ↔
      ∃ X Y : Matrix (ι × κ) (ι × κ) K, D = X + Y ∧ P * X * P = X ∧ P * Y * P = Y ∧
        (∀ b ∈ S_R, Commute X ((1 : Matrix ι ι K) ⊗ₖ b)) ∧
        (∀ a ∈ S_L, Commute Y (a ⊗ₖ (1 : Matrix κ κ K))) := by
  rw [orderOne_iff_commutant]
  constructor
  · rintro ⟨X, Y, hXY, hX, hY⟩
    refine ⟨P * X * P, P * Y * P, ?_, ?_, ?_, fun b hb => ?_, fun a ha => ?_⟩
    · calc D = P * D * P := hD.symm
        _ = P * X * P + P * Y * P := by rw [hXY, Matrix.mul_add, Matrix.add_mul]
    · calc P * (P * X * P) * P = (P * P) * X * (P * P) := by simp only [Matrix.mul_assoc]
        _ = P * X * P := by rw [hPP]
    · calc P * (P * Y * P) * P = (P * P) * Y * (P * P) := by simp only [Matrix.mul_assoc]
        _ = P * Y * P := by rw [hPP]
    · exact ((hPR b hb).mul_left (hX b hb)).mul_left (hPR b hb)
    · exact ((hPL a ha).mul_left (hY a ha)).mul_left (hPL a ha)
  · rintro ⟨X, Y, hXY, -, -, hX, hY⟩
    exact ⟨X, Y, hXY, hX, hY⟩

/-! ## 4. The commutant of a full matrix algebra acting with multiplicity -/

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

/-- The `(i, j)` fibre over the multiplicity index of a matrix on `κ × μ`: a `κ × κ` matrix. -/
def fibreAt (N : Matrix (κ × μ) (κ × μ) K) (i j : μ) : Matrix κ κ K :=
  Matrix.of fun p q => N (p, i) (q, j)

omit [DecidableEq κ] in
theorem kron_one_mul_apply_fibreAt (b : Matrix κ κ K) (N : Matrix (κ × μ) (κ × μ) K) (p i q j) :
    ((b ⊗ₖ (1 : Matrix μ μ K)) * N) (p, i) (q, j) = (b * fibreAt N i j) p q := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    fibreAt, Matrix.of_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

omit [DecidableEq κ] in
theorem mul_kron_one_apply_fibreAt (b : Matrix κ κ K) (N : Matrix (κ × μ) (κ × μ) K) (p i q j) :
    (N * (b ⊗ₖ (1 : Matrix μ μ K))) (p, i) (q, j) = (fibreAt N i j * b) p q := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    fibreAt, Matrix.of_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single j]
  · simp
  · intro s _ hs; simp [hs]
  · simp

omit [DecidableEq κ] in
/-- `N` commutes with `b ⊗ 1` iff every fibre of `N` commutes with `b`. -/
theorem commute_kron_one_iff (b : Matrix κ κ K) (N : Matrix (κ × μ) (κ × μ) K) :
    Commute N (b ⊗ₖ (1 : Matrix μ μ K)) ↔ ∀ i j, Commute (fibreAt N i j) b := by
  constructor
  · intro h i j
    ext p q
    have := congrFun (congrFun h.eq (p, i)) (q, j)
    rw [mul_kron_one_apply_fibreAt, kron_one_mul_apply_fibreAt] at this
    exact this
  · intro h
    ext ⟨p, i⟩ ⟨q, j⟩
    rw [mul_kron_one_apply_fibreAt, kron_one_mul_apply_fibreAt, (h i j).eq]

/-- **The commutant of `M_κ` acting with multiplicity**: `N` commutes with every `b ⊗ 1` iff
`N = 1 ⊗ G` — it acts on the multiplicity space alone. -/
theorem commute_all_kron_one_iff (N : Matrix (κ × μ) (κ × μ) K) :
    (∀ b : Matrix κ κ K, Commute N (b ⊗ₖ (1 : Matrix μ μ K))) ↔
      ∃ G : Matrix μ μ K, N = (1 : Matrix κ κ K) ⊗ₖ G := by
  constructor
  · intro h
    have hs : ∀ i j, fibreAt N i j ∈ Set.range (Matrix.scalar κ) := fun i j =>
      Matrix.mem_range_scalar_of_commute_single fun p q _ =>
        ((commute_kron_one_iff _ N).mp (h (single p q 1)) i j).symm
    choose g hg using hs
    refine ⟨Matrix.of g, ?_⟩
    ext ⟨p, i⟩ ⟨q, j⟩
    have := congrFun (congrFun (hg i j) p) q
    simp only [fibreAt, Matrix.of_apply, scalar_apply, diagonal_apply] at this
    simp only [kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply]
    split_ifs at this ⊢ with hpq
    · rw [one_mul]; exact this.symm
    · rw [zero_mul]; exact this.symm
  · rintro ⟨G, rfl⟩ b
    rw [commute_iff_eq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

/-! ## 5. Order-one with multiplicity -/

/-- The part acting on the left space and the multiplicity space together, trivially on `κ`:
`genPart C (x, (p, i)) (y, (q, j)) = [p = q] · C (x, i) (y, j)`. -/
def genPart (C : Matrix (ι × μ) (ι × μ) K) : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K :=
  Matrix.of fun a b => if a.2.1 = b.2.1 then C (a.1, a.2.2) (b.1, b.2.2) else 0

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype μ] [DecidableEq μ] in
theorem blockAt_genPart (C : Matrix (ι × μ) (ι × μ) K) (x y : ι) :
    blockAt (genPart (κ := κ) C) x y =
      (1 : Matrix κ κ K) ⊗ₖ Matrix.of fun i j => C (x, i) (y, j) := by
  ext ⟨p, i⟩ ⟨q, j⟩
  simp only [blockAt, genPart, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp

/-- `X` commutes with the right action of `M_κ` with multiplicity iff it is a `genPart`. -/
theorem commute_genPart_iff (X : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K) :
    (∀ b : Matrix κ κ K,
      Commute X ((1 : Matrix ι ι K) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ K)))) ↔
      ∃ C : Matrix (ι × μ) (ι × μ) K, X = genPart C := by
  constructor
  · intro h
    have hb : ∀ x y, ∃ G : Matrix μ μ K, blockAt X x y = (1 : Matrix κ κ K) ⊗ₖ G := fun x y =>
      (commute_all_kron_one_iff _).mp fun b => (commute_one_kron_iff _ X).mp (h b) x y
    choose G hG using hb
    refine ⟨Matrix.of fun a b => G a.1 b.1 a.2 b.2, ?_⟩
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    have := congrFun (congrFun (hG x y) (p, i)) (q, j)
    simp only [blockAt, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply] at this
    simp only [genPart, Matrix.of_apply]
    split_ifs at this ⊢ <;> simp_all
  · rintro ⟨C, rfl⟩ b
    rw [commute_one_kron_iff]
    intro x y
    rw [blockAt_genPart]
    exact ((commute_all_kron_one_iff _).mpr ⟨_, rfl⟩ b)

/-- **ORDER-ONE WITH MULTIPLICITY.** On `K^ι ⊗ (K^κ ⊗ K^μ)`, with all of `M_ι` acting on the left
and `M_κ` acting on the right with multiplicity `μ` (`b ↦ b ⊗ 1`), an operator satisfies order-one
iff it is `genPart C + 1 ⊗ B`: a part acting on the left space and the multiplicity space
together, plus a part acting on the right space and the multiplicity space together. -/
theorem orderOne_multiplicity_iff (D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K) :
    (∀ (a : Matrix ι ι K) (b : Matrix κ κ K),
      ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) K)⁆,
        (1 : Matrix ι ι K) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ K))⁆ = 0) ↔
      ∃ (C : Matrix (ι × μ) (ι × μ) K) (B : Matrix (κ × μ) (κ × μ) K),
        D = genPart C + (1 : Matrix ι ι K) ⊗ₖ B := by
  have key := orderOne_iff_commutant (Set.univ : Set (Matrix ι ι K))
    (Set.range fun b : Matrix κ κ K => b ⊗ₖ (1 : Matrix μ μ K)) D
  simp only [Set.mem_univ, Set.forall_mem_range, forall_const] at key
  rw [key]
  constructor
  · rintro ⟨X, Y, rfl, hX, hY⟩
    obtain ⟨C, rfl⟩ := (commute_genPart_iff X).mp hX
    obtain ⟨B, rfl⟩ := (commute_all_kron_one_iff Y).mp hY
    exact ⟨C, B, rfl⟩
  · rintro ⟨C, B, rfl⟩
    exact ⟨genPart C, (1 : Matrix ι ι K) ⊗ₖ B, rfl, (commute_genPart_iff _).mpr ⟨C, rfl⟩,
      (commute_all_kron_one_iff _).mpr ⟨B, rfl⟩⟩

/-! ## 6. The tensor-sum shape is a multiplicity-one fact -/

/-- **At multiplicity one the tensor-sum shape is forced**, at any sizes: with `μ` a one-point
type, order-one holds iff `D = C ⊗ 1 + 1 ⊗ B`. -/
theorem orderOne_iff_kronSum_of_unique [Unique μ] (D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K) :
    (∀ (a : Matrix ι ι K) (b : Matrix κ κ K),
      ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) K)⁆,
        (1 : Matrix ι ι K) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ K))⁆ = 0) ↔
      ∃ (C : Matrix ι ι K) (B : Matrix (κ × μ) (κ × μ) K),
        D = C ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) K) + (1 : Matrix ι ι K) ⊗ₖ B := by
  rw [orderOne_multiplicity_iff]
  constructor
  · rintro ⟨C, B, rfl⟩
    refine ⟨Matrix.of fun x y => C (x, default) (y, default), B, ?_⟩
    congr 1
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    rw [Subsingleton.elim i default, Subsingleton.elim j default]
    simp only [genPart, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq,
      and_true]
    split_ifs <;> simp
  · rintro ⟨C, B, rfl⟩
    refine ⟨Matrix.of fun a b => C a.1 b.1, B, ?_⟩
    congr 1
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    rw [Subsingleton.elim i j]
    simp only [genPart, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq,
      and_true]
    split_ifs <;> simp


/-- **ORDER-ONE DOES NOT FORCE THE TENSOR-SUM SHAPE ONCE A PIECE REPEATS.** With
`ι = κ = μ = Fin 2`, `genPart (single (0, 0) (0, 0) 1) + 1 ⊗ single (0, 0) (0, 1) 1` satisfies
order-one, and it is neither `C ⊗ 1 + 1 ⊗ B` (an operator on the left factor plus one on the
right factor with its multiplicity) nor `genPart C + 1 ⊗ (B ⊗ 1)` (an operator on the left factor
with the multiplicity plus one on the right factor alone). -/
theorem exists_orderOne_not_kronSum :
    ∃ D : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) K,
      (∀ a b : Matrix (Fin 2) (Fin 2) K,
        ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K)⁆,
          (1 : Matrix (Fin 2) (Fin 2) K) ⊗ₖ (b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K))⁆ = 0) ∧
      (∀ (C : Matrix (Fin 2) (Fin 2) K) (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K),
        D ≠ C ⊗ₖ 1 + 1 ⊗ₖ B) ∧
      (∀ (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) K) (B : Matrix (Fin 2) (Fin 2) K),
        D ≠ genPart C + 1 ⊗ₖ (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) K))) := by
  refine ⟨genPart (single (0, 0) (0, 0) 1) + 1 ⊗ₖ single (0, 0) (0, 1) 1,
    (orderOne_multiplicity_iff _).mpr ⟨_, _, rfl⟩, fun C B h => ?_, fun C B h => ?_⟩
  · have e1 := congrFun (congrFun h (0, (0, 0))) (0, (0, 0))
    have e2 := congrFun (congrFun h (1, (0, 0))) (1, (0, 0))
    have e3 := congrFun (congrFun h (0, (0, 1))) (0, (0, 1))
    have e4 := congrFun (congrFun h (1, (0, 1))) (1, (0, 1))
    simp only [genPart, Fin.isValue, single_apply, Prod.mk.injEq, add_apply, of_apply, ↓reduceIte,
      and_self, kroneckerMap_apply, one_apply_eq, one_ne_zero, and_false, mul_zero, add_zero,
      mul_one, one_mul, zero_ne_one, and_true] at e1 e2 e3 e4
    have : (1 : K) = 0 := by linear_combination e1 - e2 - e3 + e4
    exact one_ne_zero this
  · have e1 := congrFun (congrFun h (0, (0, 0))) (0, (0, 1))
    have e2 := congrFun (congrFun h (0, (1, 0))) (0, (1, 1))
    simp only [genPart, Fin.isValue, single_apply, Prod.mk.injEq, add_apply, of_apply, ↓reduceIte,
      and_self, zero_ne_one, and_false, kroneckerMap_apply, one_apply_eq, mul_one, zero_add, ne_eq,
      not_false_eq_true, one_apply_ne, mul_zero, add_zero, and_true] at e1 e2
    have : (1 : K) = 0 := by linear_combination e1 - e2
    exact one_ne_zero this

end OrderOneCommutant
