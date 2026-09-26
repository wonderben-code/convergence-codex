/-
  OrderOneBlockDiagonal.lean — the order-one condition for a finite product of matrix algebras
  sitting block-diagonally in `M_N`, with `M_N` as the bimodule (the regular bimodule of `M_N`,
  restricted to the product): tested against the block-diagonal matrices on both sides, an
  operator satisfies it iff it is a left multiplication that may depend on the right block plus a
  right multiplication that may depend on the left block, and the pair of multiplications is
  determined up to block-scalars moved between them. Over any commutative ring.

  SPINE L6 / `WALLS` §W9 rung 2, second clause — *what the order-one condition does to the pair
  `(A, A°)` acting on `H`* — carried from the regular bimodule of ONE matrix factor (unit 168) to
  a product of matrix factors with every pair of factors occurring once. Hardening unit 228,
  26 September 2026.

  WHY. Unit 168 solved order-one on the regular bimodule of `Mₙ(ℂ)` — `D = C ⊗ 1 + 1 ⊗ B`
  (`OrderOneRegularBimodule.orderOne_iff_kron`) — and its NOT list says *"Anything off the
  REGULAR bimodule … No factor list is cut; two factors … — none of it."* SPINE's Caesar order
  puts rung 2 first (*"still the highest cascade on the spine"*), and `WALLS` §W9.1 says *"What
  order-one forces on a general `(A_F, H_F)` is still open."* CCM's `A_F = ℂ ⊕ ℍ ⊕ M₃(ℂ)` is a
  product of matrix algebras, and a bimodule of a product of COMPLEX matrix algebras is a sum of
  pieces `ℂ^{nᵢ} ⊗ ℂ^{nⱼ}`. A product `∏ᵢ M_{nᵢ}` is the
  subalgebra of block-diagonal matrices in `M_N`, `N = Σ nᵢ`, and the regular bimodule of `M_N`
  restricted to it is the sum of all the pieces, each once. So for a product, with every pair of
  factors present once, the question is unit 168's with the test algebra shrunk to the
  block-diagonal matrices, and this file answers it.

  WHAT IS PROVED (`R` any commutative ring, `ι` any finite type, the blocks the fibres of any
  `β : ι → κ`).
  (1) `blockDiagSet β`, the block-diagonal matrices, and `single_mem_blockDiagSet`; the entries of
      the four products with `a ⊗ 1` and `1 ⊗ b` (`mul_kron_one_apply`, `kron_one_mul_apply`,
      `mul_one_kron_apply`, `one_kron_mul_apply`).
  (2) `OrderOne β M`: `⁅⁅M, a ⊗ 1⁆, 1 ⊗ b⁆ = 0` for all block-diagonal `a` and `b`.
      `entry_of_orderOne` reads it at matrix units inside blocks; its four consequences:
      **`offdiag_offdiag_eq_zero`** — an entry joining two different points on the left AND two
      different points on the right vanishes, whatever the blocks; `offdiag_diag_eq` and
      `diag_offdiag_eq` — an entry joining two points on one side is constant as the diagonal
      point on the other side moves within its block; `diag_diag_sub_eq` — the difference of two
      diagonal entries whose left points share a block does not change as the right point moves
      within its block.
  (3) **`exists_blockKron_of_orderOne`**: order-one forces
      `M (x, p) (y, q) = [p = q] · C (β p) x y + [x = y] · B (β x) p q` (`blockKron`), with `C`
      and `B` read off `M` at one point of each block (`Function.invFun β`).
  (4) The converse: `blockKron_eq` splits `blockKron` into `leftMulPart` and `rightMulPart`;
      `lie_leftMulPart` (its bracket with `a ⊗ 1` is the left part of the brackets `⁅C j, a⁆`),
      `lie_leftMulPart_one_kron` and `lie_rightMulPart_kron_one` (each part commutes with the
      block-diagonal multiplications on the other side); so **`orderOne_blockKron`**, and
      **`orderOne_iff`**.
  (5) **`entry_eq_zero_of_orderOne`**: no entry of an order-one operator joins two different left
      blocks and two different right blocks — in the language of WHY, the operator maps the piece
      `ℂ^{nₖ} ⊗ ℂ^{nₗ}` into `ℂ^{nᵢ} ⊗ ℂ^{nⱼ}` only when `i = k` or `j = l`. **`blockKron_const`**:
      with one block, `blockKron` is `C ⊗ 1 + 1 ⊗ B`; and **`orderOne_iff_kron_of_const`** derives
      unit 168's `orderOne_iff_kron` from `orderOne_iff`, for every finite `ι` (unit 168 takes
      `Fin n`, `n ≠ 0`).
  (6) Uniqueness. `blockKron_add`, `blockKron_sub`, `smul_blockKron`: `blockKron` is linear in the
      pair. **`blockKron_eq_zero_iff`**: it vanishes exactly when `C` is diagonal with entries
      `f (β p) (β x)` depending only on the two blocks and `B` carries their negatives; so
      **`blockKron_eq_blockKron_iff`**: `(C, B)` is determined exactly up to adding `f (β p) (β x)`
      to the diagonal of `C` and subtracting it from the diagonal of `B`, at the labels `β` takes —
      the only ones `blockKron` reads. **`kron_eq_kron_iff`**: with one block and `ι` nonempty,
      `C ⊗ 1 + 1 ⊗ B` determines `(C, B)` exactly up to `(C + c • 1, B − c • 1)`, which unit 168's
      NOT list left unstated.

  NOT PROVED, said exactly.
  • The identifications in WHY: that the block-diagonal matrices form an algebra isomorphic to
    `∏ᵢ M_{nᵢ}`, and that the regular bimodule restricted to it is `⊕ ℂ^{nᵢ} ⊗ ℂ^{nⱼ}`, are not
    written; the theorem is stated on `ι × ι`.
  • Multiplicities and sub-bimodules. CCM's `H_F` contains some pieces several times (the
    generations) and others not at all; here every piece occurs exactly once. The statement for a
    sum with multiplicities, and for the compression to a sub-bimodule, is not written.
    ⚠ 26 September 2026 (hardening unit 232, `paper_f/OrderOneCommutant.lean`): written
    there in commutant form, for any sets of test matrices over any field — order-one iff
    `D = X + Y`, `X` commuting with the right action and `Y` with the left
    (`OrderOneCommutant.orderOne_iff_commutant`), and on a sub-bimodule with both parts on it
    (`orderOne_iff_commutant_compress`); computed for full matrix algebras with a multiplicity on
    one side (`orderOne_multiplicity_iff`), where at multiplicity two not every solution is
    `C ⊗ 1 + 1 ⊗ B` (`exists_orderOne_not_kronSum`). Block-diagonal test sets with
    multiplicities — an analogue of `blockKron` — are not computed, and that `H_F` is such a
    compression is not written.
  • The real structure `J`, the grading `γ` and the KO signs: units 169 and 170 did them for one
    factor of size two; nothing here.
    ⚠ 26 September 2026 (hardening unit 230, `paper_f/OrderOneRealBlock.lean`): `J` is
    done there — order-one and `J`-invariance hold iff `M = blockKron β A Ā`
    (`OrderOneRealBlock.orderOne_exchConj_iff`); `γ` and the KO signs are not.
  • Quaternionic factors and the real case (`UNLOCK_WATCHLIST` 262): the factors here are matrix
    algebras over one commutative ring.
    ⚠ 26 September 2026 (hardening unit 232, `paper_f/OrderOneCommutant.lean`): in
    part — the test sets there are any sets of matrices over any field, `ℍ` inside `M₂(ℂ)` among
    them, and order-one against them is the sum of the two commutants
    (`OrderOneCommutant.orderOne_iff_commutant`); the commutants for `ℍ` are not computed, and
    entry 262's faithfulness question is untouched.
    ⚠ 26 September 2026 (hardening unit 237, `paper_f/OrderOneQuaternion.lean`): for
    `ℍ` inside `M₂(ℂ)` acting on `ℂ² ⊗ ℂ²` they are `M₂(ℂ)`'s — order-one against `ℍ` holds iff
    `M = C ⊗ 1 + 1 ⊗ B` (`OrderOneQuaternion.orderOne_quat_iff`); `ℍ` as one block of a
    product, and entry 262, are not.
  • Nothing about the cascade, the factor list, or a tag: rung 2 is not climbed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `single_mem_blockDiagSet` takes `β k = β l`.
  `entry_of_orderOne`, the four consequences in (2), `exists_blockKron_of_orderOne` and
  `entry_eq_zero_of_orderOne` take `OrderOne β M`, and besides it: `entry_of_orderOne` takes
  `β k = β l` and `β r = β q`; `offdiag_offdiag_eq_zero` takes `i ≠ k` and `p ≠ q`;
  `offdiag_diag_eq` takes `i ≠ k` and `β p = β q`; `diag_offdiag_eq` takes `β i = β j` and
  `p ≠ q`; `diag_diag_sub_eq` takes `β i = β j` and `β p = β q`; `entry_eq_zero_of_orderOne` takes
  `β x ≠ β y` and `β p ≠ β q`. `lie_leftMulPart_one_kron` takes `b ∈ blockDiagSet β` and
  `lie_rightMulPart_kron_one` takes `a ∈ blockDiagSet β`; `kron_eq_kron_iff` takes `[Nonempty ι]`.
  The rest take elements of their types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 31 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: `leftPart` was taken (`CycleRestriction`), so the two parts are `leftMulPart` and
  `rightMulPart`. They were then run against Mathlib's declarations, because the file opens
  `Matrix`: the set was first called `blockDiag`, which is Mathlib's `Matrix.blockDiag` (one
  diagonal block of a block matrix) and is ambiguous in any file that opens both namespaces, so it
  is `blockDiagSet`; no other name occurs there. Unit 168's four entry lemmas
  (`OrderOneRegularBimodule.mul_single_kron_one_apply` and its siblings, for `Fin n`) are not
  re-declared — `entry_of_orderOne` reads the matrix units through the general products of (1) — and
  unit 168's `orderOne_entry` and its four consequences have their counterparts here under other
  names. The nearest statement is unit 168's `orderOne_iff_kron`, which `orderOne_iff_kron_of_const`
  derives from this file's `orderOne_iff`; unit 168's plan — read the condition at matrix units,
  then write `C` and `B` down — is followed.

  `#print axioms` on all 31 declarations below: each is `[propext, Classical.choice, Quot.sound]`
  or a subset of it.
-/
import OrderOneRegularBimodule

open Matrix
open scoped Kronecker

namespace OrderOneBlockDiagonal

variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-! ## 1. Block-diagonal matrices, and the entries of the four products -/

/-- The matrices that are block-diagonal for the labelling `β`: no entry joins two blocks. -/
def blockDiagSet (β : ι → κ) : Set (Matrix ι ι R) := {a | ∀ x y, β x ≠ β y → a x y = 0}

omit [Fintype ι] in
theorem single_mem_blockDiagSet {β : ι → κ} {k l : ι} (h : β k = β l) :
    single k l (1 : R) ∈ blockDiagSet β := by
  intro x y hxy
  rw [Matrix.single_apply]
  split_ifs with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact absurd h hxy
  · rfl

theorem mul_kron_one_apply (M : Matrix (ι × ι) (ι × ι) R) (a : Matrix ι ι R) (x p y q : ι) :
    (M * (a ⊗ₖ (1 : Matrix ι ι R))) (x, p) (y, q) = ∑ z, M (x, p) (z, q) * a z y := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [mul_ite, Finset.sum_ite_eq']

theorem kron_one_mul_apply (M : Matrix (ι × ι) (ι × ι) R) (a : Matrix ι ι R) (x p y q : ι) :
    ((a ⊗ₖ (1 : Matrix ι ι R)) * M) (x, p) (y, q) = ∑ z, a x z * M (z, p) (y, q) := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [ite_mul, Finset.sum_ite_eq]

theorem mul_one_kron_apply (M : Matrix (ι × ι) (ι × ι) R) (b : Matrix ι ι R) (x p y q : ι) :
    (M * ((1 : Matrix ι ι R) ⊗ₖ b)) (x, p) (y, q) = ∑ s, M (x, p) (y, s) * b s q := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [mul_ite, ite_mul, Finset.sum_ite_eq']

theorem one_kron_mul_apply (M : Matrix (ι × ι) (ι × ι) R) (b : Matrix ι ι R) (x p y q : ι) :
    (((1 : Matrix ι ι R) ⊗ₖ b) * M) (x, p) (y, q) = ∑ s, b p s * M (x, s) (y, q) := by
  simp only [Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp [ite_mul, Finset.sum_ite_eq]

/-! ## 2. Order-one against the block-diagonal matrices, entrywise -/

/-- The order-one condition, tested only against block-diagonal matrices on both sides. -/
def OrderOne (β : ι → κ) (M : Matrix (ι × ι) (ι × ι) R) : Prop :=
  ∀ a ∈ blockDiagSet (R := R) β, ∀ b ∈ blockDiagSet (R := R) β,
    ⁅⁅M, a ⊗ₖ (1 : Matrix ι ι R)⁆, (1 : Matrix ι ι R) ⊗ₖ b⁆ = 0

theorem entry_of_orderOne {β : ι → κ} {M : Matrix (ι × ι) (ι × ι) R} (h : OrderOne β M)
    (i p j q k l r : ι) (hkl : β k = β l) (hrq : β r = β q) :
    (if l = j then M (i, p) (k, r) else 0) - (if k = i then M (l, p) (j, r) else 0)
      - ((if l = j then (if r = p then M (i, q) (k, q) else 0) else 0)
        - (if k = i then (if r = p then M (l, q) (j, q) else 0) else 0)) = 0 := by
  have := congrFun (congrFun (h _ (single_mem_blockDiagSet hkl) _ (single_mem_blockDiagSet hrq))
    (i, p)) (j, q)
  simp only [Ring.lie_def, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply, Matrix.zero_apply,
    mul_one_kron_apply, one_kron_mul_apply, mul_kron_one_apply, kron_one_mul_apply,
    Matrix.single_apply] at this
  simpa [Finset.sum_ite, Finset.filter_eq', Finset.filter_eq, ite_and, mul_ite, ite_mul] using this

/-- **Every entry joining two different points on both sides vanishes.** -/
theorem offdiag_offdiag_eq_zero {β : ι → κ} {M : Matrix (ι × ι) (ι × ι) R} (h : OrderOne β M)
    {i k p q : ι} (hik : i ≠ k) (hpq : p ≠ q) : M (i, p) (k, q) = 0 := by
  have e := entry_of_orderOne h i p k q k k q rfl rfl
  simp only [↓reduceIte, hik.symm, sub_zero, hpq.symm, sub_self] at e
  exact e

theorem offdiag_diag_eq {β : ι → κ} {M : Matrix (ι × ι) (ι × ι) R} (h : OrderOne β M)
    {i k : ι} (hik : i ≠ k) {p q : ι} (hpq : β p = β q) : M (i, p) (k, p) = M (i, q) (k, q) := by
  have e := entry_of_orderOne h i p k q k k p rfl hpq
  simp only [↓reduceIte, hik.symm, sub_zero] at e
  exact sub_eq_zero.mp e

theorem diag_offdiag_eq {β : ι → κ} {M : Matrix (ι × ι) (ι × ι) R} (h : OrderOne β M)
    {i j : ι} (hij : β i = β j) {p q : ι} (hpq : p ≠ q) : M (i, p) (i, q) = M (j, p) (j, q) := by
  have e := entry_of_orderOne h i p j q i j q hij rfl
  simp only [↓reduceIte, hpq.symm, sub_self, sub_zero] at e
  exact sub_eq_zero.mp e

theorem diag_diag_sub_eq {β : ι → κ} {M : Matrix (ι × ι) (ι × ι) R} (h : OrderOne β M)
    {i j : ι} (hij : β i = β j) {p q : ι} (hpq : β p = β q) :
    M (i, p) (i, p) - M (j, p) (j, p) = M (i, q) (i, q) - M (j, q) (j, q) := by
  have e := entry_of_orderOne h i p j q i j p hij hpq
  simp only [↓reduceIte] at e
  exact sub_eq_zero.mp e

/-! ## 3. The classification -/

/-- The shape order-one forces: a left multiplication that may depend on the right block, plus a
right multiplication that may depend on the left block. -/
def blockKron (β : ι → κ) (C B : κ → Matrix ι ι R) : Matrix (ι × ι) (ι × ι) R :=
  Matrix.of fun xp yq => (if xp.2 = yq.2 then C (β xp.2) xp.1 yq.1 else 0)
    + (if xp.1 = yq.1 then B (β xp.1) xp.2 yq.2 else 0)

/-- **THE CLASSIFICATION**: order-one against the block-diagonal matrices forces `blockKron`. -/
theorem exists_blockKron_of_orderOne {β : ι → κ} {M : Matrix (ι × ι) (ι × ι) R}
    (h : OrderOne β M) : ∃ C B : κ → Matrix ι ι R, M = blockKron β C B := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, 0, by ext ⟨x, _⟩ _; exact isEmptyElim x⟩
  classical
  have hr : ∀ x, β x = β (Function.invFun β (β x)) := fun x => (Function.invFun_eq ⟨x, rfl⟩).symm
  refine ⟨fun j => Matrix.of fun x y => M (x, Function.invFun β j) (y, Function.invFun β j)
      - (if x = y then M (Function.invFun β (β x), Function.invFun β j)
          (Function.invFun β (β x), Function.invFun β j) else 0),
    fun i => Matrix.of fun p q => M (Function.invFun β i, p) (Function.invFun β i, q), ?_⟩
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [blockKron, Matrix.of_apply]
  by_cases hxy : x = y
  · subst hxy
    by_cases hpq : p = q
    · subst hpq
      simp only [if_true]
      have e := diag_diag_sub_eq h (hr x) (hr p)
      linear_combination e
    · simp only [if_true, hpq, if_false, zero_add]
      exact diag_offdiag_eq h (hr x) hpq
  · by_cases hpq : p = q
    · subst hpq
      simp only [if_true, hxy, if_false, sub_zero, add_zero]
      exact offdiag_diag_eq h hxy (hr p)
    · simp only [hxy, hpq, if_false, add_zero]
      exact offdiag_offdiag_eq_zero h hxy hpq

/-! ## 4. The converse -/

/-- The left-multiplication part of `blockKron`. -/
def leftMulPart (β : ι → κ) (C : κ → Matrix ι ι R) : Matrix (ι × ι) (ι × ι) R :=
  Matrix.of fun xp yq => if xp.2 = yq.2 then C (β xp.2) xp.1 yq.1 else 0

/-- The right-multiplication part of `blockKron`. -/
def rightMulPart (β : ι → κ) (B : κ → Matrix ι ι R) : Matrix (ι × ι) (ι × ι) R :=
  Matrix.of fun xp yq => if xp.1 = yq.1 then B (β xp.1) xp.2 yq.2 else 0

omit [Fintype ι] in
theorem blockKron_eq (β : ι → κ) (C B : κ → Matrix ι ι R) :
    blockKron β C B = leftMulPart β C + rightMulPart β B := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp [blockKron, leftMulPart, rightMulPart]

/-- The left part's bracket with a left multiplication is the left part of the brackets. -/
theorem lie_leftMulPart (β : ι → κ) (C : κ → Matrix ι ι R) (a : Matrix ι ι R) :
    ⁅leftMulPart β C, a ⊗ₖ (1 : Matrix ι ι R)⁆ = leftMulPart β fun j => ⁅C j, a⁆ := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [Ring.lie_def, Matrix.sub_apply, mul_kron_one_apply, kron_one_mul_apply, leftMulPart,
    Matrix.of_apply]
  by_cases hpq : p = q
  · subst hpq
    simp [Matrix.mul_apply]
  · simp [hpq]

/-- The left part commutes with every block-diagonal right multiplication. -/
theorem lie_leftMulPart_one_kron {β : ι → κ} (C : κ → Matrix ι ι R) {b : Matrix ι ι R}
    (hb : b ∈ blockDiagSet β) : ⁅leftMulPart β C, (1 : Matrix ι ι R) ⊗ₖ b⁆ = 0 := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [Ring.lie_def, Matrix.sub_apply, mul_one_kron_apply, one_kron_mul_apply, leftMulPart,
    Matrix.of_apply, Matrix.zero_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hpq : β p = β q
  · rw [hpq, mul_comm, sub_self]
  · rw [hb p q hpq, mul_zero, zero_mul, sub_self]

/-- The right part commutes with every block-diagonal left multiplication. -/
theorem lie_rightMulPart_kron_one {β : ι → κ} (B : κ → Matrix ι ι R) {a : Matrix ι ι R}
    (ha : a ∈ blockDiagSet β) : ⁅rightMulPart β B, a ⊗ₖ (1 : Matrix ι ι R)⁆ = 0 := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [Ring.lie_def, Matrix.sub_apply, mul_kron_one_apply, kron_one_mul_apply, rightMulPart,
    Matrix.of_apply, Matrix.zero_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hxy : β x = β y
  · rw [hxy, mul_comm, sub_self]
  · rw [ha x y hxy, mul_zero, zero_mul, sub_self]

/-- **The converse**: every `blockKron` satisfies order-one against the block-diagonal matrices. -/
theorem orderOne_blockKron (β : ι → κ) (C B : κ → Matrix ι ι R) :
    OrderOne β (blockKron β C B) := by
  intro a ha b hb
  have e : ⁅leftMulPart β C + rightMulPart β B, a ⊗ₖ (1 : Matrix ι ι R)⁆ =
      ⁅leftMulPart β C, a ⊗ₖ (1 : Matrix ι ι R)⁆ + ⁅rightMulPart β B, a ⊗ₖ (1 : Matrix ι ι R)⁆ := by
    simp only [Ring.lie_def, Matrix.add_mul, Matrix.mul_add]
    abel
  rw [blockKron_eq, e, lie_leftMulPart, lie_rightMulPart_kron_one B ha, add_zero,
    lie_leftMulPart_one_kron _ hb]

/-- **ORDER-ONE AGAINST THE BLOCK-DIAGONAL MATRICES, CHARACTERISED.** -/
theorem orderOne_iff (β : ι → κ) (M : Matrix (ι × ι) (ι × ι) R) :
    OrderOne β M ↔ ∃ C B : κ → Matrix ι ι R, M = blockKron β C B :=
  ⟨exists_blockKron_of_orderOne, fun ⟨C, B, hM⟩ => hM ▸ orderOne_blockKron β C B⟩

/-- **The support**: an operator satisfying order-one has no entry joining two different points of
the left factor AND two different points of the right one — in particular, no block joining two
different left blocks and two different right blocks. -/
theorem entry_eq_zero_of_orderOne {β : ι → κ} {M : Matrix (ι × ι) (ι × ι) R} (h : OrderOne β M)
    {x y p q : ι} (hxy : β x ≠ β y) (hpq : β p ≠ β q) : M (x, p) (y, q) = 0 :=
  offdiag_offdiag_eq_zero h (fun e => hxy (e ▸ rfl)) (fun e => hpq (e ▸ rfl))

omit [Fintype ι] in
/-- **One block is unit 168's theorem**: for a constant labelling, `blockKron` is
`C ⊗ 1 + 1 ⊗ B`. -/
theorem blockKron_const (C B : Matrix ι ι R) :
    blockKron (fun _ : ι => ()) (fun _ => C) (fun _ => B) =
      C ⊗ₖ (1 : Matrix ι ι R) + (1 : Matrix ι ι R) ⊗ₖ B := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp [blockKron, kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul, add_comm]

/-- **Unit 168's theorem, recovered from `orderOne_iff`**, for every finite `ι`
(`OrderOneRegularBimodule` takes `Fin n` with `n ≠ 0`): with one block, order-one against all
matrices holds exactly for `C ⊗ 1 + 1 ⊗ B`. -/
theorem orderOne_iff_kron_of_const (M : Matrix (ι × ι) (ι × ι) R) :
    (∀ a b : Matrix ι ι R, ⁅⁅M, a ⊗ₖ (1 : Matrix ι ι R)⁆, (1 : Matrix ι ι R) ⊗ₖ b⁆ = 0) ↔
      ∃ C B : Matrix ι ι R, M = C ⊗ₖ (1 : Matrix ι ι R) + (1 : Matrix ι ι R) ⊗ₖ B := by
  have hall : ∀ a : Matrix ι ι R, a ∈ blockDiagSet (fun _ : ι => ()) := fun _ _ _ h => absurd rfl h
  constructor
  · intro h
    obtain ⟨C, B, rfl⟩ := exists_blockKron_of_orderOne (β := fun _ : ι => ()) fun a _ b _ => h a b
    exact ⟨C (), B (), blockKron_const (C ()) (B ())⟩
  · rintro ⟨C, B, rfl⟩ a b
    rw [← blockKron_const]
    exact orderOne_blockKron _ _ _ a (hall a) b (hall b)

/-! ## 6. Uniqueness: what `(C, B)` is determined up to -/

omit [Fintype ι] in
theorem blockKron_add (β : ι → κ) (C B C' B' : κ → Matrix ι ι R) :
    blockKron β C B + blockKron β C' B' = blockKron β (C + C') (B + B') := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [blockKron, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> ring

omit [Fintype ι] in
theorem blockKron_sub (β : ι → κ) (C B C' B' : κ → Matrix ι ι R) :
    blockKron β C B - blockKron β C' B' = blockKron β (C - C') (B - B') := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [blockKron, Matrix.sub_apply, Matrix.of_apply, Pi.sub_apply]
  split_ifs <;> ring

omit [Fintype ι] in
theorem smul_blockKron (β : ι → κ) (c : R) (C B : κ → Matrix ι ι R) :
    c • blockKron β C B = blockKron β (c • C) (c • B) := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [blockKron, Matrix.smul_apply, Matrix.of_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

omit [Fintype ι] in
/-- **The kernel of `blockKron`**: it vanishes exactly when `C` is diagonal with entries depending
only on the two blocks, and `B` carries their negatives — block-scalars moved from one part to
the other. Stated at the labels `β` takes, the only ones `blockKron` reads. -/
theorem blockKron_eq_zero_iff (β : ι → κ) (C B : κ → Matrix ι ι R) :
    blockKron β C B = 0 ↔ ∃ f : κ → κ → R,
      (∀ x y p, C (β p) x y = if x = y then f (β p) (β x) else 0) ∧
        ∀ x p q, B (β x) p q = if p = q then -f (β p) (β x) else 0 := by
  classical
  constructor
  · intro h
    have e : ∀ x p y q, (if p = q then C (β p) x y else 0) + (if x = y then B (β x) p q else 0)
        = 0 := fun x p y q => by
      simpa [blockKron] using congrFun (congrFun h (x, p)) (y, q)
    have hC : ∀ x y p, x ≠ y → C (β p) x y = 0 := fun x y p hxy => by
      simpa [hxy] using e x p y p
    have hB : ∀ x p q, p ≠ q → B (β x) p q = 0 := fun x p q hpq => by
      simpa [hpq] using e x p x q
    have hd : ∀ x p, C (β p) x x = -B (β x) p p := fun x p => by
      have := e x p x p
      simp only [if_true] at this
      exact eq_neg_of_add_eq_zero_left this
    refine ⟨fun j k => if h : ∃ x, β x = k then C j h.choose h.choose else 0, ?_, ?_⟩
    · intro x y p
      by_cases hxy : x = y
      · subst hxy
        have hex : ∃ z, β z = β x := ⟨x, rfl⟩
        rw [if_pos rfl]
        dsimp only
        rw [dif_pos hex, hd, hd, hex.choose_spec]
      · rw [if_neg hxy, hC x y p hxy]
    · intro x p q
      by_cases hpq : p = q
      · subst hpq
        have hex : ∃ z, β z = β x := ⟨x, rfl⟩
        rw [if_pos rfl]
        dsimp only
        rw [dif_pos hex, hd, neg_neg, hex.choose_spec]
      · rw [if_neg hpq, hB x p q hpq]
  · rintro ⟨f, hC, hB⟩
    ext ⟨x, p⟩ ⟨y, q⟩
    simp only [blockKron, Matrix.of_apply, Matrix.zero_apply]
    by_cases hxy : x = y <;> by_cases hpq : p = q
    · subst hxy; subst hpq
      rw [if_pos rfl, if_pos rfl, hC, hB, if_pos rfl, if_pos rfl, add_neg_cancel]
    · subst hxy
      rw [if_neg hpq, if_pos rfl, hB, if_neg hpq, zero_add]
    · subst hpq
      rw [if_pos rfl, if_neg hxy, hC, if_neg hxy, add_zero]
    · rw [if_neg hpq, if_neg hxy, add_zero]

omit [Fintype ι] in
/-- **UNIQUENESS**: two pairs give the same operator exactly when they differ by block-scalars
`f j k` added to the diagonal of `C` and taken from the diagonal of `B`. -/
theorem blockKron_eq_blockKron_iff (β : ι → κ) (C B C' B' : κ → Matrix ι ι R) :
    blockKron β C' B' = blockKron β C B ↔ ∃ f : κ → κ → R,
      (∀ x y p, C' (β p) x y = C (β p) x y + if x = y then f (β p) (β x) else 0) ∧
        ∀ x p q, B' (β x) p q = B (β x) p q - if p = q then f (β p) (β x) else 0 := by
  rw [← sub_eq_zero, blockKron_sub, blockKron_eq_zero_iff]
  refine exists_congr fun f => and_congr
    (forall_congr' fun x => forall_congr' fun y => forall_congr' fun p => ?_)
    (forall_congr' fun x => forall_congr' fun p => forall_congr' fun q => ?_)
  · simp only [Pi.sub_apply, Matrix.sub_apply]
    exact sub_eq_iff_eq_add'
  · simp only [Pi.sub_apply, Matrix.sub_apply]
    split_ifs <;> constructor <;> intro h <;> linear_combination h

omit [Fintype ι] in
/-- **Unit 168's pair, determined**: with one block and `ι` nonempty, `C ⊗ 1 + 1 ⊗ B` determines
`(C, B)` exactly up to `(C + c • 1, B − c • 1)`. -/
theorem kron_eq_kron_iff [Nonempty ι] (C B C' B' : Matrix ι ι R) :
    C' ⊗ₖ (1 : Matrix ι ι R) + (1 : Matrix ι ι R) ⊗ₖ B' =
        C ⊗ₖ (1 : Matrix ι ι R) + (1 : Matrix ι ι R) ⊗ₖ B ↔
      ∃ c : R, C' = C + c • (1 : Matrix ι ι R) ∧ B' = B - c • (1 : Matrix ι ι R) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rw [← blockKron_const, ← blockKron_const, blockKron_eq_blockKron_iff]
  constructor
  · rintro ⟨f, hC, hB⟩
    refine ⟨f () (), ?_, ?_⟩
    · ext x y
      simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply] using hC x y i₀
    · ext p q
      simpa [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] using hB i₀ p q
  · rintro ⟨c, rfl, rfl⟩
    exact ⟨fun _ _ => c, fun x y _ => by simp [Matrix.one_apply],
      fun _ p q => by simp [Matrix.one_apply]⟩

end OrderOneBlockDiagonal
