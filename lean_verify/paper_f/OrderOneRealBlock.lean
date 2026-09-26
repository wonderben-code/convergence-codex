/-
  OrderOneRealBlock.lean — the real structure on a product: for `M_N` as a bimodule over a product
  of matrix algebras sitting block-diagonally in it (every pair of factors once), an operator
  satisfies the order-one condition and commutes with the real structure `ξ ↦ ξ⋆` iff it is a left
  multiplication by `A` depending on the right block plus a right multiplication by `A⋆` depending
  on the left block. With one block this is unit 169's theorem at every finite size, and the
  operator determines `A` up to exactly `i t · 1`, `t` real.

  SPINE L6 / `WALLS` §W9 rung 2, second clause, with `J` — carried from one factor of size two
  (unit 169) to products of matrix algebras. Hardening unit 230, 26 September 2026.

  WHY. Unit 228 solved order-one for `M_N` over a product of matrix algebras
  (`OrderOneBlockDiagonal.orderOne_iff`), and its NOT list says *"The real structure `J`, the
  grading `γ` and the KO signs: units 169 and 170 did them for one factor of size two; nothing
  here."* Unit 169's `JSelectsDirac` did `J` on `Hw` alone, and its NOT list says *"`n = 2` only,
  because `Jprod`, `piW`, `piOpW` are defined on `Hw` only"* and, of `A ↦ D`, *"that this is the
  whole fibre is not stated"*. In CCM the right action is manufactured from `J`
  (`OppositeFromRealStructure`), so `J` is the next constraint on `D` after order-one. On `M_N` the
  real structure is `ξ ↦ ξ⋆` — exchange the two factors and conjugate,
  `ConjugatePermutation.conjPerm (Equiv.prodComm ι ι)` — which at `ι = Fin 2` is unit 169's `Jprod`.

  WHAT IS PROVED (`ι` any finite type, the blocks the fibres of any `β : ι → κ`, over `ℂ`).
  (1) `exchConj M`: exchange the two factors of `M`'s indices and conjugate its entries;
      `exchConj_exchConj`; **`exchConj_blockKron`**: it swaps the two parts of unit 228's
      `blockKron` and conjugates each.
  (2) **`orderOne_exchConj_iff`**: order-one against the block-diagonal matrices and
      `exchConj M = M` hold iff `M = blockKron β A Ā` for some family `A` — `M` is the average of
      itself and `exchConj M`, by unit 228's `blockKron_add` and `smul_blockKron`.
  (3) The fibre. **`blockKron_conj_eq_iff`**: `blockKron β A Ā` determines `A` exactly up to
      block-scalars `f j k` on the diagonal with `conj (f j k) = −f k j`, from unit 228's
      `blockKron_eq_blockKron_iff`; **`kron_conj_eq_iff`**: with one block and `ι` nonempty,
      `A ⊗ 1 + 1 ⊗ Ā` determines `A` exactly up to `i t · 1`, `t` real.
  (4) As operators on `ℂ^{ι × ι}`, `ι : Type`. `transpose_mem_blockDiagSet` and
      `transpose_star_eq_map`; **`jInv_matAlg_iff`**: `matAlg M` commutes with
      `J = conjPerm (Equiv.prodComm ι ι)` iff `exchConj M = M`, through
      `OppositeFromRealStructure.conjPerm_conj`; **`orderOne_jInv_matAlg_iff`**: with
      `π = matAlg ∘ kronLeft` and `πOp = matAlg ∘ kronRight` restricted to the block-diagonal
      matrices, order-one and `J`-invariance hold iff `D = matAlg (blockKron β A Ā)`;
      **`orderOne_jInv_matAlg_iff_one`**: with one block, iff `D = π(A) + π°(A⋆)` — unit 169's
      `orderOne_jInv_iff`, at every finite index type.
  (5) **`piW_add_piOpW_star_eq_iff`**: on the witness `Hw`, `piW A + piOpW (op (star A))`
      determines `A` exactly up to `i t · 1` — the fibre unit 169 left unstated.

  NOT PROVED, said exactly.
  • The grading `γ` and the KO signs on a product. Unit 170 did them for `gammaCcm` on `M₂(ℂ)`;
    which gradings a product admits, and what `Dγ = −γD` then leaves of `A`, are not here.
  • Multiplicities and sub-bimodules (CCM's `H_F`), and real or quaternionic factors
    (`UNLOCK_WATCHLIST` 262), as in unit 228.
    ⚠ 26 September 2026 (hardening unit 232, `paper_f/OrderOneCommutant.lean`): in
    part — order-one alone, without `J`, is written there for any sets of test matrices over any
    field and on sub-bimodules, in commutant form (`OrderOneCommutant.orderOne_iff_commutant`,
    `orderOne_iff_commutant_compress`), and computed for full matrix algebras with a multiplicity
    (`orderOne_multiplicity_iff`); `J` with multiplicities is not.
  • Nothing about the cascade, the factor list, or a tag: rung 2 is not climbed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `transpose_mem_blockDiagSet` takes
  `a ∈ blockDiagSet β`; `kron_conj_eq_iff` takes `[Nonempty ι]`. The rest take elements of their
  types and nothing else; (4) takes `ι : Type` because `kronLeft` and `kronRight` do.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 12 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: none is taken. The nearest statements are unit 169's
  `orderOne_jInv_iff` on `Hw`, which `orderOne_jInv_matAlg_iff_one` extends to every finite index
  type, and its `swapConj_kron_sum` and `jInv_iff_matrix`, of which `exchConj_blockKron` and
  `jInv_matAlg_iff` are the product and every-size versions; `JSelectsDirac.transpose_conjTranspose`
  is `transpose_star_eq_map` at `Fin 2`, which is why the general one is written here.

  `#print axioms` on all 12 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/
import OrderOneBlockDiagonal

open Matrix
open scoped Kronecker

namespace OrderOneRealBlock

open OrderOneBlockDiagonal

/-! ## 1. Exchange-conjugation, and what it does to `blockKron` -/

section Matrices

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]

/-- Exchange the two factors and conjugate every entry: the real structure `ξ ↦ ξ⋆` of the
regular bimodule, acting on an operator by conjugation. -/
def exchConj (M : Matrix (ι × ι) (ι × ι) ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  (M.submatrix Prod.swap Prod.swap).map (starRingEnd ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem exchConj_exchConj (M : Matrix (ι × ι) (ι × ι) ℂ) : exchConj (exchConj M) = M := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp [exchConj]

omit [Fintype ι] in
/-- **Exchange-conjugation swaps the two parts of `blockKron` and conjugates them.** -/
theorem exchConj_blockKron (β : ι → κ) (C B : κ → Matrix ι ι ℂ) :
    exchConj (blockKron β C B) =
      blockKron β (fun j => (B j).map (starRingEnd ℂ)) (fun j => (C j).map (starRingEnd ℂ)) := by
  ext ⟨x, p⟩ ⟨y, q⟩
  simp only [exchConj, blockKron, Matrix.map_apply, Matrix.submatrix_apply, Prod.swap_prod_mk,
    Matrix.of_apply, map_add, apply_ite (starRingEnd ℂ), map_zero]
  exact add_comm _ _

/-! ## 2. Order-one and the real structure on a product -/

/-- **ORDER-ONE AND THE REAL STRUCTURE ON A PRODUCT**: an operator satisfies order-one against the
block-diagonal matrices and is invariant under exchange-conjugation iff it is `blockKron β A Ā` —
left multiplication by `A` of the right block plus right multiplication by `A⋆` of the left
block. -/
theorem orderOne_exchConj_iff (β : ι → κ) (M : Matrix (ι × ι) (ι × ι) ℂ) :
    (OrderOne β M ∧ exchConj M = M) ↔
      ∃ A : κ → Matrix ι ι ℂ, M = blockKron β A (fun j => (A j).map (starRingEnd ℂ)) := by
  constructor
  · rintro ⟨h, hJ⟩
    obtain ⟨C, B, rfl⟩ := (orderOne_iff β _).mp h
    rw [exchConj_blockKron] at hJ
    refine ⟨(1 / 2 : ℂ) • (C + fun j => (B j).map (starRingEnd ℂ)), ?_⟩
    have e : blockKron β C B = (1 / 2 : ℂ) • (blockKron β C B +
        blockKron β (fun j => (B j).map (starRingEnd ℂ)) (fun j => (C j).map (starRingEnd ℂ))) := by
      rw [hJ, ← two_smul ℂ (blockKron β C B), smul_smul]
      norm_num
    rw [blockKron_add, smul_blockKron] at e
    rw [e]
    congr 1
    funext j
    ext x y
    simp [Matrix.map_apply, Pi.add_apply, Pi.smul_apply, add_comm, map_ofNat, mul_add]
  · rintro ⟨A, rfl⟩
    refine ⟨orderOne_blockKron β _ _, ?_⟩
    rw [exchConj_blockKron]
    congr 1
    funext j
    ext x y
    simp

omit [Fintype ι] in
/-- **The fibre of `A ↦ blockKron β A Ā`**: two families give the same operator exactly when they
differ by block-scalars `f j k` on the diagonal with `conj (f j k) = −f k j`. -/
theorem blockKron_conj_eq_iff (β : ι → κ) (A A' : κ → Matrix ι ι ℂ) :
    blockKron β A' (fun j => (A' j).map (starRingEnd ℂ)) =
        blockKron β A (fun j => (A j).map (starRingEnd ℂ)) ↔
      ∃ f : κ → κ → ℂ, (∀ x y p, A' (β p) x y = A (β p) x y + if x = y then f (β p) (β x) else 0)
        ∧ ∀ x p, starRingEnd ℂ (f (β p) (β x)) = -f (β x) (β p) := by
  rw [blockKron_eq_blockKron_iff]
  refine exists_congr fun f => and_congr_right fun hA => ?_
  constructor
  · intro hB x p
    have h1 := hB p x x
    simp only [Matrix.map_apply, if_true] at h1
    rw [hA x x p, if_pos rfl, map_add] at h1
    linear_combination h1
  · intro hf x p q
    simp only [Matrix.map_apply]
    rw [hA p q x, map_add]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos rfl, if_pos rfl, hf]
      ring
    · rw [if_neg hpq, if_neg hpq, map_zero]
      ring

omit [Fintype ι] in
/-- **One block: the fibre is `i t · 1`**. For `ι` nonempty, `A ⊗ 1 + 1 ⊗ Ā` determines `A`
exactly up to adding `i t · 1` with `t` real. -/
theorem kron_conj_eq_iff [Nonempty ι] (A A' : Matrix ι ι ℂ) :
    A' ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ A'.map (starRingEnd ℂ) =
        A ⊗ₖ (1 : Matrix ι ι ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ A.map (starRingEnd ℂ) ↔
      ∃ t : ℝ, A' = A + ((t : ℂ) * Complex.I) • (1 : Matrix ι ι ℂ) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  rw [kron_eq_kron_iff]
  constructor
  · rintro ⟨c, hA, hB⟩
    have e := congrFun (congrFun hB i₀) i₀
    rw [hA] at e
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, mul_one, map_add] at e
    have hc : starRingEnd ℂ c = -c := by linear_combination e
    refine ⟨c.im, ?_⟩
    rw [hA]
    congr 2
    apply Complex.ext
    · have := congrArg Complex.re hc
      simp only [Complex.conj_re, Complex.neg_re] at this
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
        Complex.I_im, mul_one, sub_zero]
      linarith
    · simp
  · rintro ⟨t, rfl⟩
    refine ⟨(t : ℂ) * Complex.I, rfl, ?_⟩
    ext x y
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul, map_add]
    split_ifs
    · simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
        Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
      constructor <;> ring
    · simp

omit [Fintype ι] [DecidableEq ι] in
theorem transpose_mem_blockDiagSet {β : ι → κ} {a : Matrix ι ι ℂ} (ha : a ∈ blockDiagSet β) :
    aᵀ ∈ blockDiagSet β :=
  fun x y h => ha y x (Ne.symm h)

omit [Fintype ι] [DecidableEq ι] in
/-- `(A⋆)ᵀ` is `A` with its entries conjugated. -/
theorem transpose_star_eq_map (A : Matrix ι ι ℂ) : (star A)ᵀ = A.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

end Matrices

/-! ## 3. As operators on `ℂ^{ι × ι}`, with the conjugate-linear `J` -/

section Operators

open OrderOneNontrivial ConjugatePermutation OppositeFromRealStructure OrderOneRegularBimodule
  MulOpposite

variable {ι κ : Type} [Fintype ι] [DecidableEq ι]

/-- **The real structure as an operator**: conjugating `matAlg M` by `ξ ↦ ξ⋆` (exchange the
factors, conjugate the coordinates) is `matAlg (exchConj M)`, so invariance is `exchConj M = M`. -/
theorem jInv_matAlg_iff (M : Matrix (ι × ι) (ι × ι) ℂ) :
    (∀ v, conjPerm (Equiv.prodComm ι ι) (matAlg _ M (conjPerm (Equiv.prodComm ι ι) v)) =
        matAlg _ M v) ↔ exchConj M = M := by
  have hσ : ∀ i : ι × ι, Equiv.prodComm ι ι (Equiv.prodComm ι ι i) = i := fun _ => rfl
  constructor
  · intro h
    apply matAlg_injective
    refine LinearMap.ext fun v => ?_
    have := h v
    rw [matAlg_apply, matAlg_apply, conjPerm_conj _ hσ] at this
    rw [matAlg_apply, matAlg_apply]
    exact this
  · intro h v
    rw [matAlg_apply, matAlg_apply, conjPerm_conj _ hσ]
    exact congrArg (fun N => Matrix.toEuclideanCLM (𝕜 := ℂ) N v) h

/-- **ORDER-ONE AND THE REAL STRUCTURE ON A PRODUCT, AS OPERATORS.** With `π = matAlg ∘ kronLeft`
and `πOp = matAlg ∘ kronRight` restricted to the block-diagonal matrices, and `J` the
conjugate-linear `ξ ↦ ξ⋆`, an operator satisfies order-one and commutes with `J` iff it is
`matAlg (blockKron β A Ā)`. -/
theorem orderOne_jInv_matAlg_iff (β : ι → κ) (D : Module.End ℂ (EuclideanSpace ℂ (ι × ι))) :
    ((∀ a ∈ blockDiagSet (R := ℂ) β, ∀ b ∈ blockDiagSet (R := ℂ) β,
        ⁅⁅D, matAlg _ (kronLeft ι ι a)⁆, matAlg _ (kronRight ι ι (op b))⁆ = 0) ∧
      ∀ v, conjPerm (Equiv.prodComm ι ι) (D (conjPerm (Equiv.prodComm ι ι) v)) = D v) ↔
    ∃ A : κ → Matrix ι ι ℂ,
      D = matAlg _ (blockKron β A fun j => (A j).map (starRingEnd ℂ)) := by
  obtain ⟨M, rfl⟩ := matAlg_surjective' (ι × ι) D
  have key : ∀ a b : Matrix ι ι ℂ,
      ⁅⁅matAlg _ M, matAlg _ (kronLeft ι ι a)⁆, matAlg _ (kronRight ι ι (op b))⁆ = 0 ↔
        ⁅⁅M, a ⊗ₖ (1 : Matrix ι ι ℂ)⁆, (1 : Matrix ι ι ℂ) ⊗ₖ bᵀ⁆ = 0 := by
    intro a b
    rw [← map_lie_lie, kronLeft_apply, kronRight_apply, unop_op]
    exact ⟨fun h => matAlg_injective _ (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  have hOO : (∀ a ∈ blockDiagSet (R := ℂ) β, ∀ b ∈ blockDiagSet (R := ℂ) β,
      ⁅⁅matAlg _ M, matAlg _ (kronLeft ι ι a)⁆, matAlg _ (kronRight ι ι (op b))⁆ = 0) ↔
        OrderOne β M := by
    constructor
    · intro h a ha b hb
      have := (key a bᵀ).mp (h a ha bᵀ (transpose_mem_blockDiagSet hb))
      rwa [Matrix.transpose_transpose] at this
    · intro h a ha b hb
      exact (key a b).mpr (h a ha bᵀ (transpose_mem_blockDiagSet hb))
  rw [hOO, jInv_matAlg_iff, orderOne_exchConj_iff]
  exact ⟨fun ⟨A, hA⟩ => ⟨A, by rw [hA]⟩, fun ⟨A, hA⟩ => ⟨A, matAlg_injective _ hA⟩⟩

/-- **Unit 169's theorem at every finite index type**: with one block, order-one against all
matrices and `J`-invariance hold iff `D = π(A) + π°(A⋆)`. -/
theorem orderOne_jInv_matAlg_iff_one (D : Module.End ℂ (EuclideanSpace ℂ (ι × ι))) :
    ((∀ (a : Matrix ι ι ℂ) (b : (Matrix ι ι ℂ)ᵐᵒᵖ),
        ⁅⁅D, matAlg _ (kronLeft ι ι a)⁆, matAlg _ (kronRight ι ι b)⁆ = 0) ∧
      ∀ v, conjPerm (Equiv.prodComm ι ι) (D (conjPerm (Equiv.prodComm ι ι) v)) = D v) ↔
    ∃ A : Matrix ι ι ℂ, D = matAlg _ (kronLeft ι ι A) + matAlg _ (kronRight ι ι (op (star A))) := by
  have hall : ∀ a : Matrix ι ι ℂ, a ∈ blockDiagSet (fun _ : ι => ()) := fun _ _ _ h => absurd rfl h
  have e := orderOne_jInv_matAlg_iff (fun _ : ι => ()) D
  constructor
  · rintro ⟨h, hJ⟩
    obtain ⟨A, hA⟩ := e.mp ⟨fun a _ b _ => h a (op b), hJ⟩
    refine ⟨A (), ?_⟩
    rw [hA, ← map_add, kronLeft_apply, kronRight_apply, unop_op, transpose_star_eq_map,
      ← blockKron_const]
  · rintro ⟨A, hA⟩
    refine ⟨fun a b => ?_, (e.mpr ⟨fun _ => A, ?_⟩).2⟩
    · have := (e.mpr ⟨fun _ => A, ?_⟩).1 a (hall a) (unop b) (hall _)
      · simpa using this
      · rw [hA, ← map_add, kronLeft_apply, kronRight_apply, unop_op, transpose_star_eq_map,
          ← blockKron_const]
    · rw [hA, ← map_add, kronLeft_apply, kronRight_apply, unop_op, transpose_star_eq_map,
        ← blockKron_const]

end Operators

/-! ## 4. On the estate's witness `Hw`: the fibre unit 169 left unstated -/

section Witness

open OrderOneNontrivial MulOpposite

/-- **The fibre of `A ↦ piW A + piOpW (op (star A))` on `Hw`**: exactly `A + i t · 1`, `t` real. -/
theorem piW_add_piOpW_star_eq_iff (A A' : Matrix (Fin 2) (Fin 2) ℂ) :
    piW A' + piOpW (op (star A')) = piW A + piOpW (op (star A)) ↔
      ∃ t : ℝ, A' = A + ((t : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, piW X + piOpW (op (star X)) =
      matAlg Slots (X ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)
        + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ X.map (starRingEnd ℂ)) := fun X => by
    rw [map_add, ← transpose_star_eq_map]
    rfl
  rw [h, h, ← kron_conj_eq_iff]
  exact (matAlg_injective Slots).eq_iff

end Witness

end OrderOneRealBlock
