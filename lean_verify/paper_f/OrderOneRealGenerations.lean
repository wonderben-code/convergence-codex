/-
  OrderOneRealGenerations.lean — the real structure with a generation index. On
  `ℂ^ι ⊗ (ℂ^ι ⊗ ℂ^μ)` — `M_ι(ℂ)` acting on itself, every vector carrying a generation label from
  `μ` — an operator satisfies order-one and commutes with the real structure `J` (exchange the two
  `ι` factors, keep the generation, conjugate) iff it is `genPart A + 1 ⊗ Ā` for one matrix `A` on
  `ι × μ`: one operator on the left factor with the generations and, conjugated, the same on the
  right factor with the generations. `A` is determined exactly up to `1 ⊗ G` with `conj G = −G`.
  And `J` does not restore the tensor-sum shape: at a multiplicity of two a self-adjoint, order-one,
  `J`-invariant operator can be `C ⊗ 1 + 1 ⊗ B` in neither grouping.

  SPINE L6 / `WALLS` §W9 rung 2, second clause with `J` — unit 230's `J` carried to a space whose
  pieces repeat; and SPINE L19 / `ASSUMPTIONS_LEDGER` 12 — unit 232's finding that order-one does
  not force the tensor-sum shape at a multiplicity of two survives the real structure. Hardening
  unit 234, 26 September 2026.

  WHY. Unit 232 (`OrderOneCommutant`) solved order-one with a multiplicity —
  `D = genPart C + 1 ⊗ B`, two parts sharing the multiplicity space (`orderOne_multiplicity_iff`) —
  and its NOT list says *"The real structure `J`, the grading `γ` and the KO signs: unit 230 did `J`
  with every pair of factors once; nothing here."* In CCM's `H_F` the generations are such a
  multiplicity and `J` acts on the generation label by complex conjugation, `J (ξ ⊗ v) = ξ⋆ ⊗ v̄`;
  and the right action is manufactured from `J` (`OppositeFromRealStructure`), so `J` is the next
  constraint on `D`. Unit 232 also showed the tensor-sum shape — the premise of unit 172's
  factorisation of the spectral action — is not forced at multiplicity two; whether `J` restores it
  was open.

  WHAT IS PROVED (`ι`, `μ` any finite types, over `ℂ`).
  (1) `genSwap ι μ`: the permutation `(x, (p, i)) ↦ (p, (x, i))`, its own inverse
      (`genSwap_genSwap`); `exchConjGen M`: `M` with both indices permuted by it and every entry
      conjugated — `J ∘ M ∘ J` as a matrix; `exchConjGen_exchConjGen`, `exchConjGen_add`.
      **`exchConjGen_genPart`** and **`exchConjGen_one_kron`**: it carries `genPart C` to `1 ⊗ C̄`
      and `1 ⊗ B` to `genPart B̄`; **`exchConjGen_kron_one`**: it carries the left action `a ⊗ 1` to
      `1 ⊗ (ā ⊗ 1)`. `genPart_add`, `genPart_smul`, `genPart_conjTranspose`: unit 232's `genPart` is
      linear and commutes with the conjugate transpose.
  (2) **`orderOne_exchConjGen_iff`**: order-one against all of `M_ι` on the left and `M_ι ⊗ 1` on
      the right, together with `exchConjGen D = D`, holds iff `D = genPart A + 1 ⊗ Ā` — an order-one
      `genPart C + 1 ⊗ B` that `J` fixes is the average of itself and its image, `A = ½ (C + B̄)`.
  (3) **`genPart_conj_eq_iff`**: `genPart A + 1 ⊗ Ā` determines `A` exactly up to adding `1 ⊗ G`,
      `G` a matrix on `μ` with `conj G = −G` entrywise — with `μ` a point, unit 230's `i t · 1`.
  (4) **`exists_orderOne_jInv_not_kronSum`**: at `ι = μ = Fin 2`, with `E = single (0, 0) (0, 0) 1`,
      `genPart E + 1 ⊗ Ē` is self-adjoint, satisfies order-one and `J`-invariance, and is neither
      `C ⊗ 1 + 1 ⊗ B` nor `genPart C + 1 ⊗ (B ⊗ 1)` for any `C`, `B`.
  (5) As operators on `ℂ^{ι × (ι × μ)}`, with `J = conjPerm (genSwap ι μ)` conjugate-linear:
      **`conjPerm_genSwap_matAlg`**: `J ∘ matAlg M ∘ J = matAlg (exchConjGen M)`;
      **`conjPerm_genSwap_star`**: `J π(a⋆) J = 1 ⊗ (aᵀ ⊗ 1)` — the right action used here is the
      one `J` implements from `π`, CCM's `πOp_impl`; **`jInvGen_matAlg_iff`**: `J`-invariance of
      `matAlg M` is `exchConjGen M = M`; **`orderOne_jInvGen_matAlg_iff`**: order-one and
      `J`-invariance hold iff `D = matAlg (genPart A + 1 ⊗ Ā)`.

  NOT PROVED, said exactly.
  • Products, sub-bimodules and other algebras with a generation index: one full matrix factor
    only. Block-diagonal algebras, `ℍ` and CCM's `A_F` with generations are not done, and `H_F`
    is not named.
  • The grading `γ` and the KO signs with a generation index, and what `Dγ = −γD` leaves of `A`.
    ⚠ 26 September 2026 (hardening unit 236, `paper_f/GammaFixesDiracGenerations.lean`): in
    part — at `ι = Fin 2`, with unit 170's `gammaMat` and the identity on the generation,
    `Dγ = −γD` leaves `A = diag(a, −ā)` block by block and `D = Dsym ⊗ R` with `R` real
    (`GammaFixesDiracGenerations.gen_fixes_dirac`), and `JγJ = −γ` (`exchConjGen_gammaGen`);
    other `ι`, other gradings and products are not.
  • What `A` is physically: nothing here identifies `A`'s action on the generation label with
    Yukawa matrices, or reads a mass or a mixing angle off it.
  • That the trace of the exponential fails to factorise for the operator in (4): only the shape
    is shown not forced, as in unit 232; nothing here computes a spectrum.
    ⚠ 26 September 2026 (hardening unit 242, `paper_f/KronSumCriterion.lean`): the
    shape decided for every `A` — `genPart A + 1 ⊗ Ā` is a tensor sum, in either grouping, iff
    `A` is a Kronecker sum (`KronSumCriterion.isKronSum_genPart_conj_iff`,
    `genPart_conj_genPartSum_iff`), so it is forced for every such operator iff `ι` or `μ` has at
    most one point (`orderOne_jInv_forces_isKronSum_iff`), and (4) holds at every size
    (`exists_orderOne_jInv_not_kronSum_of_nontrivial`); the trace where it fails is not computed.
  • Nothing about the cascade, its `D` (`L40433`), the factor list, or a tag: rung 2 is not
    climbed.
    ⚠ 26 September 2026 (unit 239, `ERRATUM 700`): the watchlist item meant, *the cascade's `D`
    AS A TENSOR SUM*, stood at `L40927` when this was written; the number given, 40433, was its
    line on 20 September, copied from an older record.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). None beyond the declarations' types: every
  statement takes elements of its types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 18 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: none is taken. The nearest statements are unit 230's `exchConj`,
  `exchConj_blockKron`, `orderOne_exchConj_iff`, `kron_conj_eq_iff`, `jInv_matAlg_iff` and
  `orderOne_jInv_matAlg_iff`, whose versions with a generation index are `exchConjGen`,
  `exchConjGen_genPart` with `exchConjGen_one_kron`, `orderOne_exchConjGen_iff`,
  `genPart_conj_eq_iff`, `jInvGen_matAlg_iff` and `orderOne_jInvGen_matAlg_iff`; and unit 232's
  `exists_orderOne_not_kronSum`, of which (4) is the version with `J`.

  `#print axioms` on all 18 declarations below: `genSwap` depends on none, `genSwap_genSwap` on
  `[Quot.sound]`, the other sixteen on `[propext, Classical.choice, Quot.sound]`.
-/
import OrderOneCommutant

open Matrix
open scoped Kronecker

namespace OrderOneRealGenerations

open OrderOneCommutant

/-! ## 1. The real structure with a generation index -/

section Matrices

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

/-- The permutation `(x, (p, i)) ↦ (p, (x, i))`: exchange the two `ι` factors, keep the
generation index. -/
def genSwap (ι μ : Type*) : Equiv.Perm (ι × (ι × μ)) where
  toFun a := (a.2.1, (a.1, a.2.2))
  invFun a := (a.2.1, (a.1, a.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exchange the two `ι` factors, keep the generation index, conjugate every entry: the real
structure `ξ ⊗ v ↦ ξ⋆ ⊗ v̄` acting on an operator by conjugation. -/
def exchConjGen (M : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ) : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ :=
  (M.submatrix (genSwap ι μ) (genSwap ι μ)).map (starRingEnd ℂ)

omit [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ] in
theorem exchConjGen_exchConjGen (M : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ) :
    exchConjGen (exchConjGen M) = M := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp [exchConjGen, genSwap]

omit [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ] in
theorem exchConjGen_add (M N : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ) :
    exchConjGen (M + N) = exchConjGen M + exchConjGen N := by
  ext a b
  simp [exchConjGen]

omit [Fintype ι] [Fintype μ] [DecidableEq μ] in
/-- Exchange-conjugation carries the part on the left factor and the generations to the part on
the right factor and the generations, conjugated. -/
theorem exchConjGen_genPart (C : Matrix (ι × μ) (ι × μ) ℂ) :
    exchConjGen (genPart (κ := ι) C) = (1 : Matrix ι ι ℂ) ⊗ₖ C.map (starRingEnd ℂ) := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [exchConjGen, genSwap, genPart, Matrix.map_apply, Matrix.submatrix_apply,
    Equiv.coe_fn_mk, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype ι] [Fintype μ] [DecidableEq μ] in
theorem exchConjGen_one_kron (B : Matrix (ι × μ) (ι × μ) ℂ) :
    exchConjGen ((1 : Matrix ι ι ℂ) ⊗ₖ B) = genPart (κ := ι) (B.map (starRingEnd ℂ)) := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [exchConjGen, genSwap, genPart, Matrix.map_apply, Matrix.submatrix_apply,
    Equiv.coe_fn_mk, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype ι] [Fintype μ] in
/-- Exchange-conjugation carries the left action `a ⊗ 1` to the right action `1 ⊗ (ā ⊗ 1)`. -/
theorem exchConjGen_kron_one (a : Matrix ι ι ℂ) :
    exchConjGen (a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ)) =
      (1 : Matrix ι ι ℂ) ⊗ₖ (a.map (starRingEnd ℂ) ⊗ₖ (1 : Matrix μ μ ℂ)) := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [exchConjGen, genSwap, Matrix.map_apply, Matrix.submatrix_apply, Equiv.coe_fn_mk,
    kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

omit [Fintype ι] [Fintype μ] [DecidableEq μ] in
theorem genPart_add (C C' : Matrix (ι × μ) (ι × μ) ℂ) :
    genPart (κ := ι) (C + C') = genPart C + genPart C' := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [genPart, Matrix.of_apply, Matrix.add_apply]
  split_ifs <;> simp

omit [Fintype ι] [Fintype μ] [DecidableEq μ] in
theorem genPart_smul (c : ℂ) (C : Matrix (ι × μ) (ι × μ) ℂ) :
    genPart (κ := ι) (c • C) = c • genPart C := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [genPart, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

omit [Fintype ι] [Fintype μ] [DecidableEq μ] in
/-- `genPart` commutes with the conjugate transpose. -/
theorem genPart_conjTranspose (C : Matrix (ι × μ) (ι × μ) ℂ) :
    (genPart (κ := ι) C)ᴴ = genPart Cᴴ := by
  ext ⟨x, p, i⟩ ⟨y, q, j⟩
  simp only [genPart, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

/-! ## 2. Order-one and the real structure with generations -/

/-- **ORDER-ONE AND THE REAL STRUCTURE WITH A GENERATION INDEX.** On `ℂ^ι ⊗ (ℂ^ι ⊗ ℂ^μ)`, an
operator satisfies order-one against all of `M_ι` on the left and `M_ι ⊗ 1` on the right and is
invariant under exchange-conjugation iff it is `genPart A + 1 ⊗ Ā` for one `A` on `ι × μ` — the
same operator on the left factor with the generations and, conjugated, on the right. -/
theorem orderOne_exchConjGen_iff (D : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ) :
    ((∀ (a b : Matrix ι ι ℂ), ⁅⁅D, a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ)⁆,
        (1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧ exchConjGen D = D) ↔
      ∃ A : Matrix (ι × μ) (ι × μ) ℂ,
        D = genPart A + (1 : Matrix ι ι ℂ) ⊗ₖ A.map (starRingEnd ℂ) := by
  rw [orderOne_multiplicity_iff]
  constructor
  · rintro ⟨⟨C, B, rfl⟩, hJ⟩
    rw [exchConjGen_add, exchConjGen_genPart, exchConjGen_one_kron] at hJ
    refine ⟨(1 / 2 : ℂ) • (C + B.map (starRingEnd ℂ)), ?_⟩
    have hmap : ((1 / 2 : ℂ) • (C + B.map (starRingEnd ℂ))).map (starRingEnd ℂ) =
        (1 / 2 : ℂ) • (C.map (starRingEnd ℂ) + B) := by
      ext a b
      simp [Matrix.map_apply, map_ofNat]
      ring
    rw [hmap, genPart_smul, genPart_add, Matrix.kronecker_smul, Matrix.kronecker_add]
    calc genPart C + (1 : Matrix ι ι ℂ) ⊗ₖ B
        = (1 / 2 : ℂ) • (genPart C + (1 : Matrix ι ι ℂ) ⊗ₖ B) +
            (1 / 2 : ℂ) • (genPart C + (1 : Matrix ι ι ℂ) ⊗ₖ B) := by
          rw [← add_smul]; norm_num
      _ = (1 / 2 : ℂ) • (genPart C + (1 : Matrix ι ι ℂ) ⊗ₖ B) +
            (1 / 2 : ℂ) • ((1 : Matrix ι ι ℂ) ⊗ₖ C.map (starRingEnd ℂ) +
              genPart (B.map (starRingEnd ℂ))) := by rw [hJ]
      _ = _ := by simp only [smul_add]; abel
  · rintro ⟨A, rfl⟩
    refine ⟨⟨A, _, rfl⟩, ?_⟩
    rw [exchConjGen_add, exchConjGen_genPart, exchConjGen_one_kron, add_comm]
    congr 2
    ext a b
    simp

omit [Fintype ι] [Fintype μ] [DecidableEq μ] in
/-- **The fibre**: `genPart A + 1 ⊗ Ā` determines `A` exactly up to adding `1 ⊗ G` with
`conj G = −G` — an operator on the generations alone, skew under conjugation. -/
theorem genPart_conj_eq_iff (A A' : Matrix (ι × μ) (ι × μ) ℂ) :
    genPart (κ := ι) A' + (1 : Matrix ι ι ℂ) ⊗ₖ A'.map (starRingEnd ℂ) =
        genPart A + (1 : Matrix ι ι ℂ) ⊗ₖ A.map (starRingEnd ℂ) ↔
      ∃ G : Matrix μ μ ℂ, A' = A + (1 : Matrix ι ι ℂ) ⊗ₖ G ∧ G.map (starRingEnd ℂ) = -G := by
  constructor
  · intro h
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨x₀⟩⟩
    · exact ⟨0, Subsingleton.elim _ _, by simp⟩
    have e : ∀ x p i y q j, (if p = q then A' (x, i) (y, j) - A (x, i) (y, j) else 0) +
        (if x = y then starRingEnd ℂ (A' (p, i) (q, j) - A (p, i) (q, j)) else 0) = 0 := by
      intro x p i y q j
      have := congrFun (congrFun h (x, (p, i))) (y, (q, j))
      simp only [genPart, Matrix.add_apply, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply,
        Matrix.map_apply] at this
      rw [map_sub]
      split_ifs at this ⊢ <;> linear_combination this
    refine ⟨Matrix.of fun i j => A' (x₀, i) (x₀, j) - A (x₀, i) (x₀, j), ?_, ?_⟩
    · ext ⟨x, i⟩ ⟨y, j⟩
      simp only [Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply, Matrix.of_apply]
      by_cases hxy : x = y
      · subst hxy
        have h1 := e x x₀ i x x₀ j
        have h2 := e x₀ x₀ i x₀ x₀ j
        simp only [if_true] at h1 h2
        rw [if_pos rfl, one_mul]
        have h3 : A' (x, i) (x, j) - A (x, i) (x, j) = A' (x₀, i) (x₀, j) - A (x₀, i) (x₀, j) := by
          linear_combination h1 - h2
        linear_combination h3
      · have h1 := e x x₀ i y x₀ j
        simp only [if_true, if_neg hxy, add_zero] at h1
        rw [if_neg hxy, zero_mul, add_zero]
        linear_combination h1
    · ext i j
      have h2 := e x₀ x₀ i x₀ x₀ j
      simp only [if_true] at h2
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.neg_apply]
      linear_combination h2
  · rintro ⟨G, rfl, hG⟩
    have h0 : genPart (κ := ι) ((1 : Matrix ι ι ℂ) ⊗ₖ G) +
        (1 : Matrix ι ι ℂ) ⊗ₖ ((1 : Matrix ι ι ℂ) ⊗ₖ G).map (starRingEnd ℂ) = 0 := by
      ext ⟨x, p, i⟩ ⟨y, q, j⟩
      have hg := congrFun (congrFun hG i) j
      simp only [Matrix.map_apply, Matrix.neg_apply] at hg
      simp only [genPart, Matrix.add_apply, Matrix.of_apply, kroneckerMap_apply, Matrix.one_apply,
        Matrix.map_apply, Matrix.zero_apply]
      split_ifs <;> simp [hg]
    rw [Matrix.map_add _ (map_add (starRingEnd ℂ)), genPart_add, Matrix.kronecker_add,
      add_add_add_comm, h0, add_zero]

/-- **`J` DOES NOT RESTORE THE TENSOR-SUM SHAPE.** At `ι = μ = Fin 2`, with
`E = single (0, 0) (0, 0) 1`, `genPart E + 1 ⊗ Ē` is self-adjoint, satisfies order-one and is
invariant under exchange-conjugation, and it is neither `C ⊗ 1 + 1 ⊗ B` nor
`genPart C + 1 ⊗ (B ⊗ 1)`. -/
theorem exists_orderOne_jInv_not_kronSum :
    ∃ D : Matrix (Fin 2 × (Fin 2 × Fin 2)) (Fin 2 × (Fin 2 × Fin 2)) ℂ, D.IsHermitian ∧
      ((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ),
          ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)⁆,
            (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))⁆ = 0) ∧
        exchConjGen D = D) ∧
      (∀ (C : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
        D ≠ C ⊗ₖ 1 + 1 ⊗ₖ B) ∧
      (∀ (C : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ),
        D ≠ genPart C + 1 ⊗ₖ (B ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  refine ⟨genPart (single (0, 0) (0, 0) 1) +
      1 ⊗ₖ (single ((0 : Fin 2), (0 : Fin 2)) (0, 0) (1 : ℂ)).map (starRingEnd ℂ),
    ?_, (orderOne_exchConjGen_iff _).mpr ⟨_, rfl⟩, fun C B h => ?_, fun C B h => ?_⟩
  · refine Matrix.IsHermitian.add ?_ ?_
    · rw [Matrix.IsHermitian, genPart_conjTranspose, Matrix.conjTranspose_single, star_one]
    · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        Matrix.map_single _ _ _ (starRingEnd ℂ), Matrix.conjTranspose_single, map_one, star_one]
  · have e1 := congrFun (congrFun h (0, (0, 0))) (0, (0, 0))
    have e2 := congrFun (congrFun h (1, (0, 0))) (1, (0, 0))
    have e3 := congrFun (congrFun h (0, (0, 1))) (0, (0, 1))
    have e4 := congrFun (congrFun h (1, (0, 1))) (1, (0, 1))
    simp only [genPart, Fin.isValue, single_apply, Prod.mk.injEq, map_single, map_one, add_apply,
      of_apply, ↓reduceIte, and_self, kroneckerMap_apply, one_apply_eq, mul_one, one_mul,
      zero_ne_one, and_true, zero_add, and_false, mul_zero, add_zero] at e1 e2 e3 e4
    have : (1 : ℂ) = 0 := by linear_combination e1 - e2 - e3 + e4
    exact one_ne_zero this
  · have e1 := congrFun (congrFun h (0, (0, 0))) (0, (0, 0))
    have e2 := congrFun (congrFun h (0, (1, 0))) (0, (1, 0))
    have e3 := congrFun (congrFun h (0, (0, 1))) (0, (0, 1))
    have e4 := congrFun (congrFun h (0, (1, 1))) (0, (1, 1))
    simp only [genPart, Fin.isValue, single_apply, Prod.mk.injEq, map_single, map_one, add_apply,
      of_apply, ↓reduceIte, and_self, kroneckerMap_apply, one_apply_eq, mul_one, one_mul,
      zero_ne_one, and_true, mul_zero, add_zero, and_false] at e1 e2 e3 e4
    have : (1 : ℂ) = 0 := by linear_combination e1 - e2 - e3 + e4
    exact one_ne_zero this

end Matrices

/-! ## 3. As operators on `ℂ^{ι × (ι × μ)}`, with the conjugate-linear `J` -/

section Operators

open OrderOneNontrivial ConjugatePermutation OppositeFromRealStructure OrderOneRegularBimodule

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

omit [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ] in
theorem genSwap_genSwap (a : ι × (ι × μ)) : genSwap ι μ (genSwap ι μ a) = a := rfl

/-- **The real structure as an operator**: conjugating `matAlg M` by `J = conjPerm (genSwap ι μ)`
— exchange the two `ι` factors, keep the generation index, conjugate the coordinates — is
`matAlg (exchConjGen M)`. -/
theorem conjPerm_genSwap_matAlg (M : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ)
    (v : EuclideanSpace ℂ (ι × (ι × μ))) :
    conjPerm (genSwap ι μ) (matAlg _ M (conjPerm (genSwap ι μ) v)) =
      matAlg _ (exchConjGen M) v := by
  rw [matAlg_apply, matAlg_apply, conjPerm_conj _ genSwap_genSwap]
  rfl

/-- **`J` implements the right action from the left one**: `J π(a⋆) J = 1 ⊗ (aᵀ ⊗ 1)`, CCM's
`πOp_impl` in this model. -/
theorem conjPerm_genSwap_star (a : Matrix ι ι ℂ) (v : EuclideanSpace ℂ (ι × (ι × μ))) :
    conjPerm (genSwap ι μ)
        (matAlg _ (star a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ)) (conjPerm (genSwap ι μ) v)) =
      matAlg _ ((1 : Matrix ι ι ℂ) ⊗ₖ (aᵀ ⊗ₖ (1 : Matrix μ μ ℂ))) v := by
  rw [conjPerm_genSwap_matAlg, exchConjGen_kron_one]
  congr 3
  ext x y
  simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- `J`-invariance of `matAlg M` is `exchConjGen M = M`. -/
theorem jInvGen_matAlg_iff (M : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ) :
    (∀ v, conjPerm (genSwap ι μ) (matAlg _ M (conjPerm (genSwap ι μ) v)) = matAlg _ M v) ↔
      exchConjGen M = M := by
  simp only [conjPerm_genSwap_matAlg]
  constructor
  · intro h
    exact matAlg_injective _ (LinearMap.ext h)
  · intro h v
    rw [h]

/-- **ORDER-ONE AND THE REAL STRUCTURE WITH GENERATIONS, AS OPERATORS.** With `π(a) = a ⊗ 1` and
the right action `1 ⊗ (b ⊗ 1)`, and `J` the conjugate-linear exchange-conjugation keeping the
generation index, an operator satisfies order-one and commutes with `J` iff it is
`matAlg (genPart A + 1 ⊗ Ā)`. -/
theorem orderOne_jInvGen_matAlg_iff (D : Module.End ℂ (EuclideanSpace ℂ (ι × (ι × μ)))) :
    ((∀ a b : Matrix ι ι ℂ, ⁅⁅D, matAlg _ (a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ))⁆,
        matAlg _ ((1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ)))⁆ = 0) ∧
      ∀ v, conjPerm (genSwap ι μ) (D (conjPerm (genSwap ι μ) v)) = D v) ↔
    ∃ A : Matrix (ι × μ) (ι × μ) ℂ,
      D = matAlg _ (genPart A + (1 : Matrix ι ι ℂ) ⊗ₖ A.map (starRingEnd ℂ)) := by
  obtain ⟨M, rfl⟩ := matAlg_surjective' (ι × (ι × μ)) D
  have key : ∀ a b : Matrix ι ι ℂ,
      ⁅⁅matAlg _ M, matAlg _ (a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ))⁆,
          matAlg _ ((1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ)))⁆ = 0 ↔
        ⁅⁅M, a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ)⁆,
          (1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0 := by
    intro a b
    have e := map_lie_lie (matAlg (ι × (ι × μ))) M (a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ))
      ((1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ)))
    constructor
    · intro h
      exact matAlg_injective _ (by rw [map_zero]; exact e.trans h)
    · intro h
      exact e.symm.trans (by rw [h, map_zero])
  simp only [key, jInvGen_matAlg_iff]
  rw [orderOne_exchConjGen_iff]
  exact ⟨fun ⟨A, hA⟩ => ⟨A, by rw [hA]⟩, fun ⟨A, hA⟩ => ⟨A, matAlg_injective _ hA⟩⟩

end Operators

end OrderOneRealGenerations
