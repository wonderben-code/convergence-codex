/-
  KronSumCriterion.lean — which Dirac operators have the tensor-sum shape, decided exactly. Every
  operator satisfying order-one on `ℂ^ι ⊗ (ℂ^κ ⊗ ℂ^μ)` — full matrix algebras on the two slots,
  every vector carrying a generation label from `μ` — is `genPart C + 1 ⊗ B` (unit 232). The
  space splits into two factors in three ways, and each split is decided: the operator is a tensor
  sum across `ι | κ × μ` iff `C` is a Kronecker sum `C₀ ⊗ 1 + 1 ⊗ G`, a part on the slot plus a
  part on the generation; across `κ | ι × μ` iff `B` is one; and across `ι × κ | μ`, the
  generations split off, iff both are. Every matrix on `ι × μ` is a Kronecker sum iff `ι` or `μ`
  has at most one point. So the shape is forced for every order-one operator exactly when `ι` or
  `μ` has at most one point; with the real structure `J` the three splits coincide and the same
  holds; with unit 170's grading on `M₂(ℂ)`, exactly when `μ` has at most one point. Where the
  shape holds the operator is unit 174's `kroneckerSum` and its cutoff trace factorises — into
  three factors when the generations split off — so unit 172's derivation, order-one gives the
  shape and the shape the factorisation, goes through for every operator exactly at those sizes.

  SPINE L19 / `ASSUMPTIONS_LEDGER` 12 — the tensor-sum premise of unit 172's factorisation, now
  decided for every operator of these models and forced exactly at multiplicity one; SPINE L6 /
  `WALLS` §W9 rung 2, second half. Hardening unit 242, 26 September 2026.

  WHY. Unit 232 proved the shape forced at multiplicity one (`orderOne_iff_kronSum_of_unique`)
  and showed by one example at `ι = κ = μ = Fin 2` that order-one does not force it once a piece
  repeats (`exists_orderOne_not_kronSum`); units 234 and 236 showed the same with `J` and with the
  grading, each by one example at size two, and unit 241 decided it for unit 170's model. Examples
  at size two do not say what happens at other sizes, nor which operators have the shape: unit
  232's NOT list says the grouping `(ι × κ) ⊗ μ` is *not tested* and (8) not *carried to `A_F`
  or to a multiplicity of three*, and unit 234's that *only the shape is shown not forced, as in
  unit 232*. The shape is the premise unit 172's factorisation starts from (`ASSUMPTIONS_LEDGER`
  12), so which operators have it is the question that premise asks.

  WHAT IS PROVED.
  (1) `IsKronSum C`: `C = C₀ ⊗ 1 + 1 ⊗ G` for some `C₀`, `G` — on `ι × (κ × μ)`, the tensor-sum
      shape `C ⊗ 1 + 1 ⊗ B` itself. `isKronSum_of_subsingleton_left` and
      `isKronSum_of_subsingleton_right`: every matrix is one when a side has at most one point;
      **`not_isKronSum_single`**: a diagonal matrix unit is not, once both sides have two;
      **`forall_isKronSum_iff`**: every matrix on `ι × μ` is a Kronecker sum iff `ι` or `μ` has at
      most one point. Over any field.
  (2) Order-one alone, over any field, at any `ι`, `κ`, `μ`. **`isKronSum_genPart_add_iff`**:
      `genPart C + 1 ⊗ B` is a tensor sum iff `C` is a Kronecker sum, whatever `B`;
      **`genPart_add_genPartSum_iff`**: it is `genPart C' + 1 ⊗ (B' ⊗ 1)` iff `B` is one, whatever
      `C`; `slotsPart X`, `X` on the two slots and the identity on the generation label, and
      **`genPart_add_slotsSum_iff`**: it is `slotsPart X + 1 ⊗ (1 ⊗ G)` iff `C` and `B` both are.
      **`orderOne_forces_isKronSum_iff`**: every order-one operator is a tensor sum iff `ι` or `μ`
      has at most one point; **`orderOne_forces_genPartSum_iff`**: in the second grouping, iff `κ`
      or `μ` has; **`orderOne_forces_slotsSum_iff`**: in the third, iff both hold;
      **`exists_orderOne_not_kronSum_of_nontrivial`**: with two points in each of `ι`, `κ`, `μ`, an
      order-one operator that is a tensor sum in none of the three groupings — unit 232's
      `exists_orderOne_not_kronSum` at every size.
  (3) With `J`, over `ℂ`, `κ = ι`. `isKronSum_conj_iff`; **`isKronSum_genPart_conj_iff`**,
      **`genPart_conj_genPartSum_iff`** and **`genPart_conj_slotsSum_iff`**: `genPart A + 1 ⊗ Ā`,
      the shape of every operator satisfying order-one and `J` (unit 234's
      `orderOne_exchConjGen_iff`), is a tensor sum in each of the three groupings iff `A` is a
      Kronecker sum — with `J` the three coincide; **`orderOne_jInv_forces_isKronSum_iff`**: every
      such operator is a tensor sum iff `ι` or `μ` has at most one point;
      **`exists_orderOne_jInv_not_kronSum_of_nontrivial`**: with two points in each, a self-adjoint
      one that is a tensor sum in none of the three groupings — unit 234's
      `exists_orderOne_jInv_not_kronSum` at every size.
  (4) With unit 170's grading, `ι = Fin 2`. `not_exists_smul_one_diagSingle`;
      **`gen_fixes_dirac_forces_isKronSum_iff`**: every operator satisfying order-one, `J` and
      anticommutation with the grading is a tensor sum iff `μ` has at most one point;
      **`selfAdj_forces_isKronSum_iff`**: the same for unit 241's self-adjoint solutions;
      **`exists_gen_fixes_dirac_not_kronSum_of_nontrivial`**: with two generations or more, a
      self-adjoint solution that is a tensor sum in none of the three groupings — unit 236's
      `exists_gen_fixes_dirac_not_kronSum` at every multiplicity. These use unit 241's
      `DsymGen_kronSum_iff`, `DsymGen_genPartSum_iff` and `DsymGen_real_kronSum_iff`.
  (5) **`trace_exp_of_isKronSum`**: a Kronecker sum is unit 174's `kroneckerSum`, and
      `trace (exp (t • M))` is `trace (exp (t • C)) * trace (exp (t • B))` for every `t`;
      **`trace_exp_of_orderOne_of_subsingleton`**: with `ι` or `μ` of at most one point, every
      order-one operator — so every one also satisfying `J` — is a `kroneckerSum` whose cutoff
      trace factorises: unit 172's `trace_exp_of_orderOne` with a generation index. By (2) and
      (3) these are the only sizes at which the shape holds for every such operator.
      **`trace_exp_of_orderOne_slotsSum`**: an order-one operator in the third grouping is
      `kroneckerSum C₀ (kroneckerSum B₀ G)`, and its cutoff trace is the product of three traces,
      one for each slot and one for the generations.

  NOT PROVED, said exactly.
  • The trace of the exponential where the shape fails: whether `trace (exp (t • D))` factorises
    for another reason when `C`, or `A`, is not a Kronecker sum is not asked, and nothing here
    computes a spectrum. (5) gives the factorisation unit 174's arrow uses, and no other.
  • Products and sub-bimodules with a generation index — unit 228's `blockKron` with a
    multiplicity — `ℍ` or CCM's `A_F` with generations, and gradings other than unit 170's: each
    slot here carries one full matrix algebra.
  • What `C₀`, `G` or the generation matrix are physically: nothing identifies them with Yukawa
    matrices or masses.
  • The cascade's `D` (the watchlist item *the cascade's `D` AS A TENSOR SUM*, `L40927` today),
    the factor list, a tag: rung 2 is not climbed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `κ` nonempty: `isKronSum_genPart_add_iff`,
  `orderOne_forces_isKronSum_iff`, `trace_exp_of_orderOne_of_subsingleton`. `ι` nonempty:
  `genPart_add_genPartSum_iff`, `orderOne_forces_genPartSum_iff`, `isKronSum_genPart_conj_iff`,
  `genPart_conj_genPartSum_iff`, `genPart_conj_slotsSum_iff`. Both nonempty:
  `genPart_add_slotsSum_iff`, `orderOne_forces_slotsSum_iff`, `trace_exp_of_orderOne_slotsSum`,
  the last with order-one and the third grouping's shape. At most one point:
  `isKronSum_of_subsingleton_left` (`ι`), `isKronSum_of_subsingleton_right` (`μ`),
  `trace_exp_of_orderOne_of_subsingleton` (`ι` or `μ`, with order-one). At least two points:
  `not_isKronSum_single` (`ι`, `μ`), `exists_orderOne_not_kronSum_of_nontrivial` (`ι`, `κ`, `μ`),
  `exists_orderOne_jInv_not_kronSum_of_nontrivial` (`ι`, `μ`),
  `exists_gen_fixes_dirac_not_kronSum_of_nontrivial` (`μ`). `not_exists_smul_one_diagSingle`
  takes two distinct generations; `trace_exp_of_isKronSum` takes `IsKronSum M`. The three
  declarations of (5) take their index types in `Type`, as unit 174's `kroneckerSum` does.
  Everything else takes elements of its types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 26 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration, the file
  list and Mathlib's declarations: none is taken. The nearest statements are unit 174's
  `SpectralCutoffFactorises.kroneckerSum`, whose range `IsKronSum` is; unit 232's
  `orderOne_iff_kronSum_of_unique`, the multiplicity-one case of (2), `orderOne_multiplicity_iff`,
  the shape (2) starts from, and `exists_orderOne_not_kronSum`; unit 234's
  `orderOne_exchConjGen_iff` and `exists_orderOne_jInv_not_kronSum`; unit 236's
  `exists_gen_fixes_dirac_not_kronSum`; unit 241's criteria, which (4) uses; and unit 172's
  `trace_exp_of_orderOne`, of which (5) is the version with a generation index.

  `#print axioms` on all 26 declarations below: `[propext, Classical.choice, Quot.sound]`.
-/

import SelfAdjointDiracCount

open Matrix
open scoped Kronecker

namespace KronSumCriterion

open OrderOneCommutant OrderOneRealGenerations GammaFixesDiracGenerations SelfAdjointDiracCount

/-! ## 1. Kronecker sums, and when every matrix is one -/

section KronSum

variable {ι μ K : Type*} [DecidableEq ι] [DecidableEq μ] [Field K]

/-- `C` on `ι × μ` is a **Kronecker sum**: a part on `ι` alone plus a part on `μ` alone,
`C = C₀ ⊗ 1 + 1 ⊗ G`. On `ι × (κ × μ)` this is the tensor-sum shape `C ⊗ 1 + 1 ⊗ B`. -/
def IsKronSum (C : Matrix (ι × μ) (ι × μ) K) : Prop :=
  ∃ (C₀ : Matrix ι ι K) (G : Matrix μ μ K),
    C = C₀ ⊗ₖ (1 : Matrix μ μ K) + (1 : Matrix ι ι K) ⊗ₖ G

/-- With at most one point on the left, every matrix is a Kronecker sum. -/
theorem isKronSum_of_subsingleton_left [Subsingleton ι] (C : Matrix (ι × μ) (ι × μ) K) :
    IsKronSum C := by
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨x₀⟩⟩
  · exact ⟨0, 0, Matrix.ext fun a _ => hι.elim a.1⟩
  · refine ⟨0, Matrix.of fun i j => C (x₀, i) (x₀, j), ?_⟩
    ext ⟨x, i⟩ ⟨y, j⟩
    rw [Subsingleton.elim x x₀, Subsingleton.elim y x₀]
    simp [kroneckerMap_apply]

/-- With at most one point on the right, every matrix is a Kronecker sum. -/
theorem isKronSum_of_subsingleton_right [Subsingleton μ] (C : Matrix (ι × μ) (ι × μ) K) :
    IsKronSum C := by
  rcases isEmpty_or_nonempty μ with hμ | ⟨⟨i₀⟩⟩
  · exact ⟨0, 0, Matrix.ext fun a _ => hμ.elim a.2⟩
  · refine ⟨Matrix.of fun x y => C (x, i₀) (y, i₀), 0, ?_⟩
    ext ⟨x, i⟩ ⟨y, j⟩
    rw [Subsingleton.elim i i₀, Subsingleton.elim j i₀]
    simp [kroneckerMap_apply]

/-- **A diagonal matrix unit is not a Kronecker sum** once both sides have two points: the four
diagonal entries at `(x₀, i₀)`, `(x₁, i₀)`, `(x₀, i₁)`, `(x₁, i₁)` would give `1 = 0`. -/
theorem not_isKronSum_single [Nontrivial ι] [Nontrivial μ] (x₀ : ι) (i₀ : μ) :
    ¬ IsKronSum (single (x₀, i₀) (x₀, i₀) (1 : K)) := by
  rintro ⟨C₀, G, h⟩
  obtain ⟨x₁, hx⟩ := exists_ne x₀
  obtain ⟨i₁, hi⟩ := exists_ne i₀
  have e1 := congrFun (congrFun h (x₀, i₀)) (x₀, i₀)
  have e2 := congrFun (congrFun h (x₁, i₀)) (x₁, i₀)
  have e3 := congrFun (congrFun h (x₀, i₁)) (x₀, i₁)
  have e4 := congrFun (congrFun h (x₁, i₁)) (x₁, i₁)
  simp only [single_apply, Prod.mk.injEq, add_apply, kroneckerMap_apply, one_apply_eq,
    and_self, if_true, mul_one, one_mul, hx.symm, hi.symm, and_true, and_false,
    if_false] at e1 e2 e3 e4
  have : (1 : K) = 0 := by linear_combination e1 - e2 - e3 + e4
  exact one_ne_zero this

/-- **Every matrix on `ι × μ` is a Kronecker sum iff one side has at most one point.** -/
theorem forall_isKronSum_iff :
    (∀ C : Matrix (ι × μ) (ι × μ) K, IsKronSum C) ↔ Subsingleton ι ∨ Subsingleton μ := by
  constructor
  · intro h
    by_contra hn
    rw [not_or, not_subsingleton_iff_nontrivial, not_subsingleton_iff_nontrivial] at hn
    obtain ⟨_, _⟩ := hn
    exact not_isKronSum_single (Classical.arbitrary ι) (Classical.arbitrary μ) (h _)
  · rintro (_ | _) C
    · exact isKronSum_of_subsingleton_left C
    · exact isKronSum_of_subsingleton_right C

end KronSum

/-! ## 2. Order-one alone: the criterion in both groupings, and the dichotomy -/

section OrderOne

variable {ι κ μ K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Field K]

omit [Fintype ι] [Fintype κ] [Fintype μ] in
/-- **THE CRITERION, FIRST GROUPING**: `genPart C + 1 ⊗ B` — the shape of every order-one
operator (`OrderOneCommutant.orderOne_multiplicity_iff`) — is a tensor sum `C' ⊗ 1 + 1 ⊗ B'`
iff `C` is a Kronecker sum. `B` plays no part. -/
theorem isKronSum_genPart_add_iff [Nonempty κ] (C : Matrix (ι × μ) (ι × μ) K)
    (B : Matrix (κ × μ) (κ × μ) K) :
    IsKronSum (genPart (κ := κ) C + (1 : Matrix ι ι K) ⊗ₖ B) ↔ IsKronSum C := by
  obtain ⟨p₀⟩ := ‹Nonempty κ›
  constructor
  · rintro ⟨C', B', h⟩
    refine ⟨C', Matrix.of fun i j => B' (p₀, i) (p₀, j) - B (p₀, i) (p₀, j), ?_⟩
    ext ⟨x, i⟩ ⟨y, j⟩
    have e := congrFun (congrFun h (x, (p₀, i))) (y, (p₀, j))
    simp only [genPart, add_apply, of_apply, kroneckerMap_apply, one_apply, Prod.mk.injEq,
      true_and, if_true] at e ⊢
    linear_combination e
  · rintro ⟨C₀, G, rfl⟩
    refine ⟨C₀, (1 : Matrix κ κ K) ⊗ₖ G + B, ?_⟩
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    simp only [genPart, add_apply, of_apply, kroneckerMap_apply, one_apply, Prod.mk.injEq]
    rcases eq_or_ne x y with rfl | hxy <;> rcases eq_or_ne p q with rfl | hpq <;>
      rcases eq_or_ne i j with rfl | hij <;> simp [*]
    all_goals ring

omit [Fintype ι] [Fintype κ] [Fintype μ] in
/-- **THE CRITERION, OTHER GROUPING**: `genPart C + 1 ⊗ B` is `genPart C' + 1 ⊗ (B' ⊗ 1)` — an
operator on the left factor with the multiplicity plus one on the right factor alone — iff `B`
is a Kronecker sum. `C` plays no part. -/
theorem genPart_add_genPartSum_iff [Nonempty ι] (C : Matrix (ι × μ) (ι × μ) K)
    (B : Matrix (κ × μ) (κ × μ) K) :
    (∃ (C' : Matrix (ι × μ) (ι × μ) K) (B' : Matrix κ κ K),
        genPart (κ := κ) C + (1 : Matrix ι ι K) ⊗ₖ B =
          genPart (κ := κ) C' + (1 : Matrix ι ι K) ⊗ₖ (B' ⊗ₖ (1 : Matrix μ μ K))) ↔
      IsKronSum B := by
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  constructor
  · rintro ⟨C', B', h⟩
    refine ⟨B', Matrix.of fun i j => C' (x₀, i) (x₀, j) - C (x₀, i) (x₀, j), ?_⟩
    ext ⟨p, i⟩ ⟨q, j⟩
    have e := congrFun (congrFun h (x₀, (p, i))) (x₀, (q, j))
    simp only [genPart, add_apply, of_apply, kroneckerMap_apply, one_apply, if_true,
      one_mul] at e ⊢
    rcases eq_or_ne p q with rfl | hpq
    · simp only [if_true, one_mul] at e ⊢
      linear_combination e
    · simp only [hpq, if_false, zero_add, zero_mul, add_zero] at e ⊢
      exact e
  · rintro ⟨B₀, G, rfl⟩
    refine ⟨C + (1 : Matrix ι ι K) ⊗ₖ G, B₀, ?_⟩
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    simp only [genPart, add_apply, of_apply, kroneckerMap_apply, one_apply]
    rcases eq_or_ne x y with rfl | hxy <;> rcases eq_or_ne p q with rfl | hpq <;>
      rcases eq_or_ne i j with rfl | hij <;> simp [*]
    all_goals ring

/-- **ORDER-ONE FORCES THE TENSOR-SUM SHAPE EXACTLY AT ONE SLOT OR ONE GENERATION**: every
operator satisfying order-one is `C ⊗ 1 + 1 ⊗ B` iff `ι` or `μ` has at most one point. -/
theorem orderOne_forces_isKronSum_iff [Nonempty κ] :
    (∀ D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K,
      (∀ (a : Matrix ι ι K) (b : Matrix κ κ K),
        ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) K)⁆,
          (1 : Matrix ι ι K) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ K))⁆ = 0) → IsKronSum D) ↔
      Subsingleton ι ∨ Subsingleton μ := by
  rw [← forall_isKronSum_iff (K := K)]
  constructor
  · intro h C
    exact (isKronSum_genPart_add_iff C 0).mp
      (h _ ((orderOne_multiplicity_iff _).mpr ⟨C, 0, rfl⟩))
  · intro h D hD
    obtain ⟨C, B, rfl⟩ := (orderOne_multiplicity_iff D).mp hD
    exact (isKronSum_genPart_add_iff C B).mpr (h C)

/-- **AND IN THE OTHER GROUPING**: every operator satisfying order-one is
`genPart C + 1 ⊗ (B ⊗ 1)` iff `κ` or `μ` has at most one point. -/
theorem orderOne_forces_genPartSum_iff [Nonempty ι] :
    (∀ D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K,
      (∀ (a : Matrix ι ι K) (b : Matrix κ κ K),
        ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) K)⁆,
          (1 : Matrix ι ι K) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ K))⁆ = 0) →
        ∃ (C : Matrix (ι × μ) (ι × μ) K) (B : Matrix κ κ K),
          D = genPart C + (1 : Matrix ι ι K) ⊗ₖ (B ⊗ₖ (1 : Matrix μ μ K))) ↔
      Subsingleton κ ∨ Subsingleton μ := by
  rw [← forall_isKronSum_iff (K := K) (ι := κ) (μ := μ)]
  constructor
  · intro h B
    obtain ⟨C', B', e⟩ := h _ ((orderOne_multiplicity_iff _).mpr ⟨0, B, rfl⟩)
    exact (genPart_add_genPartSum_iff 0 B).mp ⟨C', B', e⟩
  · intro h D hD
    obtain ⟨C, B, rfl⟩ := (orderOne_multiplicity_iff D).mp hD
    exact (genPart_add_genPartSum_iff C B).mpr (h B)

omit [Fintype ι] [Fintype κ] [Fintype μ] in
/-- `X` on the two slots and the identity on the generation label: `X ⊗ 1` in the third grouping,
`(ι × κ) ⊗ μ`, written on `ι × (κ × μ)`. -/
def slotsPart (X : Matrix (ι × κ) (ι × κ) K) : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K :=
  Matrix.of fun a b => if a.2.2 = b.2.2 then X (a.1, a.2.1) (b.1, b.2.1) else 0

omit [Fintype ι] [Fintype κ] [Fintype μ] in
/-- **THE CRITERION, THIRD GROUPING**: `genPart C + 1 ⊗ B` is `slotsPart X + 1 ⊗ (1 ⊗ G)` — an
operator on the two slots plus one on the generation label alone — iff `C` AND `B` are Kronecker
sums: iff it is a tensor sum in both other groupings. -/
theorem genPart_add_slotsSum_iff [Nonempty ι] [Nonempty κ] (C : Matrix (ι × μ) (ι × μ) K)
    (B : Matrix (κ × μ) (κ × μ) K) :
    (∃ (X : Matrix (ι × κ) (ι × κ) K) (G : Matrix μ μ K),
        genPart (κ := κ) C + (1 : Matrix ι ι K) ⊗ₖ B =
          slotsPart X + (1 : Matrix ι ι K) ⊗ₖ ((1 : Matrix κ κ K) ⊗ₖ G)) ↔
      IsKronSum C ∧ IsKronSum B := by
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  obtain ⟨p₀⟩ := ‹Nonempty κ›
  constructor
  · rintro ⟨X, G, h⟩
    refine ⟨⟨Matrix.of fun x y => X (x, p₀) (y, p₀),
      Matrix.of fun i j => G i j - B (p₀, i) (p₀, j), ?_⟩,
      ⟨Matrix.of fun p q => X (x₀, p) (x₀, q),
      Matrix.of fun i j => G i j - C (x₀, i) (x₀, j), ?_⟩⟩
    · ext ⟨x, i⟩ ⟨y, j⟩
      have e := congrFun (congrFun h (x, (p₀, i))) (y, (p₀, j))
      simp only [genPart, slotsPart, add_apply, of_apply, kroneckerMap_apply, one_apply, if_true,
        one_mul] at e ⊢
      rcases eq_or_ne i j with rfl | hij <;> simp only [*, if_true, if_false] at e ⊢ <;>
        linear_combination e
    · ext ⟨p, i⟩ ⟨q, j⟩
      have e := congrFun (congrFun h (x₀, (p, i))) (x₀, (q, j))
      simp only [genPart, slotsPart, add_apply, of_apply, kroneckerMap_apply, one_apply, if_true,
        one_mul] at e ⊢
      rcases eq_or_ne i j with rfl | hij <;> rcases eq_or_ne p q with rfl | hpq <;>
        simp only [*, if_true, if_false] at e ⊢ <;> linear_combination e
  · rintro ⟨⟨C₀, G₁, rfl⟩, ⟨B₀, G₂, rfl⟩⟩
    refine ⟨C₀ ⊗ₖ (1 : Matrix κ κ K) + (1 : Matrix ι ι K) ⊗ₖ B₀, G₁ + G₂, ?_⟩
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    simp only [genPart, slotsPart, add_apply, of_apply, kroneckerMap_apply, one_apply]
    rcases eq_or_ne x y with rfl | hxy <;> rcases eq_or_ne p q with rfl | hpq <;>
      rcases eq_or_ne i j with rfl | hij <;> simp [*]
    all_goals ring

/-- **AND THE THIRD GROUPING'S DICHOTOMY**: every operator satisfying order-one is
`slotsPart X + 1 ⊗ (1 ⊗ G)` iff `ι` or `μ`, and `κ` or `μ`, has at most one point. -/
theorem orderOne_forces_slotsSum_iff [Nonempty ι] [Nonempty κ] :
    (∀ D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K,
      (∀ (a : Matrix ι ι K) (b : Matrix κ κ K),
        ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) K)⁆,
          (1 : Matrix ι ι K) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ K))⁆ = 0) →
        ∃ (X : Matrix (ι × κ) (ι × κ) K) (G : Matrix μ μ K),
          D = slotsPart X + (1 : Matrix ι ι K) ⊗ₖ ((1 : Matrix κ κ K) ⊗ₖ G)) ↔
      (Subsingleton ι ∨ Subsingleton μ) ∧ (Subsingleton κ ∨ Subsingleton μ) := by
  rw [← forall_isKronSum_iff (K := K) (ι := ι) (μ := μ),
    ← forall_isKronSum_iff (K := K) (ι := κ) (μ := μ)]
  constructor
  · intro h
    refine ⟨fun C => ?_, fun B => ?_⟩
    · exact ((genPart_add_slotsSum_iff C 0).mp
        (h _ ((orderOne_multiplicity_iff _).mpr ⟨C, 0, rfl⟩))).1
    · exact ((genPart_add_slotsSum_iff 0 B).mp
        (h _ ((orderOne_multiplicity_iff _).mpr ⟨0, B, rfl⟩))).2
  · rintro ⟨hC, hB⟩ D hD
    obtain ⟨C, B, rfl⟩ := (orderOne_multiplicity_iff D).mp hD
    exact (genPart_add_slotsSum_iff C B).mpr ⟨hC C, hB B⟩

/-- **UNIT 232'S EXAMPLE AT EVERY SIZE**: once `ι`, `κ` and `μ` each have two points, some
operator satisfying order-one is a tensor sum in none of the three groupings. -/
theorem exists_orderOne_not_kronSum_of_nontrivial [Nontrivial ι] [Nontrivial κ]
    [Nontrivial μ] :
    ∃ D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) K,
      (∀ (a : Matrix ι ι K) (b : Matrix κ κ K),
        ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) K)⁆,
          (1 : Matrix ι ι K) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ K))⁆ = 0) ∧
      ¬ IsKronSum D ∧
      (∀ (C : Matrix (ι × μ) (ι × μ) K) (B : Matrix κ κ K),
        D ≠ genPart C + (1 : Matrix ι ι K) ⊗ₖ (B ⊗ₖ (1 : Matrix μ μ K))) ∧
      ∀ (X : Matrix (ι × κ) (ι × κ) K) (G : Matrix μ μ K),
        D ≠ slotsPart X + (1 : Matrix ι ι K) ⊗ₖ ((1 : Matrix κ κ K) ⊗ₖ G) := by
  obtain x₀ := Classical.arbitrary ι
  obtain p₀ := Classical.arbitrary κ
  obtain i₀ := Classical.arbitrary μ
  refine ⟨genPart (κ := κ) (single (x₀, i₀) (x₀, i₀) (1 : K)) +
      (1 : Matrix ι ι K) ⊗ₖ single (p₀, i₀) (p₀, i₀) (1 : K),
    (orderOne_multiplicity_iff _).mpr ⟨_, _, rfl⟩, fun h => ?_, fun C B h => ?_,
    fun X G h => ?_⟩
  · exact not_isKronSum_single x₀ i₀ ((isKronSum_genPart_add_iff _ _).mp h)
  · exact not_isKronSum_single p₀ i₀ ((genPart_add_genPartSum_iff _ _).mp ⟨C, B, h⟩)
  · exact not_isKronSum_single x₀ i₀ ((genPart_add_slotsSum_iff _ _).mp ⟨X, G, h⟩).1

end OrderOne

/-! ## 3. With the real structure `J` -/

section Real

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]

omit [Fintype ι] [Fintype μ] in
/-- Conjugating the entries keeps a Kronecker sum one, and loses none. -/
theorem isKronSum_conj_iff (A : Matrix (ι × μ) (ι × μ) ℂ) :
    IsKronSum (A.map (starRingEnd ℂ)) ↔ IsKronSum A := by
  have key : ∀ A : Matrix (ι × μ) (ι × μ) ℂ, IsKronSum A → IsKronSum (A.map (starRingEnd ℂ)) := by
    rintro A ⟨C₀, G, rfl⟩
    refine ⟨C₀.map (starRingEnd ℂ), G.map (starRingEnd ℂ), ?_⟩
    ext ⟨x, i⟩ ⟨y, j⟩
    simp only [map_apply, add_apply, kroneckerMap_apply, one_apply, map_add, map_mul]
    split_ifs <;> simp
  refine ⟨fun h => ?_, key A⟩
  have e : (A.map (starRingEnd ℂ)).map (starRingEnd ℂ) = A := by ext; simp
  simpa only [e] using key _ h

omit [Fintype ι] [Fintype μ] in
/-- **THE CRITERION UNDER ORDER-ONE AND `J`**: `genPart A + 1 ⊗ Ā` — the shape of every operator
satisfying both (`OrderOneRealGenerations.orderOne_exchConjGen_iff`) — is a tensor sum iff `A`
is a Kronecker sum. -/
theorem isKronSum_genPart_conj_iff [Nonempty ι] (A : Matrix (ι × μ) (ι × μ) ℂ) :
    IsKronSum (genPart (κ := ι) A + (1 : Matrix ι ι ℂ) ⊗ₖ A.map (starRingEnd ℂ)) ↔
      IsKronSum A :=
  isKronSum_genPart_add_iff A _

omit [Fintype ι] [Fintype μ] in
/-- **And in the other grouping**, iff `A` is a Kronecker sum. -/
theorem genPart_conj_genPartSum_iff [Nonempty ι] (A : Matrix (ι × μ) (ι × μ) ℂ) :
    (∃ (C : Matrix (ι × μ) (ι × μ) ℂ) (B : Matrix ι ι ℂ),
        genPart (κ := ι) A + (1 : Matrix ι ι ℂ) ⊗ₖ A.map (starRingEnd ℂ) =
          genPart (κ := ι) C + (1 : Matrix ι ι ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix μ μ ℂ))) ↔
      IsKronSum A :=
  (genPart_add_genPartSum_iff A _).trans (isKronSum_conj_iff A)

omit [Fintype ι] [Fintype μ] in
/-- **And in the third grouping**, iff `A` is a Kronecker sum: with `J` the three groupings
coincide. -/
theorem genPart_conj_slotsSum_iff [Nonempty ι] (A : Matrix (ι × μ) (ι × μ) ℂ) :
    (∃ (X : Matrix (ι × ι) (ι × ι) ℂ) (G : Matrix μ μ ℂ),
        genPart (κ := ι) A + (1 : Matrix ι ι ℂ) ⊗ₖ A.map (starRingEnd ℂ) =
          slotsPart X + (1 : Matrix ι ι ℂ) ⊗ₖ ((1 : Matrix ι ι ℂ) ⊗ₖ G)) ↔
      IsKronSum A :=
  (genPart_add_slotsSum_iff A _).trans ⟨fun h => h.1, fun h => ⟨h, (isKronSum_conj_iff A).mpr h⟩⟩

/-- **ORDER-ONE AND `J` FORCE THE TENSOR-SUM SHAPE EXACTLY AT ONE SLOT OR ONE GENERATION.** -/
theorem orderOne_jInv_forces_isKronSum_iff :
    (∀ D : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ,
      ((∀ (a b : Matrix ι ι ℂ), ⁅⁅D, a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ)⁆,
          (1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧ exchConjGen D = D) →
        IsKronSum D) ↔
      Subsingleton ι ∨ Subsingleton μ := by
  rcases isEmpty_or_nonempty ι with hι | _
  · exact ⟨fun _ => Or.inl inferInstance,
      fun _ D _ => ⟨0, 0, Matrix.ext fun a _ => hι.elim a.1⟩⟩
  rw [← forall_isKronSum_iff (K := ℂ) (ι := ι) (μ := μ)]
  constructor
  · intro h A
    exact (isKronSum_genPart_conj_iff A).mp (h _ ((orderOne_exchConjGen_iff _).mpr ⟨A, rfl⟩))
  · intro h D hD
    obtain ⟨A, rfl⟩ := (orderOne_exchConjGen_iff D).mp hD
    exact (isKronSum_genPart_conj_iff A).mpr (h A)

/-- **UNIT 234'S EXAMPLE AT EVERY SIZE**: once `ι` and `μ` each have two points, some
self-adjoint operator satisfying order-one and `J` is a tensor sum in none of the three
groupings. -/
theorem exists_orderOne_jInv_not_kronSum_of_nontrivial [Nontrivial ι] [Nontrivial μ] :
    ∃ D : Matrix (ι × (ι × μ)) (ι × (ι × μ)) ℂ, D.IsHermitian ∧
      ((∀ (a b : Matrix ι ι ℂ), ⁅⁅D, a ⊗ₖ (1 : Matrix (ι × μ) (ι × μ) ℂ)⁆,
          (1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧ exchConjGen D = D) ∧
      ¬ IsKronSum D ∧
      (∀ (C : Matrix (ι × μ) (ι × μ) ℂ) (B : Matrix ι ι ℂ),
        D ≠ genPart C + (1 : Matrix ι ι ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix μ μ ℂ))) ∧
      ∀ (X : Matrix (ι × ι) (ι × ι) ℂ) (G : Matrix μ μ ℂ),
        D ≠ slotsPart X + (1 : Matrix ι ι ℂ) ⊗ₖ ((1 : Matrix ι ι ℂ) ⊗ₖ G) := by
  obtain x₀ := Classical.arbitrary ι
  obtain i₀ := Classical.arbitrary μ
  refine ⟨genPart (κ := ι) (single (x₀, i₀) (x₀, i₀) 1) +
      (1 : Matrix ι ι ℂ) ⊗ₖ (single (x₀, i₀) (x₀, i₀) (1 : ℂ)).map (starRingEnd ℂ), ?_,
    (orderOne_exchConjGen_iff _).mpr ⟨_, rfl⟩,
    fun h => not_isKronSum_single x₀ i₀ ((isKronSum_genPart_conj_iff _).mp h),
    fun C B h => not_isKronSum_single x₀ i₀ ((genPart_conj_genPartSum_iff _).mp ⟨C, B, h⟩),
    fun X G h => not_isKronSum_single x₀ i₀ ((genPart_conj_slotsSum_iff _).mp ⟨X, G, h⟩)⟩
  refine Matrix.IsHermitian.add ?_ ?_
  · rw [Matrix.IsHermitian, genPart_conjTranspose, Matrix.conjTranspose_single, star_one]
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      Matrix.map_single _ _ _ (starRingEnd ℂ), Matrix.conjTranspose_single, map_one, star_one]

end Real

/-! ## 4. With the grading, on unit 170's `M₂(ℂ)` -/

section Graded

variable {μ : Type*} [Fintype μ] [DecidableEq μ]

omit [Fintype μ] in
/-- A diagonal matrix unit is not a multiple of the identity once `μ` has two points. -/
theorem not_exists_smul_one_diagSingle {i₀ i₁ : μ} (h : i₁ ≠ i₀) :
    ¬ ∃ r : ℂ, (diagonal (Pi.single i₀ (1 : ℝ))).map ((↑) : ℝ → ℂ) = r • (1 : Matrix μ μ ℂ) := by
  rintro ⟨r, hr⟩
  have e0 := congrFun (congrFun hr i₀) i₀
  have e1 := congrFun (congrFun hr i₁) i₁
  simp only [map_apply, diagonal_apply_eq, Pi.single_eq_same, Pi.single_eq_of_ne h,
    Complex.ofReal_one, Complex.ofReal_zero, smul_apply, one_apply_eq, smul_eq_mul,
    mul_one] at e0 e1
  exact one_ne_zero (e0.trans e1.symm)

/-- **THE THREE CONDITIONS FORCE THE TENSOR-SUM SHAPE EXACTLY AT ONE GENERATION**: on unit
170's space with a generation label, every operator satisfying order-one, `J` and
anticommutation with the grading is a tensor sum iff `μ` has at most one point. -/
theorem gen_fixes_dirac_forces_isKronSum_iff :
    (∀ D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ,
      ((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ),
          ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)⁆,
            (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧
        exchConjGen D = D ∧ D * gammaGen μ = -(gammaGen μ * D)) → IsKronSum D) ↔
      Subsingleton μ := by
  constructor
  · intro h
    by_contra hμ
    rw [not_subsingleton_iff_nontrivial] at hμ
    obtain ⟨i₀, i₁, hi⟩ := exists_pair_ne μ
    exact not_exists_smul_one_diagSingle hi.symm ((DsymGen_kronSum_iff _).mp
      (h _ ((gen_fixes_dirac _).mpr ⟨diagonal (Pi.single i₀ 1), rfl⟩)))
  · intro _ D hD
    obtain ⟨R, rfl⟩ := (gen_fixes_dirac D).mp hD
    refine (DsymGen_real_kronSum_iff R).mpr ?_
    rcases isEmpty_or_nonempty μ with hμ | ⟨⟨i₀⟩⟩
    · exact ⟨0, Matrix.ext fun i _ => hμ.elim i⟩
    · refine ⟨R i₀ i₀, ?_⟩
      ext i j
      rw [Subsingleton.elim i i₀, Subsingleton.elim j i₀]
      simp

/-- **AND FOR THE SELF-ADJOINT SOLUTIONS**: every one is a tensor sum iff `μ` has at most one
point. -/
theorem selfAdj_forces_isKronSum_iff :
    (∀ D ∈ selfAdjSolutions μ, IsKronSum D) ↔ Subsingleton μ := by
  constructor
  · intro h
    by_contra hμ
    rw [not_subsingleton_iff_nontrivial] at hμ
    obtain ⟨i₀, i₁, hi⟩ := exists_pair_ne μ
    refine not_exists_smul_one_diagSingle hi.symm ((DsymGen_kronSum_iff _).mp (h _ ?_))
    exact Submodule.mem_map.mpr ⟨diagonal (Pi.single i₀ 1), Matrix.isSymm_diagonal _, rfl⟩
  · intro hμ D hD
    exact gen_fixes_dirac_forces_isKronSum_iff.mpr hμ D ((mem_selfAdjSolutions_iff D).mp hD).1

/-- **UNIT 236'S EXAMPLE AT EVERY MULTIPLICITY**: once `μ` has two points, some self-adjoint
operator satisfying the three conditions is a tensor sum in none of the three groupings. -/
theorem exists_gen_fixes_dirac_not_kronSum_of_nontrivial [Nontrivial μ] :
    ∃ D : Matrix (Fin 2 × (Fin 2 × μ)) (Fin 2 × (Fin 2 × μ)) ℂ, D.IsHermitian ∧
      ((∀ (a b : Matrix (Fin 2) (Fin 2) ℂ),
          ⁅⁅D, a ⊗ₖ (1 : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ)⁆,
            (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) ∧
        exchConjGen D = D ∧ D * gammaGen μ = -(gammaGen μ * D)) ∧
      ¬ IsKronSum D ∧
      (∀ (C : Matrix (Fin 2 × μ) (Fin 2 × μ) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ),
        D ≠ genPart C + (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix μ μ ℂ))) ∧
      ∀ (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (G : Matrix μ μ ℂ),
        D ≠ slotsPart X +
          (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ G) := by
  obtain ⟨i₀, i₁, hi⟩ := exists_pair_ne μ
  have hD := (gen_fixes_dirac_selfAdjoint
    (DsymGen ((diagonal (Pi.single i₀ (1 : ℝ))).map ((↑) : ℝ → ℂ)))).mpr
    ⟨_, Matrix.isSymm_diagonal _, rfl⟩
  have hnot : ¬ IsKronSum (DsymGen ((diagonal (Pi.single i₀ (1 : ℝ))).map ((↑) : ℝ → ℂ))) :=
    fun h => not_exists_smul_one_diagSingle hi.symm ((DsymGen_kronSum_iff _).mp h)
  refine ⟨_, hD.2, hD.1, hnot, fun C B h => not_exists_smul_one_diagSingle hi.symm
    ((DsymGen_genPartSum_iff _).mp ⟨C, B, h⟩), fun X G h => hnot ?_⟩
  obtain ⟨A, hA⟩ := (orderOne_exchConjGen_iff _).mp ⟨hD.1.1, hD.1.2.1⟩
  rw [hA] at h ⊢
  exact (isKronSum_genPart_conj_iff A).mpr ((genPart_conj_slotsSum_iff A).mp ⟨X, G, h⟩)

end Graded

/-! ## 5. Where the shape holds, unit 172's factorisation holds -/

section Factorisation

open NormedSpace SpectralCutoffFactorises
open scoped Matrix.Norms.Operator

variable {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- **A Kronecker sum is unit 174's `kroneckerSum`, so its cutoff trace factorises.** -/
theorem trace_exp_of_isKronSum {M : Matrix (ι × μ) (ι × μ) ℂ} (h : IsKronSum M) :
    ∃ (C : Matrix ι ι ℂ) (B : Matrix μ μ ℂ), M = kroneckerSum C B ∧
      ∀ t : ℂ, (exp (t • M)).trace = (exp (t • C)).trace * (exp (t • B)).trace := by
  obtain ⟨C, B, rfl⟩ := h
  exact ⟨C, B, rfl, fun t => trace_exp_smul_kroneckerSum t C B⟩

/-- **UNIT 172'S FACTORISATION WITH A GENERATION INDEX**: with `ι` or `μ` of at most one point,
every operator satisfying order-one — so every one also satisfying `J` — is a `kroneckerSum`
and its cutoff trace factorises. By `orderOne_forces_isKronSum_iff` these are the only sizes at
which the shape holds for every such operator. -/
theorem trace_exp_of_orderOne_of_subsingleton [Nonempty κ]
    (hs : Subsingleton ι ∨ Subsingleton μ) (D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) ℂ)
    (hD : ∀ (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ),
      ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) ℂ)⁆,
        (1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0) :
    ∃ (C : Matrix ι ι ℂ) (B : Matrix (κ × μ) (κ × μ) ℂ), D = kroneckerSum C B ∧
      ∀ t : ℂ, (exp (t • D)).trace = (exp (t • C)).trace * (exp (t • B)).trace :=
  trace_exp_of_isKronSum (orderOne_forces_isKronSum_iff.mpr hs D hD)

/-- **IN THE THIRD GROUPING THE GENERATIONS FACTOR OUT**: an order-one operator of the shape
`slotsPart X + 1 ⊗ (1 ⊗ G)` is `kroneckerSum C₀ (kroneckerSum B₀ G')`, and its cutoff trace is a
product of three — one factor for each slot and one for the generations. -/
theorem trace_exp_of_orderOne_slotsSum [Nonempty ι] [Nonempty κ]
    (D : Matrix (ι × (κ × μ)) (ι × (κ × μ)) ℂ)
    (hD : ∀ (a : Matrix ι ι ℂ) (b : Matrix κ κ ℂ),
      ⁅⁅D, a ⊗ₖ (1 : Matrix (κ × μ) (κ × μ) ℂ)⁆,
        (1 : Matrix ι ι ℂ) ⊗ₖ (b ⊗ₖ (1 : Matrix μ μ ℂ))⁆ = 0)
    (h3 : ∃ (X : Matrix (ι × κ) (ι × κ) ℂ) (G : Matrix μ μ ℂ),
      D = slotsPart X + (1 : Matrix ι ι ℂ) ⊗ₖ ((1 : Matrix κ κ ℂ) ⊗ₖ G)) :
    ∃ (C₀ : Matrix ι ι ℂ) (B₀ : Matrix κ κ ℂ) (G : Matrix μ μ ℂ),
      D = kroneckerSum C₀ (kroneckerSum B₀ G) ∧
      ∀ t : ℂ, (exp (t • D)).trace =
        (exp (t • C₀)).trace * (exp (t • B₀)).trace * (exp (t • G)).trace := by
  obtain ⟨C, B, rfl⟩ := (orderOne_multiplicity_iff D).mp hD
  obtain ⟨⟨C₀, G₁, rfl⟩, ⟨B₀, G₂, rfl⟩⟩ := (genPart_add_slotsSum_iff C B).mp h3
  have e : genPart (κ := κ) (C₀ ⊗ₖ (1 : Matrix μ μ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ G₁) +
      (1 : Matrix ι ι ℂ) ⊗ₖ (B₀ ⊗ₖ (1 : Matrix μ μ ℂ) + (1 : Matrix κ κ ℂ) ⊗ₖ G₂) =
        kroneckerSum C₀ (kroneckerSum B₀ (G₁ + G₂)) := by
    ext ⟨x, p, i⟩ ⟨y, q, j⟩
    simp only [kroneckerSum, genPart, add_apply, of_apply, kroneckerMap_apply, one_apply]
    rcases eq_or_ne x y with rfl | hxy <;> rcases eq_or_ne p q with rfl | hpq <;>
      rcases eq_or_ne i j with rfl | hij <;> simp [*]
    all_goals ring
  refine ⟨C₀, B₀, G₁ + G₂, e, fun t => ?_⟩
  rw [e, trace_exp_smul_kroneckerSum, trace_exp_smul_kroneckerSum, mul_assoc]

end Factorisation

end KronSumCriterion
