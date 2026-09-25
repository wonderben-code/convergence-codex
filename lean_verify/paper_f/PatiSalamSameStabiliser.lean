/-
  PatiSalamSameStabiliser.lean — WHICH VACUA LEAVE EXACTLY THE SAME UNBROKEN GROUP. At the first
  stage the stabiliser determines the vacuum up to scale: a `(4, 1, 2)` vacuum has exactly the
  stabiliser of `vac` if and only if it is a nonzero multiple of `vac`
  (`stabilizer_eq_stabilizer_vac_iff`). At the second stage it does not: a pair has exactly the
  stabiliser of `(vac, vacEW)` if and only if its first field is a nonzero multiple of `vac` and its
  second a nonzero diagonal `diag(κ, κ')` (`stabilizer_pair_eq_iff`), and its stabiliser is a
  conjugate of that group exactly when the pair is a gauge transform of such a pair
  (`stabilizer_conj_iff`).

  SPINE link L15 (Higgs sector, PARTIAL); `ASSUMPTIONS_LEDGER` 60; `ERRATUM 690`. Hardening unit
  207, 2026-09-25.

  WHY. `PatiSalamVacuumStabiliser`'s header and `ASSUMPTIONS_LEDGER` 60 say *a different vector has
  a different stabiliser*, and the ledger's unit-203 amendment says this *stays true of the
  subgroup, since a conjugate is a different subgroup*. As written both are false: every nonzero
  multiple of `vac` is a different vector with the same stabiliser
  (`PatiSalamVacuumOrbit.stabilizer_smul_of_ne_zero`, unit 203), and `-vac` is one in `vac`'s own
  orbit (`exists_smul_vac_ne_stabilizer_eq`), so a conjugate can be the same subgroup.
  `PatiSalamStabiliserGroup`'s header says *a vector of another orbit type has another stabiliser*:
  true by definition if an orbit type is a conjugacy class of stabilisers, false in the sense the
  estate later gave the words (unit 203: rank one, aligned), since `diag(0, 1)` is not aligned with
  `vac` and leaves the same subgroup (unit 205). This file proves what is true instead.

  WHAT IS PROVED.
  (1) The first stage. Two diagonal elements of `U(3)`, `diag(i, 1, 1)` and `diag(1, i, 1)`
      (`diagU3`, `u3ToStage1_diagU3_smul_apply`), already force a bidoublet they fix to be a
      multiple of `vac` (`eq_smul_vac_of_forall_fixed`). Hence
      **`forall_mem_stabilizer_vac_fixes_iff`** — the vectors the unbroken group fixes are the
      multiples of `vac` — and **`stabilizer_eq_stabilizer_vac_iff`**, with `negOneSU2` ruling out
      `0`. `exists_smul_vac_ne_stabilizer_eq`: `(1, -1)` moves `vac` to `-vac`, and the stabiliser
      does not move.
  (2) The second stage. `diag(i, 1, 1)` forces an electroweak bidoublet fixed by the unbroken group
      to be diagonal (`eq_vacKK_of_forall_fixed`). Hence **`forall_mem_stabilizer_pair_fixes_iff`**
      — the pairs the unbroken group fixes, that is the vacuum values that leave all of it unbroken,
      are the `(c • vac, diag(κ, κ'))` — and **`stabilizer_pair_eq_iff`**, with `negOneSU4` and
      `negOneSU2` ruling out `c = 0` and `(κ, κ') = 0`. `exists_ne_smul_vacEW_stabilizer_eq`:
      `diag(0, 1)` is no multiple of `vacEW` and has the same stabiliser.
  (3) **`stabilizer_conj_iff`** — the orbit type of `(vac, vacEW)` in the technical sense: a pair's
      stabiliser is a conjugate of the unbroken group, `(stabilizer (vac, vacEW)).map (conj g)`,
      exactly when the pair is `g • (c • vac, diag(κ, κ'))` with `c ≠ 0` and `(κ, κ') ≠ 0`.
  (4) The Lie algebra, for `PatiSalamVacuumStabiliser`'s own `stab`: `act_smul_vec` (`act` is
      complex-linear in the vector) and `mem_stab_iff_act_smul_vac` — the elements of
      `su(4) ⊕ su(2)_R` annihilating `c • vac` are exactly `stab`, for every `c ≠ 0`.

  NOT PROVED, said exactly.
  • Which pairs have a stabiliser merely ISOMORPHIC to `U(3)`: (3) finds the conjugates of the
    unbroken group, and an isomorphic subgroup need not be a conjugate. At the first stage unit 204
    settles the question (rank one); at the second it stays open.
    ⚠ 25 September 2026 (hardening unit 221, `paper_f/PatiSalamJointCount.lean`): at the second
    stage, with the first vacuum `vac`, every `Φ ≠ 0` with orthogonal columns leaves `U(3)`
    (`nonempty_stabilizer_pair_equiv_U3_of_orthogonal`), and every other an eight-dimensional joint
    unbroken subalgebra (`finrank_jointStabAt_vac`); whether any of those leaves a group isomorphic
    to `U(3)` stays open. Kept as written (`ERRATUM 94`).
  • The Lie-algebra form of (1): that `stab` determines the line through `vac` is not stated; (4)
    is rescaling only.
  • Why the vacua have these shapes (no potential); masses.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `diagU3`, `u3ToStage1_diagU3_smul_apply` and
  `u3ToFull_diagU3_smul_snd_apply` take entries of modulus one; `eq_zero_of_mul_eq_self` takes
  `m ≠ 1`; the two `forall_fixed` lemmas take a vector fixed by every element of the image of
  `U(3)`; `mem_stab_iff_act_smul_vac` takes `c ≠ 0`; `stabilizer_smul_congr` takes an equality of
  stabilisers. Nothing else takes a hypothesis.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 27 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list. One short name was taken, `act_smul`, by `LovelockEquivariance` (a curvature lemma), so this
  file's is `act_smul_vec`; none of the rest is. The pinned Mathlib supplies
  `MulAction.stabilizer_smul_eq_stabilizer_map_conj`, used for (3).

  0 sorry. 0 new axioms. `#print axioms` on all 27 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamTwoComponentVacuum

open Matrix

namespace PatiSalamSameStabiliser

open PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup PatiSalamVacuumOrbit PatiSalamTwoComponentVacuum

/-- A diagonal element of `U(3)`: `diag(v₀, v₁, v₂)` with every `vᵢ` of modulus one. -/
noncomputable def diagU3 (v : Fin 3 → ℂ) (hv : ∀ i, star (v i) * v i = 1) : GroupU3 :=
  ⟨diagonal v, by
    rw [Matrix.mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    ext i
    exact hv i⟩

theorem blockDiag4_diagonal (v : Fin 3 → ℂ) (c : ℂ) :
    blockDiag4 (diagonal v) c = diagonal ![v 0, v 1, v 2, c] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem u3ToStage1_diagU3_smul_apply (v : Fin 3 → ℂ) (hv : ∀ i, star (v i) * v i = 1)
    (X : Bidoublet) (i : Fin 4) (j : Fin 2) :
    (u3ToStage1 (diagU3 v hv) • X) i j
      = ![v 0, v 1, v 2, star (v 0 * v 1 * v 2)] i * X i j
        * ![v 0 * v 1 * v 2, star (v 0 * v 1 * v 2)] j := by
  rw [stage1_smul_def, stage1Act]
  simp only [u3ToStage1, MonoidHom.coe_mk, OneHom.coe_mk, su4Part, su2Part, diagU3, det_diagonal,
    Fin.prod_univ_three, blockDiag4_diagonal, diagConj2, diagonal_transpose, diagonal_mul,
    mul_diagonal]

theorem u3ToFull_diagU3_smul_snd_apply (v : Fin 3 → ℂ) (hv : ∀ i, star (v i) * v i = 1)
    (p : Bidoublet × EWBidoublet) (i j : Fin 2) :
    (u3ToFull (diagU3 v hv) • p).2 i j
      = ![v 0 * v 1 * v 2, star (v 0 * v 1 * v 2)] i * p.2 i j
        * star (![v 0 * v 1 * v 2, star (v 0 * v 1 * v 2)] j) := by
  rw [full_smul_snd, stage2_smul_def, stage2Act]
  simp only [u3ToFull_apply, u3ToStage1, MonoidHom.coe_mk, OneHom.coe_mk, su2Part, diagU3,
    det_diagonal, Fin.prod_univ_three, diagConj2, star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul, mul_diagonal, Pi.star_apply]

theorem u3ToFull_smul_fst (A : GroupU3) (p : Bidoublet × EWBidoublet) :
    (u3ToFull A • p).1 = u3ToStage1 A • p.1 := rfl

theorem eq_zero_of_mul_eq_self {m x : ℂ} (hm : m ≠ 1) (h : m * x = x) : x = 0 := by
  have h' : (m - 1) * x = 0 := by rw [sub_mul, h, one_mul, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hm)

theorem diagI_mem : ∀ i, star (![Complex.I, 1, 1] i) * ![Complex.I, 1, 1] i = 1 := by
  intro i; fin_cases i <;> simp

theorem diagI'_mem : ∀ i, star (![1, Complex.I, 1] i) * ![1, Complex.I, 1] i = 1 := by
  intro i; fin_cases i <;> simp

theorem eq_smul_vac_of_forall_fixed (X : Bidoublet) (h : ∀ A : GroupU3, u3ToStage1 A • X = X) :
    X = X 3 0 • vac := by
  have key : ∀ (v : Fin 3 → ℂ) (hv : ∀ i, star (v i) * v i = 1) (i : Fin 4) (j : Fin 2),
      ![v 0, v 1, v 2, star (v 0 * v 1 * v 2)] i * ![v 0 * v 1 * v 2, star (v 0 * v 1 * v 2)] j
        ≠ 1 → X i j = 0 := by
    intro v hv i j hm
    have e := congrFun (congrFun (h (diagU3 v hv)) i) j
    rw [u3ToStage1_diagU3_smul_apply, mul_right_comm] at e
    exact eq_zero_of_mul_eq_self hm e
  have h1 := key _ diagI_mem
  have h2 := key _ diagI'_mem
  ext i j
  fin_cases i <;> fin_cases j
  · simp [vac, h1 0 0 (by simp [Complex.ext_iff]; norm_num)]
  · simp [vac, h2 0 1 (by simp [Complex.ext_iff])]
  · simp [vac, h1 1 0 (by simp [Complex.ext_iff])]
  · simp [vac, h1 1 1 (by simp [Complex.ext_iff])]
  · simp [vac, h1 2 0 (by simp [Complex.ext_iff])]
  · simp [vac, h1 2 1 (by simp [Complex.ext_iff])]
  · simp [vac]
  · simp [vac, h1 3 1 (by simp [Complex.ext_iff]; norm_num)]

theorem eq_vacKK_of_forall_fixed (p : Bidoublet × EWBidoublet)
    (h : ∀ A : GroupU3, u3ToFull A • p = p) : p.2 = vacKK (p.2 0 0) (p.2 1 1) := by
  have key : ∀ (v : Fin 3 → ℂ) (hv : ∀ i, star (v i) * v i = 1) (i j : Fin 2),
      ![v 0 * v 1 * v 2, star (v 0 * v 1 * v 2)] i
        * star (![v 0 * v 1 * v 2, star (v 0 * v 1 * v 2)] j) ≠ 1 → p.2 i j = 0 := by
    intro v hv i j hm
    have e := congrFun (congrFun (congrArg Prod.snd (h (diagU3 v hv))) i) j
    rw [u3ToFull_diagU3_smul_snd_apply, mul_right_comm] at e
    exact eq_zero_of_mul_eq_self hm e
  have h1 := key _ diagI_mem
  ext i j
  fin_cases i <;> fin_cases j
  · simp [vacKK]
  · simp [vacKK, h1 0 1 (by simp [Complex.ext_iff]; norm_num)]
  · simp [vacKK, h1 1 0 (by simp [Complex.ext_iff]; norm_num)]
  · simp [vacKK]

/-- `-1` in `SU(4)`: unitary, with determinant `(-1)⁴ = 1`. -/
noncomputable def negOneSU4 : specialUnitaryGroup (Fin 4) ℂ :=
  ⟨-1, mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr
    (by rw [star_neg, star_one, neg_mul_neg, mul_one]),
    by rw [det_neg, det_one, Fintype.card_fin]; norm_num⟩⟩

/-- `-1` in `SU(2)`: unitary, with determinant `(-1)² = 1`. -/
noncomputable def negOneSU2 : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨-1, mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr
    (by rw [star_neg, star_one, neg_mul_neg, mul_one]),
    by rw [det_neg, det_one, Fintype.card_fin]; norm_num⟩⟩

theorem stage1_smul_zero (g : Stage1Group) : g • (0 : Bidoublet) = 0 := by
  rw [stage1_smul_def, stage1Act, Matrix.mul_zero, Matrix.zero_mul]

theorem stage2_smul_zero (g : Stage2Group) : g • (0 : EWBidoublet) = 0 := by
  rw [stage2_smul_def, stage2Act, Matrix.mul_zero, Matrix.zero_mul]

theorem negOneSU2_smul_vac : ((1, negOneSU2) : Stage1Group) • vac = -vac := by
  rw [stage1_smul_def, stage1Act]
  simp [negOneSU2]

theorem neg_vac_ne_vac : -vac ≠ vac := fun h => by
  have := congrFun (congrFun h 3) 0
  norm_num [vac] at this

/-- **THE FIRST-STAGE STABILISER DETERMINES THE VACUUM UP TO SCALE**: a first-stage vacuum has
exactly the stabiliser of `vac` if and only if it is a nonzero multiple of `vac`. -/
theorem stabilizer_eq_stabilizer_vac_iff (X : Bidoublet) :
    MulAction.stabilizer Stage1Group X = MulAction.stabilizer Stage1Group vac ↔
      ∃ c : ℂ, c ≠ 0 ∧ X = c • vac := by
  constructor
  · intro h
    have hfix : ∀ A : GroupU3, u3ToStage1 A • X = X := fun A => by
      have hA := u3ToStage1_mem A
      rw [← h] at hA
      exact MulAction.mem_stabilizer_iff.mp hA
    refine ⟨X 3 0, fun h0 => ?_, eq_smul_vac_of_forall_fixed X hfix⟩
    have hX : X = 0 := by rw [eq_smul_vac_of_forall_fixed X hfix, h0, zero_smul]
    have hg : ((1, negOneSU2) : Stage1Group) ∈ MulAction.stabilizer Stage1Group X := by
      rw [MulAction.mem_stabilizer_iff, hX, stage1_smul_zero]
    rw [h, MulAction.mem_stabilizer_iff, negOneSU2_smul_vac] at hg
    exact neg_vac_ne_vac hg
  · rintro ⟨c, hc, rfl⟩
    exact stabilizer_smul_of_ne_zero hc vac

/-- **A DIFFERENT VECTOR WITH THE SAME STABILISER, IN `vac`'s OWN ORBIT**: `(1, -1)` moves `vac` to
`-vac`, and the stabiliser does not move. -/
theorem exists_smul_vac_ne_stabilizer_eq :
    ∃ g : Stage1Group, g • vac ≠ vac ∧
      MulAction.stabilizer Stage1Group (g • vac) = MulAction.stabilizer Stage1Group vac := by
  refine ⟨(1, negOneSU2), ?_, ?_⟩
  · rw [negOneSU2_smul_vac]
    exact neg_vac_ne_vac
  · rw [negOneSU2_smul_vac, ← neg_one_smul ℂ vac]
    exact stabilizer_smul_of_ne_zero (by norm_num) vac

/-- **THE VECTORS THE FIRST-STAGE UNBROKEN GROUP FIXES** are the multiples of `vac`. -/
theorem forall_mem_stabilizer_vac_fixes_iff (X : Bidoublet) :
    (∀ g ∈ MulAction.stabilizer Stage1Group vac, g • X = X) ↔ ∃ c : ℂ, X = c • vac := by
  constructor
  · intro h
    exact ⟨X 3 0, eq_smul_vac_of_forall_fixed X fun A => h _ (u3ToStage1_mem A)⟩
  · rintro ⟨c, rfl⟩ g hg
    rw [stage1_smul_smul, MulAction.mem_stabilizer_iff.mp hg]

theorem vacKK_zero_zero : vacKK 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vacKK]

/-- **THE TWO-STAGE STABILISER DETERMINES THE VACUA EXACTLY UP TO THE NEUTRAL PLANE**: a pair has
exactly the stabiliser of `(vac, vacEW)` if and only if its first field is a nonzero multiple of
`vac` and its second is a nonzero diagonal `diag(κ, κ')`. -/
theorem stabilizer_pair_eq_iff (p : Bidoublet × EWBidoublet) :
    MulAction.stabilizer FullGroup p = MulAction.stabilizer FullGroup (vac, vacEW) ↔
      (∃ c : ℂ, c ≠ 0 ∧ p.1 = c • vac) ∧ ∃ κ κ' : ℂ, (κ ≠ 0 ∨ κ' ≠ 0) ∧ p.2 = vacKK κ κ' := by
  constructor
  · intro h
    have hfix : ∀ A : GroupU3, u3ToFull A • p = p := fun A => by
      have hA := u3ToFull_mem A
      rw [← h] at hA
      exact MulAction.mem_stabilizer_iff.mp hA
    have h1 := eq_smul_vac_of_forall_fixed p.1 fun A => by rw [← u3ToFull_smul_fst, hfix A]
    have h2 := eq_vacKK_of_forall_fixed p hfix
    refine ⟨⟨p.1 3 0, fun h0 => ?_, h1⟩, p.2 0 0, p.2 1 1, ?_, h2⟩
    · have hg : ((negOneSU4, 1, 1) : FullGroup) ∈ MulAction.stabilizer FullGroup p := by
        rw [MulAction.mem_stabilizer_iff]
        refine Prod.ext ?_ ?_
        · rw [full_smul_fst, h1, h0, zero_smul, stage1_smul_zero]
        · rw [full_smul_snd]
          exact one_smul _ _
      rw [h, MulAction.mem_stabilizer_iff] at hg
      have e := congrFun (congrFun (congrArg Prod.fst hg) 3) 0
      norm_num [full_smul_def, fullAct, stage1Act, negOneSU4, vac] at e
    · by_contra hκ
      simp only [ne_eq, not_or, not_not] at hκ
      have hΦ : p.2 = 0 := by rw [h2, hκ.1, hκ.2, vacKK_zero_zero]
      have hg : ((1, negOneSU2, 1) : FullGroup) ∈ MulAction.stabilizer FullGroup p := by
        rw [MulAction.mem_stabilizer_iff]
        refine Prod.ext ?_ ?_
        · rw [full_smul_fst]
          exact one_smul _ _
        · rw [full_smul_snd, hΦ, stage2_smul_zero]
      rw [h, MulAction.mem_stabilizer_iff] at hg
      have e := congrFun (congrFun (congrArg Prod.snd hg) 0) 0
      norm_num [full_smul_def, fullAct, stage2Act, negOneSU2, vacEW] at e
  · rintro ⟨⟨c, hc, h1⟩, κ, κ', hκ, h2⟩
    have hp : p = (c • vac, (1 : ℂ) • vacKK κ κ') := by rw [one_smul, ← h1, ← h2]
    rw [hp]
    exact (stabilizer_pair_smul hc one_ne_zero (vac, vacKK κ κ')).trans (stabilizer_vacKK_eq hκ)

/-- **At the second stage the stabiliser does not determine the vacuum even up to scale**:
`diag(0, 1)` is no multiple of `vacEW` and leaves the same subgroup. -/
theorem exists_ne_smul_vacEW_stabilizer_eq :
    ∃ Φ : EWBidoublet, (∀ c : ℂ, Φ ≠ c • vacEW) ∧
      MulAction.stabilizer FullGroup (vac, Φ) = MulAction.stabilizer FullGroup (vac, vacEW) := by
  refine ⟨vacKK 0 1, fun c h => ?_, stabilizer_vacKK_eq (Or.inr one_ne_zero)⟩
  have e := congrFun (congrFun h 1) 1
  simp [vacKK, vacEW] at e

/-- **THE VECTORS THE UNBROKEN GROUP FIXES**: the multiples of `vac`, with any diagonal
`diag(κ, κ')` — the directions a vacuum value can take without breaking `U(3)` further. -/
theorem forall_mem_stabilizer_pair_fixes_iff (p : Bidoublet × EWBidoublet) :
    (∀ g ∈ MulAction.stabilizer FullGroup (vac, vacEW), g • p = p) ↔
      (∃ c : ℂ, p.1 = c • vac) ∧ ∃ κ κ' : ℂ, p.2 = vacKK κ κ' := by
  constructor
  · intro h
    have hfix : ∀ A : GroupU3, u3ToFull A • p = p := fun A => h _ (u3ToFull_mem A)
    exact ⟨⟨p.1 3 0, eq_smul_vac_of_forall_fixed p.1 fun A => by
      rw [← u3ToFull_smul_fst, hfix A]⟩, p.2 0 0, p.2 1 1, eq_vacKK_of_forall_fixed p hfix⟩
  · rintro ⟨⟨c, h1⟩, κ, κ', h2⟩ g hg
    have hg1 := ((mem_stabilizer_pair_iff g).mp hg).1
    refine Prod.ext ?_ ?_
    · rw [full_smul_fst, h1, stage1_smul_smul, MulAction.mem_stabilizer_iff.mp hg1]
    · rw [full_smul_snd, h2]
      by_cases hκ : κ ≠ 0 ∨ κ' ≠ 0
      · rw [← stabilizer_vacKK_eq hκ, MulAction.mem_stabilizer_iff] at hg
        exact congrArg Prod.snd hg
      · simp only [ne_eq, not_or, not_not] at hκ
        rw [hκ.1, hκ.2, vacKK_zero_zero, stage2_smul_zero]

theorem stabilizer_smul_congr {a b : Bidoublet × EWBidoublet} (h : FullGroup)
    (hab : MulAction.stabilizer FullGroup a = MulAction.stabilizer FullGroup b) :
    MulAction.stabilizer FullGroup (h • a) = MulAction.stabilizer FullGroup (h • b) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj, hab]

/-- **THE ORBIT TYPE, IN THE TECHNICAL SENSE**: a pair's stabiliser is a conjugate of the unbroken
group exactly when the pair is a gauge transform of `(c • vac, diag(κ, κ'))` with `c ≠ 0` and
`(κ, κ') ≠ 0`. -/
theorem stabilizer_conj_iff (p : Bidoublet × EWBidoublet) :
    (∃ g : FullGroup, MulAction.stabilizer FullGroup p =
        (MulAction.stabilizer FullGroup (vac, vacEW)).map (MulAut.conj g).toMonoidHom) ↔
      ∃ g : FullGroup, ∃ c κ κ' : ℂ, c ≠ 0 ∧ (κ ≠ 0 ∨ κ' ≠ 0) ∧
        p = g • (c • vac, vacKK κ κ') := by
  simp_rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  constructor
  · rintro ⟨g, hg⟩
    have h := stabilizer_smul_congr g⁻¹ hg
    rw [inv_smul_smul] at h
    obtain ⟨⟨c, hc, h1⟩, κ, κ', hκ, h2⟩ := (stabilizer_pair_eq_iff _).mp h
    exact ⟨g, c, κ, κ', hc, hκ, inv_smul_eq_iff.mp (Prod.ext h1 h2)⟩
  · rintro ⟨g, c, κ, κ', hc, hκ, rfl⟩
    exact ⟨g, stabilizer_smul_congr g ((stabilizer_pair_eq_iff _).mpr
      ⟨⟨c, hc, rfl⟩, κ, κ', hκ, rfl⟩)⟩

/-- `act` is complex-linear in the vector. -/
theorem act_smul_vec (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (X : Bidoublet) : act A B (c • X) = c • act A B X := by
  rw [act, act, Matrix.mul_smul, Matrix.smul_mul, smul_add]

/-- **The Lie-algebra stabiliser does not see rescaling either**: for `c ≠ 0`, the elements of
`su(4) ⊕ su(2)_R` that annihilate `c • vac` are exactly `stab`. -/
theorem mem_stab_iff_act_smul_vac {c : ℂ} (hc : c ≠ 0) (p : PSLie) :
    p ∈ stab ↔ act (mat4 p.1) (mat2 p.2) (c • vac) = 0 := by
  rw [act_smul_vec, smul_eq_zero, or_iff_right hc, stab, LinearMap.mem_ker]
  rfl

end PatiSalamSameStabiliser
