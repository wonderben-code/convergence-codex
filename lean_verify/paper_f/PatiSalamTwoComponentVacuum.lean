/-
  PatiSalamTwoComponentVacuum.lean — the second-stage Higgs vacuum of the physics literature is
  not the estate's `vacEW = diag(1, 0)` but `diag(κ, κ')`, the bidoublet's two neutral components
  (`vacKK`). For every `(κ, κ') ≠ (0, 0)` the unbroken group is the SAME SUBGROUP of
  `SU(4) × SU(2)_L × SU(2)_R` as for `(vac, vacEW)` (`stabilizer_vacKK_eq`), hence `U(3)`
  (`nonempty_stabilizer_vacKK_equiv_U3`). When both entries are nonzero the vacuum has rank two
  (`rank_vacKK`), outside unit 203's aligned family; and `diag(0, 1)` is not aligned with `vac`
  at all (`not_aligned_vac_vacKK_zero_one`), so ALIGNMENT IS SUFFICIENT AND NOT NECESSARY
  (`exists_not_aligned_stabilizer_equiv_U3`).

  SPINE link L15 (Higgs sector, PARTIAL); `ASSUMPTIONS_LEDGER` 60. Units 203 and 204 left the second
  stage's necessity question open; this file settles it one way — alignment is not necessary — and
  removes the hypothesis `κ' = 0` from the estate's electroweak vacuum. Hardening unit 205,
  2026-09-25.

  WHAT IS PROVED.
  (1) **`mem_stabilizer_vacKK_iff`**: for a gauge element whose `(SU(4), SU(2)_R)` part fixes
      `vac`, the pair `(SU(2)_L, SU(2)_R)` fixes `diag(κ, κ') ≠ 0` iff its two `SU(2)` components
      are equal. Unit 199's `exists_u3ToStage1_eq` gives `SU(2)_R = diag(d, d̄)`; a nonzero entry of
      `diag(κ, κ')` then pins one column of the `SU(2)_L` matrix (`eq_diagConj2_of` for the first,
      `eq_diagConj2_of_col1` for the second); the converse is diagonal algebra
      (`diagConj2_mul_star`, `star_diagConj2_mul`).
  (2) **`stabilizer_vacKK_eq`**: `stabilizer (vac, diag(κ, κ')) = stabilizer (vac, vacEW)` for every
      `(κ, κ') ≠ 0` — the condition in (1) does not depend on `κ, κ'` (`vacEW = diag(1, 0)`,
      `vacEW_eq_vacKK`; membership of a joint stabiliser, `mem_stabilizer_pair_iff'`). Hence
      `nonempty_stabilizer_vacKK_equiv_U3`, through unit 199's `stabilizerPairEquivU3`.
  (3) **`rank_vacKK`**: `diag(κ, κ')` has rank two when `κ, κ' ≠ 0`, so it is outside unit 203's
      aligned family, whose second fields are pure tensors (`not_aligned_vac_vacKK`).
  (4) **`not_aligned_vac_vacKK_zero_one`** and **`exists_not_aligned_stabilizer_equiv_U3`**: a
      second-stage vacuum outside unit 203's aligned family still leaves `U(3)` unbroken.

  NOT PROVED, said exactly.
  • A classification of all second-stage vacua: which `Φ` leave `U(3)` unbroken beside the diagonal
    ones is not decided; nothing here says a vacuum with off-diagonal entries does not.
  • The first-stage vacuum is `vac` itself; other rank-one first-stage vacua are covered only by
    conjugation, as in unit 203, and that transport is not written for this file's statements.
  • Why the vacua have these shapes (no potential); the magnitudes; topology.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `eq_diagConj2_of_col1` takes `h ∈ SU(2)`,
  `d * star d = 1`, `h 1 1 = star d` and `h 0 1 = 0`; `diagConj2_mul_star` and
  `star_diagConj2_mul` take `d * star d = 1`; `mem_stabilizer_vacKK_iff` takes `κ ≠ 0 ∨ κ' ≠ 0`
  and the element's first-stage part in `vac`'s stabiliser; `stabilizer_vacKK_eq` and
  `nonempty_stabilizer_vacKK_equiv_U3` take `κ ≠ 0 ∨ κ' ≠ 0`; `rank_vacKK` takes `κ ≠ 0` and
  `κ' ≠ 0`, and so does `not_aligned_vac_vacKK`. Nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 13 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. `mem_stabilizer_pair_iff'` is unit 199's
  `PatiSalamStabiliserGroup.mem_stabilizer_pair_iff` for an arbitrary pair of fields, and
  `eq_diagConj2_of_col1` is the second-column twin of its `eq_diagConj2_of`.

  0 sorry. 0 new axioms. `#print axioms` on all 13 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamRankTwoVacuum

open Matrix

namespace PatiSalamTwoComponentVacuum

open PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup

/-- The general neutral vacuum of the `(1, 2, 2)` bidoublet: `diag(κ, κ')`. -/
noncomputable def vacKK (κ κ' : ℂ) : EWBidoublet := diagonal ![κ, κ']

theorem vacEW_eq_vacKK : vacEW = vacKK 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vacEW, vacKK]

/-- An `SU(2)` matrix whose second column is `d̄ e₁`, with `|d| = 1`, is `diag(d, d̄)`. -/
theorem eq_diagConj2_of_col1 {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ) {d : ℂ} (hd : d * star d = 1) (h11 : h 1 1 = star d)
    (h01 : h 0 1 = 0) : h = diagConj2 d := by
  obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp hh
  have hs : star h * h = 1 := mem_unitaryGroup_iff'.mp hU
  have hsd : star d ≠ 0 := right_ne_zero_of_mul_eq_one hd
  have h10 : h 1 0 = 0 := by
    have e := congrFun (congrFun hs 0) 1
    simp only [mul_apply, Fin.sum_univ_two, star_apply, h01, h11, mul_zero, zero_add,
      one_apply_ne (by decide : (0 : Fin 2) ≠ 1)] at e
    exact star_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hsd)
  have h00 : h 0 0 = d := by
    rw [det_fin_two, h01, h11, zero_mul, sub_zero] at hdet
    calc h 0 0 = h 0 0 * (star d * d) := by rw [mul_comm (star d), hd, mul_one]
      _ = h 0 0 * star d * d := by ring
      _ = d := by rw [hdet, one_mul]
  exact eq_diagConj2_of hh hd h00 h10

theorem diagConj2_mul_star (d : ℂ) (hd : d * star d = 1) :
    diagConj2 d * star (diagConj2 d) = 1 := by
  rw [diagConj2, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa using hd
  · simpa [mul_comm] using hd

theorem star_diagConj2_mul (d : ℂ) (hd : d * star d = 1) :
    star (diagConj2 d) * diagConj2 d = 1 := by
  rw [diagConj2, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
    ← diagonal_one]
  congr 1
  funext i
  fin_cases i
  · simpa [mul_comm] using hd
  · simpa using hd

/-- **Given the first stage, a nonzero diagonal second-stage vacuum is fixed exactly when the two
`SU(2)` components agree** — for every `(κ, κ') ≠ 0`, the same condition as for `vacEW`. -/
theorem mem_stabilizer_vacKK_iff {κ κ' : ℂ} (hκ : κ ≠ 0 ∨ κ' ≠ 0) (g : FullGroup)
    (hg : ((g.1, g.2.2) : Stage1Group) ∈ MulAction.stabilizer Stage1Group vac) :
    ((g.2.1, g.2.2) : Stage2Group) ∈ MulAction.stabilizer Stage2Group (vacKK κ κ') ↔
      (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = g.2.2 := by
  obtain ⟨A, hA⟩ := exists_u3ToStage1_eq hg
  have hd : (A : Matrix (Fin 3) (Fin 3) ℂ).det * star (A : Matrix (Fin 3) (Fin 3) ℂ).det = 1 :=
    det_mul_star_det A
  set d := (A : Matrix (Fin 3) (Fin 3) ℂ).det with hd_def
  have hBR : (g.2.2 : Matrix (Fin 2) (Fin 2) ℂ) = diagConj2 d := by
    have := congrArg (fun x : Stage1Group => (x.2 : Matrix (Fin 2) (Fin 2) ℂ)) hA
    simpa [u3ToStage1, su2Part] using this.symm
  rw [MulAction.mem_stabilizer_iff, stage2_smul_def, stage2Act, hBR]
  constructor
  · intro h
    have h' : (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) * vacKK κ κ' = vacKK κ κ' * diagConj2 d := by
      set BL := (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ)
      calc BL * vacKK κ κ' = BL * vacKK κ κ' * (star (diagConj2 d) * diagConj2 d) := by
            rw [star_diagConj2_mul d hd, Matrix.mul_one]
        _ = (BL * vacKK κ κ' * star (diagConj2 d)) * diagConj2 d := by
            simp only [Matrix.mul_assoc]
        _ = vacKK κ κ' * diagConj2 d := by rw [h]
    rcases hκ with hκ | hκ'
    · have e0 := congrFun (congrFun h' 0) 0
      have e1 := congrFun (congrFun h' 1) 0
      simp only [vacKK, Fin.isValue, mul_apply, Fin.sum_univ_two, diagonal_apply_eq, cons_val_zero,
        ne_eq, one_ne_zero, not_false_eq_true, diagonal_apply_ne, mul_zero, add_zero, diagConj2,
        RCLike.star_def, zero_ne_one, zero_mul, cons_val_one, cons_val_fin_one,
        mul_eq_zero] at e0 e1
      exact eq_diagConj2_of (g.2.1).2 hd (by
          have := mul_right_cancel₀ hκ (e0.trans (mul_comm κ d))
          exact this) (by
          rcases e1 with h1 | h1
          · exact h1
          · exact absurd h1 hκ)
    · have e0 := congrFun (congrFun h' 0) 1
      have e1 := congrFun (congrFun h' 1) 1
      simp only [vacKK, Fin.isValue, mul_apply, Fin.sum_univ_two, diagonal_apply_eq, cons_val_zero,
        ne_eq, one_ne_zero, not_false_eq_true, diagonal_apply_ne, mul_zero, add_zero, diagConj2,
        RCLike.star_def, zero_ne_one, zero_mul, cons_val_one, cons_val_fin_one, zero_add,
        mul_eq_zero] at e0 e1
      exact eq_diagConj2_of_col1 (g.2.1).2 hd (by
          have := mul_right_cancel₀ hκ' (e1.trans (mul_comm κ' (star d)))
          exact this) (by
          rcases e0 with h0 | h0
          · exact h0
          · exact absurd h0 hκ')
  · intro h
    rw [h, diagConj2, vacKK, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal,
      diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, cons_val_zero, Pi.star_apply]
      linear_combination κ * hd
    · simp only [Fin.mk_one, Fin.isValue, cons_val_one, cons_val_fin_one, Pi.star_apply, star_star]
      linear_combination κ' * hd

/-- Membership of the joint stabiliser, for any pair of fields. -/
theorem mem_stabilizer_pair_iff' (g : FullGroup) (X : Bidoublet) (Φ : EWBidoublet) :
    g ∈ MulAction.stabilizer FullGroup (X, Φ) ↔
      ((g.1, g.2.2) : Stage1Group) ∈ MulAction.stabilizer Stage1Group X ∧
        ((g.2.1, g.2.2) : Stage2Group) ∈ MulAction.stabilizer Stage2Group Φ := by
  simp only [MulAction.mem_stabilizer_iff, full_smul_def, fullAct, Prod.mk.injEq, stage1_smul_def,
    stage2_smul_def]

/-- **Every nonzero diagonal second-stage vacuum has the SAME joint stabiliser as `vacEW`** — the
same subgroup of `SU(4) × SU(2)_L × SU(2)_R`, not merely an isomorphic one. -/
theorem stabilizer_vacKK_eq {κ κ' : ℂ} (hκ : κ ≠ 0 ∨ κ' ≠ 0) :
    MulAction.stabilizer FullGroup (vac, vacKK κ κ') =
      MulAction.stabilizer FullGroup (vac, vacEW) := by
  ext g
  rw [mem_stabilizer_pair_iff', mem_stabilizer_pair_iff', vacEW_eq_vacKK]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (mem_stabilizer_vacKK_iff (Or.inl one_ne_zero) g h1).mpr
      ((mem_stabilizer_vacKK_iff hκ g h1).mp h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (mem_stabilizer_vacKK_iff hκ g h1).mpr
      ((mem_stabilizer_vacKK_iff (Or.inl one_ne_zero) g h1).mp h2)⟩

theorem nonempty_stabilizer_vacKK_equiv_U3 {κ κ' : ℂ} (hκ : κ ≠ 0 ∨ κ' ≠ 0) :
    Nonempty (MulAction.stabilizer FullGroup (vac, vacKK κ κ') ≃* GroupU3) := by
  rw [stabilizer_vacKK_eq hκ]
  exact ⟨stabilizerPairEquivU3⟩

/-- The standard left–right vacuum `diag(κ, κ')` with both entries nonzero has rank two. -/
theorem rank_vacKK {κ κ' : ℂ} (hκ : κ ≠ 0) (hκ' : κ' ≠ 0) : (vacKK κ κ').rank = 2 := by
  have hall : ∀ i : Fin 2, ![κ, κ'] i ≠ 0 := by
    intro i
    fin_cases i
    · exact hκ
    · exact hκ'
  rw [vacKK, rank_diagonal, Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_fin]

/-- `diag(0, 1)` is not aligned with `vac`: its `SU(2)_R` direction is the other one. -/
theorem not_aligned_vac_vacKK_zero_one : ¬ PatiSalamVacuumOrbit.Aligned vac (vacKK 0 1) := by
  rintro ⟨u, v, a, c, hu, hv, ha, hc, hX, hΦ⟩
  have hvac1 : vac (Fin.last 3) 1 = 0 := by simp [vac]
  have hvac0 : vac (Fin.last 3) 0 = 1 := by simp [vac]
  have hv1 : v 1 = 0 := by
    have e := congrFun (congrFun hX (Fin.last 3)) 1
    have e0 := congrFun (congrFun hX (Fin.last 3)) 0
    rw [vecMulVec_apply, hvac1] at e
    rw [vecMulVec_apply, hvac0] at e0
    exact (mul_eq_zero.mp e.symm).resolve_left (left_ne_zero_of_mul_eq_one e0.symm)
  have e := congrFun (congrFun hΦ 1) 1
  simp [vacKK, vecMulVec_apply, hv1] at e

/-- **Alignment is sufficient and not necessary**: a second-stage vacuum outside unit 203's aligned
family still leaves `U(3)` unbroken. -/
theorem exists_not_aligned_stabilizer_equiv_U3 :
    ∃ Φ : EWBidoublet, ¬ PatiSalamVacuumOrbit.Aligned vac Φ ∧
      Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* GroupU3) :=
  ⟨vacKK 0 1, not_aligned_vac_vacKK_zero_one,
    nonempty_stabilizer_vacKK_equiv_U3 (Or.inr one_ne_zero)⟩

/-- With both entries nonzero, `diag(κ, κ')` is outside the aligned family: an aligned field is a
pure tensor, of rank at most one (`rank_vecMulVec_le`), and this one has rank two. -/
theorem not_aligned_vac_vacKK {κ κ' : ℂ} (hκ : κ ≠ 0) (hκ' : κ' ≠ 0) :
    ¬ PatiSalamVacuumOrbit.Aligned vac (vacKK κ κ') := by
  rintro ⟨u, v, a, c, -, -, -, -, -, hΦ⟩
  have h := rank_vecMulVec_le a (c • star v)
  rw [← hΦ, rank_vacKK hκ hκ'] at h
  exact absurd h (by norm_num)

end PatiSalamTwoComponentVacuum
