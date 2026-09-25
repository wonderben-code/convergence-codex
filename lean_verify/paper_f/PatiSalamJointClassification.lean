/-
  PatiSalamJointClassification: the joint unbroken group of both vacua, with the estate's
  first-stage `vac`, at every second-stage vacuum `Φ` — `U(3) × SU(2)` at `Φ = 0`, `U(3)` when the
  columns of `Φ ≠ 0` are orthogonal, and `SU(3) × {±1}` otherwise: colour and a sign, with the
  electric charge broken. The three groups are pairwise non-isomorphic.

  Campaign 3 hardening unit 222 (25 September 2026). Spine link L15 (Higgs sector).

  WHY. Unit 221 (`PatiSalamJointCount`) counted the joint unbroken generators at every `(vac, Φ)`
  — twelve at `Φ = 0`, nine at orthogonal columns, eight otherwise — and found the group `U(3)` at
  the nine. Its NOT list: *"That a `Φ` with non-orthogonal columns leaves a group not isomorphic
  to `U(3)`. Its joint Lie algebra has dimension eight, and a dimension is not an invariant of
  abstract groups"*. This file computes the groups at the twelve and at the eight, and decides it.

  WHAT IS PROVED.
  (1) The embedding. `jointToU3 Φ` reads a joint unbroken element's first-stage part in `U(3)`,
      through unit 199's `stabilizerVacEquivU3`; **`jointToU3_injective`**: at `Φ ≠ 0` the
      `SU(2)_L` part is fixed by the `SU(2)_R` part (unit 220's `fst_eq_of_snd_eq`).
  (2) The image. **`det_jointToU3`**: with non-orthogonal columns, `(Φᴴ Φ) 0 1 ≠ 0`, the
      determinant is `±1` — the `SU(2)_R` part `diag(d, d̄)` commutes with `Φᴴ Φ` (unit 220's
      `snd_mem_commSU2`), whose corner is nonzero, so `d = d̄`. **`u3ToFull_mem_of_det`**: at every
      `Φ`, each `W ∈ U(3)` of determinant `±1` gives the joint unbroken element `u3ToFull W`, its
      two `SU(2)` parts being one scalar `±1`. So **`mem_range_jointToU3_iff`**: the image is
      exactly the determinant-`±1` part of `U(3)`.
  (3) **`stabilizerPairEquivSU3Sign : Stab (vac, Φ) ≃* SU(3) × ℤˣ`** at `Φ ≠ 0` with non-orthogonal
      columns, through `su3SignHom (A, ε) = ε · A`, injective onto the same image
      (`su3SignHom_injective`, `mem_range_su3SignHom_iff`). Every element is `u3ToFull` of its
      `U(3)` part (`coe_stabilizerPairEquivSU3Sign_symm`). **The `SU(3)` factor is colour**:
      `(A, 1)` is `(diag(A, 1), 1, 1)`, unit 201's `colour_components`
      (`stabilizerPairEquivSU3Sign_symm_colour`). **The sign is `(−1, −1, −1)`**
      (`coe_stabilizerPairEquivSU3Sign_symm_sign`), which fixes every pair of vacua
      (`negOneFull_mem_stabilizer`).
  (4) The electric charge. **`expFull_charge_mem_stabilizer_pair_iff`**: with non-orthogonal
      columns the charge's rotation `expFull (t • qFull)`, whose `U(3)` part is `e^{it} · 1` (unit
      200's `stabilizerPairEquivU3_charge`), fixes `(vac, Φ)` exactly when `e^{6it} = 1`; so
      **`expFull_charge_not_mem_stabilizer_pair`**: the rotation by `π/6` is broken.
  (5) **`stabilizerPairZeroEquiv : Stab (vac, 0) ≃* U(3) × SU(2)`**: at `Φ = 0` the joint group is
      unit 199's `U(3)` times the whole of `SU(2)_L`, every element fixing `0` (unit 207's
      `stage2_smul_zero`).
  (6) The three groups are pairwise non-isomorphic. **`pow_six_eq_one_of_mem_center_SU3Sign`**:
      every central element of `SU(3) × {±1}` has sixth power one — its `SU(3)` part commutes with
      `−signAt k`, `−swap01` and `−swap12`, so is a scalar `z` (`eq_smul_one_of_comm`, unit 200's
      argument), and `z³ = det = 1`; `i · 1` is central in `U(3)` with sixth power `−1`
      (`iU3_mem_center`, `iU3_pow_six_ne_one`). Hence **`not_nonempty_U3_equiv_SU3Sign`** and
      **`not_nonempty_U3SU2_equiv_SU3Sign`** (`not_nonempty_mulEquiv_of_center`). And
      **`not_nonempty_U3SU2_equiv_U3`**: `(1, −1)` and `(−1, 1)` are distinct central elements of
      order two in `U(3) × SU(2)`, while `−1` is the only one in `U(3)`
      (`eq_neg_one_of_mem_center`).
  (7) **`joint_trichotomy`**: at every `Φ` exactly one of the three, by whether `Φ = 0` and whether
      the columns are orthogonal; **`nonempty_stabilizer_pair_equiv_iff`**: two second-stage vacua
      leave isomorphic joint groups exactly when they agree on both; and
      **`nonempty_stabilizer_pair_equiv_U3_iff`**: `Φ` leaves a group isomorphic to `U(3)` exactly
      when it is nonzero with orthogonal columns — unit 221's
      `nonempty_stabilizer_pair_equiv_U3_of_orthogonal` and its converse. So
      **`not_aligned_of_not_orthogonal`**: a pair with non-orthogonal columns is not in unit 203's
      aligned family, whose pairs all leave `U(3)`.

  NOT PROVED, said exactly.
  • Topology: the isomorphisms at `Φ = 0` and at non-orthogonal columns are of abstract groups;
    unit 209's topological upgrade is not made for them. At orthogonal columns it is unit 221's.
    ⚠ 25 September 2026 (hardening unit 223, `paper_f/PatiSalamSecondStageTopology.lean`): made
    there — `stabilizerPairZeroContinuousEquiv` and `stabilizerPairContinuousEquivSU3Sign`, so
    `joint_trichotomy_continuous` and `nonempty_stabilizer_pair_continuousEquiv_iff`. Kept as
    written (`ERRATUM 94`).
  • Other first-stage vacua: only the estate's `vac`. For a rank-one `X`, unit 203's conjugation
    would transport the statements; that transport is not written.
    ⚠ 25 September 2026 (hardening unit 225, `paper_f/PatiSalamPairCriterion.lean`): written there —
    every pair with a rank-one first vacuum has the unbroken group of a pair `(vac, Φ gR)`
    (`exists_stabilizer_pair_continuousEquiv`), so the trichotomy holds at every rank-one `X`, with
    the condition that `Φᴴ Φ` commute with `(Xᴴ X)ᵀ` (`joint_trichotomy_of_rank_eq_one`); and a
    rank-two first vacuum leaves `U(3)` with no `Φ`
    (`not_nonempty_stabilizer_pair_equiv_U3_of_rank_eq_two`). Kept as written (`ERRATUM 94`).
  • The joint Lie algebras are unit 221's counts, twelve, nine and eight; no statement here joins
    them to these groups.
    ⚠ 25 September 2026 (hardening unit 225, `paper_f/PatiSalamPairCriterion.lean`): joined for the
    isomorphism class there — two second-stage vacua leave isomorphic joint groups exactly when the
    counts agree (`nonempty_stabilizer_pair_equiv_iff_finrank_eq`); that the counts are the
    dimensions of these groups' Lie algebras is unit 217's `mem_matLieFull_stabilizer_iff` with unit
    221's count.
  • Which vacuum: a potential's minimum, and there is no potential. *Colour* and *electric charge*
    are the physics names of unit 201's `diag(A, 1)` and unit 200's `qFull`; what a vacuum that
    breaks the charge would mean for the photon is physics the estate does not state.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `jointToU3_injective` takes `Φ ≠ 0`;
  `det_jointToU3`, `mem_range_jointToU3_iff`, `range_jointToU3_eq`, `not_aligned_of_not_orthogonal`,
  `expFull_charge_mem_stabilizer_pair_iff` and `expFull_charge_not_mem_stabilizer_pair` take
  `(Φᴴ Φ) 0 1 ≠ 0`; `stabilizerPairEquivSU3Sign`, `su3SignHom_stabilizerPairEquivSU3Sign`,
  `coe_stabilizerPairEquivSU3Sign_symm`, `stabilizerPairEquivSU3Sign_symm_colour` and
  `coe_stabilizerPairEquivSU3Sign_symm_sign` take both; `su2Part_val_of_det`, `u3ToFull_mem_of_det`
  and `jointToU3_u3ToFull` take `det W = 1 ∨ det W = -1`; `neg_mem_SU3` takes a unitary `M` with
  `det M = -1`; `eq_smul_one_of_comm` takes commutation with every `signAt k`, with `swap01` and
  with `swap12`; `pow_six_eq_one_of_mem_center_SU3Sign`, `mem_center_map` and `mem_center_prod` take
  central elements; `eq_neg_one_of_mem_center` takes a central `W` with `W ^ 2 = 1` and `W ≠ 1`;
  `not_nonempty_mulEquiv_of_center` takes a central `c` with `c ^ 6 ≠ 1` and that every central
  element of the target has sixth power one. The rest take elements of their types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 61 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements are unit 200's `mem_center_iff_scalar` (the centre of
  `U(3)` is the scalars), used, whose argument `eq_smul_one_of_comm` restates for the five matrices
  alone, since `SU(3) × {±1}` does not contain `signAt k`; unit 201's `splitHom` (`(A, λ) ↦ λ · A`
  on `SU(3) × U(1)`), of which `su3SignHom` is the restriction to `λ = ±1`, and `colour_components`,
  used; unit 199's `u3ToFull`, `u3ToStage1_mem` and `stabilizerPairEquivU3`, used; unit 207's
  `negOneSU4`, `negOneSU2` and `stage2_smul_zero`, used; unit 212's `mem_center_fst` and
  `mem_center_snd` (the converse of `mem_center_prod`), `unitI` (`i ∈ U(1)`; `iU3` is
  `i · 1 ∈ U(3)`) and the centre arguments of `not_nonempty_SU2_SU2_equiv_SU2_circle`, whose inline
  step `mem_center_map` states once; and unit 221's `toStage1` (the Lie-algebra form of
  `toStage1Stab`) and `nonempty_stabilizer_pair_equiv_U3_of_orthogonal`, used; unit 203's
  `nonempty_stabilizer_pair_equiv_U3` for aligned pairs, used; and unit 205's
  `not_aligned_vac_vacKK` (the diagonal vacua are not aligned either, though they leave `U(3)`).

  `#print axioms` on all 61 declarations below: 59 are `[propext, Classical.choice, Quot.sound]`,
  and `nonempty_mulEquiv_congr` and `nonempty_mulEquiv_symm` use `[Quot.sound]` alone.
-/

import ElectroweakUnbrokenGroup
import PatiSalamJointCount
import PatiSalamSameStabiliser
import PatiSalamUnbrokenSplit

open Matrix PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup PatiSalamTwoComponentVacuum PatiSalamChargeCentre
  PatiSalamRankTwoStabiliser ElectroweakUnbrokenGroup PatiSalamSameStabiliser PatiSalamUnbrokenSplit
  SkewAdjointExponential PatiSalamTwoStageStabiliser

namespace PatiSalamJointClassification

noncomputable section

/-! ### The joint unbroken group inside `U(3)` -/

/-- The first-stage part of a joint unbroken element. -/
def toStage1Stab (Φ : EWBidoublet) :
    MulAction.stabilizer FullGroup (vac, Φ) →* MulAction.stabilizer Stage1Group vac where
  toFun h := ⟨((h : FullGroup).1, (h : FullGroup).2.2),
    ((mem_stabilizer_pair_iff' _ _ _).mp h.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- … read in `U(3)` through unit 199's `stabilizerVacEquivU3`. -/
def jointToU3 (Φ : EWBidoublet) : MulAction.stabilizer FullGroup (vac, Φ) →* GroupU3 :=
  stabilizerVacEquivU3.toMonoidHom.comp (toStage1Stab Φ)

theorem stage2_mem {Φ : EWBidoublet} (h : MulAction.stabilizer FullGroup (vac, Φ)) :
    ((h : FullGroup).2.1, (h : FullGroup).2.2) ∈ MulAction.stabilizer Stage2Group Φ :=
  ((mem_stabilizer_pair_iff' _ _ _).mp h.2).2

theorem u3ToStage1_jointToU3 {Φ : EWBidoublet} (h : MulAction.stabilizer FullGroup (vac, Φ)) :
    u3ToStage1 (jointToU3 Φ h) = ((h : FullGroup).1, (h : FullGroup).2.2) :=
  u3ToStage1_stabilizerVacEquivU3 _

/-- **At `Φ ≠ 0` the joint unbroken group embeds in `U(3)`**: its `SU(2)_L` part is fixed by its
`SU(2)_R` part (unit 220's `fst_eq_of_snd_eq`). -/
theorem jointToU3_injective {Φ : EWBidoublet} (hΦ : Φ ≠ 0) :
    Function.Injective (jointToU3 Φ) := by
  intro h h' e
  have e1 : toStage1Stab Φ h = toStage1Stab Φ h' := stabilizerVacEquivU3.injective e
  have e1' : ((h : FullGroup).1, (h : FullGroup).2.2) =
      ((h' : FullGroup).1, (h' : FullGroup).2.2) := congrArg Subtype.val e1
  have hL := fst_eq_of_snd_eq hΦ (stage2_mem h) (stage2_mem h') (Prod.ext_iff.mp e1').2
  exact Subtype.ext (Prod.ext (Prod.ext_iff.mp e1').1 (Prod.ext hL (Prod.ext_iff.mp e1').2))

/-- **With non-orthogonal columns the determinant is `±1`**: the `SU(2)_R` part `diag(d, d̄)`,
`d = det`, commutes with `Φᴴ Φ`, whose corner is nonzero, so `d = d̄`. -/
theorem det_jointToU3 {Φ : EWBidoublet} (h01 : (Φᴴ * Φ) 0 1 ≠ 0)
    (h : MulAction.stabilizer FullGroup (vac, Φ)) :
    ((jointToU3 Φ h : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ).det = 1 ∨
      ((jointToU3 Φ h : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ).det = -1 := by
  set d := ((jointToU3 Φ h : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ).det with hd
  have hR : (((h : FullGroup).2.2 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = diagConj2 d := by
    have := congrArg (fun g : Stage1Group => ((g.2 : SU2) : Matrix (Fin 2) (Fin 2) ℂ))
      (u3ToStage1_jointToU3 h)
    exact this.symm
  have hc := snd_mem_commSU2 (stage2_mem h)
  have hc' : diagConj2 d * (Φᴴ * Φ) = (Φᴴ * Φ) * diagConj2 d := by
    have : ((((h : FullGroup).2.2 : SU2)) : Matrix (Fin 2) (Fin 2) ℂ) * (Φᴴ * Φ) =
        (Φᴴ * Φ) * (((h : FullGroup).2.2 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) := hc
    rwa [hR] at this
  have e01 := congrFun (congrFun hc' 0) 1
  simp only [diagConj2, diagonal_mul, mul_diagonal, Matrix.cons_val_zero,
    Matrix.cons_val_one] at e01
  have hds : d = star d := by
    have : (d - star d) * (Φᴴ * Φ) 0 1 = 0 := by linear_combination e01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right h01)
  have hdd : star d * d = 1 := star_det_mul_det (jointToU3 Φ h)
  rw [← hds] at hdd
  have h2 : (d - 1) * (d + 1) = 0 := by linear_combination hdd
  rcases mul_eq_zero.mp h2 with h1 | h1
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h1)

/-- At determinant `±1` the `SU(2)_R` part `diag(d, d̄)` is the scalar `d`. -/
theorem su2Part_val_of_det {W : GroupU3}
    (hW : (W : Matrix (Fin 3) (Fin 3) ℂ).det = 1 ∨ (W : Matrix (Fin 3) (Fin 3) ℂ).det = -1) :
    ((su2Part W : SU2) : Matrix (Fin 2) (Fin 2) ℂ) = (W : Matrix (Fin 3) (Fin 3) ℂ).det • 1 := by
  change diagConj2 (W : Matrix (Fin 3) (Fin 3) ℂ).det = _
  rcases hW with h | h <;> rw [h, diagConj2] <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp

/-- **Every `W ∈ U(3)` of determinant `±1` gives a joint unbroken element at every `Φ`**:
`u3ToFull W` — its `SU(2)_L` and `SU(2)_R` parts are the same scalar `±1`, which fixes every `Φ`. -/
theorem u3ToFull_mem_of_det {Φ : EWBidoublet} {W : GroupU3}
    (hW : (W : Matrix (Fin 3) (Fin 3) ℂ).det = 1 ∨ (W : Matrix (Fin 3) (Fin 3) ℂ).det = -1) :
    u3ToFull W ∈ MulAction.stabilizer FullGroup (vac, Φ) := by
  rw [mem_stabilizer_pair_iff', u3ToFull_apply]
  refine ⟨u3ToStage1_mem W, ?_⟩
  rw [mem_stabilizer_stage2_iff]
  change ((su2Part W : SU2) : Matrix (Fin 2) (Fin 2) ℂ) * Φ = Φ * (su2Part W : SU2)
  rw [su2Part_val_of_det hW, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]

theorem jointToU3_u3ToFull {Φ : EWBidoublet} {W : GroupU3}
    (hW : (W : Matrix (Fin 3) (Fin 3) ℂ).det = 1 ∨ (W : Matrix (Fin 3) (Fin 3) ℂ).det = -1) :
    jointToU3 Φ ⟨u3ToFull W, u3ToFull_mem_of_det hW⟩ = W := by
  apply u3ToStage1_injective
  rw [u3ToStage1_jointToU3]
  rfl

/-- **THE IMAGE**: with non-orthogonal columns, the `U(3)` parts of the joint unbroken elements are
exactly the `W ∈ U(3)` of determinant `±1`. -/
theorem mem_range_jointToU3_iff {Φ : EWBidoublet} (h01 : (Φᴴ * Φ) 0 1 ≠ 0) (W : GroupU3) :
    W ∈ (jointToU3 Φ).range ↔
      (W : Matrix (Fin 3) (Fin 3) ℂ).det = 1 ∨ (W : Matrix (Fin 3) (Fin 3) ℂ).det = -1 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact det_jointToU3 h01 h
  · intro hW
    exact ⟨_, jointToU3_u3ToFull hW⟩

/-! ### `SU(3) × {±1}` inside `U(3)` -/

theorem intCast_units_mul_self (ε : ℤˣ) : ((ε : ℤ) : ℂ) * ((ε : ℤ) : ℂ) = 1 := by
  rcases Int.units_eq_one_or ε with h | h <;> rw [h] <;> norm_num

/-- `(A, ε) ↦ ε • A`, from `SU(3) × {±1}` to `U(3)`. -/
def su3SignHom : SU3 × ℤˣ →* GroupU3 where
  toFun p := ⟨((p.2 : ℤ) : ℂ) • (p.1 : Matrix (Fin 3) (Fin 3) ℂ),
    smul_mem_unitary (mem_specialUnitaryGroup_iff.mp p.1.2).1
      (by rw [star_intCast]; exact intCast_units_mul_self p.2)⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' p q := by
    apply Subtype.ext
    simp only [Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, Units.val_mul, Int.cast_mul]
    rw [smul_mul_smul_comm]

theorem su3SignHom_val (p : SU3 × ℤˣ) :
    ((su3SignHom p : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ)
      = ((p.2 : ℤ) : ℂ) • (p.1 : Matrix (Fin 3) (Fin 3) ℂ) :=
  rfl

theorem det_su3SignHom (p : SU3 × ℤˣ) :
    ((su3SignHom p : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ).det = ((p.2 : ℤ) : ℂ) := by
  rw [su3SignHom_val, det_smul, Fintype.card_fin, (mem_specialUnitaryGroup_iff.mp p.1.2).2,
    mul_one]
  rcases Int.units_eq_one_or p.2 with h | h <;> rw [h] <;> norm_num

theorem su3SignHom_injective : Function.Injective su3SignHom := by
  intro p q e
  have hd := congrArg (fun W : GroupU3 => (W : Matrix (Fin 3) (Fin 3) ℂ).det) e
  simp only [det_su3SignHom] at hd
  have h2 : p.2 = q.2 := Units.ext (Int.cast_injective hd)
  have e' : ((p.2 : ℤ) : ℂ) • (p.1 : Matrix (Fin 3) (Fin 3) ℂ) =
      ((q.2 : ℤ) : ℂ) • (q.1 : Matrix (Fin 3) (Fin 3) ℂ) := congrArg Subtype.val e
  rw [h2] at e'
  have h1 : (p.1 : Matrix (Fin 3) (Fin 3) ℂ) = q.1 := by
    have := congrArg (fun M => ((q.2 : ℤ) : ℂ) • M) e'
    simpa only [smul_smul, intCast_units_mul_self, one_smul] using this
  exact Prod.ext (Subtype.ext h1) h2

/-- **THE IMAGE OF `SU(3) × {±1}`**: exactly the `W ∈ U(3)` of determinant `±1`. -/
theorem mem_range_su3SignHom_iff (W : GroupU3) :
    W ∈ su3SignHom.range ↔
      (W : Matrix (Fin 3) (Fin 3) ℂ).det = 1 ∨ (W : Matrix (Fin 3) (Fin 3) ℂ).det = -1 := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [det_su3SignHom]
    rcases Int.units_eq_one_or p.2 with h | h <;> rw [h] <;> norm_num
  · intro hW
    obtain ⟨ε, hε⟩ : ∃ ε : ℤˣ, ((ε : ℤ) : ℂ) = (W : Matrix (Fin 3) (Fin 3) ℂ).det := by
      rcases hW with h | h
      · exact ⟨1, by rw [h]; norm_num⟩
      · exact ⟨-1, by rw [h]; norm_num⟩
    have hA : ((ε : ℤ) : ℂ) • (W : Matrix (Fin 3) (Fin 3) ℂ) ∈ specialUnitaryGroup (Fin 3) ℂ := by
      refine mem_specialUnitaryGroup_iff.mpr
        ⟨smul_mem_unitary W.2 (by rw [star_intCast]; exact intCast_units_mul_self ε), ?_⟩
      rw [det_smul, Fintype.card_fin, ← hε]
      rcases Int.units_eq_one_or ε with h | h <;> rw [h] <;> norm_num
    refine ⟨(⟨_, hA⟩, ε), Subtype.ext ?_⟩
    rw [su3SignHom_val]
    change ((ε : ℤ) : ℂ) • (((ε : ℤ) : ℂ) • (W : Matrix (Fin 3) (Fin 3) ℂ)) = W
    rw [smul_smul, intCast_units_mul_self, one_smul]

theorem range_jointToU3_eq {Φ : EWBidoublet} (h01 : (Φᴴ * Φ) 0 1 ≠ 0) :
    (jointToU3 Φ).range = su3SignHom.range := by
  ext W
  rw [mem_range_jointToU3_iff h01, mem_range_su3SignHom_iff]

/-- **THE JOINT UNBROKEN GROUP AT NON-ORTHOGONAL COLUMNS IS `SU(3) × {±1}`.** -/
def stabilizerPairEquivSU3Sign {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (h01 : (Φᴴ * Φ) 0 1 ≠ 0) :
    MulAction.stabilizer FullGroup (vac, Φ) ≃* SU3 × ℤˣ :=
  (MonoidHom.ofInjective (jointToU3_injective hΦ)).trans
    ((MulEquiv.subgroupCongr (range_jointToU3_eq h01)).trans
      (MonoidHom.ofInjective su3SignHom_injective).symm)

theorem su3SignHom_stabilizerPairEquivSU3Sign {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 ≠ 0) (h : MulAction.stabilizer FullGroup (vac, Φ)) :
    su3SignHom (stabilizerPairEquivSU3Sign hΦ h01 h) = jointToU3 Φ h := by
  simp only [stabilizerPairEquivSU3Sign, MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm]
  rfl

/-- **Every joint unbroken element at non-orthogonal columns is `u3ToFull` of its `U(3)` part**: its
`SU(2)_L` and `SU(2)_R` parts are one scalar `±1`. -/
theorem coe_stabilizerPairEquivSU3Sign_symm {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 ≠ 0) (p : SU3 × ℤˣ) :
    (((stabilizerPairEquivSU3Sign hΦ h01).symm p : MulAction.stabilizer FullGroup (vac, Φ)) :
      FullGroup) = u3ToFull (su3SignHom p) := by
  have hW := (mem_range_su3SignHom_iff (su3SignHom p)).mp ⟨p, rfl⟩
  have e : (stabilizerPairEquivSU3Sign hΦ h01).symm p = ⟨u3ToFull (su3SignHom p),
      u3ToFull_mem_of_det hW⟩ := by
    apply jointToU3_injective hΦ
    rw [jointToU3_u3ToFull hW, ← su3SignHom_stabilizerPairEquivSU3Sign hΦ h01,
      MulEquiv.apply_symm_apply]
  rw [e]

/-- **THE `SU(3)` FACTOR IS COLOUR**: `(A, 1)` is the joint unbroken element `(diag(A, 1), 1, 1)` —
unit 201's colour embedding (`colour_components`). -/
theorem stabilizerPairEquivSU3Sign_symm_colour {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 ≠ 0) (A : SU3) :
    ((((stabilizerPairEquivSU3Sign hΦ h01).symm (A, 1) : MulAction.stabilizer FullGroup (vac, Φ)) :
        FullGroup).1 : Matrix (Fin 4) (Fin 4) ℂ) = blockDiag4 A 1 ∧
      (((stabilizerPairEquivSU3Sign hΦ h01).symm (A, 1) : MulAction.stabilizer FullGroup (vac, Φ)) :
        FullGroup).2.1 = 1 ∧
      (((stabilizerPairEquivSU3Sign hΦ h01).symm (A, 1) : MulAction.stabilizer FullGroup (vac, Φ)) :
        FullGroup).2.2 = 1 := by
  have hsp : su3SignHom (A, 1) = splitHom (A, 1) := by
    apply Subtype.ext
    rw [su3SignHom_val, splitHom_val]
    simp
  rw [coe_stabilizerPairEquivSU3Sign_symm, hsp]
  exact colour_components A

/-! ### The sign: `(−1, −1, −1)` fixes every pair -/

/-- `−1 ∈ U(3)`. -/
def negOneU3 : GroupU3 :=
  ⟨-1, by rw [mem_unitaryGroup_iff, star_neg, star_one, neg_mul_neg, mul_one]⟩

/-- **`(−1, −1, −1)` fixes every pair of vacua**: it acts as `(−1) X (−1)ᵀ` and `(−1) Φ (−1)ᴴ`. -/
theorem negOneFull_mem_stabilizer (X : Bidoublet) (Φ : EWBidoublet) :
    ((negOneSU4, negOneSU2, negOneSU2) : FullGroup) ∈ MulAction.stabilizer FullGroup (X, Φ) := by
  rw [mem_stabilizer_pair_iff', MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    stage1_smul_def, stage2_smul_def, stage1Act, stage2Act]
  change (-1 : Matrix (Fin 4) (Fin 4) ℂ) * X * (-1 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = X ∧
    (-1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ * star (-1 : Matrix (Fin 2) (Fin 2) ℂ) = Φ
  simp only [transpose_neg, transpose_one, star_neg, star_one, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.one_mul, Matrix.mul_one]
  exact ⟨neg_neg X, neg_neg Φ⟩

theorem det_negOneU3 : (negOneU3 : Matrix (Fin 3) (Fin 3) ℂ).det = -1 := by
  change (-1 : Matrix (Fin 3) (Fin 3) ℂ).det = -1
  rw [det_neg, det_one, Fintype.card_fin]
  norm_num

theorem blockDiag4_neg_one : blockDiag4 (-1) (-1) = (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h3 : (-1 : Matrix (Fin 3) (Fin 3) ℂ) = diagonal (fun _ => -1) := by
    rw [← diagonal_one, ← diagonal_neg]
  rw [h3, blockDiag4_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The first-stage part of `−1 ∈ U(3)` is `(−1, −1)`.** -/
theorem u3ToStage1_negOneU3 : u3ToStage1 negOneU3 = (negOneSU4, negOneSU2) := by
  have h4 : su4Part negOneU3 = negOneSU4 := by
    apply Subtype.ext
    change blockDiag4 (negOneU3 : Matrix (Fin 3) (Fin 3) ℂ)
      (star (negOneU3 : Matrix (Fin 3) (Fin 3) ℂ).det) = -1
    rw [det_negOneU3, star_neg, star_one]
    exact blockDiag4_neg_one
  have h2 : su2Part negOneU3 = negOneSU2 := by
    apply Subtype.ext
    change diagConj2 (negOneU3 : Matrix (Fin 3) (Fin 3) ℂ).det = -1
    rw [det_negOneU3, diagConj2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  change (su4Part negOneU3, su2Part negOneU3) = _
  rw [h4, h2]

/-- **THE SIGN IS `(−1, −1, −1)`**: at non-orthogonal columns `(1, −1) ∈ SU(3) × {±1}` is the
element that fixes every pair of vacua (`negOneFull_mem_stabilizer`). -/
theorem coe_stabilizerPairEquivSU3Sign_symm_sign {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 ≠ 0) :
    (((stabilizerPairEquivSU3Sign hΦ h01).symm (1, -1) : MulAction.stabilizer FullGroup (vac, Φ)) :
      FullGroup) = (negOneSU4, negOneSU2, negOneSU2) := by
  have hs : su3SignHom (1, -1) = negOneU3 := by
    apply Subtype.ext
    rw [su3SignHom_val]
    change (((-1 : ℤˣ) : ℤ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) = -1
    norm_num
  rw [coe_stabilizerPairEquivSU3Sign_symm, hs, u3ToFull_apply, u3ToStage1_negOneU3]

/-! ### Electric charge -/

/-- **WHICH CHARGE ROTATIONS SURVIVE AT NON-ORTHOGONAL COLUMNS**: `expFull (t • qFull)`, whose
`U(3)` part is `e^{it} · 1` (unit 200's `stabilizerPairEquivU3_charge`), fixes `(vac, Φ)` exactly
when `e^{6it} = 1`. -/
theorem expFull_charge_mem_stabilizer_pair_iff {Φ : EWBidoublet} (h01 : (Φᴴ * Φ) 0 1 ≠ 0)
    (t : ℝ) :
    expFull (t • qFull) ∈ MulAction.stabilizer FullGroup (vac, Φ) ↔
      Complex.exp (t * Complex.I) ^ 6 = 1 := by
  set W := stabilizerPairEquivU3 ⟨expFull (t • qFull), charge_mem t⟩ with hWdef
  have hg : u3ToFull W = expFull (t • qFull) := u3ToFull_stabilizerPairEquivU3 _
  have hd : (W : Matrix (Fin 3) (Fin 3) ℂ).det = Complex.exp (t * Complex.I) ^ 3 := by
    rw [hWdef, stabilizerPairEquivU3_charge, det_smul, det_one, Fintype.card_fin, mul_one]
  have h6 : Complex.exp (t * Complex.I) ^ 6 = (Complex.exp (t * Complex.I) ^ 3) ^ 2 := by
    rw [← pow_mul]
  constructor
  · intro hmem
    have hj : jointToU3 Φ ⟨_, hmem⟩ = W := by
      apply u3ToStage1_injective
      rw [u3ToStage1_jointToU3]
      change ((expFull (t • qFull)).1, (expFull (t • qFull)).2.2) = u3ToStage1 W
      rw [← hg, u3ToFull_apply]
    have hdet := det_jointToU3 h01 ⟨_, hmem⟩
    rw [hj, hd] at hdet
    rw [h6]
    rcases hdet with h | h <;> rw [h] <;> norm_num
  · intro h
    have h2 : (Complex.exp (t * Complex.I) ^ 3 - 1) * (Complex.exp (t * Complex.I) ^ 3 + 1)
        = 0 := by
      linear_combination h6.symm.trans h
    rw [← hg]
    apply u3ToFull_mem_of_det
    rw [hd]
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (eq_neg_of_add_eq_zero_left h')

/-- **ELECTRIC CHARGE IS BROKEN AT NON-ORTHOGONAL COLUMNS**: the rotation by `π/6` does not fix
`(vac, Φ)`, since `e^{iπ} = −1`. -/
theorem expFull_charge_not_mem_stabilizer_pair {Φ : EWBidoublet} (h01 : (Φᴴ * Φ) 0 1 ≠ 0) :
    expFull ((Real.pi / 6) • qFull) ∉ MulAction.stabilizer FullGroup (vac, Φ) := by
  rw [expFull_charge_mem_stabilizer_pair_iff h01, ← Complex.exp_nat_mul]
  have : ((6 : ℕ) : ℂ) * (((Real.pi / 6 : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_pi_mul_I]
  norm_num

/-! ### `Φ = 0`: the joint group is `U(3) × SU(2)` -/

/-- The `SU(2)_L` part of a joint unbroken element. -/
def leftSU2Part (Φ : EWBidoublet) : MulAction.stabilizer FullGroup (vac, Φ) →* SU2 where
  toFun h := (h : FullGroup).2.1
  map_one' := rfl
  map_mul' _ _ := rfl

theorem jointZeroHom_injective :
    Function.Injective ((jointToU3 0).prod (leftSU2Part 0)) := by
  intro h h' e
  have e1 : toStage1Stab 0 h = toStage1Stab 0 h' :=
    stabilizerVacEquivU3.injective (congrArg Prod.fst e)
  have e1' : ((h : FullGroup).1, (h : FullGroup).2.2) =
      ((h' : FullGroup).1, (h' : FullGroup).2.2) := congrArg Subtype.val e1
  have e2 : (h : FullGroup).2.1 = (h' : FullGroup).2.1 := congrArg Prod.snd e
  exact Subtype.ext (Prod.ext (Prod.ext_iff.mp e1').1 (Prod.ext e2 (Prod.ext_iff.mp e1').2))

theorem jointZeroHom_surjective :
    Function.Surjective ((jointToU3 0).prod (leftSU2Part 0)) := by
  rintro ⟨W, g⟩
  have hmem : ((su4Part W, g, su2Part W) : FullGroup) ∈
      MulAction.stabilizer FullGroup (vac, (0 : EWBidoublet)) := by
    rw [mem_stabilizer_pair_iff']
    exact ⟨u3ToStage1_mem W, MulAction.mem_stabilizer_iff.mpr (stage2_smul_zero _)⟩
  refine ⟨⟨_, hmem⟩, Prod.ext ?_ rfl⟩
  apply u3ToStage1_injective
  rw [MonoidHom.prod_apply, u3ToStage1_jointToU3]
  rfl

/-- **THE JOINT UNBROKEN GROUP AT `Φ = 0` IS `U(3) × SU(2)`**: unit 199's `U(3)` and the whole of
`SU(2)_L`. -/
def stabilizerPairZeroEquiv :
    MulAction.stabilizer FullGroup (vac, (0 : EWBidoublet)) ≃* GroupU3 × SU2 :=
  MulEquiv.ofBijective _ ⟨jointZeroHom_injective, jointZeroHom_surjective⟩

/-! ### The three groups are pairwise non-isomorphic -/

theorem det_signAt (k : Fin 3) : (signAt k).det = -1 := by
  fin_cases k <;> simp [signAt, det_diagonal, Fin.prod_univ_three]

theorem det_swap01 : swap01.det = -1 := by
  simp [swap01, det_fin_three]

theorem det_swap12 : swap12.det = -1 := by
  simp [swap12, det_fin_three]

/-- A `3 × 3` matrix commuting with every `signAt k` and with the two transpositions is a scalar —
unit 200's argument for the centre of `U(3)` (`mem_center_iff_scalar`), which uses only those
elements. -/
theorem eq_smul_one_of_comm (M : Matrix (Fin 3) (Fin 3) ℂ)
    (hs : ∀ k, signAt k * M = M * signAt k) (h01 : swap01 * M = M * swap01)
    (h12 : swap12 * M = M * swap12) : M = M 0 0 • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun (hs i) i) j
    rw [signAt, diagonal_mul, mul_diagonal] at e
    simp only [if_true, Ne.symm hij, if_false, neg_one_mul, mul_one] at e
    linear_combination (-1 / 2 : ℂ) * e
  have e01 := congrFun (congrFun h01 0) 1
  have e12 := congrFun (congrFun h12 1) 2
  simp [swap01, swap12, Matrix.mul_apply, Fin.sum_univ_three] at e01 e12
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hoff, e01, e12]

theorem neg_mem_SU3 {M : Matrix (Fin 3) (Fin 3) ℂ} (hM : M ∈ unitaryGroup (Fin 3) ℂ)
    (hd : M.det = -1) : -M ∈ specialUnitaryGroup (Fin 3) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff']
  refine ⟨?_, ?_⟩
  · rw [star_neg, neg_mul_neg]
    exact mem_unitaryGroup_iff'.mp hM
  · rw [det_neg, Fintype.card_fin, hd]
    norm_num

/-- **Every central element of `SU(3) × {±1}` has sixth power one**: its `SU(3)` part commutes with
`−signAt k`, `−swap01`, `−swap12`, so is a scalar `z` with `z³ = det = 1`. -/
theorem pow_six_eq_one_of_mem_center_SU3Sign {d : SU3 × ℤˣ} (hd : d ∈ Subgroup.center (SU3 × ℤˣ)) :
    d ^ 6 = 1 := by
  set M := (d.1 : Matrix (Fin 3) (Fin 3) ℂ) with hMdef
  have hcomm : ∀ V : Matrix (Fin 3) (Fin 3) ℂ, V ∈ unitaryGroup (Fin 3) ℂ → V.det = -1 →
      V * M = M * V := by
    intro V hV hVd
    have e := Subgroup.mem_center_iff.mp hd ((⟨-V, neg_mem_SU3 hV hVd⟩ : SU3), (1 : ℤˣ))
    have e1 : (-V) * M = M * (-V) :=
      congrArg (fun x : SU3 × ℤˣ => ((x.1 : SU3) : Matrix (Fin 3) (Fin 3) ℂ)) e
    rw [neg_mul, mul_neg] at e1
    exact neg_injective e1
  have hM := eq_smul_one_of_comm M (fun k => hcomm _ (signAt_mem k) (det_signAt k))
    (hcomm _ swap01_mem det_swap01) (hcomm _ swap12_mem det_swap12)
  have hz : (M 0 0) ^ 3 = 1 := by
    have hdet := (mem_specialUnitaryGroup_iff.mp d.1.2).2
    rw [← hMdef, hM, det_smul, det_one, Fintype.card_fin, mul_one] at hdet
    exact hdet
  have hA : d.1 ^ 6 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, ← hMdef, hM, smul_pow, one_pow, show (6 : ℕ) = 3 * 2 by rfl,
      pow_mul, hz, one_pow, one_smul]
    rfl
  have hε : d.2 ^ 6 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Int.units_sq, one_pow]
  exact Prod.ext hA hε

/-- `i · 1`: central in `U(3)`, with sixth power `−1`. -/
def iU3 : GroupU3 :=
  ⟨Complex.I • (1 : Matrix (Fin 3) (Fin 3) ℂ), by
    rw [mem_unitaryGroup_iff, star_smul, star_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul, Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I,
      neg_neg, one_smul]⟩

theorem iU3_mem_center : iU3 ∈ Subgroup.center GroupU3 :=
  (mem_center_iff_scalar iU3).mpr ⟨Complex.I, rfl⟩

theorem iU3_pow_six_ne_one : iU3 ^ 6 ≠ 1 := by
  intro h6
  have hI : Complex.I ^ 6 = -1 := by
    rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, Complex.I_sq]
    norm_num
  have h' : ((iU3 ^ 6 : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
    rw [h6, OneMemClass.coe_one]
  rw [SubmonoidClass.coe_pow] at h'
  change (Complex.I • (1 : Matrix (Fin 3) (Fin 3) ℂ)) ^ 6 = 1 at h'
  rw [smul_pow, one_pow, hI] at h'
  have h00 := congrFun (congrFun h' 0) 0
  norm_num at h00

theorem mem_center_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) {c : G}
    (hc : c ∈ Subgroup.center G) : e c ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro g
  rw [← e.apply_symm_apply g, ← map_mul, ← map_mul, hc]

theorem mem_center_prod {G H : Type*} [Group G] [Group H] {a : G} {b : H}
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center H) :
    (a, b) ∈ Subgroup.center (G × H) := by
  rw [Subgroup.mem_center_iff] at ha hb ⊢
  intro g
  exact Prod.ext (ha g.1) (hb g.2)

/-- A group with a central element of sixth power not one is not isomorphic to a group all of
whose central elements have sixth power one. -/
theorem not_nonempty_mulEquiv_of_center {G H : Type*} [Group G] [Group H] {c : G}
    (hc : c ∈ Subgroup.center G) (h6 : c ^ 6 ≠ 1)
    (hH : ∀ d ∈ Subgroup.center H, d ^ 6 = 1) : ¬ Nonempty (G ≃* H) := by
  rintro ⟨e⟩
  apply h6
  apply e.injective
  rw [map_pow, hH _ (mem_center_map e hc), map_one]

/-- **`U(3) ≄ SU(3) × {±1}`.** -/
theorem not_nonempty_U3_equiv_SU3Sign : ¬ Nonempty (GroupU3 ≃* SU3 × ℤˣ) :=
  not_nonempty_mulEquiv_of_center iU3_mem_center iU3_pow_six_ne_one
    fun _ hd => pow_six_eq_one_of_mem_center_SU3Sign hd

/-- **`U(3) × SU(2) ≄ SU(3) × {±1}`.** -/
theorem not_nonempty_U3SU2_equiv_SU3Sign : ¬ Nonempty (GroupU3 × SU2 ≃* SU3 × ℤˣ) :=
  not_nonempty_mulEquiv_of_center (c := (iU3, 1)) (mem_center_prod iU3_mem_center
    (Subgroup.one_mem _)) (fun h => iU3_pow_six_ne_one (congrArg Prod.fst h))
    fun _ hd => pow_six_eq_one_of_mem_center_SU3Sign hd

theorem negOneU3_mem_center : negOneU3 ∈ Subgroup.center GroupU3 :=
  (mem_center_iff_scalar negOneU3).mpr ⟨-1, by
    change (-1 : Matrix (Fin 3) (Fin 3) ℂ) = (-1 : ℂ) • 1
    rw [neg_one_smul]⟩

theorem negOneSU2_mem_center : negOneSU2 ∈ Subgroup.center SU2 := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) * (-1) = (-1) * (g : Matrix (Fin 2) (Fin 2) ℂ)
  rw [mul_neg, neg_mul, mul_one, one_mul]

theorem negOneU3_sq : negOneU3 ^ 2 = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  change (-1 : Matrix (Fin 3) (Fin 3) ℂ) ^ 2 = 1
  rw [neg_one_sq]

theorem negOneSU2_sq : negOneSU2 ^ 2 = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  change (-1 : Matrix (Fin 2) (Fin 2) ℂ) ^ 2 = 1
  rw [neg_one_sq]

theorem negOneU3_ne_one : negOneU3 ≠ 1 := fun h => by
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  norm_num [negOneU3] at this

theorem negOneSU2_ne_one : negOneSU2 ≠ 1 := fun h => by
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  norm_num [negOneSU2] at this

/-- A central element of `U(3)` of order two is `−1`. -/
theorem eq_neg_one_of_mem_center {W : GroupU3} (hc : W ∈ Subgroup.center GroupU3)
    (h2 : W ^ 2 = 1) (h1 : W ≠ 1) : (W : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
  obtain ⟨z, hz⟩ := (mem_center_iff_scalar W).mp hc
  have hz2 : z ^ 2 = 1 := by
    have e : ((W ^ 2 : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      rw [h2, OneMemClass.coe_one]
    rw [SubmonoidClass.coe_pow, hz, smul_pow, one_pow] at e
    have e00 := congrFun (congrFun e 0) 0
    simpa using e00
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact h1 (Subtype.ext (by rw [hz, one_smul, OneMemClass.coe_one]))
  have hzm : z = -1 := by
    have : (z - 1) * (z + 1) = 0 := by linear_combination hz2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hz1
    · exact eq_neg_of_add_eq_zero_left h
  rw [hz, hzm, neg_one_smul]

/-- **`U(3) × SU(2) ≄ U(3)`**: `(1, −1)` and `(−1, 1)` are distinct central elements of order two
in the first, and the only one in the second is `−1` (`eq_neg_one_of_mem_center`). -/
theorem not_nonempty_U3SU2_equiv_U3 : ¬ Nonempty (GroupU3 × SU2 ≃* GroupU3) := by
  rintro ⟨e⟩
  have key : ∀ x : GroupU3 × SU2, x ∈ Subgroup.center _ → x ^ 2 = 1 → x ≠ 1 →
      ((e x : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ) = -1 := fun x hx h2 h1 =>
    eq_neg_one_of_mem_center (mem_center_map e hx) (by rw [← map_pow, h2, map_one])
      (fun h => h1 (e.injective (by rw [h, map_one])))
  have ha := key (1, negOneSU2) (mem_center_prod (Subgroup.one_mem _) negOneSU2_mem_center)
    (Prod.ext (one_pow 2) negOneSU2_sq) (fun h => negOneSU2_ne_one (congrArg Prod.snd h))
  have hb := key (negOneU3, 1) (mem_center_prod negOneU3_mem_center (Subgroup.one_mem _))
    (Prod.ext negOneU3_sq (one_pow 2)) (fun h => negOneU3_ne_one (congrArg Prod.fst h))
  have hab : ((1, negOneSU2) : GroupU3 × SU2) = (negOneU3, 1) :=
    e.injective (Subtype.ext (ha.trans hb.symm))
  exact negOneSU2_ne_one (congrArg Prod.snd hab)

/-! ### The classification -/

/-- **THE JOINT UNBROKEN GROUP, WITH `vac`, AT EVERY SECOND-STAGE VACUUM**: `U(3) × SU(2)` at
`Φ = 0`; `U(3)` when the columns of `Φ ≠ 0` are orthogonal; `SU(3) × {±1}` otherwise. -/
theorem joint_trichotomy (Φ : EWBidoublet) :
    (Φ = 0 ∧ Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* GroupU3 × SU2)) ∨
    (Φ ≠ 0 ∧ (Φᴴ * Φ) 0 1 = 0 ∧ Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* GroupU3)) ∨
    (Φ ≠ 0 ∧ (Φᴴ * Φ) 0 1 ≠ 0 ∧
      Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* SU3 × ℤˣ)) := by
  by_cases hΦ : Φ = 0
  · subst hΦ
    exact Or.inl ⟨rfl, ⟨stabilizerPairZeroEquiv⟩⟩
  · by_cases h01 : (Φᴴ * Φ) 0 1 = 0
    · exact Or.inr (Or.inl ⟨hΦ, h01,
        PatiSalamJointCount.nonempty_stabilizer_pair_equiv_U3_of_orthogonal hΦ h01⟩)
    · exact Or.inr (Or.inr ⟨hΦ, h01, ⟨stabilizerPairEquivSU3Sign hΦ h01⟩⟩)

theorem nonempty_mulEquiv_congr {G G' H H' : Type*} [Group G] [Group G'] [Group H] [Group H']
    (e : G ≃* G') (f : H ≃* H') : Nonempty (G ≃* H) ↔ Nonempty (G' ≃* H') :=
  ⟨fun ⟨g⟩ => ⟨e.symm.trans (g.trans f)⟩, fun ⟨g⟩ => ⟨e.trans (g.trans f.symm)⟩⟩

theorem nonempty_mulEquiv_symm {G H : Type*} [Group G] [Group H] :
    Nonempty (G ≃* H) → Nonempty (H ≃* G) :=
  fun ⟨g⟩ => ⟨g.symm⟩

/-- **WHICH SECOND-STAGE VACUA LEAVE ISOMORPHIC JOINT UNBROKEN GROUPS**, with `vac`: exactly those
that agree on whether `Φ = 0` and on whether the columns are orthogonal. -/
theorem nonempty_stabilizer_pair_equiv_iff (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* MulAction.stabilizer FullGroup (vac, Ψ)) ↔
      ((Φ = 0 ↔ Ψ = 0) ∧ ((Φᴴ * Φ) 0 1 = 0 ↔ (Ψᴴ * Ψ) 0 1 = 0)) := by
  have z : ∀ A : EWBidoublet, A = 0 → (Aᴴ * A) 0 1 = 0 := by
    rintro A rfl
    simp
  rcases joint_trichotomy Φ with ⟨hΦ, ⟨eΦ⟩⟩ | ⟨hΦ, hΦ1, ⟨eΦ⟩⟩ | ⟨hΦ, hΦ1, ⟨eΦ⟩⟩ <;>
  rcases joint_trichotomy Ψ with ⟨hΨ, ⟨eΨ⟩⟩ | ⟨hΨ, hΨ1, ⟨eΨ⟩⟩ | ⟨hΨ, hΨ1, ⟨eΨ⟩⟩ <;>
  rw [nonempty_mulEquiv_congr eΦ eΨ]
  · exact iff_of_true ⟨MulEquiv.refl _⟩ ⟨iff_of_true hΦ hΨ, iff_of_true (z _ hΦ) (z _ hΨ)⟩
  · exact iff_of_false not_nonempty_U3SU2_equiv_U3 (fun h => hΨ (h.1.mp hΦ))
  · exact iff_of_false not_nonempty_U3SU2_equiv_SU3Sign (fun h => hΨ (h.1.mp hΦ))
  · exact iff_of_false (fun h => not_nonempty_U3SU2_equiv_U3 (nonempty_mulEquiv_symm h))
      (fun h => hΦ (h.1.mpr hΨ))
  · exact iff_of_true ⟨MulEquiv.refl _⟩ ⟨iff_of_false hΦ hΨ, iff_of_true hΦ1 hΨ1⟩
  · exact iff_of_false not_nonempty_U3_equiv_SU3Sign (fun h => hΨ1 (h.2.mp hΦ1))
  · exact iff_of_false (fun h => not_nonempty_U3SU2_equiv_SU3Sign (nonempty_mulEquiv_symm h))
      (fun h => hΦ (h.1.mpr hΨ))
  · exact iff_of_false (fun h => not_nonempty_U3_equiv_SU3Sign (nonempty_mulEquiv_symm h))
      (fun h => hΦ1 (h.2.mpr hΨ1))
  · exact iff_of_true ⟨MulEquiv.refl _⟩ ⟨iff_of_false hΦ hΨ, iff_of_false hΦ1 hΨ1⟩

/-- **WHICH SECOND-STAGE VACUA LEAVE `U(3)`, WITH `vac`**: `Φ` leaves a joint unbroken group
isomorphic to `U(3)` exactly when it is nonzero with orthogonal columns — unit 221's
`nonempty_stabilizer_pair_equiv_U3_of_orthogonal` and its converse. -/
theorem nonempty_stabilizer_pair_equiv_U3_iff (Φ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* GroupU3) ↔
      Φ ≠ 0 ∧ (Φᴴ * Φ) 0 1 = 0 := by
  by_cases hΦ : Φ = 0
  · subst hΦ
    exact iff_of_false
      (fun ⟨e⟩ => not_nonempty_U3SU2_equiv_U3 ⟨stabilizerPairZeroEquiv.symm.trans e⟩)
      (fun h => h.1 rfl)
  · refine ⟨fun h => ⟨hΦ, ?_⟩, fun h =>
      PatiSalamJointCount.nonempty_stabilizer_pair_equiv_U3_of_orthogonal hΦ h.2⟩
    by_contra h01
    obtain ⟨e⟩ := h
    exact not_nonempty_U3_equiv_SU3Sign ⟨e.symm.trans (stabilizerPairEquivSU3Sign hΦ h01)⟩

/-- **A pair with non-orthogonal columns is not aligned**: aligned pairs leave `U(3)` (unit 203's
`nonempty_stabilizer_pair_equiv_U3`), and these do not. -/
theorem not_aligned_of_not_orthogonal {Φ : EWBidoublet} (h01 : (Φᴴ * Φ) 0 1 ≠ 0) :
    ¬ PatiSalamVacuumOrbit.Aligned vac Φ := fun h =>
  h01 ((nonempty_stabilizer_pair_equiv_U3_iff Φ).mp
    (PatiSalamVacuumOrbit.nonempty_stabilizer_pair_equiv_U3 vac Φ h)).2

end

end PatiSalamJointClassification
