/-
  PatiSalamPairCount: the joint count at every rank-one first-stage vacuum — twelve, nine or eight
  unbroken generators, nine, twelve or thirteen broken — and there the count decides the joint
  group, as an abstract and as a topological group

  Campaign 3 hardening unit 227 (26 September 2026). Spine link L15 (Higgs sector).

  WHY. Unit 225 transported the joint groups from `vac` to every rank-one first vacuum and left
  the counts behind: its (6) lets the number of unbroken generators decide the joint group at `vac`
  only, and its pointer in `PatiSalamJointCount` says *"the counts in (4) are not transported"*.
  Unit 213 proved, for the first stage alone, that the number of BROKEN generators decides the
  group at every nonzero vacuum — the half of the published §6.8's *"determined by Goldstone
  counting"* that the estate can state (`PROPOSED_TAG_CHANGES` entry 31). This file transports the
  joint count by the adjoint action and states the pair's version in broken generators.

  WHAT IS PROVED.
  (1) The adjoint action. `adFull g` conjugates the three components of `Full` (unit 213's
      `conjTL`, three times; `stage1_adFull`); **`jointOrbitAt_adFull`**:
      `jointOrbitAt (g • v) (adFull g p) = g • jointOrbitAt v p` — the first component is unit
      213's `act_adPS`, the second `L Φ − Φ R` conjugated by `g_L` and `g_R`. So
      `adFull_mem_jointStabAt`, `adFull_injective`, `finrank_jointStabAt_le_smul` and
      **`finrank_jointStabAt_smul`**: the number of unbroken generators of a pair is a gauge
      invariant — unit 213's `finrank_stabAt_smul`, for pairs. `jointStabAt_smul_fst`: scaling the
      first vacuum by a nonzero number leaves the joint algebra where it is. Two small facts are
      stated on the way: `smul_zero_pair` (the gauge group fixes the zero pair) and `rank_vac` (the
      chosen first vacuum has rank one).
  (2) **`finrank_jointStabAt_of_rank_eq_one`**: at every rank-one first vacuum `X`, twelve unbroken
      generators at `Φ = 0`, nine when `Φᴴ Φ` commutes with `(Xᴴ X)ᵀ`, eight otherwise — unit 221's
      count, carried by unit 225's `liftR_smul` (`finrank_jointStabAt_eq_vac`), every rank-one
      first vacuum being `r • (g • vac)` by unit 203's `rank_eq_one_iff_mem_orbit`, with unit 225's
      `mul_unitary_eq_zero_iff` and `comm_transpose_iff` for the two conditions.
  (3) **`nonempty_stabilizer_pair_equiv_iff_finrank_eq_of_rank_eq_one`** and
      **`nonempty_stabilizer_pair_continuousEquiv_iff_finrank_eq_of_rank_eq_one`**: two pairs whose
      first vacua have rank one — the same first vacuum or different ones — leave isomorphic joint
      groups exactly when they leave the same number of unbroken generators, as abstract and as
      topological groups. Unit 225's (6) at every rank-one first vacuum;
      `nonempty_stabilizer_pair_continuousEquiv_iff_finrank_eq` is its topological case at `vac`,
      from unit 223's classification.
  (4) Broken generators. `finrank_quotient_jointStabAt_add`: broken and unbroken add up to unit
      183's 21 (`finrank_Full`); **`finrank_quotient_jointStabAt_of_rank_eq_one`**: nine, twelve or
      thirteen broken; **`nonempty_stabilizer_pair_equiv_iff_finrank_broken_eq_of_rank_eq_one`** and
      its topological twin: the number of broken generators decides the joint group at every
      rank-one first vacuum — unit 213's `nonempty_stabilizer_equiv_iff_finrank_broken_eq`, for the
      pair. **`finrank_quotient_jointStabAt_vac_vacEW`**: the chosen pair's twelve, reached from the
      count at every pair; it agrees with unit 183's `finrank_jointBroken`, which reached it from
      `jointStab ≃ u(3)`.

  NOT PROVED, said exactly.
  • `X = 0` and the rank-two first vacua: the joint counts there are not computed, and the groups
    at rank-two pairs are not (unit 225: none of them is `U(3)`).
  • Goldstone's theorem: these are counts of broken generators, as a codimension. That the broken
    directions are massless modes needs a potential the estate does not have (`ASSUMPTIONS_LEDGER`
    60; the NOT lists of units 179 and 184).
  • `adFull` is conjugation of matrices; that it is the differential of the conjugation between the
    two stabilisers (Mathlib's `stabilizerEquivStabilizer`, unit 209's `stabilizerContinuousEquiv`)
    is not stated.
  • Lie-group (smooth) structure, which vacuum, masses: as in units 222, 223 and 225.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `adFull_mem_jointStabAt` takes
  `p ∈ jointStabAt v`; `jointStabAt_smul_fst` takes `c ≠ 0`; `finrank_jointStabAt_eq_vac` takes
  `0 < r`; `finrank_jointStabAt_of_rank_eq_one` and `finrank_quotient_jointStabAt_of_rank_eq_one`
  take `X.rank = 1`; the four `_iff_…_of_rank_eq_one` statements take `X.rank = 1` and
  `Y.rank = 1`. The rest take elements of their types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 20 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements are unit 213's first-stage `adPS`, `act_adPS`,
  `adPS_mem_stabAt`, `adPS_injective`, `finrank_stabAt_le_smul` and `finrank_stabAt_smul`, of which
  (1) is the pair's version (`conjTL`, `conjTL_injective`, `act_adPS` and `act_smul_right` used);
  unit 221's `finrank_jointStabAt_vac` and `finrank_jointStabAt_vac_zero`, through unit 225's
  `finrank_jointStabAt_vac_eq`, used; unit 225's `nonempty_stabilizer_pair_equiv_iff_finrank_eq`,
  the `vac` case of (3), used, with its `exists_stabilizer_pair_continuousEquiv`, `liftR_smul`,
  `comm_transpose_iff`, `mul_unitary_eq_zero_iff` and `conjTranspose_vac_mul_vac`; unit 223's
  `nonempty_stabilizer_pair_continuousEquiv_iff` and unit 222's
  `nonempty_stabilizer_pair_equiv_iff`, used; unit 183's `finrank_Full`, used, and
  `finrank_jointBroken`, agreed with; unit 213's `nonempty_stabilizer_equiv_iff_finrank_broken_eq`,
  of which (4) is the pair's version.

  `#print axioms` on all 20 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamPairCriterion

open Matrix PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup PatiSalamRankTwoStabiliser PatiSalamTwoStageStabiliser
  PatiSalamBrokenCount PatiSalamMatrixLie PatiSalamJointCount PatiSalamJointClassification
  PatiSalamSecondStageTopology PatiSalamVacuumOrbit PatiSalamPairCriterion

namespace PatiSalamPairCount

noncomputable section

/-! ## 1. The adjoint action on both stages, and the joint count as a gauge invariant -/

/-- The adjoint action of `SU(4) × SU(2)_L × SU(2)_R` on `su(4) ⊕ su(2)_L ⊕ su(2)_R`. -/
def adFull (g : FullGroup) : Full →ₗ[ℝ] Full :=
  LinearMap.prodMap (conjTL (mem_specialUnitaryGroup_iff.mp g.1.2).1)
    (LinearMap.prodMap (conjTL (mem_specialUnitaryGroup_iff.mp g.2.1.2).1)
      (conjTL (mem_specialUnitaryGroup_iff.mp g.2.2.2).1))

theorem stage1_adFull (g : FullGroup) (p : Full) :
    stage1 (adFull g p) = adPS (g.1, g.2.2) (stage1 p) := rfl

/-- **The joint orbit map is equivariant**: `jointOrbitAt (g • v) (adFull g p)` is
`g • jointOrbitAt v p`. -/
theorem jointOrbitAt_adFull (g : FullGroup) (v : Bidoublet × EWBidoublet) (p : Full) :
    jointOrbitAt (g • v) (adFull g p) = g • jointOrbitAt v p := by
  refine Prod.ext ?_ ?_
  · rw [full_smul_fst]
    change act (mat4 (stage1 (adFull g p)).1) (mat2 (stage1 (adFull g p)).2) (g • v).1
      = (g.1, g.2.2) • act (mat4 (stage1 p).1) (mat2 (stage1 p).2) v.1
    rw [full_smul_fst, stage1_adFull, act_adPS, stage1_smul_def]
    rfl
  · rw [full_smul_snd]
    have hL := (mem_unitaryGroup_iff').mp (mem_specialUnitaryGroup_iff.mp g.2.1.2).1
    have hR := (mem_unitaryGroup_iff').mp (mem_specialUnitaryGroup_iff.mp g.2.2.2).1
    have hL' : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        star (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) * ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) * M) = M :=
      fun M => by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
    have hR' : ∀ M : Matrix (Fin 2) (Fin 2) ℂ,
        star (g.2.2 : Matrix (Fin 2) (Fin 2) ℂ) * ((g.2.2 : Matrix (Fin 2) (Fin 2) ℂ) * M) = M :=
      fun M => by rw [← Matrix.mul_assoc, hR, Matrix.one_mul]
    change actEW ((g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) * mat2 p.2.1 *
        star (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ))
      ((g.2.2 : Matrix (Fin 2) (Fin 2) ℂ) * mat2 p.2.2 * star (g.2.2 : Matrix (Fin 2) (Fin 2) ℂ))
      (g • v).2 = (g.2.1, g.2.2) • actEW (mat2 p.2.1) (mat2 p.2.2) v.2
    rw [full_smul_snd, stage2_smul_def, stage2_smul_def]
    simp only [actEW, stage2Act, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hL', hR']

theorem smul_zero_pair (g : FullGroup) : g • (0 : Bidoublet × EWBidoublet) = 0 := by
  refine Prod.ext ?_ ?_
  · rw [full_smul_fst, stage1_smul_def]
    simp [stage1Act]
  · rw [full_smul_snd, stage2_smul_def]
    simp [stage2Act]

theorem adFull_mem_jointStabAt {g : FullGroup} {v : Bidoublet × EWBidoublet} {p : Full}
    (hp : p ∈ jointStabAt v) : adFull g p ∈ jointStabAt (g • v) := by
  rw [jointStabAt, LinearMap.mem_ker] at hp ⊢
  rw [jointOrbitAt_adFull, hp, smul_zero_pair]

theorem adFull_injective (g : FullGroup) : Function.Injective (adFull g) :=
  fun _ _ h => Prod.ext
    (conjTL_injective (mem_specialUnitaryGroup_iff.mp g.1.2).1 (congrArg Prod.fst h))
    (Prod.ext
      (conjTL_injective (mem_specialUnitaryGroup_iff.mp g.2.1.2).1 (congrArg (fun x => x.2.1) h))
      (conjTL_injective (mem_specialUnitaryGroup_iff.mp g.2.2.2).1 (congrArg (fun x => x.2.2) h)))

theorem finrank_jointStabAt_le_smul (g : FullGroup) (v : Bidoublet × EWBidoublet) :
    Module.finrank ℝ (jointStabAt v) ≤ Module.finrank ℝ (jointStabAt (g • v)) :=
  LinearMap.finrank_le_finrank_of_injective
    (f := (adFull g).restrict fun _ hp => adFull_mem_jointStabAt hp)
    fun _ _ h => Subtype.ext (adFull_injective g (congrArg Subtype.val h))

/-- **The number of unbroken generators of a pair is a gauge invariant.** -/
theorem finrank_jointStabAt_smul (g : FullGroup) (v : Bidoublet × EWBidoublet) :
    Module.finrank ℝ (jointStabAt (g • v)) = Module.finrank ℝ (jointStabAt v) := by
  refine le_antisymm ?_ (finrank_jointStabAt_le_smul g v)
  have := finrank_jointStabAt_le_smul g⁻¹ (g • v)
  rwa [inv_smul_smul] at this

/-- Scaling the first vacuum leaves the joint unbroken subalgebra where it is. -/
theorem jointStabAt_smul_fst {c : ℂ} (hc : c ≠ 0) (X : Bidoublet) (Φ : EWBidoublet) :
    jointStabAt (c • X, Φ) = jointStabAt (X, Φ) := by
  ext p
  change (act (mat4 (stage1 p).1) (mat2 (stage1 p).2) (c • X),
      actEW (mat2 p.2.1) (mat2 p.2.2) Φ) = 0 ↔
    (act (mat4 (stage1 p).1) (mat2 (stage1 p).2) X, actEW (mat2 p.2.1) (mat2 p.2.2) Φ) = 0
  rw [act_smul_right, Prod.mk_eq_zero, Prod.mk_eq_zero, smul_eq_zero, or_iff_right hc]

/-! ## 2. The count at every rank-one first vacuum, and what it decides -/

theorem rank_vac : vac.rank = 1 :=
  (rank_eq_one_iff_mem_orbit vac).mpr ⟨1, 1, one_pos, by simp⟩

/-- A pair with a rank-one first vacuum has the count of its representative at `vac`. -/
theorem finrank_jointStabAt_eq_vac (g : Stage1Group) {r : ℝ} (hr : 0 < r) (Φ : EWBidoublet) :
    Module.finrank ℝ (jointStabAt ((r : ℂ) • (g • vac), Φ)) =
      Module.finrank ℝ (jointStabAt (vac, Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  rw [← liftR_smul g r Φ, finrank_jointStabAt_smul,
    jointStabAt_smul_fst (Complex.ofReal_ne_zero.mpr hr.ne')]

/-- **THE JOINT COUNT AT EVERY RANK-ONE FIRST VACUUM**: twelve unbroken generators at `Φ = 0`,
nine when `Φᴴ Φ` commutes with `(Xᴴ X)ᵀ`, eight otherwise. -/
theorem finrank_jointStabAt_of_rank_eq_one (X : Bidoublet) (hX : X.rank = 1) (Φ : EWBidoublet) :
    Module.finrank ℝ (jointStabAt (X, Φ)) =
      if Φ = 0 then 12 else if (Φᴴ * Φ) * (Xᴴ * X)ᵀ = (Xᴴ * X)ᵀ * (Φᴴ * Φ) then 9 else 8 := by
  obtain ⟨g, r, hr, rfl⟩ := (rank_eq_one_iff_mem_orbit X).mp hX
  rw [finrank_jointStabAt_eq_vac g hr, finrank_jointStabAt_vac_eq]
  by_cases h0 : Φ = 0
  · rw [if_pos h0, if_pos ((mul_unitary_eq_zero_iff Φ g.2).mpr h0)]
  · rw [if_neg h0, if_neg (fun h => h0 ((mul_unitary_eq_zero_iff Φ g.2).mp h))]
    by_cases hc : (Φᴴ * Φ) * (((r : ℂ) • (g • vac))ᴴ * ((r : ℂ) • (g • vac)))ᵀ =
        (((r : ℂ) • (g • vac))ᴴ * ((r : ℂ) • (g • vac)))ᵀ * (Φᴴ * Φ)
    · rw [if_pos hc, if_pos ((comm_transpose_iff g hr Φ).mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc ((comm_transpose_iff g hr Φ).mpr h))]

/-- **AT EVERY RANK-ONE FIRST VACUUM, THE COUNT DECIDES THE JOINT GROUP**: two pairs whose first
vacua have rank one leave isomorphic joint groups exactly when they leave the same number of
unbroken generators. -/
theorem nonempty_stabilizer_pair_equiv_iff_finrank_eq_of_rank_eq_one {X Y : Bidoublet}
    (hX : X.rank = 1) (hY : Y.rank = 1) (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃* MulAction.stabilizer FullGroup (Y, Ψ)) ↔
      Module.finrank ℝ (jointStabAt (X, Φ)) = Module.finrank ℝ (jointStabAt (Y, Ψ)) := by
  obtain ⟨g, r, hr, rfl, ⟨e⟩⟩ := exists_stabilizer_pair_continuousEquiv X hX Φ
  obtain ⟨h, s, hs, rfl, ⟨f⟩⟩ := exists_stabilizer_pair_continuousEquiv Y hY Ψ
  rw [finrank_jointStabAt_eq_vac g hr, finrank_jointStabAt_eq_vac h hs,
    ← nonempty_stabilizer_pair_equiv_iff_finrank_eq]
  exact ⟨fun ⟨k⟩ => ⟨e.toMulEquiv.symm.trans (k.trans f.toMulEquiv)⟩,
    fun ⟨k⟩ => ⟨e.toMulEquiv.trans (k.trans f.toMulEquiv.symm)⟩⟩

/-- At `vac`, as topological groups: the count decides. -/
theorem nonempty_stabilizer_pair_continuousEquiv_iff_finrank_eq (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* MulAction.stabilizer FullGroup (vac, Ψ)) ↔
      Module.finrank ℝ (jointStabAt (vac, Φ)) = Module.finrank ℝ (jointStabAt (vac, Ψ)) := by
  rw [nonempty_stabilizer_pair_continuousEquiv_iff, ← nonempty_stabilizer_pair_equiv_iff,
    nonempty_stabilizer_pair_equiv_iff_finrank_eq]

/-- **And as topological groups, at every rank-one first vacuum.** -/
theorem nonempty_stabilizer_pair_continuousEquiv_iff_finrank_eq_of_rank_eq_one {X Y : Bidoublet}
    (hX : X.rank = 1) (hY : Y.rank = 1) (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ* MulAction.stabilizer FullGroup (Y, Ψ)) ↔
      Module.finrank ℝ (jointStabAt (X, Φ)) = Module.finrank ℝ (jointStabAt (Y, Ψ)) := by
  obtain ⟨g, r, hr, rfl, ⟨e⟩⟩ := exists_stabilizer_pair_continuousEquiv X hX Φ
  obtain ⟨h, s, hs, rfl, ⟨f⟩⟩ := exists_stabilizer_pair_continuousEquiv Y hY Ψ
  rw [finrank_jointStabAt_eq_vac g hr, finrank_jointStabAt_eq_vac h hs,
    ← nonempty_stabilizer_pair_continuousEquiv_iff_finrank_eq]
  exact ⟨fun ⟨k⟩ => ⟨e.symm.trans (k.trans f)⟩, fun ⟨k⟩ => ⟨e.trans (k.trans f.symm)⟩⟩

/-! ## 3. Broken generators: the count the published sentence names -/

/-- Broken and unbroken generators of any pair add up to the 21 of `su(4) ⊕ su(2) ⊕ su(2)`. -/
theorem finrank_quotient_jointStabAt_add (v : Bidoublet × EWBidoublet) :
    Module.finrank ℝ (Full ⧸ jointStabAt v) + Module.finrank ℝ (jointStabAt v) = 21 := by
  rw [Submodule.finrank_quotient_add_finrank, finrank_Full]

/-- **BROKEN GENERATORS AT EVERY RANK-ONE FIRST VACUUM**: nine at `Φ = 0`, twelve when `Φᴴ Φ`
commutes with `(Xᴴ X)ᵀ`, thirteen otherwise. -/
theorem finrank_quotient_jointStabAt_of_rank_eq_one (X : Bidoublet) (hX : X.rank = 1)
    (Φ : EWBidoublet) :
    Module.finrank ℝ (Full ⧸ jointStabAt (X, Φ)) =
      if Φ = 0 then 9 else if (Φᴴ * Φ) * (Xᴴ * X)ᵀ = (Xᴴ * X)ᵀ * (Φᴴ * Φ) then 12 else 13 := by
  have h := finrank_quotient_jointStabAt_add (X, Φ)
  rw [finrank_jointStabAt_of_rank_eq_one X hX Φ] at h
  split_ifs at h ⊢ <;> omega

/-- **The number of broken generators decides the joint group**, at every rank-one first vacuum. -/
theorem nonempty_stabilizer_pair_equiv_iff_finrank_broken_eq_of_rank_eq_one {X Y : Bidoublet}
    (hX : X.rank = 1) (hY : Y.rank = 1) (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃* MulAction.stabilizer FullGroup (Y, Ψ)) ↔
      Module.finrank ℝ (Full ⧸ jointStabAt (X, Φ)) =
        Module.finrank ℝ (Full ⧸ jointStabAt (Y, Ψ)) := by
  rw [nonempty_stabilizer_pair_equiv_iff_finrank_eq_of_rank_eq_one hX hY]
  have h1 := finrank_quotient_jointStabAt_add (X, Φ)
  have h2 := finrank_quotient_jointStabAt_add (Y, Ψ)
  omega

/-- And as topological groups. -/
theorem nonempty_stabilizer_pair_continuousEquiv_iff_finrank_broken_eq_of_rank_eq_one
    {X Y : Bidoublet} (hX : X.rank = 1) (hY : Y.rank = 1) (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ* MulAction.stabilizer FullGroup (Y, Ψ)) ↔
      Module.finrank ℝ (Full ⧸ jointStabAt (X, Φ)) =
        Module.finrank ℝ (Full ⧸ jointStabAt (Y, Ψ)) := by
  rw [nonempty_stabilizer_pair_continuousEquiv_iff_finrank_eq_of_rank_eq_one hX hY]
  have h1 := finrank_quotient_jointStabAt_add (X, Φ)
  have h2 := finrank_quotient_jointStabAt_add (Y, Ψ)
  omega

/-- The chosen pair: twelve broken generators — unit 183's `finrank_jointBroken`, reached here from
the count at every pair rather than from `jointStab ≃ u(3)`. -/
theorem finrank_quotient_jointStabAt_vac_vacEW :
    Module.finrank ℝ (Full ⧸ jointStabAt (vac, vacEW)) = 12 := by
  have hne : vacEW ≠ 0 := fun h => by
    have := congrFun (congrFun h 0) 0
    simp [vacEW] at this
  have hc : (vacEWᴴ * vacEW) * (vacᴴ * vac)ᵀ = (vacᴴ * vac)ᵀ * (vacEWᴴ * vacEW) := by
    rw [conjTranspose_vac_mul_vac]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vacEW, Matrix.mul_apply, Matrix.single_apply]
  rw [finrank_quotient_jointStabAt_of_rank_eq_one vac rank_vac vacEW, if_neg hne, if_pos hc]

end

end PatiSalamPairCount
