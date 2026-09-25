/-
  PatiSalamSecondStageTopology: every identification of the electroweak stage's unbroken groups,
  alone and jointly with the estate's first-stage `vac`, as TOPOLOGICAL groups — `SU(2)` or the
  circle for `Φ ≠ 0` alone; `U(3) × SU(2)`, `U(3)` or `SU(3) × {±1}` for the pair — each by a
  homeomorphic isomorphism; and every second-stage stabiliser closed and compact

  Campaign 3 hardening unit 223 (25 September 2026). Spine link L15 (Higgs sector).

  WHY. Units 220 (`ElectroweakUnbrokenGroup`) and 222 (`PatiSalamJointClassification`) identified
  the electroweak stage's unbroken groups, alone and jointly with `vac`, as abstract groups. Unit
  220's NOT list: *"Topology: the isomorphisms are of groups; unit 209's topological upgrades are
  not made here"*; unit 222's: *"Topology: the isomorphisms at `Φ = 0` and at non-orthogonal
  columns are of abstract groups; unit 209's topological upgrade is not made for them"*. This file
  makes them, by unit 212's `continuousMulEquivOfCompact`: a continuous isomorphism out of a
  compact group into a Hausdorff one is an isomorphism of topological groups. The second-stage
  stabilisers needed for that had no closedness theorem, although unit 215's pointer in
  `PatiSalamGaugeAction` says *every stabiliser is closed and compact* (`ERRATUM 696`); (1)
  supplies it.

  WHAT IS PROVED.
  (1) The electroweak stage alone. `continuous_stage2_smul`; **`isClosed_stabilizer_stage2`** and
      **`compactSpace_stabilizer_stage2`**: every second-stage vacuum's unbroken group is closed in
      `SU(2)_L × SU(2)_R`, hence compact — unit 209's statements for the first stage and for pairs,
      at the second stage.
  (2) Unit 220's isomorphisms are continuous — `continuous_stabilizerEquivSU2` (the `SU(2)_R` half),
      `continuous_toComm`, `continuous_stabilizerEquivCircle` (an entry of `V⋆ U V` for a constant
      `V`) — so **`stabilizerContinuousEquivSU2`**, **`stabilizerContinuousEquivCommSU2`**,
      **`stabilizerContinuousEquivCircle`** and **`stabilizerVacEWContinuousEquivCircle`**;
      `nonempty_stabilizer_continuousEquiv_SU2_iff`,
      `nonempty_stabilizer_continuousEquiv_circle_iff` and **`stabilizer_dichotomy_continuous`**:
      unit 220's dichotomy with every `≃*` a `≃ₜ*`.
  (3) Both vacua at once. **`continuous_su3SignHom`**, `ℤˣ` carrying Mathlib's topology on units,
      discrete here (`Units.instDiscreteTopology`) and compact, being finite; at non-orthogonal
      columns the inverse of unit 222's `stabilizerPairEquivSU3Sign` is `u3ToFull ∘ su3SignHom`
      (`continuous_stabilizerPairEquivSU3Sign_symm`, through unit 206's `continuous_u3ToFull`), so
      **`stabilizerPairContinuousEquivSU3Sign : Stab (vac, Φ) ≃ₜ* SU(3) × ℤˣ`**;
      `continuous_stabilizerPairZeroEquiv` (the `U(3)` part through unit 206's
      `stabilizerVacContinuousEquivU3`), so **`stabilizerPairZeroContinuousEquiv : Stab (vac, 0) ≃ₜ*
      U(3) × SU(2)`**, the stabiliser compact by unit 209's `compactSpace_stabilizer_full`.
  (4) **`joint_trichotomy_continuous`**: unit 222's `joint_trichotomy` with every `≃*` a `≃ₜ*`;
      **`nonempty_stabilizer_pair_continuousEquiv_iff`**: two second-stage vacua leave joint groups
      isomorphic as topological groups exactly when they agree on whether `Φ = 0` and on whether
      the columns are orthogonal; **`nonempty_stabilizer_pair_continuousEquiv_U3_iff`**: `Φ` leaves
      `U(3)` as a topological group exactly when it is nonzero with orthogonal columns.

  NOT PROVED, said exactly.
  • Other first-stage vacua: only the estate's `vac`, as in unit 222.
    ⚠ 25 September 2026 (hardening unit 225, `paper_f/PatiSalamPairCriterion.lean`): every rank-one
    first vacuum, as topological groups, there (`joint_trichotomy_of_rank_eq_one`); a rank-two one
    leaves `U(3)` with no `Φ` (`nonempty_stabilizer_pair_continuousEquiv_U3_iff_of_ne_zero`). Kept
    as written (`ERRATUM 94`).
  • Lie-group structure: no smooth structure is put on any group here, for unit 209's reason.
  • The Lie algebras are units 219's and 221's counts; no statement here joins them to these groups.
    ⚠ 25 September 2026 (hardening unit 225, `paper_f/PatiSalamPairCriterion.lean`): for the joint
    groups at `vac`, joined for the isomorphism class there
    (`nonempty_stabilizer_pair_equiv_iff_finrank_eq`); the electroweak stage alone is not.
  • Which vacuum, masses: unchanged from units 220 and 222.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `continuous_stabilizerEquivSU2` and
  `stabilizerContinuousEquivSU2` take `c ≠ 0` and `Φᴴ Φ = c • 1`; `stabilizerContinuousEquivCommSU2`
  takes `Φ ≠ 0`; `continuous_stabilizerEquivCircle` and `stabilizerContinuousEquivCircle` take
  `Φ ≠ 0` and that `Φᴴ Φ` is not a multiple of the identity;
  `nonempty_stabilizer_continuousEquiv_SU2_iff`, `nonempty_stabilizer_continuousEquiv_circle_iff`
  and `stabilizer_dichotomy_continuous` take `Φ ≠ 0`; `continuous_stabilizerPairEquivSU3Sign_symm`
  and `stabilizerPairContinuousEquivSU3Sign` take `Φ ≠ 0` and `(Φᴴ Φ) 0 1 ≠ 0`. The rest take
  elements of their types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 21 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements are unit 209's `continuous_stage1_smul`,
  `isClosed_stabilizer`, `isClosed_stabilizer_full`, `compactSpace_stabilizer` and
  `compactSpace_stabilizer_full`, of which (1) is the second-stage version, and
  `continuous_splitHom` (the same argument for `(A, λ) ↦ λ · A` on `SU(3) × U(1)`); unit 212's
  `continuousMulEquivOfCompact`, used for every `≃ₜ*` here, and
  `continuous_stabilizerVac2EquivCircle` (the same entry-of-a-conjugate argument for
  `commHermitianEquiv` at the first stage); unit 206's `continuous_u3ToFull` and
  `stabilizerVacContinuousEquivU3`, used; and unit 221's
  `nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal`, used. The non-isomorphisms are units
  220's and 222's, applied to the underlying abstract isomorphisms.

  `#print axioms` on all 21 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamJointClassification
import PatiSalamTopologicalCopies

open Matrix PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup PatiSalamRankTwoStabiliser PatiSalamUnbrokenSplit
  PatiSalamStabiliserTopology PatiSalamTopologicalCopies PatiSalamJointClassification
  ElectroweakUnbrokenGroup PatiSalamFirstStageClassification

namespace PatiSalamSecondStageTopology

noncomputable section

/-! ### The electroweak stage alone -/

/-- The second-stage action is continuous in the group element. -/
theorem continuous_stage2_smul (Φ : EWBidoublet) : Continuous fun g : Stage2Group => g • Φ :=
  ((continuous_subtype_val.comp continuous_fst).matrix_mul continuous_const).matrix_mul
    (continuous_star.comp (continuous_subtype_val.comp continuous_snd))

/-- **Every second-stage vacuum's unbroken group is a closed subgroup** of `SU(2)_L × SU(2)_R`. -/
theorem isClosed_stabilizer_stage2 (Φ : EWBidoublet) :
    IsClosed (MulAction.stabilizer Stage2Group Φ : Set Stage2Group) :=
  isClosed_eq (continuous_stage2_smul Φ) continuous_const

/-- **And compact**, for every `Φ`. -/
theorem compactSpace_stabilizer_stage2 (Φ : EWBidoublet) :
    CompactSpace (MulAction.stabilizer Stage2Group Φ) :=
  isCompact_iff_compactSpace.mp (isClosed_stabilizer_stage2 Φ).isCompact

theorem continuous_stabilizerEquivSU2 {Φ : EWBidoublet} {c : ℂ} (hc0 : c ≠ 0)
    (hc : Φᴴ * Φ = c • 1) : Continuous (stabilizerEquivSU2 hc0 hc) :=
  continuous_snd.comp continuous_subtype_val

/-- **Unit 220's `SU(2)`, as a topological group**: when `Φᴴ Φ = c • 1` with `c ≠ 0`. -/
def stabilizerContinuousEquivSU2 {Φ : EWBidoublet} {c : ℂ} (hc0 : c ≠ 0)
    (hc : Φᴴ * Φ = c • 1) : MulAction.stabilizer Stage2Group Φ ≃ₜ* SU2 :=
  haveI := compactSpace_stabilizer_stage2 Φ
  continuousMulEquivOfCompact _ (continuous_stabilizerEquivSU2 hc0 hc)

theorem continuous_toComm (Φ : EWBidoublet) : Continuous (toComm Φ) :=
  continuous_induced_rng.mpr (continuous_snd.comp continuous_subtype_val)

/-- **Unit 220's commutant, as a topological group**: at every `Φ ≠ 0`. -/
def stabilizerContinuousEquivCommSU2 {Φ : EWBidoublet} (hΦ : Φ ≠ 0) :
    MulAction.stabilizer Stage2Group Φ ≃ₜ* commSU2 (Φᴴ * Φ) :=
  haveI := compactSpace_stabilizer_stage2 Φ
  continuousMulEquivOfCompact (stabilizerEquivCommSU2 hΦ) (continuous_toComm Φ)

theorem continuous_stabilizerEquivCircle {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (hns : ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) : Continuous (stabilizerEquivCircle hΦ hns) :=
  continuous_induced_rng.mpr ((continuous_apply 0).comp ((continuous_apply 0).comp
    (((continuous_const.matrix_mul
      ((continuous_subtype_val.comp continuous_snd).comp continuous_subtype_val)).matrix_mul
        continuous_const))))

/-- **Unit 220's circle, as a topological group**: when `Φᴴ Φ` is not a multiple of the identity. -/
def stabilizerContinuousEquivCircle {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (hns : ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) : MulAction.stabilizer Stage2Group Φ ≃ₜ* unitary ℂ :=
  haveI := compactSpace_stabilizer_stage2 Φ
  continuousMulEquivOfCompact _ (continuous_stabilizerEquivCircle hΦ hns)

open scoped ComplexOrder in
theorem nonempty_stabilizer_continuousEquiv_SU2_iff (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    Nonempty (MulAction.stabilizer Stage2Group Φ ≃ₜ* SU2) ↔ ∃ c : ℂ, Φᴴ * Φ = c • 1 := by
  refine ⟨fun ⟨e⟩ => (nonempty_stabilizer_equiv_SU2_iff Φ hΦ).mp ⟨e.toMulEquiv⟩, ?_⟩
  rintro ⟨c, hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΦ (Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa using hc))
  exact ⟨stabilizerContinuousEquivSU2 hc0 hc⟩

theorem nonempty_stabilizer_continuousEquiv_circle_iff (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    Nonempty (MulAction.stabilizer Stage2Group Φ ≃ₜ* unitary ℂ) ↔
      ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1 :=
  ⟨fun ⟨e⟩ => (nonempty_stabilizer_equiv_circle_iff Φ hΦ).mp ⟨e.toMulEquiv⟩,
    fun hns => ⟨stabilizerContinuousEquivCircle hΦ hns⟩⟩

/-- **THE ELECTROWEAK STAGE, CLASSIFIED AS TOPOLOGICAL GROUPS**: unit 220's `stabilizer_dichotomy`
with every `≃*` a `≃ₜ*`. -/
theorem stabilizer_dichotomy_continuous (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    ((∃ c : ℂ, Φᴴ * Φ = c • 1) ∧ Nonempty (MulAction.stabilizer Stage2Group Φ ≃ₜ* SU2)) ∨
    ((¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) ∧
      Nonempty (MulAction.stabilizer Stage2Group Φ ≃ₜ* unitary ℂ)) := by
  by_cases hs : ∃ c : ℂ, Φᴴ * Φ = c • 1
  · exact Or.inl ⟨hs, (nonempty_stabilizer_continuousEquiv_SU2_iff Φ hΦ).mpr hs⟩
  · exact Or.inr ⟨hs, (nonempty_stabilizer_continuousEquiv_circle_iff Φ hΦ).mpr hs⟩

/-- **At the estate's `vacEW`, the circle as a topological group.** -/
def stabilizerVacEWContinuousEquivCircle :
    MulAction.stabilizer Stage2Group vacEW ≃ₜ* unitary ℂ :=
  haveI := compactSpace_stabilizer_stage2 vacEW
  continuousMulEquivOfCompact stabilizerVacEWEquivCircle
    (continuous_stabilizerEquivCircle _ ElectroweakCustodial.not_scalar_vacEW)

/-! ### Both vacua at once -/

/-- **`(A, ε) ↦ ε · A` is continuous**: `ℤˣ` is discrete. -/
theorem continuous_su3SignHom : Continuous su3SignHom :=
  continuous_induced_rng.mpr <|
    (((continuous_of_discreteTopology (f := fun ε : ℤˣ => ((ε : ℤ) : ℂ))).comp
      continuous_snd).smul (continuous_subtype_val.comp continuous_fst))

theorem continuous_stabilizerPairEquivSU3Sign_symm {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 ≠ 0) : Continuous (stabilizerPairEquivSU3Sign hΦ h01).symm := by
  refine continuous_induced_rng.mpr ?_
  have h : (Subtype.val ∘ (stabilizerPairEquivSU3Sign hΦ h01).symm : SU3 × ℤˣ → FullGroup)
      = u3ToFull ∘ su3SignHom := funext (coe_stabilizerPairEquivSU3Sign_symm hΦ h01)
  rw [h]
  exact continuous_u3ToFull.comp continuous_su3SignHom

/-- **AT NON-ORTHOGONAL COLUMNS THE JOINT UNBROKEN GROUP IS `SU(3) × {±1}` AS A TOPOLOGICAL
GROUP**: the inverse is a continuous bijection out of the compact `SU(3) × ℤˣ`. -/
def stabilizerPairContinuousEquivSU3Sign {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 ≠ 0) : MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* SU3 × ℤˣ :=
  (continuousMulEquivOfCompact _ (continuous_stabilizerPairEquivSU3Sign_symm hΦ h01)).symm

theorem continuous_stabilizerPairZeroEquiv : Continuous stabilizerPairZeroEquiv := by
  refine Continuous.prodMk ?_ ?_
  · exact stabilizerVacContinuousEquivU3.continuous.comp
      (continuous_induced_rng.mpr ((continuous_fst.prodMk (continuous_snd.comp continuous_snd)).comp
        continuous_subtype_val))
  · exact (continuous_fst.comp continuous_snd).comp continuous_subtype_val

/-- **AT `Φ = 0` THE JOINT UNBROKEN GROUP IS `U(3) × SU(2)` AS A TOPOLOGICAL GROUP.** -/
def stabilizerPairZeroContinuousEquiv :
    MulAction.stabilizer FullGroup (vac, (0 : EWBidoublet)) ≃ₜ* GroupU3 × SU2 :=
  haveI := compactSpace_stabilizer_full (vac, (0 : EWBidoublet))
  continuousMulEquivOfCompact _ continuous_stabilizerPairZeroEquiv

/-- **THE JOINT UNBROKEN GROUP, WITH `vac`, AT EVERY SECOND-STAGE VACUUM, AS A TOPOLOGICAL GROUP**:
`U(3) × SU(2)` at `Φ = 0`; `U(3)` when the columns of `Φ ≠ 0` are orthogonal; `SU(3) × {±1}`
otherwise. -/
theorem joint_trichotomy_continuous (Φ : EWBidoublet) :
    (Φ = 0 ∧ Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* GroupU3 × SU2)) ∨
    (Φ ≠ 0 ∧ (Φᴴ * Φ) 0 1 = 0 ∧
      Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* GroupU3)) ∨
    (Φ ≠ 0 ∧ (Φᴴ * Φ) 0 1 ≠ 0 ∧
      Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* SU3 × ℤˣ)) := by
  by_cases hΦ : Φ = 0
  · subst hΦ
    exact Or.inl ⟨rfl, ⟨stabilizerPairZeroContinuousEquiv⟩⟩
  · by_cases h01 : (Φᴴ * Φ) 0 1 = 0
    · exact Or.inr (Or.inl ⟨hΦ, h01,
        PatiSalamJointCount.nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal hΦ h01⟩)
    · exact Or.inr (Or.inr ⟨hΦ, h01, ⟨stabilizerPairContinuousEquivSU3Sign hΦ h01⟩⟩)

/-- **WHICH SECOND-STAGE VACUA LEAVE JOINT GROUPS ISOMORPHIC AS TOPOLOGICAL GROUPS**, with `vac`:
exactly those that agree on whether `Φ = 0` and on whether the columns are orthogonal. -/
theorem nonempty_stabilizer_pair_continuousEquiv_iff (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ*
      MulAction.stabilizer FullGroup (vac, Ψ)) ↔
      ((Φ = 0 ↔ Ψ = 0) ∧ ((Φᴴ * Φ) 0 1 = 0 ↔ (Ψᴴ * Ψ) 0 1 = 0)) := by
  refine ⟨fun ⟨e⟩ => (nonempty_stabilizer_pair_equiv_iff Φ Ψ).mp ⟨e.toMulEquiv⟩, fun h => ?_⟩
  rcases joint_trichotomy_continuous Φ with ⟨hΦ, ⟨eΦ⟩⟩ | ⟨hΦ, hΦ1, ⟨eΦ⟩⟩ | ⟨hΦ, hΦ1, ⟨eΦ⟩⟩ <;>
  rcases joint_trichotomy_continuous Ψ with ⟨hΨ, ⟨eΨ⟩⟩ | ⟨hΨ, hΨ1, ⟨eΨ⟩⟩ | ⟨hΨ, hΨ1, ⟨eΨ⟩⟩ <;>
  first
    | exact ⟨eΦ.trans eΨ.symm⟩
    | exact (hΨ (h.1.mp hΦ)).elim
    | exact (hΦ (h.1.mpr hΨ)).elim
    | exact (hΨ1 (h.2.mp hΦ1)).elim
    | exact (hΦ1 (h.2.mpr hΨ1)).elim

/-- **`Φ` leaves `U(3)` as a topological group exactly when it is nonzero with orthogonal
columns.** -/
theorem nonempty_stabilizer_pair_continuousEquiv_U3_iff (Φ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* GroupU3) ↔
      Φ ≠ 0 ∧ (Φᴴ * Φ) 0 1 = 0 :=
  ⟨fun ⟨e⟩ => (nonempty_stabilizer_pair_equiv_U3_iff Φ).mp ⟨e.toMulEquiv⟩, fun h =>
    PatiSalamJointCount.nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal h.1 h.2⟩

end

end PatiSalamSecondStageTopology
