/-
  PatiSalamTopologicalCopies.lean — EVERY IDENTIFICATION OF THE UNBROKEN GROUP IS TOPOLOGICAL, AND
  EVERY UNBROKEN GROUP IS COMPACT. Unit 206 made the two identifications at the chosen vacua
  topological and left the rest abstract: the conjugated copies of units 203–204 and unit 201's
  splitting. This file makes them topological. Conjugation carries a stabiliser onto the moved
  point's as topological groups (`stabilizerContinuousEquiv`), so every rank-one first-stage vacuum,
  every aligned pair, and every pair unit 207 found with a conjugate stabiliser leaves `U(3)` as a
  topological group, and at the first stage exactly the rank-one vacua do. `(SU(3) × U(1)) ⧸ ℤ₃`,
  with the quotient topology, is homeomorphic to the unbroken group (`unbrokenContinuousEquiv`).
  And for EVERY vacuum, not only the chosen ones, the unbroken group is a closed subgroup and is
  compact.

  SPINE link L15 (Higgs sector, PARTIAL). Hardening unit 209, 2026-09-25.

  WHAT IS PROVED.
  (1) `stabilizerContinuousEquiv`: in any group with continuous multiplication, Mathlib's
      `MulAction.stabilizerEquivStabilizer` — conjugation by `g` — is a homeomorphism, since it and
      its inverse are restrictions of `x ↦ g x g⁻¹` and `x ↦ g⁻¹ x g`.
  (2) The conjugated copies. **`nonempty_stabilizer_continuousEquiv_U3`**: a rank-one `X` is a
      positive multiple of a point of `vac`'s orbit (unit 203), and rescaling does not move the
      stabiliser. **`nonempty_stabilizer_continuousEquiv_U3_iff`**: with unit 204, for `X ≠ 0`,
      exactly when `X` has rank one. **`nonempty_stabilizer_pair_continuousEquiv_U3`**: aligned
      pairs (unit 203). `nonempty_stabilizer_pair_continuousEquiv_U3_of_conj`: the pairs
      `g • (c • vac, diag(κ, κ'))` of unit 207. `aligned_vac_single` and
      `nonempty_stabilizer_vac_single_continuousEquiv_U3`: `(vac, E₁₀)` is aligned, so a
      second-stage vacuum with no nonzero diagonal entry leaves `U(3)` too.
  (3) The splitting. `continuous_splitHom`; `isCompact_specialUnitaryGroup` (`SU(n)` is compact for
      every `n`) and `isCompact_unitary` (`U(1)` is compact), with their `CompactSpace` instances;
      `continuous_unbrokenEquiv`, through the quotient map; and **`unbrokenContinuousEquiv`**, since
      a continuous bijection from a compact space to a Hausdorff one is a homeomorphism (Mathlib's
      `Continuous.homeoOfEquivCompactToT2`).
  (4) Every vacuum. `continuous_stage1_smul` and `continuous_full_smul` (the actions are continuous
      in the group element); **`isClosed_stabilizer`** and **`isClosed_stabilizer_full`**: the
      stabiliser of any first-stage vacuum, and of any pair, is closed; `compactSpace_stabilizer`
      and `compactSpace_stabilizer_full`: and compact, the groups being compact by (3).
      ⚠ 25 September 2026 (hardening unit 223, `paper_f/PatiSalamSecondStageTopology.lean`,
      `ERRATUM 696`): the title's *every unbroken group is compact* and *for EVERY vacuum* are (4)'s
      first stage and pairs; the second-stage action and its stabilisers, alone, had no such theorem
      until unit 223 (`continuous_stage2_smul`, `isClosed_stabilizer_stage2`,
      `compactSpace_stabilizer_stage2`).

  NOT PROVED, said exactly.
  • Lie-group structure. The pinned Mathlib has smooth `LieGroup` instances for the units of a
    normed algebra, for the circle and for products, none for `unitaryGroup` or
    `specialUnitaryGroup`, and no closed-subgroup theorem to transfer one; no smooth structure is
    put on any group here.
  • Which second-stage vacua leave a group merely isomorphic to `U(3)` (unit 207's residue).
    ⚠ 25 September 2026 (hardening unit 221, `paper_f/PatiSalamJointCount.lean`): decided there for
    the first vacuum `vac` in one direction, and at the Lie-algebra level in the other — a nonzero
    `Φ` with orthogonal columns leaves `U(3)`, as a topological group
    (`nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal`), and any other leaves an
    eight-dimensional joint unbroken subalgebra (`finrank_jointStabAt_vac`). Whether one of those
    leaves a group isomorphic to `U(3)` stands: a dimension is not an invariant of abstract groups.
    ⚠ 25 September 2026 (hardening unit 222, `paper_f/PatiSalamJointClassification.lean`): decided —
    none does: the group there is `SU(3) × {±1}`, and with `vac` a second-stage vacuum `Φ` leaves a
    group isomorphic to `U(3)` exactly when it is nonzero with orthogonal columns
    (`nonempty_stabilizer_pair_equiv_U3_iff`). At those the isomorphism is topological (unit 221);
    at the others the groups are identified as abstract groups only. Other first vacua still stand.
    ⚠ 25 September 2026 (hardening unit 223, `paper_f/PatiSalamSecondStageTopology.lean`): and at
    the others too, as topological groups (`stabilizerPairZeroContinuousEquiv`,
    `stabilizerPairContinuousEquivSU3Sign`, `nonempty_stabilizer_pair_continuousEquiv_U3_iff`).
    Other first vacua still stand.
    ⚠ 25 September 2026 (hardening unit 225, `paper_f/PatiSalamPairCriterion.lean`): both pointers'
    *other first vacua*, decided for every nonzero first vacuum, as topological groups too: `(X, Φ)`
    leaves `U(3)` exactly when `X` has rank one, `Φ ≠ 0` and `Φᴴ Φ` commutes with `(Xᴴ X)ᵀ`
    (`nonempty_stabilizer_pair_continuousEquiv_U3_iff_of_ne_zero`).
  • Why the vacua have these shapes (no potential); the magnitudes; the charge's scale; masses.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `stabilizerContinuousEquiv` takes `b = g • a`
  in a group with continuous multiplication; `nonempty_stabilizer_continuousEquiv_U3` takes rank
  one, and its `_iff` takes `X ≠ 0`; `nonempty_stabilizer_pair_continuousEquiv_U3` takes
  `Aligned X Φ`; `nonempty_stabilizer_pair_continuousEquiv_U3_of_conj` takes `c ≠ 0` and
  `κ ≠ 0 ∨ κ' ≠ 0`. Nothing else takes a hypothesis.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 20 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The pinned Mathlib supplies `stabilizerEquivStabilizer` (abstract),
  `homeoOfEquivCompactToT2`, `isClosed_unitary` and `CStarRing.norm_of_mem_unitary`, all used, and
  has no compactness statement for `specialUnitaryGroup` or `unitary ℂ`.

  0 sorry. 0 new axioms. `#print axioms` on all 20 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamSameStabiliser
import PatiSalamStabiliserTopology
import PatiSalamUnbrokenSplit
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Basic

open Matrix

namespace PatiSalamTopologicalCopies

open PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup PatiSalamVacuumOrbit PatiSalamStabiliserTopology

/-- Conjugation carries a stabiliser onto the stabiliser of the moved point, as topological groups,
in any group whose multiplication is continuous. -/
noncomputable def stabilizerContinuousEquiv {G α : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] [MulAction G α] {g : G} {a b : α} (hg : b = g • a) :
    MulAction.stabilizer G a ≃ₜ* MulAction.stabilizer G b :=
  { MulAction.stabilizerEquivStabilizer hg with
    continuous_toFun := continuous_induced_rng.mpr <|
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).congr fun x =>
        (MulAction.stabilizerEquivStabilizer_apply hg x).symm
    continuous_invFun := continuous_induced_rng.mpr <|
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).congr fun x =>
        (MulAction.stabilizerEquivStabilizer_symm_apply hg x).symm }

/-- **Every rank-one first-stage vacuum leaves `U(3)` as a topological group.** -/
theorem nonempty_stabilizer_continuousEquiv_U3 (X : Bidoublet) (hX : X.rank = 1) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃ₜ* GroupU3) := by
  obtain ⟨g, r, hr, rfl⟩ := (rank_eq_one_iff_mem_orbit X).mp hX
  rw [stabilizer_smul_of_ne_zero (by exact_mod_cast hr.ne') (g • vac)]
  exact ⟨(stabilizerContinuousEquiv (rfl : g • vac = g • vac)).symm.trans
    stabilizerVacContinuousEquivU3⟩

/-- **At the first stage, exactly the rank-one vacua leave `U(3)` as a topological group.** -/
theorem nonempty_stabilizer_continuousEquiv_U3_iff (X : Bidoublet) (hX : X ≠ 0) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃ₜ* GroupU3) ↔ X.rank = 1 := by
  constructor
  · rintro ⟨e⟩
    exact (PatiSalamRankTwoVacuum.nonempty_stabilizer_equiv_U3_iff X hX).mp ⟨e.toMulEquiv⟩
  · exact nonempty_stabilizer_continuousEquiv_U3 X

/-- **Every aligned pair of vacua leaves `U(3)` as a topological group.** -/
theorem nonempty_stabilizer_pair_continuousEquiv_U3 (X : Bidoublet) (Φ : EWBidoublet)
    (h : Aligned X Φ) : Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ* GroupU3) := by
  obtain ⟨g, r, s, hr, hs, rfl, rfl⟩ := (aligned_iff_mem_orbit X Φ).mp h
  rw [stabilizer_pair_smul (by exact_mod_cast hr.ne') (by exact_mod_cast hs.ne')
    (g • (vac, vacEW))]
  exact ⟨(stabilizerContinuousEquiv (rfl : g • (vac, vacEW) = g • (vac, vacEW))).symm.trans
    stabilizerPairContinuousEquivU3⟩

/-- **Every pair whose stabiliser is a conjugate of the unbroken group leaves `U(3)` as a
topological group** — by unit 207, the gauge transforms of `(c • vac, diag(κ, κ'))`. -/
theorem nonempty_stabilizer_pair_continuousEquiv_U3_of_conj {g : FullGroup} {c κ κ' : ℂ}
    (hc : c ≠ 0) (hκ : κ ≠ 0 ∨ κ' ≠ 0) :
    Nonempty (MulAction.stabilizer FullGroup
      (g • (c • vac, PatiSalamTwoComponentVacuum.vacKK κ κ')) ≃ₜ* GroupU3) := by
  have h := (PatiSalamSameStabiliser.stabilizer_pair_eq_iff
    (c • vac, PatiSalamTwoComponentVacuum.vacKK κ κ')).mpr ⟨⟨c, hc, rfl⟩, κ, κ', hκ, rfl⟩
  refine ⟨(stabilizerContinuousEquiv rfl).symm.trans ?_⟩
  rw [h]
  exact stabilizerPairContinuousEquivU3

/-- **An off-diagonal second-stage vacuum in unit 203's aligned family**: `(vac, E₁₀)` is aligned,
though `E₁₀` has no nonzero diagonal entry. -/
theorem aligned_vac_single : Aligned vac (Matrix.single 1 0 1 : EWBidoublet) := by
  refine ⟨Pi.single 3 1, Pi.single 0 1, Pi.single 1 1, 1, fun h => ?_, fun h => ?_, fun h => ?_,
    one_ne_zero, ?_, ?_⟩
  · simpa using congrFun h 3
  · simpa using congrFun h 0
  · simpa using congrFun h 1
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [vac, vecMulVec_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply]

/-- **And it leaves `U(3)` unbroken as a topological group.** -/
theorem nonempty_stabilizer_vac_single_continuousEquiv_U3 :
    Nonempty (MulAction.stabilizer FullGroup (vac, (Matrix.single 1 0 1 : EWBidoublet)) ≃ₜ*
      GroupU3) :=
  nonempty_stabilizer_pair_continuousEquiv_U3 _ _ aligned_vac_single

open PatiSalamUnbrokenSplit

theorem continuous_splitHom : Continuous splitHom :=
  continuous_induced_rng.mpr <|
    ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst))

/-- **`SU(n)` is compact** for every `n`: `U(n)` cut by the closed condition `det = 1`. -/
theorem isCompact_specialUnitaryGroup (n : ℕ) :
    IsCompact (specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have : (specialUnitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))
      = (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ∩ {A | A.det = 1} := by
    ext A
    exact mem_specialUnitaryGroup_iff
  rw [this]
  exact (isCompact_unitaryGroup n).inter_right
    (isClosed_eq continuous_id.matrix_det continuous_const)

instance instCompactSpaceSpecialUnitary (n : ℕ) : CompactSpace (specialUnitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_specialUnitaryGroup n)

theorem isCompact_unitary : IsCompact (unitary ℂ : Set ℂ) :=
  (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_unitary fun z hz => by
    rw [Metric.mem_closedBall, dist_zero_right, CStarRing.norm_of_mem_unitary hz]

instance instCompactSpaceUnitary : CompactSpace (unitary ℂ) :=
  isCompact_iff_compactSpace.mp isCompact_unitary

theorem continuous_unbrokenEquiv : Continuous unbrokenEquiv := by
  refine (QuotientGroup.isQuotientMap_mk splitHom.ker).continuous_iff.mpr ?_
  refine (continuous_stabilizerPairEquivU3_symm.comp continuous_splitHom).congr fun p => ?_
  rfl

/-- **Unit 201's splitting is an isomorphism of topological groups**: `(SU(3) × U(1)) ⧸ ℤ₃` with the
quotient topology is homeomorphic to the unbroken group — a continuous bijection from a compact
space to a Hausdorff one. -/
noncomputable def unbrokenContinuousEquiv :
    (SU3 × unitary ℂ) ⧸ splitHom.ker ≃ₜ* MulAction.stabilizer FullGroup (vac, vacEW) :=
  { unbrokenEquiv with
    continuous_toFun := continuous_unbrokenEquiv
    continuous_invFun :=
      (continuous_unbrokenEquiv.homeoOfEquivCompactToT2
        (f := unbrokenEquiv.toEquiv)).symm.continuous }

/-- The first-stage action is continuous in the group element. -/
theorem continuous_stage1_smul (X : Bidoublet) : Continuous fun g : Stage1Group => g • X :=
  ((continuous_subtype_val.comp continuous_fst).matrix_mul continuous_const).matrix_mul
    (continuous_subtype_val.comp continuous_snd).matrix_transpose

/-- The action on both fields is continuous in the group element. -/
theorem continuous_full_smul (p : Bidoublet × EWBidoublet) :
    Continuous fun g : FullGroup => g • p :=
  (((continuous_subtype_val.comp continuous_fst).matrix_mul continuous_const).matrix_mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)).matrix_transpose).prodMk
    (((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).matrix_mul
      continuous_const).matrix_mul
      (continuous_star.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

/-- **Every first-stage vacuum's unbroken group is a closed subgroup**, whatever the vacuum. -/
theorem isClosed_stabilizer (X : Bidoublet) :
    IsClosed (MulAction.stabilizer Stage1Group X : Set Stage1Group) :=
  isClosed_eq (continuous_stage1_smul X) continuous_const

/-- **Every pair's unbroken group is a closed subgroup** of `SU(4) × SU(2)_L × SU(2)_R`. -/
theorem isClosed_stabilizer_full (p : Bidoublet × EWBidoublet) :
    IsClosed (MulAction.stabilizer FullGroup p : Set FullGroup) :=
  isClosed_eq (continuous_full_smul p) continuous_const

/-- **And compact**, for every vacuum: a closed subgroup of a compact group. -/
theorem compactSpace_stabilizer (X : Bidoublet) :
    CompactSpace (MulAction.stabilizer Stage1Group X) :=
  isCompact_iff_compactSpace.mp (isClosed_stabilizer X).isCompact

theorem compactSpace_stabilizer_full (p : Bidoublet × EWBidoublet) :
    CompactSpace (MulAction.stabilizer FullGroup p) :=
  isCompact_iff_compactSpace.mp (isClosed_stabilizer_full p).isCompact

end PatiSalamTopologicalCopies
