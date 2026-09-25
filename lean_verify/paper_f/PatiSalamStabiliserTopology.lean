/-
  PatiSalamStabiliserTopology.lean — the unbroken group is `U(3)` as a TOPOLOGICAL group, and it is
  compact. Unit 199's two isomorphisms — `stabilizerVacEquivU3` at the first stage and
  `stabilizerPairEquivU3` for both — are continuous with continuous inverses, so they are
  isomorphisms of topological groups (`stabilizerVacContinuousEquivU3`,
  `stabilizerPairContinuousEquivU3`, both `≃ₜ*`). `U(n)` is compact (`isCompact_unitaryGroup`), so
  both unbroken groups are, and the two-stage one is a closed subgroup of
  `SU(4) × SU(2)_L × SU(2)_R` (`isClosed_stabilizer_pair`). By unit 205 the same holds for every
  nonzero `diag(κ, κ')` (`nonempty_stabilizer_vacKK_continuousEquiv_U3`).

  SPINE link L15 (Higgs sector, PARTIAL). Units 199–205 stated every identification as an
  isomorphism of abstract groups and listed topology among what stands. This file supplies it for
  the two identifications the rest are built on. Hardening unit 206, 2026-09-25.

  WHAT IS PROVED.
  (1) Continuity of the building blocks: `continuous_blockDiag4` (every entry of `diag(A, c)` is an
      entry of `A`, or `c`, or `0`) and `continuous_diagConj2`; hence `continuous_u3ToStage1` and
      `continuous_u3ToFull`.
  (2) Continuity back: unit 199's isomorphisms send a stabiliser element to the top-left `3 × 3`
      block of its `SU(4)` component (`stabilizerPairEquivU3_apply`), a continuous function
      (`continuous_stabilizerPairEquivU3`), and their inverses are `u3ToStage1` and `u3ToFull`
      (`coe_stabilizerPairEquivU3_symm`, `continuous_stabilizerPairEquivU3_symm`,
      `coe_stabilizerVacEquivU3_symm`). So **`stabilizerPairContinuousEquivU3`** and
      **`stabilizerVacContinuousEquivU3`**.
  (3) **`isCompact_unitaryGroup`**: `U(n)` is compact for every `n`, being closed (`A⋆ A = 1`) and
      inside the product of closed unit discs, since every entry of a unitary matrix has modulus at
      most one (`norm_entry_le_one_of_mem_unitary`). Hence the instances `instCompactSpaceGroupU3`,
      `instCompactSpaceStabilizerPair` and `instCompactSpaceStabilizerVac`, and
      **`isClosed_stabilizer_pair`**.
  (4) **`nonempty_stabilizer_vacKK_continuousEquiv_U3`**: for `(κ, κ') ≠ 0` the unbroken group of
      `(vac, diag(κ, κ'))` is `U(3)` as a topological group — it is the same subgroup (unit 205's
      `stabilizer_vacKK_eq`).

  NOT PROVED, said exactly.
  • Lie-group structure: no smooth structure is put on either group, and unit 181's Lie-algebra
    identification is not connected to these isomorphisms.
  • Unit 201's splitting `(SU(3) × U(1)) ⧸ ℤ₃` and the conjugated copies of units 203–204 remain
    isomorphisms of abstract groups; only the identifications at `vac`, at `(vac, vacEW)` and, by
    unit 205, at the diagonal vacua are made topological here.
    ⚠ 25 September 2026 (hardening unit 209): both are made topological in
    `PatiSalamTopologicalCopies` — `unbrokenContinuousEquiv` for the splitting;
    `nonempty_stabilizer_continuousEquiv_U3`, `nonempty_stabilizer_pair_continuousEquiv_U3` and
    `nonempty_stabilizer_pair_continuousEquiv_U3_of_conj` for the copies. Kept as written
    (`ERRATUM 94`).
  • The charge's scale; why the vacua have their shapes (no potential); masses.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `norm_entry_le_one_of_mem_unitary` takes a
  unitary matrix; `nonempty_stabilizer_vacKK_continuousEquiv_U3` takes `κ ≠ 0 ∨ κ' ≠ 0`. Nothing
  else takes a hypothesis.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 17 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The pinned Mathlib has `ContinuousMulEquiv` (used) and no compactness
  statement for `Matrix.unitaryGroup` (its sources searched for `isCompact` and `CompactSpace` with
  `unitaryGroup`), so (3) is proved here.

  0 sorry. 0 new axioms. `#print axioms` on all 17 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamTwoComponentVacuum

open Matrix

namespace PatiSalamStabiliserTopology

open PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup

theorem continuous_blockDiag4 :
    Continuous (fun p : Matrix (Fin 3) (Fin 3) ℂ × ℂ => blockDiag4 p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [blockDiag4, of_apply, Fin.lastCases_last, Fin.lastCases_castSucc] <;> fun_prop

theorem continuous_diagConj2 : Continuous diagConj2 := by
  have hv : Continuous (fun d : ℂ => ![d, star d]) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · exact continuous_id
    · exact continuous_star
  exact hv.matrix_diagonal

theorem continuous_u3ToFull : Continuous (u3ToFull : GroupU3 → FullGroup) := by
  have hdet : Continuous (fun A : GroupU3 => (A : Matrix (Fin 3) (Fin 3) ℂ).det) :=
    continuous_subtype_val.matrix_det
  have h4 : Continuous (fun A : GroupU3 => (su4Part A : Matrix (Fin 4) (Fin 4) ℂ)) :=
    continuous_blockDiag4.comp (continuous_subtype_val.prodMk (continuous_star.comp hdet))
  have h2 : Continuous (fun A : GroupU3 => (su2Part A : Matrix (Fin 2) (Fin 2) ℂ)) :=
    continuous_diagConj2.comp hdet
  have h4' : Continuous (fun A : GroupU3 => su4Part A) := continuous_induced_rng.mpr h4
  have h2' : Continuous (fun A : GroupU3 => su2Part A) := continuous_induced_rng.mpr h2
  exact (h4'.prodMk (h2'.prodMk h2')).congr fun A => (u3ToFull_apply A).symm

theorem continuous_stabilizerPairEquivU3 :
    Continuous (stabilizerPairEquivU3 : MulAction.stabilizer FullGroup (vac, vacEW) → GroupU3) := by
  have h : Continuous (fun x : MulAction.stabilizer FullGroup (vac, vacEW) =>
      ((x : FullGroup).1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.castSucc Fin.castSucc) :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).matrix_submatrix _ _
  exact continuous_induced_rng.mpr (h.congr fun x => (stabilizerPairEquivU3_apply x).symm)

theorem coe_stabilizerPairEquivU3_symm (A : GroupU3) :
    ((stabilizerPairEquivU3.symm A : MulAction.stabilizer FullGroup (vac, vacEW)) : FullGroup)
      = u3ToFull A := by
  conv_rhs => rw [← stabilizerPairEquivU3.apply_symm_apply A]
  exact (u3ToFull_stabilizerPairEquivU3 _).symm

theorem continuous_stabilizerPairEquivU3_symm :
    Continuous
      (stabilizerPairEquivU3.symm : GroupU3 → MulAction.stabilizer FullGroup (vac, vacEW)) :=
  continuous_induced_rng.mpr
    (continuous_u3ToFull.congr fun A => (coe_stabilizerPairEquivU3_symm A).symm)

/-- **The unbroken group is `U(3)` as a TOPOLOGICAL group**: unit 199's isomorphism and its inverse
are continuous. -/
noncomputable def stabilizerPairContinuousEquivU3 :
    MulAction.stabilizer FullGroup (vac, vacEW) ≃ₜ* GroupU3 :=
  { stabilizerPairEquivU3 with
    continuous_toFun := continuous_stabilizerPairEquivU3
    continuous_invFun := continuous_stabilizerPairEquivU3_symm }

/-- Every entry of a unitary matrix has modulus at most one. -/
theorem norm_entry_le_one_of_mem_unitary {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) : ‖A i j‖ ≤ 1 := by
  have h := congrFun (congrFun ((Matrix.mem_unitaryGroup_iff').mp hA) j) j
  rw [mul_apply, one_apply_eq] at h
  simp only [star_apply] at h
  have hterm : ∀ k, star (A k j) * A k j = ((‖A k j‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [RCLike.star_def, RCLike.conj_mul]
    push_cast
    rfl
  have hsum : ∑ k, ‖A k j‖ ^ 2 = 1 := by
    have : ((∑ k, ‖A k j‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_sum, ← h]
      exact Finset.sum_congr rfl fun k _ => (hterm k).symm
    exact_mod_cast this
  have hle : ‖A i j‖ ^ 2 ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun k _ => sq_nonneg ‖A k j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (A i j)]

/-- **`U(n)` is compact**: closed, and inside the product of closed unit discs. -/
theorem isCompact_unitaryGroup (n : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hC : IsClosed (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have : (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))
        = {A | star A * A = 1} := by
      ext A
      exact Matrix.mem_unitaryGroup_iff'
    rw [this]
    exact isClosed_eq (continuous_star.matrix_mul continuous_id) continuous_const
  refine hK.of_isClosed_subset hC fun A hA => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
  exact fun i j => norm_entry_le_one_of_mem_unitary hA i j

instance instCompactSpaceGroupU3 : CompactSpace GroupU3 :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup 3)

/-- **The unbroken group is compact.** -/
instance instCompactSpaceStabilizerPair :
    CompactSpace (MulAction.stabilizer FullGroup (vac, vacEW)) :=
  stabilizerPairContinuousEquivU3.toHomeomorph.symm.compactSpace

/-- **The unbroken group is a closed subgroup** of `SU(4) × SU(2)_L × SU(2)_R`: compact, in a
Hausdorff group. -/
theorem isClosed_stabilizer_pair :
    IsClosed (MulAction.stabilizer FullGroup (vac, vacEW) : Set FullGroup) := by
  have h := isCompact_range
    (continuous_subtype_val : Continuous
      (Subtype.val : MulAction.stabilizer FullGroup (vac, vacEW) → FullGroup))
  rw [Subtype.range_coe] at h
  exact h.isClosed

/-! ## The first stage, the same way -/

theorem continuous_u3ToStage1 : Continuous (u3ToStage1 : GroupU3 → Stage1Group) := by
  have hdet : Continuous (fun A : GroupU3 => (A : Matrix (Fin 3) (Fin 3) ℂ).det) :=
    continuous_subtype_val.matrix_det
  have h4' : Continuous (fun A : GroupU3 => su4Part A) := continuous_induced_rng.mpr
    (continuous_blockDiag4.comp (continuous_subtype_val.prodMk (continuous_star.comp hdet)))
  have h2' : Continuous (fun A : GroupU3 => su2Part A) :=
    continuous_induced_rng.mpr (continuous_diagConj2.comp hdet)
  exact (h4'.prodMk h2').congr fun A => rfl

theorem coe_stabilizerVacEquivU3_symm (A : GroupU3) :
    ((stabilizerVacEquivU3.symm A : MulAction.stabilizer Stage1Group vac) : Stage1Group)
      = u3ToStage1 A := by
  conv_rhs => rw [← stabilizerVacEquivU3.apply_symm_apply A]
  exact (u3ToStage1_stabilizerVacEquivU3 _).symm

/-- **The first-stage unbroken group is `U(3)` as a topological group.** -/
noncomputable def stabilizerVacContinuousEquivU3 :
    MulAction.stabilizer Stage1Group vac ≃ₜ* GroupU3 :=
  { stabilizerVacEquivU3 with
    continuous_toFun := by
      have h : Continuous (fun x : MulAction.stabilizer Stage1Group vac =>
          ((x : Stage1Group).1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.castSucc Fin.castSucc) :=
        (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).matrix_submatrix
          _ _
      exact continuous_induced_rng.mpr (h.congr fun x => (stabilizerVacEquivU3_apply x).symm)
    continuous_invFun := continuous_induced_rng.mpr
      (continuous_u3ToStage1.congr fun A => (coe_stabilizerVacEquivU3_symm A).symm) }

instance instCompactSpaceStabilizerVac :
    CompactSpace (MulAction.stabilizer Stage1Group vac) :=
  stabilizerVacContinuousEquivU3.toHomeomorph.symm.compactSpace

/-- **The textbook vacuum too**: for every nonzero `diag(κ, κ')` the unbroken group is the same
subgroup as for `vacEW` (unit 205), hence `U(3)` as a topological group. -/
theorem nonempty_stabilizer_vacKK_continuousEquiv_U3 {κ κ' : ℂ} (hκ : κ ≠ 0 ∨ κ' ≠ 0) :
    Nonempty (MulAction.stabilizer FullGroup (vac, PatiSalamTwoComponentVacuum.vacKK κ κ') ≃ₜ*
      GroupU3) := by
  rw [PatiSalamTwoComponentVacuum.stabilizer_vacKK_eq hκ]
  exact ⟨stabilizerPairContinuousEquivU3⟩

end PatiSalamStabiliserTopology
