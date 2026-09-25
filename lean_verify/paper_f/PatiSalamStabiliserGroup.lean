/-
  PatiSalamStabiliserGroup.lean — the stabiliser SUBGROUPS of the two Higgs vacua, computed: each is
  `U(3)`. Inside `SU(4) × SU(2)_R` the group fixing the `(4, 1, 2)` vacuum is isomorphic to `U(3)`
  (`stabilizerVacEquivU3`); inside `SU(4) × SU(2)_L × SU(2)_R` the group fixing both vacua is
  isomorphic to `U(3)` (`stabilizerPairEquivU3`). Each isomorphism sends an element to the top-left
  `3 × 3` block of its `SU(4)` component.

  SPINE link L15 (Higgs sector, PARTIAL) — the residue its row named on 25 September (unit 191): the
  stabiliser SUBGROUP was named, not computed, and not shown to be `U(3)`. Hardening unit 199,
  2026-09-25.

  WHY. Units 178–184 computed the unbroken ALGEBRAS: the first vacuum's stabiliser is `u(3)` (units
  179–180), and so is the joint stabiliser of both, with the charge at its centre (units 183–184).
  Unit 191 made the gauge GROUP act on both Higgs fields (`PatiSalamGaugeAction`) and wrote the
  stabilisers as `MulAction.stabilizer`, but said what is in them only for one-parameter subgroups.
  This file computes the groups themselves.

  WHAT IS PROVED.
  (1) `blockDiag4 A c` — `diag(A, c)` in `M₄(ℂ)` — with its products, adjoint, identity and
      determinant (`det_blockDiag4 : det (diag(A, c)) = det A · c`, by expansion along the last
      row); `diagConj2 d = diag(d, d̄)` in `M₂(ℂ)`, special unitary when `d̄ d = 1`.
  (2) `u3ToStage1 : U(3) →* SU(4) × SU(2)`, `A ↦ (diag(A, det A⁻¹), diag(det A, det A⁻¹))`, with
      `det A⁻¹ = star (det A)` on `U(3)`; injective (`u3ToStage1_injective`).
  (3) `range_u3ToStage1`: its range IS the stabiliser of `vac`. One inclusion is a computation
      (`u3ToStage1_mem`). For the other (`exists_u3ToStage1_eq`): the `(i, j)` entry of
      `(g, h) • vac` is `g i 3 · h j 0` (`stage1_smul_vac_apply`), so column 3 of `g` is a multiple
      of `e₃` and `h 1 0 = 0`; unitarity of `g` then clears row 3 off the corner, so
      `g = diag(A, c)` with `A` unitary; `det g = det A · c = 1` gives `c = det A⁻¹`; and a special
      unitary `2 × 2` matrix with `h 1 0 = 0` is `diag(h 0 0, h 0 0⁻¹)` (`eq_diagConj2_of`).
  (4) **`stabilizerVacEquivU3 : MulAction.stabilizer (SU(4) × SU(2)) vac ≃* U(3)`**, and
      `stabilizerVacEquivU3_apply`: the image of `(g, h)` is the top-left block of `g`.
  (5) Both vacua at once. `mem_stabilizer_pair_iff` splits the joint stabiliser into its two stages;
      `u3ToFull` adds `SU(2)_L`'s component `diag(det A, det A⁻¹)`; the second vacuum forces
      `SU(2)_L`'s component to equal `SU(2)_R`'s (`exists_u3ToFull_eq`); and
      **`stabilizerPairEquivU3 : MulAction.stabilizer (SU(4) × SU(2)_L × SU(2)_R) (vac, vacEW) ≃*
      U(3)`**, with `stabilizerPairEquivU3_apply` as in (4).

  NOT PROVED, said exactly.
  • The VACUA are still chosen (`ASSUMPTIONS_LEDGER` 60): these are the stabilisers of `vac` and
    `vacEW`, and a vector of another orbit type has another stabiliser.
  • Nothing topological. `≃*` is an isomorphism of abstract groups; that it is a homeomorphism or an
    isomorphism of Lie groups is not stated, and the group's Lie algebra is not computed here. The
    link to the algebra stabilisers of units 179–184 is still the one unit 191 proved:
    exponentials of elements of `jointStab` lie in the group stabiliser
    (`PatiSalamGaugeAction.expFull_mem_stabilizer`).
  • No splitting into `SU(3)_c × U(1)_Q`. `U(3)` is `(SU(3) × U(1)) ⧸ ℤ₃`, and that quotient is not
    written. Which `U(1)` is the electric charge is unit 184's statement about algebras
    (`jointStabEquivU3_qFull`); its group-level counterpart — that the centre of `U(3)` is the
    charge's one-parameter subgroup — is not proved here.
  • Still no potential, no masses and no gauge bosons as objects (unit 191's NOT list stands).

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `blockDiag4_mem_unitary` takes `A` unitary and
  `star c * c = 1`; `diagConj2_mem_specialUnitary` takes `star d * d = 1`; `eq_diagConj2_of` takes
  `h` special unitary, `d * star d = 1`, `h 0 0 = d` and `h 1 0 = 0`; `exists_u3ToStage1_eq` and
  `exists_u3ToFull_eq` take membership of the stabiliser. Nothing else is assumed.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 48 declaration names were run
  against the estate's theorem index and against every `paper_f` declaration: none is taken. The
  first draft's `blk_mul`, `blk_one` and `dg_mul` collided with `CliffordEvenBlock` and
  `CliffordPeriodicity`, and its `U3` with `PatiSalamStabiliserDimension.U3` (the Lie algebra
  `u(3)`); all were renamed. No estate declaration states a stabiliser `≃*` a unitary group (the
  index was queried for `stabilizer` and `unitaryGroup (Fin 3)`).

  0 sorry. 0 new axioms. `#print axioms` on all 48 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamGaugeAction

open Matrix

namespace PatiSalamStabiliserGroup

/-- `diag(A, c)` in `M₄(ℂ)`. -/
def blockDiag4 (A : Matrix (Fin 3) (Fin 3) ℂ) (c : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of fun i j => Fin.lastCases (Fin.lastCases c (fun _ => 0) j)
    (fun i' => Fin.lastCases 0 (fun j' => A i' j') j) i

variable (A B : Matrix (Fin 3) (Fin 3) ℂ) (c d : ℂ)

theorem blockDiag4_cc (i j : Fin 3) : blockDiag4 A c i.castSucc j.castSucc = A i j := by
  simp only [blockDiag4, of_apply, Fin.lastCases_castSucc]
theorem blockDiag4_cl (i : Fin 3) : blockDiag4 A c i.castSucc (Fin.last 3) = 0 := by
  simp only [blockDiag4, of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
theorem blockDiag4_lc (j : Fin 3) : blockDiag4 A c (Fin.last 3) j.castSucc = 0 := by
  simp only [blockDiag4, of_apply, Fin.lastCases_castSucc, Fin.lastCases_last]
theorem blockDiag4_ll : blockDiag4 A c (Fin.last 3) (Fin.last 3) = c := by
  simp only [blockDiag4, of_apply, Fin.lastCases_last]

theorem blockDiag4_mul : blockDiag4 A c * blockDiag4 B d = blockDiag4 (A * B) (c * d) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, blockDiag4_cc, blockDiag4_cl, blockDiag4_lc,
      blockDiag4_ll, mul_zero, zero_mul, add_zero, zero_add, Finset.sum_const_zero]

theorem blockDiag4_conjTranspose : (blockDiag4 A c)ᴴ = blockDiag4 Aᴴ (star c) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [conjTranspose_apply, blockDiag4_cc, blockDiag4_cl, blockDiag4_lc, blockDiag4_ll,
      star_zero]

theorem blockDiag4_one : blockDiag4 1 1 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp only [blockDiag4_cc, blockDiag4_cl, blockDiag4_lc, blockDiag4_ll, one_apply,
      Fin.castSucc_inj, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne', if_false,
      if_true]

theorem det_blockDiag4 : (blockDiag4 A c).det = A.det * c := by
  have hsub : (blockDiag4 A c).submatrix (Fin.last 3).succAbove (Fin.last 3).succAbove = A := by
    ext i j; simp only [submatrix_apply, Fin.succAbove_last, blockDiag4_cc]
  rw [Matrix.det_succ_row _ (Fin.last 3), Fin.sum_univ_castSucc]
  simp only [blockDiag4_lc, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, blockDiag4_ll,
    hsub]
  norm_num [Fin.val_last]
  ring

theorem blockDiag4_mem_unitary {A : Matrix (Fin 3) (Fin 3) ℂ} (hA : A ∈ unitaryGroup (Fin 3) ℂ)
    {c : ℂ} (hc : star c * c = 1) : blockDiag4 A c ∈ unitaryGroup (Fin 4) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, blockDiag4_conjTranspose, blockDiag4_mul,
    ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp hA, hc, blockDiag4_one]

/-- `diag(d, d̄)` in `M₂(ℂ)`. -/
noncomputable def diagConj2 (d : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := diagonal ![d, star d]

theorem diagConj2_mul (d e : ℂ) : diagConj2 d * diagConj2 e = diagConj2 (d * e) := by
  simp only [diagConj2, diagonal_mul_diagonal]
  congr 1; ext i; fin_cases i <;> simp

theorem diagConj2_one : diagConj2 1 = 1 := by
  rw [diagConj2, ← diagonal_one]; congr 1; ext i; fin_cases i <;> simp

theorem star_diagConj2 (d : ℂ) : star (diagConj2 d) = diagConj2 (star d) := by
  rw [star_eq_conjTranspose, diagConj2, diagonal_conjTranspose]
  congr 1; ext i; fin_cases i <;> simp

theorem det_diagConj2 (d : ℂ) : (diagConj2 d).det = d * star d := by
  simp [diagConj2, det_diagonal, Fin.prod_univ_two]

theorem diagConj2_mem_specialUnitary {d : ℂ} (hd : star d * d = 1) :
    diagConj2 d ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff', star_diagConj2, diagConj2_mul, hd,
    diagConj2_one, det_diagConj2, mul_comm, hd]
  exact ⟨rfl, rfl⟩

abbrev GroupU3 := Matrix.unitaryGroup (Fin 3) ℂ

theorem star_det_mul_det (A : GroupU3) : star A.1.det * A.1.det = 1 :=
  Unitary.star_mul_self_of_mem (det_of_mem_unitary A.2)

theorem det_mul_star_det (A : GroupU3) : A.1.det * star A.1.det = 1 :=
  Unitary.mul_star_self_of_mem (det_of_mem_unitary A.2)

/-- The `SU(4)` component: `diag(A, det A⁻¹)`, with `det A⁻¹ = star (det A)`. -/
noncomputable def su4Part (A : GroupU3) : specialUnitaryGroup (Fin 4) ℂ :=
  ⟨blockDiag4 (A : Matrix (Fin 3) (Fin 3) ℂ) (star (A : Matrix (Fin 3) (Fin 3) ℂ).det),
    mem_specialUnitaryGroup_iff.mpr
      ⟨blockDiag4_mem_unitary A.2 (by rw [star_star]; exact det_mul_star_det A),
        by rw [det_blockDiag4]; exact det_mul_star_det A⟩⟩

/-- The `SU(2)_R` component: `diag(det A, det A⁻¹)`. -/
noncomputable def su2Part (A : GroupU3) : specialUnitaryGroup (Fin 2) ℂ :=
  ⟨diagConj2 (A : Matrix (Fin 3) (Fin 3) ℂ).det, diagConj2_mem_specialUnitary (star_det_mul_det A)⟩

noncomputable def u3ToStage1 : GroupU3 →* PatiSalamGaugeAction.Stage1Group where
  toFun A := (su4Part A, su2Part A)
  map_one' := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp [su4Part, det_one, star_one, blockDiag4_one]
    · simp [su2Part, det_one, diagConj2_one]
  map_mul' A B := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp only [su4Part, Prod.fst_mul, Submonoid.coe_mul, blockDiag4_mul, det_mul, star_mul']
    · simp only [su2Part, Prod.snd_mul, Submonoid.coe_mul, diagConj2_mul, det_mul]

theorem u3ToStage1_injective : Function.Injective u3ToStage1 := by
  intro A B h
  have h1 := congrArg
    (fun x : PatiSalamGaugeAction.Stage1Group => (x.1 : Matrix (Fin 4) (Fin 4) ℂ)) h
  simp only [u3ToStage1, MonoidHom.coe_mk, OneHom.coe_mk, su4Part] at h1
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h1 i.castSucc) j.castSucc
  rwa [blockDiag4_cc, blockDiag4_cc] at this

theorem blockDiag4_inj {A B : Matrix (Fin 3) (Fin 3) ℂ} {c d : ℂ}
    (h : blockDiag4 A c = blockDiag4 B d) : A = B ∧ c = d := by
  refine ⟨?_, ?_⟩
  · ext i j
    have := congrFun (congrFun h i.castSucc) j.castSucc
    rwa [blockDiag4_cc, blockDiag4_cc] at this
  · have := congrFun (congrFun h (Fin.last 3)) (Fin.last 3)
    rwa [blockDiag4_ll, blockDiag4_ll] at this

open PatiSalamVacuumStabiliser PatiSalamGaugeAction

theorem vac_last_zero : vac (Fin.last 3) 0 = 1 := by simp [vac]
theorem vac_last_one : vac (Fin.last 3) 1 = 0 := by simp [vac]
theorem vac_castSucc (i : Fin 3) (j : Fin 2) : vac i.castSucc j = 0 := by
  simp only [vac, single_apply]
  rw [if_neg]
  rintro ⟨h, -⟩
  exact (Fin.castSucc_lt_last i).ne' h

theorem stage1_smul_vac_apply (g : Stage1Group) (i : Fin 4) (j : Fin 2) :
    (g • vac) i j
      = (g.1 : Matrix (Fin 4) (Fin 4) ℂ) i (Fin.last 3)
        * (g.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0 := by
  rw [stage1_smul_def, stage1Act, vac]
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_four]

theorem mem_stabilizer_vac_iff (g : Stage1Group) : g ∈ MulAction.stabilizer Stage1Group vac ↔
    ∀ i j, (g.1 : Matrix (Fin 4) (Fin 4) ℂ) i (Fin.last 3) * (g.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0
      = vac i j := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h i j; rw [← stage1_smul_vac_apply, h]
  · intro h; ext i j; rw [stage1_smul_vac_apply, h]

theorem u3ToStage1_mem (A : GroupU3) : u3ToStage1 A ∈ MulAction.stabilizer Stage1Group vac := by
  rw [mem_stabilizer_vac_iff]
  intro i j
  simp only [u3ToStage1, MonoidHom.coe_mk, OneHom.coe_mk, su4Part, su2Part]
  induction i using Fin.lastCases with
  | last =>
    rw [blockDiag4_ll]
    fin_cases j
    · simp only [diagConj2, Fin.zero_eta, diagonal_apply_eq, Matrix.cons_val_zero]
      rw [star_det_mul_det, vac_last_zero]
    · simp only [diagConj2, Fin.mk_one, diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0), mul_zero]
      rw [vac_last_one]
  | cast i => rw [blockDiag4_cl, zero_mul, vac_castSucc]

/-- A `2 × 2` special unitary matrix with `h 1 0 = 0` and `h 0 0 = d` is `diag(d, d̄)`. -/
theorem eq_diagConj2_of {h : Matrix (Fin 2) (Fin 2) ℂ} (hh : h ∈ specialUnitaryGroup (Fin 2) ℂ)
    {d : ℂ} (hd : d * star d = 1) (h00 : h 0 0 = d) (h10 : h 1 0 = 0) : h = diagConj2 d := by
  obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp hh
  have hs : star h * h = 1 := mem_unitaryGroup_iff'.mp hU
  have hd0 : d ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have h01 : h 0 1 = 0 := by
    have e := congrFun (congrFun hs 1) 0
    simp only [mul_apply, Fin.sum_univ_two, star_apply, h10, mul_zero, add_zero, h00,
      one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e
    exact star_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hd0)
  have h11 : h 1 1 = star d := by
    rw [det_fin_two, h00, h01, h10, mul_zero, sub_zero] at hdet
    have : d * h 1 1 = d * star d := hdet.trans hd.symm
    exact mul_left_cancel₀ hd0 this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagConj2, h00, h01, h10, h11]

theorem exists_u3ToStage1_eq {x : Stage1Group} (hx : x ∈ MulAction.stabilizer Stage1Group vac) :
    ∃ A : GroupU3, u3ToStage1 A = x := by
  obtain ⟨⟨g, hg⟩, ⟨h, hh⟩⟩ := x
  rw [mem_stabilizer_vac_iff] at hx
  simp only at hx
  obtain ⟨hgU, hgdet⟩ := mem_specialUnitaryGroup_iff.mp hg
  have h30 : g (Fin.last 3) (Fin.last 3) * h 0 0 = 1 := (hx _ _).trans vac_last_zero
  have hg33 : g (Fin.last 3) (Fin.last 3) ≠ 0 := left_ne_zero_of_mul_eq_one h30
  have hh00 : h 0 0 ≠ 0 := right_ne_zero_of_mul_eq_one h30
  have hcol : ∀ i : Fin 3, g i.castSucc (Fin.last 3) = 0 := fun i =>
    (mul_eq_zero.mp ((hx _ 0).trans (vac_castSucc i 0))).resolve_right hh00
  have hh10 : h 1 0 = 0 :=
    (mul_eq_zero.mp ((hx (Fin.last 3) 1).trans vac_last_one)).resolve_left hg33
  have hgs : star g * g = 1 := mem_unitaryGroup_iff'.mp hgU
  have hrow : ∀ j : Fin 3, g (Fin.last 3) j.castSucc = 0 := by
    intro j
    have e := congrFun (congrFun hgs j.castSucc) (Fin.last 3)
    rw [mul_apply, Fin.sum_univ_castSucc] at e
    simp only [hcol, mul_zero, Finset.sum_const_zero, zero_add, star_apply,
      one_apply_ne (Fin.castSucc_lt_last j).ne] at e
    exact star_eq_zero.mp ((mul_eq_zero.mp e).resolve_right hg33)
  set c := g (Fin.last 3) (Fin.last 3) with hc
  set A : Matrix (Fin 3) (Fin 3) ℂ := g.submatrix Fin.castSucc Fin.castSucc with hA
  have hgblock : g = blockDiag4 A c := by
    ext i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [blockDiag4_cc, blockDiag4_cl, blockDiag4_lc, blockDiag4_ll, hcol, hrow, hA, hc,
        submatrix_apply]
  rw [hgblock, star_eq_conjTranspose, blockDiag4_conjTranspose, blockDiag4_mul,
    ← blockDiag4_one] at hgs
  obtain ⟨hAA, -⟩ := blockDiag4_inj hgs
  have hAU : A ∈ unitaryGroup (Fin 3) ℂ :=
    mem_unitaryGroup_iff'.mpr (by rw [star_eq_conjTranspose]; exact hAA)
  have hdet : A.det * c = 1 := by rw [← det_blockDiag4, ← hgblock]; exact hgdet
  have hdd : star A.det * A.det = 1 := Unitary.star_mul_self_of_mem (det_of_mem_unitary hAU)
  have hdd' : A.det * star A.det = 1 := Unitary.mul_star_self_of_mem (det_of_mem_unitary hAU)
  have hcd : c = star A.det :=
    mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hdet) (hdet.trans hdd'.symm)
  have hh00' : h 0 0 = A.det := by
    rw [hcd] at h30
    exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hdd) (h30.trans hdd.symm)
  have hhdg : h = diagConj2 A.det := eq_diagConj2_of hh hdd' hh00' hh10
  refine ⟨⟨A, hAU⟩, Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change blockDiag4 A (star A.det) = g
    rw [← hcd, ← hgblock]
  · change diagConj2 A.det = h
    rw [hhdg]

theorem range_u3ToStage1 : u3ToStage1.range = MulAction.stabilizer Stage1Group vac := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩; exact u3ToStage1_mem A
  · intro hx; obtain ⟨A, hA⟩ := exists_u3ToStage1_eq hx; exact ⟨A, hA⟩

/-- **The stabiliser SUBGROUP of the `(4, 1, 2)` vacuum is `U(3)`.** -/
noncomputable def stabilizerVacEquivU3 : MulAction.stabilizer Stage1Group vac ≃* GroupU3 :=
  ((MonoidHom.ofInjective u3ToStage1_injective).trans
    (MulEquiv.subgroupCongr range_u3ToStage1)).symm

theorem u3ToStage1_stabilizerVacEquivU3 (x : MulAction.stabilizer Stage1Group vac) :
    u3ToStage1 (stabilizerVacEquivU3 x) = x := by
  have := congrArg Subtype.val ((MonoidHom.ofInjective u3ToStage1_injective).trans
    (MulEquiv.subgroupCongr range_u3ToStage1) |>.apply_symm_apply x)
  exact this

theorem stabilizerVacEquivU3_apply (x : MulAction.stabilizer Stage1Group vac) :
    ((stabilizerVacEquivU3 x : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ)
      = ((x : Stage1Group).1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.castSucc Fin.castSucc := by
  rw [← u3ToStage1_stabilizerVacEquivU3 x]
  ext i j
  simp only [u3ToStage1, MonoidHom.coe_mk, OneHom.coe_mk, su4Part, submatrix_apply, blockDiag4_cc]

open ElectroweakVacuumStabiliser

theorem stage2_smul_vacEW_apply (g : Stage2Group) (i j : Fin 2) :
    (g • vacEW) i j
      = (g.1 : Matrix (Fin 2) (Fin 2) ℂ) i 0 * star ((g.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0) := by
  rw [stage2_smul_def, stage2Act, vacEW]
  simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two, star_apply]

theorem mem_stabilizer_vacEW_iff (g : Stage2Group) : g ∈ MulAction.stabilizer Stage2Group vacEW ↔
    ∀ i j, (g.1 : Matrix (Fin 2) (Fin 2) ℂ) i 0 * star ((g.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0)
      = vacEW i j := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h i j; rw [← stage2_smul_vacEW_apply, h]
  · intro h; ext i j; rw [stage2_smul_vacEW_apply, h]

theorem mem_stabilizer_pair_iff (g : FullGroup) :
    g ∈ MulAction.stabilizer FullGroup (vac, vacEW) ↔
      ((g.1, g.2.2) : Stage1Group) ∈ MulAction.stabilizer Stage1Group vac ∧
        ((g.2.1, g.2.2) : Stage2Group) ∈ MulAction.stabilizer Stage2Group vacEW := by
  simp only [MulAction.mem_stabilizer_iff, full_smul_def, fullAct, Prod.mk.injEq, stage1_smul_def,
    stage2_smul_def]

/-- `A ↦ (diag(A, det A⁻¹), diag(det A, det A⁻¹), diag(det A, det A⁻¹))`. -/
noncomputable def u3ToFull : GroupU3 →* FullGroup :=
  ((MonoidHom.fst _ _).comp u3ToStage1).prod
    (((MonoidHom.snd _ _).comp u3ToStage1).prod ((MonoidHom.snd _ _).comp u3ToStage1))

theorem u3ToFull_apply (A : GroupU3) :
    u3ToFull A = ((u3ToStage1 A).1, (u3ToStage1 A).2, (u3ToStage1 A).2) := rfl

theorem u3ToFull_injective : Function.Injective u3ToFull := by
  intro A B h
  apply u3ToStage1_injective
  rw [u3ToFull_apply, u3ToFull_apply, Prod.mk.injEq, Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.1

theorem u3ToFull_mem (A : GroupU3) : u3ToFull A ∈ MulAction.stabilizer FullGroup (vac, vacEW) := by
  rw [mem_stabilizer_pair_iff, u3ToFull_apply]
  refine ⟨u3ToStage1_mem A, ?_⟩
  rw [mem_stabilizer_vacEW_iff]
  intro i j
  simp only [u3ToStage1, MonoidHom.coe_mk, OneHom.coe_mk, su2Part]
  have hA : A.1.det * (starRingEnd ℂ) A.1.det = 1 := det_mul_star_det A
  fin_cases i <;> fin_cases j <;> simp [diagConj2, vacEW, hA]

theorem exists_u3ToFull_eq {x : FullGroup} (hx : x ∈ MulAction.stabilizer FullGroup (vac, vacEW)) :
    ∃ A : GroupU3, u3ToFull A = x := by
  rw [mem_stabilizer_pair_iff] at hx
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨A, hA⟩ := exists_u3ToStage1_eq h1
  refine ⟨A, ?_⟩
  obtain ⟨g, hL, hR⟩ := x
  rw [Prod.mk.injEq] at hA
  simp only at hA h2
  rw [mem_stabilizer_vacEW_iff] at h2
  simp only at h2
  have hRd : (hR : Matrix (Fin 2) (Fin 2) ℂ) = diagConj2 A.1.det := by rw [← hA.2]; rfl
  have hdd := star_det_mul_det A
  have hdd' := det_mul_star_det A
  have hsd : star A.1.det ≠ 0 := left_ne_zero_of_mul_eq_one hdd
  have e0 := h2 0 0
  have e1 := h2 1 0
  rw [hRd] at e0 e1
  simp only [diagConj2, diagonal_apply_eq, Matrix.cons_val_zero, vacEW, single_apply] at e0 e1
  have hL00 : (hL : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = A.1.det :=
    mul_right_cancel₀ hsd (by simpa using e0.trans hdd'.symm)
  have hL10 : (hL : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = 0 :=
    (mul_eq_zero.mp (by simpa using e1)).resolve_right hsd
  have hLd := eq_diagConj2_of hL.2 hdd' hL00 hL10
  rw [u3ToFull_apply, ← hA.1, ← hA.2]
  refine Prod.ext rfl (Prod.ext (Subtype.ext ?_) rfl)
  change diagConj2 A.1.det = (hL : Matrix (Fin 2) (Fin 2) ℂ)
  rw [hLd]

theorem range_u3ToFull : u3ToFull.range = MulAction.stabilizer FullGroup (vac, vacEW) := by
  ext x
  constructor
  · rintro ⟨A, rfl⟩; exact u3ToFull_mem A
  · intro hx; obtain ⟨A, hA⟩ := exists_u3ToFull_eq hx; exact ⟨A, hA⟩

/-- **The unbroken GROUP of both stages is `U(3)`.** -/
noncomputable def stabilizerPairEquivU3 : MulAction.stabilizer FullGroup (vac, vacEW) ≃* GroupU3 :=
  ((MonoidHom.ofInjective u3ToFull_injective).trans (MulEquiv.subgroupCongr range_u3ToFull)).symm

theorem u3ToFull_stabilizerPairEquivU3 (x : MulAction.stabilizer FullGroup (vac, vacEW)) :
    u3ToFull (stabilizerPairEquivU3 x) = x := by
  have := congrArg Subtype.val ((MonoidHom.ofInjective u3ToFull_injective).trans
    (MulEquiv.subgroupCongr range_u3ToFull) |>.apply_symm_apply x)
  exact this

theorem stabilizerPairEquivU3_apply (x : MulAction.stabilizer FullGroup (vac, vacEW)) :
    ((stabilizerPairEquivU3 x : GroupU3) : Matrix (Fin 3) (Fin 3) ℂ)
      = ((x : FullGroup).1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.castSucc Fin.castSucc := by
  rw [← u3ToFull_stabilizerPairEquivU3 x]
  ext i j
  simp only [u3ToFull_apply, u3ToStage1, MonoidHom.coe_mk, OneHom.coe_mk, su4Part, submatrix_apply,
    blockDiag4_cc]

end PatiSalamStabiliserGroup
