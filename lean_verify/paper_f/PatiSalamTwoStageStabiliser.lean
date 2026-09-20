/-
  PatiSalamTwoStageStabiliser: both vacua at once — the joint stabiliser inside
  `su(4) ⊕ su(2)_L ⊕ su(2)_R` is `u(3)`, the charge direction fixes both, twelve directions are
  broken over the two stages, and `12 = 9 + 3` is a short exact sequence

  Campaign 3 hardening unit 183 (20 September 2026). Spine link L15 (Higgs sector).

  WHY. Units 178–180 did the Pati–Salam stage on `su(4) ⊕ su(2)_R` (vacuum `E₃₀`, stabiliser
  `u(3)`, nine broken); unit 182 did the electroweak stage on what stage 1 leaves,
  `su(2)_L ⊕ u(1)_{T₃R}` (vacuum `E₀₀`, stabiliser the charge line, three broken). Unit 182's
  header says the two are *not yet COMPOSED*. This file composes them in the only way that needs
  no choice: put both vacua in front of the FULL algebra `su(4) ⊕ su(2)_L ⊕ su(2)_R` and take
  the joint stabiliser — the directions fixing both vectors at once.

  WHAT IS PROVED.
  (1) `Full := traceless 4 × traceless 2 × traceless 2`, written `(A, (L, R))`; `stage1` is the
      projection to `(A, R)`; `orbitEWFull (L, R) = actEW L R vacEW` is unit 182's action on the
      whole of `su(2)_L ⊕ su(2)_R`; `jointOrbit p = (act A R vac, actEW L R vacEW)` and
      `jointStab := ker jointOrbit`. `mem_jointStab_iff`: `p ∈ jointStab` iff its stage-1
      projection is in unit 178's `stab` and `(L, R)` fixes `E₀₀`.
  (2) `jointStabEquivU3 : jointStab ≃ₗ[ℝ] skewAdjoint (Matrix (Fin 3) (Fin 3) ℂ)` — **the joint
      stabiliser is `u(3)`**: `C ↦ (blockdiag(C, −tr C), (diag(tr C, −tr C), diag(tr C, −tr C)))`
      (`ofU3Full`, built from unit 179's `ofU3` with `L = R`), inverse the top-left block of `A`
      (`toU3Full`). The reconstruction `ofU3Full_toU3Full` is unit 179's `ofU3_toU3` for `(A, R)`
      plus one new fact: `L` is diagonal with `L 0 0 = R 0 0`, so `L = R`. `finrank_jointStab = 9`,
      `finrank_Full = 21`, **`finrank_jointBroken : finrank ℝ (Full ⧸ jointStab) = 12`**.
  (3) `qFull := (blT, (3 • t3RT, 3 • t3RT))` — `6i · Q` for `Q = T₃L + T₃R + (B − L)/2` — fixes
      both vacua (`qFull_mem_jointStab`). Together with (2): the joint stabiliser is `u(3)` and the
      charge direction lies in it; the reading `u(3) = su(3)_colour ⊕ u(1)_Q` is the block
      decomposition of `u(3)`, not a separate theorem here.
  (4) The two stages as a short exact sequence `0 → 3 → 12 → 9 → 0`: `stage1Lift :
      Full ⧸ jointStab →ₗ[ℝ] PSLie ⧸ stab` (the projection descended; well defined because a joint
      stabiliser element's stage-1 part is in `stab`), `stage1Lift_surjective`, and
      `finrank_ker_stage1Lift = 3` — the kernel is the electroweak stage, three-dimensional,
      by rank–nullity on `12` and `9`.

  NOT PROVED, said exactly.
  • Both vacuum directions are conventions (`E₃₀`, `E₀₀`); the theorems are about the stabiliser
    GIVEN them. No potential, no minimisation, no mass, no Goldstone theorem; the twelve broken
    directions are twelve gauge bosons only under a theorem this estate does not have (the three
    `goldstone`-named declarations are numerals — unit 179's header names them).
  • The kernel in (4) is three-dimensional and is not identified with unit 182's
    `EWLie ⧸ stabEW` by an isomorphism; only the dimensions agree. No splitting is chosen.
    ⚠ 20 September 2026 (hardening unit 184, `paper_f/PatiSalamGoldstoneDirections.lean`), in
    part: the BROKEN space itself is now identified — `brokenEquivTangent : Full ⧸ jointStab ≃ₗ[ℝ]
    range jointOrbit`, the tangent directions of the vacuum orbit (and the same at each stage).
    The kernel of (4) is still not matched to unit 182's quotient by an isomorphism.
  • `u(3)` is reached as a real vector space, as in unit 179; the Lie structure of the joint
    stabiliser would be unit 180's argument repeated on `Full`, and is not repeated.
  • The `su(3)_colour ⊕ u(1)_Q` reading of `u(3)` is not stated as a direct sum in Lean.
    ⚠ DONE, 20 September 2026 (hardening unit 184): `isCompl_traceless_centreLine` (`u(3) =
    su(3) ⊕ u(1)` as an internal direct sum), `jointStabEquivU3_qFull` (the charge is the centre
    `i · 1₃`) and `ofU3Full_snd_eq_zero` (the `su(3)` is colour, in the `su(4)` factor alone).
    The bullet is kept as written (`ERRATUM 94`).
  • No `LieRing` on `Full`; the two bracket laws (`act_bracket`, `actEW_bracket`) are matrix
    identities in the files this one imports.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `ofU3Full_toU3Full` takes `p ∈ jointStab`;
  every other theorem is hypothesis-free. Nothing takes positivity, hermiticity or a norm.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 26 names run against `paper_f`
  with `newnames_scan`'s regex before this header was written — none taken). The prototype carried
  local copies of unit 182's `actEW`, `vacEW` and `actEW_vac_eq_zero_iff` while that file was not
  yet in the estate; they were deleted for the import before this header was written, and the
  three names are unit 182's. `stage1` composes Mathlib's `LinearMap.fst`/`snd`; `Full` is the
  first three-factor product in the Higgs-sector files (`PSLie`, `RightSector`, `EWLie` are pairs).
  This file imports `PatiSalamStabiliserDimension` and `ElectroweakVacuumStabiliser`, and not
  `PatiSalamStabiliserLie`, for the reason unit 182's header records (the Lie-product import makes
  the product's `smul` time out in typeclass search).
-/

import PatiSalamStabiliserDimension
import ElectroweakVacuumStabiliser

open Matrix TracelessSkewDimension PatiSalamRightSector PatiSalamVacuumStabiliser
  PatiSalamStabiliserDimension PatiSalamOffDiagonal ElectroweakVacuumStabiliser

namespace PatiSalamTwoStageStabiliser

noncomputable section

/-- `su(4) ⊕ su(2)_L ⊕ su(2)_R`, as `(A, (L, R))`. -/
abbrev Full := traceless 4 × traceless 2 × traceless 2

/-- The stage-1 projection `(A, (L, R)) ↦ (A, R)`. -/
def stage1 : Full →ₗ[ℝ] PSLie :=
  LinearMap.prod (LinearMap.fst ℝ (traceless 4) (traceless 2 × traceless 2))
    ((LinearMap.snd ℝ (traceless 2) (traceless 2)).comp
      (LinearMap.snd ℝ (traceless 4) (traceless 2 × traceless 2)))

theorem stage1_apply (p : Full) : stage1 p = (p.1, p.2.2) := rfl

/-- The electroweak orbit map on the full `su(2)_L ⊕ su(2)_R`. -/
def orbitEWFull : traceless 2 × traceless 2 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun q := actEW (mat2 q.1) (mat2 q.2) vacEW
  map_add' q q' := by
    simp only [Prod.fst_add, Prod.snd_add, mat2, Submodule.coe_add, AddSubgroup.coe_add, actEW,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' r q := by
    simp only [Prod.smul_fst, Prod.smul_snd, mat2, Submodule.coe_smul, skewAdjoint.val_smul, actEW,
      RingHom.id_apply]
    erw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- Both vacua at once. -/
def jointOrbit : Full →ₗ[ℝ] Bidoublet × Matrix (Fin 2) (Fin 2) ℂ :=
  LinearMap.prod (orbitMap.comp stage1)
    (orbitEWFull.comp (LinearMap.snd ℝ (traceless 4) (traceless 2 × traceless 2)))

/-- **THE JOINT STABILISER OF THE TWO VACUA.** -/
def jointStab : Submodule ℝ Full := LinearMap.ker jointOrbit

theorem mem_jointStab_iff (p : Full) :
    p ∈ jointStab ↔ (p.1, p.2.2) ∈ stab ∧ actEW (mat2 p.2.1) (mat2 p.2.2) vacEW = 0 := by
  rw [jointStab, LinearMap.mem_ker, jointOrbit, LinearMap.prod_apply, Prod.mk_eq_zero]
  rfl

/-- `C ∈ u(3) ↦ (blockdiag(C, −tr C), (diag(tr C, −tr C), diag(tr C, −tr C)))`. -/
def ofU3Full : U3 →ₗ[ℝ] Full :=
  LinearMap.prod (LinearMap.fst ℝ (traceless 4) (traceless 2) ∘ₗ ofU3)
    (LinearMap.prod (LinearMap.snd ℝ (traceless 4) (traceless 2) ∘ₗ ofU3)
      (LinearMap.snd ℝ (traceless 4) (traceless 2) ∘ₗ ofU3))

theorem ofU3Full_apply (C : U3) : ofU3Full C = ((ofU3 C).1, ((ofU3 C).2, (ofU3 C).2)) := rfl

theorem ofU3Full_mem_jointStab (C : U3) : ofU3Full C ∈ jointStab := by
  rw [mem_jointStab_iff, ofU3Full_apply]
  refine ⟨ofU3_mem_stab C, ?_⟩
  rw [actEW_vac_eq_zero_iff]
  change diagB C 1 0 = 0 ∧ diagB C 0 0 = diagB C 0 0 ∧ diagB C 0 1 = 0
  refine ⟨?_, rfl, ?_⟩ <;> simp [diagB]

/-- The block of the `su(4)` component, on all of `Full`. -/
def toU3Full : Full →ₗ[ℝ] U3 := toU3.comp stage1

theorem toU3Full_ofU3Full (C : U3) : toU3Full (ofU3Full C) = C := by
  change toU3 (ofU3 C) = C
  exact toU3_ofU3 C

/-- The reconstruction: a joint stabiliser element is determined by its `3 × 3` block, with
`L = R`. -/
theorem ofU3Full_toU3Full (p : Full) (hp : p ∈ jointStab) : ofU3Full (toU3Full p) = p := by
  rw [mem_jointStab_iff] at hp
  obtain ⟨h1, h2⟩ := hp
  have hAR : ofU3 (toU3 (p.1, p.2.2)) = (p.1, p.2.2) := ofU3_toU3 _ h1
  have hA : (ofU3 (toU3 (p.1, p.2.2))).1 = p.1 := congrArg Prod.fst hAR
  have hR : (ofU3 (toU3 (p.1, p.2.2))).2 = p.2.2 := congrArg Prod.snd hAR
  -- L: skew, traceless, with L 1 0 = 0 and L 0 0 = R 0 0
  rw [actEW_vac_eq_zero_iff] at h2
  obtain ⟨hL10, hL00, -⟩ := h2
  set L : Matrix (Fin 2) (Fin 2) ℂ := mat2 p.2.1 with hLdef
  have hskew : star L = -L := skewAdjoint.mem_iff.mp p.2.1.1.2
  have htr : Matrix.trace L = 0 := trace_eq_zero_of_mem_traceless p.2.1.2
  have hL01 : L 0 1 = 0 := by
    have := congrFun (congrFun hskew 0) 1
    rw [Matrix.star_apply, Matrix.neg_apply, hL10] at this
    simpa using this.symm
  have hL11 : L 1 1 = -L 0 0 := by
    have : L 0 0 + L 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using htr
    linear_combination this
  have hRmat : mat2 p.2.2 = diagB (topBlock (mat4 p.1)) := by
    have := congrArg mat2 hR
    exact this.symm
  have hL : L = diagB (topBlock (mat4 p.1)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hL00, hL01, hL10, hL11, hRmat, diagB]
  refine Prod.ext hA (Prod.ext (Subtype.ext (Subtype.ext ?_)) hR)
  exact hL.symm

/-- `ofU3Full`, landing in the joint stabiliser. -/
def ofU3Full' : U3 →ₗ[ℝ] jointStab :=
  LinearMap.codRestrict jointStab ofU3Full ofU3Full_mem_jointStab

/-- `toU3Full`, restricted to the joint stabiliser. -/
def toU3Full' : jointStab →ₗ[ℝ] U3 := toU3Full.comp jointStab.subtype

/-- **THE JOINT STABILISER IS `u(3)`** as a real vector space. -/
def jointStabEquivU3 : jointStab ≃ₗ[ℝ] U3 :=
  LinearEquiv.ofLinear toU3Full' ofU3Full' (LinearMap.ext fun C => toU3Full_ofU3Full C)
    (LinearMap.ext fun p => Subtype.ext (ofU3Full_toU3Full p.1 p.2))

theorem finrank_jointStab : Module.finrank ℝ jointStab = 9 := by
  rw [jointStabEquivU3.finrank_eq, finrank_U3]

theorem finrank_Full : Module.finrank ℝ Full = 21 := by
  rw [Module.finrank_prod, Module.finrank_prod, finrank_traceless_four, finrank_traceless_two]

/-- **TWELVE BROKEN DIRECTIONS OVER THE TWO STAGES**, as a codimension. -/
theorem finrank_jointBroken : Module.finrank ℝ (Full ⧸ jointStab) = 12 := by
  have h := Submodule.finrank_quotient_add_finrank jointStab
  rw [finrank_jointStab, finrank_Full] at h
  omega

/-- The charge direction `6i · Q`, `Q = T₃L + T₃R + (B − L)/2`, fixes both vacua. -/
def qFull : Full := (blT, ((3 : ℝ) • t3RT, (3 : ℝ) • t3RT))

theorem qFull_mem_jointStab : qFull ∈ jointStab := by
  rw [mem_jointStab_iff]
  refine ⟨yG_mem_stab, ?_⟩
  rw [actEW_vac_eq_zero_iff]
  change ((3 : ℝ) • t3RGen) 1 0 = 0 ∧ ((3 : ℝ) • t3RGen) 0 0 = ((3 : ℝ) • t3RGen) 0 0 ∧
    ((3 : ℝ) • t3RGen) 0 1 = 0
  refine ⟨?_, rfl, ?_⟩ <;> simp [t3RGen]

/-! ## The two stages as an exact sequence: `0 → 3 → 12 → 9 → 0` -/

theorem jointStab_le_ker : jointStab ≤ LinearMap.ker (stab.mkQ ∘ₗ stage1) := by
  intro p hp
  rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ((mem_jointStab_iff p).mp hp).1

/-- The broken directions of both stages map onto the stage-1 broken directions. -/
def stage1Lift : Full ⧸ jointStab →ₗ[ℝ] PSLie ⧸ stab :=
  jointStab.liftQ (stab.mkQ ∘ₗ stage1) jointStab_le_ker

theorem stage1_surjective : Function.Surjective stage1 := fun q => ⟨(q.1, (0, q.2)), rfl⟩

theorem stage1Lift_surjective : Function.Surjective stage1Lift := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H q =>
    obtain ⟨p, hp⟩ := stage1_surjective q
    exact ⟨Submodule.Quotient.mk p, by
      change stab.mkQ (stage1 p) = Submodule.Quotient.mk q
      rw [hp]; rfl⟩

/-- **THE ELECTROWEAK STAGE IS THE KERNEL, AND IT IS THREE-DIMENSIONAL.** -/
theorem finrank_ker_stage1Lift : Module.finrank ℝ (LinearMap.ker stage1Lift) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker stage1Lift
  rw [LinearMap.range_eq_top.mpr stage1Lift_surjective, finrank_top, finrank_broken,
    finrank_jointBroken] at h
  omega

end

end PatiSalamTwoStageStabiliser
