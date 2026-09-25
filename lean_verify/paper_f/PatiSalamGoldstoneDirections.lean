/-
  PatiSalamGoldstoneDirections: what is unbroken and what is broken, both as SPACES — the joint
  stabiliser is `su(3) ⊕ u(1)` as a direct sum with the charge on the centre line, and the broken
  directions are exactly the tangent directions of the vacuum orbit

  Campaign 3 hardening unit 184 (20 September 2026). Spine link L15 (Higgs sector).

  WHY. Unit 183 left two readings unproved: that the joint stabiliser's `u(3)` is
  `su(3)_colour ⊕ u(1)_Q`, and what *broken* means beyond *not in the stabiliser*. L15's row
  still says *no Goldstone theorem*. This file proves the two readings as linear algebra and
  says where Goldstone's theorem ends and dynamics begins.

  WHAT IS PROVED.
  (1) `brokenEquivTangent : (Full ⧸ jointStab) ≃ₗ[ℝ] range jointOrbit` — **the broken directions
      ARE the tangent directions of the vacuum orbit**, by the first isomorphism theorem applied
      to the joint orbit map (`LinearMap.quotKerEquivRange`; `jointStab` is that map's kernel
      by definition). `finrank_range_jointOrbit = 12`; the same at each stage alone:
      `stage1EquivTangent` (nine, unit 178's `orbitMap`) and `stage2EquivTangent` (three, unit
      182's `orbitEW`). `finrank_scalars = 24` (the two Higgs fields, `16 + 8` real dimensions)
      and `finrank_transverse = 12`: twelve directions along the orbit, twelve transverse to it.
  (2) `isCompl_traceless_centreLine : IsCompl (traceless 3) centreLine` in `u(3)` —
      **`u(3) = su(3) ⊕ u(1)` as an internal direct sum**, `centreLine := span {i · 1₃}`;
      disjoint because the imaginary trace of `t • i1₃` is `3t`, complementary by the count
      `8 + 1 = 9` (`Submodule.eq_top_of_disjoint`).
  (3) `jointStabEquivU3_qFull`: under unit 183's `jointStabEquivU3`, the charge direction
      `6i · Q` goes to `i · 1₃` — **the charge IS the centre `u(1)`**; and `ofU3Full_snd_eq_zero`:
      a traceless block gives zero in both `su(2)` slots — **the `su(3)` IS colour**, sitting in
      the `su(4)` factor alone. So the unbroken algebra is `su(3)_colour ⊕ u(1)_Q` with both
      summands identified, not merely `9 = 8 + 1`.

  NOT PROVED, said exactly.
  • GOLDSTONE'S THEOREM proper is not here and cannot be: it says the modes along the orbit are
    MASSLESS, which needs a Lagrangian, a potential ON THE HIGGS FIELDS and a mass matrix.
    Checked by name before writing (`ERRATUM 76`): no declaration's name contains `lagrangian`
    or `massmatrix`; the six whose names contain `potential` are `BakryEmeryGap`'s
    `QuadraticPotential` (`V(x) = a‖x‖²` on `Herm₄`, the spectral action's Gaussian weight — a
    potential on the Dirac slice, not on `(4, 1, 2) ⊕ (1, 2, 2)`), its `cascade_quadratic_potential`
    and `F3_9g`'s gap theorem from it, and `F3_9g`'s confining and linear Schrödinger potentials;
    `F3_2_HiggsForced.higgs_mechanism_forced` and `prediction_heavy_higgs` are conjunctions of
    `finrank` counts and numerals (`2 = 2`). What (1) proves is the part of Goldstone's argument
    that is linear algebra: the
    broken generators and the orbit's tangent directions are one space. Whether those twelve
    directions are eaten by twelve gauge bosons is physics the estate does not state; the
    three `goldstone`-named declarations remain numerals (unit 179's header names them).
    ⚠ 25 September 2026 (hardening unit 191, `paper_f/PatiSalamGaugeAction.lean`): when (1) was
    written the vacuum ORBIT was not an object — no group acted on the Higgs fields, and
    `range jointOrbit` is the image of the Lie-algebra action at the vacuum, which (1) names by its
    Lie-theoretic reading. The orbit now exists: `SU(4) × SU(2)_L × SU(2)_R` acts on the pair
    (`instMulActionFull`), and `mem_range_jointOrbit_iff` proves `range jointOrbit` is exactly the
    set of velocities at `t = 0` of the curves `t ↦ expFull (t • p) • (vac, vacEW)` in that orbit.
    No manifold structure on the orbit is claimed. The bullet is kept as written (`ERRATUM 94`).
  • *Transverse to the orbit* (twelve directions) is not *physical Higgs*: without a potential
    there is no radial direction to single out, and `F3_2_HiggsForced.physical_higgs_count`'s
    `8 − 6 = 2` counts differently (the `(1, 2, 2)` alone, six Goldstones subtracted); the two
    numbers are not compared here.
  • Both vacuum directions are still conventions; `su(3) ⊕ u(1)` is a direct sum of real
    vector spaces, not of Lie algebras (unit 180's bracket is not carried across).

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `ofU3Full_snd_eq_zero` takes
  `C ∈ traceless 3`; every other declaration is hypothesis-free.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 17 names run against `paper_f` with
  `newnames_scan`'s regex before this header was written — none taken). `iOne3` is
  `TracelessSkewDimension.iOne_mem 3`'s matrix as an element of the subtype; that file proves the
  membership and the dimension count `finrank_traceless_add_one_eq_skewAdjoint` but states no
  complement — the direct sum is new. The first isomorphism theorem is Mathlib's; the content is
  the identification of both sides with unit 183's objects.
-/

import PatiSalamTwoStageStabiliser

open Matrix TracelessSkewDimension PatiSalamRightSector PatiSalamVacuumStabiliser
  PatiSalamStabiliserDimension ElectroweakVacuumStabiliser PatiSalamTwoStageStabiliser
  PatiSalamOffDiagonal

namespace PatiSalamGoldstoneDirections

noncomputable section

/-- **THE BROKEN DIRECTIONS ARE THE TANGENT DIRECTIONS OF THE VACUUM ORBIT**: the quotient by the
joint stabiliser is the range of the joint orbit map, as real vector spaces. -/
def brokenEquivTangent : (Full ⧸ jointStab) ≃ₗ[ℝ] LinearMap.range jointOrbit :=
  LinearMap.quotKerEquivRange jointOrbit

theorem finrank_range_jointOrbit : Module.finrank ℝ (LinearMap.range jointOrbit) = 12 := by
  rw [← brokenEquivTangent.finrank_eq, finrank_jointBroken]

/-- Stage 1 alone. -/
def stage1EquivTangent : (PSLie ⧸ stab) ≃ₗ[ℝ] LinearMap.range orbitMap :=
  LinearMap.quotKerEquivRange orbitMap

theorem finrank_range_orbitMap : Module.finrank ℝ (LinearMap.range orbitMap) = 9 := by
  rw [← stage1EquivTangent.finrank_eq, finrank_broken]

/-- Stage 2 alone. -/
def stage2EquivTangent : (EWLie ⧸ stabEW) ≃ₗ[ℝ] LinearMap.range orbitEW :=
  LinearMap.quotKerEquivRange orbitEW

theorem finrank_range_orbitEW : Module.finrank ℝ (LinearMap.range orbitEW) = 3 := by
  rw [← stage2EquivTangent.finrank_eq, finrank_brokenEW]

/-- The two Higgs fields together: `16 + 8 = 24` real dimensions. -/
theorem finrank_scalars : Module.finrank ℝ (Bidoublet × Matrix (Fin 2) (Fin 2) ℂ) = 24 := by
  rw [Module.finrank_prod]
  change Module.finrank ℝ (Fin 4 → Fin 2 → ℂ) + Module.finrank ℝ (Fin 2 → Fin 2 → ℂ) = 24
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]

/-- **THE DIRECTIONS TRANSVERSE TO THE ORBIT**: twelve of the twenty-four. -/
theorem finrank_transverse :
    Module.finrank ℝ ((Bidoublet × Matrix (Fin 2) (Fin 2) ℂ) ⧸ LinearMap.range jointOrbit)
      = 12 := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range jointOrbit)
  rw [finrank_range_jointOrbit, finrank_scalars] at h
  omega

/-! ## 2. What is unbroken, as a direct sum: colour `su(3)` and the charge `u(1)` -/

/-- `i · 1₃`, the generator of the centre of `u(3)`. -/
def iOne3 : U3 := ⟨Complex.I • (1 : Matrix (Fin 3) (Fin 3) ℂ), iOne_mem 3⟩

/-- The centre line `u(1) = ℝ • i1₃` inside `u(3)`. -/
def centreLine : Submodule ℝ U3 := Submodule.span ℝ {iOne3}

theorem iOne3_ne_zero : iOne3 ≠ 0 := by
  intro h
  have h1 := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  simp [iOne3] at h1

theorem finrank_centreLine : Module.finrank ℝ centreLine = 1 := finrank_span_singleton iOne3_ne_zero

theorem traceIm_iOne3 : traceIm 3 iOne3 = 3 := by
  change (Matrix.trace (Complex.I • (1 : Matrix (Fin 3) (Fin 3) ℂ))).im = 3
  simp [Matrix.trace_smul, Matrix.trace_one]

theorem disjoint_traceless_centreLine : Disjoint (traceless 3) centreLine := by
  rw [Submodule.disjoint_def]
  intro x hx hc
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hc
  have h : traceIm 3 (t • iOne3) = 0 := hx
  rw [map_smul, traceIm_iOne3, smul_eq_mul] at h
  have ht : t = 0 := by linarith [h]
  rw [ht, zero_smul]

/-- **`u(3) = su(3) ⊕ u(1)`** as an internal direct sum: the traceless part and the centre line
are complementary. -/
theorem isCompl_traceless_centreLine : IsCompl (traceless 3) centreLine := by
  refine ⟨disjoint_traceless_centreLine, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_disjoint _ _ ?_ disjoint_traceless_centreLine
  rw [finrank_traceless_three, finrank_centreLine, finrank_U3]

/-- **THE CHARGE DIRECTION IS THE CENTRE OF `u(3)`**: under `jointStabEquivU3`, `6i · Q` goes to
`i · 1₃`. -/
theorem jointStabEquivU3_qFull :
    jointStabEquivU3 ⟨qFull, qFull_mem_jointStab⟩ = iOne3 := by
  apply Subtype.ext
  change topBlock blGen = Complex.I • (1 : Matrix (Fin 3) (Fin 3) ℂ)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [topBlock_apply, fin3_to_fin4, blGen]

/-- **THE COLOUR `su(3)` SITS IN THE `su(4)` FACTOR ALONE**: a traceless block gives zero in both
`su(2)` slots. -/
theorem ofU3Full_snd_eq_zero (C : U3) (hC : C ∈ traceless 3) : (ofU3Full C).2 = 0 := by
  have htr : Matrix.trace (C : Matrix (Fin 3) (Fin 3) ℂ) = 0 := trace_eq_zero_of_mem_traceless hC
  have hd : diagB C = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagB, htr]
  rw [ofU3Full_apply]
  refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext (Subtype.ext ?_)) <;> exact hd

end

end PatiSalamGoldstoneDirections
