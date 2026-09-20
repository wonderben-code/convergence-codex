/-
  ElectroweakVacuumStabiliser: the second stage of the breaking — the `(1, 2, 2)` bidoublet as
  a representation, the electroweak vacuum as a vector, and the unbroken direction is EXACTLY
  the electric charge

  Campaign 3 hardening unit 182 (20 September 2026). Spine link L15 (Higgs sector).

  WHY. Units 178–180 did the Pati–Salam stage: the `(4, 1, 2)` vacuum `E₃₀`, its stabiliser
  `u(3)`, hypercharge forced, `9 = 6 + 3` as an exact sequence. Their headers say the `(1, 2, 2)`
  ELECTROWEAK step is untouched, and `F3_2_HiggsForced.goldstone_boson_count` records that step's
  three broken generators as the numeral `3 = 3` (`ERRATUM 559`'s species). This file does the
  second stage the same way as the first: a representation, a vacuum vector, a stabiliser as a
  kernel, and the count as a codimension — with the unbroken direction coming OUT of the
  computation as the charge `Q = T₃L + T₃R`.

  WHAT IS PROVED.
  (1) `actEW A B X = A X − X B` on `EWBidoublet := Matrix (Fin 2) (Fin 2) ℂ` — the `(1, 2, 2)`
      space, `su(2)_L` on the left index and `su(2)_R` on the right — and `actEW_bracket`: the
      bracket law for ALL matrices, so it is a representation of the product Lie algebra at the
      matrix level. (This is the infinitesimal form of `Φ ↦ U_L Φ U_R⁻¹`; unit 178's `act` used
      the transpose on the right, `X Bᵀ`, which for skew `B` is the CONJUGATE representation —
      equivalent for `su(2)` but not the same map, and the two files say so rather than pretend
      one convention.)
  (2) `vacEW := single 0 0 1`, the `(0, 0)` entry; `actEW_vac_eq_zero_iff`: `(A, B)` fixes it
      iff `A 1 0 = 0`, `A 0 0 = B 0 0` and `B 0 1 = 0` — three entry conditions.
  (3) The stage-2 algebra is `EWLie := traceless 2 × t3RLine`, `su(2)_L ⊕ u(1)_{T₃R}`, where
      `t3RLine := span {t3RT}` — AND THIS LINE IS DERIVED, not chosen:
      `t3RLine_eq_map_hyperchargeLine` says it is the image of unit 178's `hyperchargeLine` under
      the projection to the `su(2)_R` component. On a colour singlet the `B − L` part of `Y` acts
      trivially, so what stage 1 leaves of `su(2)_R` is exactly `T₃R`; the theorem is the linear
      algebra of that sentence (`span {3 • t3RT} = span {t3RT}`).
  (4) `orbitEW : EWLie →ₗ[ℝ] EWBidoublet`, `stabEW := ker orbitEW`, `mem_stabEW_iff`;
      `qG := (t3RT, t3RT)` — `Q = T₃L + T₃R` — and **`stabEW_eq_span : stabEW = span {qG}`**: the
      stabiliser of the electroweak vacuum is EXACTLY the charge line (`mem_stabEW_iff_mem_span`:
      the three entry conditions, skew-adjointness and the two zero traces force `A = t • t3RGen`
      and `B = t • t3RGen` for one real `t`). `finrank_stabEW = 1`, `finrank_EWLie = 4`, and
      `finrank_brokenEW : finrank ℝ (EWLie ⧸ stabEW) = 3` — the three broken directions
      (`W±`, `Z`) as a CODIMENSION, where `F3_2_HiggsForced` has a numeral.

  NOT PROVED, said exactly.
  • The vacuum direction is a convention — `E₀₀` here, `E₃₀` in unit 178; nothing derives either.
    What is not a convention is the unbroken direction GIVEN the vacuum, at both stages.
  • No potential, no minimisation, no mass, no Goldstone theorem, no `W`, `Z` or photon as
    objects: *broken* means *not in the stabiliser* and the names in (4) are the physics reading.
  • The two stages are not yet COMPOSED: the joint stabiliser of the pair of vacua inside
    `su(4) ⊕ su(2)_L ⊕ su(2)_R` — which should be `su(3) ⊕ u(1)_Q`, nine-dimensional, so that
    `21 − 9 = 12 = 9 + 3` — is the next unit, not this one. Here stage 2 is done on the algebra
    stage 1 leaves, with the `u(3)` colour part set aside because it acts trivially on `(1, 2, 2)`.
    ⚠ DONE, 20 September 2026 (hardening unit 183, `paper_f/PatiSalamTwoStageStabiliser.lean`):
    `jointStabEquivU3` (the joint stabiliser of both vacua in `Full` is `u(3)`),
    `qFull_mem_jointStab` (`6i · Q` fixes both), `finrank_jointBroken = 12`, and the exact sequence
    `0 → 3 → Full ⧸ jointStab → PSLie ⧸ stab → 0` (`stage1Lift_surjective`,
    `finrank_ker_stage1Lift = 3`). The bullet is kept as written (`ERRATUM 94`).
  • `EWLie` is a product of `ℝ`-subspaces with no `LieRing` instance, as in unit 178; the
    bracket law (1) is a matrix identity.
  • This file does NOT import `PatiSalamStabiliserLie`: with `Mathlib.Algebra.Lie.Prod` in the
    import closure, elaborating `r • p` for `p : traceless 2 × t3RLine` times out in typeclass
    search (measured: three `example`s, all `(deterministic) timeout at elaborator` at the
    statement; the same three elaborate at once without that import). Recorded so the next
    Higgs-sector file does not spend an hour on it; not understood beyond the measurement.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `actEW_bracket`, `actEW_vac_apply` and
  `actEW_vac_eq_zero_iff` take arbitrary complex matrices; `mem_stabEW_iff_mem_span` and
  `stabEW_eq_span` are unconditional; no theorem takes positivity, hermiticity or a norm.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 22 names run against `paper_f` with
  `newnames_scan`'s regex before this header was written — none taken). `actEW` is unit 178's
  `act` with `− X B` in place of `+ X Bᵀ` and at size `2 × 2`, deliberately a separate definition
  (different convention, different type; the header says which). `Su2ModuleSixteen` builds the
  `su(2)_L ⊕ su(2)_R` action on the 16 fermions over `ℚ`; `HiggsBridge` works on the Yukawa
  matrix and the coupling window; neither has the bidoublet as a representation.
  `F3_2_HiggsForced.goldstone_boson_count` and `physical_higgs_count` are the numerals this
  file's `finrank_brokenEW` replaces at the Lie-algebra level; they are cited, not deleted.
-/

import PatiSalamStabiliserDimension

open Matrix TracelessSkewDimension PatiSalamRightSector PatiSalamVacuumStabiliser

namespace ElectroweakVacuumStabiliser

noncomputable section

/-- The `(1, 2, 2)` space: `2 × 2` complex matrices, `su(2)_L` index by `su(2)_R` index. -/
abbrev EWBidoublet := Matrix (Fin 2) (Fin 2) ℂ

/-- `Φ ↦ A Φ − Φ B`, the infinitesimal form of `Φ ↦ U_L Φ U_R⁻¹`. -/
def actEW (A B X : Matrix (Fin 2) (Fin 2) ℂ) : EWBidoublet := A * X - X * B

theorem actEW_bracket (A₁ A₂ B₁ B₂ X : Matrix (Fin 2) (Fin 2) ℂ) :
    actEW ⁅A₁, A₂⁆ ⁅B₁, B₂⁆ X =
      actEW A₁ B₁ (actEW A₂ B₂ X) - actEW A₂ B₂ (actEW A₁ B₁ X) := by
  simp only [actEW, Ring.lie_def, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- The electroweak vacuum direction: the `(0, 0)` entry. -/
def vacEW : EWBidoublet := Matrix.single 0 0 1

theorem actEW_vac_apply (A B : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    actEW A B vacEW i j =
      (if (0 : Fin 2) = j then A i 0 else 0) - (if (0 : Fin 2) = i then B 0 j else 0) := by
  simp [actEW, vacEW, Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two]

theorem actEW_vac_eq_zero_iff (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    actEW A B vacEW = 0 ↔ A 1 0 = 0 ∧ A 0 0 = B 0 0 ∧ B 0 1 = 0 := by
  constructor
  · intro h
    have e : ∀ i j, actEW A B vacEW i j = 0 := fun i j => by rw [h]; rfl
    have h10 := e 1 0
    have h00 := e 0 0
    have h01 := e 0 1
    rw [actEW_vac_apply] at h10 h00 h01
    have h10' : A 1 0 = 0 := by simpa using h10
    have h00' : A 0 0 - B 0 0 = 0 := by simpa using h00
    have h01' : B 0 1 = 0 := by simpa using h01
    exact ⟨h10', sub_eq_zero.mp h00', h01'⟩
  · rintro ⟨h1, h2, h3⟩
    ext i j
    rw [actEW_vac_apply, Matrix.zero_apply]
    fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]

/-- What survives of `su(2)_R` on a colour singlet after stage 1: the `T₃R` line. -/
def t3RLine : Submodule ℝ (traceless 2) := Submodule.span ℝ {t3RT}

/-- **THE `T₃R` LINE IS WHAT STAGE 1 LEAVES OF `su(2)_R` ON A COLOUR SINGLET**: the image of the
hypercharge line under the projection to the `su(2)_R` component, as a theorem. -/
theorem t3RLine_eq_map_hyperchargeLine :
    t3RLine = hyperchargeLine.map (LinearMap.snd ℝ blLine (traceless 2)) := by
  rw [hyperchargeLine, Submodule.map_span, Set.image_singleton]
  change Submodule.span ℝ {t3RT} = Submodule.span ℝ {(3 : ℝ) • t3RT}
  rw [Submodule.span_singleton_smul_eq (by norm_num : IsUnit (3 : ℝ))]

/-- The stage-2 algebra, `su(2)_L ⊕ u(1)_{T₃R}`. -/
abbrev EWLie := traceless 2 × t3RLine

/-- The orbit map `g ↦ g · vacEW`, `ℝ`-linear. -/
def orbitEW : EWLie →ₗ[ℝ] EWBidoublet where
  toFun p := actEW (mat2 p.1) (mat2 (p.2 : traceless 2)) vacEW
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, mat2, Submodule.coe_add, AddSubgroup.coe_add, actEW,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, mat2, Submodule.coe_smul, skewAdjoint.val_smul,
      actEW, RingHom.id_apply]
    erw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- **THE STABILISER OF THE ELECTROWEAK VACUUM**, as a kernel. -/
def stabEW : Submodule ℝ EWLie := LinearMap.ker orbitEW

theorem mem_stabEW_iff (p : EWLie) :
    p ∈ stabEW ↔ mat2 p.1 1 0 = 0 ∧ mat2 p.1 0 0 = mat2 (p.2 : traceless 2) 0 0 ∧
      mat2 (p.2 : traceless 2) 0 1 = 0 := by
  rw [stabEW, LinearMap.mem_ker]
  exact actEW_vac_eq_zero_iff _ _

/-- The charge generator `Q = T₃L + T₃R`, as `(t3RT, t3RT)`. -/
def qG : EWLie := (t3RT, ⟨t3RT, Submodule.mem_span_singleton_self t3RT⟩)

theorem mat2_qG_fst : mat2 qG.1 = t3RGen := rfl

theorem mat2_qG_snd : mat2 (qG.2 : traceless 2) = t3RGen := rfl

theorem qG_mem_stabEW : qG ∈ stabEW := by
  rw [mem_stabEW_iff, mat2_qG_fst, mat2_qG_snd]
  refine ⟨?_, rfl, ?_⟩ <;> simp [t3RGen]

/-- **THE STABILISER IS EXACTLY THE CHARGE LINE.** -/
theorem mem_stabEW_iff_mem_span (p : EWLie) : p ∈ stabEW ↔ p ∈ Submodule.span ℝ {qG} := by
  constructor
  · intro h
    rw [mem_stabEW_iff] at h
    obtain ⟨h10, h00, h01⟩ := h
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp p.2.2
    have hB : mat2 (p.2 : traceless 2) = t • t3RGen := by
      change mat2 (p.2 : traceless 2) = t • t3RGen
      rw [← ht]; rfl
    set A : Matrix (Fin 2) (Fin 2) ℂ := mat2 p.1 with hA
    have hskew : star A = -A := skewAdjoint.mem_iff.mp p.1.1.2
    have htr : Matrix.trace A = 0 := trace_eq_zero_of_mem_traceless p.1.2
    have hA01 : A 0 1 = 0 := by
      have := congrFun (congrFun hskew 0) 1
      rw [Matrix.star_apply, Matrix.neg_apply, h10] at this
      simpa using this.symm
    have hA00 : A 0 0 = t * Complex.I := by
      rw [h00, hB]; simp [t3RGen]
    have hA11 : A 1 1 = -(t * Complex.I) := by
      have : A 0 0 + A 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using htr
      linear_combination this - hA00
    refine Submodule.mem_span_singleton.mpr ⟨t, ?_⟩
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) (Subtype.ext ?_)
    · change t • t3RGen = A
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hA00, hA01, h10, hA11, t3RGen]
    · exact ht
  · intro h
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp h
    exact stabEW.smul_mem t qG_mem_stabEW

theorem stabEW_eq_span : stabEW = Submodule.span ℝ {qG} := by
  ext p
  exact mem_stabEW_iff_mem_span p

theorem qG_ne_zero : qG ≠ 0 := fun h => t3RT_ne_zero (congrArg Prod.fst h)

theorem finrank_stabEW : Module.finrank ℝ stabEW = 1 := by
  rw [stabEW_eq_span]; exact finrank_span_singleton qG_ne_zero

theorem finrank_t3RLine : Module.finrank ℝ t3RLine = 1 := finrank_span_singleton t3RT_ne_zero

theorem finrank_EWLie : Module.finrank ℝ EWLie = 4 := by
  rw [Module.finrank_prod, finrank_traceless_two, finrank_t3RLine]

/-- **THREE BROKEN DIRECTIONS**, as a codimension: `W±` and `Z`, at the Lie-algebra level. -/
theorem finrank_brokenEW : Module.finrank ℝ (EWLie ⧸ stabEW) = 3 := by
  have h := Submodule.finrank_quotient_add_finrank stabEW
  rw [finrank_stabEW, finrank_EWLie] at h
  omega

end

end ElectroweakVacuumStabiliser
