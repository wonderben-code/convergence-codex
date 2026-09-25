/-
  PatiSalamJointCount: both vacua at once, at every second-stage vacuum — with the estate's
  first-stage `vac`, a nonzero bidoublet vacuum `Φ` leaves the joint group `U(3)`, as a topological
  group, when the columns of `Φ` are orthogonal, `(Φᴴ Φ) 0 1 = 0`, and otherwise a joint unbroken
  subalgebra of dimension eight; `Φ = 0` leaves twelve generators

  Campaign 3 hardening unit 221 (25 September 2026). Spine link L15 (Higgs sector).

  WHY. Unit 183 counted the joint unbroken subalgebra at the estate's pair `(vac, vacEW)`: nine,
  `u(3)` (`PatiSalamTwoStageStabiliser.finrank_jointStab`). Unit 205 showed the joint GROUP is the
  same `U(3)` at every nonzero `diag(κ, κ')`, and since unit 207 `SPINE` L15 has carried *which
  second-stage vacua leave a group merely isomorphic to `U(3)`* as open. Unit 219's NOT list: *"the
  dimension of the joint unbroken subalgebra at a general `(vac, Φ)` is not computed"*. This file
  computes that dimension at every `Φ`, and the group at every `Φ` where the dimension is nine.

  WHAT IS PROVED.
  (1) `comm_t3RGen_iff` (`diag(i, −i)` commutes with a `2 × 2` matrix exactly when its off-diagonal
      entries vanish, by unit 212's `comm_diagonal_iff`) and **`exists_mem_stabEWAt_t3RT_iff`**: at
      `Φ ≠ 0` the `su(2)_R` direction `T₃R` is the right half of an unbroken generator of the
      `(1, 2, 2)` exactly when `(Φᴴ Φ) 0 1 = 0` — one way by unit 219's `comm_of_mem_stabEWAt`, the
      other by its `custA` when `Φᴴ Φ` is scalar and a real multiple of its `ewGen Φ` otherwise.
  (2) `toStage1` (`p ↦ (p.1, p.2.2)`, `toStage1_apply`, `toStage1_mem_stab`) and
      **`toStage1_injective`**: at `Φ ≠ 0` a joint unbroken generator is determined by its
      first-stage part, by unit 219's `snd_eq_zero_imp`.
  (3) **`range_toStage1_of_orthogonal`**: with orthogonal columns every first-stage generator
      completes — the range is unit 178's `stab`; **`range_toStage1_of_not_orthogonal`**: otherwise
      the range is `stab0`, the first-stage generators with no `su(2)_R` part — because every
      first-stage generator's `su(2)_R` part lies on the `T₃R` line (unit 219's
      `snd_mem_t3RLine_of_mem_stabAt_vac`); `sndOnStab`, `range_sndOnStab` (those parts fill the
      line, by unit 178's hypercharge `yG`) and `finrank_stab0`: eight.
  (4) **`finrank_jointStabAt_vac`**: at `Φ ≠ 0` the joint unbroken subalgebra has dimension nine
      when `(Φᴴ Φ) 0 1 = 0` and eight otherwise; `jointStabAtZeroEquiv` and
      **`finrank_jointStabAt_vac_zero`**: at `Φ = 0`, twelve (`stab` times all of `su(2)_L`).
  (5) The rotation. `colNormSq a c = |a|² + |c|²` (`colNormSq_pos`, `sqrt_mul_sqrt_colNormSq`,
      `sqrt_colNormSq_ne_zero`), **`colRot a c = n^{−1/2} · [[ā, c̄], [−c, a]]`**,
      `colRotM_mul_conjTranspose` and **`colRot_mem`**: for `(a, c) ≠ 0`, `colRot a c ∈ SU(2)`.
      **`exists_mul_eq_vacKK`**: every `Φ ≠ 0` with orthogonal columns is carried by an element of
      `SU(2)` acting on the left to a nonzero `diag(κ, κ')` — `colRot` of the first column when it
      is nonzero (`smul_colRotM_mul_col0`: `diag(√n, det Φ / √n)`, the orthogonality killing the
      corner), and of `(d̄, −b̄)` from the second when the first vanishes (`smul_colRotM_mul_col1`:
      `diag(0, √n)`), each with the square root held as a variable.
  (6) `smul_pair_eq_vacKK`: `(1, U, 1)` moves `(vac, Φ)` to `(vac, U Φ)` — `SU(2)_L` does not act on
      the first field. So **`nonempty_stabilizer_pair_equiv_U3_of_orthogonal`** (unit 205's
      `nonempty_stabilizer_vacKK_equiv_U3` and Mathlib's `MulAction.stabilizerEquivStabilizer`) and
      **`nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal`** (unit 206's
      `nonempty_stabilizer_vacKK_continuousEquiv_U3` and unit 209's `stabilizerContinuousEquiv`): at
      every `Φ ≠ 0` with orthogonal columns the joint unbroken group is `U(3)`, as a topological
      group. The isomorphisms are units 205's and 206's, carried; what is new is the rotation.
  (7) **`joint_dichotomy`**: with `vac`, a nonzero `Φ` leaves `U(3)` when its columns are
      orthogonal, and otherwise a joint unbroken subalgebra of dimension eight.

  NOT PROVED, said exactly.
  • That a `Φ` with non-orthogonal columns leaves a group not isomorphic to `U(3)`. Its joint Lie
    algebra has dimension eight, and a dimension is not an invariant of abstract groups; no
    topological or smooth invariant is computed here.
  • By unit 217's `mem_matLieFull_stabilizer_iff` the counts in (4) are the joint groups' Lie
    algebras in the sense matrix groups use; no statement here joins the two files.
  • Other first-stage vacua: only the estate's `vac`.
  • Which vacuum, masses, and what an eight-generator vacuum would mean physically: nothing here.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `exists_mem_stabEWAt_t3RT_iff`,
  `toStage1_injective`, `finrank_jointStabAt_vac` and `joint_dichotomy` take `Φ ≠ 0`;
  `range_toStage1_of_orthogonal` takes `Φ ≠ 0` and `(Φᴴ Φ) 0 1 = 0`,
  `range_toStage1_of_not_orthogonal` `Φ ≠ 0` and its negation; `colNormSq_pos`,
  `sqrt_mul_sqrt_colNormSq`, `sqrt_colNormSq_ne_zero` and `colRot_mem` take `a ≠ 0 ∨ c ≠ 0`;
  `smul_colRotM_mul_col0` takes `s ≠ 0`, `s · s = ā a + c̄ c` and the orthogonality of the columns,
  entrywise; `smul_colRotM_mul_col1` takes the two zero entries, `s ≠ 0` and `s · s = d d̄ + b b̄`;
  `exists_mul_eq_vacKK` and the two `U(3)` theorems take `Φ ≠ 0` and `(Φᴴ Φ) 0 1 = 0`;
  `smul_pair_eq_vacKK` takes `U ∈ SU(2)` and `U Φ = diag(κ, κ')`. The rest take elements of their
  types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 29 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken (a draft's `nrm` and `rotL` were renamed `colNormSq` and `colRot` before the
  check). The nearest statements: unit 183's `finrank_jointStab` (nine at `(vac, vacEW)`), which (4)
  extends to every `Φ`; unit 205's `stabilizer_vacKK_eq` and `nonempty_stabilizer_vacKK_equiv_U3`
  and unit 206's `nonempty_stabilizer_vacKK_continuousEquiv_U3`, which (6) carries; unit 209's
  `stabilizerContinuousEquiv`, used, and its `nonempty_stabilizer_pair_continuousEquiv_U3_of_conj`
  (the gauge transforms of neutral-plane pairs), of which (5) exhibits the orthogonal-column pairs
  `(vac, Φ)` as instances; unit 207's `stabilizer_conj_iff`; unit 217's `jointStabAt` and
  `mem_jointStabAt_iff`, used; unit 219's `comm_of_mem_stabEWAt`, `custA`, `custA_mem`, `ewGen`,
  `ewGen_mem`, `snd_eq_zero_imp`, `stabEWAt_zero` and `snd_mem_t3RLine_of_mem_stabAt_vac`, used;
  unit 212's `comm_diagonal_iff`, unit 179's `finrank_stab`, unit 178's `yG_mem_stab`, unit 182's
  `finrank_t3RLine` and unit 213's `tlPart` and `real_smul_eq_complex_smul`, used. The pinned
  Mathlib supplies `Real.sqrt`, `Real.mul_self_sqrt`, `Real.sqrt_pos`, `Matrix.det_fin_two_of` and
  `MulAction.stabilizerEquivStabilizer`, used.

  `#print axioms` on all 29 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import ElectroweakCustodial

open Matrix PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamBrokenCount
  PatiSalamRightSector PatiSalamGaugeAction PatiSalamMatrixLie PatiSalamTwoStageStabiliser
  TracelessSkewDimension PatiSalamFirstStageClassification ElectroweakCustodial
  PatiSalamStabiliserGroup PatiSalamTwoComponentVacuum

namespace PatiSalamJointCount

noncomputable section

/-- `t3RGen = diag(i, −i)` commutes with a `2 × 2` matrix exactly when its off-diagonal entries
vanish. -/
theorem comm_t3RGen_iff (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * t3RGen = t3RGen * M ↔ M 0 1 = 0 ∧ M 1 0 = 0 := by
  have hf : (![Complex.I, -Complex.I] : Fin 2 → ℂ) 0 ≠ ![Complex.I, -Complex.I] 1 := by
    intro h
    have h' : Complex.I = -Complex.I := by simpa using h
    have := congrArg Complex.im h'
    simp at this
    norm_num at this
  exact comm_diagonal_iff hf M

/-- **The right part `T₃R` completes to an unbroken generator at `Φ ≠ 0` exactly when the columns of
`Φ` are orthogonal**, `(Φᴴ Φ) 0 1 = 0`. -/
theorem exists_mem_stabEWAt_t3RT_iff {Φ : EWBidoublet} (hΦ : Φ ≠ 0) :
    (∃ b : traceless 2, (b, t3RT) ∈ stabEWAt Φ) ↔ (Φᴴ * Φ) 0 1 = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    have h := comm_of_mem_stabEWAt hb
    exact ((comm_t3RGen_iff (Φᴴ * Φ)).mp h.symm).1
  · intro h01
    by_cases hs : ∃ c : ℂ, Φᴴ * Φ = c • 1
    · obtain ⟨c, hc⟩ := hs
      have hcs : star c = c := by
        have h := star_conjTranspose_mul_self Φ
        rw [hc] at h
        simpa [star_smul] using congrFun (congrFun h 0) 0
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hΦ (by
          open scoped ComplexOrder in
          exact Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa using hc))
      exact ⟨custA hcs hc t3RT, custA_mem hc0 hcs hc t3RT⟩
    · set M := Φᴴ * Φ with hM
      have hMs : star M = M := star_conjTranspose_mul_self Φ
      have h10 : M 1 0 = 0 := by
        have := congrFun (congrFun hMs 0) 1
        rw [star_apply, h01] at this
        exact star_eq_zero.mp this
      have him0 : (M 0 0).im = 0 := by
        have := congrArg Complex.im (congrFun (congrFun hMs 0) 0)
        rw [star_apply, Complex.star_def, Complex.conj_im] at this
        linarith
      have him1 : (M 1 1).im = 0 := by
        have := congrArg Complex.im (congrFun (congrFun hMs 1) 1)
        rw [star_apply, Complex.star_def, Complex.conj_im] at this
        linarith
      set s : ℝ := ((M 0 0).re - (M 1 1).re) / 2 with hsdef
      have hs0 : s ≠ 0 := by
        intro h
        apply hs
        refine ⟨M 0 0, ?_⟩
        have e : M 1 1 = M 0 0 := Complex.ext (by linarith) (by rw [him0, him1])
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10, e]
      have hg : (ewGen Φ).2 = s • t3RT := by
        apply Subtype.ext
        apply Subtype.ext
        change Complex.I • tlPart M = s • t3RGen
        rw [real_smul_eq_complex_smul]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [tlPart, t3RGen, trace, h01, h10, hsdef, Complex.ext_iff, him0, him1] <;> ring
      refine ⟨s⁻¹ • (ewGen Φ).1, ?_⟩
      have hm := (stabEWAt Φ).smul_mem s⁻¹ (ewGen_mem Φ)
      convert hm using 1
      refine Prod.ext rfl ?_
      change t3RT = s⁻¹ • (ewGen Φ).2
      rw [hg, smul_smul, inv_mul_cancel₀ hs0, one_smul]

/-- A joint unbroken generator at `(vac, Φ)`, read on the first stage: `p ↦ (p.1, p.2.2)`. -/
def toStage1 (Φ : EWBidoublet) : jointStabAt (vac, Φ) →ₗ[ℝ] PSLie :=
  (LinearMap.prod (LinearMap.fst ℝ (traceless 4) (traceless 2 × traceless 2))
    ((LinearMap.snd ℝ (traceless 2) (traceless 2)).comp
      (LinearMap.snd ℝ (traceless 4) (traceless 2 × traceless 2)))).comp
    (jointStabAt (vac, Φ)).subtype

theorem toStage1_apply (Φ : EWBidoublet) (p : jointStabAt (vac, Φ)) :
    toStage1 Φ p = ((p : Full).1, (p : Full).2.2) := rfl

/-- **At `Φ ≠ 0` a joint unbroken generator is determined by its first-stage part**: the
`su(2)_L` part is fixed by the `su(2)_R` part (unit 219's `snd_eq_zero_imp`). -/
theorem toStage1_injective {Φ : EWBidoublet} (hΦ : Φ ≠ 0) : Function.Injective (toStage1 Φ) := by
  intro p q h
  have h' : ((p : Full).1, (p : Full).2.2) = ((q : Full).1, (q : Full).2.2) := h
  have h1 : (p : Full).1 = (q : Full).1 := (Prod.ext_iff.mp h').1
  have h3 : (p : Full).2.2 = (q : Full).2.2 := (Prod.ext_iff.mp h').2
  have hp := ((mem_jointStabAt_iff _ _).mp p.2).2
  have hq := ((mem_jointStabAt_iff _ _).mp q.2).2
  have hd : (p : Full).2 - (q : Full).2 ∈ stabEWAt Φ := Submodule.sub_mem _ hp hq
  have h2 : ((p : Full).2 - (q : Full).2).2 = 0 := by rw [Prod.snd_sub, h3, sub_self]
  have h0 := snd_eq_zero_imp hΦ hd h2
  exact Subtype.ext (Prod.ext h1 (sub_eq_zero.mp h0))

theorem toStage1_mem_stab (Φ : EWBidoublet) (p : jointStabAt (vac, Φ)) : toStage1 Φ p ∈ stab :=
  ((mem_jointStabAt_iff _ _).mp p.2).1

/-- The first-stage generators whose `su(2)_R` part vanishes. -/
def stab0 : Submodule ℝ PSLie :=
  stab ⊓ LinearMap.ker (LinearMap.snd ℝ (traceless 4) (traceless 2))

/-- **When the columns of `Φ` are orthogonal, every first-stage generator completes**: the range
is all of unit 178's `stab`. -/
theorem range_toStage1_of_orthogonal {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (h01 : (Φᴴ * Φ) 0 1 = 0) :
    LinearMap.range (toStage1 Φ) = stab := by
  obtain ⟨b0, hb0⟩ := (exists_mem_stabEWAt_t3RT_iff hΦ).mpr h01
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    exact toStage1_mem_stab Φ p
  · intro q hq
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (snd_mem_t3RLine_of_mem_stabAt_vac hq)
    have hm : (q.1, (t • b0, q.2)) ∈ jointStabAt (vac, Φ) := by
      rw [mem_jointStabAt_iff]
      refine ⟨hq, ?_⟩
      have := (stabEWAt Φ).smul_mem t hb0
      rwa [Prod.smul_mk, ht] at this
    exact ⟨⟨_, hm⟩, rfl⟩

/-- **Otherwise only the generators with no `su(2)_R` part complete.** -/
theorem range_toStage1_of_not_orthogonal {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 ≠ 0) :
    LinearMap.range (toStage1 Φ) = stab0 := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    refine ⟨toStage1_mem_stab Φ p, ?_⟩
    change (p : Full).2.2 = 0
    have hp := ((mem_jointStabAt_iff _ _).mp p.2)
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (snd_mem_t3RLine_of_mem_stabAt_vac hp.1)
    by_cases h0 : t = 0
    · rw [← ht, h0, zero_smul]
    · exfalso
      apply h01
      apply (exists_mem_stabEWAt_t3RT_iff hΦ).mp
      refine ⟨t⁻¹ • (p : Full).2.1, ?_⟩
      have := (stabEWAt Φ).smul_mem t⁻¹ hp.2
      convert this using 1
      refine Prod.ext rfl ?_
      change t3RT = t⁻¹ • (p : Full).2.2
      rw [← ht, smul_smul, inv_mul_cancel₀ h0, one_smul]
  · rintro q ⟨hq, hq2⟩
    have hq2' : q.2 = 0 := hq2
    have hm : (q.1, ((0 : traceless 2), q.2)) ∈ jointStabAt (vac, Φ) := by
      rw [mem_jointStabAt_iff, hq2']
      exact ⟨by rw [← hq2']; exact hq, Submodule.zero_mem _⟩
    exact ⟨⟨_, hm⟩, rfl⟩

/-- The `su(2)_R` part on unit 178's `stab`. -/
def sndOnStab : stab →ₗ[ℝ] traceless 2 :=
  (LinearMap.snd ℝ (traceless 4) (traceless 2)).comp stab.subtype

theorem range_sndOnStab : LinearMap.range sndOnStab = ElectroweakVacuumStabiliser.t3RLine := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    exact snd_mem_t3RLine_of_mem_stabAt_vac q.2
  · rw [ElectroweakVacuumStabiliser.t3RLine, Submodule.span_le]
    rintro _ rfl
    refine ⟨⟨(1 / 3 : ℝ) • yG, stab.smul_mem _ yG_mem_stab⟩, ?_⟩
    change (1 / 3 : ℝ) • ((3 : ℝ) • t3RT) = t3RT
    rw [smul_smul]
    norm_num

theorem finrank_stab0 : Module.finrank ℝ stab0 = 8 := by
  have hr := LinearMap.finrank_range_add_finrank_ker sndOnStab
  rw [range_sndOnStab, ElectroweakVacuumStabiliser.finrank_t3RLine,
    PatiSalamStabiliserDimension.finrank_stab] at hr
  have hk : Module.finrank ℝ (LinearMap.ker sndOnStab) = 8 := by omega
  have he : (LinearMap.ker sndOnStab).map stab.subtype = stab0 := by
    ext q
    constructor
    · rintro ⟨q', hq', rfl⟩
      exact ⟨q'.2, hq'⟩
    · rintro ⟨hq, hq2⟩
      exact ⟨⟨q, hq⟩, hq2, rfl⟩
  rw [← he, ← hk]
  exact (Submodule.equivMapOfInjective _ stab.injective_subtype _).finrank_eq.symm

/-- **THE JOINT UNBROKEN SUBALGEBRA AT `(vac, Φ)`, COUNTED**: nine when the columns of `Φ ≠ 0` are
orthogonal, eight otherwise. -/
theorem finrank_jointStabAt_vac {Φ : EWBidoublet} (hΦ : Φ ≠ 0) :
    Module.finrank ℝ (jointStabAt (vac, Φ)) = if (Φᴴ * Φ) 0 1 = 0 then 9 else 8 := by
  rw [← LinearMap.finrank_range_of_inj (toStage1_injective hΦ)]
  split_ifs with h01
  · rw [range_toStage1_of_orthogonal hΦ h01, PatiSalamStabiliserDimension.finrank_stab]
  · rw [range_toStage1_of_not_orthogonal hΦ h01, finrank_stab0]

/-- At `Φ = 0` the second stage constrains nothing: the joint unbroken subalgebra is unit 178's
`stab` times all of `su(2)_L`. -/
def jointStabAtZeroEquiv : jointStabAt (vac, (0 : EWBidoublet)) ≃ₗ[ℝ] stab × traceless 2 where
  toFun p := (⟨toStage1 0 p, toStage1_mem_stab 0 p⟩, (p : Full).2.1)
  invFun q := ⟨((q.1 : PSLie).1, (q.2, (q.1 : PSLie).2)), by
    rw [mem_jointStabAt_iff, stabEWAt_zero]
    exact ⟨q.1.2, Submodule.mem_top⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_jointStabAt_vac_zero :
    Module.finrank ℝ (jointStabAt (vac, (0 : EWBidoublet))) = 12 := by
  rw [jointStabAtZeroEquiv.finrank_eq, Module.finrank_prod,
    PatiSalamStabiliserDimension.finrank_stab, finrank_traceless_two]

/-! ## The groups: an `SU(2)_L` rotation to the neutral plane -/

/-- `n = |a|² + |c|²`. -/
def colNormSq (a c : ℂ) : ℝ := Complex.normSq a + Complex.normSq c

/-- The rotation carrying the column `(a, c)` to `(√n, 0)`: `n^{−1/2} · [[ā, c̄], [−c, a]]`. -/
def colRot (a c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (colNormSq a c) : ℂ))⁻¹ • !![star a, star c; -c, a]

theorem colNormSq_pos {a c : ℂ} (h : a ≠ 0 ∨ c ≠ 0) : 0 < colNormSq a c := by
  rcases h with h | h
  · exact add_pos_of_pos_of_nonneg (Complex.normSq_pos.mpr h) (Complex.normSq_nonneg c)
  · exact add_pos_of_nonneg_of_pos (Complex.normSq_nonneg a) (Complex.normSq_pos.mpr h)

theorem sqrt_mul_sqrt_colNormSq {a c : ℂ} (h : a ≠ 0 ∨ c ≠ 0) :
    (Real.sqrt (colNormSq a c) : ℂ) * (Real.sqrt (colNormSq a c) : ℂ) =
      star a * a + star c * c := by
  have e : (Real.sqrt (colNormSq a c) : ℂ) * (Real.sqrt (colNormSq a c) : ℂ) =
      (colNormSq a c : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (colNormSq_pos h).le
  rw [e, colNormSq]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
  rfl

theorem colRotM_mul_conjTranspose (a c : ℂ) :
    !![star a, star c; -c, a] * (!![star a, star c; -c, a])ᴴ =
      (star a * a + star c * c) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> ring

theorem colRot_mem {a c : ℂ} (h : a ≠ 0 ∨ c ≠ 0) : colRot a c ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hs := sqrt_mul_sqrt_colNormSq h
  have hs0 : (Real.sqrt (colNormSq a c) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (colNormSq_pos h)).ne'
  have hst : star ((Real.sqrt (colNormSq a c) : ℂ))⁻¹ = ((Real.sqrt (colNormSq a c) : ℂ))⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  constructor
  · rw [colRot, star_smul, hst, Matrix.smul_mul, Matrix.mul_smul, smul_smul, star_eq_conjTranspose,
      colRotM_mul_conjTranspose, smul_smul, ← hs]
    rw [show (Real.sqrt (colNormSq a c) : ℂ)⁻¹ * (Real.sqrt (colNormSq a c) : ℂ)⁻¹ *
      ((Real.sqrt (colNormSq a c) : ℂ) * (Real.sqrt (colNormSq a c) : ℂ)) = 1 by field_simp,
      one_smul]
  · rw [colRot, det_smul, det_fin_two_of]
    simp only [Fintype.card_fin]
    field_simp
    linear_combination -hs
theorem sqrt_colNormSq_ne_zero {a c : ℂ} (h : a ≠ 0 ∨ c ≠ 0) :
    (Real.sqrt (colNormSq a c) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (colNormSq_pos h)).ne'

/-- The rotation's action when the first column is nonzero, with the square root a variable `s`. -/
theorem smul_colRotM_mul_col0 (Φ : EWBidoublet) {s : ℂ} (hs0 : s ≠ 0)
    (hs : s * s = star (Φ 0 0) * Φ 0 0 + star (Φ 1 0) * Φ 1 0)
    (h01 : star (Φ 0 0) * Φ 0 1 + star (Φ 1 0) * Φ 1 1 = 0) :
    (s⁻¹ • !![star (Φ 0 0), star (Φ 1 0); -Φ 1 0, Φ 0 0]) * Φ =
      vacKK s (s⁻¹ * (Φ 0 0 * Φ 1 1 - Φ 0 1 * Φ 1 0)) := by
  rw [Complex.star_def] at hs h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vacKK, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  · linear_combination -hs
  · linear_combination h01
  · ring
  · ring

/-- … and when the first column vanishes, with `(b, d)` the second. -/
theorem smul_colRotM_mul_col1 (Φ : EWBidoublet) (h0 : Φ 0 0 = 0) (h1 : Φ 1 0 = 0) {s : ℂ}
    (hs0 : s ≠ 0) (hs : s * s = Φ 1 1 * star (Φ 1 1) + Φ 0 1 * star (Φ 0 1)) :
    (s⁻¹ • !![star (star (Φ 1 1)), star (-star (Φ 0 1)); -(-star (Φ 0 1)), star (Φ 1 1)]) * Φ =
      vacKK 0 s := by
  rw [Complex.star_def] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vacKK, Matrix.mul_apply, Fin.sum_univ_two, h0, h1] <;> field_simp
  · ring
  · linear_combination -hs

/-- **An `SU(2)_L` rotation carries every `Φ ≠ 0` with orthogonal columns to the neutral plane.** -/
theorem exists_mul_eq_vacKK {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (h01 : (Φᴴ * Φ) 0 1 = 0) :
    ∃ U ∈ specialUnitaryGroup (Fin 2) ℂ, ∃ κ κ' : ℂ, (κ ≠ 0 ∨ κ' ≠ 0) ∧ U * Φ = vacKK κ κ' := by
  have h01' : star (Φ 0 0) * Φ 0 1 + star (Φ 1 0) * Φ 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] using h01
  by_cases hc : Φ 0 0 ≠ 0 ∨ Φ 1 0 ≠ 0
  · exact ⟨colRot (Φ 0 0) (Φ 1 0), colRot_mem hc, _, _, Or.inl (sqrt_colNormSq_ne_zero hc),
      smul_colRotM_mul_col0 Φ (sqrt_colNormSq_ne_zero hc) (sqrt_mul_sqrt_colNormSq hc) h01'⟩
  · have hc' : Φ 0 0 = 0 ∧ Φ 1 0 = 0 := by
      rw [not_or, not_not, not_not] at hc
      exact hc
    have hd : star (Φ 1 1) ≠ 0 ∨ -star (Φ 0 1) ≠ 0 := by
      by_contra hn
      rw [not_or, not_not, not_not, neg_eq_zero, star_eq_zero, star_eq_zero] at hn
      apply hΦ
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hc'.1, hc'.2, hn.1, hn.2]
    have hs := sqrt_mul_sqrt_colNormSq hd
    rw [star_star, star_neg, star_star, neg_mul_neg] at hs
    exact ⟨colRot (star (Φ 1 1)) (-star (Φ 0 1)), colRot_mem hd, _, _,
      Or.inr (sqrt_colNormSq_ne_zero hd),
      smul_colRotM_mul_col1 Φ hc'.1 hc'.2 (sqrt_colNormSq_ne_zero hd) hs⟩

/-- The rotation, as an element of `SU(4) × SU(2)_L × SU(2)_R` moving `(vac, Φ)` to the neutral
plane: `(1, U, 1)` does not move `vac`. -/
theorem smul_pair_eq_vacKK {Φ : EWBidoublet} {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U ∈ specialUnitaryGroup (Fin 2) ℂ) {κ κ' : ℂ} (h : U * Φ = vacKK κ κ') :
    ((vac, vacKK κ κ') : Bidoublet × EWBidoublet) = ((1, ⟨U, hU⟩, 1) : FullGroup) • (vac, Φ) := by
  rw [full_smul_def]
  change (vac, vacKK κ κ') = (stage1Act 1 vac, stage2Act (⟨U, hU⟩, 1) Φ)
  rw [stage1Act_one, stage2Act]
  simp [h]

/-- **At every `Φ ≠ 0` with orthogonal columns the joint unbroken group is `U(3)`** — unit 205's
`U(3)` on the neutral plane, carried by the `SU(2)_L` rotation. -/
theorem nonempty_stabilizer_pair_equiv_U3_of_orthogonal {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 = 0) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* GroupU3) := by
  obtain ⟨U, hU, κ, κ', hκ, hUΦ⟩ := exists_mul_eq_vacKK hΦ h01
  obtain ⟨e⟩ := nonempty_stabilizer_vacKK_equiv_U3 hκ
  exact ⟨(MulAction.stabilizerEquivStabilizer (smul_pair_eq_vacKK hU hUΦ)).trans e⟩

/-- **… and as a topological group**, by unit 206's `U(3)` on the neutral plane and unit 209's
conjugation. -/
theorem nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h01 : (Φᴴ * Φ) 0 1 = 0) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* GroupU3) := by
  obtain ⟨U, hU, κ, κ', hκ, hUΦ⟩ := exists_mul_eq_vacKK hΦ h01
  obtain ⟨e⟩ := PatiSalamStabiliserTopology.nonempty_stabilizer_vacKK_continuousEquiv_U3 hκ
  exact ⟨(PatiSalamTopologicalCopies.stabilizerContinuousEquiv
    (smul_pair_eq_vacKK hU hUΦ)).trans e⟩

/-- **BOTH VACUA AT ONCE, AT EVERY SECOND-STAGE VACUUM**: with `vac`, a nonzero `Φ` leaves `U(3)`,
as a topological group, when its columns are orthogonal, and otherwise a joint unbroken subalgebra
of dimension eight. -/
theorem joint_dichotomy (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    ((Φᴴ * Φ) 0 1 = 0 ∧
      Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃ₜ* GroupU3)) ∨
    ((Φᴴ * Φ) 0 1 ≠ 0 ∧ Module.finrank ℝ (jointStabAt (vac, Φ)) = 8) := by
  by_cases h01 : (Φᴴ * Φ) 0 1 = 0
  · exact Or.inl ⟨h01, nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal hΦ h01⟩
  · refine Or.inr ⟨h01, ?_⟩
    rw [finrank_jointStabAt_vac hΦ, if_neg h01]

end

end PatiSalamJointCount
