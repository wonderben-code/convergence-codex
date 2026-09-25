/-
  ElectroweakCustodial: the electroweak stage counted — a nonzero vacuum `Φ` of the `(1, 2, 2)`
  leaves three generators of `su(2)_L ⊕ su(2)_R` unbroken, the custodial `su(2)`, exactly when
  `Φᴴ Φ` is a multiple of the identity, and one otherwise; `diag(κ, κ')` keeps three exactly when
  `|κ| = |κ'|`, and at the estate's vacuum the one survivor is the charge; with the first-stage
  vacuum as well, only the `T₃R` direction of the custodial `su(2)` survives

  Campaign 3 hardening unit 219 (25 September 2026). Spine link L15 (Higgs sector).

  WHY. Unit 213 counted the first stage: nine, six or four unbroken generators, and the count
  decides the group. The second stage had no count beyond unit 182's single vacuum, and there only
  on `su(2)_L ⊕ u(1)_{T₃R}`, the algebra the first stage leaves.
  `PatiSalamFirstStageClassification`'s NOT list: *"The second stage, the pair with the electroweak
  vacuum, beyond units 203–207"*; `PatiSalamBrokenCount`'s: *"The second stage, and the electroweak
  count, beyond unit 184"*; and unit 217's: at stage 2 the subalgebras are *"characterised at every
  vacuum, not classified"*. Unit 217 put the unbroken subalgebra `stabEWAt Φ` on the whole of
  `su(2)_L ⊕ su(2)_R` at every `Φ`; this file counts it, and reads the count as the unbroken group's
  Lie algebra.

  WHAT IS PROVED.
  (1) Two facts about any unbroken generator `(A, B)`. **`comm_of_mem_stabEWAt`**: `B` commutes with
      `Φᴴ Φ` — the conjugate transpose of `A Φ = Φ B` is `Φᴴ A = B Φᴴ`.
      **`eq_zero_of_mat2_mul_eq_zero`**: a nonzero element of `su(2)` annihilates no nonzero
      matrix, its determinant being `|A₀₀|² + |A₀₁|²`; so at `Φ ≠ 0` an unbroken generator is fixed
      by its right half (`snd_eq_zero_imp`). `mem_stabEWAt_iff`, `star_mat2`.
  (2) **`ewGen Φ = (i · tl(Φ Φᴴ), i · tl(Φᴴ Φ))`** is unbroken at every `Φ` (`ewGen_mem`, since
      `tr (Φ Φᴴ) = tr (Φᴴ Φ)`), and nonzero exactly when `Φᴴ Φ` is not a multiple of the identity
      (`ewGen_ne_zero`); `iTl`, `mat2_iTl`, `star_mul_conjTranspose_self`. When it is not,
      **`stabEWAt_eq_span`**: the unbroken subalgebra is the line through `ewGen Φ`, by unit 213's
      `eq_smul_of_comm`; `finrank_stabEWAt_of_not_scalar`: one.
  (3) When `Φᴴ Φ = c • 1` and `Φ ≠ 0`: `custA` (`B ↦ c⁻¹ • Φ B Φᴴ`) and `custA_mem`, the custodial
      `su(2)` `{(c⁻¹ • Φ B Φᴴ, B)}`; **`finrank_stabEWAt_of_scalar`**: three.
  (4) `stabEWAt_zero`, `finrank_stabEWAt_zero`: six. **`finrank_stabEWAt_dichotomy`** and
      `finrank_stabEWAt_eq_three_iff`: at `Φ ≠ 0`, three exactly when `Φᴴ Φ` is scalar, one
      otherwise.
  (5) The diagonal vacua, unit 205's `vacKK κ κ' = diag(κ, κ')`: `conjTranspose_mul_self_diagonal`,
      `exists_scalar_diagonal_iff` (`Φᴴ Φ` is scalar exactly when `|κ| = |κ'|`) and
      **`finrank_stabEWAt_diagonal`** — a nonzero `diag(κ, κ')` keeps three generators if
      `|κ| = |κ'|` and one otherwise. At the
      estate's `vacEW`: `not_scalar_vacEW`, `ewGen_vacEW` and **`stabEWAt_vacEW`** — the one
      unbroken generator of all of `su(2)_L ⊕ su(2)_R` is `(t3RT, t3RT)`, the charge
      `Q = T₃L + T₃R`: unit 182's `stabEW_eq_span`, on the whole algebra.
  (6) The group. `matLieEW G` for `G ≤ SU(2)_L × SU(2)_R` (unit 217's definition at stage 2),
      `eq_oneParamLR` and **`mem_matLieEW_stabilizer_iff`**: the Lie algebra of `Stab Φ` is exactly
      the matrices of `stabEWAt Φ`; with `toMatEW` (injective, `toMatEW_injective`),
      **`matLieEW_stabilizer_eq`** and `finrank_map_toMatEW`, it is a real subspace of that
      dimension — so the counts above are the unbroken group's Lie-algebra dimensions.
  (7) With the first-stage vacuum. **`snd_mem_t3RLine_of_mem_stabAt_vac`**: at `vac` the `su(2)_R`
      part of every unbroken generator lies on the `T₃R` line — unit 178's entry condition
      `B 1 0 = 0`, with skewness and zero trace — so the same holds of the joint unbroken generators
      at every `(vac, Φ)` (`snd_snd_mem_t3RLine_of_mem_jointStabAt`).
      **`exists_custodial_mem_jointStabAt_iff`**: when `Φᴴ Φ = c • 1` with `c ≠ 0`, a custodial
      generator `(c⁻¹ • Φ B Φᴴ, B)` completes to a joint unbroken generator at `(vac, Φ)` exactly
      when `B` is on the `T₃R` line, a third of unit 178's hypercharge `yG` supplying the `su(4)`
      part; and `exists_custodial_not_mem_jointStabAt`: so the custodial `su(2)` is not in the joint
      unbroken subalgebra.

  NOT PROVED, said exactly.
  • The groups themselves: that `Stab Φ` is `SU(2)`, as `U ↦ (c⁻¹ • Φ U Φᴴ, U)`, in the scalar case
    and a circle otherwise is not proved; (6) is its Lie algebra.
    ⚠ 25 September 2026 (hardening unit 220, `paper_f/ElectroweakUnbrokenGroup.lean`): proved there
    — at every nonzero `Φ` the unbroken group is the commutant of `Φᴴ Φ` in `SU(2)`
    (`stabilizerEquivCommSU2`): `SU(2)`, as `U ↦ (c⁻¹ • Φ U Φᴴ, U)`, when `Φᴴ Φ = c • 1`
    (`stabilizerEquivSU2`), and the circle otherwise, rank one or two (`stabilizerEquivCircle`); the
    two are not isomorphic (`stabilizer_dichotomy`). Kept as written (`ERRATUM 94`).
  • The counts (2)–(5) are for the `(1, 2, 2)` alone under `SU(2)_L × SU(2)_R`. The joint count is
    units 183's and 205's and nothing here changes it: `u(3)` at `(vac, vacEW)`, and the same
    subgroup, `U(3)`, at every nonzero `diag(κ, κ')`. (7) says only which custodial directions
    survive there; the dimension of the joint unbroken subalgebra at a general `(vac, Φ)` is not
    computed.
  • Which vacuum: a potential's minimum, and there is no potential. *Custodial* is the physics name
    for the `su(2)` of (3) — the diagonal one when `Φ` is a multiple of the identity; what it would
    mean for gauge-boson masses is physics the estate does not state. What is proved is the count.
  • Goldstone's theorem, masses: unchanged (units 179 and 184).

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `eq_zero_of_mat2_mul_eq_zero` and
  `snd_eq_zero_imp` take `Φ ≠ 0`, the second also membership and `q.2 = 0`; `comm_of_mem_stabEWAt`
  takes membership; `iTl` and `mat2_iTl` take `star P = P`; `ewGen_ne_zero`, `stabEWAt_eq_span` and
  `finrank_stabEWAt_of_not_scalar` take `Φᴴ Φ` not a multiple of the identity; `custA` takes
  `star c = c` and `Φᴴ Φ = c • 1`, `custA_mem` those and `c ≠ 0`; `finrank_stabEWAt_of_scalar` takes
  `Φ ≠ 0` and `Φᴴ Φ = c • 1`; the dichotomy and `finrank_stabEWAt_eq_three_iff` take `Φ ≠ 0`;
  `finrank_stabEWAt_diagonal` takes `κ ≠ 0 ∨ κ' ≠ 0`; `eq_oneParamLR` takes the two matrix
  equations; `snd_mem_t3RLine_of_mem_stabAt_vac` and `snd_snd_mem_t3RLine_of_mem_jointStabAt` take
  membership at `vac` and at `(vac, Φ)`; `exists_custodial_mem_jointStabAt_iff` takes `c ≠ 0`,
  `star c = c` and `Φᴴ Φ = c • 1`, and `exists_custodial_not_mem_jointStabAt` the last two. The rest
  take nothing.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 37 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements: unit 213's `genT` (`i · tl(Dᴴ D)ᵀ` on the first
  stage), `commT_eq_span` and `finrank_commT_of_not_scalar`, whose argument (2) repeats on the
  `(1, 2, 2)`, and its `eq_smul_of_comm`, `tlPart`, `star_tlPart`, `comm_tlPart_iff`,
  `tlPart_ne_zero`, `star_conjTranspose_mul_self` and `real_smul_eq_complex_smul`, used; unit 182's
  `stabEW_eq_span`, which `stabEWAt_vacEW` extends from `su(2)_L ⊕ u(1)_{T₃R}` to
  `su(2)_L ⊕ su(2)_R`; unit 217's `mem_matLie_stabilizer_iff` and `eq_oneParamG1`, of which (6) is
  the stage-2 form; unit 180's `toMat`, whose stage-2 form `toMatEW` is. Unit 182's
  `t3RLine_eq_map_hyperchargeLine` (the `su(2)_R` image of the hypercharge line is the `T₃R` line),
  which `snd_mem_t3RLine_of_mem_stabAt_vac` extends, as an inclusion, from that line to the whole of
  unit 178's `stab`; unit 178's `act_vac_eq_zero_iff` and `yG_mem_stab`, used. The pinned Mathlib
  supplies `Matrix.exists_mulVec_eq_zero_iff`, `Matrix.conjTranspose_mul_self_eq_zero` and
  `sq_eq_sq₀`, used.

  `#print axioms` on all 37 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamMatrixLie

open Matrix NormedSpace TracelessSkewDimension PatiSalamVacuumStabiliser
  ElectroweakVacuumStabiliser PatiSalamBrokenCount PatiSalamRightSector PatiSalamGaugeAction
  PatiSalamMatrixLie PatiSalamTwoStageStabiliser
open scoped Matrix.Norms.Operator

namespace ElectroweakCustodial

noncomputable section

theorem mem_stabEWAt_iff (Φ : EWBidoublet) (q : traceless 2 × traceless 2) :
    q ∈ stabEWAt Φ ↔ mat2 q.1 * Φ = Φ * mat2 q.2 := by
  change actEW (mat2 q.1) (mat2 q.2) Φ = 0 ↔ _
  rw [actEW, sub_eq_zero]

theorem star_mat2 (B : traceless 2) : star (mat2 B) = -mat2 B := skewAdjoint.mem_iff.mp B.1.2

/-- **Any generator fixing `Φ` has its right part commuting with `Φᴴ Φ`.** -/
theorem comm_of_mem_stabEWAt {Φ : EWBidoublet} {q : traceless 2 × traceless 2}
    (hq : q ∈ stabEWAt Φ) : mat2 q.2 * (Φᴴ * Φ) = (Φᴴ * Φ) * mat2 q.2 := by
  have h := (mem_stabEWAt_iff Φ q).mp hq
  -- Φᴴ A = B Φᴴ, from the conjugate transpose of A Φ = Φ B
  have hs : Φᴴ * mat2 q.1 = mat2 q.2 * Φᴴ := by
    have hA : (mat2 q.1)ᴴ = -mat2 q.1 := by rw [← star_eq_conjTranspose]; exact star_mat2 q.1
    have hB : (mat2 q.2)ᴴ = -mat2 q.2 := by rw [← star_eq_conjTranspose]; exact star_mat2 q.2
    have h' := congrArg conjTranspose h
    rw [conjTranspose_mul, conjTranspose_mul, hA, hB, Matrix.mul_neg, Matrix.neg_mul] at h'
    exact neg_injective h'
  calc mat2 q.2 * (Φᴴ * Φ) = (mat2 q.2 * Φᴴ) * Φ := by rw [Matrix.mul_assoc]
    _ = (Φᴴ * mat2 q.1) * Φ := by rw [hs]
    _ = Φᴴ * (mat2 q.1 * Φ) := by rw [Matrix.mul_assoc]
    _ = Φᴴ * (Φ * mat2 q.2) := by rw [h]
    _ = (Φᴴ * Φ) * mat2 q.2 := by rw [Matrix.mul_assoc]

/-- **A nonzero element of `su(2)` annihilates no nonzero matrix**: its determinant is
`|A₀₀|² + |A₀₁|²`. -/
theorem eq_zero_of_mat2_mul_eq_zero {a : traceless 2} {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (h : mat2 a * Φ = 0) : a = 0 := by
  set A := mat2 a with hAdef
  obtain ⟨i, j, hij⟩ : ∃ i j, Φ i j ≠ 0 := by
    by_contra hc
    exact hΦ (Matrix.ext fun i j => not_not.mp fun h => hc ⟨i, j, h⟩)
  have hdet : A.det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun k => Φ k j, fun hv => hij ?_, ?_⟩
    · exact congrFun hv i
    · funext k
      have := congrFun (congrFun h k) j
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have hs : star A = -A := star_mat2 a
  have h10 : A 1 0 = -star (A 0 1) := by
    have := congrFun (congrFun hs 1) 0
    simp only [star_apply, neg_apply] at this
    rw [this, neg_neg]
  have h00 : star (A 0 0) = -A 0 0 := by
    have := congrFun (congrFun hs 0) 0
    simpa only [star_apply, neg_apply] using this
  have h11 : A 1 1 = -A 0 0 := by
    have ht := trace_mat2 a
    simp only [trace, Fin.sum_univ_two, diag_apply] at ht
    linear_combination ht
  rw [det_fin_two, h11, h10] at hdet
  have hn : Complex.normSq (A 0 0) + Complex.normSq (A 0 1) = 0 := by
    have e1 : ((Complex.normSq (A 0 0) : ℝ) : ℂ) = A 0 0 * star (A 0 0) := by
      rw [Complex.star_def, Complex.mul_conj]
    have e2 : ((Complex.normSq (A 0 1) : ℝ) : ℂ) = A 0 1 * star (A 0 1) := by
      rw [Complex.star_def, Complex.mul_conj]
    have : ((Complex.normSq (A 0 0) + Complex.normSq (A 0 1) : ℝ) : ℂ) = 0 := by
      push_cast
      rw [e1, e2, h00]
      linear_combination hdet
    exact_mod_cast this
  have z00 : A 0 0 = 0 := Complex.normSq_eq_zero.mp (by
    linarith [Complex.normSq_nonneg (A 0 0), Complex.normSq_nonneg (A 0 1)])
  have z01 : A 0 1 = 0 := Complex.normSq_eq_zero.mp (by
    linarith [Complex.normSq_nonneg (A 0 0), Complex.normSq_nonneg (A 0 1)])
  have hA0 : A = 0 := by
    ext k l
    fin_cases k <;> fin_cases l
    · exact z00
    · exact z01
    · simp [h10, z01]
    · simp [h11, z00]
  exact Subtype.ext (Subtype.ext hA0)

/-- `i` times the traceless part of a Hermitian `2 × 2` matrix, as an element of `su(2)`. -/
def iTl (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : star P = P) : traceless 2 :=
  ⟨⟨Complex.I • tlPart P, by
    rw [skewAdjoint.mem_iff, star_smul, Complex.star_def, Complex.conj_I, star_tlPart hP,
      neg_smul]⟩, by
    change (trace (Complex.I • tlPart P)).im = 0
    rw [trace_smul, show trace (tlPart P) = 0 by
      simp [tlPart, trace_sub, trace_smul]]
    simp⟩

theorem mat2_iTl (P : Matrix (Fin 2) (Fin 2) ℂ) (hP : star P = P) :
    mat2 (iTl P hP) = Complex.I • tlPart P := rfl

theorem star_mul_conjTranspose_self (Φ : EWBidoublet) : star (Φ * Φᴴ) = Φ * Φᴴ := by
  rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- **The generator every vacuum leaves unbroken**: `(i · tl(Φ Φᴴ), i · tl(Φᴴ Φ))`. -/
def ewGen (Φ : EWBidoublet) : traceless 2 × traceless 2 :=
  (iTl (Φ * Φᴴ) (star_mul_conjTranspose_self Φ), iTl (Φᴴ * Φ) (star_conjTranspose_mul_self Φ))

theorem ewGen_mem (Φ : EWBidoublet) : ewGen Φ ∈ stabEWAt Φ := by
  rw [mem_stabEWAt_iff]
  simp only [ewGen, mat2_iTl, tlPart, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm Φ Φᴴ]

theorem ewGen_ne_zero {Φ : EWBidoublet} (hns : ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) : ewGen Φ ≠ 0 := by
  intro h
  have h2 : Complex.I • tlPart (Φᴴ * Φ) = 0 := congrArg (fun q => mat2 q.2) h
  rcases smul_eq_zero.mp h2 with hI | hT
  · exact Complex.I_ne_zero hI
  · exact tlPart_ne_zero hns hT

theorem snd_eq_zero_imp {Φ : EWBidoublet} (hΦ : Φ ≠ 0) {q : traceless 2 × traceless 2}
    (hq : q ∈ stabEWAt Φ) (h2 : q.2 = 0) : q = 0 := by
  have h := (mem_stabEWAt_iff Φ q).mp hq
  rw [h2] at h
  have h1 : mat2 q.1 * Φ = 0 := by simpa [mat2] using h
  exact Prod.ext (eq_zero_of_mat2_mul_eq_zero hΦ h1) h2

/-- **When `Φᴴ Φ` is not a multiple of the identity, one generator is unbroken**: the stabiliser is
the line through `ewGen Φ`. -/
theorem stabEWAt_eq_span {Φ : EWBidoublet} (hns : ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) :
    stabEWAt Φ = Submodule.span ℝ {ewGen Φ} := by
  have hΦ : Φ ≠ 0 := fun h => hns ⟨0, by simp [h]⟩
  refine le_antisymm (fun q hq => ?_) ((Submodule.span_le).mpr (by simp [ewGen_mem]))
  set C := mat2 q.2 with hCdef
  have hc : C * tlPart (Φᴴ * Φ) = tlPart (Φᴴ * Φ) * C :=
    (comm_tlPart_iff C (Φᴴ * Φ)).mpr (comm_of_mem_stabEWAt hq)
  have hCt : C 1 1 = -C 0 0 := by
    have ht := trace_mat2 q.2
    simp only [trace, Fin.sum_univ_two, diag_apply] at ht
    linear_combination ht
  obtain ⟨t, ht⟩ := eq_smul_of_comm (tlPart_ne_zero hns) (tlPart_11 _)
    (star_tlPart (star_conjTranspose_mul_self Φ)) hCt (star_mat2 q.2) hc
  have hq2 : (q - t • ewGen Φ).2 = 0 := by
    apply Subtype.ext; apply Subtype.ext
    change mat2 q.2 - t • mat2 (ewGen Φ).2 = 0
    rw [← hCdef, ht, ewGen, mat2_iTl, real_smul_eq_complex_smul, smul_smul, sub_self]
  have hmem : q - t • ewGen Φ ∈ stabEWAt Φ :=
    Submodule.sub_mem _ hq (Submodule.smul_mem _ t (ewGen_mem Φ))
  have h0 := snd_eq_zero_imp hΦ hmem hq2
  rw [sub_eq_zero] at h0
  rw [h0]
  exact Submodule.smul_mem _ t (Submodule.subset_span rfl)

theorem finrank_stabEWAt_of_not_scalar {Φ : EWBidoublet} (hns : ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) :
    Module.finrank ℝ (stabEWAt Φ) = 1 := by
  rw [stabEWAt_eq_span hns, finrank_span_singleton (ewGen_ne_zero hns)]

/-- The custodial partner of `B` when `Φᴴ Φ = c • 1`: `c⁻¹ • Φ B Φᴴ`, again in `su(2)`. -/
def custA {Φ : EWBidoublet} {c : ℂ} (hcs : star c = c) (hc : Φᴴ * Φ = c • 1) (B : traceless 2) :
    traceless 2 :=
  ⟨⟨c⁻¹ • (Φ * mat2 B * Φᴴ), by
    rw [skewAdjoint.mem_iff, star_smul, star_inv₀, hcs, star_eq_conjTranspose, conjTranspose_mul,
      conjTranspose_mul, conjTranspose_conjTranspose, ← star_eq_conjTranspose (mat2 B), star_mat2,
      Matrix.neg_mul, Matrix.mul_neg, smul_neg, Matrix.mul_assoc]⟩, by
    change (trace (c⁻¹ • (Φ * mat2 B * Φᴴ))).im = 0
    rw [trace_smul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hc,
      Matrix.mul_smul, Matrix.mul_one, trace_smul, trace_mat2]
    simp⟩

theorem custA_mem {Φ : EWBidoublet} {c : ℂ} (hc0 : c ≠ 0) (hcs : star c = c)
    (hc : Φᴴ * Φ = c • 1) (B : traceless 2) : (custA hcs hc B, B) ∈ stabEWAt Φ := by
  rw [mem_stabEWAt_iff]
  change (c⁻¹ • (Φ * mat2 B * Φᴴ)) * Φ = Φ * mat2 B
  rw [Matrix.smul_mul, Matrix.mul_assoc, hc, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ hc0, one_smul]

open scoped ComplexOrder in
/-- **When `Φᴴ Φ` is a nonzero multiple of the identity, three generators are unbroken**: the
custodial `su(2)`, `B ↦ (c⁻¹ • Φ B Φᴴ, B)`. -/
theorem finrank_stabEWAt_of_scalar {Φ : EWBidoublet} (hΦ : Φ ≠ 0) {c : ℂ}
    (hc : Φᴴ * Φ = c • 1) : Module.finrank ℝ (stabEWAt Φ) = 3 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hΦ (Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa using hc))
  have hcs : star c = c := by
    have h := star_conjTranspose_mul_self Φ
    rw [hc] at h
    simpa [star_smul] using congrFun (congrFun h 0) 0
  let f : stabEWAt Φ →ₗ[ℝ] traceless 2 :=
    (LinearMap.snd ℝ (traceless 2) (traceless 2)).comp (stabEWAt Φ).subtype
  have hinj : Function.Injective f := fun q q' h => by
    have h2 : ((q : traceless 2 × traceless 2) - q').2 = 0 := by
      change (q : traceless 2 × traceless 2).2 - (q' : traceless 2 × traceless 2).2 = 0
      exact sub_eq_zero.mpr h
    exact Subtype.ext (sub_eq_zero.mp (snd_eq_zero_imp hΦ (Submodule.sub_mem _ q.2 q'.2) h2))
  have hsurj : Function.Surjective f := fun B =>
    ⟨⟨(custA hcs hc B, B), custA_mem hc0 hcs hc B⟩, rfl⟩
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩), finrank_traceless_two]

theorem stabEWAt_zero : stabEWAt 0 = ⊤ := by
  ext q
  simp [mem_stabEWAt_iff]

/-- **At `Φ = 0` all six generators are unbroken.** -/
theorem finrank_stabEWAt_zero : Module.finrank ℝ (stabEWAt 0) = 6 := by
  rw [stabEWAt_zero, finrank_top, Module.finrank_prod, finrank_traceless_two]

/-- **THE ELECTROWEAK STAGE, COUNTED**: a nonzero bidoublet vacuum leaves three unbroken generators
when `Φᴴ Φ` is a multiple of the identity, and one otherwise. -/
theorem finrank_stabEWAt_dichotomy (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    ((∃ c : ℂ, Φᴴ * Φ = c • 1) ∧ Module.finrank ℝ (stabEWAt Φ) = 3) ∨
    ((¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) ∧ Module.finrank ℝ (stabEWAt Φ) = 1) := by
  by_cases h : ∃ c : ℂ, Φᴴ * Φ = c • 1
  · obtain ⟨c, hc⟩ := h
    exact Or.inl ⟨⟨c, hc⟩, finrank_stabEWAt_of_scalar hΦ hc⟩
  · exact Or.inr ⟨h, finrank_stabEWAt_of_not_scalar h⟩

theorem finrank_stabEWAt_eq_three_iff (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    Module.finrank ℝ (stabEWAt Φ) = 3 ↔ ∃ c : ℂ, Φᴴ * Φ = c • 1 := by
  rcases finrank_stabEWAt_dichotomy Φ hΦ with ⟨h, h3⟩ | ⟨h, h1⟩
  · exact ⟨fun _ => h, fun _ => h3⟩
  · exact ⟨fun h3 => absurd (h1.symm.trans h3) (by norm_num), fun h' => absurd h' h⟩

theorem conjTranspose_mul_self_diagonal (κ κ' : ℂ) :
    (diagonal ![κ, κ'])ᴴ * diagonal ![κ, κ'] = diagonal ![star κ * κ, star κ' * κ'] := by
  rw [diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp

/-- **`Φᴴ Φ` is scalar on the diagonal exactly when the two entries have the same modulus.** -/
theorem exists_scalar_diagonal_iff (κ κ' : ℂ) :
    (∃ c : ℂ, (diagonal ![κ, κ'])ᴴ * diagonal ![κ, κ'] = c • 1) ↔ ‖κ‖ = ‖κ'‖ := by
  rw [conjTranspose_mul_self_diagonal]
  constructor
  · rintro ⟨c, hc⟩
    have e0 := congrFun (congrFun hc 0) 0
    have e1 := congrFun (congrFun hc 1) 1
    simp only [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at e0 e1
    have : star κ * κ = star κ' * κ' := by simpa using e0.trans e1.symm
    rw [Complex.star_def, Complex.conj_mul', Complex.conj_mul'] at this
    have h2 : ‖κ‖ ^ 2 = ‖κ'‖ ^ 2 := by exact_mod_cast this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
  · intro hn
    refine ⟨star κ * κ, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Complex.conj_mul', hn]

/-- **The custodial criterion on the diagonal vacua `diag(κ, κ')`**: three unbroken generators when
`|κ| = |κ'|`, one otherwise. -/
theorem finrank_stabEWAt_diagonal (κ κ' : ℂ) (h : κ ≠ 0 ∨ κ' ≠ 0) :
    Module.finrank ℝ (stabEWAt (diagonal ![κ, κ'])) = if ‖κ‖ = ‖κ'‖ then 3 else 1 := by
  have hΦ : diagonal ![κ, κ'] ≠ 0 := by
    intro h0
    rcases h with h | h
    · exact h (by simpa using congrFun (congrFun h0 0) 0)
    · exact h (by simpa using congrFun (congrFun h0 1) 1)
  rcases finrank_stabEWAt_dichotomy _ hΦ with ⟨hs, h3⟩ | ⟨hs, h1⟩
  · rw [h3, if_pos ((exists_scalar_diagonal_iff κ κ').mp hs)]
  · rw [h1, if_neg (fun hn => hs ((exists_scalar_diagonal_iff κ κ').mpr hn))]

theorem not_scalar_vacEW : ¬ ∃ c : ℂ, vacEWᴴ * vacEW = c • 1 := by
  rintro ⟨c, hc⟩
  have e0 : (1 : ℂ) = c := by
    simpa [vacEW, Matrix.mul_apply, Matrix.single_apply] using congrFun (congrFun hc 0) 0
  have e1 : (0 : ℂ) = c := by
    simpa [vacEW, Matrix.mul_apply, Matrix.single_apply] using congrFun (congrFun hc 1) 1
  exact one_ne_zero (e0.trans e1.symm)

theorem ewGen_vacEW : ewGen vacEW = (1 / 2 : ℝ) • (t3RT, t3RT) := by
  have hm : Complex.I • tlPart (vacEW * vacEWᴴ) = (1 / 2 : ℝ) • t3RGen ∧
      Complex.I • tlPart (vacEWᴴ * vacEW) = (1 / 2 : ℝ) • t3RGen := by
    constructor <;>
    · rw [real_smul_eq_complex_smul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [tlPart, vacEW, t3RGen, trace] <;> ring
  exact Prod.ext (Subtype.ext (Subtype.ext hm.1)) (Subtype.ext (Subtype.ext hm.2))

/-- **At the estate's electroweak vacuum the one unbroken generator of all of `su(2)_L ⊕ su(2)_R`
is the charge `Q = T₃L + T₃R`** — unit 182's `stabEW_eq_span`, on the whole algebra rather than on
the `su(2)_L ⊕ u(1)_{T₃R}` the first stage leaves. -/
theorem stabEWAt_vacEW : stabEWAt vacEW = Submodule.span ℝ {(t3RT, t3RT)} := by
  rw [stabEWAt_eq_span not_scalar_vacEW, ewGen_vacEW]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (by norm_num)) _

/-! ## 6. The group's Lie algebra -/

/-- The Lie algebra of a subgroup of `SU(2)_L × SU(2)_R`, as matrix groups define it (unit 217's
`matLie` at stage 2). -/
def matLieEW (G : Subgroup Stage2Group) :
    Set (Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :=
  {M | ∀ t : ℝ, ∃ g ∈ G, (g.1 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • M.1) ∧
    (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • M.2)}

theorem eq_oneParamLR (a b : traceless 2) (t : ℝ) (g : Stage2Group)
    (h1 : (g.1 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • mat2 a))
    (h2 : (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • mat2 b)) : g = oneParamLR a b t :=
  Prod.ext (Subtype.ext (h1.trans (coe_oneParam a t).symm))
    (Subtype.ext (h2.trans (coe_oneParam b t).symm))

/-- **The Lie algebra of the electroweak unbroken group at any `Φ` is the unbroken subalgebra.** -/
theorem mem_matLieEW_stabilizer_iff (Φ : EWBidoublet)
    (M : Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :
    M ∈ matLieEW (MulAction.stabilizer Stage2Group Φ) ↔
      ∃ q ∈ stabEWAt Φ, mat2 q.1 = M.1 ∧ mat2 q.2 = M.2 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (forall_exp_mem_specialUnitaryGroup_iff_traceless M.1).mp fun t => by
      obtain ⟨g, -, h1, -⟩ := h t
      exact h1 ▸ g.1.2
    obtain ⟨b, hb⟩ := (forall_exp_mem_specialUnitaryGroup_iff_traceless M.2).mp fun t => by
      obtain ⟨g, -, -, h2⟩ := h t
      exact h2 ▸ g.2.2
    refine ⟨(a, b), (mem_stabEWAt_iff_fixes Φ _).mpr fun t => ?_, ha, hb⟩
    obtain ⟨g, hg, h1, h2⟩ := h t
    rw [← eq_oneParamLR a b t g (h1.trans (ha ▸ rfl)) (h2.trans (hb ▸ rfl))]
    exact hg
  · rintro ⟨q, hq, h1, h2⟩ t
    exact ⟨oneParamLR q.1 q.2 t, (mem_stabEWAt_iff_fixes Φ q).mp hq t, h1 ▸ coe_oneParam q.1 t,
      h2 ▸ coe_oneParam q.2 t⟩

/-- `su(2)_L ⊕ su(2)_R` inside pairs of matrices, `ℝ`-linearly — unit 180's `toMat` at stage 2. -/
def toMatEW :
    traceless 2 × traceless 2 →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ where
  toFun q := (mat2 q.1, mat2 q.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toMatEW_injective : Function.Injective toMatEW := by
  intro p q h
  have h1 : mat2 p.1 = mat2 q.1 := congrArg Prod.fst h
  have h2 : mat2 p.2 = mat2 q.2 := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext (Subtype.ext h1)) (Subtype.ext (Subtype.ext h2))

/-- **The electroweak unbroken group's Lie algebra is a real subspace**: `stabEWAt Φ` in
matrices. -/
theorem matLieEW_stabilizer_eq (Φ : EWBidoublet) :
    matLieEW (MulAction.stabilizer Stage2Group Φ) = ((stabEWAt Φ).map toMatEW : Set _) := by
  ext M
  rw [mem_matLieEW_stabilizer_iff]
  constructor
  · rintro ⟨q, hq, h1, h2⟩
    exact ⟨q, hq, Prod.ext h1 h2⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, rfl, rfl⟩

/-- **… of the unbroken subalgebra's dimension**: six, three or one by (4). -/
theorem finrank_map_toMatEW (Φ : EWBidoublet) :
    Module.finrank ℝ ((stabEWAt Φ).map toMatEW) = Module.finrank ℝ (stabEWAt Φ) :=
  (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective toMatEW toMatEW_injective (stabEWAt Φ))).symm

/-! ## 7. With the first-stage vacuum -/

/-- **At the first-stage vacuum the `su(2)_R` part of every unbroken generator lies on the `T₃R`
line**: unit 178's entry condition `B 1 0 = 0`, with skewness and zero trace. -/
theorem snd_mem_t3RLine_of_mem_stabAt_vac {p : PSLie} (hp : p ∈ stabAt vac) : p.2 ∈ t3RLine := by
  obtain ⟨-, -, h10⟩ := (act_vac_eq_zero_iff _ _).mp ((mem_stabAt_iff vac p).mp hp)
  set B := mat2 p.2 with hBdef
  have hs : star B = -B := star_mat2 p.2
  have h01 : B 0 1 = 0 := by
    have := congrFun (congrFun hs 1) 0
    rw [star_apply, neg_apply, h10, neg_zero] at this
    simpa using this
  have h11 : B 1 1 = -B 0 0 := by
    have ht := trace_mat2 p.2
    simp only [trace, Fin.sum_univ_two, diag_apply] at ht
    linear_combination ht
  have hre : (B 0 0).re = 0 := by
    have := congrArg Complex.re (congrFun (congrFun hs 0) 0)
    simp only [star_apply, neg_apply, Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  refine Submodule.mem_span_singleton.mpr ⟨(B 0 0).im, ?_⟩
  apply Subtype.ext; apply Subtype.ext
  change (B 0 0).im • t3RGen = B
  ext i j
  fin_cases i <;> fin_cases j <;> simp [t3RGen, h01, h10, h11, Complex.ext_iff, hre]

/-- … and so at every pair `(vac, Φ)` the joint unbroken generators have their `su(2)_R` part on
that line. -/
theorem snd_snd_mem_t3RLine_of_mem_jointStabAt {Φ : EWBidoublet} {p : Full}
    (hp : p ∈ jointStabAt (vac, Φ)) : p.2.2 ∈ t3RLine :=
  snd_mem_t3RLine_of_mem_stabAt_vac ((mem_jointStabAt_iff _ p).mp hp).1

/-- **Exactly the `T₃R` direction of the custodial `su(2)` survives the first-stage vacuum**: when
`Φᴴ Φ = c • 1`, a custodial generator `(c⁻¹ • Φ B Φᴴ, B)` completes to a joint unbroken generator at
`(vac, Φ)` exactly when `B` is on the `T₃R` line — a third of unit 178's hypercharge supplies the
`su(4)` part. -/
theorem exists_custodial_mem_jointStabAt_iff {Φ : EWBidoublet} {c : ℂ} (hc0 : c ≠ 0)
    (hcs : star c = c) (hc : Φᴴ * Φ = c • 1) (B : traceless 2) :
    (∃ a : traceless 4, (a, custA hcs hc B, B) ∈ jointStabAt (vac, Φ)) ↔ B ∈ t3RLine := by
  constructor
  · rintro ⟨a, h⟩
    exact snd_snd_mem_t3RLine_of_mem_jointStabAt h
  · intro hB
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hB
    refine ⟨t • ((1 / 3 : ℝ) • blT), (mem_jointStabAt_iff _ _).mpr ⟨?_, custA_mem hc0 hcs hc _⟩⟩
    have h := stab.smul_mem (t * (1 / 3 : ℝ)) yG_mem_stab
    convert h using 1
    refine Prod.ext ?_ ?_
    · change t • ((1 / 3 : ℝ) • blT) = (t * (1 / 3 : ℝ)) • blT
      rw [smul_smul]
    · change t • t3RT = (t * (1 / 3 : ℝ)) • ((3 : ℝ) • t3RT)
      rw [smul_smul, show t * (1 / 3 : ℝ) * 3 = t by ring]

/-- **So the custodial `su(2)` is not in the joint unbroken subalgebra**: some custodial generator
is the `su(2)_L ⊕ su(2)_R` part of no joint unbroken generator at `(vac, Φ)`. -/
theorem exists_custodial_not_mem_jointStabAt {Φ : EWBidoublet} {c : ℂ} (hcs : star c = c)
    (hc : Φᴴ * Φ = c • 1) :
    ∃ B : traceless 2, ∀ a : traceless 4, (a, custA hcs hc B, B) ∉ jointStabAt (vac, Φ) := by
  have hlt : t3RLine < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    have h1 := finrank_t3RLine
    rw [h, finrank_top, finrank_traceless_two] at h1
    norm_num at h1
  obtain ⟨B, -, hB⟩ := SetLike.exists_of_lt hlt
  exact ⟨B, fun a h => hB (snd_snd_mem_t3RLine_of_mem_jointStabAt h)⟩

end

end ElectroweakCustodial
