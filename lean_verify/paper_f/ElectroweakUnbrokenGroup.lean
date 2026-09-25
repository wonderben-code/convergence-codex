/-
  ElectroweakUnbrokenGroup: the electroweak stage's unbroken GROUP, classified — at every nonzero
  bidoublet vacuum `Φ` it is the commutant of `Φᴴ Φ` in `SU(2)`: `SU(2)` itself when `Φᴴ Φ` is a
  multiple of the identity, and the circle otherwise, two groups that are not isomorphic

  Campaign 3 hardening unit 220 (25 September 2026). Spine link L15 (Higgs sector).

  WHY. Unit 219 (`ElectroweakCustodial`) counted the electroweak stage in the Lie algebra — three
  unbroken generators when `Φᴴ Φ` is scalar, one otherwise — and read the counts as the unbroken
  groups' Lie-algebra dimensions. Its NOT list: *"The groups themselves: that `Stab Φ` is `SU(2)`,
  as `U ↦ (c⁻¹ • Φ U Φᴴ, U)`, in the scalar case and a circle otherwise is not proved"*. Unit 212
  (`PatiSalamFirstStageClassification`) did the group level for the first stage; this file does it
  for the second, with unit 211's commutant `commSU2` and unit 212's `commHermitianEquiv`. Before
  this file the stage-2 stabiliser appeared only in membership statements — unit 191's one-parameter
  ones (`mem_stabEW_iff_mem_stabilizer`), unit 199's entrywise `mem_stabilizer_vacEW_iff`, unit
  205's `mem_stabilizer_vacKK_iff` under the first-stage condition — and no stage-2 unbroken group
  had been identified.

  WHAT IS PROVED.
  (1) **`mem_stabilizer_stage2_iff`**: `(h, k)` fixes `Φ` iff `h Φ = Φ k` (`star_mul_self_snd`,
      `mul_star_self_snd`) — the form of unit 199's `mem_stabilizer_vacEW_iff` at every `Φ`.
  (2) The scalar case, explicitly. When `Φᴴ Φ = c • 1` with `c ≠ 0`:
      `star_eq_of_conjTranspose_mul_self` (`c` is real), `mul_conjTranspose_self_eq` (`Φ Φᴴ = c • 1`
      too), `custG_mem` (`c⁻¹ • Φ U Φᴴ ∈ SU(2)` for `U ∈ SU(2)`), and **`stabilizerEquivSU2`**: the
      unbroken group is `SU(2)`, as `U ↦ (c⁻¹ • Φ U Φᴴ, U)` — the group whose Lie algebra is unit
      219's custodial `su(2)`.
  (3) Into the commutant, at every `Φ ≠ 0`. `snd_mem_commSU2`: the right half of an unbroken element
      commutes with `Φᴴ Φ`; **`eq_one_of_mul_eq_self`**: an element of `SU(2)` fixing a nonzero
      matrix is the identity (`det (k − 1) = 0` gives `tr k = 2`, and two unit columns do the rest);
      `fst_eq_of_snd_eq`: so an unbroken element is determined by its right half; `toComm` and
      **`toComm_injective`**.
  (4) Onto the commutant, at every `Φ ≠ 0`. Invertible `Φ`: `conj_mem_of_mem_commSU2`,
      `U ↦ (Φ U Φ⁻¹, U)`. Rank one: **`mul_mul_self_of_det_eq_zero`** — for `2 × 2` matrices with
      `det P = 0`, `P X P = tr (X P) • P`, the `2 × 2` identity
      `P X P = tr (X P) • P − det P • (tr X • 1 − X)` (a consequence of Cayley–Hamilton) at
      `det P = 0`, checked entry by entry as a polynomial identity; with it
      **`mul_eq_smul_of_det_eq_zero`** (a `U` commuting with `Φᴴ Φ` acts on `Φ` as a scalar,
      `Φ U = μ • Φ`), `trace_mul_conjTranspose_ne_zero`, `star_mul_self_of_mul_eq_smul` (`|μ| = 1`),
      the projector `projQ` onto the column space (`projQ_mul_self`, `projQ_mul_projQ`,
      `star_projQ`, `trace_projQ`, `det_projQ`) and **`rankOneLeft`** — `μ` on that line and `μ̄` on
      its complement — with `rankOneLeft_mul` and `rankOneLeft_mem`. So **`toComm_surjective`**, and
      **`stabilizerEquivCommSU2`**: at every nonzero `Φ` the unbroken group IS `commSU2 (Φᴴ Φ)`.
  (5) The classification. **`stabilizerEquivCircle`**: when `Φᴴ Φ` is not scalar, the circle, by
      `commHermitianEquiv` — rank one or two; **`not_nonempty_SU2_equiv_circle`** (unit 212's centre
      argument: `i ∈ U(1)` is central and does not square to one);
      **`nonempty_stabilizer_equiv_SU2_iff`** and **`nonempty_stabilizer_equiv_circle_iff`** — unit
      219's `finrank_stabEWAt_eq_three_iff` at the group level; **`stabilizer_dichotomy`**.
  (6) The neutral plane, unit 205's `vacKK κ κ' = diag(κ, κ')`, and the estate's vacuum.
      `vacKK_ne_zero`, `nonempty_stabilizer_vacKK_equiv_SU2_iff` and
      **`nonempty_stabilizer_vacKK_equiv_circle_iff`**: a nonzero `diag(κ, κ')` leaves the circle
      exactly when `|κ| ≠ |κ'|`, and `SU(2)` otherwise — unit 219's `finrank_stabEWAt_diagonal` at
      the group level; **`stabilizerVacEWEquivCircle`**: at `vacEW` the unbroken subgroup of
      `SU(2)_L × SU(2)_R` is the circle.

  NOT PROVED, said exactly.
  • `Φ = 0` is excluded throughout; its stabiliser is the whole group, and no statement here says
    so.
  • The joint group is unchanged: units 199's and 205's `U(3)`. This file is the `(1, 2, 2)` alone.
    ⚠ 25 September 2026 (hardening unit 222, `paper_f/PatiSalamJointClassification.lean`): the joint
    group at every `(vac, Φ)` is computed there from this file's `fst_eq_of_snd_eq` and
    `snd_mem_commSU2` — `U(3) × SU(2)` at `Φ = 0`, `U(3)` at orthogonal columns and `SU(3) × {±1}`
    otherwise (`joint_trichotomy`). Kept as written (`ERRATUM 94`).
  • Topology: the isomorphisms are of groups; unit 209's topological upgrades are not made here.
  • That these groups' Lie algebras are unit 219's `stabEWAt Φ` is unit 219's
    `mem_matLieEW_stabilizer_iff`; no statement here joins the two files.
  • Which vacuum, masses, and what *custodial* would mean physically: unit 219's bullets, unchanged.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `star_eq_of_conjTranspose_mul_self` takes
  `Φᴴ Φ = c • 1`, `mul_conjTranspose_self_eq` that and `c ≠ 0`, `custG_mem` those and `U ∈ SU(2)`,
  `stabilizerEquivSU2` `c ≠ 0` and `Φᴴ Φ = c • 1`; `snd_mem_commSU2` membership;
  `eq_one_of_mul_eq_self` takes `k ∈ SU(2)`, `Φ ≠ 0` and `k Φ = Φ`; `fst_eq_of_snd_eq` `Φ ≠ 0`, two
  memberships and equal right halves; `conj_mem_of_mem_commSU2` `IsUnit Φ.det` and commutant
  membership; `mul_mul_self_of_det_eq_zero` `det P = 0`; `trace_mul_conjTranspose_ne_zero` `Φ ≠ 0`;
  `mul_eq_smul_of_det_eq_zero` `Φ ≠ 0`, `det Φ = 0` and the commutation; `projQ_mul_self`,
  `projQ_mul_projQ` and `rankOneLeft_mul` `Φ ≠ 0` and `det Φ = 0`, `rankOneLeft_mem` those and
  `μ̄ μ = 1`; `trace_projQ` `Φ ≠ 0`; `det_projQ` `det Φ = 0`; `star_mul_self_of_mul_eq_smul`
  `Φ ≠ 0`, `U Uᴴ = 1` and `Φ U = μ • Φ`; `toComm_injective`, `toComm_surjective`,
  `stabilizerEquivCommSU2`, the two `nonempty_stabilizer_equiv_…_iff` and `stabilizer_dichotomy`
  `Φ ≠ 0`, and `stabilizerEquivCircle` that and `Φᴴ Φ` not scalar; `vacKK_ne_zero` and the two
  `vacKK` biconditionals `κ ≠ 0 ∨ κ' ≠ 0`. The rest take elements of their types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 37 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list; `mem_stabilizer_iff` is Mathlib's `MulAction` name, so the file's is
  `mem_stabilizer_stage2_iff`; none of the 37 is taken. The nearest statements: unit 212's
  `stabilizerVac2EquivOfScalar`, `stabilizerVac2EquivCircle`,
  `nonempty_stabilizer_equiv_SU2_SU2_iff` and `not_nonempty_SU2_SU2_equiv_SU2_circle` (the
  first-stage forms), and its `commHermitianEquiv` and `mul_self_eq_one_of_mem_center` and `unitI`,
  used; unit 211's `commSU2`, used; unit 199's `mem_stabilizer_vacEW_iff`, which (1) extends; units
  199's and 205's `stabilizerPairEquivU3` and `stabilizer_vacKK_eq` (the joint group, not the
  stage-2 one); unit 219's `custA` and `comm_of_mem_stabEWAt` (the Lie-algebra forms of `custG_mem`
  and `snd_mem_commSU2`), and its `exists_scalar_diagonal_iff` and `not_scalar_vacEW`, used. The
  pinned Mathlib supplies `Matrix.exists_mulVec_eq_zero_iff`, `mul_eq_one_comm`,
  `Matrix.conjTranspose_mul_self_eq_zero`, `Matrix.trace_mul_conjTranspose_self_eq_zero_iff` (in
  `Mathlib.LinearAlgebra.Matrix.PosDef`, imported for it), `Ring.mul_inverse_cancel` and
  `MulEquiv.ofBijective`, used; the `2 × 2` identity in (4) was written here.

  `#print axioms` on all 37 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import ElectroweakCustodial
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix PatiSalamGaugeAction ElectroweakVacuumStabiliser PatiSalamRankTwoStabiliser
  PatiSalamFirstStageClassification PatiSalamTwoComponentVacuum ElectroweakCustodial

namespace ElectroweakUnbrokenGroup

noncomputable section

theorem star_mul_self_snd (g : Stage2Group) :
    star (g.2 : Matrix (Fin 2) (Fin 2) ℂ) * (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp g.2.2).1

theorem mul_star_self_snd (g : Stage2Group) :
    (g.2 : Matrix (Fin 2) (Fin 2) ℂ) * star (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp g.2.2).1

/-- **Membership of the stage-2 unbroken group**: `h Φ k⁻¹ = Φ` iff `h Φ = Φ k`. -/
theorem mem_stabilizer_stage2_iff (Φ : EWBidoublet) (g : Stage2Group) :
    g ∈ MulAction.stabilizer Stage2Group Φ ↔
      (g.1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ = Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [MulAction.mem_stabilizer_iff, stage2_smul_def, stage2Act]
  constructor
  · intro h
    calc (g.1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ
        = (g.1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ * (star (g.2 : Matrix (Fin 2) (Fin 2) ℂ) *
          (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) := by rw [star_mul_self_snd, Matrix.mul_one]
      _ = ((g.1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ * star (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) *
          (g.2 : Matrix (Fin 2) (Fin 2) ℂ) := by simp only [Matrix.mul_assoc]
      _ = Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ) := by rw [h]
  · intro h
    rw [h, Matrix.mul_assoc, mul_star_self_snd, Matrix.mul_one]

theorem star_eq_of_conjTranspose_mul_self {Φ : EWBidoublet} {c : ℂ} (hc : Φᴴ * Φ = c • 1) :
    star c = c := by
  have h := congrArg star hc
  rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, star_smul,
    star_one] at h
  have h00 := congrFun (congrFun (h.symm.trans hc) 0) 0
  simpa using h00

theorem mul_conjTranspose_self_eq {Φ : EWBidoublet} {c : ℂ} (hc0 : c ≠ 0)
    (hc : Φᴴ * Φ = c • 1) : Φ * Φᴴ = c • 1 := by
  have h1 : (c⁻¹ • Φᴴ) * Φ = 1 := by
    rw [Matrix.smul_mul, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : Φ * (c⁻¹ • Φᴴ) = 1 := mul_eq_one_comm.mp h1
  rw [Matrix.mul_smul] at h2
  calc Φ * Φᴴ = c • (c⁻¹ • (Φ * Φᴴ)) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    _ = c • 1 := by rw [h2]

/-- **The custodial partner of `U ∈ SU(2)`, `c⁻¹ • Φ U Φᴴ`, is in `SU(2)`.** -/
theorem custG_mem {Φ : EWBidoublet} {c : ℂ} (hc0 : c ≠ 0) (hc : Φᴴ * Φ = c • 1)
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ specialUnitaryGroup (Fin 2) ℂ) :
    c⁻¹ • (Φ * U * Φᴴ) ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hcs := star_eq_of_conjTranspose_mul_self hc
  have hc' := mul_conjTranspose_self_eq hc0 hc
  obtain ⟨hUu, hUd⟩ := mem_specialUnitaryGroup_iff.mp hU
  have hUU : U * star U = 1 := mem_unitaryGroup_iff.mp hUu
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff]
  constructor
  · rw [star_smul, star_inv₀, hcs, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      conjTranspose_conjTranspose, ← star_eq_conjTranspose U, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    have : Φ * U * Φᴴ * (Φ * (star U * Φᴴ)) = c • (Φ * Φᴴ) := by
      calc Φ * U * Φᴴ * (Φ * (star U * Φᴴ)) = Φ * U * (Φᴴ * Φ) * star U * Φᴴ := by
            simp only [Matrix.mul_assoc]
        _ = c • (Φ * (U * star U) * Φᴴ) := by
            rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul]
            simp only [Matrix.mul_assoc]
        _ = c • (Φ * Φᴴ) := by rw [hUU, Matrix.mul_one]
    rw [this, hc', smul_smul, smul_smul, show c⁻¹ * c⁻¹ * c * c = 1 by field_simp, one_smul]
  · rw [det_smul, det_mul, det_mul, hUd, mul_one, ← det_mul, hc', det_smul, det_one,
      Fintype.card_fin, mul_one, ← mul_pow, inv_mul_cancel₀ hc0, one_pow]

/-- **When `Φᴴ Φ = c • 1` with `c ≠ 0`, the unbroken group is `SU(2)`**, as
`U ↦ (c⁻¹ • Φ U Φᴴ, U)`. -/
def stabilizerEquivSU2 {Φ : EWBidoublet} {c : ℂ} (hc0 : c ≠ 0) (hc : Φᴴ * Φ = c • 1) :
    MulAction.stabilizer Stage2Group Φ ≃* SU2 where
  toFun g := (g : Stage2Group).2
  invFun U := ⟨(⟨c⁻¹ • (Φ * U * Φᴴ), custG_mem hc0 hc U.2⟩, U), by
    rw [mem_stabilizer_stage2_iff]
    change c⁻¹ • (Φ * (U : Matrix (Fin 2) (Fin 2) ℂ) * Φᴴ) * Φ = Φ * U
    rw [Matrix.smul_mul, Matrix.mul_assoc, hc, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hc0, one_smul]⟩
  left_inv g := by
    obtain ⟨⟨g1, g2⟩, hg⟩ := g
    have h := (mem_stabilizer_stage2_iff Φ _).mp hg
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change c⁻¹ • (Φ * (g2 : Matrix (Fin 2) (Fin 2) ℂ) * Φᴴ) = g1
      rw [← h, Matrix.mul_assoc, mul_conjTranspose_self_eq hc0 hc, Matrix.mul_smul,
        Matrix.mul_one, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    · rfl
  right_inv U := rfl
  map_mul' g h := rfl

/-- The right half of any unbroken `g` commutes with `Φᴴ Φ`. -/
theorem snd_mem_commSU2 {Φ : EWBidoublet} {g : Stage2Group}
    (hg : g ∈ MulAction.stabilizer Stage2Group Φ) : g.2 ∈ commSU2 (Φᴴ * Φ) := by
  have h := (mem_stabilizer_stage2_iff Φ g).mp hg
  set L := (g.1 : Matrix (Fin 2) (Fin 2) ℂ)
  set R := (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  have hL : star L * L = 1 := mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp g.1.2).1
  have hR : R * star R = 1 := mul_star_self_snd g
  -- Φᴴ Lᴴ = Rᴴ Φᴴ, so Φᴴ Φ R = Φᴴ L Φ = R Φᴴ Φ
  have hs : Φᴴ * star L = star R * Φᴴ := by
    have := congrArg conjTranspose h
    rwa [conjTranspose_mul, conjTranspose_mul, ← star_eq_conjTranspose L,
      ← star_eq_conjTranspose R] at this
  have hs' : Φᴴ * L = R * Φᴴ := by
    calc Φᴴ * L = R * star R * Φᴴ * L := by rw [hR, Matrix.one_mul]
      _ = R * (star R * Φᴴ) * L := by simp only [Matrix.mul_assoc]
      _ = R * (Φᴴ * star L) * L := by rw [hs]
      _ = R * Φᴴ * (star L * L) := by simp only [Matrix.mul_assoc]
      _ = R * Φᴴ := by rw [hL, Matrix.mul_one]
  change R * (Φᴴ * Φ) = Φᴴ * Φ * R
  calc R * (Φᴴ * Φ) = Φᴴ * L * Φ := by rw [hs', Matrix.mul_assoc]
    _ = Φᴴ * Φ * R := by rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc]

/-- **An element of `SU(2)` fixing a nonzero matrix is the identity**: `det (k − 1) = 0` gives
`tr k = 2`, and two unit columns with diagonal entries summing to two force `k = 1`. -/
theorem eq_one_of_mul_eq_self {k : Matrix (Fin 2) (Fin 2) ℂ}
    (hk : k ∈ specialUnitaryGroup (Fin 2) ℂ) {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (h : k * Φ = Φ) :
    k = 1 := by
  obtain ⟨hku, hkd⟩ := mem_specialUnitaryGroup_iff.mp hk
  have hkk : star k * k = 1 := mem_unitaryGroup_iff'.mp hku
  obtain ⟨i, j, hij⟩ : ∃ i j, Φ i j ≠ 0 := by
    by_contra hc
    exact hΦ (Matrix.ext fun i j => not_not.mp fun h => hc ⟨i, j, h⟩)
  have h0 : (k - 1) * Φ = 0 := by rw [Matrix.sub_mul, h, Matrix.one_mul, sub_self]
  have hdet : (k - 1).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨fun r => Φ r j, fun hv => hij (congrFun hv i), ?_⟩
    funext r
    have := congrFun (congrFun h0 r) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  rw [det_fin_two] at hdet hkd
  simp only [sub_apply, one_apply_eq, one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), sub_zero] at hdet
  have htr : k 0 0 + k 1 1 = 2 := by linear_combination hkd - hdet
  have c0 := congrFun (congrFun hkk 0) 0
  have c1 := congrFun (congrFun hkk 1) 1
  simp only [mul_apply, star_apply, Fin.sum_univ_two, one_apply_eq] at c0 c1
  have n0 : Complex.normSq (k 0 0) + Complex.normSq (k 1 0) = 1 := by
    have : ((Complex.normSq (k 0 0) + Complex.normSq (k 1 0) : ℝ) : ℂ) = 1 := by
      push_cast
      rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
      simpa [Complex.star_def] using c0
    exact_mod_cast this
  have n1 : Complex.normSq (k 0 1) + Complex.normSq (k 1 1) = 1 := by
    have : ((Complex.normSq (k 0 1) + Complex.normSq (k 1 1) : ℝ) : ℂ) = 1 := by
      push_cast
      rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
      simpa [Complex.star_def] using c1
    exact_mod_cast this
  rw [Complex.normSq_apply, Complex.normSq_apply] at n0 n1
  have hre : (k 0 0).re + (k 1 1).re = 2 := by simpa using congrArg Complex.re htr
  have him : (k 0 0).im + (k 1 1).im = 0 := by simpa using congrArg Complex.im htr
  have ra : (k 0 0).re = 1 := by
    nlinarith [sq_nonneg ((k 0 0).re - (k 1 1).re), sq_nonneg (k 0 0).im, sq_nonneg (k 1 1).im,
      sq_nonneg (k 1 0).re, sq_nonneg (k 1 0).im, sq_nonneg (k 0 1).re, sq_nonneg (k 0 1).im]
  have rd : (k 1 1).re = 1 := by linarith
  have ia : (k 0 0).im = 0 := by
    nlinarith [sq_nonneg (k 0 0).im, sq_nonneg (k 1 0).re, sq_nonneg (k 1 0).im]
  have id' : (k 1 1).im = 0 := by linarith
  have c10 : k 1 0 = 0 := by
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;>
      nlinarith [sq_nonneg (k 1 0).re, sq_nonneg (k 1 0).im]
  have c01 : k 0 1 = 0 := by
    apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;>
      nlinarith [sq_nonneg (k 0 1).re, sq_nonneg (k 0 1).im]
  have a1 : k 0 0 = 1 := Complex.ext (by simpa using ra) (by simpa using ia)
  have d1 : k 1 1 = 1 := Complex.ext (by simpa using rd) (by simpa using id')
  ext r s
  fin_cases r <;> fin_cases s <;> simp [a1, d1, c01, c10]

/-- **At `Φ ≠ 0` an unbroken element is determined by its right half.** -/
theorem fst_eq_of_snd_eq {Φ : EWBidoublet} (hΦ : Φ ≠ 0) {g h : Stage2Group}
    (hg : g ∈ MulAction.stabilizer Stage2Group Φ) (hh : h ∈ MulAction.stabilizer Stage2Group Φ)
    (h2 : g.2 = h.2) : g.1 = h.1 := by
  have e1 := (mem_stabilizer_stage2_iff Φ g).mp hg
  have e2 := (mem_stabilizer_stage2_iff Φ h).mp hh
  have hh1 : star (h.1 : Matrix (Fin 2) (Fin 2) ℂ) * h.1 = 1 :=
    mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp h.1.2).1
  have hk : ((h.1⁻¹ * g.1 : SU2) : Matrix (Fin 2) (Fin 2) ℂ) * Φ = Φ := by
    change star (h.1 : Matrix (Fin 2) (Fin 2) ℂ) * g.1 * Φ = Φ
    rw [Matrix.mul_assoc, e1, h2, ← e2, ← Matrix.mul_assoc, hh1, Matrix.one_mul]
  have := eq_one_of_mul_eq_self (h.1⁻¹ * g.1).2 hΦ hk
  have h1 : h.1⁻¹ * g.1 = 1 := Subtype.ext this
  rw [inv_mul_eq_one] at h1
  exact h1.symm

/-- The unbroken group into the commutant of `Φᴴ Φ`, by the right half. -/
def toComm (Φ : EWBidoublet) : MulAction.stabilizer Stage2Group Φ →* commSU2 (Φᴴ * Φ) where
  toFun g := ⟨(g : Stage2Group).2, snd_mem_commSU2 g.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toComm_injective {Φ : EWBidoublet} (hΦ : Φ ≠ 0) : Function.Injective (toComm Φ) := by
  intro g h hgh
  have h2 : (g : Stage2Group).2 = (h : Stage2Group).2 := congrArg Subtype.val hgh
  exact Subtype.ext (Prod.ext (fst_eq_of_snd_eq hΦ g.2 h.2 h2) h2)

/-- For invertible `Φ`, `Φ U Φ⁻¹ ∈ SU(2)` whenever `U ∈ SU(2)` commutes with `Φᴴ Φ`. -/
theorem conj_mem_of_mem_commSU2 {Φ : EWBidoublet} (hΦ : IsUnit Φ.det) {U : SU2}
    (hU : U ∈ commSU2 (Φᴴ * Φ)) :
    Φ * (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ⁻¹ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hUc : (U : Matrix (Fin 2) (Fin 2) ℂ) * (Φᴴ * Φ) = Φᴴ * Φ * U := hU
  obtain ⟨hUu, hUd⟩ := mem_specialUnitaryGroup_iff.mp U.2
  have hUU : star (U : Matrix (Fin 2) (Fin 2) ℂ) * U = 1 := mem_unitaryGroup_iff'.mp hUu
  have hΦs : IsUnit Φᴴ.det := by
    rw [det_conjTranspose]; exact hΦ.star
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff']
  constructor
  · rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv,
      ← star_eq_conjTranspose (U : Matrix (Fin 2) (Fin 2) ℂ)]
    calc Φᴴ⁻¹ * (star (U : Matrix (Fin 2) (Fin 2) ℂ) * Φᴴ) * (Φ * U * Φ⁻¹)
        = Φᴴ⁻¹ * star (U : Matrix (Fin 2) (Fin 2) ℂ) * ((Φᴴ * Φ) * U) * Φ⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = Φᴴ⁻¹ * (star (U : Matrix (Fin 2) (Fin 2) ℂ) * U) * (Φᴴ * Φ) * Φ⁻¹ := by
          rw [← hUc]; simp only [Matrix.mul_assoc]
      _ = (Φᴴ⁻¹ * Φᴴ) * (Φ * Φ⁻¹) := by rw [hUU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [nonsing_inv_mul _ hΦs, mul_nonsing_inv _ hΦ, Matrix.mul_one]
  · rw [det_mul, det_mul, hUd, mul_one, det_nonsing_inv, Ring.mul_inverse_cancel _ hΦ]

/-- **For a `2 × 2` matrix `P` of determinant zero, `P X P = tr (X P) • P`** — the `2 × 2`
identity `P X P = tr (X P) • P − det P • (tr X • 1 − X)`, a consequence of Cayley–Hamilton, at
`det P = 0`; each entry is checked as a polynomial identity. -/
theorem mul_mul_self_of_det_eq_zero {P : Matrix (Fin 2) (Fin 2) ℂ} (h : P.det = 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : P * X * P = trace (X * P) • P := by
  rw [det_fin_two] at h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, trace, diag_apply, Matrix.smul_apply,
      smul_eq_mul, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination (-X 1 1) * h
  · linear_combination (X 0 1) * h
  · linear_combination (X 1 0) * h
  · linear_combination (-X 0 0) * h

open scoped ComplexOrder in
/-- `tr (Φ Φᴴ) ≠ 0` for `Φ ≠ 0`. -/
theorem trace_mul_conjTranspose_ne_zero {Φ : EWBidoublet} (hΦ : Φ ≠ 0) :
    trace (Φ * Φᴴ) ≠ 0 := fun h => hΦ (trace_mul_conjTranspose_self_eq_zero_iff.mp h)

/-- **Rank one: a `U` commuting with `Φᴴ Φ` acts on `Φ` as a scalar**, `Φ U = μ • Φ` with
`μ = tr (U Φᴴ Φ) / tr (Φ Φᴴ)`. -/
theorem mul_eq_smul_of_det_eq_zero {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (hdet : Φ.det = 0)
    {U : Matrix (Fin 2) (Fin 2) ℂ} (hUc : U * (Φᴴ * Φ) = Φᴴ * Φ * U) :
    Φ * U = (trace (U * Φᴴ * Φ) / trace (Φ * Φᴴ)) • Φ := by
  have ht := trace_mul_conjTranspose_ne_zero hΦ
  have e1 : Φ * (U * Φᴴ) * Φ = trace (U * Φᴴ * Φ) • Φ := mul_mul_self_of_det_eq_zero hdet _
  have e2 : Φ * Φᴴ * Φ = trace (Φᴴ * Φ) • Φ := mul_mul_self_of_det_eq_zero hdet _
  have e3 : Φ * (U * Φᴴ) * Φ = trace (Φ * Φᴴ) • (Φ * U) := by
    calc Φ * (U * Φᴴ) * Φ = Φ * (U * (Φᴴ * Φ)) := by simp only [Matrix.mul_assoc]
      _ = Φ * Φᴴ * Φ * U := by rw [hUc]; simp only [Matrix.mul_assoc]
      _ = trace (Φ * Φᴴ) • (Φ * U) := by
          rw [e2, Matrix.smul_mul, trace_mul_comm]
  rw [e3] at e1
  calc Φ * U = (trace (Φ * Φᴴ))⁻¹ • (trace (Φ * Φᴴ) • (Φ * U)) := by
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    _ = _ := by rw [e1, smul_smul, div_eq_inv_mul]

/-- The projector onto the column space of a rank-one `Φ`. -/
noncomputable def projQ (Φ : EWBidoublet) : Matrix (Fin 2) (Fin 2) ℂ :=
  (trace (Φ * Φᴴ))⁻¹ • (Φ * Φᴴ)

theorem projQ_mul_self {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (hdet : Φ.det = 0) :
    projQ Φ * Φ = Φ := by
  rw [projQ, Matrix.smul_mul, mul_mul_self_of_det_eq_zero hdet Φᴴ, smul_smul, trace_mul_comm Φᴴ Φ,
    inv_mul_cancel₀ (trace_mul_conjTranspose_ne_zero hΦ), one_smul]

theorem projQ_mul_projQ {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (hdet : Φ.det = 0) :
    projQ Φ * projQ Φ = projQ Φ := by
  have ht := trace_mul_conjTranspose_ne_zero hΦ
  have e : Φ * Φᴴ * (Φ * Φᴴ) = trace (Φ * Φᴴ) • (Φ * Φᴴ) := by
    rw [← Matrix.mul_assoc, mul_mul_self_of_det_eq_zero hdet Φᴴ, Matrix.smul_mul,
      trace_mul_comm Φᴴ Φ]
  rw [projQ, Matrix.smul_mul, Matrix.mul_smul, e, smul_smul, smul_smul, mul_assoc,
    inv_mul_cancel₀ ht, mul_one]

theorem star_projQ (Φ : EWBidoublet) : star (projQ Φ) = projQ Φ := by
  have hs : star (Φ * Φᴴ) = Φ * Φᴴ := by
    rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  have ht : star (trace (Φ * Φᴴ)) = trace (Φ * Φᴴ) := by
    rw [← trace_conjTranspose, ← star_eq_conjTranspose, hs]
  rw [projQ, star_smul, star_inv₀, ht, hs]

theorem trace_projQ {Φ : EWBidoublet} (hΦ : Φ ≠ 0) : trace (projQ Φ) = 1 := by
  rw [projQ, trace_smul, smul_eq_mul, inv_mul_cancel₀ (trace_mul_conjTranspose_ne_zero hΦ)]

theorem det_projQ {Φ : EWBidoublet} (hdet : Φ.det = 0) : (projQ Φ).det = 0 := by
  rw [projQ, det_smul, det_mul, hdet, zero_mul, mul_zero]

/-- The left partner of `U` at a rank-one `Φ`: `μ̄ • 1 + (μ − μ̄) • Q`, which is `μ` on the column
space of `Φ` and `μ̄` on its complement. -/
noncomputable def rankOneLeft (Φ : EWBidoublet) (μ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  star μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) + (μ - star μ) • projQ Φ

theorem rankOneLeft_mul {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (hdet : Φ.det = 0) (μ : ℂ) :
    rankOneLeft Φ μ * Φ = μ • Φ := by
  rw [rankOneLeft, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul,
    projQ_mul_self hΦ hdet, ← add_smul]
  ring_nf

theorem rankOneLeft_mem {Φ : EWBidoublet} (hΦ : Φ ≠ 0) (hdet : Φ.det = 0) {μ : ℂ}
    (hμ : star μ * μ = 1) : rankOneLeft Φ μ ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hQQ := projQ_mul_projQ hΦ hdet
  rw [mem_specialUnitaryGroup_iff, mem_unitaryGroup_iff']
  constructor
  · have hc : μ * star μ = 1 := by rw [mul_comm]; exact hμ
    have key : star (rankOneLeft Φ μ) * rankOneLeft Φ μ =
        (μ * star μ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        (μ * (μ - star μ) + (star μ - μ) * star μ + (star μ - μ) * (μ - star μ)) • projQ Φ := by
      rw [rankOneLeft, star_add, star_smul, star_smul, star_one, star_sub, star_star, star_projQ]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hQQ]
      module
    rw [key, hc, one_smul, show μ * (μ - star μ) + (star μ - μ) * star μ +
      (star μ - μ) * (μ - star μ) = 0 by ring, zero_smul, add_zero]
  · have htr : projQ Φ 0 0 + projQ Φ 1 1 = 1 := by
      simpa [trace, Fin.sum_univ_two] using trace_projQ hΦ
    have hd : projQ Φ 0 0 * projQ Φ 1 1 - projQ Φ 0 1 * projQ Φ 1 0 = 0 := by
      rw [← det_fin_two]; exact det_projQ hdet
    rw [rankOneLeft, det_fin_two]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_apply_eq,
      one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
      mul_zero, mul_one, zero_add]
    linear_combination (star μ * (μ - star μ)) * htr + (μ - star μ) ^ 2 * hd + hμ


/-- **`|μ| = 1`**: if `Φ U = μ • Φ` with `U` unitary and `Φ ≠ 0`, then `μ̄ μ = 1` — take the trace
of `(Φ U)(Φ U)ᴴ = Φ Φᴴ`. -/
theorem star_mul_self_of_mul_eq_smul {Φ : EWBidoublet} (hΦ : Φ ≠ 0) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU : U * star U = 1) {μ : ℂ} (h : Φ * U = μ • Φ) : star μ * μ = 1 := by
  have e1 : Φ * U * (Φ * U)ᴴ = Φ * Φᴴ := by
    rw [conjTranspose_mul, ← star_eq_conjTranspose U, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU,
      Matrix.one_mul]
  have e2 : Φ * U * (Φ * U)ᴴ = (μ * star μ) • (Φ * Φᴴ) := by
    rw [h, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have ht := congrArg trace (e2.symm.trans e1)
  rw [trace_smul, smul_eq_mul] at ht
  have := mul_right_cancel₀ (trace_mul_conjTranspose_ne_zero hΦ) (ht.trans (one_mul _).symm)
  rw [mul_comm]; exact this

/-- **At every `Φ ≠ 0` the embedding is onto**: invertible `Φ` by `U ↦ (Φ U Φ⁻¹, U)`, rank-one `Φ`
by `U ↦ (rankOneLeft Φ μ, U)`. -/
theorem toComm_surjective {Φ : EWBidoublet} (hΦ : Φ ≠ 0) : Function.Surjective (toComm Φ) := by
  intro U
  have hUc : (U : Matrix (Fin 2) (Fin 2) ℂ) * (Φᴴ * Φ) = Φᴴ * Φ * U := U.2
  by_cases hdet : Φ.det = 0
  · set μ := trace ((U : Matrix (Fin 2) (Fin 2) ℂ) * Φᴴ * Φ) / trace (Φ * Φᴴ)
    have hΦU : Φ * (U : Matrix (Fin 2) (Fin 2) ℂ) = μ • Φ := mul_eq_smul_of_det_eq_zero hΦ hdet hUc
    have hUU : (U : Matrix (Fin 2) (Fin 2) ℂ) * star (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp U.1.2).1
    have hμ := star_mul_self_of_mul_eq_smul hΦ hUU hΦU
    refine ⟨⟨(⟨rankOneLeft Φ μ, rankOneLeft_mem hΦ hdet hμ⟩, (U : SU2)), ?_⟩, rfl⟩
    rw [mem_stabilizer_stage2_iff]
    change rankOneLeft Φ μ * Φ = Φ * (U : Matrix (Fin 2) (Fin 2) ℂ)
    rw [rankOneLeft_mul hΦ hdet, hΦU]
  · have hu : IsUnit Φ.det := isUnit_iff_ne_zero.mpr hdet
    refine ⟨⟨(⟨Φ * (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ⁻¹, conj_mem_of_mem_commSU2 hu U.2⟩,
      (U : SU2)), ?_⟩, rfl⟩
    rw [mem_stabilizer_stage2_iff]
    change Φ * (U : Matrix (Fin 2) (Fin 2) ℂ) * Φ⁻¹ * Φ = Φ * U
    rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one]

/-- **THE ELECTROWEAK UNBROKEN GROUP AT EVERY NONZERO VACUUM IS THE COMMUTANT OF `Φᴴ Φ` IN
`SU(2)`**, by its right half. -/
noncomputable def stabilizerEquivCommSU2 {Φ : EWBidoublet} (hΦ : Φ ≠ 0) :
    MulAction.stabilizer Stage2Group Φ ≃* commSU2 (Φᴴ * Φ) :=
  MulEquiv.ofBijective (toComm Φ) ⟨toComm_injective hΦ, toComm_surjective hΦ⟩

/-- **When `Φᴴ Φ` is not a multiple of the identity, the unbroken group is the circle** — at every
nonzero `Φ`, rank one or two. -/
noncomputable def stabilizerEquivCircle {Φ : EWBidoublet} (hΦ : Φ ≠ 0)
    (hns : ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) : MulAction.stabilizer Stage2Group Φ ≃* unitary ℂ :=
  (stabilizerEquivCommSU2 hΦ).trans
    (commHermitianEquiv (isHermitian_conjTranspose_mul_self Φ) hns)

/-- **`SU(2)` and `U(1)` are not isomorphic**: every central element of `SU(2)` squares to one,
and `i ∈ U(1)` is central and does not. -/
theorem not_nonempty_SU2_equiv_circle : ¬ Nonempty (SU2 ≃* unitary ℂ) := by
  rintro ⟨φ⟩
  have hw : φ.symm unitI ∈ Subgroup.center SU2 := by
    refine Subgroup.mem_center_iff.mpr fun x => φ.injective ?_
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, mul_comm]
  have hww := mul_self_eq_one_of_mem_center hw
  have hzz : unitI * unitI = 1 := by
    have := congrArg φ hww
    rwa [map_mul, MulEquiv.apply_symm_apply, map_one] at this
  have h2 := congrArg (fun y : unitary ℂ => (y : ℂ)) hzz
  simp [unitI] at h2
  norm_num at h2

open scoped ComplexOrder in
/-- **A nonzero electroweak vacuum leaves `SU(2)` unbroken exactly when `Φᴴ Φ` is a multiple of
the identity.** -/
theorem nonempty_stabilizer_equiv_SU2_iff (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    Nonempty (MulAction.stabilizer Stage2Group Φ ≃* SU2) ↔ ∃ c : ℂ, Φᴴ * Φ = c • 1 := by
  constructor
  · rintro ⟨e⟩
    by_contra hns
    exact not_nonempty_SU2_equiv_circle ⟨e.symm.trans (stabilizerEquivCircle hΦ hns)⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hΦ (Matrix.conjTranspose_mul_self_eq_zero.mp (by simpa using hc))
    exact ⟨stabilizerEquivSU2 hc0 hc⟩

/-- **… and the circle exactly when it is not.** -/
theorem nonempty_stabilizer_equiv_circle_iff (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    Nonempty (MulAction.stabilizer Stage2Group Φ ≃* unitary ℂ) ↔
      ¬ ∃ c : ℂ, Φᴴ * Φ = c • 1 := by
  constructor
  · rintro ⟨e⟩ hs
    obtain ⟨f⟩ := (nonempty_stabilizer_equiv_SU2_iff Φ hΦ).mpr hs
    exact not_nonempty_SU2_equiv_circle ⟨f.symm.trans e⟩
  · intro hns
    exact ⟨stabilizerEquivCircle hΦ hns⟩

/-- **THE ELECTROWEAK STAGE, CLASSIFIED AT THE GROUP LEVEL**: a nonzero vacuum leaves `SU(2)` when
`Φᴴ Φ` is a multiple of the identity and the circle otherwise — two groups that are not
isomorphic. -/
theorem stabilizer_dichotomy (Φ : EWBidoublet) (hΦ : Φ ≠ 0) :
    ((∃ c : ℂ, Φᴴ * Φ = c • 1) ∧ Nonempty (MulAction.stabilizer Stage2Group Φ ≃* SU2)) ∨
    ((¬ ∃ c : ℂ, Φᴴ * Φ = c • 1) ∧
      Nonempty (MulAction.stabilizer Stage2Group Φ ≃* unitary ℂ)) := by
  by_cases hs : ∃ c : ℂ, Φᴴ * Φ = c • 1
  · exact Or.inl ⟨hs, (nonempty_stabilizer_equiv_SU2_iff Φ hΦ).mpr hs⟩
  · exact Or.inr ⟨hs, (nonempty_stabilizer_equiv_circle_iff Φ hΦ).mpr hs⟩

theorem vacKK_ne_zero {κ κ' : ℂ} (h : κ ≠ 0 ∨ κ' ≠ 0) : vacKK κ κ' ≠ 0 := by
  intro h0
  rcases h with h | h
  · exact h (by simpa [vacKK] using congrFun (congrFun h0 0) 0)
  · exact h (by simpa [vacKK] using congrFun (congrFun h0 1) 1)

theorem nonempty_stabilizer_vacKK_equiv_SU2_iff {κ κ' : ℂ} (h : κ ≠ 0 ∨ κ' ≠ 0) :
    Nonempty (MulAction.stabilizer Stage2Group (vacKK κ κ') ≃* SU2) ↔ ‖κ‖ = ‖κ'‖ := by
  rw [nonempty_stabilizer_equiv_SU2_iff _ (vacKK_ne_zero h)]
  exact exists_scalar_diagonal_iff κ κ'

/-- **THE NEUTRAL PLANE**: a nonzero `diag(κ, κ')` leaves the circle exactly when `|κ| ≠ |κ'|`, and
`SU(2)` otherwise. -/
theorem nonempty_stabilizer_vacKK_equiv_circle_iff {κ κ' : ℂ} (h : κ ≠ 0 ∨ κ' ≠ 0) :
    Nonempty (MulAction.stabilizer Stage2Group (vacKK κ κ') ≃* unitary ℂ) ↔ ‖κ‖ ≠ ‖κ'‖ := by
  rw [nonempty_stabilizer_equiv_circle_iff _ (vacKK_ne_zero h)]
  exact not_congr (exists_scalar_diagonal_iff κ κ')

/-- **At the estate's `vacEW` the unbroken subgroup of `SU(2)_L × SU(2)_R` is the circle.** -/
noncomputable def stabilizerVacEWEquivCircle :
    MulAction.stabilizer Stage2Group vacEW ≃* unitary ℂ :=
  stabilizerEquivCircle (fun h => not_scalar_vacEW ⟨0, by simp [h]⟩) not_scalar_vacEW

end

end ElectroweakUnbrokenGroup
