/-
  PatiSalamChargeCentre.lean — the electric charge's one-parameter subgroup IS the centre of the
  unbroken `U(3)`. Carried through unit 199's `stabilizerPairEquivU3`, the gauge-group elements
  `expFull (t • qFull)` land on `e^{it} · 1` (`stabilizerPairEquivU3_charge`); the centre of `U(3)`
  is exactly the scalar matrices (`mem_center_iff_scalar`); and as `t` runs over `ℝ` the charge's
  image fills that centre exactly (`range_charge_eq_center`).

  SPINE link L15 (Higgs sector, PARTIAL) — the group-level form of unit 184's
  `PatiSalamGoldstoneDirections.jointStabEquivU3_qFull` (the charge is the centre of the unbroken
  ALGEBRA `u(3)`), which unit 199's NOT list named as not proved. Hardening unit 200, 2026-09-25.

  WHAT IS PROVED.
  (1) `expFull_charge_fst`: the `SU(4)` component of `expFull (t • qFull)` is
      `diag(e^{it}, e^{it}, e^{it}, e^{−3it})` — `exp` of the diagonal `t • blGen`, entry by entry
      (`Matrix.exp_diagonal`).
  (2) `stabilizerPairEquivU3_charge`: its image in `U(3)` is `e^{it} · 1`.
  (3) **`mem_center_iff_scalar`: a `3 × 3` unitary matrix is central in `U(3)` if and only if it is
      a scalar.** A central `U` commutes with the sign flips `signAt k = diag(±1)`, which clears
      every off-diagonal entry, and with the transpositions `swap01` and `swap12`, which equalise
      the diagonal; scalars are central.
  (4) **`range_charge_eq_center`: the set `{stabilizerPairEquivU3 (expFull (t • qFull)) | t ∈ ℝ}` is
      the centre of `U(3)`.** One inclusion is (2) with (3); for the other, a central unitary is
      `z · 1` with `|z| = 1`, and `t = arg z` gives `e^{it} = z` (`Complex.norm_mul_exp_arg_mul_I`).

  NOT PROVED, said exactly.
  • The charge's SCALE. `qFull` is `6i · Q` (`PatiSalamTwoStageStabiliser`'s header, item (3)), so
    the `t` here is a multiple of the physical phase; the theorem is about the subgroup, which a
    rescaling of `t` does not change.
  • The rest of the splitting. `U(3) = (SU(3) × U(1)) ⧸ ℤ₃`: the `U(1)` — the centre — is now the
    charge's subgroup; that `SU(3)_c` is the determinant-one part, and the quotient by `ℤ₃`, are not
    written.
    ⚠ 25 September 2026 (hardening unit 201): written in `PatiSalamUnbrokenSplit` —
    `PatiSalamUnbrokenSplit.unbrokenEquiv` identifies `(SU(3) × U(1)) ⧸ K` with the stabiliser of
    both vacua, `K` cyclic of order three, the `SU(3)` factor acting on colour only. Kept as
    written (`ERRATUM 94`).
  • Topology: `stabilizerPairEquivU3` is an isomorphism of abstract groups (unit 199's NOT list).
  • The vacua are still chosen (`ASSUMPTIONS_LEDGER` 60); no potential, no masses.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). None beyond the types: `expFull_charge_fst`,
  `charge_mem`, `stabilizerPairEquivU3_charge` take `t : ℝ`; `mem_center_iff_scalar` takes
  `U : U(3)`.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 12 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The pinned Mathlib has the centre of the matrix RING
  (`Matrix.center_eq_range`) and of `GL(n)` (`Matrix.GeneralLinearGroup.center_eq_range_scalar`),
  and no statement about the centre of the unitary group (its sources searched for `center` with
  `unitary`), so (3) is proved here.

  0 sorry. 0 new axioms. `#print axioms` on all 12 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamStabiliserGroup

open Matrix NormedSpace PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamTwoStageStabiliser SkewAdjointExponential PatiSalamRightSector TracelessSkewDimension
  PatiSalamStabiliserGroup

namespace PatiSalamChargeCentre

theorem real_smul_diagonal (t : ℝ) (v : Fin 4 → ℂ) :
    t • diagonal v = diagonal (fun i => (t : ℂ) * v i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [diagonal_apply_eq, Complex.real_smul]
  · simp [diagonal_apply_ne _ h]

/-- The `SU(4)` component of the charge's one-parameter subgroup: `exp (t • blGen)`,
`blGen = diag(i, i, i, −3i)`, is `diag(e^{it}, e^{it}, e^{it}, e^{−3it})`. -/
theorem expFull_charge_fst (t : ℝ) :
    ((expFull (t • qFull)).1 : Matrix (Fin 4) (Fin 4) ℂ)
      = diagonal (fun i =>
          Complex.exp (t * ![Complex.I, Complex.I, Complex.I, -3 * Complex.I] i)) := by
  simp only [expFull, Prod.smul_fst, expSU_val, coe_smul_traceless, qFull, blT]
  rw [blGen, real_smul_diagonal, exp_diagonal, Pi.exp_def, ← Complex.exp_eq_exp_ℂ]

/-- The charge's one-parameter subgroup fixes both vacua (unit 191's `expFull_mem_stabilizer`). -/
theorem charge_mem (t : ℝ) : expFull (t • qFull) ∈ MulAction.stabilizer FullGroup (vac, vacEW) :=
  expFull_mem_stabilizer qFull qFull_mem_jointStab t

/-- **In the unbroken `U(3)` the charge's one-parameter subgroup is `t ↦ e^{it} · 1`.** -/
theorem stabilizerPairEquivU3_charge (t : ℝ) :
    ((stabilizerPairEquivU3 ⟨expFull (t • qFull), charge_mem t⟩ : GroupU3)
        : Matrix (Fin 3) (Fin 3) ℂ) = Complex.exp (t * Complex.I) • 1 := by
  rw [stabilizerPairEquivU3_apply]
  change ((expFull (t • qFull)).1 : Matrix (Fin 4) (Fin 4) ℂ).submatrix Fin.castSucc Fin.castSucc
    = _
  rw [expFull_charge_fst]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `diag(±1)` with `-1` at `k`. -/
noncomputable def signAt (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  diagonal (fun i => if i = k then -1 else 1)

theorem signAt_mem (k : Fin 3) : signAt k ∈ unitaryGroup (Fin 3) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, signAt, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1; ext i; by_cases h : i = k <;> simp [h]

/-- The transposition of coordinates `0` and `1`. -/
def swap01 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 1, 0, 0; 0, 0, 1]
/-- The transposition of coordinates `1` and `2`. -/
def swap12 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem swap01_mem : swap01 ∈ unitaryGroup (Fin 3) ℂ := by
  rw [mem_unitaryGroup_iff']
  ext i j; fin_cases i <;> fin_cases j <;> simp [swap01, Matrix.mul_apply, Fin.sum_univ_three]

theorem swap12_mem : swap12 ∈ unitaryGroup (Fin 3) ℂ := by
  rw [mem_unitaryGroup_iff']
  ext i j; fin_cases i <;> fin_cases j <;> simp [swap12, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The centre of `U(3)` is the unit scalars.** -/
theorem mem_center_iff_scalar (U : GroupU3) :
    U ∈ Subgroup.center GroupU3 ↔ ∃ z : ℂ, (U : Matrix (Fin 3) (Fin 3) ℂ) = z • 1 := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro h
    set M := (U : Matrix (Fin 3) (Fin 3) ℂ) with hM
    have hc : ∀ V : Matrix (Fin 3) (Fin 3) ℂ, V ∈ unitaryGroup (Fin 3) ℂ → V * M = M * V := by
      intro V hV
      exact congrArg Subtype.val (h ⟨V, hV⟩)
    have hoff : ∀ i j : Fin 3, i ≠ j → M i j = 0 := by
      intro i j hij
      have e := congrFun (congrFun (hc _ (signAt_mem i)) i) j
      rw [signAt, diagonal_mul, mul_diagonal] at e
      simp only [if_true, Ne.symm hij, if_false, neg_one_mul, mul_one] at e
      linear_combination (-1 / 2 : ℂ) * e
    have e01 := congrFun (congrFun (hc _ swap01_mem) 0) 1
    have e12 := congrFun (congrFun (hc _ swap12_mem) 1) 2
    simp [swap01, swap12, Matrix.mul_apply, Fin.sum_univ_three] at e01 e12
    refine ⟨M 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hoff, e01, e12]
  · rintro ⟨z, hz⟩ g
    apply Subtype.ext
    simp only [Submonoid.coe_mul, hz, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul]

/-- **The charge's one-parameter subgroup IS the centre of the unbroken `U(3)`.** -/
theorem range_charge_eq_center :
    Set.range (fun t : ℝ => stabilizerPairEquivU3 ⟨expFull (t • qFull), charge_mem t⟩)
      = (Subgroup.center GroupU3 : Set GroupU3) := by
  ext U
  simp only [Set.mem_range, SetLike.mem_coe]
  constructor
  · rintro ⟨t, rfl⟩
    exact (mem_center_iff_scalar _).mpr ⟨_, stabilizerPairEquivU3_charge t⟩
  · intro hU
    obtain ⟨z, hz⟩ := (mem_center_iff_scalar U).mp hU
    have hu : star (U : Matrix (Fin 3) (Fin 3) ℂ) * U = 1 := mem_unitaryGroup_iff'.mp U.2
    rw [hz] at hu
    have hz1 : star z * z = 1 := by
      have e := congrFun (congrFun hu 0) 0
      simpa [Matrix.mul_apply, Matrix.one_apply] using e
    have hn : ‖z‖ = 1 := by
      have h2 : Complex.normSq z = 1 := by
        have := Complex.mul_conj z
        rw [show (starRingEnd ℂ) z = star z from rfl, mul_comm, hz1] at this
        exact_mod_cast this.symm
      rw [Complex.normSq_eq_norm_sq] at h2
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) two_ne_zero).mp h2
    refine ⟨z.arg, Subtype.ext ?_⟩
    rw [stabilizerPairEquivU3_charge, hz]
    congr 1
    have := Complex.norm_mul_exp_arg_mul_I z
    rwa [hn, Complex.ofReal_one, one_mul] at this

end PatiSalamChargeCentre
