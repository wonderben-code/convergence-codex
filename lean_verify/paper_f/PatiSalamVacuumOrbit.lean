/-
  PatiSalamVacuumOrbit.lean — the unbroken group is `U(3)` for EVERY vacuum of the right shape, not
  only for the one the estate wrote down. Up to a positive scale, the `SU(4) × SU(2)_R` orbit of the
  first-stage vacuum `vac` is exactly the set of rank-one `4 × 2` matrices
  (`rank_eq_one_iff_mem_orbit`), so every rank-one first-stage vacuum has stabiliser `U(3)`
  (`nonempty_stabilizer_equiv_U3`). For both stages together, the orbit of `(vac, vacEW)` up to a
  positive scale on each field is exactly the ALIGNED pairs — two rank-one fields pointing the same
  way under `SU(2)_R` (`aligned_iff_mem_orbit`) — and every aligned pair has joint stabiliser `U(3)`
  (`nonempty_stabilizer_pair_equiv_U3`).

  SPINE link L15 (Higgs sector, PARTIAL); `ASSUMPTIONS_LEDGER` 60 says the two vacua are chosen, and
  units 199–201 computed the unbroken group at those two matrices only. This file removes that
  hypothesis down to its orbit type: what is chosen is that the first vacuum has rank one, that the
  second is aligned with it, and the two magnitudes; within that, nothing. Hardening unit 203,
  2026-09-25.

  WHAT IS PROVED.
  (1) **`exists_specialUnitary_col`**: for `n ≥ 2` (two distinct indices `j ≠ k`), every unit
      vector of `ℂⁿ` is the `k`-th column of a matrix in `SU(n)`. An orthonormal basis extending the
      vector (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) gives a unitary matrix
      (`exists_unitary_col`); a phase on column `j` makes the determinant `1`.
  (2) **`rank_eq_one_iff`**: over any field, `X.rank = 1` iff `X = u vᵀ` (`vecMulVec u v`) with
      `u ≠ 0` and `v ≠ 0`. Mathlib has `rank_vecMulVec_le`; the converse is written here.
  (3) **`rank_eq_one_iff_mem_orbit`**: a bidoublet `X` has rank one iff `X = r · (g • vac)` for some
      `g ∈ SU(4) × SU(2)_R` and real `r > 0` (`g • vac` is the pure tensor of `g`'s last `SU(4)`
      column and first `SU(2)` column, `smul_vac_eq`).
  (4) **`nonempty_stabilizer_equiv_U3`**: every rank-one bidoublet's stabiliser is isomorphic to
      `U(3)` — rescaling does not change a stabiliser (`stabilizer_smul_of_ne_zero`), a point of the
      orbit has a conjugate one (`MulAction.stabilizerEquivStabilizer`), and unit 199's
      `stabilizerVacEquivU3` does the rest.
  (5) **`aligned_iff_mem_orbit`**: `Aligned X Φ` — `X = u vᵀ`, `Φ = a (c · v̄)ᵀ` with `u, v, a, c`
      nonzero — iff `X = r · (g • (vac, vacEW)).1` and `Φ = s · (g • (vac, vacEW)).2` for one
      `g ∈ SU(4) × SU(2)_L × SU(2)_R` and reals `r, s > 0`. The conjugate appears because
      `SU(2)_R` acts on the first field by `Bᵀ` and on the second by `B⋆` on the right.
  (6) **`nonempty_stabilizer_pair_equiv_U3`**: every aligned pair's joint stabiliser is isomorphic
      to `U(3)`, through unit 199's `stabilizerPairEquivU3`.

  NOT PROVED, said exactly.
  • That the rank-one shape is NECESSARY: no theorem here says that a rank-two first-stage vacuum,
    or a non-aligned pair, has a stabiliser that is not `U(3)`. The orbit statements (3) and (5) do
    say such vacua are not gauge-equivalent to the estate's.
    ⚠ 25 September 2026 (hardening unit 204): the rank-two half is proved in
    `PatiSalamRankTwoVacuum` — `nonempty_stabilizer_equiv_U3_iff`: a nonzero first-stage vacuum's
    stabiliser is `U(3)` if and only if it has rank one. The non-aligned half stands. Kept as
    written (`ERRATUM 94`).
  • Why the vacuum should have rank one and be aligned — that is a potential's minimum, and there
    is no potential; nor are the two magnitudes `r`, `s` fixed.
  • Each `≃*` is of abstract groups, and it is conjugation by a chosen `g`: the isomorphism exists
    (`Nonempty`), and the copy of `U(3)` inside the gauge group moves with the vacuum.
  • The charge's scale, masses and gauge bosons, as in units 199–201.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `exists_unitary_col` takes a unit vector
  (`∑ ‖u i‖² = 1`); `exists_specialUnitary_col` also takes two distinct indices `j ≠ k`;
  `exists_pos_smul_unit` takes `u ≠ 0`; `col_ne_zero_of_mem_unitary` takes a unitary matrix;
  `stabilizer_smul_of_ne_zero` takes `c ≠ 0`, `stabilizer_pair_smul` `c ≠ 0` and `d ≠ 0`;
  `exists_smul_vac` takes `u ≠ 0` and `v ≠ 0`; the two stabiliser theorems take `X.rank = 1` and
  `Aligned X Φ`. `rank_eq_one_iff` is over any field with finitely many columns. Nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 19 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statement in the estate is the real one,
  `LovelockOrthonormalFrame.exists_isOrth_rows` (an orthonormal pair of `ℝⁿ` as two rows of an
  orthogonal matrix); unit 191's `PatiSalamGaugeAction.mem_range_jointOrbit_iff` is about orbit
  VELOCITIES, not orbits. The pinned Mathlib has `rank_vecMulVec_le` and no converse, and no
  statement that `SU(n)` moves a unit vector to any other.

  0 sorry. 0 new axioms. `#print axioms` on all 19 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamUnbrokenSplit

open Matrix

namespace PatiSalamVacuumOrbit

/-- A unit vector of `ℂⁿ` is a column of a unitary matrix. -/
theorem exists_unitary_col {n : ℕ} (u : Fin n → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) (k : Fin n) :
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ i, U i k = u i := by
  let v : Fin n → EuclideanSpace ℂ (Fin n) := fun _ => WithLp.toLp 2 u
  have hn : ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n))‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [hu]
  have hv : Orthonormal ℂ (({k} : Set (Fin n)).restrict v) :=
    ⟨fun _ => hn, fun a b hab => (hab (Subsingleton.elim a b)).elim⟩
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix b,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _, fun i => ?_⟩
  rw [Module.Basis.toMatrix_apply, hb k rfl]
  simp [v]


/-- For `n ≥ 2`: a unit vector of `ℂⁿ` is the `k`-th column of a SPECIAL unitary matrix — a phase
on a second column `j` corrects the determinant. -/
theorem exists_specialUnitary_col {n : ℕ} (u : Fin n → ℂ) (hu : ∑ i, ‖u i‖ ^ 2 = 1) {j k : Fin n}
    (hjk : j ≠ k) : ∃ A ∈ Matrix.specialUnitaryGroup (Fin n) ℂ, ∀ i, A i k = u i := by
  obtain ⟨U, hU, hcol⟩ := exists_unitary_col u hu k
  have hc : star U.det * U.det = 1 := Unitary.star_mul_self_of_mem (det_of_mem_unitary hU)
  let d : Fin n → ℂ := fun i => if i = j then star U.det else 1
  have hd : ∀ i, d i * star (d i) = 1 := by
    intro i
    by_cases hi : i = j
    · simp only [d, hi, if_true, star_star]
      exact hc
    · simp only [d, hi, if_false, star_one, mul_one]
  have hD : diagonal d ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, diagonal_conjTranspose,
      diagonal_mul_diagonal, ← diagonal_one]
    exact congrArg diagonal (funext hd)
  refine ⟨U * diagonal d, ?_, fun i => ?_⟩
  · rw [Matrix.mem_specialUnitaryGroup_iff]
    refine ⟨mul_mem hU hD, ?_⟩
    rw [det_mul, det_diagonal, Fintype.prod_ite_eq']
    rw [mul_comm]
    exact hc
  · rw [mul_diagonal, hcol]
    simp [d, hjk.symm]

theorem rank_eq_one_iff {m n K : Type*} [Fintype n] [Field K] (X : Matrix m n K) :
    X.rank = 1 ↔ ∃ u : m → K, ∃ v : n → K, u ≠ 0 ∧ v ≠ 0 ∧ X = vecMulVec u v := by
  classical
  constructor
  · intro h
    have h' := h
    rw [Matrix.rank] at h'
    obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp h'
    have hc : ∀ j, ∃ c : K, c • (w : m → K) = X *ᵥ Pi.single j 1 := fun j => by
      obtain ⟨c, hc⟩ := hw ⟨X *ᵥ Pi.single j 1, ⟨Pi.single j 1, rfl⟩⟩
      exact ⟨c, congrArg Subtype.val hc⟩
    choose c hcj using hc
    have hX : X = vecMulVec (w : m → K) c := by
      ext i j
      have := congrFun (hcj j) i
      rw [mulVec_single_one, Pi.smul_apply, smul_eq_mul] at this
      rw [vecMulVec_apply, col_apply] at *
      rw [← this, mul_comm]
    refine ⟨w, c, fun h0 => hw0 (Subtype.ext h0), fun h0 => ?_, hX⟩
    have h00 : vecMulVec (w : m → K) (0 : n → K) = 0 := by
      ext i j
      rw [vecMulVec_apply, Pi.zero_apply, mul_zero, zero_apply]
    rw [hX, h0, h00, Matrix.rank_zero] at h
    exact zero_ne_one h
  · rintro ⟨u, v, hu, hv, rfl⟩
    refine le_antisymm (rank_vecMulVec_le u v) ?_
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    rw [Matrix.rank, Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
    intro h0
    have hmem : vecMulVec u v *ᵥ Pi.single j 1 ∈ LinearMap.range (vecMulVec u v).mulVecLin :=
      ⟨Pi.single j 1, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    have := congrFun hmem i
    rw [mulVec_single_one, col_apply, vecMulVec_apply, Pi.zero_apply] at this
    exact mul_ne_zero hi hj this

/-- A nonzero vector of `ℂⁿ` is a positive multiple of a unit vector. -/
theorem exists_pos_smul_unit {n : ℕ} (u : Fin n → ℂ) (hu : u ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ w : Fin n → ℂ, ∑ i, ‖w i‖ ^ 2 = 1 ∧ u = (r : ℂ) • w := by
  set S := ∑ i, ‖u i‖ ^ 2 with hS_def
  have hS : 0 < S := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    exact Finset.sum_pos' (fun j _ => sq_nonneg ‖u j‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hr : 0 < √S := Real.sqrt_pos.mpr hS
  have hr' : ((√S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  refine ⟨√S, hr, ((√S : ℝ) : ℂ)⁻¹ • u, ?_, ?_⟩
  · have hn : ∀ i, ‖(((√S : ℝ) : ℂ)⁻¹ • u) i‖ ^ 2 = (√S ^ 2)⁻¹ * ‖u i‖ ^ 2 := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr, mul_pow, inv_pow]
    simp_rw [hn]
    rw [← Finset.mul_sum, ← hS_def, Real.sq_sqrt hS.le, inv_mul_cancel₀ hS.ne']
  · rw [smul_smul, mul_inv_cancel₀ hr', one_smul]

/-- A column of a unitary matrix is nonzero. -/
theorem col_ne_zero_of_mem_unitary {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) (k : Fin n) : (fun i => A i k) ≠ 0 := by
  intro h
  have h1 : (star A * A) k k = 1 := by
    rw [(Matrix.mem_unitaryGroup_iff').mp hA, one_apply_eq]
  rw [mul_apply] at h1
  have h0 : ∀ i, A i k = 0 := fun i => congrFun h i
  simp only [h0, mul_zero, Finset.sum_const_zero, zero_ne_one] at h1

open PatiSalamVacuumStabiliser PatiSalamGaugeAction PatiSalamStabiliserGroup

/-- `g • vac` is the pure tensor of `g`'s `SU(4)` last column and its `SU(2)` first column. -/
theorem smul_vac_eq (g : Stage1Group) :
    g • vac = vecMulVec (fun i => (g.1 : Matrix (Fin 4) (Fin 4) ℂ) i (Fin.last 3))
      (fun j => (g.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0) := by
  ext i j
  rw [stage1_smul_vac_apply, vecMulVec_apply]

/-- The stage-1 action commutes with complex scalars. -/
theorem stage1_smul_smul (g : Stage1Group) (c : ℂ) (X : Bidoublet) : g • (c • X) = c • (g • X) := by
  rw [stage1_smul_def, stage1_smul_def, stage1Act, stage1Act, Matrix.mul_smul, Matrix.smul_mul]

/-- Rescaling a bidoublet by a nonzero complex number does not change its stabiliser. -/
theorem stabilizer_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (X : Bidoublet) :
    MulAction.stabilizer Stage1Group (c • X) = MulAction.stabilizer Stage1Group X := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, stage1_smul_smul]
  exact (smul_right_injective _ hc).eq_iff

/-- Every pure tensor of two nonzero vectors is a positive multiple of a point of `vac`'s orbit. -/
theorem exists_smul_vac (u : Fin 4 → ℂ) (v : Fin 2 → ℂ) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Stage1Group, ∃ r : ℝ, 0 < r ∧ vecMulVec u v = (r : ℂ) • (g • vac) := by
  obtain ⟨r, hr, u', hu', rfl⟩ := exists_pos_smul_unit u hu
  obtain ⟨s, hs, v', hv', rfl⟩ := exists_pos_smul_unit v hv
  obtain ⟨A, hA, hAc⟩ := exists_specialUnitary_col u' hu' (j := 0) (k := Fin.last 3) (by decide)
  obtain ⟨B, hB, hBc⟩ := exists_specialUnitary_col v' hv' (j := 1) (k := 0) (by decide)
  refine ⟨(⟨A, hA⟩, ⟨B, hB⟩), r * s, mul_pos hr hs, ?_⟩
  rw [smul_vac_eq]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hAc, hBc,
    Complex.ofReal_mul]
  ring

/-- **The orbit of `vac`, up to positive scalars, is exactly the rank-one bidoublets.** -/
theorem rank_eq_one_iff_mem_orbit (X : Bidoublet) :
    X.rank = 1 ↔ ∃ g : Stage1Group, ∃ r : ℝ, 0 < r ∧ X = (r : ℂ) • (g • vac) := by
  rw [rank_eq_one_iff]
  constructor
  · rintro ⟨u, v, hu, hv, rfl⟩
    exact exists_smul_vac u v hu hv
  · rintro ⟨g, r, hr, rfl⟩
    refine ⟨(r : ℂ) • fun i => (g.1 : Matrix (Fin 4) (Fin 4) ℂ) i (Fin.last 3),
      fun j => (g.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0,
      smul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')
        (col_ne_zero_of_mem_unitary (Matrix.mem_specialUnitaryGroup_iff.mp g.1.2).1 _),
      col_ne_zero_of_mem_unitary (Matrix.mem_specialUnitaryGroup_iff.mp g.2.2).1 _, ?_⟩
    rw [smul_vac_eq]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, mul_assoc]

/-- **Every rank-one bidoublet has stabiliser `U(3)`** — not only `vac`. -/
theorem nonempty_stabilizer_equiv_U3 (X : Bidoublet) (hX : X.rank = 1) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* GroupU3) := by
  obtain ⟨g, r, hr, rfl⟩ := (rank_eq_one_iff_mem_orbit X).mp hX
  rw [stabilizer_smul_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne')]
  exact ⟨(MulAction.stabilizerEquivStabilizer rfl).symm.trans stabilizerVacEquivU3⟩

open ElectroweakVacuumStabiliser

/-- The two vacua are *aligned*: both nonzero pure tensors, with the electroweak field's `SU(2)_R`
factor the complex conjugate of the first field's, up to a nonzero scalar — the two fields point the
same way under `SU(2)_R`, which acts on the first by `Bᵀ` on the right and on the second by `B⋆`. -/
def Aligned (X : Bidoublet) (Φ : EWBidoublet) : Prop :=
  ∃ u : Fin 4 → ℂ, ∃ v : Fin 2 → ℂ, ∃ a : Fin 2 → ℂ, ∃ c : ℂ,
    u ≠ 0 ∧ v ≠ 0 ∧ a ≠ 0 ∧ c ≠ 0 ∧ X = vecMulVec u v ∧ Φ = vecMulVec a (c • star v)

theorem full_smul_fst (g : FullGroup) (p : Bidoublet × EWBidoublet) :
    (g • p).1 = ((g.1, g.2.2) : Stage1Group) • p.1 := rfl

theorem full_smul_snd (g : FullGroup) (p : Bidoublet × EWBidoublet) :
    (g • p).2 = ((g.2.1, g.2.2) : Stage2Group) • p.2 := rfl

/-- `g • vacEW` is the pure tensor of `g`'s first `SU(2)` column and the conjugate of the
second's. -/
theorem smul_vacEW_eq (g : Stage2Group) :
    g • vacEW = vecMulVec (fun i => (g.1 : Matrix (Fin 2) (Fin 2) ℂ) i 0)
      (star fun j => (g.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0) := by
  ext i j
  rw [stage2_smul_vacEW_apply, vecMulVec_apply, Pi.star_apply]

theorem stage2_smul_smul (g : Stage2Group) (c : ℂ) (Φ : EWBidoublet) :
    g • (c • Φ) = c • (g • Φ) := by
  rw [stage2_smul_def, stage2_smul_def, stage2Act, stage2Act, Matrix.mul_smul, Matrix.smul_mul]

/-- Rescaling either field by a nonzero complex number does not change the joint stabiliser. -/
theorem stabilizer_pair_smul {c d : ℂ} (hc : c ≠ 0) (hd : d ≠ 0) (p : Bidoublet × EWBidoublet) :
    MulAction.stabilizer FullGroup (c • p.1, d • p.2) = MulAction.stabilizer FullGroup p := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Prod.ext_iff, Prod.ext_iff,
    full_smul_fst, full_smul_snd, full_smul_fst, full_smul_snd, stage1_smul_smul,
    stage2_smul_smul, (smul_right_injective _ hc).eq_iff, (smul_right_injective _ hd).eq_iff]

/-- **The orbit of the two vacua, up to a positive scale on each field, is exactly the aligned
pairs.** -/
theorem aligned_iff_mem_orbit (X : Bidoublet) (Φ : EWBidoublet) :
    Aligned X Φ ↔ ∃ g : FullGroup, ∃ r s : ℝ, 0 < r ∧ 0 < s ∧
      X = (r : ℂ) • (g • (vac, vacEW)).1 ∧ Φ = (s : ℂ) • (g • (vac, vacEW)).2 := by
  constructor
  · rintro ⟨u, v, a, c, hu, hv, ha, hc, rfl, rfl⟩
    obtain ⟨r₁, hr₁, u', hu', rfl⟩ := exists_pos_smul_unit u hu
    obtain ⟨r₂, hr₂, v', hv', rfl⟩ := exists_pos_smul_unit v hv
    have ha' : (c * r₂) • a ≠ 0 :=
      smul_ne_zero (mul_ne_zero hc (Complex.ofReal_ne_zero.mpr hr₂.ne')) ha
    obtain ⟨s₁, hs₁, a', ha'', ha'e⟩ := exists_pos_smul_unit _ ha'
    obtain ⟨A, hA, hAc⟩ := exists_specialUnitary_col u' hu' (j := 0) (k := Fin.last 3) (by decide)
    obtain ⟨B, hB, hBc⟩ := exists_specialUnitary_col a' ha'' (j := 1) (k := 0) (by decide)
    obtain ⟨C, hC, hCc⟩ := exists_specialUnitary_col v' hv' (j := 1) (k := 0) (by decide)
    refine ⟨(⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩), r₁ * r₂, s₁, mul_pos hr₁ hr₂, hs₁, ?_, ?_⟩
    · rw [full_smul_fst, smul_vac_eq]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hAc, hCc,
        Complex.ofReal_mul]
      ring
    · rw [full_smul_snd, smul_vacEW_eq]
      ext i j
      have hij := congrFun ha'e i
      simp only [Pi.smul_apply, smul_eq_mul] at hij
      simp only [vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, Matrix.smul_apply,
        hBc, hCc, star_mul', Complex.star_def, Complex.conj_ofReal]
      rw [← mul_assoc (s₁ : ℂ), ← hij]
      ring
  · rintro ⟨g, r, s, hr, hs, rfl, rfl⟩
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.mp g.1.2).1
    have h2 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2.1.2).1
    have h3 := (Matrix.mem_specialUnitaryGroup_iff.mp g.2.2.2).1
    refine ⟨(r : ℂ) • fun i => (g.1 : Matrix (Fin 4) (Fin 4) ℂ) i (Fin.last 3),
      fun j => (g.2.2 : Matrix (Fin 2) (Fin 2) ℂ) j 0,
      (s : ℂ) • fun i => (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) i 0, 1,
      smul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') (col_ne_zero_of_mem_unitary h1 _),
      col_ne_zero_of_mem_unitary h3 _,
      smul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') (col_ne_zero_of_mem_unitary h2 _),
      one_ne_zero, ?_, ?_⟩
    · rw [full_smul_fst, smul_vac_eq]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, mul_assoc]
    · rw [full_smul_snd, smul_vacEW_eq, one_smul]
      ext i j
      simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, mul_assoc]

/-- **Every aligned pair of vacua has joint stabiliser `U(3)`** — not only `(vac, vacEW)`. -/
theorem nonempty_stabilizer_pair_equiv_U3 (X : Bidoublet) (Φ : EWBidoublet) (h : Aligned X Φ) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃* GroupU3) := by
  obtain ⟨g, r, s, hr, hs, rfl, rfl⟩ := (aligned_iff_mem_orbit X Φ).mp h
  rw [stabilizer_pair_smul (Complex.ofReal_ne_zero.mpr hr.ne')
    (Complex.ofReal_ne_zero.mpr hs.ne')]
  exact ⟨(MulAction.stabilizerEquivStabilizer rfl).symm.trans stabilizerPairEquivU3⟩

end PatiSalamVacuumOrbit
