/-
  PatiSalamRankTwoStabiliser.lean — WHAT A RANK-TWO FIRST-STAGE VACUUM LEAVES UNBROKEN. Unit 204
  proved that a rank-two vacuum of the `(4, 1, 2)` field does not leave `U(3)`, by an invariant,
  and said what its stabiliser is only by what it is not. This file says what it is. For every
  invertible `D`, the stabiliser of `vac2 · D` is isomorphic to `SU(2) × C(D Dᴴ)`, where `C(P)`
  (`commSU2 P`) is the subgroup of `SU(2)` of the elements commuting with `P`
  (`stabilizerVac2Equiv`); so, by unit 204's normal form, every rank-two vacuum leaves such a group
  (`nonempty_stabilizer_equiv_of_rank_eq_two`). When `D Dᴴ` is a multiple of the identity the
  second factor is all of `SU(2)`, and the stabiliser is `SU(2) × SU(2)`
  (`stabilizerVac2EquivOfScalar`; `vac2` itself, `stabilizerVac2OneEquiv`); when it is not, the
  second factor is commutative (`commSU2_mul_comm`).

  SPINE link L15 (Higgs sector, PARTIAL); `ASSUMPTIONS_LEDGER` 60. The model's chosen vacuum has
  rank one; this file concerns the vacua it does not choose, and answers the NOT-PROVED bullet
  of `PatiSalamRankTwoVacuum` "what the rank-two stabiliser IS as a group". Hardening unit 211,
  2026-09-25.

  WHAT IS PROVED.
  (1) Block matrices. `blk2 A N`, the matrix `diag(A, N)` in `M₄(ℂ)`: `det_blk2`, `blk2_mul`,
      `blk2_conjTranspose`, `blk2_one` and `blk2_inj`, from Mathlib's `fromBlocks` through
      `blk2_eq_reindex`; `blk2_mem`: `diag(A, N)` is in `SU(4)` when `A` and `N` are in `SU(2)`.
  (2) Every element is block-diagonal. For `(G, H)` fixing `vac2 · D`, with `D` invertible:
      `Hᵀ · conj(H) = 1` for unitary `H` (`transpose_mul_map_star`), so **`mul_vac2_of_mem`**:
      `G · vac2 = vac2 · N` with `N = D · conj(H) · D⁻¹` (`botBlk`). Its entries (unit 204's
      `mul_vac2_col0` and `mul_vac2_col1`, `vac2_mul_apply`) fix `G`'s last two columns; the
      orthogonality of `G`'s columns and `det N = 1` (`det_conj_mul`, `det_map_star`) empty the
      lower-left block (`eq_zero_of_two_eqs`); so **`eq_blk2_of_mem`**: `G = diag(A, N)`.
      `blocks_mem`: `A` and `N` are in `SU(2)`. **`botBlk_comm`**: `N` commutes with `D Dᴴ`,
      because `N · D Dᴴ · Nᴴ = D · conj(H) · conj(H)ᴴ · Dᴴ = D Dᴴ` and `N` is unitary.
  (3) The converse, and the isomorphism. For `N` in `SU(2)` commuting with `D Dᴴ`, `D⁻¹ N D` is
      unitary (`inv_conj_mem_unitary`), its conjugate is in `SU(2)` (`conjSU2_mem`), and
      `(diag(A, N), conj(D⁻¹ N D))` fixes `vac2 · D` for every `A` (`blk2_smul_eq`,
      `blk2_mul_vac2`). **`stabilizerVac2Equiv`**: `g ↦ (A, N)` is an isomorphism
      `stabilizer (vac2 · D) ≃* SU(2) × C(D Dᴴ)`, with inverse `stabOfBlocks`.
      **`nonempty_stabilizer_equiv_of_rank_eq_two`**: for every `X` of rank two there is an
      invertible `D` with `stabilizer X ≃* SU(2) × C(D Dᴴ)` — unit 204's
      `exists_smul_eq_vac2_mul`, then Mathlib's `stabilizerEquivStabilizer`.
  (4) The two cases. **`commSU2_eq_top_iff`**: every element of `SU(2)` commutes with `P` iff `P`
      is a multiple of the identity — `diag(i, −i)` (`diagI2`) forces `P` diagonal and the
      rotation `rot2` equal diagonal entries. Hence **`stabilizerVac2EquivOfScalar`**: if
      `D Dᴴ = c · 1`, the stabiliser is `SU(2) × SU(2)`; and **`stabilizerVac2OneEquiv`** for `vac2`
      itself. **`commSU2_mul_comm`**: if `P` is not a multiple of the identity, any two elements
      of `C(P)` commute — `mul_comm_of_comm_nonscalar`, from the entries of the two commutation
      equations (`comm_entries`, `mul_comm_of_entries`).

  NOT PROVED, said exactly.
  • What the commutative factor is. That `C(P)` is a circle, `U(1)`, when `P = D Dᴴ` is not a
    multiple of the identity, is not proved here; nor that `SU(2) × SU(2)` and `SU(2) × C(P)` are
    not isomorphic. This file alone does not show that the two cases are different groups.
  • The case split in terms of `X`: which rank-two `X` have a `D` with `D Dᴴ` a multiple of the
    identity is not stated in terms of `X` itself, and the `D` of (3) is not unique.
  • Each `≃*` is of abstract groups; no topology is put on either side here.
  • Why a vacuum should have rank two, or one: that is a potential's minimum, and there is no
    potential; nor are the magnitudes fixed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `IsUnit D.det` is taken by `mul_vac2_of_mem`,
  `det_conj_mul`, `det_inv_conj`, `eq_blk2_of_mem`, `blocks_mem`, `botBlk_comm`,
  `inv_conj_mem_unitary`, `conjSU2_mem`, `blk2_smul_eq`, `stabOfBlocks`, `stabilizerVac2Equiv` and
  `stabilizerVac2EquivOfScalar`; stabiliser membership by `mul_vac2_of_mem`, `eq_blk2_of_mem`,
  `blocks_mem` and `botBlk_comm`; commutation with `D Dᴴ` by `inv_conj_mem_unitary`,
  `conjSU2_mem` and `blk2_smul_eq`; `D Dᴴ = c • 1` by `stabilizerVac2EquivOfScalar`; that `P` is
  not a multiple of the identity by `mul_comm_of_comm_nonscalar` and `commSU2_mul_comm`;
  `X.rank = 2` by `nonempty_stabilizer_equiv_of_rank_eq_two`. The rest take unitarity or
  membership of `SU(2)` (`transpose_mul_map_star`, `star_mul_comm_of_mul_comm`,
  `map_star_mem_unitary`, `blk2_mem`), a matrix equation (`eq_zero_of_two_eqs`, `blk2_inj`,
  `topBlk_blk2`, `comm_entries`, `mul_comm_of_entries`), or nothing.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 44 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list. One was taken, `ofBlocks` (`FieldBlockProduct`), and was renamed `stabOfBlocks` before
  writing. The nearest statements: unit 204's `mul_vac2_col0` and `mul_vac2_col1`, used here in
  place of a combined lemma; `BlockGrading.diag_mul_diag`, the `fromBlocks` product that
  `blk2_mul` reindexes; unit 204's `eq_of_mem_stabilizer_of_mul_self`, which found the block form
  of the stabiliser's elements of square one, and which (2) gives for every element.

  0 sorry. 0 new axioms. `#print axioms` on all 44 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamRankTwoVacuum
set_option linter.mathlibStandardSet true

open Matrix

namespace PatiSalamRankTwoStabiliser

open PatiSalamVacuumStabiliser PatiSalamGaugeAction PatiSalamStabiliserGroup PatiSalamRankTwoVacuum

/-- `diag(A, N)` in `M₄(ℂ)`, from two `2 × 2` blocks. -/
def blk2 (A N : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, N 0 0, N 0 1; 0, 0, N 1 0, N 1 1]

theorem blk2_eq_reindex (A N : Matrix (Fin 2) (Fin 2) ℂ) :
    blk2 A N = reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 N) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem det_blk2 (A N : Matrix (Fin 2) (Fin 2) ℂ) : (blk2 A N).det = A.det * N.det := by
  rw [blk2_eq_reindex, det_reindex_self, det_fromBlocks_zero₂₁]

theorem blk2_mul (A N A' N' : Matrix (Fin 2) (Fin 2) ℂ) :
    blk2 A N * blk2 A' N' = blk2 (A * A') (N * N') := by
  rw [blk2_eq_reindex, blk2_eq_reindex, blk2_eq_reindex, reindex_apply, reindex_apply,
    reindex_apply, submatrix_mul_equiv, fromBlocks_multiply]
  simp

theorem blk2_conjTranspose (A N : Matrix (Fin 2) (Fin 2) ℂ) : (blk2 A N)ᴴ = blk2 Aᴴ Nᴴ := by
  rw [blk2_eq_reindex, blk2_eq_reindex, conjTranspose_reindex, fromBlocks_conjTranspose]
  simp

theorem blk2_one : blk2 1 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- For a unitary `H`, `Hᵀ * conj H = 1`. -/
theorem transpose_mul_map_star {H : Matrix (Fin 2) (Fin 2) ℂ}
    (hH : H ∈ unitaryGroup (Fin 2) ℂ) :
    Hᵀ * H.map star = 1 := by
  have h := (Matrix.mem_unitaryGroup_iff').mp hH
  have h' := congrArg transpose h
  rw [transpose_mul, transpose_one, star_eq_conjTranspose, conjTranspose] at h'
  rwa [← transpose_map, transpose_transpose] at h'

/-- **The stabiliser equation, solved for `g.1 * vac2`.** -/
theorem mul_vac2_of_mem {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (g : Stage1Group)
    (hg : g ∈ MulAction.stabilizer Stage1Group (vac2 * D)) :
    (g.1 : Matrix (Fin 4) (Fin 4) ℂ) * vac2
      = vac2 * (D * (g.2 : Matrix (Fin 2) (Fin 2) ℂ).map star * D⁻¹) := by
  have h := MulAction.mem_stabilizer_iff.mp hg
  rw [stage1_smul_def, stage1Act] at h
  have hH := transpose_mul_map_star (mem_specialUnitaryGroup_iff.mp g.2.2).1
  set G := (g.1 : Matrix (Fin 4) (Fin 4) ℂ)
  set H := (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  calc G * vac2 = G * vac2 * (D * (Hᵀ * H.map star) * D⁻¹) := by
        rw [hH, Matrix.mul_one, Matrix.mul_nonsing_inv D hD, Matrix.mul_one]
    _ = G * (vac2 * D) * Hᵀ * H.map star * D⁻¹ := by simp only [Matrix.mul_assoc]
    _ = vac2 * (D * H.map star * D⁻¹) := by rw [h]; simp only [Matrix.mul_assoc]

theorem vac2_mul_apply (N : Matrix (Fin 2) (Fin 2) ℂ) (i : Fin 4) (j : Fin 2) :
    (vac2 * N) i j = if i = 2 then N 0 j else if i = 3 then N 1 j else 0 := by
  fin_cases i <;> simp [vac2, mul_apply, single_apply]

theorem det_conj_mul {D M : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    (D * M * D⁻¹).det = M.det := by
  rw [det_mul, det_mul, det_nonsing_inv, mul_comm D.det M.det, mul_assoc,
    Ring.mul_inverse_cancel _ hD, mul_one]

theorem det_map_star (H : Matrix (Fin 2) (Fin 2) ℂ) : (H.map star).det = star H.det := by
  rw [det_fin_two, det_fin_two]
  simp [star_sub, star_mul']

/-- Two linear equations with an invertible coefficient matrix have only the zero solution. -/
theorem eq_zero_of_two_eqs {a b n00 n01 n10 n11 : ℂ} (hd : n00 * n11 - n01 * n10 ≠ 0)
    (h1 : a * n00 + b * n10 = 0) (h2 : a * n01 + b * n11 = 0) : a = 0 ∧ b = 0 := by
  have ha : a * (n00 * n11 - n01 * n10) = 0 := by linear_combination n11 * h1 - n10 * h2
  have hb : b * (n00 * n11 - n01 * n10) = 0 := by linear_combination n00 * h2 - n01 * h1
  exact ⟨(mul_eq_zero.mp ha).resolve_right hd, (mul_eq_zero.mp hb).resolve_right hd⟩

/-- **A stabiliser element is block-diagonal**: `g.1 = diag(A, D · conj(g.2) · D⁻¹)`. -/
theorem eq_blk2_of_mem {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (g : Stage1Group)
    (hg : g ∈ MulAction.stabilizer Stage1Group (vac2 * D)) :
    (g.1 : Matrix (Fin 4) (Fin 4) ℂ) = blk2 !![(g.1 : Matrix (Fin 4) (Fin 4) ℂ) 0 0,
      (g.1 : Matrix (Fin 4) (Fin 4) ℂ) 0 1; (g.1 : Matrix (Fin 4) (Fin 4) ℂ) 1 0,
      (g.1 : Matrix (Fin 4) (Fin 4) ℂ) 1 1]
      (D * (g.2 : Matrix (Fin 2) (Fin 2) ℂ).map star * D⁻¹) := by
  have h := mul_vac2_of_mem hD g hg
  have hNdet : (D * (g.2 : Matrix (Fin 2) (Fin 2) ℂ).map star * D⁻¹).det = 1 := by
    rw [det_conj_mul hD, det_map_star, (mem_specialUnitaryGroup_iff.mp g.2.2).2, star_one]
  have hU := (Matrix.mem_unitaryGroup_iff').mp (mem_specialUnitaryGroup_iff.mp g.1.2).1
  set G := (g.1 : Matrix (Fin 4) (Fin 4) ℂ) with hG
  set N := D * (g.2 : Matrix (Fin 2) (Fin 2) ℂ).map star * D⁻¹ with hN
  have e : ∀ i j, (G * vac2) i j = (vac2 * N) i j := fun i j => by rw [h]
  have e02 : G 0 2 = 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 0 0
  have e03 : G 0 3 = 0 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 0 1
  have e12 : G 1 2 = 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 1 0
  have e13 : G 1 3 = 0 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 1 1
  have e22 : G 2 2 = N 0 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 2 0
  have e23 : G 2 3 = N 0 1 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 2 1
  have e32 : G 3 2 = N 1 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 3 0
  have e33 : G 3 3 = N 1 1 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 3 1
  have hd : N 0 0 * N 1 1 - N 0 1 * N 1 0 ≠ 0 := by
    rw [← det_fin_two, hNdet]; exact one_ne_zero
  have low : ∀ j : Fin 4, j = 0 ∨ j = 1 → G 2 j = 0 ∧ G 3 j = 0 := by
    intro j hj
    have u2 := congrFun (congrFun hU j) 2
    have u3 := congrFun (congrFun hU j) 3
    have hj2 : j ≠ 2 := by rcases hj with rfl | rfl <;> decide
    have hj3 : j ≠ 3 := by rcases hj with rfl | rfl <;> decide
    simp only [mul_apply, star_apply, Fin.sum_univ_four, one_apply_ne hj2, one_apply_ne hj3, e02,
      e03, e12, e13, e22, e23, e32, e33, mul_zero, zero_add] at u2 u3
    obtain ⟨a0, b0⟩ := eq_zero_of_two_eqs hd u2 u3
    exact ⟨star_eq_zero.mp a0, star_eq_zero.mp b0⟩
  obtain ⟨l20, l30⟩ := low 0 (Or.inl rfl)
  obtain ⟨l21, l31⟩ := low 1 (Or.inr rfl)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, e02, e03, e12, e13, e22, e23, e32, e33, l20, l30, l21, l31]

abbrev SU2 := specialUnitaryGroup (Fin 2) ℂ

theorem star_mul_comm_of_mul_comm {M P : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ unitaryGroup (Fin 2) ℂ) (h : M * P = P * M) : star M * P = P * star M := by
  have h1 := (Matrix.mem_unitaryGroup_iff').mp hM
  have h2 := (Matrix.mem_unitaryGroup_iff).mp hM
  calc star M * P = star M * P * (M * star M) := by rw [h2, Matrix.mul_one]
    _ = star M * (M * P) * star M := by rw [h]; simp only [Matrix.mul_assoc]
    _ = P * star M := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]

/-- The elements of `SU(2)` commuting with `P`. -/
def commSU2 (P : Matrix (Fin 2) (Fin 2) ℂ) : Subgroup SU2 where
  carrier := {M | (M : Matrix (Fin 2) (Fin 2) ℂ) * P = P * M}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Submonoid.coe_mul] at *
    rw [Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    exact star_mul_comm_of_mul_comm (mem_specialUnitaryGroup_iff.mp a.2).1 ha

theorem blk2_inj {A N A' N' : Matrix (Fin 2) (Fin 2) ℂ} (h : blk2 A N = blk2 A' N') :
    A = A' ∧ N = N' := by
  have e := fun i j => congrFun (congrFun h i) j
  constructor
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [blk2] using e 0 0
    · simpa [blk2] using e 0 1
    · simpa [blk2] using e 1 0
    · simpa [blk2] using e 1 1
  · ext i j
    fin_cases i <;> fin_cases j
    · simpa [blk2] using e 2 2
    · simpa [blk2] using e 2 3
    · simpa [blk2] using e 3 2
    · simpa [blk2] using e 3 3

/-- The top-left block of `g.1`. -/
def topBlk (g : Stage1Group) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(g.1 : Matrix (Fin 4) (Fin 4) ℂ) 0 0, (g.1 : Matrix (Fin 4) (Fin 4) ℂ) 0 1;
    (g.1 : Matrix (Fin 4) (Fin 4) ℂ) 1 0, (g.1 : Matrix (Fin 4) (Fin 4) ℂ) 1 1]

/-- `D · conj(g.2) · D⁻¹`, which is the bottom-right block of `g.1` for `g` in the
stabiliser. -/
noncomputable def botBlk (D : Matrix (Fin 2) (Fin 2) ℂ) (g : Stage1Group) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  D * (g.2 : Matrix (Fin 2) (Fin 2) ℂ).map star * D⁻¹

theorem blocks_mem {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (g : Stage1Group)
    (hg : g ∈ MulAction.stabilizer Stage1Group (vac2 * D)) :
    topBlk g ∈ specialUnitaryGroup (Fin 2) ℂ ∧
      botBlk D g ∈ specialUnitaryGroup (Fin 2) ℂ := by
  have hb := eq_blk2_of_mem hD g hg
  have hN : (botBlk D g).det = 1 := by
    rw [botBlk, det_conj_mul hD, det_map_star, (mem_specialUnitaryGroup_iff.mp g.2.2).2, star_one]
  have hU := (Matrix.mem_unitaryGroup_iff').mp (mem_specialUnitaryGroup_iff.mp g.1.2).1
  have hdet := (mem_specialUnitaryGroup_iff.mp g.1.2).2
  rw [hb] at hU hdet
  rw [star_eq_conjTranspose, blk2_conjTranspose, blk2_mul, ← blk2_one] at hU
  obtain ⟨hA, hN'⟩ := blk2_inj hU
  rw [det_blk2] at hdet
  change (topBlk g).det * (botBlk D g).det = 1 at hdet
  rw [hN, mul_one] at hdet
  exact ⟨mem_specialUnitaryGroup_iff.mpr ⟨(Matrix.mem_unitaryGroup_iff').mpr hA, hdet⟩,
    mem_specialUnitaryGroup_iff.mpr ⟨(Matrix.mem_unitaryGroup_iff').mpr hN', hN⟩⟩

theorem map_star_conjTranspose (H : Matrix (Fin 2) (Fin 2) ℂ) : (H.map star)ᴴ = Hᵀ := by
  ext i j
  simp [conjTranspose_apply]

/-- **The bottom block commutes with `D Dᴴ`.** -/
theorem botBlk_comm {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (g : Stage1Group)
    (hg : g ∈ MulAction.stabilizer Stage1Group (vac2 * D)) :
    botBlk D g * (D * Dᴴ) = (D * Dᴴ) * botBlk D g := by
  have hH := transpose_mul_map_star (mem_specialUnitaryGroup_iff.mp g.2.2).1
  set H := (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  have hH' : H.map star * Hᵀ = 1 := mul_eq_one_comm.mp hH
  have hND : botBlk D g * D = D * H.map star := by
    rw [botBlk, Matrix.mul_assoc, Matrix.nonsing_inv_mul D hD, Matrix.mul_one]
  have hNU := (Matrix.mem_unitaryGroup_iff').mp
    (mem_specialUnitaryGroup_iff.mp (blocks_mem hD g hg).2).1
  rw [star_eq_conjTranspose] at hNU
  have key : botBlk D g * (D * Dᴴ) * (botBlk D g)ᴴ = D * Dᴴ := by
    calc botBlk D g * (D * Dᴴ) * (botBlk D g)ᴴ
        = (botBlk D g * D) * (botBlk D g * D)ᴴ := by
          rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = D * (H.map star * (H.map star)ᴴ) * Dᴴ := by
          rw [hND, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = D * Dᴴ := by rw [map_star_conjTranspose, hH', Matrix.mul_one]
  calc botBlk D g * (D * Dᴴ) = botBlk D g * (D * Dᴴ) * ((botBlk D g)ᴴ * botBlk D g) := by
        rw [hNU, Matrix.mul_one]
    _ = (D * Dᴴ) * botBlk D g := by rw [← Matrix.mul_assoc, key]

/-- If `N` is unitary and commutes with `D Dᴴ`, then `D⁻¹ N D` is unitary. -/
theorem inv_conj_mem_unitary {D N : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (hN : N ∈ unitaryGroup (Fin 2) ℂ) (hc : N * (D * Dᴴ) = (D * Dᴴ) * N) :
    D⁻¹ * N * D ∈ unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose]
  have hNN := (Matrix.mem_unitaryGroup_iff).mp hN
  rw [star_eq_conjTranspose] at hNN
  calc D⁻¹ * N * D * (D⁻¹ * N * D)ᴴ = D⁻¹ * (N * (D * Dᴴ)) * Nᴴ * (D⁻¹)ᴴ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = D⁻¹ * D * Dᴴ * (N * Nᴴ) * (D⁻¹)ᴴ := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = Dᴴ * (D⁻¹)ᴴ := by
        rw [hNN, Matrix.nonsing_inv_mul D hD, Matrix.one_mul, Matrix.mul_one]
    _ = (D⁻¹ * D)ᴴ := (conjTranspose_mul _ _).symm
    _ = 1 := by rw [Matrix.nonsing_inv_mul D hD, conjTranspose_one]

theorem map_star_mem_unitary {X : Matrix (Fin 2) (Fin 2) ℂ}
    (hX : X ∈ unitaryGroup (Fin 2) ℂ) :
    X.map star ∈ unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, map_star_conjTranspose]
  have h := (Matrix.mem_unitaryGroup_iff).mp hX
  rw [star_eq_conjTranspose] at h
  have e : X.map star * Xᵀ = (X * Xᴴ).map star := by
    ext i j
    simp [mul_apply, Fin.sum_univ_two, mul_comm]
  rw [e, h]
  ext i j
  simp [one_apply]

theorem det_inv_conj {D M : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    (D⁻¹ * M * D).det = M.det := by
  rw [det_mul, det_mul, det_nonsing_inv, mul_comm (Ring.inverse D.det) M.det, mul_assoc,
    Ring.inverse_mul_cancel _ hD, mul_one]

theorem blk2_mul_vac2 (A N : Matrix (Fin 2) (Fin 2) ℂ) : blk2 A N * vac2 = vac2 * N := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2, vac2, mul_apply, single_apply]

theorem blk2_mem {A N : Matrix (Fin 2) (Fin 2) ℂ} (hA : A ∈ specialUnitaryGroup (Fin 2) ℂ)
    (hN : N ∈ specialUnitaryGroup (Fin 2) ℂ) :
    blk2 A N ∈ specialUnitaryGroup (Fin 4) ℂ := by
  rw [mem_specialUnitaryGroup_iff] at hA hN ⊢
  refine ⟨(Matrix.mem_unitaryGroup_iff').mpr ?_, by rw [det_blk2, hA.2, hN.2, mul_one]⟩
  rw [star_eq_conjTranspose, blk2_conjTranspose, blk2_mul, ← star_eq_conjTranspose,
    ← star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff').mp hA.1,
    (Matrix.mem_unitaryGroup_iff').mp hN.1, blk2_one]

theorem conjSU2_mem {D N : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (hN : N ∈ specialUnitaryGroup (Fin 2) ℂ) (hc : N * (D * Dᴴ) = (D * Dᴴ) * N) :
    (D⁻¹ * N * D).map star ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff] at hN ⊢
  exact ⟨map_star_mem_unitary (inv_conj_mem_unitary hD hN.1 hc),
    by rw [det_map_star, det_inv_conj hD, hN.2, star_one]⟩

theorem map_star_transpose (X : Matrix (Fin 2) (Fin 2) ℂ) : (X.map star)ᵀ = Xᴴ := by
  ext i j
  simp [conjTranspose_apply]

/-- **The pair `(diag(A, N), conj(D⁻¹ N D))` fixes `vac2 * D`.** -/
theorem blk2_smul_eq {D A N : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (hN : N ∈ specialUnitaryGroup (Fin 2) ℂ) (hc : N * (D * Dᴴ) = (D * Dᴴ) * N) :
    blk2 A N * (vac2 * D) * ((D⁻¹ * N * D).map star)ᵀ = vac2 * D := by
  have hX := (Matrix.mem_unitaryGroup_iff).mp
    (inv_conj_mem_unitary hD (mem_specialUnitaryGroup_iff.mp hN).1 hc)
  rw [star_eq_conjTranspose] at hX
  rw [map_star_transpose, ← Matrix.mul_assoc, blk2_mul_vac2]
  calc vac2 * N * D * (D⁻¹ * N * D)ᴴ
        = vac2 * (D * (D⁻¹ * N * D)) * (D⁻¹ * N * D)ᴴ := by
        rw [← Matrix.mul_assoc D, ← Matrix.mul_assoc D, Matrix.mul_nonsing_inv D hD,
          Matrix.one_mul]
        simp only [Matrix.mul_assoc]
    _ = vac2 * D := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hX, Matrix.mul_one]

theorem map_star_mul (H H' : Matrix (Fin 2) (Fin 2) ℂ) :
    (H * H').map star = H.map star * H'.map star := by
  ext i j
  simp [mul_apply, Fin.sum_univ_two]

theorem topBlk_blk2 (g : Stage1Group) (A N : Matrix (Fin 2) (Fin 2) ℂ)
    (h : (g.1 : Matrix (Fin 4) (Fin 4) ℂ) = blk2 A N) : topBlk g = A := by
  rw [topBlk, h]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The inverse direction as an element of the stabiliser. -/
noncomputable def stabOfBlocks {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (A : SU2)
    (N : commSU2 (D * Dᴴ)) : MulAction.stabilizer Stage1Group (vac2 * D) :=
  ⟨(⟨blk2 A N.1, blk2_mem A.2 N.1.2⟩,
      ⟨(D⁻¹ * N.1 * D).map star, conjSU2_mem hD N.1.2 N.2⟩), by
    rw [MulAction.mem_stabilizer_iff, stage1_smul_def, stage1Act]
    exact blk2_smul_eq hD N.1.2 N.2⟩

/-- **THE RANK-TWO STABILISER**: for invertible `D`, the stabiliser of `vac2 * D` is
`SU(2) ×` the elements of `SU(2)` commuting with `D Dᴴ`, by
`g ↦ (A, D · conj(g.2) · D⁻¹)`. -/
noncomputable def stabilizerVac2Equiv {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    MulAction.stabilizer Stage1Group (vac2 * D) ≃* SU2 × commSU2 (D * Dᴴ) where
  toFun x := (⟨topBlk x, (blocks_mem hD x x.2).1⟩,
    ⟨⟨botBlk D x, (blocks_mem hD x x.2).2⟩, botBlk_comm hD x x.2⟩)
  invFun p := stabOfBlocks hD p.1 p.2
  left_inv x := by
    have hb := eq_blk2_of_mem hD x x.2
    refine Subtype.ext (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · exact hb.symm
    · change (D⁻¹ * botBlk D x * D).map star
        = ((x : Stage1Group).2 : Matrix (Fin 2) (Fin 2) ℂ)
      rw [botBlk, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul D hD, Matrix.mul_one,
        ← Matrix.mul_assoc, Matrix.nonsing_inv_mul D hD, Matrix.one_mul]
      ext i j
      simp
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext (Subtype.ext ?_))
    · exact topBlk_blk2 _ _ _ rfl
    · change D * ((D⁻¹ * p.2.1.1 * D).map star).map star * D⁻¹ = p.2.1.1
      have : ((D⁻¹ * p.2.1.1 * D).map star).map star = D⁻¹ * p.2.1.1 * D := by
        ext i j; simp only [map_apply, star_star]
      rw [this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv D hD,
        Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv D hD, Matrix.mul_one]
  map_mul' x y := by
    have hx := eq_blk2_of_mem hD x x.2
    have hy := eq_blk2_of_mem hD y y.2
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext (Subtype.ext ?_))
    · change topBlk (x * y : MulAction.stabilizer Stage1Group (vac2 * D)) = topBlk x * topBlk y
      refine topBlk_blk2 _ _ (botBlk D x * botBlk D y) ?_
      change (x : Stage1Group).1.1 * (y : Stage1Group).1.1 = _
      rw [hx, hy, blk2_mul]
      rfl
    · change D * ((x : Stage1Group).2.1 * (y : Stage1Group).2.1).map star * D⁻¹
        = botBlk D x * botBlk D y
      rw [map_star_mul, botBlk, botBlk]
      calc D * ((x : Stage1Group).2.1.map star * (y : Stage1Group).2.1.map star) * D⁻¹
          = D * (x : Stage1Group).2.1.map star * (D⁻¹ * D) * (y : Stage1Group).2.1.map star
            * D⁻¹ := by
            rw [Matrix.nonsing_inv_mul D hD, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = _ := by simp only [Matrix.mul_assoc]

/-- `diag(i, -i)` in `SU(2)`. -/
noncomputable def diagI2 : SU2 :=
  ⟨!![Complex.I, 0; 0, -Complex.I], mem_specialUnitaryGroup_iff.mpr
    ⟨(Matrix.mem_unitaryGroup_iff').mpr (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]),
     by simp [det_fin_two]⟩⟩

/-- The rotation `!![0, 1; -1, 0]` in `SU(2)`. -/
noncomputable def rot2 : SU2 :=
  ⟨!![0, 1; -1, 0], mem_specialUnitaryGroup_iff.mpr
    ⟨(Matrix.mem_unitaryGroup_iff').mpr (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]),
     by simp [det_fin_two]⟩⟩

/-- **`SU(2)` commutes with `P` exactly when `P` is scalar.** -/
theorem commSU2_eq_top_iff (P : Matrix (Fin 2) (Fin 2) ℂ) :
    commSU2 P = ⊤ ↔ ∃ c : ℂ, P = c • 1 := by
  constructor
  · intro h
    have h1 : (diagI2 : Matrix (Fin 2) (Fin 2) ℂ) * P = P * diagI2 :=
      (show diagI2 ∈ commSU2 P from h ▸ Subgroup.mem_top _)
    have h2 : (rot2 : Matrix (Fin 2) (Fin 2) ℂ) * P = P * rot2 :=
      (show rot2 ∈ commSU2 P from h ▸ Subgroup.mem_top _)
    have e01 := congrFun (congrFun h1 0) 1
    have e10 := congrFun (congrFun h1 1) 0
    have f01 := congrFun (congrFun h2 0) 1
    simp only [diagI2, Fin.isValue, mul_apply, of_apply, cons_val', cons_val_fin_one,
      cons_val_zero, Fin.sum_univ_two, cons_val_one, zero_mul, add_zero, mul_zero, mul_neg,
      zero_add, neg_mul, rot2, one_mul, mul_one] at e01 e10 f01
    refine ⟨P 0 0, ?_⟩
    have q01 : P 0 1 = 0 := by
      have : (2 * Complex.I) * P 0 1 = 0 := by linear_combination e01
      simpa [Complex.I_ne_zero] using this
    have q10 : P 1 0 = 0 := by
      have : (2 * Complex.I) * P 1 0 = 0 := by linear_combination -e10
      simpa [Complex.I_ne_zero] using this
    ext i j
    fin_cases i <;> fin_cases j <;> simp [q01, q10]
    linear_combination f01
  · rintro ⟨c, rfl⟩
    refine eq_top_iff.mpr fun M _ => ?_
    change (M : Matrix (Fin 2) (Fin 2) ℂ) * (c • 1) = (c • 1) * M
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

/-- **Equal singular values: the rank-two stabiliser is `SU(2) × SU(2)`.** When `D Dᴴ` is
scalar — `D` a multiple of a unitary — the second factor is all of `SU(2)`. -/
noncomputable def stabilizerVac2EquivOfScalar {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    {c : ℂ} (hc : D * Dᴴ = c • 1) :
    MulAction.stabilizer Stage1Group (vac2 * D) ≃* SU2 × SU2 :=
  (stabilizerVac2Equiv hD).trans (MulEquiv.prodCongr (MulEquiv.refl SU2)
    ((MulEquiv.subgroupCongr ((commSU2_eq_top_iff _).mpr ⟨c, hc⟩)).trans Subgroup.topEquiv))

/-- `vac2` itself: its stabiliser is `SU(2) × SU(2)`. -/
noncomputable def stabilizerVac2OneEquiv : MulAction.stabilizer Stage1Group vac2 ≃* SU2 × SU2 :=
  (MulEquiv.subgroupCongr (by rw [Matrix.mul_one])).trans
    (stabilizerVac2EquivOfScalar (D := (1 : Matrix (Fin 2) (Fin 2) ℂ)) (by simp) (c := 1)
      (by simp))

/-- The entries of `M * P = P * M` for `2 × 2` matrices. -/
theorem comm_entries {M P : Matrix (Fin 2) (Fin 2) ℂ} (h : M * P = P * M) :
    M 0 1 * P 1 0 = P 0 1 * M 1 0 ∧ (M 0 0 - M 1 1) * P 0 1 = M 0 1 * (P 0 0 - P 1 1) ∧
      (M 0 0 - M 1 1) * P 1 0 = M 1 0 * (P 0 0 - P 1 1) := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  simp only [mul_apply, Fin.sum_univ_two] at e00 e01 e10
  exact ⟨by linear_combination e00, by linear_combination e01, by linear_combination -e10⟩

theorem mul_comm_of_entries {M M' : Matrix (Fin 2) (Fin 2) ℂ}
    (e00 : M 0 1 * M' 1 0 - M' 0 1 * M 1 0 = 0)
    (e01 : M' 0 1 * (M 0 0 - M 1 1) - M 0 1 * (M' 0 0 - M' 1 1) = 0)
    (e10 : M 1 0 * (M' 0 0 - M' 1 1) - M' 1 0 * (M 0 0 - M 1 1) = 0) : M * M' = M' * M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one,
    Fin.isValue]
  · linear_combination e00
  · linear_combination e01
  · linear_combination e10
  · linear_combination -e00

/-- **Two matrices commuting with a non-scalar `2 × 2` matrix commute with each other.** -/
theorem mul_comm_of_comm_nonscalar {P M M' : Matrix (Fin 2) (Fin 2) ℂ}
    (hP : ¬ ∃ c : ℂ, P = c • 1) (hM : M * P = P * M) (hM' : M' * P = P * M') :
    M * M' = M' * M := by
  obtain ⟨a1, a2, a3⟩ := comm_entries hM
  obtain ⟨b1, b2, b3⟩ := comm_entries hM'
  by_cases h01 : P 0 1 = 0
  · by_cases h10 : P 1 0 = 0
    · have hd : P 0 0 - P 1 1 ≠ 0 := by
        intro hd
        refine hP ⟨P 0 0, ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h01, h10]
        linear_combination -hd
      have m01 : M 0 1 = 0 := by
        rw [h01, mul_zero] at a2; exact (mul_eq_zero.mp a2.symm).resolve_right hd
      have m10 : M 1 0 = 0 := by
        rw [h10, mul_zero] at a3; exact (mul_eq_zero.mp a3.symm).resolve_right hd
      have n01 : M' 0 1 = 0 := by
        rw [h01, mul_zero] at b2; exact (mul_eq_zero.mp b2.symm).resolve_right hd
      have n10 : M' 1 0 = 0 := by
        rw [h10, mul_zero] at b3; exact (mul_eq_zero.mp b3.symm).resolve_right hd
      exact mul_comm_of_entries (by rw [m01, n01]; ring) (by rw [m01, n01]; ring)
        (by rw [m10, n10]; ring)
    · have m01 : M 0 1 = 0 := by
        rw [h01, zero_mul] at a1; exact (mul_eq_zero.mp a1).resolve_right h10
      have n01 : M' 0 1 = 0 := by
        rw [h01, zero_mul] at b1; exact (mul_eq_zero.mp b1).resolve_right h10
      refine mul_comm_of_entries (by rw [m01, n01]; ring) (by rw [m01, n01]; ring) ?_
      refine (mul_eq_zero.mp ?_).resolve_left h10
      linear_combination (M 1 0) * b3 - (M' 1 0) * a3
  · refine mul_comm_of_entries ?_ ?_ ?_
    · refine (mul_eq_zero.mp ?_).resolve_left h01
      linear_combination (-M 0 1) * b1 + (M' 0 1) * a1
    · refine (mul_eq_zero.mp ?_).resolve_left h01
      linear_combination (M' 0 1) * a2 - (M 0 1) * b2
    · refine (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 2 h01)
      linear_combination (-P 0 1 * (M' 0 0 - M' 1 1)) * a1 + (P 0 1 * (M 0 0 - M 1 1)) * b1 +
        (M 0 1 * P 1 0) * b2 - (M' 0 1 * P 1 0) * a2

/-- **Away from the scalar case the second factor is commutative.** -/
theorem commSU2_mul_comm {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : ¬ ∃ c : ℂ, P = c • 1)
    (M M' : commSU2 P) : M * M' = M' * M :=
  Subtype.ext (Subtype.ext (mul_comm_of_comm_nonscalar hP M.2 M'.2))

/-- **Every rank-two first-stage vacuum** leaves `SU(2) × commSU2 (D Dᴴ)` for some invertible `D`:
unit 204's normal form `g • X = vac2 · D`, then conjugation by `g`. -/
theorem nonempty_stabilizer_equiv_of_rank_eq_two (X : Bidoublet) (hX : X.rank = 2) :
    ∃ D : Matrix (Fin 2) (Fin 2) ℂ, IsUnit D.det ∧
      Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × commSU2 (D * Dᴴ)) := by
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  exact ⟨D, hD, ⟨((MulAction.stabilizerEquivStabilizer rfl).trans
    (MulEquiv.subgroupCongr (congrArg (MulAction.stabilizer Stage1Group) hgX))).trans
    (stabilizerVac2Equiv hD)⟩⟩

end PatiSalamRankTwoStabiliser
