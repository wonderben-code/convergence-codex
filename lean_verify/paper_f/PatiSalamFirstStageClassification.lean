/-
  PatiSalamFirstStageClassification.lean — THE FIRST STAGE OF THE PATI–SALAM BREAKING, CLASSIFIED,
  AS ABSTRACT AND AS TOPOLOGICAL GROUPS. Unit 211 proved that a rank-two vacuum `vac2 · D` leaves
  `SU(2) × C(D Dᴴ)`, with `C(P)` the elements of `SU(2)` commuting with `P`: all of `SU(2)` when
  `D Dᴴ` is a multiple of the identity, commutative otherwise. This file finishes it. The
  commutative factor is the circle `U(1)` (`commHermitianEquiv`); `SU(2) × SU(2)` and `SU(2) × U(1)`
  are not isomorphic (`not_nonempty_SU2_SU2_equiv_SU2_circle`); and which one a rank-two `X` leaves
  is read off `X` itself — `SU(2) × SU(2)` exactly when `Xᴴ X` is a multiple of the identity, its
  two columns orthogonal and of equal length, and `SU(2) × U(1)` otherwise
  (`nonempty_stabilizer_equiv_SU2_SU2_iff`, `nonempty_stabilizer_equiv_SU2_circle_iff`). With unit
  204, every nonzero first-stage vacuum leaves exactly one of `U(3)`, `SU(2) × SU(2)` and
  `SU(2) × U(1)`, and no two of the three are isomorphic (`stabilizer_trichotomy`); and every
  identification holds as topological groups (`stabilizer_trichotomy_continuous`).

  SPINE link L15 (Higgs sector, PARTIAL); `ASSUMPTIONS_LEDGER` 60. The model's chosen vacuum has
  rank one; this file says what every other nonzero choice would leave. Hardening unit 212,
  2026-09-25.

  WHAT IS PROVED.
  (1) The circle. `comm_diagonal_iff`: for `f 0 ≠ f 1`, `M` commutes with `diagonal f` iff `M` is
      diagonal; `star_mul_self_of_lower_zero`, `diagConj2_comm_diagonal`; and
      **`commDiagonalEquiv`**: `M ↦ M₀₀` is an isomorphism from `C(diagonal f)` onto `U(1)`, with
      inverse `z ↦ diag(z, z̄)` — unit 199's `diagConj2`, and its `eq_diagConj2_of`.
  (2) Diagonalising. `conj_mem_SU2` and **`conjCommEquiv`**: conjugation by a unitary `U` carries
      `C(P)` onto `C(U⋆ P U)`. `star_mul_mul_eigenvectorUnitary`: Mathlib's spectral theorem for a
      Hermitian `P`, as `U⋆ P U = diagonal (eigenvalues)`; `eigenvalues_ne_of_not_scalar`: if `P` is
      not a multiple of the identity its two eigenvalues differ. So **`commHermitianEquiv`**:
      `C(P) ≃* U(1)` for every Hermitian `P` that is not a multiple of the identity, and
      **`stabilizerVac2EquivCircle`**: when `D Dᴴ` is not, `stabilizer (vac2 · D) ≃* SU(2) × U(1)`.
  (3) Different groups. **`mul_self_eq_one_of_mem_center`**: a central element of `SU(2)` is a
      scalar `c · 1` (unit 211's `commSU2_eq_top_iff`) with `c² = det = 1`, so it squares to one;
      `mem_center_fst`, `mem_center_snd`: a central element of a product has central components.
      **`not_nonempty_SU2_SU2_equiv_SU2_circle`**: `(1, i)` (`unitI`) is central in `SU(2) × U(1)`
      and squares to `(1, −1) ≠ 1`, while every central element of `SU(2) × SU(2)` squares to one.
  (4) Read off `X`. **`gram_smul`**: `(g • X)ᴴ (g • X) = conj(H) · Xᴴ X · Hᵀ`
      (`transpose_conjTranspose_eq_map_star`, `map_star_mul_transpose`), so whether the Gram matrix
      `Xᴴ X` is a multiple of the identity does not depend on the gauge (`gram_scalar_smul_iff`);
      `gram_vac2_mul`: for `vac2 · D` it is `Dᴴ D` (`vac2_conjTranspose_mul_self`);
      `scalar_conjTranspose_mul_iff`: for invertible `D`, `Dᴴ D` is a multiple of the identity iff
      `D Dᴴ` is; hence `scalar_iff_of_smul_eq`. With unit 204's normal form:
      **`nonempty_stabilizer_equiv_SU2_SU2_iff`** and **`nonempty_stabilizer_equiv_SU2_circle_iff`**
      for every `X` of rank two, with their `if` halves
      `nonempty_stabilizer_equiv_SU2_SU2_of_scalar` and
      `nonempty_stabilizer_equiv_SU2_circle_of_not_scalar`.
  (5) The first stage. **`not_nonempty_SU2_SU2_equiv_U3`** (`vac2`'s stabiliser, unit 204) and
      **`not_nonempty_SU2_circle_equiv_U3`** (the stabiliser of `vac2 · diag(1, 2)`:
      `diag12_isUnit`, `diag12_not_scalar`); and **`stabilizer_trichotomy`**: for `X ≠ 0`, rank one
      and `U(3)`, or rank two, `Xᴴ X` a multiple of the identity and `SU(2) × SU(2)`, or rank two,
      `Xᴴ X` not one and `SU(2) × U(1)`.
  (6) As topological groups. `continuousMulEquivOfCompact`: a continuous isomorphism out of a
      compact group into a Hausdorff one is an isomorphism of topological groups — unit 209's
      construction of `unbrokenContinuousEquiv`, stated once. `continuous_stage1_entry`,
      `continuous_topBlk`, `continuous_botBlk`, `continuous_stabilizerVac2Equiv`,
      `continuous_stabilizerVac2EquivOfScalar`, `continuous_stabilizerVac2EquivCircle`; so, the
      stabiliser being compact (unit 209's `compactSpace_stabilizer`),
      **`stabilizerVac2ContinuousEquiv`** (unit 211's isomorphism),
      **`stabilizerVac2ContinuousEquivOfScalar`** and **`stabilizerVac2ContinuousEquivCircle`**;
      with unit 209's `stabilizerContinuousEquiv`,
      **`nonempty_stabilizer_continuousEquiv_SU2_SU2_iff`**,
      **`nonempty_stabilizer_continuousEquiv_SU2_circle_iff`** and
      **`stabilizer_trichotomy_continuous`**, the rank-one case being unit 209's
      `nonempty_stabilizer_continuousEquiv_U3`.

  NOT PROVED, said exactly.
  • Which vacuum the model should have: that is a potential's minimum, and there is no potential.
    The trichotomy says what each choice leaves, not which is chosen; nor are the magnitudes fixed.
  • The second stage, the pair with the electroweak vacuum, beyond units 203–207.
    ⚠ 25 September 2026 (hardening unit 219, `paper_f/ElectroweakCustodial.lean`): the electroweak
    field ALONE is counted there — a nonzero bidoublet vacuum `Φ` leaves three generators of
    `su(2)_L ⊕ su(2)_R` unbroken when `Φᴴ Φ` is a multiple of the identity and one otherwise
    (`finrank_stabEWAt_dichotomy`), and those are the dimensions of the unbroken groups' Lie
    algebras in the sense matrix groups use (`matLieEW_stabilizer_eq`). The pair beyond units
    203–207, and the groups themselves, still are not classified; the bullet stands for them.
    ⚠ 25 September 2026 (hardening unit 220, `paper_f/ElectroweakUnbrokenGroup.lean`): the
    electroweak field's groups are classified there — `SU(2)` when `Φᴴ Φ` is a multiple of the
    identity and the circle otherwise, at every nonzero `Φ` (`stabilizer_dichotomy`). The pair
    beyond units 203–207 still is not; the bullet stands for it.
    ⚠ 25 September 2026 (hardening unit 221, `paper_f/PatiSalamJointCount.lean`): the pair
    `(vac, Φ)` is counted there at every `Φ` — nine or eight at `Φ ≠ 0`, by whether the columns of
    `Φ` are orthogonal (`finrank_jointStabAt_vac`) — and at orthogonal columns its group is `U(3)`
    (`nonempty_stabilizer_pair_continuousEquiv_U3_of_orthogonal`). The groups at the other pairs,
    and other first vacua, still are not; the bullet stands for them.
  • The Lie algebras of the two rank-two groups are not computed, and no smooth structure is put on
    any group (unit 209's reason: none in the pinned Mathlib for `SU(n)`).
    ⚠ 25 September 2026 (hardening unit 213): the unbroken SUBALGEBRAS are computed in
    `PatiSalamBrokenCount` — `su(2) × commT D` (`stabAtVac2Equiv`), of dimension six or four
    (`finrank_stabAt_trichotomy`). That they are these groups' Lie algebras stays unproved, for
    the same reason. Kept as written (`ERRATUM 94`).
    ⚠ 25 September 2026 (hardening unit 217, `paper_f/PatiSalamMatrixLie.lean`): proved in the sense
    matrix groups use — the Lie algebra of `Stab X`, the matrices `M` with `exp (t M)` in it for
    every real `t`, is exactly `stabAt X` (`mem_matLie_stabilizer_iff`), so these two groups' Lie
    algebras have dimension six and four. No smooth structure is put on any group. Kept as written
    (`ERRATUM 94`).

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `comm_diagonal_iff` and `commDiagonalEquiv` take
  `f 0 ≠ f 1`; `star_mul_self_of_lower_zero` takes `SU(2)` membership and `M 1 0 = 0`;
  `conj_mem_SU2` and `conjCommEquiv` take a unitary `U`, the first also `SU(2)` membership;
  `star_mul_mul_eigenvectorUnitary` takes `P.IsHermitian`, and `eigenvalues_ne_of_not_scalar` and
  `commHermitianEquiv` that and not being a multiple of the identity; `stabilizerVac2EquivCircle`,
  `continuous_stabilizerVac2EquivCircle` and `stabilizerVac2ContinuousEquivCircle` take
  `IsUnit D.det` and `D Dᴴ` not a multiple of the identity, and their three `OfScalar` counterparts
  `IsUnit D.det` and `D Dᴴ = c • 1`; `continuous_stabilizerVac2Equiv` and
  `stabilizerVac2ContinuousEquiv` take `IsUnit D.det`; `mul_self_eq_one_of_mem_center`,
  `mem_center_fst` and `mem_center_snd` take centrality; `map_star_mul_transpose` a unitary `H`;
  `scalar_conjTranspose_mul_iff` and `scalar_iff_of_smul_eq` take `IsUnit D.det`, the second also
  `g • X = vac2 * D`; the six rank-two theorems take `X.rank = 2`, the two `if` halves also the
  hypothesis on `Xᴴ X`; the two trichotomies take `X ≠ 0`; `continuousMulEquivOfCompact` takes a
  compact domain, a Hausdorff codomain and continuity. The rest take nothing.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 45 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements: unit 199's `diagConj2` API, used; unit 211's
  `transpose_mul_map_star`, of which `map_star_mul_transpose` is the other order; unit 204's
  `vac2_transpose_mul_self`, of which `vac2_conjTranspose_mul_self` is the conjugate-transpose form;
  unit 204's `nonempty_stabilizer_equiv_U3_iff`, which `stabilizer_trichotomy` extends; unit 209's
  `unbrokenContinuousEquiv`, whose construction `continuousMulEquivOfCompact` states once, and its
  `continuous_stage1_smul`, of which `continuous_stage1_entry` is the entrywise form for the group
  element. From Mathlib, `Matrix.IsHermitian.spectral_theorem`,
  `conjStarAlgAut_star_eigenvectorUnitary` and `Continuous.homeoOfEquivCompactToT2` are used;
  `Set.center_prod` is the set-level statement that `mem_center_fst` and `mem_center_snd` each take
  one direction of, for `Subgroup.center`, in one line.

  0 sorry. 0 new axioms. `#print axioms` on all 45 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamRankTwoStabiliser
import PatiSalamTopologicalCopies
set_option linter.mathlibStandardSet true

open Matrix

namespace PatiSalamFirstStageClassification

open PatiSalamVacuumStabiliser PatiSalamGaugeAction PatiSalamStabiliserGroup PatiSalamRankTwoVacuum
  PatiSalamRankTwoStabiliser PatiSalamTopologicalCopies

/-! ## 1. The commutant of a non-scalar diagonal matrix -/

/-- A `2 × 2` matrix commutes with `diagonal f`, `f 0 ≠ f 1`, iff it is diagonal. -/
theorem comm_diagonal_iff {f : Fin 2 → ℂ} (hf : f 0 ≠ f 1) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * diagonal f = diagonal f * M ↔ M 0 1 = 0 ∧ M 1 0 = 0 := by
  constructor
  · intro h
    have e01 := congrFun (congrFun h 0) 1
    have e10 := congrFun (congrFun h 1) 0
    simp only [mul_diagonal, diagonal_mul] at e01 e10
    have hf' : f 1 - f 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hf)
    refine ⟨?_, ?_⟩
    · have : M 0 1 * (f 1 - f 0) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hf'
    · have : M 1 0 * (f 1 - f 0) = 0 := by linear_combination -e10
      exact (mul_eq_zero.mp this).resolve_right hf'
  · rintro ⟨h01, h10⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_diagonal, diagonal_mul, h01, h10, mul_comm]

/-- The top-left entry of an element of `SU(2)` with a zero lower-left entry has modulus one. -/
theorem star_mul_self_of_lower_zero {M : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) (h10 : M 1 0 = 0) : star (M 0 0) * M 0 0 = 1 := by
  have hU := congrFun (congrFun ((Matrix.mem_unitaryGroup_iff').mp
    (mem_specialUnitaryGroup_iff.mp hM).1) 0) 0
  simp only [mul_apply, star_apply, Fin.sum_univ_two, h10, star_zero, mul_zero, add_zero,
    one_apply_eq] at hU
  exact hU

theorem diagConj2_comm_diagonal (d : ℂ) (f : Fin 2 → ℂ) :
    diagConj2 d * diagonal f = diagonal f * diagConj2 d := by
  simp only [diagConj2, diagonal_mul_diagonal, mul_comm]

/-- **`C(diagonal f)` is the circle.** For `f 0 ≠ f 1`, `M ↦ M₀₀` is an isomorphism from the
elements of `SU(2)` commuting with `diagonal f` onto `U(1)`, with inverse `z ↦ diag(z, z̄)`. -/
noncomputable def commDiagonalEquiv {f : Fin 2 → ℂ} (hf : f 0 ≠ f 1) :
    commSU2 (diagonal f) ≃* unitary ℂ where
  toFun M := ⟨(M : Matrix (Fin 2) (Fin 2) ℂ) 0 0, Unitary.mem_iff.mpr
    ⟨star_mul_self_of_lower_zero M.1.2 ((comm_diagonal_iff hf _).mp M.2).2,
     by rw [mul_comm]; exact star_mul_self_of_lower_zero M.1.2 ((comm_diagonal_iff hf _).mp M.2).2⟩⟩
  invFun z := ⟨⟨diagConj2 z, diagConj2_mem_specialUnitary (Unitary.star_mul_self_of_mem z.2)⟩,
    diagConj2_comm_diagonal _ _⟩
  left_inv M := by
    have h := (comm_diagonal_iff hf _).mp M.2
    refine Subtype.ext (Subtype.ext ?_)
    exact (eq_diagConj2_of M.1.2 (by rw [mul_comm]; exact star_mul_self_of_lower_zero M.1.2 h.2)
      rfl h.2).symm
  right_inv z := by
    refine Subtype.ext ?_
    simp [diagConj2]
  map_mul' M N := by
    have hM := (comm_diagonal_iff hf _).mp M.2
    refine Subtype.ext ?_
    change ((M : Matrix (Fin 2) (Fin 2) ℂ) * (N : Matrix (Fin 2) (Fin 2) ℂ)) 0 0
      = (M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * (N : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    simp [mul_apply, Fin.sum_univ_two, hM.1]

/-! ## 2. Conjugating by a unitary, and diagonalising a Hermitian `P` -/

theorem conj_mem_SU2 {U M : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ unitaryGroup (Fin 2) ℂ)
    (hM : M ∈ specialUnitaryGroup (Fin 2) ℂ) : star U * M * U ∈ specialUnitaryGroup (Fin 2) ℂ := by
  rw [mem_specialUnitaryGroup_iff] at hM ⊢
  refine ⟨Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hU) hM.1) hU, ?_⟩
  rw [det_mul, det_mul, hM.2, mul_one, ← det_mul, (Matrix.mem_unitaryGroup_iff').mp hU, det_one]

/-- **Conjugation by a unitary `U`** carries the elements of `SU(2)` commuting with `P` onto those
commuting with `U⋆ P U`. -/
noncomputable def conjCommEquiv {U : Matrix (Fin 2) (Fin 2) ℂ} (hU : U ∈ unitaryGroup (Fin 2) ℂ)
    (P : Matrix (Fin 2) (Fin 2) ℂ) : commSU2 P ≃* commSU2 (star U * P * U) where
  toFun M := ⟨⟨star U * M * U, conj_mem_SU2 hU M.1.2⟩, by
    have h1 := (Matrix.mem_unitaryGroup_iff).mp hU
    have hM : (M : Matrix (Fin 2) (Fin 2) ℂ) * P = P * M := M.2
    change star U * (M : Matrix (Fin 2) (Fin 2) ℂ) * U * (star U * P * U)
      = star U * P * U * (star U * (M : Matrix (Fin 2) (Fin 2) ℂ) * U)
    calc star U * (M : Matrix (Fin 2) (Fin 2) ℂ) * U * (star U * P * U)
        = star U * ((M : Matrix (Fin 2) (Fin 2) ℂ) * (U * star U) * P) * U := by
          simp only [Matrix.mul_assoc]
      _ = star U * (P * (U * star U) * M) * U := by rw [h1, Matrix.mul_one, Matrix.mul_one, hM]
      _ = _ := by simp only [Matrix.mul_assoc]⟩
  invFun M := ⟨⟨U * M * star U, by
      simpa only [star_star] using conj_mem_SU2 (Unitary.star_mem hU) M.1.2⟩, by
    have h2 := (Matrix.mem_unitaryGroup_iff').mp hU
    have h1 := (Matrix.mem_unitaryGroup_iff).mp hU
    have hM : (M : Matrix (Fin 2) (Fin 2) ℂ) * (star U * P * U) = (star U * P * U) * M := M.2
    change U * (M : Matrix (Fin 2) (Fin 2) ℂ) * star U * P = P * (U * M * star U)
    calc U * (M : Matrix (Fin 2) (Fin 2) ℂ) * star U * P
        = U * ((M : Matrix (Fin 2) (Fin 2) ℂ) * (star U * P * U)) * star U := by
          simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
      _ = U * ((star U * P * U) * M) * star U := by rw [hM]
      _ = (U * star U) * P * (U * M * star U) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.one_mul]⟩
  left_inv M := by
    have h2 := (Matrix.mem_unitaryGroup_iff').mp hU
    refine Subtype.ext (Subtype.ext ?_)
    change U * (star U * (M : Matrix (Fin 2) (Fin 2) ℂ) * U) * star U = M
    have h1 := (Matrix.mem_unitaryGroup_iff).mp hU
    calc U * (star U * (M : Matrix (Fin 2) (Fin 2) ℂ) * U) * star U
        = (U * star U) * M * (U * star U) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  right_inv M := by
    have h2 := (Matrix.mem_unitaryGroup_iff').mp hU
    refine Subtype.ext (Subtype.ext ?_)
    change star U * (U * (M : Matrix (Fin 2) (Fin 2) ℂ) * star U) * U = M
    calc star U * (U * (M : Matrix (Fin 2) (Fin 2) ℂ) * star U) * U
        = (star U * U) * M * (star U * U) := by simp only [Matrix.mul_assoc]
      _ = M := by rw [h2, Matrix.one_mul, Matrix.mul_one]
  map_mul' M N := by
    have h1 := (Matrix.mem_unitaryGroup_iff).mp hU
    refine Subtype.ext (Subtype.ext ?_)
    change star U * ((M : Matrix (Fin 2) (Fin 2) ℂ) * N) * U
      = star U * (M : Matrix (Fin 2) (Fin 2) ℂ) * U * (star U * (N : Matrix (Fin 2) (Fin 2) ℂ) * U)
    calc star U * ((M : Matrix (Fin 2) (Fin 2) ℂ) * N) * U
        = star U * ((M : Matrix (Fin 2) (Fin 2) ℂ) * (U * star U) * N) * U := by
          rw [h1, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

/-- The spectral theorem for a Hermitian `2 × 2` matrix, as `U⋆ P U = diagonal`. -/
theorem star_mul_mul_eigenvectorUnitary {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian) :
    star (hP.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) * P
      * (hP.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ)
      = diagonal (RCLike.ofReal ∘ hP.eigenvalues) := by
  have h := hP.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h
  exact h

/-- **A Hermitian `2 × 2` matrix that is not scalar has two different eigenvalues.** -/
theorem eigenvalues_ne_of_not_scalar {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian)
    (hns : ¬ ∃ c : ℂ, P = c • 1) :
    (RCLike.ofReal ∘ hP.eigenvalues : Fin 2 → ℂ) 0 ≠ (RCLike.ofReal ∘ hP.eigenvalues) 1 := by
  intro h
  apply hns
  refine ⟨(RCLike.ofReal ∘ hP.eigenvalues : Fin 2 → ℂ) 0, ?_⟩
  have hr : hP.eigenvalues 0 = hP.eigenvalues 1 := by
    simpa only [Function.comp_apply, RCLike.ofReal_inj] using h
  have hD : diagonal (RCLike.ofReal ∘ hP.eigenvalues : Fin 2 → ℂ)
      = (RCLike.ofReal ∘ hP.eigenvalues : Fin 2 → ℂ) 0 • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hr]
  have hs := hP.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, hD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2] at hs
  exact hs

/-- **The circle.** For Hermitian `P` not a multiple of the identity, the elements of `SU(2)`
commuting with `P` form a group isomorphic to `U(1)`. -/
noncomputable def commHermitianEquiv {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : P.IsHermitian)
    (hns : ¬ ∃ c : ℂ, P = c • 1) : commSU2 P ≃* unitary ℂ :=
  (conjCommEquiv hP.eigenvectorUnitary.2 P).trans
    ((MulEquiv.subgroupCongr (by rw [star_mul_mul_eigenvectorUnitary hP])).trans
      (commDiagonalEquiv (eigenvalues_ne_of_not_scalar hP hns)))

/-- **Unequal singular values: the rank-two stabiliser is `SU(2) × U(1)`.** -/
noncomputable def stabilizerVac2EquivCircle {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (hns : ¬ ∃ c : ℂ, D * Dᴴ = c • 1) :
    MulAction.stabilizer Stage1Group (vac2 * D) ≃* SU2 × unitary ℂ :=
  (stabilizerVac2Equiv hD).trans (MulEquiv.prodCongr (MulEquiv.refl SU2)
    (commHermitianEquiv (isHermitian_mul_conjTranspose_self D) hns))

/-! ## 3. The two cases are different groups -/

/-- A central element of `SU(2)` squares to one: it commutes with everything, so it is a scalar
`c · 1` (`commSU2_eq_top_iff`), and `c² = det = 1`. -/
theorem mul_self_eq_one_of_mem_center {g : SU2} (hg : g ∈ Subgroup.center SU2) : g * g = 1 := by
  have htop : commSU2 (g : Matrix (Fin 2) (Fin 2) ℂ) = ⊤ := by
    refine eq_top_iff.mpr fun M _ => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hg M)
  obtain ⟨c, hc⟩ := (commSU2_eq_top_iff _).mp htop
  have hdet := (mem_specialUnitaryGroup_iff.mp g.2).2
  rw [hc, det_smul, det_one, Fintype.card_fin, mul_one] at hdet
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℂ) * g = 1
  rw [hc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, ← sq, hdet, one_smul]

theorem mem_center_fst {G H : Type*} [Group G] [Group H] {x : G × H}
    (hx : x ∈ Subgroup.center (G × H)) : x.1 ∈ Subgroup.center G :=
  Subgroup.mem_center_iff.mpr fun g => congrArg Prod.fst (Subgroup.mem_center_iff.mp hx (g, 1))

theorem mem_center_snd {G H : Type*} [Group G] [Group H] {x : G × H}
    (hx : x ∈ Subgroup.center (G × H)) : x.2 ∈ Subgroup.center H :=
  Subgroup.mem_center_iff.mpr fun h => congrArg Prod.snd (Subgroup.mem_center_iff.mp hx (1, h))

/-- `i` as an element of `U(1)`. -/
noncomputable def unitI : unitary ℂ :=
  ⟨Complex.I, Unitary.mem_iff.mpr ⟨by simp, by simp⟩⟩

/-- **`SU(2) × SU(2)` and `SU(2) × U(1)` are not isomorphic**: every central element of the first
squares to one, and `(1, i)` is central in the second and squares to `(1, −1)`. -/
theorem not_nonempty_SU2_SU2_equiv_SU2_circle : ¬ Nonempty (SU2 × SU2 ≃* SU2 × unitary ℂ) := by
  rintro ⟨φ⟩
  set z : SU2 × unitary ℂ := (1, unitI)
  have hz : ∀ y : SU2 × unitary ℂ, y * z = z * y := fun y =>
    Prod.ext (by simp [z]) (mul_comm y.2 unitI)
  have hw : φ.symm z ∈ Subgroup.center (SU2 × SU2) := by
    refine Subgroup.mem_center_iff.mpr fun x => φ.injective ?_
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz]
  have hww : φ.symm z * φ.symm z = 1 :=
    Prod.ext (mul_self_eq_one_of_mem_center (mem_center_fst hw))
      (mul_self_eq_one_of_mem_center (mem_center_snd hw))
  have hzz : z * z = 1 := by
    have := congrArg φ hww
    rwa [map_mul, MulEquiv.apply_symm_apply, map_one] at this
  have h2 := congrArg (fun y : SU2 × unitary ℂ => ((y.2 : unitary ℂ) : ℂ)) hzz
  simp [z, unitI] at h2
  norm_num at h2

/-! ## 4. The case split, read off `X` -/

theorem transpose_conjTranspose_eq_map_star (H : Matrix (Fin 2) (Fin 2) ℂ) :
    (Hᵀ)ᴴ = H.map star := by
  ext i j
  simp [conjTranspose_apply]

theorem map_star_mul_transpose {H : Matrix (Fin 2) (Fin 2) ℂ} (hH : H ∈ unitaryGroup (Fin 2) ℂ) :
    H.map star * Hᵀ = 1 :=
  mul_eq_one_comm.mp (transpose_mul_map_star hH)

/-- **The Gram matrix under the gauge action**: `(g • X)ᴴ (g • X) = conj(H) · Xᴴ X · Hᵀ`. -/
theorem gram_smul (g : Stage1Group) (X : Bidoublet) :
    (g • X)ᴴ * (g • X) = (g.2 : Matrix (Fin 2) (Fin 2) ℂ).map star * (Xᴴ * X)
      * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by
  have hG := (Matrix.mem_unitaryGroup_iff').mp (mem_specialUnitaryGroup_iff.mp g.1.2).1
  rw [star_eq_conjTranspose] at hG
  rw [stage1_smul_def, stage1Act, conjTranspose_mul, conjTranspose_mul,
    transpose_conjTranspose_eq_map_star]
  set G := (g.1 : Matrix (Fin 4) (Fin 4) ℂ)
  set H := (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  have e : (Xᴴ * Gᴴ) * (G * X) = Xᴴ * X := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Gᴴ, hG, Matrix.one_mul]
  calc H.map star * (Xᴴ * Gᴴ) * (G * X * Hᵀ) = H.map star * ((Xᴴ * Gᴴ) * (G * X)) * Hᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [e]

/-- **Whether the Gram matrix is a multiple of the identity does not depend on the gauge.** -/
theorem gram_scalar_smul_iff (g : Stage1Group) (X : Bidoublet) :
    (∃ c : ℂ, (g • X)ᴴ * (g • X) = c • 1) ↔ ∃ c : ℂ, Xᴴ * X = c • 1 := by
  have hH := (mem_specialUnitaryGroup_iff.mp g.2.2).1
  have h1 := transpose_mul_map_star hH
  have h2 := map_star_mul_transpose hH
  rw [gram_smul]
  set H := (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc Xᴴ * X = (Hᵀ * H.map star) * (Xᴴ * X) * (Hᵀ * H.map star) := by
          rw [h1, Matrix.one_mul, Matrix.mul_one]
      _ = Hᵀ * (H.map star * (Xᴴ * X) * Hᵀ) * H.map star := by simp only [Matrix.mul_assoc]
      _ = c • 1 := by rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h2]⟩

theorem vac2_conjTranspose_mul_self : vac2ᴴ * vac2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vac2, mul_apply, single_apply]

theorem gram_vac2_mul (D : Matrix (Fin 2) (Fin 2) ℂ) : (vac2 * D)ᴴ * (vac2 * D) = Dᴴ * D := by
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc vac2ᴴ, vac2_conjTranspose_mul_self,
    Matrix.one_mul]

/-- For invertible `D`, `Dᴴ D` is a multiple of the identity iff `D Dᴴ` is. -/
theorem scalar_conjTranspose_mul_iff {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    (∃ c : ℂ, Dᴴ * D = c • 1) ↔ ∃ c : ℂ, D * Dᴴ = c • 1 := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc D * Dᴴ = D * Dᴴ * (D * D⁻¹) := by rw [Matrix.mul_nonsing_inv D hD, Matrix.mul_one]
      _ = D * (Dᴴ * D) * D⁻¹ := by simp only [Matrix.mul_assoc]
      _ = c • 1 := by
          rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_nonsing_inv D hD]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc Dᴴ * D = D⁻¹ * D * Dᴴ * D := by rw [Matrix.nonsing_inv_mul D hD, Matrix.one_mul]
      _ = D⁻¹ * (D * Dᴴ) * D := by simp only [Matrix.mul_assoc]
      _ = c • 1 := by
          rw [hc, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.nonsing_inv_mul D hD]

/-- The normal form's `D` has `D Dᴴ` scalar exactly when `X`'s Gram matrix is. -/
theorem scalar_iff_of_smul_eq {X : Bidoublet} {g : Stage1Group} {D : Matrix (Fin 2) (Fin 2) ℂ}
    (hD : IsUnit D.det) (hgX : g • X = vac2 * D) :
    (∃ c : ℂ, D * Dᴴ = c • 1) ↔ ∃ c : ℂ, Xᴴ * X = c • 1 := by
  rw [← scalar_conjTranspose_mul_iff hD, ← gram_scalar_smul_iff g X, hgX, gram_vac2_mul]

theorem nonempty_stabilizer_equiv_SU2_SU2_of_scalar (X : Bidoublet) (hX : X.rank = 2)
    (hc : ∃ c : ℂ, Xᴴ * X = c • 1) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × SU2) := by
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  obtain ⟨c, hc'⟩ := (scalar_iff_of_smul_eq hD hgX).mpr hc
  exact ⟨((MulAction.stabilizerEquivStabilizer rfl).trans
    (MulEquiv.subgroupCongr (congrArg (MulAction.stabilizer Stage1Group) hgX))).trans
    (stabilizerVac2EquivOfScalar hD hc')⟩

theorem nonempty_stabilizer_equiv_SU2_circle_of_not_scalar (X : Bidoublet) (hX : X.rank = 2)
    (hc : ¬ ∃ c : ℂ, Xᴴ * X = c • 1) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × unitary ℂ) := by
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  have hns : ¬ ∃ c : ℂ, D * Dᴴ = c • 1 := fun h => hc ((scalar_iff_of_smul_eq hD hgX).mp h)
  exact ⟨((MulAction.stabilizerEquivStabilizer rfl).trans
    (MulEquiv.subgroupCongr (congrArg (MulAction.stabilizer Stage1Group) hgX))).trans
    (stabilizerVac2EquivCircle hD hns)⟩

/-- **A rank-two vacuum leaves `SU(2) × SU(2)` exactly when its Gram matrix is a multiple of the
identity** — its two columns orthogonal and of equal length. -/
theorem nonempty_stabilizer_equiv_SU2_SU2_iff (X : Bidoublet) (hX : X.rank = 2) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × SU2) ↔ ∃ c : ℂ, Xᴴ * X = c • 1 := by
  refine ⟨fun ⟨φ⟩ => ?_, nonempty_stabilizer_equiv_SU2_SU2_of_scalar X hX⟩
  by_contra hc
  obtain ⟨ψ⟩ := nonempty_stabilizer_equiv_SU2_circle_of_not_scalar X hX hc
  exact not_nonempty_SU2_SU2_equiv_SU2_circle ⟨φ.symm.trans ψ⟩

/-- **… and `SU(2) × U(1)` exactly when it is not.** -/
theorem nonempty_stabilizer_equiv_SU2_circle_iff (X : Bidoublet) (hX : X.rank = 2) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × unitary ℂ) ↔
      ¬ ∃ c : ℂ, Xᴴ * X = c • 1 := by
  refine ⟨fun ⟨ψ⟩ hc => ?_, nonempty_stabilizer_equiv_SU2_circle_of_not_scalar X hX⟩
  obtain ⟨φ⟩ := nonempty_stabilizer_equiv_SU2_SU2_of_scalar X hX hc
  exact not_nonempty_SU2_SU2_equiv_SU2_circle ⟨φ.symm.trans ψ⟩

/-! ## 5. Neither is `U(3)`, and the first stage is classified -/

theorem not_nonempty_SU2_SU2_equiv_U3 : ¬ Nonempty (SU2 × SU2 ≃* GroupU3) := by
  rintro ⟨φ⟩
  exact not_nonempty_stabilizer_vac2_equiv_U3 ⟨stabilizerVac2OneEquiv.trans φ⟩

/-- `diag(1, 2)`: invertible, with `D Dᴴ = diag(1, 4)` not a multiple of the identity. -/
theorem diag12_isUnit : IsUnit (diagonal ![(1 : ℂ), 2]).det := by
  simp [det_diagonal, Fin.prod_univ_two]

theorem diag12_not_scalar :
    ¬ ∃ c : ℂ, diagonal ![(1 : ℂ), 2] * (diagonal ![(1 : ℂ), 2])ᴴ = c • 1 := by
  rintro ⟨c, hc⟩
  have e0 := congrFun (congrFun hc 0) 0
  have e1 := congrFun (congrFun hc 1) 1
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, diagonal_conjTranspose, Fin.isValue, mul_diagonal,
    diagonal_apply_eq, cons_val_zero, Pi.star_apply, star_one, mul_one, smul_apply, one_apply_eq,
    smul_eq_mul, cons_val_one, cons_val_fin_one, star_ofNat] at e0 e1
  rw [← e0] at e1
  norm_num at e1

theorem not_nonempty_SU2_circle_equiv_U3 : ¬ Nonempty (SU2 × unitary ℂ ≃* GroupU3) := by
  rintro ⟨φ⟩
  exact not_nonempty_stabilizer_equiv_U3 diag12_isUnit
    ⟨(stabilizerVac2EquivCircle diag12_isUnit diag12_not_scalar).trans φ⟩

/-- **THE FIRST STAGE, CLASSIFIED.** For `X ≠ 0` the unbroken group is `U(3)` at rank one,
`SU(2) × SU(2)` at rank two with `Xᴴ X` a multiple of the identity, and `SU(2) × U(1)` at rank two
otherwise. The three are pairwise non-isomorphic (`not_nonempty_SU2_SU2_equiv_U3`,
`not_nonempty_SU2_circle_equiv_U3`, `not_nonempty_SU2_SU2_equiv_SU2_circle`). -/
theorem stabilizer_trichotomy (X : Bidoublet) (hX : X ≠ 0) :
    (X.rank = 1 ∧ Nonempty (MulAction.stabilizer Stage1Group X ≃* GroupU3)) ∨
    (X.rank = 2 ∧ (∃ c : ℂ, Xᴴ * X = c • 1) ∧
      Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × SU2)) ∨
    (X.rank = 2 ∧ (¬ ∃ c : ℂ, Xᴴ * X = c • 1) ∧
      Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × unitary ℂ)) := by
  have hle : X.rank ≤ 2 := (rank_le_width X).trans (by simp)
  have h0 : X.rank ≠ 0 := fun h0 => hX (eq_zero_of_rank_eq_zero h0)
  rcases (by omega : X.rank = 1 ∨ X.rank = 2) with h1 | h2
  · exact Or.inl ⟨h1, (nonempty_stabilizer_equiv_U3_iff X hX).mpr h1⟩
  · by_cases hc : ∃ c : ℂ, Xᴴ * X = c • 1
    · exact Or.inr (Or.inl ⟨h2, hc, nonempty_stabilizer_equiv_SU2_SU2_of_scalar X h2 hc⟩)
    · exact Or.inr (Or.inr ⟨h2, hc, nonempty_stabilizer_equiv_SU2_circle_of_not_scalar X h2 hc⟩)

/-! ## 6. The same, as topological groups -/

/-- A continuous isomorphism out of a compact group into a Hausdorff one is an isomorphism of
topological groups. -/
noncomputable def continuousMulEquivOfCompact {G H : Type*} [Group G] [Group H] [TopologicalSpace G]
    [TopologicalSpace H] [CompactSpace G] [T2Space H] (e : G ≃* H) (he : Continuous e) : G ≃ₜ* H :=
  { e with
    continuous_toFun := he
    continuous_invFun := (he.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

theorem continuous_stage1_entry (a b : Fin 4) :
    Continuous fun g : Stage1Group => (g.1 : Matrix (Fin 4) (Fin 4) ℂ) a b :=
  (continuous_apply b).comp ((continuous_apply a).comp (continuous_subtype_val.comp continuous_fst))

theorem continuous_topBlk : Continuous topBlk := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simpa [topBlk] using continuous_stage1_entry _ _

theorem continuous_botBlk (D : Matrix (Fin 2) (Fin 2) ℂ) : Continuous (botBlk D) :=
  (continuous_const.matrix_mul
    ((continuous_subtype_val.comp continuous_snd).matrix_map continuous_star)).matrix_mul
    continuous_const

theorem continuous_stabilizerVac2Equiv {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    Continuous (stabilizerVac2Equiv hD) :=
  Continuous.prodMk (f := fun x => (stabilizerVac2Equiv hD x).1)
    (g := fun x => (stabilizerVac2Equiv hD x).2)
    (continuous_induced_rng.mpr (continuous_topBlk.comp continuous_subtype_val))
    (continuous_induced_rng.mpr (continuous_induced_rng.mpr
      ((continuous_botBlk D).comp continuous_subtype_val)))

/-- **Unit 211's isomorphism, as topological groups**:
`stabilizer (vac2 · D) ≃ₜ* SU(2) × C(D Dᴴ)`. -/
noncomputable def stabilizerVac2ContinuousEquiv {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    MulAction.stabilizer Stage1Group (vac2 * D) ≃ₜ* SU2 × commSU2 (D * Dᴴ) :=
  haveI := compactSpace_stabilizer (vac2 * D)
  continuousMulEquivOfCompact _ (continuous_stabilizerVac2Equiv hD)

theorem continuous_stabilizerVac2EquivOfScalar {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    {c : ℂ} (hc : D * Dᴴ = c • 1) : Continuous (stabilizerVac2EquivOfScalar hD hc) :=
  Continuous.prodMk (f := fun x => (stabilizerVac2EquivOfScalar hD hc x).1)
    (g := fun x => (stabilizerVac2EquivOfScalar hD hc x).2)
    (continuous_induced_rng.mpr (continuous_topBlk.comp continuous_subtype_val))
    (continuous_induced_rng.mpr ((continuous_botBlk D).comp continuous_subtype_val))

theorem continuous_stabilizerVac2EquivCircle {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (hns : ¬ ∃ c : ℂ, D * Dᴴ = c • 1) : Continuous (stabilizerVac2EquivCircle hD hns) :=
  Continuous.prodMk (f := fun x => (stabilizerVac2EquivCircle hD hns x).1)
    (g := fun x => (stabilizerVac2EquivCircle hD hns x).2)
    (continuous_induced_rng.mpr (continuous_topBlk.comp continuous_subtype_val))
    (continuous_induced_rng.mpr ((continuous_apply 0).comp ((continuous_apply 0).comp
      (((continuous_const.matrix_mul (continuous_botBlk D)).matrix_mul continuous_const).comp
        continuous_subtype_val))))

/-- **Equal singular values, as topological groups**: `SU(2) × SU(2)`. -/
noncomputable def stabilizerVac2ContinuousEquivOfScalar {D : Matrix (Fin 2) (Fin 2) ℂ}
    (hD : IsUnit D.det) {c : ℂ} (hc : D * Dᴴ = c • 1) :
    MulAction.stabilizer Stage1Group (vac2 * D) ≃ₜ* SU2 × SU2 :=
  haveI := compactSpace_stabilizer (vac2 * D)
  continuousMulEquivOfCompact _ (continuous_stabilizerVac2EquivOfScalar hD hc)

/-- **Unequal singular values, as topological groups**: `SU(2) × U(1)`. -/
noncomputable def stabilizerVac2ContinuousEquivCircle {D : Matrix (Fin 2) (Fin 2) ℂ}
    (hD : IsUnit D.det) (hns : ¬ ∃ c : ℂ, D * Dᴴ = c • 1) :
    MulAction.stabilizer Stage1Group (vac2 * D) ≃ₜ* SU2 × unitary ℂ :=
  haveI := compactSpace_stabilizer (vac2 * D)
  continuousMulEquivOfCompact _ (continuous_stabilizerVac2EquivCircle hD hns)

theorem nonempty_stabilizer_continuousEquiv_SU2_SU2_iff (X : Bidoublet) (hX : X.rank = 2) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃ₜ* SU2 × SU2) ↔ ∃ c : ℂ, Xᴴ * X = c • 1 := by
  refine ⟨fun ⟨φ⟩ => (nonempty_stabilizer_equiv_SU2_SU2_iff X hX).mp ⟨φ.toMulEquiv⟩, fun hc => ?_⟩
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  obtain ⟨c, hc'⟩ := (scalar_iff_of_smul_eq hD hgX).mpr hc
  exact ⟨(stabilizerContinuousEquiv hgX.symm).trans (stabilizerVac2ContinuousEquivOfScalar hD hc')⟩

theorem nonempty_stabilizer_continuousEquiv_SU2_circle_iff (X : Bidoublet) (hX : X.rank = 2) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃ₜ* SU2 × unitary ℂ) ↔
      ¬ ∃ c : ℂ, Xᴴ * X = c • 1 := by
  refine ⟨fun ⟨φ⟩ => (nonempty_stabilizer_equiv_SU2_circle_iff X hX).mp ⟨φ.toMulEquiv⟩,
    fun hc => ?_⟩
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  have hns : ¬ ∃ c : ℂ, D * Dᴴ = c • 1 := fun h => hc ((scalar_iff_of_smul_eq hD hgX).mp h)
  exact ⟨(stabilizerContinuousEquiv hgX.symm).trans (stabilizerVac2ContinuousEquivCircle hD hns)⟩

/-- **THE FIRST STAGE, CLASSIFIED AS TOPOLOGICAL GROUPS.** -/
theorem stabilizer_trichotomy_continuous (X : Bidoublet) (hX : X ≠ 0) :
    (X.rank = 1 ∧ Nonempty (MulAction.stabilizer Stage1Group X ≃ₜ* GroupU3)) ∨
    (X.rank = 2 ∧ (∃ c : ℂ, Xᴴ * X = c • 1) ∧
      Nonempty (MulAction.stabilizer Stage1Group X ≃ₜ* SU2 × SU2)) ∨
    (X.rank = 2 ∧ (¬ ∃ c : ℂ, Xᴴ * X = c • 1) ∧
      Nonempty (MulAction.stabilizer Stage1Group X ≃ₜ* SU2 × unitary ℂ)) := by
  rcases stabilizer_trichotomy X hX with ⟨h1, -⟩ | ⟨h2, hc, -⟩ | ⟨h2, hc, -⟩
  · exact Or.inl ⟨h1, nonempty_stabilizer_continuousEquiv_U3 X h1⟩
  · exact Or.inr (Or.inl ⟨h2, hc, (nonempty_stabilizer_continuousEquiv_SU2_SU2_iff X h2).mpr hc⟩)
  · exact Or.inr (Or.inr ⟨h2, hc, (nonempty_stabilizer_continuousEquiv_SU2_circle_iff X h2).mpr hc⟩)

end PatiSalamFirstStageClassification
