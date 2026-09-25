/-
  PatiSalamPairCriterion: which pairs of Higgs vacua leave `U(3)` unbroken, for every nonzero
  first-stage vacuum — exactly those whose first vacuum `X` has rank one and whose second `Φ` is
  nonzero with `Φᴴ Φ` commuting with `(Xᴴ X)ᵀ` — and, at every rank-one `X`, unit 222's three
  groups, as topological groups

  Campaign 3 hardening unit 225 (25 September 2026). Spine link L15 (Higgs sector).

  WHY. Units 222 and 223 classified the joint unbroken group at `(vac, Φ)` for every `Φ`, with the
  estate's first-stage vacuum `vac` fixed. Unit 222's NOT list: *"Other first-stage vacua: only the
  estate's `vac`. For a rank-one `X`, unit 203's conjugation would transport the statements; that
  transport is not written"*. This file writes it, and settles the rank-two first vacua by unit
  204's count of elements of square one, so that *which pairs leave `U(3)`* is answered for every
  pair with a nonzero first vacuum.

  WHAT IS PROVED.
  (1) The condition, read off `X`. **`transpose_conjTranspose_mul_self`**: for `X = c · g • vac`,
      `(Xᴴ X)ᵀ = |c|² · gR E₀₀ gR⋆`, a multiple of the projector onto `gR e₀`;
      **`comm_iff_orthogonal`**: for unitary `U`, `Φᴴ Φ` commutes with `U E₀₀ U⋆` exactly when `Φ U`
      has orthogonal columns (`mul_single_comm_iff`); so **`comm_transpose_iff`**; and
      **`comm_transpose_vac_iff`**: at `X = vac` the condition is unit 221's `(Φᴴ Φ) 0 1 = 0`.
  (2) The transport. `liftR g = (g.1, 1, g.2)` carries `(c · vac, Φ gR)` to `(c · g • vac, Φ)`
      (`liftR_smul`); with unit 203's `rank_eq_one_iff_mem_orbit` and `stabilizer_pair_smul` and
      unit 209's `stabilizerContinuousEquiv`, **`exists_stabilizer_pair_continuousEquiv`**: every
      pair with a rank-one first vacuum has the unbroken group of a pair `(vac, Φ gR)`, as a
      topological group; `Φ gR = 0` exactly when `Φ = 0` (`mul_unitary_eq_zero_iff`).
  (3) **`joint_trichotomy_of_rank_eq_one`**: at every rank-one `X`, the joint group is
      `U(3) × SU(2)` at `Φ = 0`, `U(3)` when `Φᴴ Φ` commutes with `(Xᴴ X)ᵀ`, and `SU(3) × {±1}`
      otherwise, as topological groups — unit 223's `joint_trichotomy_continuous`, transported.
  (4) Rank two. `toFirstLeft`, injective: the joint unbroken group embeds in the first vacuum's
      times `SU(2)_L`. `finite_involutions_SU2` (`±1`, by unit 204's
      `eq_one_or_eq_neg_one_of_mul_self`) and `finite_involutions_stabilizer_of_rank_eq_two` (unit
      204's count, carried by conjugation); so
      **`not_nonempty_stabilizer_pair_equiv_U3_of_rank_eq_two`**: a pair whose first vacuum has rank
      two never leaves `U(3)`, whatever `Φ`, since `U(3)` has infinitely many elements of square one
      (unit 204's `infinite_involutions_U3`).
  (5) **`nonempty_stabilizer_pair_equiv_U3_iff_of_ne_zero`** and
      **`nonempty_stabilizer_pair_continuousEquiv_U3_iff_of_ne_zero`**: for `X ≠ 0`, the pair
      `(X, Φ)` leaves `U(3)`, as an abstract or as a topological group, exactly when `X` has rank
      one, `Φ ≠ 0` and `Φᴴ Φ` commutes with `(Xᴴ X)ᵀ`; the rank-one half is
      `nonempty_stabilizer_pair_equiv_U3_iff_of_rank_eq_one`.
  (6) The count decides, at `vac`. **`finrank_jointStabAt_vac_eq`**: unit 221's joint count as one
      number, twelve, nine or eight; **`nonempty_stabilizer_pair_equiv_iff_finrank_eq`**: two
      second-stage vacua leave isomorphic joint groups exactly when they leave the same number of
      unbroken generators — unit 213's `nonempty_stabilizer_equiv_iff_finrank_broken_eq`, for the
      pair.

  NOT PROVED, said exactly.
  • `X = 0`, whose stabiliser contains the whole of `SU(4)`: not examined.
  • The joint groups at a rank-two first vacuum: only that none is `U(3)`; what they are is not
    computed.
  • Lie-group (smooth) structure, the Lie algebras, which vacuum, masses: as in units 222 and 223.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `mul_single_comm_iff` takes `Nᴴ = N`;
  `comm_iff_orthogonal` takes `star U * U = 1` and `U * star U = 1`;
  `finite_involutions_stabilizer_of_rank_eq_two` and
  `not_nonempty_stabilizer_pair_equiv_U3_of_rank_eq_two` take `X.rank = 2`;
  `subgroupContinuousCongr` takes `H = K`; `exists_stabilizer_pair_continuousEquiv`,
  `joint_trichotomy_of_rank_eq_one` and `nonempty_stabilizer_pair_equiv_U3_iff_of_rank_eq_one` take
  `X.rank = 1`; `comm_transpose_iff` takes `0 < r`;
  `nonempty_stabilizer_pair_equiv_U3_iff_of_ne_zero` and
  `nonempty_stabilizer_pair_continuousEquiv_U3_iff_of_ne_zero` take `X ≠ 0`. The rest take elements
  of their types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 22 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken, and the pinned Mathlib has no topological `subgroupCongr`. The nearest
  statements are unit 204's `not_nonempty_stabilizer_equiv_U3_of_rank_eq_two` (the first stage
  alone), of which (4) is the version for pairs, its `finite_involutions_stabilizer`,
  `infinite_involutions_U3`, `exists_smul_eq_vac2_mul` and `eq_one_or_eq_neg_one_of_mul_self`, used;
  unit 203's aligned pairs (`nonempty_stabilizer_pair_equiv_U3`, used for nothing here), which by
  (5) satisfy the condition, since they leave `U(3)`; unit 207's `negOneSU2`, used; units 222's and
  223's classifications at `vac`, of which (3) and (5) are the transports; and unit 213's
  `nonempty_stabilizer_equiv_iff_finrank_broken_eq` and unit 221's `finrank_jointStabAt_vac`, which
  (6) combines with unit 222's `nonempty_stabilizer_pair_equiv_iff`.

  `#print axioms` on all 22 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamSecondStageTopology

open Matrix PatiSalamVacuumStabiliser ElectroweakVacuumStabiliser PatiSalamGaugeAction
  PatiSalamStabiliserGroup PatiSalamRankTwoStabiliser PatiSalamUnbrokenSplit
  PatiSalamStabiliserTopology PatiSalamTopologicalCopies PatiSalamJointClassification
  PatiSalamVacuumOrbit PatiSalamRankTwoVacuum ElectroweakUnbrokenGroup PatiSalamTwoComponentVacuum
  PatiSalamSecondStageTopology PatiSalamMatrixLie PatiSalamJointCount

namespace PatiSalamPairCriterion

noncomputable section

/-- The first-stage element `g`, lifted to the full group with trivial `SU(2)_L` part. -/
def liftR (g : Stage1Group) : FullGroup := (g.1, 1, g.2)

theorem liftR_smul (g : Stage1Group) (c : ℂ) (Φ : EWBidoublet) :
    liftR g • (c • vac, Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) = (c • (g • vac), Φ) := by
  refine Prod.ext ?_ ?_
  · rw [full_smul_fst]
    exact stage1_smul_smul g c vac
  · rw [full_smul_snd, stage2_smul_def, stage2Act]
    change (1 : Matrix (Fin 2) (Fin 2) ℂ) * (Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) *
      star (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = Φ
    rw [Matrix.one_mul, Matrix.mul_assoc,
      mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp g.2.2).1, Matrix.mul_one]

/-- `vacᴴ vac = E₀₀`. -/
theorem conjTranspose_vac_mul_vac : vacᴴ * vac = Matrix.single 0 0 (1 : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vac, Matrix.mul_apply, Matrix.single_apply]

/-- **The first vacuum's `SU(2)_R` direction, read off `X` itself**: for `X = c · g • vac`,
`(Xᴴ X)ᵀ = |c|² · gR E₀₀ gRᴴ`. -/
theorem transpose_conjTranspose_mul_self (g : Stage1Group) (c : ℂ) :
    ((c • (g • vac))ᴴ * (c • (g • vac)))ᵀ =
      (star c * c) • ((g.2 : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.single 0 0 (1 : ℂ) *
        star (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  set A := (g.1 : Matrix (Fin 4) (Fin 4) ℂ)
  set B := (g.2 : Matrix (Fin 2) (Fin 2) ℂ)
  have h4 : Aᴴ * A = 1 := by
    rw [← star_eq_conjTranspose]
    exact mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp g.1.2).1
  have hB : (Bᵀᴴ)ᵀ = star B := by
    ext i j
    simp [B, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.star_apply]
  rw [stage1_smul_def, stage1Act, conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    transpose_smul]
  congr 1
  change ((A * vac * Bᵀ)ᴴ * (A * vac * Bᵀ))ᵀ = B * Matrix.single 0 0 (1 : ℂ) * star B
  rw [conjTranspose_mul, conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Aᴴ A, h4, Matrix.one_mul, ← Matrix.mul_assoc vacᴴ vac,
    conjTranspose_vac_mul_vac, transpose_mul, transpose_mul, transpose_transpose, hB,
    transpose_single, Matrix.mul_assoc]

theorem mul_single_comm_iff {N : Matrix (Fin 2) (Fin 2) ℂ} (hN : Nᴴ = N) :
    N * Matrix.single 0 0 (1 : ℂ) = Matrix.single 0 0 (1 : ℂ) * N ↔ N 0 1 = 0 := by
  have h10 : N 1 0 = star (N 0 1) := by
    rw [← hN, conjTranspose_apply, hN]
  constructor
  · intro h
    have e := congrFun (congrFun h 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply] using e.symm
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.single_apply, h, h10]

/-- **THE CONDITION, READ OFF `X`**: for unitary `U`, `Φᴴ Φ` commutes with `U E₀₀ U⋆` exactly when
`Φ U` has orthogonal columns. -/
theorem comm_iff_orthogonal (Φ : EWBidoublet) {U : Matrix (Fin 2) (Fin 2) ℂ}
    (hU1 : star U * U = 1) (hU2 : U * star U = 1) :
    (Φᴴ * Φ) * (U * Matrix.single 0 0 (1 : ℂ) * star U) =
        (U * Matrix.single 0 0 (1 : ℂ) * star U) * (Φᴴ * Φ) ↔
      ((Φ * U)ᴴ * (Φ * U)) 0 1 = 0 := by
  set E := Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)
  set M := Φᴴ * Φ
  have hN : (Φ * U)ᴴ * (Φ * U) = star U * M * U := by
    rw [conjTranspose_mul, ← star_eq_conjTranspose U]
    simp only [M, Matrix.mul_assoc]
  have hNh : ((Φ * U)ᴴ * (Φ * U))ᴴ = (Φ * U)ᴴ * (Φ * U) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [← mul_single_comm_iff hNh, hN]
  constructor
  · intro h
    calc star U * M * U * E = star U * (M * (U * E * star U)) * U := by
          simp only [Matrix.mul_assoc]
          rw [hU1, Matrix.mul_one]
      _ = star U * ((U * E * star U) * M) * U := by rw [h]
      _ = E * (star U * M * U) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (star U) U, hU1, Matrix.one_mul]
  · intro h
    calc M * (U * E * star U) = U * (star U * M * U * E) * star U := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U (star U), hU2, Matrix.one_mul]
      _ = U * (E * (star U * M * U)) * star U := by rw [h]
      _ = U * E * star U * M := by
          simp only [Matrix.mul_assoc]
          rw [hU2, Matrix.mul_one]

/-- A joint unbroken element's first-stage part and its `SU(2)_L` part. -/
def toFirstLeft (X : Bidoublet) (Φ : EWBidoublet) :
    MulAction.stabilizer FullGroup (X, Φ) →* MulAction.stabilizer Stage1Group X × SU2 where
  toFun h := (⟨((h : FullGroup).1, (h : FullGroup).2.2),
    ((mem_stabilizer_pair_iff' _ _ _).mp h.2).1⟩, (h : FullGroup).2.1)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toFirstLeft_injective (X : Bidoublet) (Φ : EWBidoublet) :
    Function.Injective (toFirstLeft X Φ) := by
  intro h h' e
  have e1 : ((h : FullGroup).1, (h : FullGroup).2.2) = ((h' : FullGroup).1, (h' : FullGroup).2.2) :=
    congrArg (fun x : MulAction.stabilizer Stage1Group X × SU2 => (x.1 : Stage1Group)) e
  have e2 : (h : FullGroup).2.1 = (h' : FullGroup).2.1 := congrArg Prod.snd e
  exact Subtype.ext (Prod.ext (Prod.ext_iff.mp e1).1 (Prod.ext e2 (Prod.ext_iff.mp e1).2))

/-- **`SU(2)` has two elements of square one**, `±1` (unit 204's
`eq_one_or_eq_neg_one_of_mul_self`). -/
theorem finite_involutions_SU2 : {u : SU2 | u * u = 1}.Finite := by
  refine (Set.toFinite ({1, PatiSalamSameStabiliser.negOneSU2} : Set SU2)).subset ?_
  intro u hu
  have hu' : (u : Matrix (Fin 2) (Fin 2) ℂ) * u = 1 := congrArg Subtype.val (show u * u = 1 from hu)
  rcases eq_one_or_eq_neg_one_of_mul_self (mem_specialUnitaryGroup_iff.mp u.2).2 hu' with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem finite_involutions_stabilizer_of_rank_eq_two (X : Bidoublet) (hX : X.rank = 2) :
    {s : MulAction.stabilizer Stage1Group X | s * s = 1}.Finite := by
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  let φ : MulAction.stabilizer Stage1Group X ≃* MulAction.stabilizer Stage1Group (vac2 * D) :=
    (MulAction.stabilizerEquivStabilizer rfl).trans
      (MulEquiv.subgroupCongr (congrArg (MulAction.stabilizer Stage1Group) hgX))
  refine ((finite_involutions_stabilizer hD).preimage φ.injective.injOn).subset ?_
  intro s hs
  change φ s * φ s = 1
  rw [← map_mul, show s * s = 1 from hs, map_one]

/-- **A PAIR WHOSE FIRST VACUUM HAS RANK TWO NEVER LEAVES `U(3)`**: its joint unbroken group embeds
in the first vacuum's times `SU(2)_L`, which has finitely many elements of square one; `U(3)` has
infinitely many (unit 204's argument, one factor wider). -/
theorem not_nonempty_stabilizer_pair_equiv_U3_of_rank_eq_two (X : Bidoublet) (hX : X.rank = 2)
    (Φ : EWBidoublet) : ¬ Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃* GroupU3) := by
  rintro ⟨e⟩
  apply infinite_involutions_U3
  have hT : {x : MulAction.stabilizer Stage1Group X × SU2 | x * x = 1}.Finite := by
    refine ((finite_involutions_stabilizer_of_rank_eq_two X hX).prod
      finite_involutions_SU2).subset ?_
    intro x hx
    exact ⟨congrArg Prod.fst (show x * x = 1 from hx), congrArg Prod.snd (show x * x = 1 from hx)⟩
  have hfin : {s : MulAction.stabilizer FullGroup (X, Φ) | s * s = 1}.Finite := by
    refine (hT.preimage (toFirstLeft_injective X Φ).injOn).subset ?_
    intro s hs
    change toFirstLeft X Φ s * toFirstLeft X Φ s = 1
    rw [← map_mul, show s * s = 1 from hs, map_one]
  have : {h : GroupU3 | h * h = 1} = e '' {s | s * s = 1} := by
    ext h
    constructor
    · intro hh
      refine ⟨e.symm h, ?_, e.apply_symm_apply h⟩
      change e.symm h * e.symm h = 1
      rw [← map_mul, show h * h = 1 from hh, map_one]
    · rintro ⟨s, hs, rfl⟩
      change e s * e s = 1
      rw [← map_mul, show s * s = 1 from hs, map_one]
  rw [this]
  exact hfin.image _

/-- Two equal subgroups, as topological groups. -/
def subgroupContinuousCongr {G : Type*} [Group G] [TopologicalSpace G] {H K : Subgroup G}
    (h : H = K) : H ≃ₜ* K :=
  { MulEquiv.subgroupCongr h with
    continuous_toFun := continuous_induced_rng.mpr continuous_subtype_val
    continuous_invFun := continuous_induced_rng.mpr continuous_subtype_val }

/-- **Every pair with a rank-one first vacuum has the unbroken group of a pair with first vacuum
`vac`**: `X = r · g • vac` (unit 203), and `(X, Φ)` is `(g, 1)` applied to `(r · vac, Φ gR)`. -/
theorem exists_stabilizer_pair_continuousEquiv (X : Bidoublet) (hX : X.rank = 1)
    (Φ : EWBidoublet) :
    ∃ g : Stage1Group, ∃ r : ℝ, 0 < r ∧ X = (r : ℂ) • (g • vac) ∧
      Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ*
        MulAction.stabilizer FullGroup (vac, Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ))) := by
  obtain ⟨g, r, hr, rfl⟩ := (rank_eq_one_iff_mem_orbit X).mp hX
  refine ⟨g, r, hr, rfl, ⟨?_⟩⟩
  have hpair : ((r : ℂ) • (g • vac), Φ) =
      liftR g • ((r : ℂ) • vac, Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) := (liftR_smul g r Φ).symm
  have hsc : MulAction.stabilizer FullGroup ((r : ℂ) • vac, Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ))
      = MulAction.stabilizer FullGroup (vac, Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    have := stabilizer_pair_smul (Complex.ofReal_ne_zero.mpr hr.ne') one_ne_zero
      (vac, Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ))
    simpa only [one_smul] using this
  exact (stabilizerContinuousEquiv hpair).symm.trans (subgroupContinuousCongr hsc)

theorem mul_unitary_eq_zero_iff (Φ : EWBidoublet) (B : SU2) :
    Φ * (B : Matrix (Fin 2) (Fin 2) ℂ) = 0 ↔ Φ = 0 := by
  constructor
  · intro h
    have hB : (B : Matrix (Fin 2) (Fin 2) ℂ) * star (B : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp B.2).1
    calc Φ = Φ * (B : Matrix (Fin 2) (Fin 2) ℂ) * star (B : Matrix (Fin 2) (Fin 2) ℂ) := by
          rw [Matrix.mul_assoc, hB, Matrix.mul_one]
      _ = 0 := by rw [h, Matrix.zero_mul]
  · rintro rfl
    exact Matrix.zero_mul _

/-- **THE CONDITION IN TERMS OF `X`**: for `X = r · g • vac`, `Φᴴ Φ` commutes with `(Xᴴ X)ᵀ` exactly
when `Φ gR` has orthogonal columns. -/
theorem comm_transpose_iff (g : Stage1Group) {r : ℝ} (hr : 0 < r) (Φ : EWBidoublet) :
    (Φᴴ * Φ) * (((r : ℂ) • (g • vac))ᴴ * ((r : ℂ) • (g • vac)))ᵀ =
        (((r : ℂ) • (g • vac))ᴴ * ((r : ℂ) • (g • vac)))ᵀ * (Φᴴ * Φ) ↔
      ((Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ))ᴴ * (Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ))) 0 1
        = 0 := by
  have hc : star (r : ℂ) * (r : ℂ) ≠ 0 := by
    have : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    exact mul_ne_zero (star_ne_zero.mpr this) this
  rw [transpose_conjTranspose_mul_self, Matrix.mul_smul, Matrix.smul_mul,
    smul_right_injective _ hc |>.eq_iff]
  exact comm_iff_orthogonal Φ (mem_unitaryGroup_iff'.mp (mem_specialUnitaryGroup_iff.mp g.2.2).1)
    (mem_unitaryGroup_iff.mp (mem_specialUnitaryGroup_iff.mp g.2.2).1)

/-- **THE JOINT UNBROKEN GROUP AT EVERY PAIR WITH A RANK-ONE FIRST VACUUM, AS A TOPOLOGICAL
GROUP**: `U(3) × SU(2)` at `Φ = 0`; `U(3)` when `Φᴴ Φ` commutes with `(Xᴴ X)ᵀ`; `SU(3) × {±1}`
otherwise. -/
theorem joint_trichotomy_of_rank_eq_one (X : Bidoublet) (hX : X.rank = 1) (Φ : EWBidoublet) :
    (Φ = 0 ∧ Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ* GroupU3 × SU2)) ∨
    (Φ ≠ 0 ∧ (Φᴴ * Φ) * (Xᴴ * X)ᵀ = (Xᴴ * X)ᵀ * (Φᴴ * Φ) ∧
      Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ* GroupU3)) ∨
    (Φ ≠ 0 ∧ (Φᴴ * Φ) * (Xᴴ * X)ᵀ ≠ (Xᴴ * X)ᵀ * (Φᴴ * Φ) ∧
      Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ* SU3 × ℤˣ)) := by
  obtain ⟨g, r, hr, rfl, ⟨e⟩⟩ := exists_stabilizer_pair_continuousEquiv X hX Φ
  simp only [ne_eq]
  rw [comm_transpose_iff g hr Φ]
  have hz := mul_unitary_eq_zero_iff Φ g.2
  rcases joint_trichotomy_continuous (Φ * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)) with
    ⟨h0, ⟨f⟩⟩ | ⟨h0, h1, ⟨f⟩⟩ | ⟨h0, h1, ⟨f⟩⟩
  · exact Or.inl ⟨hz.mp h0, ⟨e.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨fun h => h0 (hz.mpr h), h1, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨fun h => h0 (hz.mpr h), h1, ⟨e.trans f⟩⟩)

theorem nonempty_stabilizer_pair_equiv_U3_iff_of_rank_eq_one (X : Bidoublet) (hX : X.rank = 1)
    (Φ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃* GroupU3) ↔
      Φ ≠ 0 ∧ (Φᴴ * Φ) * (Xᴴ * X)ᵀ = (Xᴴ * X)ᵀ * (Φᴴ * Φ) := by
  obtain ⟨g, r, hr, rfl, ⟨e⟩⟩ := exists_stabilizer_pair_continuousEquiv X hX Φ
  rw [comm_transpose_iff g hr Φ]
  have hz := mul_unitary_eq_zero_iff Φ g.2
  constructor
  · rintro ⟨f⟩
    obtain ⟨h1, h2⟩ := (nonempty_stabilizer_pair_equiv_U3_iff _).mp ⟨e.toMulEquiv.symm.trans f⟩
    exact ⟨fun h => h1 (hz.mpr h), h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨f⟩ := (nonempty_stabilizer_pair_equiv_U3_iff _).mpr ⟨fun h => h1 (hz.mp h), h2⟩
    exact ⟨e.toMulEquiv.trans f⟩

/-- **WHICH PAIRS OF VACUA LEAVE `U(3)`, FOR EVERY NONZERO FIRST VACUUM**: exactly those whose first
vacuum has rank one and whose second is nonzero with `Φᴴ Φ` commuting with `(Xᴴ X)ᵀ`. -/
theorem nonempty_stabilizer_pair_equiv_U3_iff_of_ne_zero (X : Bidoublet) (hX : X ≠ 0)
    (Φ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃* GroupU3) ↔
      X.rank = 1 ∧ Φ ≠ 0 ∧ (Φᴴ * Φ) * (Xᴴ * X)ᵀ = (Xᴴ * X)ᵀ * (Φᴴ * Φ) := by
  have hle : X.rank ≤ 2 := (rank_le_width X).trans (by simp)
  have h0 : X.rank ≠ 0 := fun h0 => hX (eq_zero_of_rank_eq_zero h0)
  rcases (by omega : X.rank = 1 ∨ X.rank = 2) with h1 | h2
  · rw [nonempty_stabilizer_pair_equiv_U3_iff_of_rank_eq_one X h1 Φ]
    exact ⟨fun h => ⟨h1, h⟩, fun h => h.2⟩
  · exact iff_of_false (not_nonempty_stabilizer_pair_equiv_U3_of_rank_eq_two X h2 Φ)
      (fun h => by omega)

/-- **… and as topological groups.** -/
theorem nonempty_stabilizer_pair_continuousEquiv_U3_iff_of_ne_zero (X : Bidoublet) (hX : X ≠ 0)
    (Φ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (X, Φ) ≃ₜ* GroupU3) ↔
      X.rank = 1 ∧ Φ ≠ 0 ∧ (Φᴴ * Φ) * (Xᴴ * X)ᵀ = (Xᴴ * X)ᵀ * (Φᴴ * Φ) := by
  refine ⟨fun ⟨e⟩ => (nonempty_stabilizer_pair_equiv_U3_iff_of_ne_zero X hX Φ).mp ⟨e.toMulEquiv⟩,
    fun ⟨h1, h2, h3⟩ => ?_⟩
  rcases joint_trichotomy_of_rank_eq_one X h1 Φ with ⟨h, -⟩ | ⟨-, -, he⟩ | ⟨-, h, -⟩
  · exact absurd h h2
  · exact he
  · exact absurd h3 h

/-- **At `X = vac` the condition is unit 222's**: `(vacᴴ vac)ᵀ = E₀₀`, and `Φᴴ Φ` commutes with it
exactly when the columns of `Φ` are orthogonal. -/
theorem comm_transpose_vac_iff (Φ : EWBidoublet) :
    (Φᴴ * Φ) * (vacᴴ * vac)ᵀ = (vacᴴ * vac)ᵀ * (Φᴴ * Φ) ↔ (Φᴴ * Φ) 0 1 = 0 := by
  have hh : (Φᴴ * Φ)ᴴ = Φᴴ * Φ := by rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [conjTranspose_vac_mul_vac, transpose_single]
  exact mul_single_comm_iff hh

/-- **The joint unbroken count at `vac`, as one number**: twelve at `Φ = 0`, nine at orthogonal
columns, eight otherwise (unit 221). -/
theorem finrank_jointStabAt_vac_eq (Φ : EWBidoublet) :
    Module.finrank ℝ (jointStabAt (vac, Φ)) =
      if Φ = 0 then 12 else if (Φᴴ * Φ) 0 1 = 0 then 9 else 8 := by
  by_cases hΦ : Φ = 0
  · subst hΦ
    rw [if_pos rfl, finrank_jointStabAt_vac_zero]
  · rw [if_neg hΦ, finrank_jointStabAt_vac hΦ]

/-- **THE COUNT DECIDES THE JOINT GROUP**: with `vac`, two second-stage vacua leave isomorphic joint
unbroken groups exactly when they leave the same number of unbroken generators — unit 213's
`nonempty_stabilizer_equiv_iff_finrank_broken_eq`, for the pair. -/
theorem nonempty_stabilizer_pair_equiv_iff_finrank_eq (Φ Ψ : EWBidoublet) :
    Nonempty (MulAction.stabilizer FullGroup (vac, Φ) ≃* MulAction.stabilizer FullGroup (vac, Ψ)) ↔
      Module.finrank ℝ (jointStabAt (vac, Φ)) = Module.finrank ℝ (jointStabAt (vac, Ψ)) := by
  rw [nonempty_stabilizer_pair_equiv_iff, finrank_jointStabAt_vac_eq, finrank_jointStabAt_vac_eq]
  have z : ∀ A : EWBidoublet, A = 0 → (Aᴴ * A) 0 1 = 0 := by
    rintro A rfl
    simp
  by_cases hΦ : Φ = 0 <;> by_cases hΨ : Ψ = 0 <;>
    by_cases hΦ1 : (Φᴴ * Φ) 0 1 = 0 <;> by_cases hΨ1 : (Ψᴴ * Ψ) 0 1 = 0 <;>
    simp_all

end

end PatiSalamPairCriterion
