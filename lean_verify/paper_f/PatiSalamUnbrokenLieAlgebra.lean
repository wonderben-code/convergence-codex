/-
  PatiSalamUnbrokenLieAlgebra: at every first-stage vacuum the unbroken group's Lie algebra is a Lie
  subalgebra of `gl(4) ⊕ gl(2)` over `ℝ` — closed under the commutator — of dimension nine, six or
  four

  Campaign 3 hardening unit 218 (25 September 2026). Spine link L15 (Higgs sector).

  WHY. Unit 180 (`PatiSalamStabiliserLie`) carried the bracket at the chosen vacuum: `stabLie`, a
  `LieSubalgebra ℝ` of `gl(4) × gl(2)`, is unit 178's `stab` in matrices (`map_stab_toMat`). Unit
  213 counted the unbroken subalgebra `stabAt X` at every vacuum as a `Submodule`, and unit 217
  (`PatiSalamMatrixLie`) proved it is the Lie algebra of the unbroken group in the sense matrix
  groups use. Unit 217's NOT list: *"The bracket is not carried: that `stabAt X` is closed under the
  commutator is unit 180's argument at `X`, and it needs `TracelessSkewLie`, which this file does
  not import"*. This file imports both and carries it.

  WHAT IS PROVED.
  (1) `orbitMatAt X`, the orbit map at `X` on the whole of `gl(4) ⊕ gl(2)`, `ℂ`-linear; **`fixLieAt
      X`**, its kernel, a `LieSubalgebra ℂ` — unit 180's `act_bracket` alone, at every `X`; and
      **`stabLieAt X := psLie ⊓ fixLieAt X`**, a `LieSubalgebra ℝ`, with `mem_stabLieAt_iff` and
      `stabLieAt_vac` (unit 180's `stabLie`, by `rfl`) — unit 180's `fixLie` and `stabLie` without
      `X = vac`.
  (2) `toMat_mem_stabLieAt_iff` and **`map_stabAt_toMat`**: unit 213's `stabAt X`, carried to
      matrices by unit 180's `toMat`, is `stabLieAt X`; `finrank_stabLieAt`: the dimensions agree.
  (3) **`matLie_stabilizer_eq`**: the unbroken group's Lie algebra at `X`, unit 217's `matLie`, IS
      `stabLieAt X` as a set — so it is closed under the commutator; and `matLie_top_eq`: the whole
      group's is unit 180's `psLie`.
  (4) **`finrank_stabLieAt_trichotomy`**: nine, six or four, by unit 212's three cases, and
      **`nonempty_stabilizer_equiv_iff_finrank_stabLieAt_eq`**: two nonzero vacua leave isomorphic
      unbroken groups exactly when those Lie algebras have the same dimension.

  NOT PROVED, said exactly.
  • No smooth structure, as in unit 217: the Lie algebra is the matrix-group one.
  • No isomorphism of Lie algebras is named beyond unit 180's at `vac` (`stabLieEquivU3`): at rank
    two, `stabLieAt X` is not shown to be `su(2) ⊕ su(2)` or `su(2) ⊕ u(1)` AS A LIE ALGEBRA, only
    to have their dimensions.
  • The electroweak stage and the pair of vacua: their subalgebras are unit 217's, as `Submodule`s;
    the bracket is not carried there.
  • Goldstone's theorem, which vacuum, masses: unchanged.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `finrank_stabLieAt_trichotomy` takes `X ≠ 0`,
  and `nonempty_stabilizer_equiv_iff_finrank_stabLieAt_eq` takes `X ≠ 0` and `Y ≠ 0`. The rest take
  elements of their types and nothing else.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 12 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements are unit 180's `orbitMat`, `fixLie`, `stabLie`,
  `toMat_mem_stabLie_iff`, `map_stab_toMat` and `finrank_stabLie`, of which (1) and (2) are the
  versions at every `X` — the proofs are unit 180's, with `vac` a variable; unit 213's
  `finrank_stabAt_trichotomy` and `nonempty_stabilizer_equiv_iff_finrank_eq`, which (4) restates for
  `stabLieAt`; and unit 217's `mem_matLie_top_iff` and `mem_matLie_stabilizer_iff`, which (3) turns
  into set equalities with unit 180's objects.

  `#print axioms` on all 12 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamMatrixLie
import PatiSalamStabiliserLie

open Matrix TracelessSkewDimension PatiSalamVacuumStabiliser PatiSalamGaugeAction
  PatiSalamBrokenCount PatiSalamStabiliserLie PatiSalamMatrixLie

namespace PatiSalamUnbrokenLieAlgebra

noncomputable section

/-- The orbit map at any first-stage vacuum on the whole of `gl(4) ⊕ gl(2)` — unit 180's `orbitMat`
at `X`. -/
def orbitMatAt (X : Bidoublet) : Mat4 × Mat2 →ₗ[ℂ] Bidoublet where
  toFun x := act x.1 x.2 X
  map_add' x y := by
    simp only [act, Prod.fst_add, Prod.snd_add, Matrix.transpose_add, Matrix.add_mul,
      Matrix.mul_add]
    abel
  map_smul' c x := by
    simp only [act, Prod.smul_fst, Prod.smul_snd, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, RingHom.id_apply]

/-- **The full stabiliser of any first-stage vacuum in `gl(4) ⊕ gl(2)` is a Lie subalgebra** — unit
180's `fixLie`, without `X = vac`: `act_bracket` alone. -/
def fixLieAt (X : Bidoublet) : LieSubalgebra ℂ (Mat4 × Mat2) where
  toSubmodule := LinearMap.ker (orbitMatAt X)
  lie_mem' {x y} hx hy := by
    have hx' : act x.1 x.2 X = 0 := hx
    have hy' : act y.1 y.2 X = 0 := hy
    change act ⁅x.1, y.1⁆ ⁅x.2, y.2⁆ X = 0
    rw [act_bracket, hx', hy', act_zero, act_zero, sub_zero]

/-- **THE UNBROKEN SUBALGEBRA AT ANY FIRST-STAGE VACUUM, AS A LIE SUBALGEBRA OVER `ℝ`** — unit 180's
`stabLie`, without `X = vac`. -/
def stabLieAt (X : Bidoublet) : LieSubalgebra ℝ (Mat4 × Mat2) where
  toSubmodule := psLie.toSubmodule ⊓ (LinearMap.ker (orbitMatAt X)).restrictScalars ℝ
  lie_mem' hx hy := ⟨psLie.lie_mem hx.1 hy.1, (fixLieAt X).lie_mem hx.2 hy.2⟩

theorem mem_stabLieAt_iff (X : Bidoublet) (x : Mat4 × Mat2) :
    x ∈ stabLieAt X ↔ x ∈ psLie ∧ act x.1 x.2 X = 0 :=
  Iff.rfl

theorem stabLieAt_vac : stabLieAt vac = stabLie := rfl

theorem toMat_mem_stabLieAt_iff (X : Bidoublet) (p : PSLie) :
    toMat p ∈ stabLieAt X ↔ p ∈ stabAt X := by
  rw [mem_stabLieAt_iff, mem_stabAt_iff]
  exact ⟨fun h => h.2, fun h => ⟨toMat_mem_psLie p, h⟩⟩

/-- **The two unbroken subalgebras at `X` are one**: unit 213's `stabAt X`, carried to matrices, is
`stabLieAt X` — unit 180's `map_stab_toMat`, without `X = vac`. -/
theorem map_stabAt_toMat (X : Bidoublet) : (stabAt X).map toMat = (stabLieAt X).toSubmodule := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (toMat_mem_stabLieAt_iff X p).mpr hp
  · intro hx
    refine ⟨ofMat x hx.1, ?_, toMat_ofMat x hx.1⟩
    exact (toMat_mem_stabLieAt_iff X _).mp (by rw [toMat_ofMat]; exact hx)

theorem finrank_stabLieAt (X : Bidoublet) :
    Module.finrank ℝ (stabLieAt X) = Module.finrank ℝ (stabAt X) := by
  change Module.finrank ℝ (stabLieAt X).toSubmodule = _
  rw [← map_stabAt_toMat,
    ← (Submodule.equivMapOfInjective toMat toMat_injective (stabAt X)).finrank_eq]

/-- **The whole group's Lie algebra is unit 180's `psLie`.** -/
theorem matLie_top_eq : matLie ⊤ = (psLie : Set (Mat4 × Mat2)) := by
  ext M
  rw [mem_matLie_top_iff]
  constructor
  · rintro ⟨p, h1, h2⟩
    have hM : toMat p = M := Prod.ext h1 h2
    rw [← hM]
    exact toMat_mem_psLie p
  · intro hM
    exact ⟨ofMat M hM, congrArg Prod.fst (toMat_ofMat M hM), congrArg Prod.snd (toMat_ofMat M hM)⟩

/-- **THE UNBROKEN GROUP'S LIE ALGEBRA AT ANY FIRST-STAGE VACUUM IS THE LIE SUBALGEBRA
`stabLieAt X`**: unit 217's `matLie (Stab X)` is closed under the commutator. -/
theorem matLie_stabilizer_eq (X : Bidoublet) :
    matLie (MulAction.stabilizer Stage1Group X) = (stabLieAt X : Set (Mat4 × Mat2)) := by
  ext M
  rw [mem_matLie_stabilizer_iff]
  constructor
  · rintro ⟨p, hp, h1, h2⟩
    have hM : toMat p = M := Prod.ext h1 h2
    rw [← hM]
    exact (toMat_mem_stabLieAt_iff X p).mpr hp
  · intro hM
    have hp := (toMat_mem_stabLieAt_iff X (ofMat M hM.1)).mp (by rw [toMat_ofMat]; exact hM)
    exact ⟨ofMat M hM.1, hp, congrArg Prod.fst (toMat_ofMat M hM.1),
      congrArg Prod.snd (toMat_ofMat M hM.1)⟩

/-- **THE UNBROKEN GROUP'S LIE ALGEBRA HAS DIMENSION NINE, SIX OR FOUR**, by unit 212's three
cases. -/
theorem finrank_stabLieAt_trichotomy (X : Bidoublet) (hX : X ≠ 0) :
    (X.rank = 1 ∧ Module.finrank ℝ (stabLieAt X) = 9) ∨
    (X.rank = 2 ∧ (∃ c : ℂ, Xᴴ * X = c • 1) ∧ Module.finrank ℝ (stabLieAt X) = 6) ∨
    (X.rank = 2 ∧ (¬ ∃ c : ℂ, Xᴴ * X = c • 1) ∧ Module.finrank ℝ (stabLieAt X) = 4) := by
  simp only [finrank_stabLieAt]
  exact finrank_stabAt_trichotomy X hX

/-- **Two nonzero vacua leave isomorphic unbroken groups exactly when the groups' Lie algebras have
the same dimension.** -/
theorem nonempty_stabilizer_equiv_iff_finrank_stabLieAt_eq (X Y : Bidoublet) (hX : X ≠ 0)
    (hY : Y ≠ 0) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* MulAction.stabilizer Stage1Group Y) ↔
      Module.finrank ℝ (stabLieAt X) = Module.finrank ℝ (stabLieAt Y) := by
  rw [finrank_stabLieAt, finrank_stabLieAt]
  exact nonempty_stabilizer_equiv_iff_finrank_eq X Y hX hY

end

end PatiSalamUnbrokenLieAlgebra
