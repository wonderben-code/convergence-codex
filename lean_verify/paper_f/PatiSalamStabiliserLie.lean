/-
  PatiSalamStabiliserLie: the stabiliser of the vacuum is a LIE SUBALGEBRA, and it is `u(3)` AS A
  LIE ALGEBRA — the bracket that units 178–179 did not carry

  Campaign 3 hardening unit 180 (20 September 2026). Spine link L15 (Higgs sector).

  WHY. `PatiSalamStabiliserDimension` (unit 179) identified the vacuum's stabiliser with the
  skew-adjoint `3 × 3` matrices as a REAL VECTOR SPACE and said so in its NOT list: *"`u(3)` is
  reached as a real vector space, not as a Lie algebra: `stabEquivU3` is `ℝ`-linear and no
  bracket is carried across it. `PSLie` has no `LieRing` instance and `stab` is a `Submodule`"*.
  This file carries the bracket. It works at the matrix level, where Mathlib supplies the
  brackets — `Mathlib.Algebra.Lie.Prod` for `gl(4) ⊕ gl(2)`, `Ring.lie_def` for matrices — and
  the estate supplies `su(n)` as a Lie subalgebra (`TracelessSkewLie.tracelessSkewLie`).

  WHAT IS PROVED.
  (1) `fixLie : LieSubalgebra ℂ (gl(4) × gl(2))` — the FULL stabiliser of the vacuum in
      `gl(4) ⊕ gl(2)`, over `ℂ`, with no hypothesis on the matrices: `act_bracket` (unit 178)
      alone makes the kernel of the orbit map closed under the bracket. `psLie` is
      `su(4) ⊕ su(2)_R` as a Lie subalgebra over `ℝ` (the product of two `tracelessSkewLie`s),
      and `stabLie := psLie ⊓ fixLie` — the stabiliser inside `su(4) ⊕ su(2)_R` — is a Lie
      subalgebra over `ℝ`.
  (2) The bridge to unit 178: `toMat : PSLie →ₗ[ℝ] gl(4) × gl(2)` is injective with range
      `psLie` (`range_toMat`), and it carries `stab` onto `stabLie` (`map_stab_toMat`). So the
      two encodings of the stabiliser — the subtype product of units 178–179 and the matrix
      subalgebra here — are one object, and `finrank_stabLie = 9` is unit 179's count
      transported along the injection.
  (3) `u3Lie : LieSubalgebra ℝ (gl(3))` — `u(3)`, the anti-Hermitian `3 × 3` matrices under the
      commutator, closure by `TracelessSkewLie.lie_mem_skewSub`. `topBlock_mul_of_col`: the
      block of a product is the product of the blocks when the left factor's last column vanishes
      off the corner; `topBlock_lie`: hence the block of a bracket of two such matrices is the
      bracket of the blocks. `blockHom : stabLie →ₗ⁅ℝ⁆ u3Lie` — the block map is a morphism of
      Lie algebras on the stabiliser, because every stabiliser element has that column
      (`act_vac_eq_zero_iff`).
  (4) `stabLieEquivU3 : stabLie ≃ₗ⁅ℝ⁆ u3Lie` — **the stabiliser IS `u(3)` as a Lie algebra**,
      with inverse `C ↦ (blockdiag(C, −tr C), diag(tr C, −tr C))` (unit 179's `blockA`, `diagB`);
      the two inverse laws are unit 179's `topBlock_blockA` and `ofU3_toU3`, the latter
      transported along `map_stab_toMat`. `finrank_u3Lie = 9`.

  NOT PROVED, said exactly.
  • Nothing about the broken directions moves: `PSLie ⧸ stab` is a quotient of vector spaces
    (unit 179), not of Lie algebras — `stab` is a subalgebra, and no ideal property is claimed —
    and unit 179's exact sequence is one of vector spaces still.
  • No group: `u(3)` here is a Lie subalgebra of matrices; `U(3)`, its exponential, and any
    statement about the unbroken GROUP are absent, as `TracelessSkewLie`'s header records for
    `SU(n)` (Mathlib's `specialUnitaryGroup` is a `Submonoid` with no Lie algebra attached).
    ⚠ 20 September 2026 (hardening unit 188, `paper_f/SkewAdjointExponential.lean`): the exponential
    now exists — `expSU : traceless n → specialUnitaryGroup (Fin n) ℂ`, `exp_mem_unitaryGroup` for
    every skew-adjoint matrix (so `u(3)` exponentiates into `U(3)`), and `oneParam` for the
    one-parameter subgroups; statements about the unbroken GROUP as a group are still absent. The
    bullet is kept as written (`ERRATUM 94`).
    ⚠ 25 September 2026 (hardening unit 191, `paper_f/PatiSalamGaugeAction.lean`): the unbroken
    group is now NAMED — Mathlib's `MulAction.stabilizer` of the vacuum under `SU(4) × SU(2)_R`
    — and the algebra is read off it: `p ∈ stab` iff `oneParamG1 p t` lies in that stabiliser for
    every `t` (`mem_stab_iff_mem_stabilizer`). The stabiliser subgroup itself is not computed:
    its identification with `U(3)` is still absent. The bullet is kept as written (`ERRATUM 94`).
  • The vacuum direction is still a convention and nothing here is dynamics (units 178–179's
    bullets, unchanged).
  • `fixLie` is over `ℂ` and `stabLie` over `ℝ`; the two brackets agree because a product's
    `LieRing` does not see the scalars (`Prod.bracket_apply` is `rfl`), which is used, not
    assumed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `topBlock_mul_of_col` takes the LEFT
  factor's column condition only; `topBlock_lie` takes it for both matrices; `topBlock_skew` takes
  `Aᴴ = -A`; `ofMat` takes membership in `psLie`. `fixLie`'s closure takes nothing beyond
  membership. Every other declaration is hypothesis-free.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 32 names run against `paper_f`
  with `newnames_scan`'s regex before this header was written — `M4` was taken by `CascadeGNS`
  and became `Mat4`; the rest were free). The estate's block-Lie files are the COMPLEX story:
  `BlockLieHom.blockDiagHom` is `sl(p) ⊕ sl(q) ⊕ ℂ →ₗ⁅ℂ⁆ sl(p+q)` on `Fin p ⊕ Fin q`, and
  `BlockLieMorphism.lie_blockDiagOf` is the bracket of two block-diagonal embeddings; here the
  matrices live on `Fin 4` with the corner read through `fin3_to_fin4`, over `ℝ`, and the map
  goes the other way (extraction, `PatiSalamOffDiagonal.topBlock`). `TracelessSkewLie` builds
  `su(ι)` as a Lie subalgebra and records that Mathlib has no star-skew Lie algebra; `u3Lie` is
  the same construction without the trace condition, and is not in that file. The ambient `gl(4)`
  is `CascadeFoundation.CascadeAlgebra` — `Matrix (Fin 4) (Fin 4) ℂ` under its cascade name — and
  `Mat4` abbreviates THAT rather than re-spelling the type: the first draft re-spelled it and the
  duplicate-body scanner caught it on the first gate. `Mathlib.Algebra.Lie.Prod` in the WHY
  paragraph is a module path, not a declaration.
-/

import PatiSalamStabiliserDimension
import TracelessSkewLie
import Mathlib.Algebra.Lie.Prod

open Matrix TracelessSkewDimension TracelessSkewLie PatiSalamRightSector PatiSalamVacuumStabiliser
  PatiSalamStabiliserDimension PatiSalamOffDiagonal

namespace PatiSalamStabiliserLie

noncomputable section

/-- `gl(4, ℂ)` is the cascade's own algebra, `CascadeFoundation.CascadeAlgebra` — the same type,
named here for its Lie role (and not re-spelled: `dupbody_scan` found the first draft's copy). -/
abbrev Mat4 := CascadeAlgebra

/-- `gl(2, ℂ)`. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

theorem act_zero (A : Mat4) (B : Mat2) : act A B 0 = 0 := by simp [act]

/-- The orbit map on the whole of `gl(4) ⊕ gl(2)`, complex-linear. -/
def orbitMat : Mat4 × Mat2 →ₗ[ℂ] Bidoublet where
  toFun x := act x.1 x.2 vac
  map_add' x y := by
    simp only [act, Prod.fst_add, Prod.snd_add, Matrix.transpose_add, Matrix.add_mul,
      Matrix.mul_add]
    abel
  map_smul' c x := by
    simp only [act, Prod.smul_fst, Prod.smul_snd, Matrix.transpose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_add, RingHom.id_apply]

theorem orbitMat_apply (x : Mat4 × Mat2) : orbitMat x = act x.1 x.2 vac := rfl

/-- **THE FULL STABILISER OF THE VACUUM IN `gl(4) ⊕ gl(2)` IS A LIE SUBALGEBRA**, over `ℂ` and
with no hypothesis on the matrices: `act_bracket` alone. -/
def fixLie : LieSubalgebra ℂ (Mat4 × Mat2) where
  toSubmodule := LinearMap.ker orbitMat
  lie_mem' {x y} hx hy := by
    have hx' : act x.1 x.2 vac = 0 := hx
    have hy' : act y.1 y.2 vac = 0 := hy
    change act ⁅x.1, y.1⁆ ⁅x.2, y.2⁆ vac = 0
    rw [act_bracket, hx', hy', act_zero, act_zero, sub_zero]

theorem mem_fixLie_iff (x : Mat4 × Mat2) : x ∈ fixLie ↔ act x.1 x.2 vac = 0 := Iff.rfl

/-- `su(4) ⊕ su(2)_R` as a Lie subalgebra of `gl(4) ⊕ gl(2)` over `ℝ`, from the estate's
`TracelessSkewLie.tracelessSkewLie`. -/
def psLie : LieSubalgebra ℝ (Mat4 × Mat2) where
  toSubmodule :=
    (tracelessSkewLie (Fin 4)).toSubmodule.prod (tracelessSkewLie (Fin 2)).toSubmodule
  lie_mem' hx hy :=
    ⟨(tracelessSkewLie (Fin 4)).lie_mem hx.1 hy.1, (tracelessSkewLie (Fin 2)).lie_mem hx.2 hy.2⟩

theorem mem_psLie_iff (x : Mat4 × Mat2) :
    x ∈ psLie ↔ (x.1ᴴ = -x.1 ∧ Matrix.trace x.1 = 0) ∧ (x.2ᴴ = -x.2 ∧ Matrix.trace x.2 = 0) :=
  Iff.rfl

/-- **THE STABILISER OF THE VACUUM IN `su(4) ⊕ su(2)_R`, AS A LIE SUBALGEBRA OVER `ℝ`.** -/
def stabLie : LieSubalgebra ℝ (Mat4 × Mat2) where
  toSubmodule := psLie.toSubmodule ⊓ (LinearMap.ker orbitMat).restrictScalars ℝ
  lie_mem' hx hy := ⟨psLie.lie_mem hx.1 hy.1, fixLie.lie_mem hx.2 hy.2⟩

theorem mem_stabLie_iff (x : Mat4 × Mat2) : x ∈ stabLie ↔ x ∈ psLie ∧ act x.1 x.2 vac = 0 :=
  Iff.rfl

/-! ## 2. The bridge to unit 178's `stab` -/

/-- The matrices of an element of `PSLie`. -/
def toMat : PSLie →ₗ[ℝ] Mat4 × Mat2 where
  toFun p := (mat4 p.1, mat2 p.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toMat_apply (p : PSLie) : toMat p = (mat4 p.1, mat2 p.2) := rfl

theorem toMat_injective : Function.Injective toMat := by
  intro p q h
  have h1 : mat4 p.1 = mat4 q.1 := congrArg Prod.fst h
  have h2 : mat2 p.2 = mat2 q.2 := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext (Subtype.ext h1)) (Subtype.ext (Subtype.ext h2))

theorem toMat_mem_psLie (p : PSLie) : toMat p ∈ psLie :=
  ⟨⟨skewAdjoint.mem_iff.mp p.1.1.2, trace_eq_zero_of_mem_traceless p.1.2⟩,
   ⟨skewAdjoint.mem_iff.mp p.2.1.2, trace_eq_zero_of_mem_traceless p.2.2⟩⟩

/-- Every element of `su(4) ⊕ su(2)_R` at the matrix level comes from `PSLie`. -/
def ofMat (x : Mat4 × Mat2) (hx : x ∈ psLie) : PSLie :=
  (⟨⟨x.1, skewAdjoint.mem_iff.mpr hx.1.1⟩, by
      have ht : Matrix.trace x.1 = 0 := hx.1.2
      simp [traceless, traceIm, ht]⟩,
   ⟨⟨x.2, skewAdjoint.mem_iff.mpr hx.2.1⟩, by
      have ht : Matrix.trace x.2 = 0 := hx.2.2
      simp [traceless, traceIm, ht]⟩)

theorem toMat_ofMat (x : Mat4 × Mat2) (hx : x ∈ psLie) : toMat (ofMat x hx) = x := rfl

theorem range_toMat : LinearMap.range toMat = psLie.toSubmodule := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact toMat_mem_psLie p
  · intro hx
    exact ⟨ofMat x hx, toMat_ofMat x hx⟩

theorem toMat_mem_stabLie_iff (p : PSLie) : toMat p ∈ stabLie ↔ p ∈ stab := by
  rw [mem_stabLie_iff]
  exact ⟨fun h => h.2, fun h => ⟨toMat_mem_psLie p, h⟩⟩

/-- **THE TWO STABILISERS ARE ONE**: unit 178's `stab`, carried to matrices, is `stabLie`. -/
theorem map_stab_toMat : stab.map toMat = stabLie.toSubmodule := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (toMat_mem_stabLie_iff p).mpr hp
  · intro hx
    refine ⟨ofMat x hx.1, ?_, toMat_ofMat x hx.1⟩
    exact (toMat_mem_stabLie_iff _).mp (by rw [toMat_ofMat]; exact hx)

theorem finrank_stabLie : Module.finrank ℝ stabLie = 9 := by
  change Module.finrank ℝ stabLie.toSubmodule = 9
  rw [← map_stab_toMat, ← (Submodule.equivMapOfInjective toMat toMat_injective stab).finrank_eq,
    finrank_stab]

/-! ## 3. `u(3)` as a Lie algebra, and the stabiliser is it -/

/-- **`u(3)` AS A LIE SUBALGEBRA OF `gl(3)` OVER `ℝ`**: the anti-Hermitian `3 × 3` matrices with
the commutator; closure is `TracelessSkewLie.lie_mem_skewSub`. -/
def u3Lie : LieSubalgebra ℝ (Matrix (Fin 3) (Fin 3) ℂ) where
  toSubmodule := skewSub (Fin 3)
  lie_mem' := lie_mem_skewSub

theorem mem_u3Lie_iff (C : Matrix (Fin 3) (Fin 3) ℂ) : C ∈ u3Lie ↔ Cᴴ = -C := Iff.rfl

theorem topBlock_sub (X Y : Mat4) : topBlock (X - Y) = topBlock X - topBlock Y := rfl

/-- The block of a product is the product of the blocks when the left factor's last column
vanishes off the corner. -/
theorem topBlock_mul_of_col {A A' : Mat4} (hA : ∀ i, i ≠ 3 → A i 3 = 0) :
    topBlock (A * A') = topBlock A * topBlock A' := by
  ext i j
  simp only [topBlock_apply, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
  rw [hA _ (fin3_to_fin4_ne_three i), zero_mul, add_zero]
  rfl

theorem topBlock_lie {A A' : Mat4} (hA : ∀ i, i ≠ 3 → A i 3 = 0)
    (hA' : ∀ i, i ≠ 3 → A' i 3 = 0) :
    topBlock ⁅A, A'⁆ = ⁅topBlock A, topBlock A'⁆ := by
  rw [Ring.lie_def, Ring.lie_def, topBlock_sub, topBlock_mul_of_col hA, topBlock_mul_of_col hA']

theorem topBlock_skew {A : Mat4} (hA : Aᴴ = -A) : (topBlock A)ᴴ = -(topBlock A) := by
  ext i j
  rw [Matrix.conjTranspose_apply, Matrix.neg_apply, topBlock_apply, topBlock_apply]
  have h := congrFun (congrFun hA (fin3_to_fin4 i)) (fin3_to_fin4 j)
  rwa [Matrix.conjTranspose_apply, Matrix.neg_apply] at h

/-- The block map on the stabiliser, as a morphism of Lie algebras. -/
def blockHom : stabLie →ₗ⁅ℝ⁆ u3Lie where
  toFun x := ⟨topBlock x.1.1, topBlock_skew x.2.1.1.1⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  map_lie' {x y} := Subtype.ext
    (topBlock_lie ((act_vac_eq_zero_iff _ _).mp x.2.2).1 ((act_vac_eq_zero_iff _ _).mp y.2.2).1)

theorem blockHom_apply (x : stabLie) : (blockHom x : Matrix (Fin 3) (Fin 3) ℂ) = topBlock x.1.1 :=
  rfl

/-- The inverse: `C ↦ (blockdiag(C, −tr C), diag(tr C, −tr C))`, landing in the stabiliser. -/
def blockInv (C : u3Lie) : stabLie :=
  ⟨(blockA C.1, diagB C.1), by
    have hC : star (C.1 : Matrix (Fin 3) (Fin 3) ℂ) = -C.1 := C.2
    exact ⟨⟨⟨blockA_skew hC, trace_blockA _⟩, ⟨diagB_skew hC, trace_diagB _⟩⟩,
      ofU3_mem_stab ⟨C.1, skewAdjoint.mem_iff.mpr hC⟩⟩⟩

/-- **THE STABILISER IS `u(3)` AS A LIE ALGEBRA**: the block map is an isomorphism of Lie algebras
over `ℝ`, with inverse `C ↦ (blockdiag(C, −tr C), diag(tr C, −tr C))`. -/
def stabLieEquivU3 : stabLie ≃ₗ⁅ℝ⁆ u3Lie :=
  { blockHom with
    invFun := blockInv
    left_inv := fun x => by
      apply Subtype.ext
      have hx : x.1 ∈ stab.map toMat := by
        rw [map_stab_toMat]
        exact x.2
      obtain ⟨p, hp, hpx⟩ := hx
      change (blockA (topBlock x.1.1), diagB (topBlock x.1.1)) = x.1
      rw [← hpx]
      change toMat (ofU3 (toU3 p)) = toMat p
      rw [ofU3_toU3 p hp]
    right_inv := fun C => Subtype.ext (topBlock_blockA C.1) }

theorem finrank_u3Lie : Module.finrank ℝ u3Lie = 9 := by
  rw [← stabLieEquivU3.toLinearEquiv.finrank_eq, finrank_stabLie]

end

end PatiSalamStabiliserLie
