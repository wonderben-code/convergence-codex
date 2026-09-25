/-
  PatiSalamBrokenCount.lean — THE NUMBER OF BROKEN GENERATORS DECIDES THE FIRST STAGE. Unit 212
  classified the groups a nonzero first-stage vacuum `X` leaves: `U(3)` at rank one, `SU(2) × SU(2)`
  at rank two when `Xᴴ X` is a multiple of the identity, `SU(2) × U(1)` otherwise. This file counts
  generators. The unbroken subalgebra `stabAt X` — the elements `(A, B)` of `su(4) ⊕ su(2)` with
  `A X + X Bᵀ = 0`, unit 178's `stab` at `X = vac` — has dimension nine, six or four in the three
  cases (`finrank_stabAt_trichotomy`), so the number of broken generators is nine, twelve or
  fourteen; and two nonzero vacua leave isomorphic unbroken groups if and only if they break the
  same number (`nonempty_stabilizer_equiv_iff_finrank_broken_eq`). The published tree's §6.8 says
  the breaking pattern *"is determined by Goldstone counting"*. What is now a theorem at the first
  stage is the linear-algebra half of that sentence: the count of broken generators decides which of
  the three groups a given vacuum leaves. That those generators are massless Goldstone modes is
  Goldstone's theorem, which needs a Lagrangian and a potential the estate does not have (units 179
  and 184); and the count does not choose the vacuum.

  SPINE link L15 (Higgs sector, PARTIAL); `ASSUMPTIONS_LEDGER` 60. Hardening unit 213, 2026-09-25.

  WHAT IS PROVED.
  (1) The subalgebra at any vacuum. `orbitMapAt X`, the `ℝ`-linear map `(A, B) ↦ A X + X Bᵀ`, and
      **`stabAt X`**, its kernel (`mem_stabAt_iff`; `stabAt_vac`: at `vac` it is unit 178's `stab`);
      `act_smul_right`, `stabAt_smul`: a nonzero multiple has the same subalgebra; and
      **`brokenEquivTangentAt`**: the broken directions `PSLie ⧸ stabAt X` are the tangent
      directions of the orbit at every vacuum — unit 184's `stage1EquivTangent`, which is `X = vac`.
  (2) Gauge transport. `conj_mem_skewAdjoint`, `trace_conj_unitary`, `conjTL` (conjugation by a
      unitary on the traceless skew-Hermitian matrices) and `conjTL_injective`; **`adPS`**, the
      adjoint action of a gauge transformation on `su(4) ⊕ su(2)`, with **`act_adPS`**:
      `act (Ad_g p) (g • X) = G · act p X · Hᵀ`; so `adPS_mem_stabAt`, `adPS_injective`,
      `finrank_stabAt_le_smul` and **`finrank_stabAt_smul`**: the dimension is a gauge invariant.
      **`finrank_stabAt_of_rank_eq_one`**: nine, by unit 203's orbit and unit 179's `finrank_stab`.
  (3) Rank two. For invertible `D`, an element `(A, B)` of `stabAt (vac2 · D)` has
      `A = diag(a, −D Bᵀ D⁻¹)` (**`exists_stabParam_eq`**; the lower-left block is emptied by
      skewness, where unit 211 used unitarity), and `−D Bᵀ D⁻¹` is skew exactly when `Bᵀ` commutes
      with `Dᴴ D` (**`star_lowBlk_iff`**). So **`stabAtVac2Equiv`**:
      `su(2) × commT D ≃ₗ[ℝ] stabAt (vac2 · D)` by `(a, B) ↦ (diag(a, −D Bᵀ D⁻¹), B)` (`paramTL`,
      `stabParam`, `stabParam_mem`, `stabParam_injective`), with `commT D` the elements of `su(2)`
      whose transpose commutes with `Dᴴ D`; **`finrank_stabAt_vac2`**: `3 + dim commT D`; and
      **`finrank_stabAt_vac2_of_scalar`**: six when `Dᴴ D` is a multiple of the identity. The block
      lemmas: `lowBlk`, `mat2_skew`, `mat4_skew`, `trace_mat2`, `trace_mat4`,
      `star_transpose_of_skew`, `trace_lowBlk`, `trace_blk2`, `blk2_neg`, `blk2_add`, `blk2_smul`,
      `lowBlk_add`, `real_smul_eq_complex_smul`, `lowBlk_smul`, `blk2_skew`.
  (4) Unequal singular values. **`eq_smul_of_comm`**: a traceless skew-Hermitian `2 × 2` matrix
      commuting with a nonzero traceless Hermitian `N` is `t · i N` for a real `t` — from the
      entries of the commutation (unit 211's `comm_entries`), by cases on `N₀₀`. With `tlPart` (the
      traceless part), `tlPart_11`, `star_tlPart`, `comm_tlPart_iff`, `tlPart_ne_zero`,
      `star_conjTranspose_mul_self`, the generator `genT D` (`genT_mem`, `genT_ne_zero`):
      **`commT_eq_span`**, `finrank_commT_of_not_scalar` (one) and
      **`finrank_stabAt_vac2_of_not_scalar`**: four.
  (5) Every vacuum. `scalar_gram_iff_of_smul_eq` (unit 212's `scalar_iff_of_smul_eq` and
      `scalar_conjTranspose_mul_iff`), `finrank_stabAt_of_scalar`, `finrank_stabAt_of_not_scalar`,
      **`finrank_stabAt_trichotomy`**; `finrank_broken_add`: broken plus unbroken is eighteen (unit
      179's `finrank_PSLie`); `finrank_stabAt_eq_nine_iff`, `finrank_stabAt_eq_six_iff`,
      `finrank_stabAt_eq_four_iff`: the dimension and the group determine each other (unit 212's
      trichotomy and non-isomorphisms); **`nonempty_stabilizer_equiv_iff_finrank_eq`** and
      **`nonempty_stabilizer_equiv_iff_finrank_broken_eq`**.

  NOT PROVED, said exactly.
  • Goldstone's theorem proper: that the broken directions are massless modes needs a Lagrangian and
    a potential on the Higgs fields (units 179 and 184's NOT lists). The count here is of broken
    generators, and nothing in this file is named for Goldstone.
  • That `stabAt X` is the Lie algebra of the unbroken group. It is the kernel of the infinitesimal
    action; no smooth structure is put on any group (unit 209's reason), so the link between the two
    is not a theorem here, and each dimension above is the kernel's.
  • Which vacuum: the count decides the group once the vacuum is given, and does not choose it —
    that is a potential's minimum, and there is no potential (`ASSUMPTIONS_LEDGER` 60).
  • The second stage, and the electroweak count, beyond unit 184.
  • Whether `stabAt X` determines the line through `X` (unit 207's Lie-algebra bullet): not
    addressed.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `stabAt_smul` takes `c ≠ 0`;
  `trace_conj_unitary`, `conjTL` and `conjTL_injective` take a unitary `G`; `adPS_mem_stabAt` takes
  `p ∈ stabAt X`; `finrank_stabAt_of_rank_eq_one` takes `X.rank = 1`; `star_transpose_of_skew`,
  `blk2_skew` and `star_lowBlk_iff` take skewness, the last also `IsUnit D.det`; `trace_lowBlk`,
  `paramTL`, `stabParam`, `stabParam_mem`, `stabParam_injective`, `exists_stabParam_eq`,
  `stabAtVac2Equiv` and `finrank_stabAt_vac2` take `IsUnit D.det`, `exists_stabParam_eq` also
  membership; `finrank_stabAt_vac2_of_scalar` takes `IsUnit D.det` and `Dᴴ D = c • 1`, and
  `finrank_stabAt_vac2_of_not_scalar` `IsUnit D.det` and its negation, as `genT_ne_zero`,
  `commT_eq_span` and `finrank_commT_of_not_scalar` do the negation; `eq_smul_of_comm` takes
  `N ≠ 0`, the two trace conditions, Hermitian `N`, skew `C` and commutation; `star_tlPart` takes
  Hermitian `P`, `tlPart_ne_zero` `P` not a multiple of the identity; `scalar_gram_iff_of_smul_eq`
  takes `IsUnit D.det` and `g • X = vac2 * D`; `finrank_stabAt_of_scalar` and
  `finrank_stabAt_of_not_scalar` take `X.rank = 2` and the hypothesis on `Xᴴ X`; the three
  `finrank_stabAt_eq_…_iff`, `finrank_stabAt_trichotomy` and the two headline theorems take `X ≠ 0`,
  the headlines also `Y ≠ 0`. The rest take nothing.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 66 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list. One was taken, `trace_conj` (`LovelockInnerInvariant`), and was renamed `trace_conj_unitary`
  before writing. The nearest statements: unit 178's `orbitMap` and `stab`, which `orbitMapAt` and
  `stabAt` generalise (`stabAt_vac` is `rfl`); unit 179's `finrank_stab`, `finrank_PSLie` and
  `stabEquivU3` (the rank-one analogue of `stabAtVac2Equiv`), used or mirrored; unit 184's
  `stage1EquivTangent`, the case `X = vac` of `brokenEquivTangentAt`; unit 211's `blk2` API,
  `blk2_mul_vac2` and `comm_entries`, used; unit 212's `stabilizer_trichotomy` and its three
  non-isomorphisms, used.

  0 sorry. 0 new axioms. `#print axioms` on all 66 declarations below: each is
  `[propext, Classical.choice, Quot.sound]`.
-/
import PatiSalamFirstStageClassification
import PatiSalamStabiliserDimension
set_option linter.mathlibStandardSet true

open Matrix TracelessSkewDimension

namespace PatiSalamBrokenCount

open PatiSalamVacuumStabiliser PatiSalamGaugeAction PatiSalamStabiliserGroup PatiSalamRankTwoVacuum
  PatiSalamRankTwoStabiliser PatiSalamStabiliserDimension PatiSalamVacuumOrbit
  PatiSalamFirstStageClassification

/-! ## 1. The unbroken subalgebra at any vacuum -/

/-- The orbit map at a first-stage vacuum `X`: `(A, B) ↦ A X + X Bᵀ`, `ℝ`-linear. -/
noncomputable def orbitMapAt (X : Bidoublet) : PSLie →ₗ[ℝ] Bidoublet where
  toFun p := act (mat4 p.1) (mat2 p.2) X
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, mat4, mat2, Submodule.coe_add, AddSubgroup.coe_add, act,
      Matrix.add_mul, Matrix.mul_add, Matrix.transpose_add]
    abel
  map_smul' r p := by
    simp only [Prod.smul_fst, Prod.smul_snd, mat4, mat2, Submodule.coe_smul, skewAdjoint.val_smul,
      act, Matrix.smul_mul, Matrix.mul_smul, Matrix.transpose_smul, smul_add, RingHom.id_apply]

/-- **The unbroken subalgebra at `X`**, as a kernel; at `vac` it is unit 178's `stab`. -/
noncomputable def stabAt (X : Bidoublet) : Submodule ℝ PSLie := LinearMap.ker (orbitMapAt X)

theorem mem_stabAt_iff (X : Bidoublet) (p : PSLie) :
    p ∈ stabAt X ↔ act (mat4 p.1) (mat2 p.2) X = 0 :=
  LinearMap.mem_ker

theorem stabAt_vac : stabAt vac = stab := rfl

/-- **The broken directions are the tangent directions of the orbit, at every vacuum** — unit
184's `stage1EquivTangent`, which is the case `X = vac`, by the first isomorphism theorem. -/
noncomputable def brokenEquivTangentAt (X : Bidoublet) :
    (PSLie ⧸ stabAt X) ≃ₗ[ℝ] LinearMap.range (orbitMapAt X) :=
  (orbitMapAt X).quotKerEquivRange

theorem act_smul_right (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ)
    (X : Bidoublet) : act A B (c • X) = c • act A B X := by
  simp only [act, Matrix.mul_smul, Matrix.smul_mul, smul_add]

/-- A nonzero multiple of a vacuum has the same unbroken subalgebra. -/
theorem stabAt_smul {c : ℂ} (hc : c ≠ 0) (X : Bidoublet) : stabAt (c • X) = stabAt X := by
  ext p
  rw [mem_stabAt_iff, mem_stabAt_iff, act_smul_right, smul_eq_zero, or_iff_right hc]

/-! ## 2. Gauge transport: the dimension is an orbit invariant -/

theorem conj_mem_skewAdjoint {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ)) :
    G * A * star G ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) := by
  rw [skewAdjoint.mem_iff] at hA ⊢
  rw [Matrix.star_mul, Matrix.star_mul, star_star, hA, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc]

theorem trace_conj_unitary {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G ∈ unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : trace (G * A * star G) = trace A := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, (Matrix.mem_unitaryGroup_iff').mp hG,
    Matrix.one_mul]

/-- Conjugation by a unitary, on the traceless skew-Hermitian matrices. -/
noncomputable def conjTL {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G ∈ unitaryGroup (Fin n) ℂ) :
    traceless n →ₗ[ℝ] traceless n where
  toFun A := ⟨⟨G * (A : Matrix (Fin n) (Fin n) ℂ) * star G, conj_mem_skewAdjoint G A.1.2⟩, by
    have h := A.2
    change (Matrix.trace (G * (A : Matrix (Fin n) (Fin n) ℂ) * star G)).im = 0
    rw [trace_conj_unitary hG]
    exact h⟩
  map_add' A A' := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_add, AddSubgroup.coe_add, Matrix.mul_add, Matrix.add_mul]
  map_smul' r A := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_smul, skewAdjoint.val_smul, Matrix.mul_smul, Matrix.smul_mul,
      RingHom.id_apply]

theorem conjTL_injective {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G ∈ unitaryGroup (Fin n) ℂ) :
    Function.Injective (conjTL hG) := by
  intro A A' h
  have h' := congrArg (fun x : traceless n => star G * x.1.1 * G) h
  simp only [conjTL, LinearMap.coe_mk, AddHom.coe_mk] at h'
  have hGG := (Matrix.mem_unitaryGroup_iff').mp hG
  simp only [← Matrix.mul_assoc, hGG, Matrix.one_mul] at h'
  simp only [Matrix.mul_assoc, hGG, Matrix.mul_one] at h'
  exact Subtype.ext (Subtype.ext h')

/-- The adjoint action of `g` on `su(4) ⊕ su(2)`. -/
noncomputable def adPS (g : Stage1Group) : PSLie →ₗ[ℝ] PSLie :=
  LinearMap.prodMap (conjTL (mem_specialUnitaryGroup_iff.mp g.1.2).1)
    (conjTL (mem_specialUnitaryGroup_iff.mp g.2.2).1)

theorem act_adPS (g : Stage1Group) (p : PSLie) (X : Bidoublet) :
    act (mat4 (adPS g p).1) (mat2 (adPS g p).2) (g • X)
      = (g.1 : Matrix (Fin 4) (Fin 4) ℂ) * act (mat4 p.1) (mat2 p.2) X
        * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ := by
  have hG := (Matrix.mem_unitaryGroup_iff').mp (mem_specialUnitaryGroup_iff.mp g.1.2).1
  have hH := (Matrix.mem_unitaryGroup_iff').mp (mem_specialUnitaryGroup_iff.mp g.2.2).1
  have hHt : (g.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ * (star (g.2 : Matrix (Fin 2) (Fin 2) ℂ))ᵀ = 1 := by
    rw [← transpose_mul, hH, transpose_one]
  change act ((g.1 : Matrix (Fin 4) (Fin 4) ℂ) * mat4 p.1 * star (g.1 : Matrix (Fin 4) (Fin 4) ℂ))
    ((g.2 : Matrix (Fin 2) (Fin 2) ℂ) * mat2 p.2 * star (g.2 : Matrix (Fin 2) (Fin 2) ℂ))
    ((g.1 : Matrix (Fin 4) (Fin 4) ℂ) * X * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) = _
  simp only [act, transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  congr 1
  · rw [← Matrix.mul_assoc (star (g.1 : Matrix (Fin 4) (Fin 4) ℂ)), hG, Matrix.one_mul]
  · rw [← Matrix.mul_assoc ((g.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ), hHt, Matrix.one_mul]

theorem adPS_mem_stabAt {g : Stage1Group} {X : Bidoublet} {p : PSLie} (hp : p ∈ stabAt X) :
    adPS g p ∈ stabAt (g • X) := by
  rw [mem_stabAt_iff] at hp ⊢
  rw [act_adPS, hp, Matrix.mul_zero, Matrix.zero_mul]

theorem adPS_injective (g : Stage1Group) : Function.Injective (adPS g) :=
  fun _ _ h => Prod.ext
    (conjTL_injective (mem_specialUnitaryGroup_iff.mp g.1.2).1 (congrArg Prod.fst h))
    (conjTL_injective (mem_specialUnitaryGroup_iff.mp g.2.2).1 (congrArg Prod.snd h))

theorem finrank_stabAt_le_smul (g : Stage1Group) (X : Bidoublet) :
    Module.finrank ℝ (stabAt X) ≤ Module.finrank ℝ (stabAt (g • X)) :=
  LinearMap.finrank_le_finrank_of_injective (f := (adPS g).restrict fun _ hp => adPS_mem_stabAt hp)
    fun _ _ h => Subtype.ext (adPS_injective g (congrArg Subtype.val h))

/-- **The dimension of the unbroken subalgebra is a gauge invariant.** -/
theorem finrank_stabAt_smul (g : Stage1Group) (X : Bidoublet) :
    Module.finrank ℝ (stabAt (g • X)) = Module.finrank ℝ (stabAt X) := by
  refine le_antisymm ?_ (finrank_stabAt_le_smul g X)
  have := finrank_stabAt_le_smul g⁻¹ (g • X)
  rwa [inv_smul_smul] at this

/-- **Rank one: nine unbroken generators.** -/
theorem finrank_stabAt_of_rank_eq_one (X : Bidoublet) (hX : X.rank = 1) :
    Module.finrank ℝ (stabAt X) = 9 := by
  obtain ⟨g, r, hr, rfl⟩ := (rank_eq_one_iff_mem_orbit X).mp hX
  rw [stabAt_smul (by exact_mod_cast hr.ne'), finrank_stabAt_smul, stabAt_vac, finrank_stab]

/-! ## 3. Rank two: `su(2)` times the part of `su(2)` whose transpose commutes with `Dᴴ D` -/

/-- The lower block an element of the unbroken subalgebra at `vac2 · D` must have: `−D Bᵀ D⁻¹`. -/
noncomputable def lowBlk (D B : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  -(D * Bᵀ * D⁻¹)

/-- The elements of `su(2)` whose transpose commutes with `Dᴴ D`. -/
noncomputable def commT (D : Matrix (Fin 2) (Fin 2) ℂ) : Submodule ℝ (traceless 2) where
  carrier := {B | (mat2 B)ᵀ * (Dᴴ * D) = (Dᴴ * D) * (mat2 B)ᵀ}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, mat2, Submodule.coe_add, AddSubgroup.coe_add, transpose_add,
      Matrix.add_mul, Matrix.mul_add] at *
    rw [ha, hb]
  zero_mem' := by simp [mat2]
  smul_mem' := by
    intro r b hb
    simp only [Set.mem_setOf_eq, mat2, Submodule.coe_smul, skewAdjoint.val_smul, transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul] at *
    rw [hb]

theorem mat2_skew (B : traceless 2) : star (mat2 B) = -mat2 B :=
  skewAdjoint.mem_iff.mp B.1.2

theorem mat4_skew (A : traceless 4) : star (mat4 A) = -mat4 A :=
  skewAdjoint.mem_iff.mp A.1.2

theorem trace_mat2 (B : traceless 2) : trace (mat2 B) = 0 :=
  trace_eq_zero_of_mem_traceless B.2

theorem trace_mat4 (A : traceless 4) : trace (mat4 A) = 0 :=
  trace_eq_zero_of_mem_traceless A.2

theorem star_transpose_of_skew {B : Matrix (Fin 2) (Fin 2) ℂ} (hB : star B = -B) :
    star Bᵀ = -Bᵀ := by
  rw [star_eq_conjTranspose, transpose_conjTranspose, ← conjTranspose_transpose,
    ← star_eq_conjTranspose, hB, transpose_neg]

/-- The skewness of `−D Bᵀ D⁻¹` is the commutation of `Bᵀ` with `Dᴴ D`. -/
theorem star_lowBlk_iff {D B : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (hB : star B = -B) :
    star (lowBlk D B) = -lowBlk D B ↔ Bᵀ * (Dᴴ * D) = (Dᴴ * D) * Bᵀ := by
  have hBt := star_transpose_of_skew hB
  have h1 : D * D⁻¹ = 1 := Matrix.mul_nonsing_inv D hD
  have h2 : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hD
  have h3 : (D⁻¹)ᴴ * Dᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have h4 : Dᴴ * (D⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have hs : star (lowBlk D B) = (D⁻¹)ᴴ * Bᵀ * Dᴴ := by
    rw [lowBlk, star_neg, star_eq_conjTranspose, conjTranspose_mul, conjTranspose_mul,
      ← star_eq_conjTranspose Bᵀ, hBt]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    exact neg_neg _
  have hn : -lowBlk D B = D * Bᵀ * D⁻¹ := neg_neg _
  rw [hs, hn]
  constructor
  · intro h
    calc Bᵀ * (Dᴴ * D) = (Dᴴ * (D⁻¹)ᴴ) * Bᵀ * (Dᴴ * D) := by rw [h4, Matrix.one_mul]
      _ = Dᴴ * ((D⁻¹)ᴴ * Bᵀ * Dᴴ) * D := by simp only [Matrix.mul_assoc]
      _ = Dᴴ * (D * Bᵀ * D⁻¹) * D := by rw [h]
      _ = Dᴴ * D * Bᵀ * (D⁻¹ * D) := by simp only [Matrix.mul_assoc]
      _ = (Dᴴ * D) * Bᵀ := by rw [h2, Matrix.mul_one]
  · intro h
    calc (D⁻¹)ᴴ * Bᵀ * Dᴴ = (D⁻¹)ᴴ * Bᵀ * Dᴴ * (D * D⁻¹) := by rw [h1, Matrix.mul_one]
      _ = (D⁻¹)ᴴ * (Bᵀ * (Dᴴ * D)) * D⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (D⁻¹)ᴴ * ((Dᴴ * D) * Bᵀ) * D⁻¹ := by rw [h]
      _ = ((D⁻¹)ᴴ * Dᴴ) * D * Bᵀ * D⁻¹ := by simp only [Matrix.mul_assoc]
      _ = D * Bᵀ * D⁻¹ := by rw [h3, Matrix.one_mul]

theorem trace_lowBlk {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (B : Matrix (Fin 2) (Fin 2) ℂ) :
    trace (lowBlk D B) = -trace B := by
  rw [lowBlk, trace_neg, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul D hD,
    Matrix.one_mul, trace_transpose]

theorem trace_blk2 (a d : Matrix (Fin 2) (Fin 2) ℂ) : trace (blk2 a d) = trace a + trace d := by
  simp [Matrix.trace, blk2, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem blk2_neg (a d : Matrix (Fin 2) (Fin 2) ℂ) : blk2 (-a) (-d) = -blk2 a d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2]

theorem blk2_add (a d a' d' : Matrix (Fin 2) (Fin 2) ℂ) :
    blk2 (a + a') (d + d') = blk2 a d + blk2 a' d' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2]

theorem blk2_smul (r : ℝ) (a d : Matrix (Fin 2) (Fin 2) ℂ) :
    blk2 (r • a) (r • d) = r • blk2 a d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk2]

theorem lowBlk_add (D B B' : Matrix (Fin 2) (Fin 2) ℂ) :
    lowBlk D (B + B') = lowBlk D B + lowBlk D B' := by
  simp only [lowBlk, transpose_add, Matrix.mul_add, Matrix.add_mul, neg_add]

theorem real_smul_eq_complex_smul (r : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    r • M = (r : ℂ) • M := by
  ext i j
  simp [Complex.real_smul]

theorem lowBlk_smul (r : ℝ) (D B : Matrix (Fin 2) (Fin 2) ℂ) :
    lowBlk D (r • B) = r • lowBlk D B := by
  rw [real_smul_eq_complex_smul, real_smul_eq_complex_smul, lowBlk, lowBlk, transpose_smul,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem blk2_skew {a d : Matrix (Fin 2) (Fin 2) ℂ} (ha : star a = -a) (hd : star d = -d) :
    star (blk2 a d) = -blk2 a d := by
  rw [star_eq_conjTranspose, blk2_conjTranspose, ← star_eq_conjTranspose, ← star_eq_conjTranspose,
    ha, hd, blk2_neg]

/-- The element of `su(4)` with diagonal blocks `a` and `−D Bᵀ D⁻¹`. -/
noncomputable def paramTL {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (a : traceless 2)
    (B : commT D) : traceless 4 :=
  ⟨⟨blk2 (mat2 a) (lowBlk D (mat2 B.1)), skewAdjoint.mem_iff.mpr
    (blk2_skew (mat2_skew a) ((star_lowBlk_iff hD (mat2_skew B.1)).mpr B.2))⟩, by
    change (trace (blk2 (mat2 a) (lowBlk D (mat2 B.1)))).im = 0
    rw [trace_blk2, trace_lowBlk hD, trace_mat2, trace_mat2]
    simp⟩

/-- **The parametrisation**: `(a, B) ↦ (diag(a, −D Bᵀ D⁻¹), B)`. -/
noncomputable def stabParam {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    traceless 2 × commT D →ₗ[ℝ] PSLie where
  toFun q := (paramTL hD q.1 q.2, q.2.1)
  map_add' q q' := by
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) rfl
    change blk2 (mat2 q.1 + mat2 q'.1) (lowBlk D (mat2 q.2.1 + mat2 q'.2.1))
      = blk2 (mat2 q.1) (lowBlk D (mat2 q.2.1)) + blk2 (mat2 q'.1) (lowBlk D (mat2 q'.2.1))
    rw [lowBlk_add, blk2_add]
  map_smul' r q := by
    refine Prod.ext (Subtype.ext (Subtype.ext ?_)) rfl
    change blk2 (r • mat2 q.1) (lowBlk D (r • mat2 q.2.1))
      = r • blk2 (mat2 q.1) (lowBlk D (mat2 q.2.1))
    rw [lowBlk_smul, blk2_smul]

theorem stabParam_mem {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (q : traceless 2 × commT D) :
    stabParam hD q ∈ stabAt (vac2 * D) := by
  rw [mem_stabAt_iff]
  change act (blk2 (mat2 q.1) (lowBlk D (mat2 q.2.1))) (mat2 q.2.1) (vac2 * D) = 0
  have e : vac2 * (D * (mat2 q.2.1)ᵀ * D⁻¹) * D = vac2 * D * (mat2 q.2.1)ᵀ := by
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul D hD, Matrix.mul_one]
  rw [act, ← Matrix.mul_assoc, blk2_mul_vac2, lowBlk, Matrix.mul_neg, Matrix.neg_mul, e,
    neg_add_cancel]

theorem stabParam_injective {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    Function.Injective (stabParam hD) := by
  intro q q' h
  have h1 : blk2 (mat2 q.1) (lowBlk D (mat2 q.2.1)) = blk2 (mat2 q'.1) (lowBlk D (mat2 q'.2.1)) :=
    congrArg (fun p : PSLie => mat4 p.1) h
  have h2 : q.2.1 = q'.2.1 := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext (Subtype.ext (blk2_inj h1).1)) (Subtype.ext h2)

/-- Every element of the unbroken subalgebra at `vac2 · D` is `diag(a, −D Bᵀ D⁻¹)` over its `B`. -/
theorem exists_stabParam_eq {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) {p : PSLie}
    (hp : p ∈ stabAt (vac2 * D)) : ∃ q, stabParam hD q = p := by
  rw [mem_stabAt_iff, act] at hp
  set A := mat4 p.1 with hAdef
  set B := mat2 p.2 with hBdef
  set N := lowBlk D B with hN
  have hA : A * vac2 = vac2 * N := by
    calc A * vac2 = A * vac2 * (D * D⁻¹) := by rw [Matrix.mul_nonsing_inv D hD, Matrix.mul_one]
      _ = (A * (vac2 * D)) * D⁻¹ := by simp only [Matrix.mul_assoc]
      _ = (-(vac2 * D * Bᵀ)) * D⁻¹ := by rw [eq_neg_of_add_eq_zero_left hp]
      _ = vac2 * N := by simp only [hN, lowBlk, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have e : ∀ i j, (A * vac2) i j = (vac2 * N) i j := fun i j => by rw [hA]
  have e02 : A 0 2 = 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 0 0
  have e03 : A 0 3 = 0 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 0 1
  have e12 : A 1 2 = 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 1 0
  have e13 : A 1 3 = 0 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 1 1
  have e22 : A 2 2 = N 0 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 2 0
  have e23 : A 2 3 = N 0 1 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 2 1
  have e32 : A 3 2 = N 1 0 := by simpa [mul_vac2_col0, vac2_mul_apply] using e 3 0
  have e33 : A 3 3 = N 1 1 := by simpa [mul_vac2_col1, vac2_mul_apply] using e 3 1
  have hsk := mat4_skew p.1
  have sk : ∀ i j, A j i = -star (A i j) := fun i j => by
    have := congrFun (congrFun hsk j) i
    rw [star_apply, Matrix.neg_apply] at this
    rw [hAdef, this, neg_neg]
  have l20 : A 2 0 = 0 := by rw [sk 0 2, e02, star_zero, neg_zero]
  have l21 : A 2 1 = 0 := by rw [sk 1 2, e12, star_zero, neg_zero]
  have l30 : A 3 0 = 0 := by rw [sk 0 3, e03, star_zero, neg_zero]
  have l31 : A 3 1 = 0 := by rw [sk 1 3, e13, star_zero, neg_zero]
  set top : Matrix (Fin 2) (Fin 2) ℂ := !![A 0 0, A 0 1; A 1 0, A 1 1] with htop
  have hblk : A = blk2 top N := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk2, htop, e02, e03, e12, e13, e22, e23, e32, e33, l20, l21, l30, l31]
  have h1 : star (blk2 top N) = blk2 (star top) (star N) := by
    simp only [star_eq_conjTranspose, blk2_conjTranspose]
  have hstar : blk2 (star top) (star N) = blk2 (-top) (-N) := by
    rw [← h1, ← hblk, hAdef, hsk, ← hAdef, hblk, blk2_neg]
  obtain ⟨htop_sk, hN_sk⟩ := blk2_inj hstar
  have hcomm : Bᵀ * (Dᴴ * D) = (Dᴴ * D) * Bᵀ := (star_lowBlk_iff hD (mat2_skew p.2)).mp hN_sk
  have htr : trace top = 0 := by
    have h4 := trace_mat4 p.1
    rw [← hAdef, hblk, trace_blk2, hN, trace_lowBlk hD, hBdef, trace_mat2, neg_zero, add_zero] at h4
    exact h4
  refine ⟨(⟨⟨top, skewAdjoint.mem_iff.mpr htop_sk⟩, ?_⟩, ⟨p.2, hcomm⟩), ?_⟩
  · change (trace top).im = 0
    rw [htr, Complex.zero_im]
  · refine Prod.ext (Subtype.ext (Subtype.ext ?_)) rfl
    exact hblk.symm

/-- **The unbroken subalgebra at `vac2 · D` is `su(2) × commT D`.** -/
noncomputable def stabAtVac2Equiv {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    (traceless 2 × commT D) ≃ₗ[ℝ] stabAt (vac2 * D) :=
  LinearEquiv.ofBijective ((stabParam hD).codRestrict _ (stabParam_mem hD))
    ⟨fun q q' h => stabParam_injective hD (congrArg Subtype.val h), fun p => by
      obtain ⟨q, hq⟩ := exists_stabParam_eq hD p.2
      exact ⟨q, Subtype.ext hq⟩⟩

theorem finrank_stabAt_vac2 {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) :
    Module.finrank ℝ (stabAt (vac2 * D)) = 3 + Module.finrank ℝ (commT D) := by
  rw [← (stabAtVac2Equiv hD).finrank_eq, Module.finrank_prod, finrank_traceless_two]

/-- **Equal singular values: six unbroken generators.** -/
theorem finrank_stabAt_vac2_of_scalar {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) {c : ℂ}
    (hc : Dᴴ * D = c • 1) : Module.finrank ℝ (stabAt (vac2 * D)) = 6 := by
  have htop : commT D = ⊤ := by
    refine eq_top_iff.mpr fun B _ => ?_
    change (mat2 B)ᵀ * (Dᴴ * D) = (Dᴴ * D) * (mat2 B)ᵀ
    rw [hc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  rw [finrank_stabAt_vac2 hD, htop, finrank_top, finrank_traceless_two]

/-! ## 4. Unequal singular values: the commutant is a line -/

/-- **A traceless skew-Hermitian `2 × 2` matrix commuting with a nonzero traceless Hermitian `N` is
a real multiple of `i N`.** -/
theorem eq_smul_of_comm {C N : Matrix (Fin 2) (Fin 2) ℂ} (hN0 : N ≠ 0) (hNt : N 1 1 = -N 0 0)
    (hNh : star N = N) (hCt : C 1 1 = -C 0 0) (hCs : star C = -C) (hc : C * N = N * C) :
    ∃ t : ℝ, C = ((t : ℂ) * Complex.I) • N := by
  obtain ⟨a1, a2, a3⟩ := comm_entries hc
  rw [hCt, hNt] at a2 a3
  have b2 : C 0 0 * N 0 1 = C 0 1 * N 0 0 := by linear_combination a2 / 2
  have b3 : C 0 0 * N 1 0 = C 1 0 * N 0 0 := by linear_combination a3 / 2
  have hN10 : N 1 0 = star (N 0 1) := by
    have := congrFun (congrFun hNh 1) 0
    rw [star_apply] at this
    exact this.symm
  obtain ⟨l, hl⟩ : ∃ l : ℂ, C = l • N := by
    by_cases h00 : N 0 0 = 0
    · have h01 : N 0 1 ≠ 0 := by
        intro h01
        apply hN0
        ext i j
        fin_cases i <;> fin_cases j <;> simp [h00, h01, hN10, hNt]
      have hC00 : C 0 0 = 0 := by
        rw [h00, mul_zero] at b2
        exact (mul_eq_zero.mp b2).resolve_right h01
      refine ⟨C 0 1 / N 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, smul_apply, smul_eq_mul]
      · rw [hC00, h00, mul_zero]
      · field_simp
      · field_simp
        linear_combination -a1
      · rw [hCt, hNt, hC00, h00]
        ring
    · refine ⟨C 0 0 / N 0 0, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, smul_apply, smul_eq_mul]
      · field_simp
      · field_simp
        linear_combination -b2
      · field_simp
        linear_combination -b3
      · rw [hCt, hNt]
        field_simp
  refine ⟨l.im, ?_⟩
  have h1 : star C = star l • N := by rw [hl, star_smul, hNh]
  have h2 : (star l + l) • N = 0 := by rw [add_smul, ← h1, hCs, hl, neg_add_cancel]
  have h3 : star l + l = 0 := (smul_eq_zero.mp h2).resolve_right hN0
  have hre : l.re = 0 := by
    have := congrArg Complex.re h3
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at this
    linarith
  rw [hl]
  congr 1
  apply Complex.ext <;> simp [hre]

/-- The traceless part `P − (tr P / 2) · 1`. -/
noncomputable def tlPart (P : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  P - (trace P / 2) • 1

theorem tlPart_11 (P : Matrix (Fin 2) (Fin 2) ℂ) : tlPart P 1 1 = -tlPart P 0 0 := by
  simp [tlPart, trace, Fin.sum_univ_two]
  ring

theorem star_tlPart {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : star P = P) :
    star (tlPart P) = tlPart P := by
  have htr : star (trace P) = trace P := by
    rw [← Matrix.trace_conjTranspose, ← star_eq_conjTranspose, hP]
  rw [tlPart, star_sub, star_smul, star_one, hP, star_div₀, htr, star_ofNat]

theorem comm_tlPart_iff (X P : Matrix (Fin 2) (Fin 2) ℂ) :
    X * tlPart P = tlPart P * X ↔ X * P = P * X := by
  simp only [tlPart, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, sub_left_inj]

theorem tlPart_ne_zero {P : Matrix (Fin 2) (Fin 2) ℂ} (hns : ¬ ∃ c : ℂ, P = c • 1) :
    tlPart P ≠ 0 :=
  fun h => hns ⟨trace P / 2, sub_eq_zero.mp h⟩

theorem star_conjTranspose_mul_self (D : Matrix (Fin 2) (Fin 2) ℂ) : star (Dᴴ * D) = Dᴴ * D := by
  rw [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]

/-- `i · (tlPart (Dᴴ D))ᵀ`, the generator of `commT D` when `Dᴴ D` is not scalar. -/
noncomputable def genT (D : Matrix (Fin 2) (Fin 2) ℂ) : traceless 2 :=
  ⟨⟨Complex.I • (tlPart (Dᴴ * D))ᵀ, by
    rw [skewAdjoint.mem_iff, star_smul, Complex.star_def, Complex.conj_I, star_eq_conjTranspose,
      transpose_conjTranspose, ← conjTranspose_transpose, ← star_eq_conjTranspose,
      star_tlPart (star_conjTranspose_mul_self D), neg_smul]⟩, by
    change (trace (Complex.I • (tlPart (Dᴴ * D))ᵀ)).im = 0
    rw [trace_smul, trace_transpose]
    have h0 : trace (tlPart (Dᴴ * D)) = 0 := by
      rw [trace_fin_two, tlPart_11]
      ring
    rw [h0, smul_zero, Complex.zero_im]⟩

theorem genT_mem (D : Matrix (Fin 2) (Fin 2) ℂ) : genT D ∈ commT D := by
  change (Complex.I • (tlPart (Dᴴ * D))ᵀ)ᵀ * (Dᴴ * D) = (Dᴴ * D) * (Complex.I • (tlPart (Dᴴ * D))ᵀ)ᵀ
  rw [transpose_smul, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  exact ((comm_tlPart_iff (Dᴴ * D) (Dᴴ * D)).mpr rfl).symm

theorem genT_ne_zero {D : Matrix (Fin 2) (Fin 2) ℂ} (hns : ¬ ∃ c : ℂ, Dᴴ * D = c • 1) :
    genT D ≠ 0 := by
  intro h
  have h' : Complex.I • (tlPart (Dᴴ * D))ᵀ = 0 := congrArg (fun x : traceless 2 => x.1.1) h
  rcases smul_eq_zero.mp h' with hI | hT
  · exact Complex.I_ne_zero hI
  · exact tlPart_ne_zero hns (by rw [← transpose_transpose (tlPart _), hT, transpose_zero])

/-- **Unequal singular values: `commT D` is the line through `genT D`.** -/
theorem commT_eq_span {D : Matrix (Fin 2) (Fin 2) ℂ} (hns : ¬ ∃ c : ℂ, Dᴴ * D = c • 1) :
    commT D = Submodule.span ℝ {genT D} := by
  refine le_antisymm (fun B hB => ?_) ((Submodule.span_le).mpr (by simp [genT_mem]))
  set C := (mat2 B)ᵀ with hCdef
  have hCs : star C = -C := star_transpose_of_skew (mat2_skew B)
  have hCt : C 1 1 = -C 0 0 := by
    have h := trace_mat2 B
    rw [trace_fin_two] at h
    simp only [hCdef, transpose_apply]
    linear_combination h
  have hc : C * tlPart (Dᴴ * D) = tlPart (Dᴴ * D) * C := (comm_tlPart_iff C (Dᴴ * D)).mpr hB
  obtain ⟨t, ht⟩ := eq_smul_of_comm (tlPart_ne_zero hns) (tlPart_11 _)
    (star_tlPart (star_conjTranspose_mul_self D)) hCt hCs hc
  refine Submodule.mem_span_singleton.mpr ⟨t, Subtype.ext (Subtype.ext ?_)⟩
  change t • (Complex.I • (tlPart (Dᴴ * D))ᵀ) = mat2 B
  rw [← transpose_transpose (mat2 B), ← hCdef, ht, transpose_smul, real_smul_eq_complex_smul,
    smul_smul]

theorem finrank_commT_of_not_scalar {D : Matrix (Fin 2) (Fin 2) ℂ}
    (hns : ¬ ∃ c : ℂ, Dᴴ * D = c • 1) : Module.finrank ℝ (commT D) = 1 := by
  rw [commT_eq_span hns, finrank_span_singleton (genT_ne_zero hns)]

/-- **Unequal singular values: four unbroken generators.** -/
theorem finrank_stabAt_vac2_of_not_scalar {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det)
    (hns : ¬ ∃ c : ℂ, Dᴴ * D = c • 1) : Module.finrank ℝ (stabAt (vac2 * D)) = 4 := by
  rw [finrank_stabAt_vac2 hD, finrank_commT_of_not_scalar hns]

/-! ## 5. Every vacuum: nine, six or four unbroken generators, and the count decides the group -/

theorem scalar_gram_iff_of_smul_eq {X : Bidoublet} {g : Stage1Group}
    {D : Matrix (Fin 2) (Fin 2) ℂ} (hD : IsUnit D.det) (hgX : g • X = vac2 * D) :
    (∃ c : ℂ, Dᴴ * D = c • 1) ↔ ∃ c : ℂ, Xᴴ * X = c • 1 := by
  rw [scalar_conjTranspose_mul_iff hD]
  exact scalar_iff_of_smul_eq hD hgX

theorem finrank_stabAt_of_scalar (X : Bidoublet) (hX : X.rank = 2)
    (hc : ∃ c : ℂ, Xᴴ * X = c • 1) : Module.finrank ℝ (stabAt X) = 6 := by
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  obtain ⟨c, hc'⟩ := (scalar_gram_iff_of_smul_eq hD hgX).mpr hc
  rw [← finrank_stabAt_smul g X, hgX, finrank_stabAt_vac2_of_scalar hD hc']

theorem finrank_stabAt_of_not_scalar (X : Bidoublet) (hX : X.rank = 2)
    (hc : ¬ ∃ c : ℂ, Xᴴ * X = c • 1) : Module.finrank ℝ (stabAt X) = 4 := by
  obtain ⟨g, D, hD, hgX⟩ := exists_smul_eq_vac2_mul X hX
  have hns : ¬ ∃ c : ℂ, Dᴴ * D = c • 1 := fun h => hc ((scalar_gram_iff_of_smul_eq hD hgX).mp h)
  rw [← finrank_stabAt_smul g X, hgX, finrank_stabAt_vac2_of_not_scalar hD hns]

/-- **The unbroken subalgebra has dimension nine, six or four**, by the same three cases. -/
theorem finrank_stabAt_trichotomy (X : Bidoublet) (hX : X ≠ 0) :
    (X.rank = 1 ∧ Module.finrank ℝ (stabAt X) = 9) ∨
    (X.rank = 2 ∧ (∃ c : ℂ, Xᴴ * X = c • 1) ∧ Module.finrank ℝ (stabAt X) = 6) ∨
    (X.rank = 2 ∧ (¬ ∃ c : ℂ, Xᴴ * X = c • 1) ∧ Module.finrank ℝ (stabAt X) = 4) := by
  rcases stabilizer_trichotomy X hX with ⟨h1, -⟩ | ⟨h2, hc, -⟩ | ⟨h2, hc, -⟩
  · exact Or.inl ⟨h1, finrank_stabAt_of_rank_eq_one X h1⟩
  · exact Or.inr (Or.inl ⟨h2, hc, finrank_stabAt_of_scalar X h2 hc⟩)
  · exact Or.inr (Or.inr ⟨h2, hc, finrank_stabAt_of_not_scalar X h2 hc⟩)

/-- **The number of broken generators**: `18` minus the unbroken dimension. -/
theorem finrank_broken_add (X : Bidoublet) :
    Module.finrank ℝ (PSLie ⧸ stabAt X) + Module.finrank ℝ (stabAt X) = 18 := by
  rw [Submodule.finrank_quotient_add_finrank, finrank_PSLie]

/-- Nine unbroken generators exactly when the unbroken group is `U(3)`. -/
theorem finrank_stabAt_eq_nine_iff (X : Bidoublet) (hX : X ≠ 0) :
    Module.finrank ℝ (stabAt X) = 9 ↔
      Nonempty (MulAction.stabilizer Stage1Group X ≃* GroupU3) := by
  rw [nonempty_stabilizer_equiv_U3_iff X hX]
  rcases finrank_stabAt_trichotomy X hX with ⟨h1, hf⟩ | ⟨h2, -, hf⟩ | ⟨h2, -, hf⟩ <;> omega

theorem finrank_stabAt_eq_six_iff (X : Bidoublet) (hX : X ≠ 0) :
    Module.finrank ℝ (stabAt X) = 6 ↔
      Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × SU2) := by
  rcases stabilizer_trichotomy X hX with ⟨h1, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩
  · rw [finrank_stabAt_of_rank_eq_one X h1]
    exact ⟨by omega, fun ⟨φ⟩ => absurd ⟨φ.symm.trans e⟩ not_nonempty_SU2_SU2_equiv_U3⟩
  · exact ⟨fun _ => ⟨e⟩, fun _ => finrank_stabAt_of_scalar X h2 hc⟩
  · rw [finrank_stabAt_of_not_scalar X h2 hc]
    exact ⟨by omega, fun ⟨φ⟩ => absurd ⟨φ.symm.trans e⟩ not_nonempty_SU2_SU2_equiv_SU2_circle⟩

theorem finrank_stabAt_eq_four_iff (X : Bidoublet) (hX : X ≠ 0) :
    Module.finrank ℝ (stabAt X) = 4 ↔
      Nonempty (MulAction.stabilizer Stage1Group X ≃* SU2 × unitary ℂ) := by
  rcases stabilizer_trichotomy X hX with ⟨h1, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩
  · rw [finrank_stabAt_of_rank_eq_one X h1]
    exact ⟨by omega, fun ⟨φ⟩ => absurd ⟨φ.symm.trans e⟩ not_nonempty_SU2_circle_equiv_U3⟩
  · rw [finrank_stabAt_of_scalar X h2 hc]
    exact ⟨by omega, fun ⟨φ⟩ => absurd ⟨e.symm.trans φ⟩ not_nonempty_SU2_SU2_equiv_SU2_circle⟩
  · exact ⟨fun _ => ⟨e⟩, fun _ => finrank_stabAt_of_not_scalar X h2 hc⟩

/-- **GOLDSTONE COUNTING DECIDES THE FIRST STAGE.** Two nonzero first-stage vacua leave isomorphic
unbroken groups if and only if their unbroken subalgebras have the same dimension. -/
theorem nonempty_stabilizer_equiv_iff_finrank_eq (X Y : Bidoublet) (hX : X ≠ 0) (hY : Y ≠ 0) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* MulAction.stabilizer Stage1Group Y) ↔
      Module.finrank ℝ (stabAt X) = Module.finrank ℝ (stabAt Y) := by
  constructor
  · rintro ⟨φ⟩
    rcases stabilizer_trichotomy X hX with ⟨h1, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩
    · rw [finrank_stabAt_of_rank_eq_one X h1,
        (finrank_stabAt_eq_nine_iff Y hY).mpr ⟨φ.symm.trans e⟩]
    · rw [finrank_stabAt_of_scalar X h2 hc, (finrank_stabAt_eq_six_iff Y hY).mpr ⟨φ.symm.trans e⟩]
    · rw [finrank_stabAt_of_not_scalar X h2 hc,
        (finrank_stabAt_eq_four_iff Y hY).mpr ⟨φ.symm.trans e⟩]
  · intro h
    rcases stabilizer_trichotomy X hX with ⟨h1, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩ | ⟨h2, hc, ⟨e⟩⟩
    · rw [finrank_stabAt_of_rank_eq_one X h1] at h
      obtain ⟨e'⟩ := (finrank_stabAt_eq_nine_iff Y hY).mp h.symm
      exact ⟨e.trans e'.symm⟩
    · rw [finrank_stabAt_of_scalar X h2 hc] at h
      obtain ⟨e'⟩ := (finrank_stabAt_eq_six_iff Y hY).mp h.symm
      exact ⟨e.trans e'.symm⟩
    · rw [finrank_stabAt_of_not_scalar X h2 hc] at h
      obtain ⟨e'⟩ := (finrank_stabAt_eq_four_iff Y hY).mp h.symm
      exact ⟨e.trans e'.symm⟩

/-- **… and in terms of broken generators**: `9`, `12` or `14`, and two nonzero vacua leave
isomorphic groups exactly when they break the same number. -/
theorem nonempty_stabilizer_equiv_iff_finrank_broken_eq (X Y : Bidoublet) (hX : X ≠ 0)
    (hY : Y ≠ 0) :
    Nonempty (MulAction.stabilizer Stage1Group X ≃* MulAction.stabilizer Stage1Group Y) ↔
      Module.finrank ℝ (PSLie ⧸ stabAt X) = Module.finrank ℝ (PSLie ⧸ stabAt Y) := by
  rw [nonempty_stabilizer_equiv_iff_finrank_eq X Y hX hY]
  have hx := finrank_broken_add X
  have hy := finrank_broken_add Y
  omega

end PatiSalamBrokenCount
