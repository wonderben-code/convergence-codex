/-
  PatiSalamGaugeAction: the gauge GROUP acts on the two Higgs fields — `SU(4) × SU(2)_R` on the
  `(4, 1, 2)` bidoublet, `SU(2)_L × SU(2)_R` on the `(1, 2, 2)`, `SU(4) × SU(2)_L × SU(2)_R` on the
  pair — the Lie-algebra actions of units 178 and 182 are the generators of these actions, and
  each unbroken algebra is EXACTLY the set of generators whose one-parameter subgroups fix the
  vacuum

  Campaign 3 hardening unit 191 (25 September 2026). Spine link L15 (Higgs sector), with L10's
  group level.

  WHY. `SPINE` L15's row, since unit 188: *"The group's ACTION on the two Higgs fields (that
  `exp A · X · exp(B)ᵀ` integrates `A X + X Bᵀ`) is not stated, so no gauge bosons as objects and
  the potential stand."* `SkewAdjointExponential`'s third NOT bullet says the same of its own
  `expFull`. `PatiSalamStabiliserLie`, amended at unit 188: *"statements about the unbroken GROUP
  as a group are still absent."* `PatiSalamVacuumStabiliser`: *"No group, no exponential, no
  `LieModule` instance."* This file writes the action as Mathlib `MulAction`s, proves that the
  estate's Lie-algebra actions `act` and `actEW` are its infinitesimal generators, and reads the
  three stabiliser algebras of units 178, 182 and 183 at the group level, in both directions.

  WHAT IS PROVED.
  (0) Five restatements (`rsmul_mul`, `mul_rsmul`, `zero_rsmul`, `rsmul_zero`, `rsmul_neg`): under
      `Matrix.Norms.Operator`, `t • A` for real `t` elaborates through `NormedAlgebra ℝ ℂ`, and
      the library's `smul` lemmas whose scalar action is an instance chain do not rewrite it. Each
      proof is the library lemma itself; the statement is re-elaborated here so that `rw` sees it.
  (1) **`exp_mul_of_mul_eq`**: `A E = E C ⟹ exp A · E = E · exp C` for square `A`, `C` of
      DIFFERENT sizes and rectangular `E` — the exponential series (`exp_series_hasSum_exp'`)
      pushed through right and left multiplication by `E`, then `HasSum.unique`.
  (2) Stage 1. `Stage1Group := SU(4) × SU(2)` (Mathlib's `specialUnitaryGroup`),
      `stage1Act g X = g₁ · X · g₂ᵀ`, **`instMulActionStage1`**. `exp_fixes_of_act_eq_zero`:
      `A X + X Bᵀ = 0 ⟹ exp (t A) X exp (t Bᵀ) = X` for every real `t`. `oneParamG1 p t :=
      (oneParam p.1 t, oneParam p.2 t)` and `oneParamG1_smul` (its action as matrices);
      `stab_exp_fixes_vac`, `oneParamG1_mem_stabilizer` (Mathlib's `MulAction.stabilizer`), and
      **`hypercharge_fixes_vac`**: `U(1)_Y`'s one-parameter subgroup fixes the vacuum.
  (3) The generator. `hasDerivAt_exp_rsmul` (`d/dt exp (t A) = A` at `0`, restated),
      `hasDerivAt_left`, `hasDerivAt_right`, and the product rule for a `4 × 2` curve times a
      `2 × 2` curve through the `6 × 6` block algebra (`blockIn12`, `blockIn22`, `blockOut12`,
      `blockOut12_mul`, `hasDerivAt_matMul`). **`hasDerivAt_stage1`**: `d/dt|₀ (oneParamG1 p t •
      X) = act (mat4 p.1) (mat2 p.2) X` — unit 178's `act` IS the generator of the group action.
      With uniqueness of derivatives (`eq_zero_of_hasDerivAt_of_const`) the converse follows:
      **`mem_stab_iff_fixes`**: `p ∈ stab ↔ ∀ t, oneParamG1 p t • vac = vac`, and
      `mem_stab_iff_mem_stabilizer`.
  (4) Stage 2. `Stage2Group := SU(2) × SU(2)`, `stage2Act g Φ = g₁ · Φ · star g₂` (`star` is the
      inverse on the unitary group), **`instMulActionStage2`**; `exp_fixes_of_actEW_eq_zero`,
      `star_exp_smul`; `oneParamLR a b` for ANY pair of `su(2)` generators, `oneParamLR_smul`,
      **`hasDerivAt_stage2LR`** (the generator is `actEW (mat2 a) (mat2 b)`); `oneParamG2` on unit
      182's `EWLie`, `stabEW_exp_fixes_vacEW`, `oneParamG2_mem_stabilizer`,
      **`charge_fixes_vacEW`** (`U(1)_em`'s subgroup fixes the electroweak vacuum, through unit
      182's `qG_mem_stabEW`), `hasDerivAt_stage2`, **`mem_stabEW_iff_fixes`** and
      `mem_stabEW_iff_mem_stabilizer`.
  (5) Both stages. `FullGroup := SU(4) × SU(2)_L × SU(2)_R` on `Bidoublet × EWBidoublet`, with
      `SU(2)_R` acting on BOTH fields (`fullAct`, **`instMulActionFull`**, `expFull_smul_eq`,
      `expFull_smul_pair`); `jointStab_exp_fixes`, `expFull_mem_stabilizer`,
      `charge_fixes_both`; **`mem_jointStab_iff_fixes`**: unit 183's `jointStab` is exactly the
      set of `p` with `expFull (t • p) • (vac, vacEW) = (vac, vacEW)` for every `t`, and
      `mem_jointStab_iff_mem_stabilizer`. `hasDerivAt_full`, `hasDerivAt_full_vac` (the velocity
      at the vacuum pair is `jointOrbit p`), and **`mem_range_jointOrbit_iff`**: unit 184's
      tangent directions, `range jointOrbit`, are exactly the velocities at `t = 0` of the curves
      `t ↦ expFull (t • p) • (vac, vacEW)` in the vacuum's group orbit.

  NOT PROVED, said exactly.
  • The stabiliser SUBGROUPS are named, not computed. `MulAction.stabilizer Stage1Group vac` is
    not identified with `U(3)` (the group-level analogue of units 179–180's `stab ≃ u(3)`), its
    connectedness is not proved, and nothing says the one-parameter subgroups of `stab` generate
    it. The theorems here characterise the stabiliser ALGEBRAS through one-parameter subgroups;
    they do not determine the stabiliser GROUPS.
    ⚠ 25 September 2026 (hardening unit 215, `ERRATUM 694`): computed since unit 199 —
    `PatiSalamStabiliserGroup.stabilizerVacEquivU3` (`≅ U(3)` at stage one) and
    `stabilizerPairEquivU3` (both vacua); as topological groups since unit 206
    (`PatiSalamStabiliserTopology.stabilizerVacContinuousEquivU3`); and at every nonzero first-stage
    vacuum since unit 212 (`PatiSalamFirstStageClassification.stabilizer_trichotomy`).
    Connectedness, and generation by the one-parameter subgroups, are still not shown. Kept as
    written (`ERRATUM 94`).
  • No topology, manifold or Lie-group structure on `specialUnitaryGroup` (queried at unit 188:
    `LieGroup` occurs in no `paper_f` file). "Generator" means the derivative at `t = 0` of the
    curve `t ↦ exp (t p) • X` in the matrix space; smoothness in the group element is not stated.
    ⚠ 25 September 2026 (hardening unit 215, `ERRATUM 694`): the topology is stale. Units 206 and
    209 put the subspace topology of the matrices to work: `U(n)` and `SU(n)` are compact
    (`PatiSalamStabiliserTopology.isCompact_unitaryGroup`,
    `PatiSalamTopologicalCopies.isCompact_specialUnitaryGroup`), the actions are continuous
    (`continuous_stage1_smul`, `continuous_full_smul`), and every stabiliser is closed and compact
    (`isClosed_stabilizer`, `compactSpace_stabilizer`). No manifold or Lie-group structure is used
    in any declaration: the query's word now occurs in four `paper_f` files, all in prose. Kept as
    written (`ERRATUM 94`).
    ⚠ 25 September 2026 (hardening unit 223, `paper_f/PatiSalamSecondStageTopology.lean`,
    `ERRATUM 696`): *the actions are continuous* and *every stabiliser is closed and compact* cite
    the first stage and pairs only; this file's second-stage action, `stage2Act`, was shown
    continuous and its stabilisers closed and compact in unit 223 (`continuous_stage2_smul`,
    `isClosed_stabilizer_stage2`, `compactSpace_stabilizer_stage2`). Kept as written (`ERRATUM 94`).
  • The vacuum's orbit is not shown to be a manifold, and `range jointOrbit` is not shown to be
    its tangent space in a differential-geometric sense — only that its elements are exactly the
    velocities of the one-parameter orbit curves through the vacuum.
  • Still no gauge bosons as objects (no connection, no covariant derivative on the Higgs
    fields), no potential, no masses: the massless half of unit 184's Goldstone bullet stands.
  • `ASSUMPTIONS_LEDGER` 11 is untouched: that the physical gauge group IS this `SU(4) × SU(2) ×
    SU(2)` is the postulate. The representation conventions, `g X hᵀ` on the `(4, 1, 2)` and
    `h Φ k⁻¹` on the `(1, 2, 2)`, are the ones units 178 and 182 fixed for the algebra,
    integrated here, not derived.

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `exp_mul_of_mul_eq` takes `A * E = E * C`;
  `exp_fixes_of_act_eq_zero` takes `A * X + X * Bᵀ = 0`; `exp_fixes_of_actEW_eq_zero` takes
  `A * Φ - Φ * B = 0`; `stab_exp_fixes_vac` and `oneParamG1_mem_stabilizer` take `p ∈ stab`;
  `stabEW_exp_fixes_vacEW` and `oneParamG2_mem_stabilizer` take `q ∈ stabEW`;
  `jointStab_exp_fixes` and `expFull_mem_stabilizer` take `p ∈ jointStab`; `mem_stab_of_fixes`
  takes the fixing at every `t`; `eq_zero_of_hasDerivAt_of_const` takes a derivative and
  constancy; `hasDerivAt_matMul` takes two derivatives; `star_exp_smul` takes `B` in
  `skewAdjoint`. The iff theorems, the derivatives, the actions and the instances take nothing
  else. Every `t` is any real number: no smallness, no neighbourhood of the identity.

  QUERIED BEFORE WRITING. `MulAction` instances in `paper_f` → 4 files (`Herm2Action` and its
  prose in `MinkowskiHerm2`: `SL2C` on `Herm2`; `IsingFiniteVolume`; `PhaseTransitionStatement`),
  none on these types; `stabilizer` → 0 files; `exp_series_hasSum_exp` → 0 files;
  `hasDerivAt_exp_smul_const` → 1 file (`FiniteStone`, on `E →L[ℂ] E`); `specialUnitaryGroup` →
  4 files, none acting on a Higgs field.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`: the 70 names first drafted, run against
  `paper_f` by word search). One was taken: `qG_mem_stabEW` is unit 182's
  `ElectroweakVacuumStabiliser.qG_mem_stabEW`, the same statement — the copy was deleted and unit
  182's is used, leaving 69. The five restatements in (0) and `eq_zero_of_hasDerivAt_of_const`
  were checked against Mathlib by name: none there. `FiniteStone.unitaryGroup` is a
  one-parameter group of operators, not an action on a Higgs field; `Herm2Action`'s `SL2C`
  action is the Lorentz action on `Herm2`, a different group on a different type.
-/

import SkewAdjointExponential

open Matrix NormedSpace TracelessSkewDimension PatiSalamRightSector PatiSalamVacuumStabiliser
  ElectroweakVacuumStabiliser PatiSalamTwoStageStabiliser SkewAdjointExponential
open scoped Matrix.Norms.Operator

namespace PatiSalamGaugeAction

noncomputable section

/-! ## 0. Real scalars on complex matrices, restated in this file's elaboration

Under `Matrix.Norms.Operator`, `t • A` for `t : ℝ` elaborates through `NormedAlgebra ℝ ℂ`, and the
library's `smul` lemmas whose scalar action is an instance chain do not rewrite it. The five facts
below are the library lemmas, restated so that their statements elaborate here; each proof is the
library lemma itself, accepted by unfolding. -/

theorem rsmul_mul {l m n : Type*} [Fintype m] (t : ℝ) (A : Matrix l m ℂ) (X : Matrix m n ℂ) :
    (t • A) * X = t • (A * X) := Matrix.smul_mul t A X

theorem mul_rsmul {l m n : Type*} [Fintype m] (t : ℝ) (X : Matrix l m ℂ) (A : Matrix m n ℂ) :
    X * (t • A) = t • (X * A) := Matrix.mul_smul X t A

theorem zero_rsmul {m n : Type*} (A : Matrix m n ℂ) : (0 : ℝ) • A = 0 := zero_smul ℝ A

theorem rsmul_zero {m n : Type*} (t : ℝ) : t • (0 : Matrix m n ℂ) = 0 := smul_zero t

theorem rsmul_neg {m n : Type*} (t : ℝ) (A : Matrix m n ℂ) : t • -A = -(t • A) := smul_neg t A

/-! ## 1. The intertwining lemma: `A E = E C ⟹ exp A · E = E · exp C` -/

theorem exp_mul_of_mul_eq {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m m ℂ) (C : Matrix n n ℂ) (E : Matrix m n ℂ) (h : A * E = E * C) :
    exp A * E = E * exp C := by
  have hn : ∀ k : ℕ, A ^ k * E = E * C ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  let gR : Matrix m m ℂ →+ Matrix m n ℂ :=
    { toFun := fun M => M * E
      map_zero' := Matrix.zero_mul E
      map_add' := fun M N => Matrix.add_mul M N E }
  let gL : Matrix n n ℂ →+ Matrix m n ℂ :=
    { toFun := fun M => E * M
      map_zero' := Matrix.mul_zero E
      map_add' := fun M N => Matrix.mul_add E M N }
  have hR := (exp_series_hasSum_exp' (𝕂 := ℂ) A).map gR
    (Continuous.matrix_mul continuous_id continuous_const)
  have hL := (exp_series_hasSum_exp' (𝕂 := ℂ) C).map gL
    (Continuous.matrix_mul continuous_const continuous_id)
  have hL' : HasSum (gR ∘ fun k : ℕ => (k.factorial⁻¹ : ℂ) • A ^ k) (gL (exp C)) := by
    convert hL using 1
    funext k
    change ((k.factorial⁻¹ : ℂ) • A ^ k) * E = E * ((k.factorial⁻¹ : ℂ) • C ^ k)
    rw [Matrix.smul_mul, Matrix.mul_smul, hn]
  exact hR.unique hL'

/-! ## 2. Stage 1: `SU(4) × SU(2)_R` on the `(4, 1, 2)` bidoublet -/

abbrev Stage1Group :=
  Matrix.specialUnitaryGroup (Fin 4) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- `(g, h) • X = g X hᵀ` — the group action whose generator is `act A B X = A X + X Bᵀ`. -/
def stage1Act (g : Stage1Group) (X : Bidoublet) : Bidoublet :=
  (g.1 : Matrix (Fin 4) (Fin 4) ℂ) * X * (g.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ

theorem stage1Act_one (X : Bidoublet) : stage1Act 1 X = X := by
  simp [stage1Act]

theorem stage1Act_mul (g h : Stage1Group) (X : Bidoublet) :
    stage1Act (g * h) X = stage1Act g (stage1Act h X) := by
  simp only [stage1Act, Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, Matrix.transpose_mul,
    Matrix.mul_assoc]

instance instMulActionStage1 : MulAction Stage1Group Bidoublet where
  smul := stage1Act
  one_smul := stage1Act_one
  mul_smul := stage1Act_mul

theorem stage1_smul_def (g : Stage1Group) (X : Bidoublet) : g • X = stage1Act g X := rfl

/-- The matrix-level statement: `A X + X Bᵀ = 0 ⟹ exp (t A) X exp (t Bᵀ) = X`. -/
theorem exp_fixes_of_act_eq_zero (A : Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ)
    (X : Bidoublet) (h : A * X + X * Bᵀ = 0) (t : ℝ) :
    exp (t • A) * X * exp (t • Bᵀ) = X := by
  have h0 : A * X = X * (-Bᵀ) := by
    rw [Matrix.mul_neg]
    exact eq_neg_of_add_eq_zero_left h
  have ht : (t • A) * X = X * (t • (-Bᵀ)) := by
    rw [rsmul_mul, mul_rsmul, h0]
  rw [exp_mul_of_mul_eq _ _ _ ht, Matrix.mul_assoc, rsmul_neg,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • Bᵀ)).neg_left), neg_add_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

/-- The one-parameter subgroup of `SU(4) × SU(2)_R` generated by `p ∈ su(4) ⊕ su(2)_R`. -/
def oneParamG1 (p : PSLie) (t : ℝ) : Stage1Group := (oneParam p.1 t, oneParam p.2 t)

theorem coe_oneParam {k : ℕ} (A : traceless k) (t : ℝ) :
    ((oneParam A t : Matrix.specialUnitaryGroup (Fin k) ℂ) : Matrix (Fin k) (Fin k) ℂ)
      = exp (t • ((A : skewAdjoint (Matrix (Fin k) (Fin k) ℂ)) : Matrix (Fin k) (Fin k) ℂ)) := by
  rw [oneParam, expSU_val, coe_smul_traceless]

theorem oneParamG1_smul (p : PSLie) (t : ℝ) (X : Bidoublet) :
    oneParamG1 p t • X = exp (t • mat4 p.1) * X * exp (t • (mat2 p.2)ᵀ) := by
  rw [stage1_smul_def, stage1Act]
  change ((oneParam p.1 t : Matrix.specialUnitaryGroup (Fin 4) ℂ) : Matrix (Fin 4) (Fin 4) ℂ) * X
    * ((oneParam p.2 t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = _
  rw [coe_oneParam, coe_oneParam, ← Matrix.exp_transpose, Matrix.transpose_smul]

/-- **THE ONE-PARAMETER SUBGROUPS OF THE UNBROKEN ALGEBRA FIX THE VACUUM.** -/
theorem stab_exp_fixes_vac (p : PSLie) (hp : p ∈ stab) (t : ℝ) :
    oneParamG1 p t • vac = vac := by
  rw [oneParamG1_smul]
  exact exp_fixes_of_act_eq_zero _ _ _ (LinearMap.mem_ker.mp hp) t

theorem oneParamG1_mem_stabilizer (p : PSLie) (hp : p ∈ stab) (t : ℝ) :
    oneParamG1 p t ∈ MulAction.stabilizer Stage1Group vac :=
  stab_exp_fixes_vac p hp t

/-- **THE UNBROKEN `U(1)_Y`, AS A GROUP STATEMENT**: hypercharge's one-parameter subgroup fixes
the vacuum. -/
theorem hypercharge_fixes_vac (t : ℝ) : oneParamG1 yG t • vac = vac :=
  stab_exp_fixes_vac yG yG_mem_stab t

/-! ## 3. The infinitesimal generator of the stage-1 action is `act` -/

/-- Right multiplication by a fixed bidoublet, as a continuous linear map. -/
def mulRightCLM (X : Bidoublet) : Matrix (Fin 4) (Fin 4) ℂ →L[ℝ] Bidoublet :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M * X
      map_add' := fun M N => Matrix.add_mul M N X
      map_smul' := fun c M => Matrix.smul_mul c M X }

/-- Left multiplication by a fixed bidoublet, as a continuous linear map. -/
def mulLeftCLM (X : Bidoublet) : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Bidoublet :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => X * M
      map_add' := fun M N => Matrix.mul_add X M N
      map_smul' := fun c M => Matrix.mul_smul X c M }

/-- `d/dt exp (t A) = A` at `t = 0`, restated in this file's elaboration of `t • A`. -/
theorem hasDerivAt_exp_rsmul {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    HasDerivAt (fun t : ℝ => exp (t • A)) A 0 := by
  have h : HasDerivAt (fun t : ℝ => exp (t • A)) (A * exp ((0 : ℝ) • A)) 0 :=
    hasDerivAt_exp_smul_const' (𝕂 := ℝ) A 0
  rwa [zero_rsmul, NormedSpace.exp_zero, Matrix.mul_one] at h

theorem hasDerivAt_left (A : Matrix (Fin 4) (Fin 4) ℂ) (X : Bidoublet) :
    HasDerivAt (fun t : ℝ => exp (t • A) * X) (A * X) 0 :=
  (mulRightCLM X).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (hasDerivAt_exp_rsmul A)

theorem hasDerivAt_right (B : Matrix (Fin 2) (Fin 2) ℂ) (X : Bidoublet) :
    HasDerivAt (fun t : ℝ => X * exp (t • B)) (X * B) 0 :=
  (mulLeftCLM X).hasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) (hasDerivAt_exp_rsmul B)

/-- A `4 × 2` block placed in the `(1, 2)` slot of a `6 × 6` matrix. -/
def blockIn12 : Bidoublet →L[ℝ] Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => fromBlocks 0 M 0 0
      map_add' := fun M N => by simp only [fromBlocks_add, add_zero]
      map_smul' := fun c M => by
        rw [RingHom.id_apply, fromBlocks_smul]
        congr 1 <;> exact (smul_zero c).symm }

/-- A `2 × 2` block placed in the `(2, 2)` slot. -/
def blockIn22 : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun N => fromBlocks 0 0 0 N
      map_add' := fun M N => by simp only [fromBlocks_add, add_zero]
      map_smul' := fun c M => by
        rw [RingHom.id_apply, fromBlocks_smul]
        congr 1 <;> exact (smul_zero c).symm }

/-- The `(1, 2)` block of a `6 × 6` matrix. -/
def blockOut12 : Matrix (Fin 4 ⊕ Fin 2) (Fin 4 ⊕ Fin 2) ℂ →L[ℝ] Bidoublet :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M.toBlocks₁₂
      map_add' := fun M N => by ext i j; simp [Matrix.toBlocks₁₂]
      map_smul' := fun c M => by ext i j; simp [Matrix.toBlocks₁₂] }

theorem blockOut12_mul (a : Bidoublet) (b : Matrix (Fin 2) (Fin 2) ℂ) :
    blockOut12 (blockIn12 a * blockIn22 b) = a * b := by
  simp [blockOut12, blockIn12, blockIn22, fromBlocks_multiply]

/-- The product rule for a `4 × 2` curve times a `2 × 2` curve, through the `6 × 6` algebra. -/
theorem hasDerivAt_matMul {u : ℝ → Bidoublet} {v : ℝ → Matrix (Fin 2) (Fin 2) ℂ} {u' : Bidoublet}
    {v' : Matrix (Fin 2) (Fin 2) ℂ} {t : ℝ} (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => u s * v s) (u' * v t + u t * v') t := by
  have h1 := blockIn12.hasFDerivAt.comp_hasDerivAt (x := t) hu
  have h2 := blockIn22.hasFDerivAt.comp_hasDerivAt (x := t) hv
  have h4 := blockOut12.hasFDerivAt.comp_hasDerivAt (x := t) (h1.mul h2)
  convert h4 using 1
  · funext s
    exact (blockOut12_mul (u s) (v s)).symm
  · simp only [Function.comp_apply, map_add, blockOut12_mul]

/-- **THE GENERATOR OF THE STAGE-1 GROUP ACTION IS THE LIE-ALGEBRA ACTION `act`.** -/
theorem hasDerivAt_stage1 (p : PSLie) (X : Bidoublet) :
    HasDerivAt (fun t : ℝ => oneParamG1 p t • X) (act (mat4 p.1) (mat2 p.2) X) 0 := by
  have h := hasDerivAt_matMul (hasDerivAt_left (mat4 p.1) X) (hasDerivAt_exp_rsmul (mat2 p.2)ᵀ)
  simp only [zero_rsmul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul] at h
  convert h using 1
  funext t
  exact oneParamG1_smul p t X

/-- A curve that is constant has zero derivative: the step from "fixes for every `t`" back to
"annihilated by the generator". -/
theorem eq_zero_of_hasDerivAt_of_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {f' x : E} (hf : HasDerivAt f f' 0) (hc : ∀ t, f t = x) : f' = 0 :=
  hf.unique ((hasDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq (Filter.Eventually.of_forall hc))

theorem mem_stab_of_fixes (p : PSLie) (h : ∀ t : ℝ, oneParamG1 p t • vac = vac) : p ∈ stab :=
  LinearMap.mem_ker.mpr (eq_zero_of_hasDerivAt_of_const (hasDerivAt_stage1 p vac) h)

/-- **THE UNBROKEN ALGEBRA IS EXACTLY THE SET OF GENERATORS WHOSE ONE-PARAMETER SUBGROUPS FIX THE
VACUUM** — unit 178's `stab`, a kernel of a linear map, read at the group level. -/
theorem mem_stab_iff_fixes (p : PSLie) : p ∈ stab ↔ ∀ t : ℝ, oneParamG1 p t • vac = vac :=
  ⟨stab_exp_fixes_vac p, mem_stab_of_fixes p⟩

/-- The same, with Mathlib's stabiliser subgroup of `SU(4) × SU(2)_R` named. -/
theorem mem_stab_iff_mem_stabilizer (p : PSLie) :
    p ∈ stab ↔ ∀ t : ℝ, oneParamG1 p t ∈ MulAction.stabilizer Stage1Group vac :=
  mem_stab_iff_fixes p

/-! ## 4. Stage 2: `SU(2)_L × SU(2)_R` on the `(1, 2, 2)` bidoublet -/

abbrev Stage2Group :=
  Matrix.specialUnitaryGroup (Fin 2) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ

/-- `(h, k) • Φ = h Φ k⁻¹`, with `k⁻¹ = star k` on the unitary group — the action whose generator is
`actEW A B Φ = A Φ − Φ B`. -/
def stage2Act (g : Stage2Group) (Φ : EWBidoublet) : EWBidoublet :=
  (g.1 : Matrix (Fin 2) (Fin 2) ℂ) * Φ * star (g.2 : Matrix (Fin 2) (Fin 2) ℂ)

theorem stage2Act_one (Φ : EWBidoublet) : stage2Act 1 Φ = Φ := by
  simp [stage2Act]

theorem stage2Act_mul (g h : Stage2Group) (Φ : EWBidoublet) :
    stage2Act (g * h) Φ = stage2Act g (stage2Act h Φ) := by
  simp only [stage2Act, Prod.fst_mul, Prod.snd_mul, Submonoid.coe_mul, StarMul.star_mul,
    Matrix.mul_assoc]

instance instMulActionStage2 : MulAction Stage2Group EWBidoublet where
  smul := stage2Act
  one_smul := stage2Act_one
  mul_smul := stage2Act_mul

theorem stage2_smul_def (g : Stage2Group) (Φ : EWBidoublet) : g • Φ = stage2Act g Φ := rfl

theorem exp_fixes_of_actEW_eq_zero (A B Φ : Matrix (Fin 2) (Fin 2) ℂ) (h : A * Φ - Φ * B = 0)
    (t : ℝ) : exp (t • A) * Φ * exp (-(t • B)) = Φ := by
  have h0 : A * Φ = Φ * B := sub_eq_zero.mp h
  have ht : (t • A) * Φ = Φ * (t • B) := by
    rw [rsmul_mul, mul_rsmul, h0]
  rw [exp_mul_of_mul_eq _ _ _ ht, Matrix.mul_assoc,
    ← Matrix.exp_add_of_commute _ _ ((Commute.refl (t • B)).neg_right), add_neg_cancel,
    NormedSpace.exp_zero, Matrix.mul_one]

/-- On a skew-adjoint generator, `star (exp (t B)) = exp (−t B)`. -/
theorem star_exp_smul (B : skewAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) (t : ℝ) :
    star (exp (t • (B : Matrix (Fin 2) (Fin 2) ℂ)))
      = exp (-(t • (B : Matrix (Fin 2) (Fin 2) ℂ))) := by
  have hB : star (B : Matrix (Fin 2) (Fin 2) ℂ) = -(B : Matrix (Fin 2) (Fin 2) ℂ) :=
    skewAdjoint.mem_iff.mp B.2
  rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul,
    star_trivial, ← Matrix.star_eq_conjTranspose, hB, rsmul_neg]

/-- The one-parameter subgroup of `SU(2)_L × SU(2)_R` generated by a pair `(a, b)` of `su(2)`
elements — any pair, as the joint stabiliser needs; unit 182's stage-2 algebra restricts `b`. -/
def oneParamLR (a b : traceless 2) (t : ℝ) : Stage2Group := (oneParam a t, oneParam b t)

theorem oneParamLR_smul (a b : traceless 2) (t : ℝ) (Φ : EWBidoublet) :
    oneParamLR a b t • Φ = exp (t • mat2 a) * Φ * exp (-(t • mat2 b)) := by
  rw [stage2_smul_def, stage2Act]
  change ((oneParam a t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Φ
    * star ((oneParam b t : Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = _
  rw [coe_oneParam, coe_oneParam, star_exp_smul]

/-- **THE GENERATOR OF THE `SU(2)_L × SU(2)_R` ACTION IS THE LIE-ALGEBRA ACTION `actEW`**, for
every pair of generators. -/
theorem hasDerivAt_stage2LR (a b : traceless 2) (Φ : EWBidoublet) :
    HasDerivAt (fun t : ℝ => oneParamLR a b t • Φ) (actEW (mat2 a) (mat2 b) Φ) 0 := by
  have h := ((hasDerivAt_exp_rsmul (mat2 a)).mul_const Φ).mul (hasDerivAt_exp_rsmul (-(mat2 b)))
  simp only [zero_rsmul, NormedSpace.exp_zero, mul_one, one_mul] at h
  convert h using 1
  · funext t
    rw [oneParamLR_smul]
    change _ = exp (t • mat2 a) * Φ * exp (t • -(mat2 b))
    rw [rsmul_neg]
  · rw [actEW, sub_eq_add_neg, Matrix.mul_neg]

/-- The one-parameter subgroup of `SU(2)_L × SU(2)_R` generated by `q ∈ su(2)_L ⊕ (T₃R line)`. -/
def oneParamG2 (q : EWLie) (t : ℝ) : Stage2Group := oneParamLR q.1 (q.2 : traceless 2) t

theorem oneParamG2_smul (q : EWLie) (t : ℝ) (Φ : EWBidoublet) :
    oneParamG2 q t • Φ = exp (t • mat2 q.1) * Φ * exp (-(t • mat2 (q.2 : traceless 2))) :=
  oneParamLR_smul q.1 q.2 t Φ

/-- **THE ONE-PARAMETER SUBGROUPS OF THE STAGE-2 STABILISER FIX THE ELECTROWEAK VACUUM.** -/
theorem stabEW_exp_fixes_vacEW (q : EWLie) (hq : q ∈ stabEW) (t : ℝ) :
    oneParamG2 q t • vacEW = vacEW := by
  rw [oneParamG2_smul]
  exact exp_fixes_of_actEW_eq_zero _ _ _ (LinearMap.mem_ker.mp hq) t

theorem oneParamG2_mem_stabilizer (q : EWLie) (hq : q ∈ stabEW) (t : ℝ) :
    oneParamG2 q t ∈ MulAction.stabilizer Stage2Group vacEW :=
  stabEW_exp_fixes_vacEW q hq t

/-- **THE UNBROKEN `U(1)_em`, AS A GROUP STATEMENT**: the electric charge's one-parameter subgroup
fixes the electroweak vacuum. -/
theorem charge_fixes_vacEW (t : ℝ) : oneParamG2 qG t • vacEW = vacEW :=
  stabEW_exp_fixes_vacEW qG qG_mem_stabEW t

/-- **THE GENERATOR OF THE STAGE-2 GROUP ACTION IS THE LIE-ALGEBRA ACTION `actEW`.** -/
theorem hasDerivAt_stage2 (q : EWLie) (Φ : EWBidoublet) :
    HasDerivAt (fun t : ℝ => oneParamG2 q t • Φ)
      (actEW (mat2 q.1) (mat2 (q.2 : traceless 2)) Φ) 0 :=
  hasDerivAt_stage2LR q.1 q.2 Φ

/-- **THE STAGE-2 UNBROKEN ALGEBRA IS EXACTLY THE SET OF GENERATORS WHOSE ONE-PARAMETER SUBGROUPS
FIX THE ELECTROWEAK VACUUM.** -/
theorem mem_stabEW_iff_fixes (q : EWLie) :
    q ∈ stabEW ↔ ∀ t : ℝ, oneParamG2 q t • vacEW = vacEW :=
  ⟨stabEW_exp_fixes_vacEW q, fun h =>
    LinearMap.mem_ker.mpr (eq_zero_of_hasDerivAt_of_const (hasDerivAt_stage2 q vacEW) h)⟩

theorem mem_stabEW_iff_mem_stabilizer (q : EWLie) :
    q ∈ stabEW ↔ ∀ t : ℝ, oneParamG2 q t ∈ MulAction.stabilizer Stage2Group vacEW :=
  mem_stabEW_iff_fixes q

/-! ## 5. Both stages at once: `SU(4) × SU(2)_L × SU(2)_R` on the pair of Higgs fields -/

abbrev FullGroup :=
  Matrix.specialUnitaryGroup (Fin 4) ℂ × Matrix.specialUnitaryGroup (Fin 2) ℂ
    × Matrix.specialUnitaryGroup (Fin 2) ℂ

def fullAct (g : FullGroup) (v : Bidoublet × EWBidoublet) : Bidoublet × EWBidoublet :=
  (stage1Act (g.1, g.2.2) v.1, stage2Act (g.2.1, g.2.2) v.2)

theorem fullAct_one (v : Bidoublet × EWBidoublet) : fullAct 1 v = v := by
  change (stage1Act 1 v.1, stage2Act 1 v.2) = v
  rw [stage1Act_one, stage2Act_one]

theorem fullAct_mul (g h : FullGroup) (v : Bidoublet × EWBidoublet) :
    fullAct (g * h) v = fullAct g (fullAct h v) := by
  simp only [fullAct, Prod.fst_mul, Prod.snd_mul]
  rw [← stage1Act_mul, ← stage2Act_mul]
  rfl

instance instMulActionFull : MulAction FullGroup (Bidoublet × EWBidoublet) where
  smul := fullAct
  one_smul := fullAct_one
  mul_smul := fullAct_mul

theorem full_smul_def (g : FullGroup) (v : Bidoublet × EWBidoublet) : g • v = fullAct g v := rfl

theorem expFull_smul_eq (p : Full) (t : ℝ) :
    expFull (t • p) = (oneParam p.1 t, oneParam p.2.1 t, oneParam p.2.2 t) := rfl

/-- `expFull (t • p)` acts on the pair as stage 1's subgroup on the first field and the
`SU(2)_L × SU(2)_R` subgroup of `(p.2.1, p.2.2)` on the second. -/
theorem expFull_smul_pair (p : Full) (t : ℝ) (v : Bidoublet × EWBidoublet) :
    expFull (t • p) • v = (oneParamG1 (p.1, p.2.2) t • v.1, oneParamLR p.2.1 p.2.2 t • v.2) :=
  rfl

/-- **THE EXPONENTIAL OF THE JOINT STABILISER FIXES BOTH VACUA**: `expFull` of `t • p`, for
`p ∈ jointStab`, lies in the stabiliser subgroup of `(vac, vacEW)`. -/
theorem jointStab_exp_fixes (p : Full) (hp : p ∈ jointStab) (t : ℝ) :
    expFull (t • p) • (vac, vacEW) = (vac, vacEW) := by
  obtain ⟨h1, h2⟩ := (mem_jointStab_iff p).mp hp
  rw [expFull_smul_pair, stab_exp_fixes_vac (p.1, p.2.2) h1 t, oneParamLR_smul,
    exp_fixes_of_actEW_eq_zero _ _ _ h2 t]

theorem expFull_mem_stabilizer (p : Full) (hp : p ∈ jointStab) (t : ℝ) :
    expFull (t • p) ∈ MulAction.stabilizer FullGroup (vac, vacEW) :=
  jointStab_exp_fixes p hp t

/-- **THE UNBROKEN `U(1)_em` FIXES BOTH VACUA**, exponentiated: `qFull`'s one-parameter subgroup. -/
theorem charge_fixes_both (t : ℝ) : expFull (t • qFull) • (vac, vacEW) = (vac, vacEW) :=
  jointStab_exp_fixes qFull qFull_mem_jointStab t

/-- **THE JOINT UNBROKEN ALGEBRA IS EXACTLY THE SET OF GENERATORS WHOSE ONE-PARAMETER SUBGROUPS OF
`SU(4) × SU(2)_L × SU(2)_R` FIX BOTH VACUA** — unit 183's `jointStab`, read at the group level. -/
theorem mem_jointStab_iff_fixes (p : Full) :
    p ∈ jointStab ↔ ∀ t : ℝ, expFull (t • p) • (vac, vacEW) = (vac, vacEW) := by
  refine ⟨jointStab_exp_fixes p, fun h => (mem_jointStab_iff p).mpr ⟨?_, ?_⟩⟩
  · exact mem_stab_of_fixes (p.1, p.2.2) fun t => by
      simpa only [expFull_smul_pair] using congrArg Prod.fst (h t)
  · exact eq_zero_of_hasDerivAt_of_const (hasDerivAt_stage2LR p.2.1 p.2.2 vacEW) fun t => by
      simpa only [expFull_smul_pair] using congrArg Prod.snd (h t)

theorem mem_jointStab_iff_mem_stabilizer (p : Full) :
    p ∈ jointStab ↔ ∀ t : ℝ, expFull (t • p) ∈ MulAction.stabilizer FullGroup (vac, vacEW) :=
  mem_jointStab_iff_fixes p

/-- **THE GENERATOR OF THE FULL ACTION ON THE PAIR OF HIGGS FIELDS**, at every pair: stage 1's
`act` on the first field and `actEW` on the second, with `SU(2)_R`'s generator in both. -/
theorem hasDerivAt_full (p : Full) (v : Bidoublet × EWBidoublet) :
    HasDerivAt (fun t : ℝ => expFull (t • p) • v)
      (act (mat4 p.1) (mat2 p.2.2) v.1, actEW (mat2 p.2.1) (mat2 p.2.2) v.2) 0 :=
  (hasDerivAt_stage1 (p.1, p.2.2) v.1).prodMk (hasDerivAt_stage2LR p.2.1 p.2.2 v.2)

/-- At the vacuum pair, the velocity of `p`'s orbit curve is unit 183's `jointOrbit p`. -/
theorem hasDerivAt_full_vac (p : Full) :
    HasDerivAt (fun t : ℝ => expFull (t • p) • (vac, vacEW)) (jointOrbit p) 0 :=
  hasDerivAt_full p (vac, vacEW)

/-- **UNIT 184'S TANGENT DIRECTIONS ARE VELOCITIES OF ORBIT CURVES**: a pair of Higgs-field
directions lies in `range jointOrbit` iff it is the velocity at `t = 0` of the curve
`t ↦ expFull (t • p) • (vac, vacEW)` in the vacuum's orbit, for some generator `p`. -/
theorem mem_range_jointOrbit_iff (w : Bidoublet × EWBidoublet) :
    w ∈ LinearMap.range jointOrbit ↔
      ∃ p : Full, HasDerivAt (fun t : ℝ => expFull (t • p) • (vac, vacEW)) w 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, hasDerivAt_full_vac p⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (hasDerivAt_full_vac p).unique hp⟩

end

end PatiSalamGaugeAction
