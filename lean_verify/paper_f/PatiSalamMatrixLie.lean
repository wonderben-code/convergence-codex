/-
  PatiSalamMatrixLie: the estate's `su(n)` is the Lie algebra of `SU(n)`, and at every vacuum the
  unbroken subalgebra is the Lie algebra of the unbroken group — in the sense matrix groups use: the
  matrices whose one-parameter curves stay in the group

  Campaign 3 hardening unit 217 (25 September 2026). Spine links L15 (Higgs sector) and L10 (the
  group level).

  WHY. Five sentences say this link is missing. `TracelessSkewDimension`: *"That this subspace is
  the Lie algebra of `SU(n)` — the tangent space at the identity of a smooth group — is a statement
  about a smooth structure, and nothing here builds one."* `TracelessSkewLie`, amended at unit 188:
  the group *"now has the Lie algebra attached in one direction"* — `exp` carries `su(n)` into
  `SU(n)`. `PatiSalamStabiliserGroup` (unit 199): *"the group's Lie algebra is not computed here"*.
  `PatiSalamFirstStageClassification`, amended at unit 213: that the unbroken subalgebras *"are
  these groups' Lie algebras stays unproved"*; `PatiSalamBrokenCount`'s NOT list says the same. For
  a group of matrices there is a definition that needs no smooth structure: its Lie algebra is the
  set of matrices `M` with `exp (t M)` in the group for every real `t` (the definition matrix-group
  texts use, e.g. Hall, *Lie Groups, Lie Algebras, and Representations*, ch. 3). This file proves
  the other direction of unit 188's, so that `su(n)` is exactly `SU(n)`'s Lie algebra in that sense,
  and reads off the Lie algebra of the unbroken group at every vacuum. Unit 191 characterised the
  unbroken ALGEBRAS through one-parameter subgroups at the two chosen vacua only; here the
  characterisation holds at every vacuum and every pair of vacua.

  WHAT IS PROVED.
  (1) **`forall_exp_mem_specialUnitaryGroup_iff`**: `exp (t X) ∈ SU(n)` for every real `t` if and
      only if `X` is skew-Hermitian and traceless;
      `forall_exp_mem_specialUnitaryGroup_iff_traceless` is the same with the estate's `traceless n`
      named. One direction is unit 188's `exp_mem_specialUnitaryGroup`. The other: the curve
      `t ↦ exp(tX)ᴴ exp(tX)` is constantly `1` and has velocity `Xᴴ + X` at `0`
      (`hasDerivAt_star_exp_mul_exp`, through `star_exp_rsmul`), so `X` is skew-Hermitian
      (`mem_skewAdjoint_of_forall_exp_mem_unitaryGroup`); then unit 188's `det (exp X) = exp (tr X)`
      makes `t ↦ exp (t · tr X)` constantly `1`, and its velocity at `0` is `tr X`
      (`hasDerivAt_cexp_ofReal_mul`, `trace_eq_zero_of_forall_exp_mem_specialUnitaryGroup`).
      `trace_rsmul` restates `Matrix.trace_smul` in this file's elaboration, for unit 191's reason.
  (2) Stage 1, at every vacuum. **`mem_stabAt_iff_fixes`**: `p ∈ stabAt X` if and only if
      `oneParamG1 p t • X = X` for every `t`, and `mem_stabAt_iff_mem_stabilizer` — unit 191's
      `mem_stab_iff_fixes` without `X = vac`. `mem_range_orbitMapAt_iff`: the broken directions at
      `X` are exactly the velocities at `0` of the orbit curves through `X`.
  (3) The unbroken group's Lie algebra. `matLie G`, for `G ≤ SU(4) × SU(2)`: the pairs `(A, B)` of
      matrices with `(exp (t A), exp (t B)) ∈ G` for every real `t`. **`mem_matLie_top_iff`**: for
      the whole group it is `su(4) ⊕ su(2)`. **`mem_matLie_stabilizer_iff`**: for `G = Stab X` it is
      exactly the matrices of `stabAt X`, at every `X`, so the unbroken subalgebra of unit 213 — of
      dimension nine, six or four — IS the unbroken group's Lie algebra in this sense.
      `eq_oneParamG1`: a group element with the one-parameter subgroup's matrices is its element.
  (4) Stage 2 and both stages, at every vacuum. `orbitEWAt`, **`stabEWAt Φ`** (the unbroken
      subalgebra of `su(2)_L ⊕ su(2)_R` at any `Φ`), **`mem_stabEWAt_iff_fixes`**; `jointOrbitAt`,
      **`jointStabAt v`** at any pair `v = (X, Φ)`, with `orbitEWAt_vacEW`, `jointOrbitAt_vac` and
      `jointStabAt_vac` (units 183's objects, by `rfl`); `mem_jointStabAt_iff`,
      **`mem_jointStabAt_iff_fixes`**, `mem_jointStabAt_iff_mem_stabilizer` and
      `mem_range_jointOrbitAt_iff` — unit 191's `mem_stabEW_iff_fixes`, `mem_jointStab_iff_fixes`
      and `mem_range_jointOrbit_iff` without the chosen vacua. `matLieFull` and
      **`mem_matLieFull_stabilizer_iff`**: the joint unbroken group's Lie algebra at any pair is
      exactly the matrices of `jointStabAt v`.

  NOT PROVED, said exactly.
  • No smooth structure. *Lie algebra* here is the matrix-group definition; that it is the tangent
    space at the identity of a manifold is not stated, and no manifold or Lie-group structure is
    used (unit 209's reason: the pinned Mathlib puts none on `specialUnitaryGroup`).
  • The Lie algebra does not determine the group. That the one-parameter subgroups of `stabAt X`
    generate `Stab X`, or that `Stab X` is connected, is not shown; the groups themselves are units
    199–212's.
  • At stage 2 and for pairs, the subalgebras are characterised at every vacuum, not classified:
    which groups and which dimensions occur there beyond units 182–207's vacua is not computed.
    ⚠ 25 September 2026 (hardening unit 219, `paper_f/ElectroweakCustodial.lean`): at stage 2 the
    dimensions are computed — six, three or one (`finrank_stabEWAt_zero`,
    `finrank_stabEWAt_dichotomy`) — and `mem_matLieEW_stabilizer_iff` is this file's
    `mem_matLie_stabilizer_iff` at stage 2. The groups at stage 2, and everything for pairs, still
    are not.
  • The bracket is not carried: that `stabAt X` is closed under the commutator is unit 180's
    argument at `X`, and it needs `TracelessSkewLie`, which this file does not import. Measured:
    with `TracelessSkewLie` in the import closure, `hasDerivAt_star_exp_mul_exp`'s product rule
    fails to find `ContinuousSMul ℝ (Matrix (Fin n) (Fin n) ℂ)` — so does it with
    `Mathlib.Algebra.Lie.Classical` or `Mathlib.Algebra.Lie.Graded` alone, and raising the
    instance-search budget twentyfold does not help; with `Mathlib.Algebra.Lie.Prod` alone it
    elaborates. `ElectroweakVacuumStabiliser` records a timeout of the same family.
    ⚠ 25 September 2026 (hardening unit 218, `paper_f/PatiSalamUnbrokenLieAlgebra.lean`): carried
    there — `stabLieAt X` is a `LieSubalgebra ℝ` of `gl(4) × gl(2)` at every vacuum, and
    `matLie_stabilizer_eq` identifies the unbroken group's Lie algebra with it. That file imports
    this one and `PatiSalamStabiliserLie`, and elaborates no derivative. Kept as written
    (`ERRATUM 94`).
  • Goldstone's theorem, a potential, masses: unchanged (units 179 and 184).

  HYPOTHESES, READ OFF THE BINDERS (`ERRATUM 455`). `mem_skewAdjoint_of_forall_exp_mem_unitaryGroup`
  takes `exp (t X) ∈ U(n)` for every `t`; `trace_eq_zero_of_forall_exp_mem_specialUnitaryGroup`
  takes `exp (t X) ∈ SU(n)` for every `t`; `eq_oneParamG1` takes the two matrix equations. The rest
  take elements of their types and nothing else: every statement about vacua holds at every `X`,
  `Φ` and pair, zero included.

  NEAR-DUPLICATES CHECKED BEFORE WRITING (`ERRATUM 270`). The file's 29 declaration names and its
  module name were run against the estate's theorem index, every `paper_f` declaration and the file
  list: none is taken. The nearest statements are unit 188's `exp_mem_specialUnitaryGroup` (the
  forward half of (1)) and `star_exp_smul` (`star_exp_rsmul` for skew-adjoint `B` only); unit 191's
  `mem_stab_iff_fixes`, `mem_stabEW_iff_fixes`, `mem_jointStab_iff_fixes` and
  `mem_range_jointOrbit_iff`, which (2) and (4) generalise, and its `hasDerivAt_exp_rsmul`,
  `exp_fixes_of_act_eq_zero`, `exp_fixes_of_actEW_eq_zero`, `hasDerivAt_stage1`,
  `hasDerivAt_stage2LR`, `hasDerivAt_full` and `eq_zero_of_hasDerivAt_of_const`, all used; unit
  183's `orbitEWFull`, `jointOrbit` and `jointStab`, which `orbitEWAt`, `jointOrbitAt` and
  `jointStabAt` are at their vacua; unit 180's `toMat`, which is not redefined here — (3) is stated
  with the matrices `mat4 p.1`, `mat2 p.2` directly. The pinned Mathlib has
  `Matrix.exp_conjTranspose`, `hasDerivAt_exp_smul_const'` and `HasDerivAt.cexp`, used, and no
  statement that a matrix whose exponential curve is unitary is skew-Hermitian.

  `#print axioms` on all 29 declarations below: each is `[propext, Classical.choice, Quot.sound]`.
-/

import PatiSalamBrokenCount

open Matrix NormedSpace TracelessSkewDimension SkewAdjointExponential
open PatiSalamVacuumStabiliser PatiSalamGaugeAction PatiSalamBrokenCount ElectroweakVacuumStabiliser
  PatiSalamTwoStageStabiliser
open scoped Matrix.Norms.Operator

namespace PatiSalamMatrixLie

noncomputable section

variable {n : ℕ}

/-! ## 1. `su(n)` is the Lie algebra of `SU(n)` -/

/-- `exp (t X)ᴴ = exp (t Xᴴ)` for real `t` — unit 188's `star_exp_smul` without skew-adjointness. -/
theorem star_exp_rsmul (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    star (exp (t • X)) = exp (t • star X) := by
  rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul,
    star_trivial, ← Matrix.star_eq_conjTranspose]

/-- `trace (t X) = t · trace X` for real `t`, restated in this file's elaboration (as unit 191's
`rsmul_mul`). -/
theorem trace_rsmul (t : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : trace (t • X) = (t : ℂ) * trace X := by
  rw [show trace (t • X) = t • trace X from Matrix.trace_smul t X, Complex.real_smul]

/-- The unitarity curve `t ↦ exp (t X)ᴴ exp (t X)` has velocity `Xᴴ + X` at `0`. -/
theorem hasDerivAt_star_exp_mul_exp (X : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => star (exp (t • X)) * exp (t • X)) (star X + X) 0 := by
  have h := (hasDerivAt_exp_rsmul (star X)).mul (hasDerivAt_exp_rsmul X)
  simp only [zero_rsmul, NormedSpace.exp_zero, Matrix.mul_one, Matrix.one_mul] at h
  convert h using 1
  funext t
  rw [star_exp_rsmul]
  rfl

/-- **A matrix whose exponential curve is unitary is skew-Hermitian.** -/
theorem mem_skewAdjoint_of_forall_exp_mem_unitaryGroup (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, exp (t • X) ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    X ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) := by
  have h0 := eq_zero_of_hasDerivAt_of_const (hasDerivAt_star_exp_mul_exp X)
    (x := (1 : Matrix (Fin n) (Fin n) ℂ)) fun t => (Matrix.mem_unitaryGroup_iff').mp (h t)
  rw [skewAdjoint.mem_iff]
  exact eq_neg_of_add_eq_zero_left h0

/-- `t ↦ exp (t c)` has velocity `c` at `0`. -/
theorem hasDerivAt_cexp_ofReal_mul (c : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * c)) c 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c).cexp
  simpa using h

/-- **A matrix whose exponential curve lies in `SU(n)` is traceless.** -/
theorem trace_eq_zero_of_forall_exp_mem_specialUnitaryGroup (X : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, exp (t • X) ∈ Matrix.specialUnitaryGroup (Fin n) ℂ) : trace X = 0 := by
  have hX := mem_skewAdjoint_of_forall_exp_mem_unitaryGroup X fun t =>
    (Matrix.mem_specialUnitaryGroup_iff.mp (h t)).1
  have hc : ∀ t : ℝ, Complex.exp ((t : ℂ) * trace X) = 1 := by
    intro t
    have htX : t • X ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) := by
      rw [skewAdjoint.mem_iff] at hX ⊢
      rw [star_smul, hX, star_trivial, rsmul_neg]
    have hd := det_exp_of_skewAdjoint (t • X) htX
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp (h t)).2, trace_rsmul] at hd
    exact hd.symm
  exact eq_zero_of_hasDerivAt_of_const (hasDerivAt_cexp_ofReal_mul (trace X)) hc

/-- **THE LIE ALGEBRA OF `SU(n)` IS `su(n)`**: `exp (t X) ∈ SU(n)` for every real `t` exactly when
`X` is skew-Hermitian and traceless. -/
theorem forall_exp_mem_specialUnitaryGroup_iff (X : Matrix (Fin n) (Fin n) ℂ) :
    (∀ t : ℝ, exp (t • X) ∈ Matrix.specialUnitaryGroup (Fin n) ℂ) ↔
      X ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) ∧ trace X = 0 := by
  refine ⟨fun h => ⟨mem_skewAdjoint_of_forall_exp_mem_unitaryGroup X fun t =>
    (Matrix.mem_specialUnitaryGroup_iff.mp (h t)).1,
    trace_eq_zero_of_forall_exp_mem_specialUnitaryGroup X h⟩, fun ⟨hX, htr⟩ t => ?_⟩
  refine exp_mem_specialUnitaryGroup (t • X) ?_ ?_
  · rw [skewAdjoint.mem_iff] at hX ⊢
    rw [star_smul, hX, star_trivial, rsmul_neg]
  · rw [trace_rsmul, htr, mul_zero]

/-- The same, with the estate's `traceless n` named. -/
theorem forall_exp_mem_specialUnitaryGroup_iff_traceless (X : Matrix (Fin n) (Fin n) ℂ) :
    (∀ t : ℝ, exp (t • X) ∈ Matrix.specialUnitaryGroup (Fin n) ℂ) ↔
      ∃ A : traceless n, ((A : skewAdjoint (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)
        = X := by
  rw [forall_exp_mem_specialUnitaryGroup_iff]
  constructor
  · rintro ⟨hX, htr⟩
    refine ⟨⟨⟨X, hX⟩, LinearMap.mem_ker.mpr ?_⟩, rfl⟩
    change (trace X).im = 0
    rw [htr, Complex.zero_im]
  · rintro ⟨A, rfl⟩
    exact ⟨A.1.2, trace_eq_zero_of_mem_traceless A.2⟩

/-! ## 2. Stage 1 at every vacuum -/

/-- **At every first-stage vacuum, the unbroken subalgebra is the set of generators whose
one-parameter subgroups fix it** — unit 191's `mem_stab_iff_fixes`, without `X = vac`. -/
theorem mem_stabAt_iff_fixes (X : Bidoublet) (p : PSLie) :
    p ∈ stabAt X ↔ ∀ t : ℝ, oneParamG1 p t • X = X := by
  constructor
  · intro hp t
    rw [oneParamG1_smul]
    exact exp_fixes_of_act_eq_zero _ _ X ((mem_stabAt_iff X p).mp hp) t
  · intro h
    exact (mem_stabAt_iff X p).mpr (eq_zero_of_hasDerivAt_of_const (hasDerivAt_stage1 p X) h)

theorem mem_stabAt_iff_mem_stabilizer (X : Bidoublet) (p : PSLie) :
    p ∈ stabAt X ↔ ∀ t : ℝ, oneParamG1 p t ∈ MulAction.stabilizer Stage1Group X :=
  mem_stabAt_iff_fixes X p

/-- **The broken directions at every vacuum are the velocities of its orbit curves** — unit 191's
`mem_range_jointOrbit_iff` at stage 1, without `X = vac`. -/
theorem mem_range_orbitMapAt_iff (X w : Bidoublet) :
    w ∈ LinearMap.range (orbitMapAt X) ↔
      ∃ p : PSLie, HasDerivAt (fun t : ℝ => oneParamG1 p t • X) w 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, hasDerivAt_stage1 p X⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (hasDerivAt_stage1 p X).unique hp⟩

/-! ## 3. The unbroken group's Lie algebra -/

/-- **The Lie algebra of a subgroup of `SU(4) × SU(2)`, as matrix groups define it**: the pairs of
matrices whose one-parameter curves `t ↦ (exp (t A), exp (t B))` stay in the subgroup. -/
def matLie (G : Subgroup Stage1Group) :
    Set (Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :=
  {M | ∀ t : ℝ, ∃ g ∈ G, (g.1 : Matrix (Fin 4) (Fin 4) ℂ) = exp (t • M.1) ∧
    (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • M.2)}

/-- A group element with the one-parameter subgroup's matrices is its element. -/
theorem eq_oneParamG1 (p : PSLie) (t : ℝ) (g : Stage1Group)
    (h1 : (g.1 : Matrix (Fin 4) (Fin 4) ℂ) = exp (t • mat4 p.1))
    (h2 : (g.2 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • mat2 p.2)) : g = oneParamG1 p t :=
  Prod.ext (Subtype.ext (h1.trans (coe_oneParam p.1 t).symm))
    (Subtype.ext (h2.trans (coe_oneParam p.2 t).symm))

/-- **THE LIE ALGEBRA OF `SU(4) × SU(2)` IS `su(4) ⊕ su(2)`.** -/
theorem mem_matLie_top_iff (M : Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :
    M ∈ matLie ⊤ ↔ ∃ p : PSLie, mat4 p.1 = M.1 ∧ mat2 p.2 = M.2 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (forall_exp_mem_specialUnitaryGroup_iff_traceless M.1).mp fun t => by
      obtain ⟨g, -, h1, -⟩ := h t
      exact h1 ▸ g.1.2
    obtain ⟨b, hb⟩ := (forall_exp_mem_specialUnitaryGroup_iff_traceless M.2).mp fun t => by
      obtain ⟨g, -, -, h2⟩ := h t
      exact h2 ▸ g.2.2
    exact ⟨(a, b), ha, hb⟩
  · rintro ⟨p, h1, h2⟩ t
    exact ⟨oneParamG1 p t, Subgroup.mem_top _, h1 ▸ coe_oneParam p.1 t, h2 ▸ coe_oneParam p.2 t⟩

/-- **THE LIE ALGEBRA OF THE UNBROKEN GROUP AT ANY FIRST-STAGE VACUUM IS THE UNBROKEN SUBALGEBRA
THERE**: `(exp (t A), exp (t B)) ∈ Stab X` for every real `t` exactly when `(A, B)` are the
matrices of an element of `stabAt X`. -/
theorem mem_matLie_stabilizer_iff (X : Bidoublet)
    (M : Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :
    M ∈ matLie (MulAction.stabilizer Stage1Group X) ↔
      ∃ p ∈ stabAt X, mat4 p.1 = M.1 ∧ mat2 p.2 = M.2 := by
  constructor
  · intro h
    obtain ⟨p, h1, h2⟩ := (mem_matLie_top_iff M).mp fun t => by
      obtain ⟨g, -, hg1, hg2⟩ := h t
      exact ⟨g, Subgroup.mem_top _, hg1, hg2⟩
    refine ⟨p, (mem_stabAt_iff_fixes X p).mpr fun t => ?_, h1, h2⟩
    obtain ⟨g, hg, hg1, hg2⟩ := h t
    rw [← eq_oneParamG1 p t g (hg1.trans (h1 ▸ rfl)) (hg2.trans (h2 ▸ rfl))]
    exact hg
  · rintro ⟨p, hp, h1, h2⟩ t
    exact ⟨oneParamG1 p t, (mem_stabAt_iff_mem_stabilizer X p).mp hp t, h1 ▸ coe_oneParam p.1 t,
      h2 ▸ coe_oneParam p.2 t⟩

/-! ## 4. Stage 2 and both stages, at every vacuum -/

/-- The electroweak orbit map at any `Φ`: `(L, R) ↦ L Φ − Φ R` — unit 183's `orbitEWFull` at `Φ`. -/
def orbitEWAt (Φ : EWBidoublet) : traceless 2 × traceless 2 →ₗ[ℝ] EWBidoublet where
  toFun q := actEW (mat2 q.1) (mat2 q.2) Φ
  map_add' q q' := by
    simp only [Prod.fst_add, Prod.snd_add, mat2, Submodule.coe_add, AddSubgroup.coe_add, actEW,
      Matrix.add_mul, Matrix.mul_add]
    abel
  map_smul' r q := by
    simp only [Prod.smul_fst, Prod.smul_snd, mat2, Submodule.coe_smul, skewAdjoint.val_smul, actEW,
      RingHom.id_apply]
    erw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]

/-- **The unbroken subalgebra of `su(2)_L ⊕ su(2)_R` at any electroweak vacuum `Φ`.** -/
def stabEWAt (Φ : EWBidoublet) : Submodule ℝ (traceless 2 × traceless 2) :=
  LinearMap.ker (orbitEWAt Φ)

theorem orbitEWAt_vacEW : orbitEWAt vacEW = orbitEWFull := rfl

/-- **At every electroweak vacuum, the unbroken subalgebra is the set of generators whose
one-parameter subgroups fix it** — unit 191's `mem_stabEW_iff_fixes`, without `Φ = vacEW` and on the
whole of `su(2)_L ⊕ su(2)_R`. -/
theorem mem_stabEWAt_iff_fixes (Φ : EWBidoublet) (q : traceless 2 × traceless 2) :
    q ∈ stabEWAt Φ ↔ ∀ t : ℝ, oneParamLR q.1 q.2 t • Φ = Φ := by
  constructor
  · intro hq t
    rw [oneParamLR_smul]
    exact exp_fixes_of_actEW_eq_zero _ _ Φ (LinearMap.mem_ker.mp hq) t
  · intro h
    exact LinearMap.mem_ker.mpr (eq_zero_of_hasDerivAt_of_const (hasDerivAt_stage2LR q.1 q.2 Φ) h)

/-- Both vacua at once, at any pair `v = (X, Φ)` — unit 183's `jointOrbit` at `v`. -/
def jointOrbitAt (v : Bidoublet × EWBidoublet) : Full →ₗ[ℝ] Bidoublet × EWBidoublet :=
  LinearMap.prod ((orbitMapAt v.1).comp stage1)
    ((orbitEWAt v.2).comp (LinearMap.snd ℝ (traceless 4) (traceless 2 × traceless 2)))

/-- **The joint unbroken subalgebra at any pair of vacua.** -/
def jointStabAt (v : Bidoublet × EWBidoublet) : Submodule ℝ Full := LinearMap.ker (jointOrbitAt v)

theorem jointOrbitAt_vac : jointOrbitAt (vac, vacEW) = jointOrbit := rfl

theorem jointStabAt_vac : jointStabAt (vac, vacEW) = jointStab := rfl

theorem mem_jointStabAt_iff (v : Bidoublet × EWBidoublet) (p : Full) :
    p ∈ jointStabAt v ↔ (p.1, p.2.2) ∈ stabAt v.1 ∧ p.2 ∈ stabEWAt v.2 := by
  rw [jointStabAt, LinearMap.mem_ker, jointOrbitAt, LinearMap.prod_apply, Prod.mk_eq_zero]
  rfl

/-- **At every pair of vacua, the joint unbroken subalgebra is the set of generators whose
one-parameter subgroups of `SU(4) × SU(2)_L × SU(2)_R` fix both** — unit 191's
`mem_jointStab_iff_fixes`, without `(X, Φ) = (vac, vacEW)`. -/
theorem mem_jointStabAt_iff_fixes (v : Bidoublet × EWBidoublet) (p : Full) :
    p ∈ jointStabAt v ↔ ∀ t : ℝ, expFull (t • p) • v = v := by
  rw [mem_jointStabAt_iff, mem_stabAt_iff_fixes, mem_stabEWAt_iff_fixes]
  constructor
  · rintro ⟨h1, h2⟩ t
    rw [expFull_smul_pair]
    exact Prod.ext (h1 t) (h2 t)
  · intro h
    exact ⟨fun t => by simpa only [expFull_smul_pair] using congrArg Prod.fst (h t),
      fun t => by simpa only [expFull_smul_pair] using congrArg Prod.snd (h t)⟩

theorem mem_jointStabAt_iff_mem_stabilizer (v : Bidoublet × EWBidoublet) (p : Full) :
    p ∈ jointStabAt v ↔ ∀ t : ℝ, expFull (t • p) ∈ MulAction.stabilizer FullGroup v :=
  mem_jointStabAt_iff_fixes v p

/-- **The joint broken directions at every pair are the velocities of its orbit curves** — unit
191's `mem_range_jointOrbit_iff`, without `(X, Φ) = (vac, vacEW)`. -/
theorem mem_range_jointOrbitAt_iff (v w : Bidoublet × EWBidoublet) :
    w ∈ LinearMap.range (jointOrbitAt v) ↔
      ∃ p : Full, HasDerivAt (fun t : ℝ => expFull (t • p) • v) w 0 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, hasDerivAt_full p v⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (hasDerivAt_full p v).unique hp⟩

/-- The Lie algebra of a subgroup of `SU(4) × SU(2)_L × SU(2)_R`, as matrix groups define it. -/
def matLieFull (G : Subgroup FullGroup) :
    Set (Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :=
  {M | ∀ t : ℝ, ∃ g ∈ G, (g.1 : Matrix (Fin 4) (Fin 4) ℂ) = exp (t • M.1) ∧
    (g.2.1 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • M.2.1) ∧
    (g.2.2 : Matrix (Fin 2) (Fin 2) ℂ) = exp (t • M.2.2)}

/-- **THE LIE ALGEBRA OF THE UNBROKEN GROUP OF ANY PAIR OF VACUA IS THE JOINT UNBROKEN SUBALGEBRA
THERE.** -/
theorem mem_matLieFull_stabilizer_iff (v : Bidoublet × EWBidoublet)
    (M : Matrix (Fin 4) (Fin 4) ℂ × Matrix (Fin 2) (Fin 2) ℂ × Matrix (Fin 2) (Fin 2) ℂ) :
    M ∈ matLieFull (MulAction.stabilizer FullGroup v) ↔
      ∃ p ∈ jointStabAt v, mat4 p.1 = M.1 ∧ mat2 p.2.1 = M.2.1 ∧ mat2 p.2.2 = M.2.2 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := (forall_exp_mem_specialUnitaryGroup_iff_traceless M.1).mp fun t => by
      obtain ⟨g, -, h1, -, -⟩ := h t
      exact h1 ▸ g.1.2
    obtain ⟨b, hb⟩ := (forall_exp_mem_specialUnitaryGroup_iff_traceless M.2.1).mp fun t => by
      obtain ⟨g, -, -, h2, -⟩ := h t
      exact h2 ▸ g.2.1.2
    obtain ⟨c, hc⟩ := (forall_exp_mem_specialUnitaryGroup_iff_traceless M.2.2).mp fun t => by
      obtain ⟨g, -, -, -, h3⟩ := h t
      exact h3 ▸ g.2.2.2
    refine ⟨(a, b, c), (mem_jointStabAt_iff_fixes v _).mpr fun t => ?_, ha, hb, hc⟩
    obtain ⟨g, hg, h1, h2, h3⟩ := h t
    have hge : g = expFull (t • (a, b, c)) := by
      rw [expFull_smul_eq]
      refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · rw [h1, coe_oneParam, ← ha]
      · rw [h2, coe_oneParam, ← hb]
      · rw [h3, coe_oneParam, ← hc]
    rw [← hge]
    exact hg
  · rintro ⟨p, hp, h1, h2, h3⟩ t
    refine ⟨expFull (t • p), (mem_jointStabAt_iff_mem_stabilizer v p).mp hp t, ?_, ?_, ?_⟩
    · rw [expFull_smul_eq, ← h1]
      exact coe_oneParam _ t
    · rw [expFull_smul_eq, ← h2]
      exact coe_oneParam _ t
    · rw [expFull_smul_eq, ← h3]
      exact coe_oneParam _ t

end

end PatiSalamMatrixLie
