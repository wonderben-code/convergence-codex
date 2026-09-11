import CovariantOrderCovTensor
import CurvatureCovBundle

/-!
# `∇R` on tangent vectors and bundled, for ANY connection of class `C^(k+1)`

**The unit entry 32's §6 named**, and the last file of the re-definition `ERRATUM 498` priced
except one. `CurvatureCovBundle` takes `∇R` from fields to **vectors** — through their extensions —
and bundles it as a continuous bilinear map into the endomorphisms, **for the Levi-Civita
connection**. The thing that makes the extension harmless is tensoriality, and entry 126 made that
abstract, so this file is that one with the connection a variable.

**TWELVE OF ITS THIRTEEN DECLARATIONS LIFT; THE THIRTEENTH DOES NOT, AND THE REASON IS NAMED RATHER
THAN SHRUGGED AT.** `CurvatureCovBundle.covRiemannAt_cyclic` — the second Bianchi identity for three
arbitrary tangent vectors — is proved from `CurvatureBianchiSecond.covRiemann_cyclic_endo`, the
identity **for fields**, which is Levi-Civita-only and is not generalised. Generalising it needs the
cyclic Jacobi identity for Lie brackets and three derivatives of the differentiated field, which is
a file of eleven declarations, so the abstract cyclic identity is **not attempted here, no cost
claimed** (`ERRATUM 246`). It is `C` one step out, and entry 32 says so in the same words.

## What is proved

**`cmdiffAt_ext`** (private) — the order at which every extension below is taken, from Mathlib's
order-polymorphic `contMDiffAt_extend'`.

**`covRiemannAt`** — **`(∇_u R)(v, w)` ON TANGENT VECTORS**, through their extensions to sections:
`curvEndo`'s device, one derivative up.

**`covRiemannAt_eq`** — **AND ON FIELDS IT IS `covRiemann`**, which is entry 126's tensoriality
doing the only work it was built for: it is what makes the extension harmless.

**`covRiemannAt_add_left`**, **`covRiemannAt_smul_left`**, **`covRiemannAt_add_right`**,
**`covRiemannAt_smul_right`** — the four slot laws on vectors, each one entry 124's law on the
extensions plus entry 126's tensoriality to replace an extension by the field it agrees with.

**`covRiemann_add_dir`**, **`covRiemann_smul_dir`** — **AND `∇R` IS LINEAR IN THE DIRECTION**, which
`CovariantOrderCovDeriv` never states. These take **no hypothesis at all**, not even `k ≠ 0`: the
induced connection is a continuous linear map in its direction and the two corrections are linear in
theirs, so it is `map_add`, `map_smul` and the `curvEndo` slot laws.

**`covRiemannAt_add_dir`**, **`covRiemannAt_smul_dir`** — the same on vectors, by definition.

**`covRiemannHom`**, **`covRiemannHom_apply`** — **`∇_u R` BUNDLED IN ITS TWO CURVATURE SLOTS**:
`T_xM →L T_xM →L (T_xM →L T_xM)`, which is the object `CurvatureCovTensor`'s fence asked for, now
over an arbitrary connection.

**`covRiemannAt_swap`** — antisymmetry in the two curvature slots, on vectors.

**`covRiemannAt_eq_leviCivita`** — **AND `CurvatureCovBundle`'S AGREEMENT THEOREM IS THIS ONE
SPECIALISED**, with `CovariantOrderCovDeriv.covRiemann_eq` (`rfl`) identifying the objects. The
fifth checked subsumption in six units; recorded by hand because no mode here can see a duplicate
under a different name.

## What is NOT here

* **NO SECOND BIANCHI IDENTITY ON VECTORS**, for the reason above: its input is the identity on
  fields, and that is Levi-Civita-only. **This is the one declaration of the file being mirrored
  that does not lift**, and naming which one and why is the point of saying so.
* **NOT THE FOUR-DEEP BUNDLING.** `covRiemannHom` fixes the direction `u` and bundles the two
  curvature slots; bundling `u` as well needs `covRiemannAt_add_dir` and `covRiemannAt_smul_dir`,
  **which are proved here**, and what stands in the way is elaboration rather than mathematics —
  three-deep nesting already cost `HomCovariant.homCovFun_smul_id` a scoped
  `synthInstance.maxHeartbeats`. That is an `UNLOCK_WATCHLIST` residue with a trigger, filed by
  entry 118 for the Levi-Civita case, and it is unchanged by this file.
* **NO REGULARITY OF THE BUNDLED OBJECT.** Entry 125 makes `y ↦ (∇_X R)(Y, Z)(y)` a `C^k` section
  for FIELDS; nothing makes `y ↦ covRiemannHom y u` a `C^k` section of the doubly-nested bundle, and
  that is not plumbing — the extensions are taken at one point and a section statement compares
  points, so the object would have to be rebuilt from a field of directions. Same residue, same
  trigger, unstarted.
* **NO TRACE, NO DIVERGENCE**: a trace needs a metric.
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number.

**No wall moves. No published tag moves.**

**THE NAMES COLLIDE WITH `CurvatureCovBundle`'S ON PURPOSE**, as entries 124 and 126 did with their
mirrors, and the reason is the same theorem: `covRiemann_eq` identifies the two `∇R`s by `rfl`, so
the names denote one object at two generalities. Recorded in `newnames_accepted.txt`.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `E` normed over `ℝ` with `[CompleteSpace E]`
and `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]`, `[IsManifold I 3 M]`, `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`,
`[CurvatureTensor.IsLocallyC1 cov]`, and `[CovariantOrderClass.IsLocallyCk ((k : WithTop ℕ∞) + 1)
cov]` with `k ≠ 0` wherever a slot law is used — **no metric at any order**, where
`CurvatureCovBundle` asks for a `C^(k+2)` metric and its companion at `2`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderCovBundle

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CovariantOrderClass
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [CurvatureTensor.IsLocallyC1 cov]

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureTensor.contMDiffVectorBundle_two KoszulManifold.finDimTangent
  CovariantOrderEndo.contMDiffVectorBundle_add_two'

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M] [CurvatureTensor.IsLocallyC1 cov] in
/-- The order at which every extension used below is taken. -/
private theorem cmdiffAt_ext (x : M) (v : TangentSpace I x) :
    CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (extend E v)) x :=
  contMDiffAt_extend' (k := (k : WithTop ℕ∞) + 1 + 1) I E v

/-- **`(∇_u R)(v, w)` ON TANGENT VECTORS**, through their extensions to sections — `curvEndo`'s
device, one derivative up. -/
noncomputable def covRiemannAt (x : M) (u v w : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  CovariantOrderCovDeriv.covRiemann cov (extend E v) (extend E w) x u

/-! ## Linearity in the direction, which needs no hypothesis at all -/

/-- **`∇R` IS ADDITIVE IN THE DIRECTION**: the induced connection is a continuous linear map in its
direction and the two corrections are linear in theirs. No hypothesis, not even `k ≠ 0`. -/
theorem covRiemann_add_dir {Y Z : Π x : M, TangentSpace I x} {x : M} (u u' : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (u + u')
      = CovariantOrderCovDeriv.covRiemann cov Y Z x u
        + CovariantOrderCovDeriv.covRiemann cov Y Z x u' := by
  simp only [CovariantOrderCovDeriv.covRiemann, map_add, curvEndo_add_left, curvEndo_add_right]
  abel

/-- **AND HOMOGENEOUS IN THE DIRECTION.** -/
theorem covRiemann_smul_dir {Y Z : Π x : M, TangentSpace I x} {x : M} (c : ℝ)
    (u : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (c • u)
      = c • CovariantOrderCovDeriv.covRiemann cov Y Z x u := by
  simp only [CovariantOrderCovDeriv.covRiemann, map_smul, curvEndo_smul_left, curvEndo_smul_right]
  module

theorem covRiemannAt_add_dir {x : M} (u u' v w : TangentSpace I x) :
    covRiemannAt cov x (u + u') v w = covRiemannAt cov x u v w + covRiemannAt cov x u' v w :=
  covRiemann_add_dir cov u u'

theorem covRiemannAt_smul_dir {x : M} (c : ℝ) (u v w : TangentSpace I x) :
    covRiemannAt cov x (c • u) v w = c • covRiemannAt cov x u v w :=
  covRiemann_smul_dir cov c u

variable [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]

/-! ## The vector form agrees with the field form, and is linear in both slots -/

/-- **AND ON FIELDS IT IS `covRiemann`**: entry 126's tensoriality is exactly what makes the
extension harmless. -/
theorem covRiemannAt_eq (hk : k ≠ 0) {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemannAt cov x u (Y x) (Z x) = CovariantOrderCovDeriv.covRiemann cov Y Z x u := by
  rw [covRiemannAt,
    CovariantOrderCovTensor.covRiemann_congr_of_eq_left cov hk (cmdiffAt_ext x (Y x)) hY
      (cmdiffAt_ext x (Z x)) (by simp) u,
    CovariantOrderCovTensor.covRiemann_congr_of_eq_right cov hk hY (cmdiffAt_ext x (Z x)) hZ
      (by simp) u]

theorem covRiemannAt_add_left (hk : k ≠ 0) {x : M} (u v v' w : TangentSpace I x) :
    covRiemannAt cov x u (v + v') w
      = covRiemannAt cov x u v w + covRiemannAt cov x u v' w := by
  rw [covRiemannAt, covRiemannAt, covRiemannAt,
    CovariantOrderCovTensor.covRiemann_congr_of_eq_left cov hk (cmdiffAt_ext x (v + v'))
      ((cmdiffAt_ext x v).add_section (cmdiffAt_ext x v')) (cmdiffAt_ext x w) (by simp) u,
    CovariantOrderCovDeriv.covRiemann_add_left cov hk (cmdiffAt_ext x v) (cmdiffAt_ext x v')
      (cmdiffAt_ext x w) u]

theorem covRiemannAt_smul_left (hk : k ≠ 0) {x : M} (c : ℝ) (u v w : TangentSpace I x) :
    covRiemannAt cov x u (c • v) w = c • covRiemannAt cov x u v w := by
  rw [covRiemannAt, covRiemannAt,
    CovariantOrderCovTensor.covRiemann_congr_of_eq_left cov hk
      (Y' := (fun _ : M ↦ c) • extend E v)
      (cmdiffAt_ext x (c • v)) (contMDiffAt_const.smul_section (cmdiffAt_ext x v))
      (cmdiffAt_ext x w) (by simp [Pi.smul_apply']) u,
    CovariantOrderCovDeriv.covRiemann_smul_left cov hk (f := fun _ ↦ c) mdifferentiableAt_const
      (cmdiffAt_ext x v) (cmdiffAt_ext x w) u]

theorem covRiemannAt_add_right (hk : k ≠ 0) {x : M} (u v w w' : TangentSpace I x) :
    covRiemannAt cov x u v (w + w')
      = covRiemannAt cov x u v w + covRiemannAt cov x u v w' := by
  rw [covRiemannAt, covRiemannAt, covRiemannAt,
    CovariantOrderCovTensor.covRiemann_congr_of_eq_right cov hk (cmdiffAt_ext x v)
      (cmdiffAt_ext x (w + w')) ((cmdiffAt_ext x w).add_section (cmdiffAt_ext x w')) (by simp) u,
    CovariantOrderCovDeriv.covRiemann_add_right cov hk (cmdiffAt_ext x v) (cmdiffAt_ext x w)
      (cmdiffAt_ext x w') u]

theorem covRiemannAt_smul_right (hk : k ≠ 0) {x : M} (c : ℝ) (u v w : TangentSpace I x) :
    covRiemannAt cov x u v (c • w) = c • covRiemannAt cov x u v w := by
  rw [covRiemannAt, covRiemannAt,
    CovariantOrderCovTensor.covRiemann_congr_of_eq_right cov hk
      (Z' := (fun _ : M ↦ c) • extend E w)
      (cmdiffAt_ext x v) (cmdiffAt_ext x (c • w))
      (contMDiffAt_const.smul_section (cmdiffAt_ext x w)) (by simp [Pi.smul_apply']) u,
    CovariantOrderCovDeriv.covRiemann_smul_right cov hk (f := fun _ ↦ c) mdifferentiableAt_const
      (cmdiffAt_ext x v) (cmdiffAt_ext x w) u]

/-! ## The bundled object -/

/-- **`∇_u R` BUNDLED IN ITS TWO CURVATURE SLOTS**: `(∇_u R) : T_xM →L T_xM →L (T_xM →L T_xM)`, the
object `CurvatureCovTensor`'s fence asked for, over an arbitrary connection. -/
noncomputable def covRiemannHom (hk : k ≠ 0) (x : M) (u : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ LinearMap.toContinuousLinearMap
        { toFun := fun w ↦ covRiemannAt cov x u v w
          map_add' := fun w w' ↦ covRiemannAt_add_right cov hk u v w w'
          map_smul' := fun c w ↦ by
            simpa using covRiemannAt_smul_right cov hk c u v w }
      map_add' := fun v v' ↦ by
        refine ContinuousLinearMap.ext fun w ↦ ?_
        simpa using covRiemannAt_add_left cov hk u v v' w
      map_smul' := fun c v ↦ by
        refine ContinuousLinearMap.ext fun w ↦ ?_
        simpa using covRiemannAt_smul_left cov hk c u v w }

@[simp] theorem covRiemannHom_apply (hk : k ≠ 0) (x : M) (u v w : TangentSpace I x) :
    covRiemannHom cov hk x u v w = covRiemannAt cov x u v w := rfl

/-- **ANTISYMMETRY IN THE TWO CURVATURE SLOTS**, on vectors. -/
theorem covRiemannAt_swap (hk : k ≠ 0) {x : M} (u v w : TangentSpace I x) :
    covRiemannAt cov x u v w = - covRiemannAt cov x u w v :=
  CovariantOrderCovDeriv.covRiemann_swap cov hk (cmdiffAt_ext x v) (cmdiffAt_ext x w) u

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self

/-- **THE VECTOR FORMS COINCIDE AT THE LEVI-CIVITA CONNECTION, AND IT IS `rfl`**: both are
`covRiemann` on the two extensions, and entry 124's `covRiemann_eq` makes those the same term. -/
theorem covRiemannAt_leviCivita (x : M) (u v w : TangentSpace I x) :
    covRiemannAt (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) x u v w
      = CurvatureCovBundle.covRiemannAt x u v w := rfl

/-- **AND `CurvatureCovBundle`'S AGREEMENT THEOREM IS THIS FILE'S, SPECIALISED** — derived FROM the
abstract `covRiemannAt_eq` rather than restating it: the two vector forms are identified by the
`rfl` above, the two field forms by `CovariantOrderCovDeriv.covRiemann_eq`, and the class comes from
`CovariantOrderClass.isLocallyCk_leviCivita`. A theorem rather than a remark so the subsumption is
checked, and therefore a deliberate duplicate under a different name. -/
theorem covRiemannAt_eq_leviCivita (hk : k ≠ 0) {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    CurvatureCovBundle.covRiemannAt x u (Y x) (Z x) = CurvatureCovDeriv.covRiemann Y Z x u := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  haveI : IsLocallyCk ((k : WithTop ℕ∞) + 1)
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) := by
    rw [← e]
    exact CovariantOrderClass.isLocallyCk_leviCivita (k := k + 1)
  rw [← covRiemannAt_leviCivita, ← CovariantOrderCovDeriv.covRiemann_eq Y Z x u]
  exact covRiemannAt_eq _ hk hY hZ u

end LeviCivita

end CovariantOrderCovBundle
