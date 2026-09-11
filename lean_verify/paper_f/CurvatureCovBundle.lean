import CurvatureBianchiSecond
import CurvatureCovTensor

/-!
# `∇R` as a tensor, and the second Bianchi identity for three arbitrary vectors

**`CurvatureCovTensor`'s own fence, closed.** That file proves `covRiemann` depends on its two
direction fields only through their values at the point, and ends: *the tensor is not BUNDLED —
`covRiemann v w x u` as a continuous linear map in `v` and `w` [...] is not built; the two theorems
above are exactly what that construction consumes, so it is now plumbing and this file does not do
it.* **This file does the plumbing**, and the plumbing turns out to buy two things beyond it: the
curvature's derivative is linear in its **direction** as well, and the second Bianchi identity
holds for **three arbitrary tangent vectors** rather than three fields.

**The device is `curvEndo`'s, one derivative up.** `covRiemannAt x u v w` is `covRiemann` applied
to the *extensions* of `v` and `w` to sections (`extend`), which is well defined for any
vectors at all; `covRiemannAt_eq` says that on fields it is `covRiemann` itself, and that is
entry 110's tensoriality doing the only work it was built for. The slot laws then transfer from
sections to vectors, and the two nested `LinearMap.toContinuousLinearMap` calls bundle them.

## What is proved

**`covRiemannAt`, `covRiemannAt_eq`** — `(∇_u R)(v, w)` for tangent **vectors**, and its agreement
with `CurvatureCovDeriv.covRiemann` on fields of class `C^(k+2)` at the point.

**`covRiemannAt_add_left`, `covRiemannAt_smul_left`, `covRiemannAt_add_right`,
`covRiemannAt_smul_right`** — bilinearity in the two curvature slots, on vectors.

**`covRiemann_add_dir`, `covRiemann_smul_dir`** — **AND IT IS LINEAR IN THE DIRECTION**, which
`CurvatureCovDeriv` does not state: the induced connection is a continuous linear map in its
direction and both corrections are linear in theirs. These two take **no hypothesis at all** — not
even `k ≠ 0` — being a computation on the definition; `covRiemannAt_add_dir` and
`covRiemannAt_smul_dir` are the same on vectors.

**`covRiemannHom`, `covRiemannHom_apply`** — **`∇_u R` AS A CONTINUOUS BILINEAR MAP INTO
`Hom(TM, TM)`**: `T_xM →L T_xM →L (T_xM →L T_xM)`, which is the object the fence asked for.

**`covRiemannAt_swap`** — antisymmetry in the two curvature slots, on vectors.

**`covRiemannAt_cyclic`** — **THE SECOND BIANCHI IDENTITY FOR THREE ARBITRARY TANGENT VECTORS**:
`(∇_u R)(v, w) + (∇_v R)(w, u) + (∇_w R)(u, v) = 0`, with no fields, no differentiability
hypothesis and nothing for the reader to extend. `CurvatureBianchiSecond.covRiemann_cyclic_endo`
proves it for three `C^(k+2)` fields; this is that theorem at the extensions, and it is the form a
reader of a textbook expects.

## What is NOT here

* **THE DIRECTION SLOT IS NOT BUNDLED WITH THE OTHER TWO.** `covRiemannHom` is bilinear in `v` and
  `w` at a fixed `u`; the four-deep object `T_xM →L T_xM →L T_xM →L (T_xM →L T_xM)` is **not
  built as of 2026-09-11**, although the linearity it needs is proved above
  (`covRiemannAt_add_dir`, `covRiemannAt_smul_dir`). The reason is not mathematics: three-deep
  nesting already cost `HomCovariant` a scoped `synthInstance.maxHeartbeats`, and nothing in this
  estate consumes the four-deep form. **Not attempted, no cost claimed** (`ERRATUM 246`), and it
  is `UNLOCK_WATCHLIST`'s item *the two residues of `CurvatureCovBundle`*.
* **NO CONTRACTED IDENTITY.** A trace of the Bianchi identity above would give `div G = 0`, and
  which contraction is meant is the author's decision (`ASSUMPTIONS 56`). Bundling does not decide
  it: the object now has the shape a contraction could be applied to, and no contraction is
  applied.
* **NOTHING AT `k = 0`**, for the chain's standing reason — the induced connection needs an
  argument it can differentiate.
* **NO REGULARITY OF THE BUNDLED OBJECT, as of 2026-09-11.** `CurvatureCovOrder` makes
  `y ↦ (∇_X R)(Y, Z)(y)` a `C^k` section of `Hom(TM, TM)` for fields; nothing here says
  `y ↦ covRiemannHom hk y u` is a `C^k` section of the doubly-nested bundle, and the extensions
  would have to be compared across points to say it. Not attempted, and it is the second residue
  of the same `UNLOCK_WATCHLIST` item.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`), **and the paragraph is
`binder_scan.py`'s table**: the section context is `CurvatureCovDeriv`'s, unchanged, with its seven
local instances. **Nine of the fifteen** declarations take `hk : k ≠ 0` — every one that passes
through the tensoriality theorems — and the six that do not are the two direction-linearity lemmas
and their vector forms, the extension-order helper, and `covRiemannHom_apply`, which is `rfl`. One
`private` helper (`cmdiffAt_ext`), one `omit` on it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureCovBundle

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CurvatureCovDeriv

open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self KoszulManifold.finDimTangent
  CurvatureTensor.contMDiffVectorBundle_two RicciOrder.contMDiffVectorBundle_add_two

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The order at which every extension used below is taken. -/
private theorem cmdiffAt_ext (x : M) (v : TangentSpace I x) :
    CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (extend E v)) x :=
  contMDiffAt_extend' (k := (k : WithTop ℕ∞) + 1 + 1) I E v

/-- **`(∇_u R)(v, w)` ON TANGENT VECTORS**, through their extensions to sections — `curvEndo`'s
device, one derivative up. -/
noncomputable def covRiemannAt (x : M) (u v w : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  covRiemann (extend E v) (extend E w) x u

/-- **AND ON FIELDS IT IS `covRiemann`**: the tensoriality of `CurvatureCovTensor` is exactly what
makes the extension harmless. -/
theorem covRiemannAt_eq (hk : k ≠ 0) {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemannAt x u (Y x) (Z x) = covRiemann Y Z x u := by
  rw [covRiemannAt,
    CurvatureCovTensor.covRiemann_congr_of_eq_left hk (cmdiffAt_ext x (Y x)) hY
      (cmdiffAt_ext x (Z x)) (by simp) u,
    CurvatureCovTensor.covRiemann_congr_of_eq_right hk hY (cmdiffAt_ext x (Z x)) hZ (by simp) u]

theorem covRiemannAt_add_left (hk : k ≠ 0) {x : M} (u v v' w : TangentSpace I x) :
    covRiemannAt x u (v + v') w = covRiemannAt x u v w + covRiemannAt x u v' w := by
  rw [covRiemannAt, covRiemannAt, covRiemannAt,
    CurvatureCovTensor.covRiemann_congr_of_eq_left hk (cmdiffAt_ext x (v + v'))
      ((cmdiffAt_ext x v).add_section (cmdiffAt_ext x v')) (cmdiffAt_ext x w) (by simp) u,
    covRiemann_add_left hk (cmdiffAt_ext x v) (cmdiffAt_ext x v') (cmdiffAt_ext x w) u]

theorem covRiemannAt_smul_left (hk : k ≠ 0) {x : M} (c : ℝ) (u v w : TangentSpace I x) :
    covRiemannAt x u (c • v) w = c • covRiemannAt x u v w := by
  rw [covRiemannAt, covRiemannAt,
    CurvatureCovTensor.covRiemann_congr_of_eq_left hk (Y' := (fun _ : M ↦ c) • extend E v)
      (cmdiffAt_ext x (c • v)) (contMDiffAt_const.smul_section (cmdiffAt_ext x v))
      (cmdiffAt_ext x w) (by simp [Pi.smul_apply']) u,
    covRiemann_smul_left hk (f := fun _ ↦ c) mdifferentiableAt_const (cmdiffAt_ext x v)
      (cmdiffAt_ext x w) u]

theorem covRiemannAt_add_right (hk : k ≠ 0) {x : M} (u v w w' : TangentSpace I x) :
    covRiemannAt x u v (w + w') = covRiemannAt x u v w + covRiemannAt x u v w' := by
  rw [covRiemannAt, covRiemannAt, covRiemannAt,
    CurvatureCovTensor.covRiemann_congr_of_eq_right hk (cmdiffAt_ext x v)
      (cmdiffAt_ext x (w + w')) ((cmdiffAt_ext x w).add_section (cmdiffAt_ext x w')) (by simp) u,
    covRiemann_add_right hk (cmdiffAt_ext x v) (cmdiffAt_ext x w) (cmdiffAt_ext x w') u]

theorem covRiemannAt_smul_right (hk : k ≠ 0) {x : M} (c : ℝ) (u v w : TangentSpace I x) :
    covRiemannAt x u v (c • w) = c • covRiemannAt x u v w := by
  rw [covRiemannAt, covRiemannAt,
    CurvatureCovTensor.covRiemann_congr_of_eq_right hk (Z' := (fun _ : M ↦ c) • extend E w)
      (cmdiffAt_ext x v) (cmdiffAt_ext x (c • w))
      (contMDiffAt_const.smul_section (cmdiffAt_ext x w)) (by simp [Pi.smul_apply']) u,
    covRiemann_smul_right hk (f := fun _ ↦ c) mdifferentiableAt_const (cmdiffAt_ext x v)
      (cmdiffAt_ext x w) u]

/-- **AND LINEAR IN THE DIRECTION TOO**: the induced connection is a continuous linear map in
its direction and the two corrections are linear in theirs, so `∇R` is additive in `u`. -/
theorem covRiemann_add_dir {Y Z : Π x : M, TangentSpace I x} {x : M} (u u' : TangentSpace I x) :
    covRiemann Y Z x (u + u') = covRiemann Y Z x u + covRiemann Y Z x u' := by
  simp only [covRiemann, LeviCivitaRegular.riemann, map_add,
    CurvatureTensor.curvEndo_add_left, CurvatureTensor.curvEndo_add_right]
  abel

/-- **AND HOMOGENEOUS IN THE DIRECTION.** -/
theorem covRiemann_smul_dir {Y Z : Π x : M, TangentSpace I x} {x : M} (c : ℝ)
    (u : TangentSpace I x) :
    covRiemann Y Z x (c • u) = c • covRiemann Y Z x u := by
  simp only [covRiemann, LeviCivitaRegular.riemann, map_smul,
    CurvatureTensor.curvEndo_smul_left, CurvatureTensor.curvEndo_smul_right]
  module

theorem covRiemannAt_add_dir {x : M} (u u' v w : TangentSpace I x) :
    covRiemannAt x (u + u') v w = covRiemannAt x u v w + covRiemannAt x u' v w :=
  covRiemann_add_dir u u'

theorem covRiemannAt_smul_dir {x : M} (c : ℝ) (u v w : TangentSpace I x) :
    covRiemannAt x (c • u) v w = c • covRiemannAt x u v w :=
  covRiemann_smul_dir c u

/-- **THE COVARIANT DERIVATIVE OF THE CURVATURE, BUNDLED IN ITS TWO CURVATURE SLOTS**:
`(∇_u R) : T_xM →L T_xM →L (T_xM →L T_xM)`, which is what `CurvatureCovTensor`'s own fence asks
for. -/
noncomputable def covRiemannHom (hk : k ≠ 0) (x : M) (u : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v ↦ LinearMap.toContinuousLinearMap
        { toFun := fun w ↦ covRiemannAt x u v w
          map_add' := fun w w' ↦ covRiemannAt_add_right hk u v w w'
          map_smul' := fun c w ↦ by
            simpa using covRiemannAt_smul_right hk c u v w }
      map_add' := fun v v' ↦ by
        refine ContinuousLinearMap.ext fun w ↦ ?_
        simpa using covRiemannAt_add_left hk u v v' w
      map_smul' := fun c v ↦ by
        refine ContinuousLinearMap.ext fun w ↦ ?_
        simpa using covRiemannAt_smul_left hk c u v w }

@[simp] theorem covRiemannHom_apply (hk : k ≠ 0) (x : M) (u v w : TangentSpace I x) :
    covRiemannHom hk x u v w = covRiemannAt x u v w := rfl

/-- **ANTISYMMETRY IN THE TWO CURVATURE SLOTS**, on vectors. -/
theorem covRiemannAt_swap (hk : k ≠ 0) {x : M} (u v w : TangentSpace I x) :
    covRiemannAt x u v w = - covRiemannAt x u w v :=
  covRiemann_swap hk (cmdiffAt_ext x v) (cmdiffAt_ext x w) u

/-- **THE SECOND BIANCHI IDENTITY FOR THREE ARBITRARY TANGENT VECTORS**: no fields, no
differentiability hypothesis on anything, and nothing to extend on the reader's side. -/
theorem covRiemannAt_cyclic (hk : k ≠ 0) {x : M} (u v w : TangentSpace I x) :
    covRiemannAt x u v w + covRiemannAt x v w u + covRiemannAt x w u v = 0 := by
  have h := CurvatureBianchiSecond.covRiemann_cyclic_endo hk (X := extend E u) (Y := extend E v)
    (Z := extend E w) (cmdiffAt_ext x u) (cmdiffAt_ext x v) (cmdiffAt_ext x w)
  simpa [covRiemannAt] using h

end CurvatureCovBundle
