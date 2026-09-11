import CurvatureCovDeriv
import HomCovariantOrder
import CurvatureEndoOrder

/-!
# The covariant derivative of the curvature is a field

`CurvatureCovDeriv` builds `∇R` at a point and `CurvatureCovTensor` makes it a tensor in the two
directions, and both end with the same sentence: nothing makes `y ↦ (∇_X R)(Y, Z)(y)` a **field**.
`HomCovariantOrder` then proved the induced connection regular and said what stood between that and
this: the theorem there wants the curvature field **one order up**, and the two correction terms
want the derivative of a direction field **two orders up**, which is instance bookkeeping and not
mathematics. **This file does that bookkeeping and takes the step.**

## What is proved

**`isManifold_up`**, **`isManifold_up_two`**, **`isContMDiffRiemannianBundle_up`**,
**`isContMDiffRiemannianBundle_up_two`** — the upward shifts: a `C^(k+4)` manifold is a
`C^((k+1)+3)` and a `C^((k+2)+2)` one, and a `C^(k+3)` metric is a `C^((k+1)+2)` and a
`C^((k+2)+1)` one. Each is a cast of `↑(k + j)` to `↑k + j` and `infer_instance`, the device
`CurvatureOrder.isManifold_shift` introduced.

**`isManifold_down`**, **`isManifold_down_two`**, **`isContMDiffRiemannianBundle_down`**,
**`isContMDiffRiemannianBundle_down_two`** — the downward ones the unshifted theorems ask for,
`of_le` each.

**`contMDiffAt_covRiemann_hom`** — **THE THEOREM**: for `X, Y, Z` of class `C^(k+3)` at the point,
the Levi-Civita connection of a `C^(k+3)` metric on a `C^(k+4)` manifold has
`y ↦ (∇_X R)(Y, Z)(y)` a **`C^k` section of `Hom(TM, TM)`**. The three terms of
`CurvatureCovDeriv.covRiemann` are handled by `HomCovariantOrder.contMDiffAt_homCovFun_hom` on the
curvature field one order up, and by `CurvatureEndoOrder.contMDiffAt_riemann_hom` on the two
corrections, whose direction fields are `LeviCivitaOrder.contMDiffAt_leviCivita_apply` two orders
up. No new analysis: the identity is definitional and every step is an existing theorem at a
shifted order.

## What is NOT here

* **NO SECOND BIANCHI IDENTITY.** Unchanged and unaffected: the cyclic sum is a statement about
  fields at a point and needs none of this. It is the `UNLOCK_WATCHLIST` item's step (3), it needs
  three derivatives of the differentiated field where the **first** Bianchi identity needed two and
  cost a file of seven declarations, and it is **not attempted, no cost claimed**
  (`ERRATUM 246`).
* **NO TRACE, NO DIVERGENCE.** The contracted Bianchi identity and the divergence of the Einstein
  tensor — which is what a reader wants `∇R` for — need a trace of this object against the metric,
  and `TraceFrame.contMDiffAt_trace` would take it. That composition is not made, and which
  contraction is meant is a modelling decision for the author.
* **ONLY THE LEVI-CIVITA CONNECTION**, as in `HomCovariantOrder`, and for the same reason.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** This is the first object in the
  estate that `a₂` could integrate — `WALLS` §W5's rung 4 wants derivatives of the curvature — and
  **rung 4 still needs the heat semigroup and a parametrix**, which §W5.1 §4 prices as a research
  project. **No wall moves.**

**No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `RicciOrder`'s shape with every order one
higher — `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, `[CompleteSpace E]`,
`[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]`, `[IsManifold I 3 M]` and **`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1)
M]`**, a `RiemannianBundle` on the tangent spaces with
**`[IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I)]`** and its
literal-order companion at `2`. **A `C^(k+4)` manifold and a `C^(k+3)` metric**: one derivative
more than the curvature files, which is exactly what differentiating the curvature costs. The eight
shift instances `omit` the binders they do not use — four omit eight binders each and four omit
six — and the unused-variable linter reports nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureCovOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-! ## The order shifts -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- A `C^(k+4)` manifold is a `C^((k+1)+3)` manifold, which is what the curvature theorems ask for
one order up. -/
theorem isManifold_up : IsManifold I ((((k + 1 : ℕ) : WithTop ℕ∞)) + 1 + 1 + 1) M := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 + 1 + 1 = (k : WithTop ℕ∞) + 1 + 1 + 1 + 1 := by
    push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- And a `C^((k+2)+2)` manifold. -/
theorem isManifold_up_two : IsManifold I ((((k + 2 : ℕ) : WithTop ℕ∞)) + 1 + 1) M := by
  have e : (((k + 2 : ℕ) : WithTop ℕ∞)) + 1 + 1 = (k : WithTop ℕ∞) + 1 + 1 + 1 + 1 := by
    push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- A `C^(k+3)` metric is a `C^((k+1)+2)` metric. -/
theorem isContMDiffRiemannianBundle_up :
    IsContMDiffRiemannianBundle I ((((k + 1 : ℕ) : WithTop ℕ∞)) + 1 + 1) E
      (TangentSpace I : M → Type _) := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 + 1 = (k : WithTop ℕ∞) + 1 + 1 + 1 := by
    push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- And a `C^((k+2)+1)` metric. -/
theorem isContMDiffRiemannianBundle_up_two :
    IsContMDiffRiemannianBundle I ((((k + 2 : ℕ) : WithTop ℕ∞)) + 1) E
      (TangentSpace I : M → Type _) := by
  have e : (((k + 2 : ℕ) : WithTop ℕ∞)) + 1 = (k : WithTop ℕ∞) + 1 + 1 + 1 := by push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The downward shifts the unshifted theorems ask for. -/
theorem isManifold_down : IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M :=
  IsManifold.of_le (n := (k : WithTop ℕ∞) + 1 + 1 + 1 + 1) le_self_add

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem isManifold_down_two : IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M :=
  IsManifold.of_le (n := (k : WithTop ℕ∞) + 1 + 1 + 1 + 1)
    (le_self_add.trans le_self_add)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem isContMDiffRiemannianBundle_down :
    IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1 + 1 + 1) le_self_add

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem isContMDiffRiemannianBundle_down_two :
    IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1 + 1 + 1)
    (le_self_add.trans le_self_add)

attribute [local instance] isManifold_up isManifold_up_two isContMDiffRiemannianBundle_up
  isContMDiffRiemannianBundle_up_two isManifold_down isManifold_down_two
  isContMDiffRiemannianBundle_down isContMDiffRiemannianBundle_down_two
  KoszulManifold.finDimTangent CurvatureTensor.contMDiffVectorBundle_two

/-! ## The covariant derivative of the curvature is a field -/

/-- **THE COVARIANT DERIVATIVE OF THE CURVATURE IS A `C^k` SECTION OF `Hom(TM, TM)`**: for
`X, Y, Z` of class `C^(k+3)` at the point and the Levi-Civita connection of a `C^(k+3)` metric on
a `C^(k+4)` manifold, `y ↦ (∇_{X} R)(Y, Z)(y)` is a `C^k` field of endomorphisms. This is what
`CurvatureCovDeriv` and `CurvatureCovTensor` each record as missing, and what the shift in the
instances above is for. -/
theorem contMDiffAt_covRiemann_hom {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (CurvatureCovDeriv.covRiemann Y Z y (X y))) x := by
  have ecast : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  have ecast2 : (((k + 2 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  -- the curvature field, one order up
  have hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (LeviCivitaRegular.riemann I y (Y y) (Z y))) x := by
    have h := CurvatureEndoOrder.contMDiffAt_riemann_hom (k := k + 1)
      (X := Y) (W := Z) (by rw [ecast]; exact hY) (by rw [ecast]; exact hZ)
    rwa [ecast] at h
  -- the two derivatives of the direction fields, two orders up
  have hdY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (fun y ↦ leviCivita Y y (X y))) x := by
    have h := LeviCivitaOrder.contMDiffAt_leviCivita_apply (k := k + 2)
      (Y := X) (Z := Y) (by rw [ecast2]; exact hX) (by rw [ecast2]; exact hY)
    rwa [ecast2] at h
  have hdZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (fun y ↦ leviCivita Z y (X y))) x := by
    have h := LeviCivitaOrder.contMDiffAt_leviCivita_apply (k := k + 2)
      (Y := X) (Z := Z) (by rw [ecast2]; exact hX) (by rw [ecast2]; exact hZ)
    rwa [ecast2] at h
  have hYd : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x := hY.of_le le_self_add
  have hZd : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x := hZ.of_le le_self_add
  -- the three terms
  have h1 : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (HomCovariant.homCovFun
          (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
          (fun y' ↦ LeviCivitaRegular.riemann I y' (Y y') (Z y')) y (X y))) x :=
    HomCovariantOrder.contMDiffAt_homCovFun_hom hA (hX.of_le (le_self_add.trans le_self_add))
  have h2 : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (LeviCivitaRegular.riemann I y (leviCivita Y y (X y)) (Z y))) x :=
    CurvatureEndoOrder.contMDiffAt_riemann_hom hdY hZd
  have h3 : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (LeviCivitaRegular.riemann I y (Y y) (leviCivita Z y (X y)))) x :=
    CurvatureEndoOrder.contMDiffAt_riemann_hom hYd hdZ
  exact (h1.sub_section h2).sub_section h3

end CurvatureCovOrder
