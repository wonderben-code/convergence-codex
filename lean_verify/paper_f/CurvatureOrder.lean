import TraceFrame

/-!
# The curvature of a metric is a `C^k` section

The first differentiability statement about a curvature in this estate.

`LeviCivitaOrder` made the connection of a `C^(k+1)` metric `C^k`, and the watchlist item filed
there named what was still missing: **the curvature's own regularity**, which is the first thing
`WALLS` §W5's rung 4 consumes, since `a₂` integrates derivatives of the curvature. This file is
the field half of that item. **For `X, Y, Z` of class `C^(k+2)` at a point and the Levi-Civita
connection of a `C^(k+2)` metric on a `C^(k+3)` manifold, the curvature expression
`y ↦ (∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z)(y)` is a `C^k` section** (`contMDiffAt_curvAux`).

The reason this costs one file and not a subject is that `CurvatureTensorial.curvAux` applies the
connection **only to plain sections of the tangent bundle** — `∇_X(∇_Y Z)` is the connection
applied to the section `∇_Y Z`, not to a `Hom`-valued object — so the induced connection on
`Hom(TM, TM)`, which the pinned Mathlib does not have, is never needed. Each of the three terms is
`LeviCivitaOrder.contMDiffAt_leviCivita_apply` applied twice at shifted orders, and the third also
uses `KoszulOrder.contMDiffAt_mlieBracket`. Two derivatives cost two orders of the data, which is
why the metric and the fields are asked for at `C^(k+2)` and the manifold at `C^(k+3)`.

What the shift costs is instances, again. A `C^(k+3)` manifold is a `C^((k+1)+2)` manifold and a
`C^(k+2)` metric is a `C^((k+1)+1)` metric, but neither is found by unification, because the
elaborator cannot see `(k+1 : ℕ)` inside `((k : WithTop ℕ∞) + 1)`; both are proved by casting and
registered locally (`isManifold_shift`, `isContMDiffRiemannianBundle_shift`), together with the
two downward instances (`isManifold_self`, `isContMDiffRiemannianBundle_self`).

## What is proved

**`isManifold_shift`**, **`isContMDiffRiemannianBundle_shift`**, **`isManifold_self`**,
**`isContMDiffRiemannianBundle_self`** — the four order-shift instances above.

**`contMDiffAt_leviCivita_apply_succ`** — `y ↦ ∇_Y Z(y)` is a `C^(k+1)` section for `Y, Z` of
class `C^(k+2)`: the previous unit's theorem at the shifted order.

**`contMDiffAt_mlieBracket_succ`** — the bracket of two `C^(k+2)` fields is a `C^(k+1)` field.

**`contMDiffAt_curvAux`** — **THE CURVATURE EXPRESSION IS A `C^k` SECTION** for `C^(k+2)` fields
and a `C^(k+2)` metric.

## What is NOT here

**NO STATEMENT ABOUT `curvEndo` AS A FIELD, AND SO NO RICCI OR SCALAR CURVATURE AS A FUNCTION.**
What is proved is the regularity of the curvature **expression on three sections**; the curvature
**tensor** `CurvatureTensor.curvEndo` is a family of endomorphisms indexed by the point, and that
`y ↦ curvEndo leviCivita y (X y) (Y y)` is a differentiable field — which is what
`TraceFrame.contMDiffAt_trace` would consume to give the Ricci and scalar curvature as `C^k`
functions of the point — is one step further and is not taken here. The two are related by
`CurvatureTensor.curvEndo_apply`, which this file does not use. **Not attempted, no cost claimed**
(`ERRATUM 246`). ⚠ By entry 81, later the same day, that step is taken, by exactly the bridge
named here: `RicciOrder.contMDiffAt_ricciOp_apply` is `curvEndo` as a `C^k` field and
`RicciOrder.contMDiffAt_ricci` is the Ricci curvature as a `C^k` function. **The scalar curvature
is still not a function of the point**, for the reason `RicciOrder`'s own fence gives.

**NOTHING ABOUT `IsLocallyC1` OR ITS ORDER-PARAMETRISED FORM.** `CurvatureTensor` is still written
against the class that fixes one derivative, and this file neither replaces it nor generalises it;
what is proved here is about `curvAux`, which is defined before the class is used.

**NO SECOND DERIVATIVE OF THE CURVATURE, AND NO `a₂`.** One derivative of the curvature would need
`C^(k+3)` data by the same accounting, and the second Bianchi identity — the natural statement
about it — is absent (`CurvatureBianchi`'s fence). The heat-kernel expansion needs both that and a
parametrix construction, which no part of this estate has.

**ONLY FINITE ORDERS**, inherited from `KoszulOrder` and `LeviCivitaOrder`.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with
model `I`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`,
`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]` — a `C^(k+3)` manifold — the Riemannian bundle,
`[IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I)]` — a `C^(k+2)`
metric — and the `C¹` metric `leviCivita` asks for, with `omit` on each of the four instance
lemmas and on the bracket lemma.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The order shift: a `C^(k+3)` manifold is a `C^((k+1)+2)` manifold. -/
theorem isManifold_shift : IsManifold I ((((k + 1 : ℕ) : WithTop ℕ∞)) + 1 + 1) M := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 + 1 = (k : WithTop ℕ∞) + 1 + 1 + 1 := by
    push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The order shift for the metric: `C^(k+2)` is `C^((k+1)+1)`. -/
theorem isContMDiffRiemannianBundle_shift :
    IsContMDiffRiemannianBundle I ((((k + 1 : ℕ) : WithTop ℕ∞)) + 1) E
      (TangentSpace I : M → Type _) := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- A `C^(k+3)` manifold is a `C^(k+2)` manifold, which is what the unshifted theorems ask for. -/
theorem isManifold_self : IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M :=
  IsManifold.of_le (n := (k : WithTop ℕ∞) + 1 + 1 + 1) le_self_add

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- A `C^(k+2)` metric is a `C^(k+1)` metric, which is what the unshifted theorems ask for. -/
theorem isContMDiffRiemannianBundle_self :
    IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1 + 1) le_self_add

attribute [local instance] isManifold_shift isContMDiffRiemannianBundle_shift isManifold_self
  isContMDiffRiemannianBundle_self

/-- **`y ↦ ∇_Y Z(y)` is a `C^(k+1)` section** for `Y, Z` of class `C^(k+2)` — the previous unit's
theorem at the shifted order. -/
theorem contMDiffAt_leviCivita_apply_succ {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CMDiffAt ((k : WithTop ℕ∞) + 1) (T% (fun y ↦ leviCivita Z y (Y y))) x := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  have h := LeviCivitaOrder.contMDiffAt_leviCivita_apply (k := k + 1) (I := I) (M := M)
    (Y := Y) (Z := Z) (x := x) (by rw [e]; exact hY) (by rw [e]; exact hZ)
  rw [e] at h
  exact h

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The bracket of two `C^(k+2)` fields is a `C^(k+1)` field. -/
theorem contMDiffAt_mlieBracket_succ {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x) :
    CMDiffAt ((k : WithTop ℕ∞) + 1) (T% (mlieBracket I X Y)) x := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  have h := KoszulOrder.contMDiffAt_mlieBracket (k := k + 1) (I := I) (M := M)
    (X := X) (Y := Y) (x := x) (by rw [e]; exact hX) (by rw [e]; exact hY)
  rw [e] at h
  exact h

/-- **THE CURVATURE EXPRESSION IS A `C^k` SECTION**: for `X, Y, Z` of class `C^(k+2)` at `x` and
the Levi-Civita connection of a `C^(k+2)` metric,
`y ↦ (∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z)(y)` is `C^k` at `x`. -/
theorem contMDiffAt_curvAux {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞)
      (T% (curvAux (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
        X Y Z)) x := by
  have hX1 : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x := hX.of_le le_self_add
  have hY1 : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Y) x := hY.of_le le_self_add
  have hZ1 : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x := hZ.of_le le_self_add
  have h1 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ leviCivita (covApply leviCivita Y Z) y (X y))) x :=
    LeviCivitaOrder.contMDiffAt_leviCivita_apply hX1 (contMDiffAt_leviCivita_apply_succ hY hZ)
  have h2 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ leviCivita (covApply leviCivita X Z) y (Y y))) x :=
    LeviCivitaOrder.contMDiffAt_leviCivita_apply hY1 (contMDiffAt_leviCivita_apply_succ hX hZ)
  have h3 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ leviCivita Z y (mlieBracket I X Y y))) x :=
    LeviCivitaOrder.contMDiffAt_leviCivita_apply (contMDiffAt_mlieBracket_succ hX hY) hZ1
  exact (h1.sub_section h2).sub_section h3

end CurvatureOrder
