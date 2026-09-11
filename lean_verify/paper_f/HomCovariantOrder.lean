import HomCovariant
import LeviCivitaOrder

/-!
# The induced connection on the endomorphism bundle is regular

`HomCovariant` builds the induced connection on `Hom(TM, TM)` and proves **no smoothness of it at
all**, and four files record that absence in their own *What is NOT here*: `HomCovariant` itself,
`CurvatureEndoOrder`, `CurvatureCovDeriv` and `CurvatureCovTensor`. **This file closes it**, for
the Levi-Civita connection at every finite order.

## What is proved

**`eventually_mdiffHomAt`**, **`eventually_mdiffAt`** — a section of class `C^(k+1)` at a point is
differentiable at every point of a neighbourhood, for `Hom(TM, TM)` and for `TM`. This is
`RicciOrder.eventually_cmdiffAt_two`'s device at a general order, and it is what turns a pointwise
identity into one that can be used near the point.

**`contMDiffAt_homCovFun_apply`** — **THE THEOREM**: for `A` a `C^(k+1)` section of `Hom(TM, TM)`
and `X, W` of class `C^(k+1)` at the point, `y ↦ (∇_X A)(W)(y)` is a `C^k` section. The proof is
the identity `(∇_X A)(W) = ∇_X (A W) − A (∇_X W)` — which is `HomCovariant.homCovAux`'s definition
once the tensoriality lemma has replaced the extended vector by the section `W` — with
`LeviCivitaOrder.contMDiffAt_leviCivita_apply` on each term and Mathlib's
`ContMDiffAt.clm_bundle_apply` for the two applications of `A`.

**`contMDiffAt_homCovFun_hom`** — **AND SO `∇_X A` IS A `C^k` SECTION OF `Hom(TM, TM)`**, not
merely a field whose values on sections are `C^k`, through
`LeviCivitaOrder.contMDiffAt_hom_of_localFrame` fed the theorem above on the chart's own frame.

## What is NOT here

* **THE REGULARITY OF `∇R` DOES NOT FOLLOW WITHOUT AN ORDER SHIFT, AND THE SHIFT IS NOT DONE.**
  `CurvatureCovDeriv.covRiemann` is `homCovFun` applied to `y ↦ R(Y y, Z y)` minus two correction
  terms. To feed `contMDiffAt_homCovFun_hom` that field one needs it at `C^(k+1)`, which is
  `CurvatureEndoOrder.contMDiffAt_riemann_hom` **one order up** — a `C^(k+3)` metric on a `C^(k+4)`
  manifold — and the two correction terms need `RicciOrder.contMDiffAt_riemann` on `∇_X Y`, which
  is another shift. That is the instance plumbing `CurvatureOrder` needed four local instances for,
  and this file does none of it. **Not attempted, no cost claimed** (`ERRATUM 246`).
* **ONLY THE LEVI-CIVITA CONNECTION.** `HomCovariant` builds the induced connection for an
  arbitrary covariant derivative on the tangent bundle; the regularity here uses
  `LeviCivitaOrder`'s theorems and so is about `leviCivita` only. For an abstract `cov` the
  statement would be *`∇^{Hom}` is `C^k` when `cov` is*, and that needs the order-`k` hypothesis in
  the form `CovariantOrderClass.IsLocallyCk` — which exists — but no such statement is made.
* **NO SECOND BIANCHI IDENTITY.** Unchanged: it is a statement about fields and needs the cyclic
  sum, not regularity.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `LeviCivitaOrder`'s, which are lighter
than the curvature files' — `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, `[CompleteSpace E]`,
`[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]` and `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]`, a `RiemannianBundle` on the
tangent spaces with `[IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I)]` and
its literal-order companion at `1`. **A `C^(k+2)` manifold and a `C^(k+1)` metric**, where the
curvature files need `C^(k+3)` and `C^(k+2)`: the induced connection costs one derivative, not two.
Three local instances, and the two neighbourhood helpers `omit` five binders each. The
unused-variable linter reports nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HomCovariantOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

attribute [local instance] KoszulOrder.isManifold_succ KoszulOrder.contMDiffVectorBundle_succ
  KoszulManifold.finDimTangent

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- A section of `Hom(TM, TM)` of class `C^(k+1)` at a point is of that class at every point of a
neighbourhood, so a statement that holds pointwise can be used near the point. -/
theorem eventually_mdiffHomAt {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x) :
    ∀ᶠ y in 𝓝 x, HomCovariant.MDiffHomAt A y := by
  obtain ⟨u, hu, hAu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hA
  filter_upwards [interior_mem_nhds.2 hu] with y hy
  exact ((hAu.mono interior_subset).contMDiffAt
    (isOpen_interior.mem_nhds hy)).mdifferentiableAt (by simp)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)] in
/-- The same for a section of the tangent bundle. -/
theorem eventually_mdiffAt {W : Π y : M, TangentSpace I y} {x : M}
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% W) x) :
    ∀ᶠ y in 𝓝 x, MDiffAt (T% W) y := by
  obtain ⟨u, hu, hWu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hW
  filter_upwards [interior_mem_nhds.2 hu] with y hy
  exact ((hWu.mono interior_subset).contMDiffAt
    (isOpen_interior.mem_nhds hy)).mdifferentiableAt (by simp)

/-- **THE INDUCED CONNECTION ON THE ENDOMORPHISM BUNDLE IS REGULAR**: for `A` a `C^(k+1)` section
of `Hom(TM, TM)` and `X, W` of class `C^(k+1)` at the point, `y ↦ (∇_{X} A)(W)(y)` is a `C^k`
section. `HomCovariant` proves no smoothness at all, and four files of this estate record that
absence. -/
theorem contMDiffAt_homCovFun_apply
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {X W : Π y : M, TangentSpace I y}
    {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% W) x) :
    CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ HomCovariant.homCovFun
        (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
          A y (X y) (W y))) x := by
  have hAW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% (fun y ↦ A y (W y))) x :=
    ContMDiffAt.clm_bundle_apply hA hW
  have hcovW : CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ leviCivita W y (X y))) x :=
    LeviCivitaOrder.contMDiffAt_leviCivita_apply hX hW
  have h1 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ leviCivita (fun y' ↦ A y' (W y')) y (X y))) x :=
    LeviCivitaOrder.contMDiffAt_leviCivita_apply hX hAW
  have h2 : CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ A y (leviCivita W y (X y)))) x :=
    ContMDiffAt.clm_bundle_apply (hA.of_le le_self_add) hcovW
  refine (h1.sub_section h2).congr_of_eventuallyEq ?_
  filter_upwards [eventually_mdiffHomAt hA, eventually_mdiffAt hW] with y hAy hWy
  refine congrArg (TotalSpace.mk' E y) ?_
  rw [HomCovariant.homCovFun_apply hAy,
    HomCovariant.homCovAux_congr_of_eq hAy (mdifferentiableAt_extend (I := I) E _) hWy (by simp)]
  rfl

/-- **AND SO `∇_X A` IS A `C^k` SECTION OF `Hom(TM, TM)`**, not merely a field whose values on
sections are `C^k` — through the frame criterion, fed the theorem above on the chart's own frame. -/
theorem contMDiffAt_homCovFun_hom
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {X : Π y : M, TangentSpace I y} {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (HomCovariant.homCovFun
          (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) A y (X y))) x := by
  have hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  refine LeviCivitaOrder.contMDiffAt_hom_of_localFrame _ (Module.finBasis ℝ E) fun i ↦ ?_
  exact contMDiffAt_homCovFun_apply hA hX
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1) _ (Module.finBasis ℝ E) i hx)

end HomCovariantOrder
