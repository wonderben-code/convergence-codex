import RicciOrder
import HomCovariant

/-!
# The curvature as a section of the endomorphism bundle, and its covariant derivative

The `UNLOCK_WATCHLIST` item *the regularity of the curvature of a metric* records, in its entry-81
status, that what was proved there is *"the regularity of its VALUES on fields, which is all a
trace consumes and all the pinned library's `Hom`-bundle gap allows"*, and asks for the curvature
**as a section of the endomorphism bundle** instead. **That diagnosis was wrong and the gap was not
the obstacle**: `LeviCivitaOrder.contMDiffAt_hom_of_localFrame` — a section of `Hom(TM, TM)` is
`C^n` at `x` as soon as its values on the chart's local frame are `C^n` sections — has been in this
estate since 10 September, one file earlier than the status that named the gap. Feeding it
`RicciOrder.contMDiffAt_riemann` on the frame is four lines. `ERRATUM 494` is that reading.

## What is proved

**`contMDiffAt_riemann_hom`** — **THE RIEMANN CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` SECTION OF
`Hom(TM, TM)`**: `y ↦ R(X y, W y)` for `X, W` of class `C^(k+2)` at the point, in Mathlib's
`ContMDiffAt` for the endomorphism bundle rather than as values on sections.

**`contMDiffAt_ricciOp_hom`** — and so is the Ricci operator `y ↦ (v ↦ R(v, W y)(Z y))`, which is
the endomorphism `TraceFrame.contMDiffAt_trace` consumes and which `RicciOrder` feeds only its
values on a frame.

**`mdiffHomAt_riemann`** — the curvature is a **differentiable** section of `Hom(TM, TM)` as soon
as `k ≥ 1`, which is what `HomCovariant`'s induced connection asks of its argument.

**`homCovFun_riemann_apply`** — **AND SO THE COVARIANT DERIVATIVE OF THE CURVATURE EXISTS AND IS
THE EXPRESSION IT SHOULD BE**: `(∇_u A)(σ x) = ∇_u (A σ) − A (∇_u σ)` with `A = R(X, W)`, for the
Levi-Civita connection of a `C^(k+2)` metric with `k ≥ 1`. `CurvatureBianchi` records this object
as *"not defined here or in the pinned Mathlib"*.

## What is NOT here, and the first item is a correction to a register written the same day

* **THIS IS NOT `∇R` AS A TENSOR, AND THE `UNLOCK_WATCHLIST` ITEM FILED FOR THE SECOND BIANCHI
  IDENTITY GOT THAT WRONG.** That item says `∇_X R(Y, Z)` *is* `HomCovariant.homCovFun` applied to
  the section `y ↦ curvEndo cov y (Y y) (Z y)`. **It is not.** Differentiating the composite
  differentiates `Y` and `Z` too, and the tensor Leibniz rule gives
  `(∇_u A) = (∇_u R)(Y, Z) + R(∇_u Y, Z) + R(Y, ∇_u Z)` where `A y = R(Y y, Z y)`. So the
  **tensorial** derivative is `(∇_u R)(Y, Z) = (∇_u A) − R(∇_u Y, Z) − R(Y, ∇_u Z)`, and every term
  of that right-hand side now exists — but **it is not defined here, and neither is its
  tensoriality in `Y` and `Z`**, which is what makes it a tensor and what the cyclic sum needs.
  `ERRATUM 494` files the correction and the item is amended. **Not attempted, no cost claimed**
  (`ERRATUM 246`).
* **NO SECOND BIANCHI IDENTITY**, for that reason: the identity is a statement about the tensor and
  the tensor is one subtraction away, not zero away.
* **NO REGULARITY OF THE INDUCED CONNECTION.** `HomCovariant` proves no smoothness of
  `homCovFun cov A`, so nothing here says `∇R` is a `C^(k-1)` section of anything — only that it
  exists and is computed at a point.
* **RESIDUE (ii) OF THE CURVATURE-REGULARITY ITEM IS UNTOUCHED**: whether a `C^(k+1)` metric would
  suffice where this route asks for `C^(k+2)` needs a counterexample, not a theorem.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `RicciOrder`'s, unchanged and in the same
order — `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, `[CompleteSpace E]`,
`[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]`, `[IsManifold I 3 M]` and `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`, a
`RiemannianBundle` on the tangent spaces with `[IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1
+ 1) E (TangentSpace I)]` and its literal-order companion at `2`. The six local instances are
`RicciOrder`'s as well, with `RicciOrder.contMDiffVectorBundle_add_two` added because the frame is
taken at order `k + 2`. The unused-variable linter reports nothing, so every binder is
load-bearing — which is `OrderBridge`'s finding again: the literal orders are the connection's
existence conditions.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureEndoOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor
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

/-- **THE RIEMANN CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` SECTION OF THE ENDOMORPHISM
BUNDLE**: `y ↦ R(X y, W y)` is a `C^k` section of `Hom(TM, TM)`, not merely a field whose values
on sections are `C^k`. -/
theorem contMDiffAt_riemann_hom {X W : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (LeviCivitaRegular.riemann I y (X y) (W y))) x := by
  have hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  refine LeviCivitaOrder.contMDiffAt_hom_of_localFrame _ (Module.finBasis ℝ E) fun i ↦ ?_
  exact RicciOrder.contMDiffAt_riemann hX hW
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1) _ (Module.finBasis ℝ E) i hx)

/-- **AND SO IS THE RICCI OPERATOR**: `y ↦ (v ↦ R(v, W y)(Z y))` is a `C^k` section of
`Hom(TM, TM)`. This is the endomorphism `TraceFrame.contMDiffAt_trace` consumes, and `RicciOrder`
feeds that lemma only its values on a frame. -/
theorem contMDiffAt_ricciOp_hom {W Z : Π x : M, TangentSpace I x} {x : M}
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (RicciOrder.ricciOp y (W y) (Z y))) x := by
  have hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  refine LeviCivitaOrder.contMDiffAt_hom_of_localFrame _ (Module.finBasis ℝ E) fun i ↦ ?_
  refine (RicciOrder.contMDiffAt_riemann
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1) _ (Module.finBasis ℝ E) i hx)
    hW hZ).congr_of_eventuallyEq ?_
  filter_upwards with y
  exact congrArg (TotalSpace.mk' E y) (RicciOrder.riemann_eq_ricciOp y _ (W y) (Z y)).symm

/-! ## The covariant derivative of the curvature -/

/-- **THE CURVATURE IS A DIFFERENTIABLE SECTION OF `Hom(TM, TM)`** as soon as `k ≥ 1`, which is
what `HomCovariant`'s induced connection asks of its argument. -/
theorem mdiffHomAt_riemann {X W : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) :
    HomCovariant.MDiffHomAt (fun y ↦ LeviCivitaRegular.riemann I y (X y) (W y)) x :=
  (contMDiffAt_riemann_hom hX hW).mdifferentiableAt (by exact_mod_cast hk)

/-- **AND SO THE COVARIANT DERIVATIVE OF THE CURVATURE EXISTS AND IS THE EXPRESSION IT SHOULD
BE**: `(∇_u R(X, W))(σ x) = ∇_u (R(X, W) σ) − R(X, W)(∇_u σ)`. This is the object
`CurvatureBianchi` records as undefined, for the Levi-Civita connection of a `C^(k+2)` metric with
`k ≥ 1`. -/
theorem homCovFun_riemann_apply {X W σ : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) (hσ : MDiffAt (T% σ) x)
    (u : TangentSpace I x) :
    HomCovariant.homCovFun (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
        (fun y ↦ LeviCivitaRegular.riemann I y (X y) (W y)) x u (σ x)
      = leviCivita (fun y ↦ LeviCivitaRegular.riemann I y (X y) (W y) (σ y)) x u
        - LeviCivitaRegular.riemann I x (X x) (W x) (leviCivita σ x u) := by
  have hA := mdiffHomAt_riemann hk hX hW
  rw [HomCovariant.homCovFun_apply hA,
    HomCovariant.homCovAux_congr_of_eq hA (mdifferentiableAt_extend (I := I) E _) hσ (by simp)]
  rfl

end CurvatureEndoOrder
