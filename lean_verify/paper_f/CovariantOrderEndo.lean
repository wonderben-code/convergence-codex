import CovariantOrderCurv
import HomCovariant
import LeviCivitaOrder

/-!
# The curvature of ANY connection of class `C^(k+1)` is a `C^k` section of `Hom(TM, TM)`

**The second rewrite of the abstract chain, and the file the previous unit named.** It is not the
last one, and the previous unit's own pricing of what is left was wrong — see the last section of
this header, which states the measured count. What it does close is the file it names: the last
declaration here **is** `CurvatureEndoOrder`'s theorem, binder for binder, derived from the
abstract one.
`CurvatureEndoOrder` makes the curvature a `C^k` section of the endomorphism bundle — not merely a
field whose values on sections are `C^k` — **for the Levi-Civita connection of a `C^(k+2)`
metric**. The previous unit removed the metric from the expression
(`CovariantOrderCurv.contMDiffAt_curvAux_of_isLocallyCk`) and priced what was left of the
`(R-REWRITE)` residue at *one file of rewrite, and one file that is not a rewrite*. This is the
rewrite, and it is cheap for a precise reason: of the two steps `CurvatureEndoOrder` takes, **only
one ever needed the metric**, and that one is what the previous unit removed. The frame lemma it
rests on was never about a metric at all — that is the sentence to be careful with, and it is not
that the route was metric-free at every step, because the values-on-the-frame step ran through the
Koszul formula until yesterday.

**WHY THE FRAME LEMMA IS METRIC-FREE, WHICH IS THE ONE THING WORTH CHECKING BEFORE WRITING THIS
FILE.**
`LeviCivitaOrder.contMDiffAt_hom_of_localFrame` — a section of `Hom(TM, TM)` is `C^n` at `x` as
soon as its values on the chart's local frame are `C^n` sections — lives in that file's `Hom`
section, whose binders are `[FiniteDimensional ℝ E]` and the frame's index type. **The
`RiemannianBundle` binder belongs to the `Frame` section above it and ends before this theorem**,
so the lemma carries neither a connection nor a metric, and the name it is filed under is the only
Levi-Civita thing about it. Feeding it the previous unit's theorem on the frame is four lines, the
same four `CurvatureEndoOrder` used with the metric's version.

**AND THE INDUCED CONNECTION ON `Hom(TM, TM)` WAS ALREADY GENERAL**, which is the second thing
worth checking rather than assuming: `HomCovariant` takes `cov` as a plain variable and asks no
regularity class of it at all, so once the curvature is a *differentiable* section of the
endomorphism bundle, `∇R` exists for any connection by the theorems already there. That is the last
two declarations here, and they are `CurvatureEndoOrder`'s last two with the connection's name
removed.

## What is proved

**`contMDiffVectorBundle_add_two'`**, **`eventually_cmdiffAt_two'`** — the two pieces of plumbing
`RicciOrder` states inside a metric's context: the tangent bundle of a `C^(k+3)` manifold is a
`C^(k+2)` vector bundle, which is the order the local frame is taken at, and a section of class
`C²` at a point is `C²` at every point of a neighbourhood. Both are restated here with **no metric
in the context** — that is the whole of the difference, and it is why they are primed rather than
imported.

**`isLocallyC1_of_class`** — `IsLocallyCk (k+1) cov` gives `CurvatureTensor.IsLocallyC1 cov`, which
is what `curvEndo` is defined under. `CovariantOrderMono.isLocallyC1_of_isLocallyCk` proved this as
a theorem; registering it as an instance is what lets `curvEndo cov` be written at all in a file
whose hypothesis is the order-`k` class.

**`contMDiffAt_curvEndo_apply`** — `y ↦ R(X y, Y y)(Z y)` is a `C^k` section for `X, Y, Z` of class
`C^(k+2)` at the point and any connection of class `C^(k+1)`: the previous unit's theorem about the
curvature *expression*, transported to the *endomorphism* along `curvEndo_apply` on a
neighbourhood.

**`contMDiffAt_curvEndo_hom`** — **THE THEOREM: `y ↦ R(X y, Y y)` IS A `C^k` SECTION OF
`Hom(TM, TM)` FOR ANY CONNECTION OF CLASS `C^(k+1)`**, in Mathlib's `ContMDiffAt` for the
endomorphism bundle. No metric, no Koszul formula, no Levi-Civita.

**`mdiffHomAt_curvEndo`** — and so the curvature is a **differentiable** section of `Hom(TM, TM)`
once `k ≥ 1`, which is what `HomCovariant`'s induced connection asks of its argument.

**`contMDiffAt_curvEndo_hom_leviCivita`** — **AND `CurvatureEndoOrder`'S THEOREM IS THE
LEVI-CIVITA CASE OF THIS ONE, ON BINDERS THAT AGREE ONE FOR ONE.** Checked with the elaborator
rather than read off the source (`ERRATUM 455`): `#check` on the two prints the same signature,
`[IsManifold I 1 M]` through `[IsContMDiffRiemannianBundle I 2 …]`, with only the bound field's name
differing. **So this declaration is a DELIBERATE DUPLICATE of
`CurvatureEndoOrder.contMDiffAt_riemann_hom`** — the one thing `dupname_scan.py` says it cannot see,
a duplicate under a different name — kept because a subsumption that is proved is worth more than
one that is asserted, and named here so the record exists where the mode cannot look. Neither file
is withdrawn, on `ERRATUM 465`'s rule and the previous unit's precedent: that proof is
self-contained where this one routes through a class and an instance, and two files quote it
(`CurvatureCovOrder`, `HomCovariantOrder`).

**`homCovFun_curvEndo_apply`** — **AND SO `∇R` EXISTS FOR ANY SUCH CONNECTION AND IS THE
EXPRESSION IT SHOULD BE**: `(∇_u R(X, Y))(σ x) = ∇_u (R(X, Y) σ) − R(X, Y)(∇_u σ)`.
`CurvatureBianchi` records this object as *"not defined here or in the pinned Mathlib"*;
`CurvatureEndoOrder` defined it for the Levi-Civita connection earlier today, and this is that
statement with the connection arbitrary.

## What is NOT here

* **THIS IS STILL NOT `∇R` AS A TENSOR**, and `ERRATUM 494` is the reason in full:
  differentiating `y ↦ R(X y, Y y)` differentiates `X` and `Y` too, so the tensorial derivative is
  `(∇_u R)(X, Y) = (∇_u A) − R(∇_u X, Y) − R(X, ∇_u Y)`, one subtraction away rather than zero
  away. **AND THAT FAMILY IS BIGGER THAN THE PREVIOUS UNIT SAID.** `CurvatureCovDeriv.covRiemann`
  is a **definition** with `leviCivita` written into it, not a theorem quoting a Levi-Civita lemma,
  and `CurvatureCovTensor`, `CurvatureCovBundle`, `CurvatureCovCyclic` and `CurvatureBianchiSecond`
  are all stated about it. So lifting them is a re-DEFINITION followed by re-proving every theorem
  over it, which is a different and larger job than re-pointing a quoted lemma. **Not attempted
  here, no cost claimed** (`ERRATUM 246`), and `ERRATUM 498` corrects the pricing.
* **NOTHING ABOUT THE RICCI OR SCALAR CURVATURE.** A trace needs a metric, so `RicciOrder`'s and
  `ScalarOrder`'s function-valued results are not a rewrite at all and never will be. The previous
  unit's entry says this and it is repeated here because this file is where a reader would look.
* **NOT THE REGULARITY OF THE INDUCED CONNECTION.** `HomCovariantOrder` proves that for the
  Levi-Civita connection and is one of the **four** files that quote
  `LeviCivitaOrder.contMDiffAt_leviCivita_apply` **in code** (the residue's own criterion, measured
  today: `CurvatureBianchiSecond`, `CurvatureCovOrder`, `CurvatureOrder`, `HomCovariantOrder` — of
  which `CurvatureOrder` is the one the previous unit subsumed). Not attempted here.
* **NO REGULARITY OF `∇R`.** `HomCovariant` proves no smoothness of `homCovFun cov A`, and
  `HomCovariantOrder` proves it only for the Levi-Civita connection; nothing here says `∇R` is a
  `C^(k-1)` section of anything, only that it exists and is computed at a point.
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number.
⚠ **`∞` IS REACHED ON 2026-09-11 AND `ω` IS NOT, kept as written** (`ERRATUM 505`):
`CovariantOrderInfty` states this file's results at the **smooth** order — the class at `∞` is the
class at every finite order (`isLocallyCk_infty_of_nat`), the Levi-Civita connection of a `C^∞`
metric is in it, and the curvature, `∇R` and the second Bianchi identity follow. **The sentence is
still true of `ω`**, which has no *`C^n` for every `n`* characterisation, and true of this file,
which proves nothing at either.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `E` normed over `ℝ` with
`[CompleteSpace E]` and `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`,
`[IsManifold I 1 M]`, `[IsManifold I 2 M]`, `[IsManifold I 3 M]` and
`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`. The `C³` binder is load-bearing here where the
previous unit could drop it: `curvEndo` is declared under `CurvatureTensor`'s `C²`-vector-bundle
instance, which needs it, so it is an existence condition for the object rather than slack
(`OrderBridge`'s finding, in a third place). **Five of the eight** declarations take
`[IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]`; **four** of those five also take
`[CurvatureTensor.IsLocallyC1 cov]`, for the reason §2 gives, and **two** of the four take
`k ≠ 0`. The eighth takes **neither class and no connection at all** — it is the Levi-Civita
subsumption, and its binders are the metric's — which is why these figures were read from `#check`
and not from the section headers.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderEndo

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CovariantOrderClass
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureTensor.contMDiffVectorBundle_two KoszulManifold.finDimTangent

/-! ## 1. The plumbing, with no metric in the context -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M] in
/-- The tangent bundle of a `C^(k+3)` manifold is a `C^(k+2)` vector bundle, which is the order the
chart's local frame has to be available at. `RicciOrder.contMDiffVectorBundle_add_two` is this
statement inside a `RiemannianBundle` context; the proof needs no metric. -/
theorem contMDiffVectorBundle_add_two' :
    ContMDiffVectorBundle ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_add_two'

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A section of class `C²` at a point is `C²` at every point of a neighbourhood.
`RicciOrder.eventually_cmdiffAt_two` is this statement inside a `RiemannianBundle` context, proved
in four lines through the `ContMDiffOn` route; Mathlib's `contMDiffAt_iff_contMDiffAt_nhds` gives
the `∀ᶠ` form directly, at every order except `∞`. -/
theorem eventually_cmdiffAt_two' {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt (2 : WithTop ℕ∞) (T% Z) x) :
    ∀ᶠ y in 𝓝 x, CMDiffAt (2 : WithTop ℕ∞) (T% Z) y :=
  (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hZ

/-- **THE ORDER CLASS GIVES THE CLASS THE CURVATURE IS DEFINED UNDER**: `IsLocallyCk (k+1) cov`
gives `CurvatureTensor.IsLocallyC1 cov`, by `CovariantOrderMono`'s bridge at order one. -/
theorem isLocallyC1_of_class [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov] :
    CurvatureTensor.IsLocallyC1 cov :=
  CovariantOrderMono.isLocallyC1_of_isLocallyCk (n := (k : WithTop ℕ∞) + 1) le_add_self ‹_›

/-! ## 2. The curvature endomorphism as a section

**WHY THE NEXT FOUR DECLARATIONS CARRY BOTH CLASSES, WHICH IS LEAN'S REQUIREMENT AND NOT A
MATHEMATICAL ONE.** `curvEndo cov` is declared under `CurvatureTensor.IsLocallyC1 cov`, so that
instance has to be available when the STATEMENTS below are elaborated, not merely inside their
proofs. `isLocallyC1_of_class` above supplies it -- but it cannot be registered as an instance:
its conclusion is `IsLocallyC1 cov`, in which the order `k` does not occur, so the elaborator
reports *cannot find synthesization order* and every remaining argument is a metavariable. So both
binders are carried, and `isLocallyC1_of_class` is what a caller who has the order class uses to
discharge the second -- nobody has to prove anything twice, and no theorem here is stronger than
its `IsLocallyCk` hypothesis alone. The class is a `Prop`, so the two are proof-irrelevant and
cannot disagree. -/

variable [CurvatureTensor.IsLocallyC1 cov]

/-- **THE CURVATURE ENDOMORPHISM OF ANY `C^(k+1)` CONNECTION, APPLIED TO A `C^(k+2)` FIELD, IS A
`C^k` SECTION**: `y ↦ R(X y, Y y)(Z y)` is `C^k` at `x`, because near `x` it is the curvature
expression on the three fields. -/
theorem contMDiffAt_curvEndo_apply [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ curvEndo cov y (X y) (Y y) (Z y))) x := by
  have h2 : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 + 1 := by
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 + 1 by omega)
  refine (CovariantOrderCurv.contMDiffAt_curvAux_of_isLocallyCk cov hX hY
    hZ).congr_of_eventuallyEq ?_
  filter_upwards [eventually_mdiffAt_of_cmdiffAt (hX.of_le h2),
    eventually_mdiffAt_of_cmdiffAt (hY.of_le h2),
    eventually_cmdiffAt_two' (hZ.of_le h2)] with y hXy hYy hZy
  exact congrArg (TotalSpace.mk' E y) (curvEndo_apply cov hXy hYy hZy)

/-- **THE CURVATURE OF ANY `C^(k+1)` CONNECTION IS A `C^k` SECTION OF THE ENDOMORPHISM BUNDLE**:
`y ↦ R(X y, Y y)` for `X, Y` of class `C^(k+2)` at the point, in Mathlib's `ContMDiffAt` for
`Hom(TM, TM)` rather than as values on sections. No metric, no Koszul formula, no Levi-Civita. -/
theorem contMDiffAt_curvEndo_hom [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (curvEndo cov y (X y) (Y y))) x := by
  have hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  refine LeviCivitaOrder.contMDiffAt_hom_of_localFrame _ (Module.finBasis ℝ E) fun i ↦ ?_
  exact contMDiffAt_curvEndo_apply cov hX hY
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1) _ (Module.finBasis ℝ E) i hx)

/-! ## 3. The covariant derivative of the curvature, for an arbitrary connection -/

/-- **THE CURVATURE IS A DIFFERENTIABLE SECTION OF `Hom(TM, TM)`** as soon as `k ≥ 1`, which is
what `HomCovariant`'s induced connection asks of its argument. -/
theorem mdiffHomAt_curvEndo [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]
    {X Y : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x) :
    HomCovariant.MDiffHomAt (fun y ↦ curvEndo cov y (X y) (Y y)) x :=
  (contMDiffAt_curvEndo_hom cov hX hY).mdifferentiableAt (by exact_mod_cast hk)

/-- **AND SO THE COVARIANT DERIVATIVE OF THE CURVATURE EXISTS FOR ANY CONNECTION OF CLASS
`C^(k+1)`, AND IS THE EXPRESSION IT SHOULD BE**:
`(∇_u R(X, Y))(σ x) = ∇_u (R(X, Y) σ) − R(X, Y)(∇_u σ)`. `HomCovariant` asks no regularity class of
`cov` at all, so what was needed was the differentiability above and nothing else. -/
theorem homCovFun_curvEndo_apply [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]
    {X Y σ : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x) (hσ : MDiffAt (T% σ) x)
    (u : TangentSpace I x) :
    HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (X y) (Y y)) x u (σ x)
      = cov (fun y ↦ curvEndo cov y (X y) (Y y) (σ y)) x u
        - curvEndo cov x (X x) (Y x) (cov σ x u) := by
  have hA := mdiffHomAt_curvEndo cov hk hX hY
  rw [HomCovariant.homCovFun_apply hA,
    HomCovariant.homCovAux_congr_of_eq hA (mdifferentiableAt_extend (I := I) E _) hσ (by simp)]
  rfl

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self

/-- **AND `CurvatureEndoOrder`'S THEOREM IS THE LEVI-CIVITA CASE OF IT**, on the hypotheses that
file already carries: a `C^(k+3)` manifold, a `C^(k+2)` metric and its `C²` companion.
`LeviCivitaRegular.riemann` is an `abbrev` for `curvEndo leviCivita`, so what has to be supplied is
only the order class at `k + 1`, from `CovariantOrderClass.isLocallyCk_leviCivita`. Recorded as a
theorem rather than as a remark (the previous unit's precedent), so the subsumption is checked and
not asserted. -/
theorem contMDiffAt_curvEndo_hom_leviCivita {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (LeviCivitaRegular.riemann I y (X y) (Y y))) x := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  haveI : IsLocallyCk ((k : WithTop ℕ∞) + 1)
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) := by
    rw [← e]
    exact CovariantOrderClass.isLocallyCk_leviCivita (k := k + 1)
  exact contMDiffAt_curvEndo_hom _ hX hY

end LeviCivita

end CovariantOrderEndo
