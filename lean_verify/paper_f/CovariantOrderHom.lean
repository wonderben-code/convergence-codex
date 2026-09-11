import CovariantOrderApply
import HomCovariant
import LeviCivitaOrder

/-!
# The induced connection on `Hom(TM, TM)` is regular for ANY connection of class `C^k`

**This file closes a fence `HomCovariantOrder` wrote about itself.** That file proves the induced
connection on the endomorphism bundle regular — `(∇_X A)(W)` is a `C^k` section for a `C^(k+1)`
section `A` — and says in its own *What is NOT here*:

> **ONLY THE LEVI-CIVITA CONNECTION.** `HomCovariant` builds the induced connection for an
> arbitrary covariant derivative on the tangent bundle; the regularity here uses `LeviCivitaOrder`'s
> theorems and so is about `leviCivita` only. For an abstract `cov` the statement would be
> *`∇^{Hom}` is `C^k` when `cov` is*, and that needs the order-`k` hypothesis in the form
> `CovariantOrderClass.IsLocallyCk` — which exists — but no such statement is
> made.

**That statement is made here**, and the fence's own description of it is exact: the only
Levi-Civita input was `LeviCivitaOrder.contMDiffAt_leviCivita_apply`, used twice, and entry 120
replaced it with `CovariantOrderApply.contMDiffAt_covApply` on that class. Everything else in the
proof — `HomCovariant`'s induced operation, its tensoriality, Mathlib's
`ContMDiffAt.clm_bundle_apply`, and the frame criterion — never mentioned a connection or a metric.

**AND THE ABSTRACT ROUTE ASKS LESS OF THE DIRECTION FIELD**, which is entry 120's dividend showing
up for the second time: `LeviCivitaOrder.contMDiffAt_leviCivita_apply` wants both of its fields at
`C^(k+1)` where `contMDiffAt_covApply` wants the direction only at `C^k`. That is invisible in the
theorem below, whose direction field is still asked for at `C^(k+1)` — because the same field is
also fed to `ContMDiffAt.clm_bundle_apply`, which needs it there — and it is written down so the
next reader does not go looking for a weakening that is blocked elsewhere.

**NO NEIGHBOURHOOD HELPERS, AND THAT IS DELIBERATE — WITH A COUNT THAT IS NOT FLATTERING.**
`HomCovariantOrder` names two (`eventually_mdiffHomAt`, `eventually_mdiffAt`) for *a section of
class `C^(k+1)` at a point is differentiable near it*, and **both carry a `[RiemannianBundle …]`
binder the fact does not need** — read from `#check` and not from the `omit` lines, which drop five
binders each and not that one. The demonstration that it is not needed is this file: the same two
facts are used here in a context with **no metric at all**, inline from Mathlib's
`contMDiffAt_iff_contMDiffAt_nhds`, two lines inside one `filter_upwards`.

**AND THE REASON TO DO IT INLINE IS A MEASUREMENT, NOT TASTE.** That one fact — regular at a point
implies regular on a neighbourhood — is declared **six times** in this estate, at different orders
and for different bundles: `BracketDerivation.eventually_mdifferentiableAt`,
`CurvatureTensor.eventually_mdiffAt_of_cmdiffAt`, `RicciOrder.eventually_cmdiffAt_two`,
`HomCovariantOrder`'s two, and `CovariantOrderEndo.eventually_cmdiffAt_two'` — **which entry 122
wrote an hour before this file**, so the count includes one of mine. All six are one-line
specialisations of a lemma Mathlib already has in general form. This file adds a seventh to nothing,
and the de-duplication is filed as an `UNLOCK_WATCHLIST` item with its target named rather than done
here, because it edits six files and this unit edits one.

## What is proved

**`contMDiffAt_homCovFun_apply_of_isLocallyCk`** — **THE INDUCED CONNECTION OF ANY `C^k` CONNECTION
IS REGULAR**: for `A` a `C^(k+1)` section of `Hom(TM, TM)` and `X, W` of class `C^(k+1)` at the
point, `y ↦ (∇_X A)(W)(y)` is a `C^k` section. The proof is the identity
`(∇_X A)(W) = ∇_X (A W) − A (∇_X W)`, which is `homCovAux`'s definition once tensoriality has
replaced the extended vector by the section `W`.

**`contMDiffAt_homCovFun_hom_of_isLocallyCk`** — **AND SO `∇_X A` IS A `C^k` SECTION OF
`Hom(TM, TM)`**, through the frame criterion fed the theorem above on the chart's own frame.

**`contMDiffAt_homCovFun_hom_leviCivita`** — **AND `HomCovariantOrder`'S THEOREM IS THE LEVI-CIVITA
CASE OF IT**, on that file's own hypotheses: a `C^(k+2)` manifold and a `C^(k+1)` metric, with
`CovariantOrderClass.isLocallyCk_leviCivita` supplying the class. Recorded as a theorem rather than
as a remark so that the subsumption is checked and not asserted, which is this campaign's precedent
for it; and since the statement then coincides with
`HomCovariantOrder.contMDiffAt_homCovFun_hom`, it is a **deliberate duplicate under a different
name** — the case `dupname_scan.py` says it cannot see — kept for that reason and named here
because no mode will raise it.

## What is NOT here

* **NO REGULARITY OF `∇R`, AND THE REASON IS UNCHANGED BY THIS FILE.** `HomCovariantOrder`'s own
  fence says feeding the curvature to this theorem needs it at `C^(k+1)`, which is the curvature's
  regularity **one order up**, plus two correction terms at a further shift. Entry 122 made the
  curvature's `Hom`-bundle regularity abstract, so both legs now exist for an arbitrary connection
  — and the order shift is still nobody's theorem. **Not attempted, no cost claimed**
  (`ERRATUM 246`).
  **⚠ THE LAST CLAUSE IS FALSE AND IS KEPT AS WRITTEN** (`ERRATUM 94`, **`ERRATUM 499`**, the next
  unit). The shift is `CurvatureCovOrder.contMDiffAt_covRiemann_hom`, which does exactly this
  bookkeeping for the **Levi-Civita** connection and says so in its own header; it was in the list
  of four files this campaign had measured two units earlier. What is open is the **abstract**
  version, which is that file lifted.
* **NOTHING ABOUT `∇R` AS A TENSOR.** `ERRATUM 494`'s correction and `ERRATUM 498`'s pricing both
  stand: `CurvatureCovDeriv.covRiemann` is a definition with `leviCivita` written into its body, so
  that family is a re-definition and not a re-pointing.
* **NO SECOND BIANCHI IDENTITY**, which is a statement about fields and needs the cyclic sum, not
  regularity.
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`, and from the signatures rather than the
section header because entry 122 found the two disagreeing): `E` normed over `ℝ` with
`[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]` and `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]` — **a `C^(k+2)` manifold, no
`C³` binder and no metric**, where `HomCovariantOrder` asks for a `C^(k+1)` metric and its
literal-order companion. Two of the three declarations take
`[CovariantOrderClass.IsLocallyCk (k : WithTop ℕ∞) cov]`, at order `k` and not `k + 1`: this file
differentiates the section `A`, never the connection twice. The third takes the metric instead and
no connection at all.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderHom

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CovariantOrderClass
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

attribute [local instance] KoszulOrder.isManifold_succ KoszulOrder.contMDiffVectorBundle_succ
  KoszulManifold.finDimTangent

/-- **THE INDUCED CONNECTION ON THE ENDOMORPHISM BUNDLE IS REGULAR FOR ANY CONNECTION OF CLASS
`C^k`**: for `A` a `C^(k+1)` section of `Hom(TM, TM)` and `X, W` of class `C^(k+1)` at the point,
`y ↦ (∇_X A)(W)(y)` is a `C^k` section. `HomCovariantOrder` proves this for the Levi-Civita
connection and its own fence asks for exactly this statement. -/
theorem contMDiffAt_homCovFun_apply_of_isLocallyCk [IsLocallyCk (k : WithTop ℕ∞) cov]
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {X W : Π y : M, TangentSpace I y}
    {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% W) x) :
    CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ HomCovariant.homCovFun cov A y (X y) (W y))) x := by
  have hXk : CMDiffAt (k : WithTop ℕ∞) (T% X) x := hX.of_le le_self_add
  have hAW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% (fun y ↦ A y (W y))) x :=
    ContMDiffAt.clm_bundle_apply hA hW
  have hcovW : CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ cov W y (X y))) x :=
    CovariantOrderApply.contMDiffAt_covApply cov hXk hW
  have h1 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ cov (fun y' ↦ A y' (W y')) y (X y))) x :=
    CovariantOrderApply.contMDiffAt_covApply cov hXk hAW
  have h2 : CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ A y (cov W y (X y)))) x :=
    ContMDiffAt.clm_bundle_apply (hA.of_le le_self_add) hcovW
  refine (h1.sub_section h2).congr_of_eventuallyEq ?_
  filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hA,
    (contMDiffAt_iff_contMDiffAt_nhds (by simp)).1 hW] with y hAy hWy
  refine congrArg (TotalSpace.mk' E y) ?_
  rw [HomCovariant.homCovFun_apply (hAy.mdifferentiableAt (by simp)),
    HomCovariant.homCovAux_congr_of_eq (hAy.mdifferentiableAt (by simp))
      (mdifferentiableAt_extend (I := I) E _) (hWy.mdifferentiableAt (by simp)) (by simp)]
  rfl

/-- **AND SO `∇_X A` IS A `C^k` SECTION OF `Hom(TM, TM)`** for any connection of class `C^k`, not
merely a field whose values on sections are `C^k` — through the frame criterion, fed the theorem
above on the chart's own frame. -/
theorem contMDiffAt_homCovFun_hom_of_isLocallyCk [IsLocallyCk (k : WithTop ℕ∞) cov]
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {X : Π y : M, TangentSpace I y} {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (HomCovariant.homCovFun cov A y (X y))) x := by
  have hx : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  refine LeviCivitaOrder.contMDiffAt_hom_of_localFrame _ (Module.finBasis ℝ E) fun i ↦ ?_
  exact contMDiffAt_homCovFun_apply_of_isLocallyCk cov hA hX
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1) _ (Module.finBasis ℝ E) i hx)

section LeviCivita

variable [CompleteSpace E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- **AND `HomCovariantOrder`'S THEOREM IS THE LEVI-CIVITA CASE OF IT**, on that file's own
hypotheses — a `C^(k+2)` manifold and a `C^(k+1)` metric — with
`CovariantOrderClass.isLocallyCk_leviCivita` supplying the class. A theorem rather than a remark so
the subsumption is checked; and therefore a deliberate duplicate of that file's
`contMDiffAt_homCovFun_hom` under a different name, which no mode here can detect. -/
theorem contMDiffAt_homCovFun_hom_leviCivita
    {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {X : Π y : M, TangentSpace I y} {x : M}
    (hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x)
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (HomCovariant.homCovFun
        (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) A y (X y))) x :=
  contMDiffAt_homCovFun_hom_of_isLocallyCk _ hA hX

end LeviCivita

end CovariantOrderHom
