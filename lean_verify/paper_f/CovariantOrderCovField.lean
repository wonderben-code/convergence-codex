import CovariantOrderCovDeriv
import CurvatureCovOrder

/-!
# `∇R` is a `C^k` field for ANY connection of class `C^(k+2)`

**This is `ERRATUM 499`'s unit, and the erratum is why it is written now.** Three units of this
campaign wrote that the regularity of `∇R` waits on an order shift that is *still nobody's
theorem*. It is `CurvatureCovOrder.contMDiffAt_covRiemann_hom`, which does exactly that bookkeeping
for the **Levi-Civita** connection, says so in its own header, and was in the four-file list this
campaign had measured two units earlier. Asking `PROOF_STRATEGY` §6's third question as it is
written — *if the unit I just finished was a `B`, retry `A` now* — found that, and **this file is
the retry**: `CurvatureCovOrder` with the connection made a variable.

**THE THREE LEGS ARE THE THREE UNITS BEFORE THIS ONE**, which is the whole reason it costs a
substitution:

* the curvature as a `C^(k+1)` section of `Hom(TM, TM)` — `CovariantOrderEndo`, entry 122, where
  `CurvatureCovOrder` uses `CurvatureEndoOrder.contMDiffAt_riemann_hom` **one order up**;
* the induced connection's regularity — `CovariantOrderHom`, entry 123, in place of
  `HomCovariantOrder.contMDiffAt_homCovFun_hom`;
* `∇R` itself — `CovariantOrderCovDeriv`, entry 124, in place of `CurvatureCovDeriv.covRiemann`.

The fourth input, the derivative of a direction field two orders up, is `CovariantOrderApply`'s
(entry 120) in place of `LeviCivitaOrder.contMDiffAt_leviCivita_apply`, **and it asks less**: that
lemma wants both fields at `C^(k+3)` where `contMDiffAt_covApply` wants the direction only at
`C^(k+2)`. The hypotheses below are `C^(k+3)` on all three fields anyway, because the curvature leg
needs them there, so the slack is recorded and not spent.

## What is proved

**`isLocallyCk_up`**, **`isLocallyCk_up_two`**, **`isLocallyCk_down_one`** — the class at three of
the four orders the legs ask for: `↑(k+1) + 1` and `↑(k+2)` upward by the cast
`CurvatureOrder.isManifold_shift` introduced, and `↑k + 1` downward by `CovariantOrderMono`'s
order-lowering. **The fourth, `↑k`, is not declared here**: entry 121's
`CovariantOrderCurv.isLocallyCk_down` lowers by one from `↑k + 1`, so with the third of these
registered the elaborator chains them and gets there itself. A first draft declared a second
`isLocallyCk_down` doing both steps at once, and `newnames_scan.py` asked the right question about
it. **Three class shifts, then, where `CurvatureCovOrder` needs eight instance shifts**, and the
arithmetic is worth one line: the metric's four have no counterpart when there is no metric, the
manifold's four are that file's own and are imported rather than reproved, and the class's are what
that file never needs, because `leviCivita` belongs to the class at every order by a global
instance.

**`contMDiffAt_covRiemann_hom_of_isLocallyCk`** — **THE THEOREM: `y ↦ (∇_X R)(Y, Z)(y)` IS A `C^k`
SECTION OF `Hom(TM, TM)` FOR ANY CONNECTION OF CLASS `C^(k+2)`**, for `X, Y, Z` of class `C^(k+3)`
at the point. No metric, no Koszul formula, no Levi-Civita. The three terms of `covRiemann` are
handled by the induced connection's regularity on the curvature field one order up, and by the
curvature's own `Hom`-regularity on the two corrections, whose direction fields come from the
abstract `∇_Y Z` lemma two orders up.

**`contMDiffAt_covRiemann_hom_leviCivita`** — **AND `CurvatureCovOrder`'S THEOREM IS THE
LEVI-CIVITA CASE OF IT.** `CovariantOrderClass.isLocallyCk_leviCivita` supplies the class at every
order, `covRiemann_eq` identifies the objects by `rfl`, and the statement is then that file's. The
third checked subsumption in four units, and the third deliberate duplicate under a different name
— recorded because `dupname_scan.py` cannot see that kind.

## What is NOT here

* **NO SECOND BIANCHI IDENTITY**, abstract or otherwise. Unchanged and unaffected: the cyclic sum
  is a statement about fields at a point and needs none of this regularity. **Not attempted, no
  cost claimed** (`ERRATUM 246`).
* **NO TENSORIALITY.** That `∇R` depends on its two direction fields only through their values is
  `CurvatureCovTensor`'s, still Levi-Civita-only, and entry 124's slot laws are its input. Not
  attempted here.
* **NO TRACE, NO DIVERGENCE.** The contracted Bianchi identity needs a trace of this object against
  a metric, and a general connection has none — so that direction is `CurvatureCovOrder`'s to keep,
  and which contraction is meant remains the author's decision (`ASSUMPTIONS 56`).
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `WALLS` §W5's rung 4 is unchanged and
  still prices as a research project. **No wall moves.**
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number.

**No published tag moves.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`; from the signatures because entry 122 found a
header and its binders disagreeing, and entry 124 found a section binder its only declaration did
not use): `E` normed over `ℝ` with `[CompleteSpace E]` and `[FiniteDimensional ℝ E]`, a
`ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`, `[IsManifold I 3 M]`
and `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]` — **a `C^(k+4)` manifold, as in
`CurvatureCovOrder`, and NO metric at any order**, where that file also asks for a `C^(k+3)` metric
and its companion at `2`. **Four of the five** declarations take
`[CovariantOrderClass.IsLocallyCk ((k : WithTop ℕ∞) + 1 + 1) cov]`, the fifth takes the metric and
no connection at all — its binders are `CurvatureCovOrder`'s theorem's, one for one, which is what
makes the subsumption a check rather than a claim — and `[CurvatureTensor.IsLocallyC1 cov]` rides
along for `curvEndo` as in entry 122. **And none of the five takes `k ≠ 0`**: the slot laws of entry
124 need it and this regularity does not, which is `CurvatureCovOrder`'s signature too — my first
draft carried `hk` on both theorems and the unused-variable linter removed it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderCovField

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CovariantOrderClass
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [CurvatureTensor.IsLocallyC1 cov]

attribute [local instance] CurvatureCovOrder.isManifold_up CurvatureCovOrder.isManifold_up_two
  CurvatureCovOrder.isManifold_down CurvatureCovOrder.isManifold_down_two
  CurvatureTensor.contMDiffVectorBundle_two KoszulManifold.finDimTangent

variable [IsLocallyCk ((k : WithTop ℕ∞) + 1 + 1) cov]

/-! ## The class at the shifted orders -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M] [CurvatureTensor.IsLocallyC1 cov] in
/-- The class at `↑(k+1) + 1`, which is what the curvature's `Hom`-bundle regularity asks for one
order up. A cast and `infer_instance`, the device `CurvatureOrder.isManifold_shift` introduced. -/
theorem isLocallyCk_up : IsLocallyCk ((((k + 1 : ℕ) : WithTop ℕ∞)) + 1) cov := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M] [CurvatureTensor.IsLocallyC1 cov] in
/-- The class at `↑(k+2)`, which is what the abstract `∇_Y Z` lemma asks for two orders up. -/
theorem isLocallyCk_up_two : IsLocallyCk (((k + 2 : ℕ) : WithTop ℕ∞)) cov := by
  have e : (((k + 2 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  rw [e]; infer_instance

omit [IsManifold I 3 M] [CurvatureTensor.IsLocallyC1 cov] in
/-- The class at order `k + 1`, which the curvature's `Hom`-bundle regularity asks for at the
unshifted order, and at order `k`, which the induced connection's regularity asks for. Both by
`CovariantOrderMono`'s order-lowering. -/
theorem isLocallyCk_down_one : IsLocallyCk ((k : WithTop ℕ∞) + 1) cov :=
  ⟨fun u hu ↦ CovariantOrderMono.contMDiffCovariantDerivativeOn_of_le
    (j := k + 1) (n := (k : WithTop ℕ∞) + 1 + 1)
    (by exact_mod_cast (le_self_add : (k : WithTop ℕ∞) + 1 ≤ (k : WithTop ℕ∞) + 1 + 1))
    IsLocallyCk.on_open u hu⟩

/-! **AND THE CLASS AT ORDER `k` IS NOT DECLARED HERE, BECAUSE ENTRY 121 ALREADY HAS IT.**
`CovariantOrderCurv.isLocallyCk_down` lowers the class by one from `↑k + 1`, and with
`isLocallyCk_down_one` above registered as an instance the elaborator chains the two and reaches
`↑k` on its own. A first draft of this file declared a second `isLocallyCk_down` that lowered two
orders at once; `newnames_scan.py` asked whether the name was taken and whether the declaration
holding it was the theorem I was about to prove, and the answer to both was yes. There is no loop in
the chain: `↑k + 1` does not unify with `↑(k + 1)`, so the search stops. -/

attribute [local instance] isLocallyCk_up isLocallyCk_up_two isLocallyCk_down_one
  CovariantOrderCurv.isLocallyCk_down

/-! ## `∇R` is a field -/

/-- **THE COVARIANT DERIVATIVE OF THE CURVATURE OF ANY `C^(k+2)` CONNECTION IS A `C^k` SECTION OF
`Hom(TM, TM)`**: for `X, Y, Z` of class `C^(k+3)` at the point, `y ↦ (∇_X R)(Y, Z)(y)` is a `C^k`
field of endomorphisms. `CurvatureCovOrder` proves this for the Levi-Civita connection of a
`C^(k+3)` metric on a `C^(k+4)` manifold; the manifold's order is the same here and the metric is
gone. -/
theorem contMDiffAt_covRiemann_hom_of_isLocallyCk {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (CovariantOrderCovDeriv.covRiemann cov Y Z y (X y))) x := by
  have ecast : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  have ecast2 : (((k + 2 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  -- the curvature field, one order up
  have hA : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ((k : WithTop ℕ∞) + 1)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (curvEndo cov y (Y y) (Z y))) x := by
    have h := CovariantOrderEndo.contMDiffAt_curvEndo_hom (k := k + 1) cov
      (X := Y) (Y := Z) (by rw [ecast]; exact hY) (by rw [ecast]; exact hZ)
    rwa [ecast] at h
  -- the two derivatives of the direction fields, two orders up
  have hdY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (fun y ↦ cov Y y (X y))) x := by
    have h := CovariantOrderApply.contMDiffAt_covApply (k := k + 2) cov
      (Y := X) (Z := Y) (by rw [ecast2]; exact hX.of_le le_self_add) (by rw [ecast2]; exact hY)
    rwa [ecast2] at h
  have hdZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (fun y ↦ cov Z y (X y))) x := by
    have h := CovariantOrderApply.contMDiffAt_covApply (k := k + 2) cov
      (Y := X) (Z := Z) (by rw [ecast2]; exact hX.of_le le_self_add) (by rw [ecast2]; exact hZ)
    rwa [ecast2] at h
  have hYd : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x := hY.of_le le_self_add
  have hZd : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x := hZ.of_le le_self_add
  -- the three terms
  have h1 : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (HomCovariant.homCovFun cov (fun y' ↦ curvEndo cov y' (Y y') (Z y')) y (X y))) x :=
    CovariantOrderHom.contMDiffAt_homCovFun_hom_of_isLocallyCk cov hA
      (hX.of_le (le_self_add.trans le_self_add))
  have h2 : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (curvEndo cov y (cov Y y (X y)) (Z y))) x :=
    CovariantOrderEndo.contMDiffAt_curvEndo_hom cov hdY hZd
  have h3 : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (curvEndo cov y (Y y) (cov Z y (X y)))) x :=
    CovariantOrderEndo.contMDiffAt_curvEndo_hom cov hYd hdZ
  exact (h1.sub_section h2).sub_section h3

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureCovOrder.isContMDiffRiemannianBundle_up
  CurvatureCovOrder.isContMDiffRiemannianBundle_up_two
  CurvatureCovOrder.isContMDiffRiemannianBundle_down
  CurvatureCovOrder.isContMDiffRiemannianBundle_down_two

/-- **AND `CurvatureCovOrder`'S THEOREM IS THE LEVI-CIVITA CASE OF IT.** The class comes from
`CovariantOrderClass.isLocallyCk_leviCivita` at the shifted order and the objects are identified by
`CovariantOrderCovDeriv.covRiemann_eq`, which is `rfl`. A theorem rather than a remark so the
subsumption is checked; and therefore a deliberate duplicate of that file's
`contMDiffAt_covRiemann_hom` under a different name, which no mode here can detect. -/
theorem contMDiffAt_covRiemann_hom_leviCivita {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (CurvatureCovDeriv.covRiemann Y Z y (X y))) x := by
  have e : (((k + 2 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  haveI : IsLocallyCk ((k : WithTop ℕ∞) + 1 + 1)
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) := by
    rw [← e]
    exact CovariantOrderClass.isLocallyCk_leviCivita (k := k + 2)
  have h := contMDiffAt_covRiemann_hom_of_isLocallyCk
    (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) hX hY hZ
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with y
  exact congrArg (TotalSpace.mk' (E →L[ℝ] E) y)
    (CovariantOrderCovDeriv.covRiemann_eq Y Z y (X y)).symm

end LeviCivita

end CovariantOrderCovField
