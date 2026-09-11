import CovariantOrderCovField
import CovariantOrderBianchiSecond

/-!
# The curvature chain at order `∞`

**TEN FILES OF THIS CHAIN FENCE THE NON-FINITE ORDER, AND WHAT THEY SAY IS TRUE WHILE WHAT IT
IMPLIES IS NOT.** Eight carry the sentence ***NOTHING AT THE ANALYTIC ORDER**, `k` being a natural
number* — `CovariantOrderCurv`, `CovariantOrderEndo`, `CovariantOrderHom`, `CovariantOrderCovDeriv`,
`CovariantOrderCovField`, `CovariantOrderCovTensor`, `CovariantOrderCovBundle`,
`CovariantOrderCovCyclic` — and two carry a variant of it, `CovariantOrderApply` (*NOTHING ABOUT
`ω`*) and `CovariantOrderBianchiSecond`. **Counted from the files, because the census that found
this target reported seven**: the probe skips paragraphs carrying a `⚠` and `CovariantOrderHom`'s
does, which is the reproducibility caveat `ERRATUM 505` records about that census rather than a
defect in it.

**The analytic order is `ω`, and nothing here reaches it either** — the reason `CovariantOrderApply`
gives stands and is restated below. But a reader of *`k` being a natural number* takes the whole
non-finite range to be missing, and the **smooth** order `∞` is not `ω`: it is the order at which
almost all differential geometry is written, and this file supplies it.

**WHAT MAKES `∞` DIFFERENT FROM `ω`, and it is one lemma.** Mathlib's `contMDiffAt_infty` says
`C^∞` at a point is exactly `C^n` at that point for **every natural** `n`, and `contMDiffOn_infty`
says the same on a set. Nothing of the kind holds at `ω`: an analytic function is not merely one
that is `C^n` for all `n`. So every theorem below is the finite theorem quantified over `n`, and the
same move is unavailable one step further up.

**WHAT HAD TO BE PROVED RATHER THAN SUBSTITUTED, MEASURED BEFORE WRITING** (`ERRATUM 500`'s rule):

* **THE CLASS AT `∞` FROM THE CLASS AT EVERY FINITE ORDER.** `CovariantOrderClass`'s own header
  records that the class has **no monotonicity for free** — that direction is
  `CovariantOrderMono.isLocallyCk_of_le`, proved rather than projected. The **limit** direction is
  `isLocallyCk_infty_of_nat` and nobody had it: the class's single field is a `ContMDiffOn`
  statement, so `contMDiffOn_infty` is the whole proof, with the hypothesis on the section coming
  down from `∞ + 1` by `ContMDiffOn.of_le`.
* **AND THE HYPOTHESIS IS INHABITED AT `∞`.** A theorem whose hypothesis nothing supplies is not
  known to be about anything — the standard `FieldLaplacianInstance` was written to meet.
  `isLocallyCk_infty_leviCivita`: **the Levi-Civita connection of a `C^∞` metric is of class
  `C^∞`**, from `CovariantOrderClass.isLocallyCk_leviCivita` at every finite `k`, the metric-bundle
  hypotheses coming down from `∞` by Mathlib's `IsContMDiffRiemannianBundle.of_le`.
* **THE PLUMBING TO SPELL A `Hom` SECTION AT `∞`.** `contMDiffVectorBundle_infty` is
  `CovariantOrderEndo.contMDiffVectorBundle_add_two'` at `∞` instead of `k + 2`: the total space of
  the `Hom` bundle has to be a manifold before a section of it can be written down, and the order
  at which that is asked is immaterial.
* **AND THE `IsManifold` INSTANCES, WHICH ARE THE PART THAT LOOKS TRIVIAL AND IS NOT.** Every finite
  theorem in the chain takes a literal order — `[IsManifold I (k + 1 + 1 + 1) M]` — and at `∞` those
  are **not** found by instance search from `[IsManifold I ∞ M]`, because `↑j + 1 + 1 + 1 ≤ ∞` is a
  cast fact and not an instance. `isManifold_nat_add_three` and `isManifold_nat_add_four` supply
  them, and `isManifold_infty_add_two` supplies the one at `∞` itself, where `∞ + 1 + 1 = ∞`.

## What is proved

**`isLocallyCk_infty_of_nat`**, **`isLocallyCk_nat`** — the class at `∞` is exactly the class at
every finite order, in both directions.

**`isLocallyC1_of_infty`** — and a `C^∞` connection satisfies the class the whole curvature chain is
written against.

**`contMDiffAt_curvAux_infty`** — **THE CURVATURE OF A `C^∞` CONNECTION IS `C^∞`** at a point, for
`C^∞` fields.

**`contMDiffAt_curvEndo_hom_infty`** — the same as a section of `Hom(TM, TM)`, which is the form the
tensor is quoted in.

**`contMDiffAt_covRiemann_hom_infty`** — **AND SO IS `∇R`**: the covariant derivative of the
curvature, as a `C^∞` section of `Hom(TM, TM)`, for an arbitrary `C^∞` connection.

**`isLocallyCk_infty_leviCivita`** — **THE HYPOTHESIS IS INHABITED**: the Levi-Civita connection of
a `C^∞` metric is of class `C^∞`.

**`contMDiffAt_riemann_hom_infty`**, **`contMDiffAt_covRiemann_hom_infty_leviCivita`** — so the
curvature of a `C^∞` metric and its covariant derivative are `C^∞` sections, the abstract theorems
at the Levi-Civita connection with the class hypothesis discharged.

**`covRiemann_cyclic_endo_infty`** — **THE SECOND BIANCHI IDENTITY AT THE SMOOTH ORDER**, for any
torsion-free `C^∞` connection and `C^∞` fields. The finite theorem carries a `k ≠ 0` side condition
and this one does not: at `∞` the instance at `k = 1` is available, so the condition is discharged
rather than assumed.

## What is NOT here

* **NOTHING AT `ω`, AND THE SEVEN FILES' REASON STANDS.** The analytic order has no *`C^n` for every
  `n`* characterisation, and `CovariantOrderApply`'s fence names the missing neighbourhood
  characterisation. **Not attempted, no cost claimed** (`ERRATUM 246`). What this file changes is
  that the sentence *`k` being a natural number* no longer describes the estate: the range it
  excludes is now `ω` alone.
* **NO `∞` VERSION OF THE TENSORIALITY AND CYCLIC-SUM ALGEBRA.** `CovariantOrderCovTensor`,
  `CovariantOrderCovBundle` and `CovariantOrderCovCyclic` state equations, and their hypotheses are
  regularity at a finite order; each would come down from `∞` the same way this file's Bianchi
  identity does, and **only the Bianchi identity is done**, because it is the one a reader quotes.
  Not attempted for the rest.
* **NOTHING ABOUT A METRIC'S SMOOTHNESS BEYOND WHAT IS ASSUMED.** `isLocallyCk_infty_leviCivita`
  takes `[IsContMDiffRiemannianBundle I ∞ …]`; whether a `C^∞` manifold carries such a metric is not
  asked here, and no such metric is constructed anywhere in this estate.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W5`'s rung 4 needs the heat semigroup and a
  parametrix, at every order.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `E` normed over `ℝ` with
`[FiniteDimensional ℝ E]` — and **no `[CompleteSpace E]`**, which `ERRATUM 503` records as implied
by the binder beside it and which this file therefore does not write; a `ChartedSpace H M` with
model `I`, the literal orders `[IsManifold I 1 M]`, `[IsManifold I 2 M]`, `[IsManifold I 3 M]` and
**`[IsManifold I ∞ M]`**, and `[CurvatureTensor.IsLocallyC1 cov]` on the sections that mention
`curvEndo` or `covRiemann`, which is an existence condition for the object rather than slack
(`OrderBridge`'s finding, quoted in `CovariantOrderClass`). The `∞`-class hypothesis is an explicit
argument `h : IsLocallyCk ∞ cov` rather than an instance, because the finite chain's instances are
at `↑k + 1` and instance search cannot bridge the two.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderInfty

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CovariantOrderClass
open scoped Bundle ContDiff Topology Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [IsManifold I ∞ M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureTensor.contMDiffVectorBundle_two KoszulManifold.finDimTangent

/-! ## 1. At order `∞` every finite order is available -/

theorem le_infty (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] in
theorem isManifold_of_le_infty {n : WithTop ℕ∞} (hn : n ≤ ∞) : IsManifold I n M :=
  IsManifold.of_le hn

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] in
theorem isManifold_infty_add_two : IsManifold I ((∞ : WithTop ℕ∞) + 1 + 1) M :=
  isManifold_of_le_infty (by simp)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] in
theorem isManifold_nat_add_three (j : ℕ) :
    IsManifold I ((j : WithTop ℕ∞) + 1 + 1 + 1) M :=
  isManifold_of_le_infty (by exact_mod_cast le_top)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I 3 M] in
theorem isManifold_nat_add_four (j : ℕ) :
    IsManifold I ((j : WithTop ℕ∞) + 1 + 1 + 1 + 1) M :=
  isManifold_of_le_infty (by exact_mod_cast le_top)

omit [IsManifold I 3 M] in
theorem isLocallyCk_nat (h : IsLocallyCk ∞ cov) (j : ℕ) :
    IsLocallyCk (j : WithTop ℕ∞) cov := by
  haveI := isManifold_infty_add_two (I := I) (M := M)
  exact CovariantOrderMono.isLocallyCk_of_le (n := ∞) (le_infty j) h

theorem isLocallyC1_of_infty (h : IsLocallyCk ∞ cov) : CurvatureTensor.IsLocallyC1 cov := by
  haveI := isManifold_infty_add_two (I := I) (M := M)
  exact CovariantOrderMono.isLocallyC1_of_isLocallyCk (n := ∞) (by exact_mod_cast le_top) h

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M] in
/-- The tangent bundle of a `C^∞` manifold is a `C^∞` vector bundle. `CovariantOrderEndo`'s
`contMDiffVectorBundle_add_two'` is this at order `k + 2`; the order needed to spell a section of
the `Hom` bundle is any order at all, and `∞` is the one this file has. -/
theorem contMDiffVectorBundle_infty :
    ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M → Type _) I := by
  haveI := isManifold_of_le_infty (I := I) (M := M) (n := (∞ : WithTop ℕ∞) + 1) (by simp)
  exact TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_infty

/-! ## 2. The curvature, at order `∞` -/

omit [IsManifold I 3 M] in
theorem contMDiffAt_curvAux_infty (h : IsLocallyCk ∞ cov)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) (hZ : CMDiffAt ∞ (T% Z) x) :
    CMDiffAt ∞ (T% (CurvatureTensorial.curvAux cov X Y Z)) x := by
  rw [contMDiffAt_infty]
  intro j
  haveI := isManifold_nat_add_three (I := I) (M := M) j
  haveI : IsLocallyCk ((j : WithTop ℕ∞) + 1) cov := by
    have hj := isLocallyCk_nat cov h (j + 1)
    simpa using hj
  exact CovariantOrderCurv.contMDiffAt_curvAux_of_isLocallyCk cov
    (hX.of_le (by exact_mod_cast le_top)) (hY.of_le (by exact_mod_cast le_top))
    (hZ.of_le (by exact_mod_cast le_top))

section Endo

variable [CurvatureTensor.IsLocallyC1 cov]

theorem contMDiffAt_curvEndo_hom_infty (h : IsLocallyCk ∞ cov)
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (curvEndo cov y (X y) (Y y))) x := by
  rw [contMDiffAt_infty]
  intro j
  haveI := isManifold_nat_add_three (I := I) (M := M) j
  haveI : IsLocallyCk ((j : WithTop ℕ∞) + 1) cov := by
    have hj := isLocallyCk_nat cov h (j + 1)
    simpa using hj
  exact CovariantOrderEndo.contMDiffAt_curvEndo_hom cov
    (hX.of_le (by exact_mod_cast le_top)) (hY.of_le (by exact_mod_cast le_top))

theorem contMDiffAt_covRiemann_hom_infty (h : IsLocallyCk ∞ cov)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) (hZ : CMDiffAt ∞ (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (CovariantOrderCovDeriv.covRiemann cov Y Z y (X y))) x := by
  rw [contMDiffAt_infty]
  intro j
  haveI := isManifold_nat_add_four (I := I) (M := M) j
  haveI : IsLocallyCk ((j : WithTop ℕ∞) + 1 + 1) cov := by
    have hj := isLocallyCk_nat cov h (j + 1 + 1)
    simpa using hj
  exact CovariantOrderCovField.contMDiffAt_covRiemann_hom_of_isLocallyCk cov
    (hX.of_le (by exact_mod_cast le_top)) (hY.of_le (by exact_mod_cast le_top))
    (hZ.of_le (by exact_mod_cast le_top))

end Endo

/-! ## 3. And the class at `∞` is the class at every finite order, so the hypothesis is inhabited -/

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M] [IsManifold I ∞ M] in
theorem isLocallyCk_infty_of_nat (h : ∀ j : ℕ, IsLocallyCk (j : WithTop ℕ∞) cov) :
    IsLocallyCk (∞ : WithTop ℕ∞) cov := by
  refine ⟨fun u hu => ⟨fun {σ} hσ => ?_⟩⟩
  rw [contMDiffOn_infty]
  intro j
  exact ((h j).on_open u hu).contMDiff (σ := σ) (hσ.of_le (by exact_mod_cast le_top))

section LeviCivita

variable [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

-- The literal-order binders are reached through the instances `leviCivita` needs, so `omit` is
-- rejected here ("cannot omit referenced section variable") and the linter is silenced instead.
set_option linter.unusedSectionVars false in
/-- **THE LEVI-CIVITA CONNECTION OF A `C^∞` METRIC IS OF CLASS `C^∞`**, so §2's hypothesis is
inhabited and its theorems are about something. -/
theorem isLocallyCk_infty_leviCivita :
    IsLocallyCk (∞ : WithTop ℕ∞)
      (KoszulManifold.leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) := by
  refine isLocallyCk_infty_of_nat _ fun j => ?_
  haveI := isManifold_of_le_infty (I := I) (M := M) (n := (j : WithTop ℕ∞) + 1 + 1)
    (by exact_mod_cast le_top)
  haveI : IsContMDiffRiemannianBundle I ((j : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞)
      (show ((j : WithTop ℕ∞) + 1) ≤ ∞ by exact_mod_cast le_top)
  haveI : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := ∞) (show (1 : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)
  exact CovariantOrderClass.isLocallyCk_leviCivita

/-- **AND THE CURVATURE OF A `C^∞` METRIC IS A `C^∞` SECTION OF `Hom(TM, TM)`** — §2's abstract
theorem at the Levi-Civita connection, the hypothesis discharged by `isLocallyCk_infty_leviCivita`
and the two objects identified by `rfl`. -/
theorem contMDiffAt_riemann_hom_infty {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (LeviCivitaRegular.riemann I y (X y) (Y y))) x :=
  contMDiffAt_curvEndo_hom_infty _ (isLocallyCk_infty_leviCivita) hX hY

/-- **AND SO IS ITS COVARIANT DERIVATIVE**, in the direction of a `C^∞` field. -/
theorem contMDiffAt_covRiemann_hom_infty_leviCivita {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) (hZ : CMDiffAt ∞ (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y
        (CovariantOrderCovDeriv.covRiemann KoszulManifold.leviCivita Y Z y (X y))) x :=
  contMDiffAt_covRiemann_hom_infty _ (isLocallyCk_infty_leviCivita) hX hY hZ

end LeviCivita

/-! ## 4. The second Bianchi identity for a `C^∞` connection -/

section Bianchi

variable [CurvatureTensor.IsLocallyC1 cov]

/-- **THE SECOND BIANCHI IDENTITY AT THE SMOOTH ORDER**: for a torsion-free connection of class
`C^∞` and `C^∞` fields, the cyclic sum of `∇R` vanishes. `CovariantOrderBianchiSecond`'s theorem
takes `k : ℕ` with `k ≠ 0` and fields of class `C^(k+2)`; at `∞` every finite order is available, so
`k = 1` does it and the `k ≠ 0` side condition disappears from the statement. -/
theorem covRiemann_cyclic_endo_infty (h : IsLocallyCk ∞ cov) (hzero : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x) (hZ : CMDiffAt ∞ (T% Z) x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (X x)
        + CovariantOrderCovDeriv.covRiemann cov Z X x (Y x)
        + CovariantOrderCovDeriv.covRiemann cov X Y x (Z x) = 0 := by
  haveI := isManifold_nat_add_three (I := I) (M := M) 1
  haveI : IsLocallyCk ((1 : ℕ) + 1 : WithTop ℕ∞) cov := by
    have hj := isLocallyCk_nat cov h 2
    simpa using hj
  have hle : ((1 : ℕ) + 1 + 1 : WithTop ℕ∞) ≤ ∞ := by decide
  exact CovariantOrderBianchiSecond.covRiemann_cyclic_endo (k := 1) cov hzero one_ne_zero
    (hX.of_le hle) (hY.of_le hle) (hZ.of_le hle)

end Bianchi

end CovariantOrderInfty
