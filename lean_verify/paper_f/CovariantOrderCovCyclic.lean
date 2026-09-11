import CovariantOrderCovDeriv
import CurvatureCovCyclic

/-!
# The corrections of the cyclic sum, for any TORSION-FREE connection of class `C^(k+1)`

**`ERRATUM 500`'s unit, and the erratum is why the hypothesis is here.** Entry 33 named the next
theorem as the second Bianchi identity *for an arbitrary connection*. **That is false**, and the
file this one generalises says so in its own *What is NOT here*: *nothing for a connection with
torsion; for a connection with torsion the cyclic sum is an expression in the torsion and its
derivative*. `CurvatureCovCyclic` discharges torsion-freeness three times with
`KoszulManifold.leviCivita_torsion`. So the reachable statement is the identity for any
**torsion-free** connection, with `cov.torsion = 0` as a hypothesis where the metric's version gets
it for free — and that is still weaker than *is the Levi-Civita connection of a metric*, since the
Levi-Civita connection is the unique torsion-free connection **compatible with a given metric** and
a torsion-free connection need not come from a metric at all. **No witness of a torsion-free
non-metric connection is exhibited here**, which a claim of a *strictly* wider class would need
(`ERRATUM 246`); what is claimed is that this hypothesis is weaker, which is visible in the two
statements.

**WHERE TORSION-FREENESS IS USED, EXACTLY.** In `riemann_corrections_cyclic` and nowhere else: each
of the six corrections pairs with the one from the next cyclic term, skew-symmetry turns the pair
into a difference of covariant derivatives in the first slot, and torsion-freeness turns that
difference into the Lie bracket — Mathlib's `CovariantDerivative.torsion_eq_zero_iff`, three times.
Every other step is algebra that never mentions a metric or a torsion.

## What is proved

**`curvEndo_sub_left`** — the curvature of any connection is additive in its first slot on a
difference, from `curvEndo_add_left` and `curvEndo_smul_left` at `−1`. The general form of
`CurvatureCovCyclic.riemann_sub_left`.

**`riemann_corrections_cyclic`** — **THE SIX CORRECTION TERMS OF THE CYCLIC SUM ARE THREE
CURVATURES ON BRACKETS**, for any connection whose torsion vanishes. `X`, `Y`, `Z` differentiable at
the point is all the regularity used.

**`covRiemann_cyclic_eq`** — **AND SO THE CYCLIC SUM OF `∇R` HAS NO CORRECTIONS IN IT**: it is the
cyclic sum of the induced derivative of the curvature field, minus the three curvatures on the
brackets.

**`covRiemann_cyclic_eq_zero_iff`** — **WHAT THE SECOND BIANCHI IDENTITY IS EQUIVALENT TO, WITH THE
CORRECTIONS REMOVED.** **Neither side is proved here**; what is proved is that they are one
question — as in the file being generalised, and for the same reason.

**`riemann_corrections_cyclic_leviCivita`** — **AND `CurvatureCovCyclic`'S CORRECTIONS LEMMA IS
THIS ONE AT A TORSION-FREE CONNECTION, ON BINDERS THAT AGREE ONE FOR ONE** (`#check` on both), the
torsion hypothesis discharged by `KoszulManifold.leviCivita_torsion` exactly as that file discharges
it. The sixth checked subsumption in seven units; recorded by hand because no mode here sees a
duplicate under a different name.

## What is NOT here

* **NO SECOND BIANCHI IDENTITY, ABSTRACT OR OTHERWISE.** This file removes the corrections and says
  what the identity is *equivalent to*; proving it needs the third-derivative expansion and the
  cyclic Jacobi identity, which is `CurvatureBianchiSecond`'s eleven declarations — and of those,
  the Jacobi lemma **does not lift by import**: `#check` shows it carries `[RiemannianBundle …]` in
  a statement purely about Lie brackets, the fourth instance of that pattern in this campaign. So
  the abstract identity is one file further out. **Not attempted, no cost claimed**
  (`ERRATUM 246`).
* **NOTHING FOR A CONNECTION WITH TORSION**, which is the point of the hypothesis: for such a
  connection the cyclic sum is an expression in the torsion and its derivative, and nothing about
  it is stated here or anywhere in this estate.
* **NO TRACE, NO DIVERGENCE**: a trace needs a metric.
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number.
⚠ **`∞` IS REACHED ON 2026-09-11 AND `ω` IS NOT, kept as written** (`ERRATUM 505`):
`CovariantOrderInfty` states this file's results at the **smooth** order — the class at `∞` is the
class at every finite order (`isLocallyCk_infty_of_nat`), the Levi-Civita connection of a `C^∞`
metric is in it, and the curvature, `∇R` and the second Bianchi identity follow. **The sentence is
still true of `ω`**, which has no *`C^n` for every `n`* characterisation, and true of this file,
which proves nothing at either.

**No wall moves. No published tag moves.**

**THE NAMES COLLIDE WITH `CurvatureCovCyclic`'S ON PURPOSE**, as in entries 124, 126 and 127, and
for the same machine-checked reason: `CovariantOrderCovDeriv.covRiemann_eq` identifies the two `∇R`s
by `rfl`. Recorded in `newnames_accepted.txt`.

**THE HYPOTHESES, READ FROM `#check` AND NOT FROM THE SECTION HEADER** (`ERRATUM 455`, and the
difference matters here): `E` normed over `ℝ` with `[CompleteSpace E]` and `[FiniteDimensional ℝ
E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`, `[IsManifold
I 3 M]`, `[CurvatureTensor.IsLocallyC1 cov]`, and **`(hzero : cov.torsion = 0)` on the three
theorems that use it**. Counted over the five declarations: **four** take `[IsLocallyC1 cov]`,
**three** take the torsion hypothesis, **one** takes a metric — the subsumption, which takes no
connection — and **none takes `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`**, which the
section declares and every declaration drops, nor the order class `IsLocallyCk`, because **this
file differentiates nothing: it rearranges.** The comparison with `CurvatureCovCyclic` is therefore
at the signature and not at the section: that file's section asks for a `C^(k+2)` metric and a
`RiemannianBundle`, and its corrections lemma in fact takes only the `RiemannianBundle` and the
companion at literal order `2` — so what this file removes is those two, and what it adds is the
torsion hypothesis the metric was there to supply.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderCovCyclic

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

omit [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M] in
set_option linter.unusedSectionVars false in
-- The linter names `[IsManifold I 1 M]` and `[IsManifold I 2 M]`, and `omit`ting them is rejected
-- by the elaborator — *cannot omit referenced section variable* — because both are reached through
-- the instances `curvEndo` needs to be NAMED. `CurvatureCovCyclic.riemann_sub_left` carries the
-- same option and says the same of `leviCivita`; tried here and the rejection is identical, so
-- that note generalises with the file.
/-- The curvature of any connection is additive in its first slot on a difference:
`curvEndo_add_left` with `curvEndo_smul_left` at `−1`. -/
theorem curvEndo_sub_left (x : M) (a b c : TangentSpace I x) :
    curvEndo cov x (a - b) c = curvEndo cov x a c - curvEndo cov x b c := by
  have hadd : curvEndo cov x (a + (-1 : ℝ) • b) c
      = curvEndo cov x a c + curvEndo cov x ((-1 : ℝ) • b) c :=
    curvEndo_add_left cov x a ((-1 : ℝ) • b) c
  have hsmul : curvEndo cov x ((-1 : ℝ) • b) c = (-1 : ℝ) • curvEndo cov x b c :=
    curvEndo_smul_left cov x (-1 : ℝ) b c
  have hb : a - b = a + (-1 : ℝ) • b := by module
  rw [hb, hadd, hsmul]
  module

omit [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M] in
/-- **THE SIX CORRECTION TERMS OF THE CYCLIC SUM ARE THREE CURVATURES ON BRACKETS**, for any
connection whose torsion vanishes. Each correction pairs with the one from the next cyclic term,
skew-symmetry turns the pair into a difference of covariant derivatives in the first slot, and
**torsion-freeness** turns that into the bracket. `X`, `Y`, `Z` differentiable at the point is all
the regularity used. -/
theorem riemann_corrections_cyclic (hzero : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    curvEndo cov x (cov Y x (X x)) (Z x) + curvEndo cov x (Y x) (cov Z x (X x))
      + (curvEndo cov x (cov Z x (Y x)) (X x) + curvEndo cov x (Z x) (cov X x (Y x)))
      + (curvEndo cov x (cov X x (Z x)) (Y x) + curvEndo cov x (X x) (cov Y x (Z x)))
      = curvEndo cov x (mlieBracket I X Y x) (Z x)
        + curvEndo cov x (mlieBracket I Y Z x) (X x)
        + curvEndo cov x (mlieBracket I Z X x) (Y x) := by
  have t1 : mlieBracket I X Y x = cov Y x (X x) - cov X x (Y x) :=
    ((CovariantDerivative.torsion_eq_zero_iff _).mp hzero hX hY).symm
  have t2 : mlieBracket I Y Z x = cov Z x (Y x) - cov Y x (Z x) :=
    ((CovariantDerivative.torsion_eq_zero_iff _).mp hzero hY hZ).symm
  have t3 : mlieBracket I Z X x = cov X x (Z x) - cov Z x (X x) :=
    ((CovariantDerivative.torsion_eq_zero_iff _).mp hzero hZ hX).symm
  rw [t1, t2, t3, curvEndo_sub_left, curvEndo_sub_left, curvEndo_sub_left]
  have s1 : curvEndo cov x (Y x) (cov Z x (X x))
      = - curvEndo cov x (cov Z x (X x)) (Y x) :=
    curvEndo_swap cov x (Y x) (cov Z x (X x))
  have s2 : curvEndo cov x (Z x) (cov X x (Y x))
      = - curvEndo cov x (cov X x (Y x)) (Z x) :=
    curvEndo_swap cov x (Z x) (cov X x (Y x))
  have s3 : curvEndo cov x (X x) (cov Y x (Z x))
      = - curvEndo cov x (cov Y x (Z x)) (X x) :=
    curvEndo_swap cov x (X x) (cov Y x (Z x))
  rw [s1, s2, s3]
  abel

/-- **AND SO THE CYCLIC SUM OF `∇R` HAS NO CORRECTION TERMS IN IT**: it is the cyclic sum of the
induced derivative of the curvature field, minus the three curvatures on the brackets. -/
theorem covRiemann_cyclic_eq (hzero : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (X x)
        + CovariantOrderCovDeriv.covRiemann cov Z X x (Y x)
        + CovariantOrderCovDeriv.covRiemann cov X Y x (Z x)
      = (HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (Y y) (Z y)) x (X x)
          + HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (Z y) (X y)) x (Y x)
          + HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (X y) (Y y)) x (Z x))
        - (curvEndo cov x (mlieBracket I X Y x) (Z x)
          + curvEndo cov x (mlieBracket I Y Z x) (X x)
          + curvEndo cov x (mlieBracket I Z X x) (Y x)) := by
  rw [← riemann_corrections_cyclic cov hzero hX hY hZ]
  simp only [CovariantOrderCovDeriv.covRiemann]
  abel

/-- **WHAT THE SECOND BIANCHI IDENTITY IS EQUIVALENT TO, WITH THE CORRECTIONS REMOVED.** The cyclic
sum of `∇R` vanishes at the point exactly when the cyclic sum of the induced derivative of the
curvature field equals the cyclic sum of the curvature on the brackets. **Neither side is proved**;
what is proved is that they are one question. -/
theorem covRiemann_cyclic_eq_zero_iff (hzero : cov.torsion = 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (X x)
          + CovariantOrderCovDeriv.covRiemann cov Z X x (Y x)
          + CovariantOrderCovDeriv.covRiemann cov X Y x (Z x) = 0
      ↔ HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (Y y) (Z y)) x (X x)
          + HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (Z y) (X y)) x (Y x)
          + HomCovariant.homCovFun cov (fun y ↦ curvEndo cov y (X y) (Y y)) x (Z x)
        = curvEndo cov x (mlieBracket I X Y x) (Z x)
          + curvEndo cov x (mlieBracket I Y Z x) (X x)
          + curvEndo cov x (mlieBracket I Z X x) (Y x) := by
  rw [covRiemann_cyclic_eq cov hzero hX hY hZ, sub_eq_zero]

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- **AND `CurvatureCovCyclic`'S CORRECTIONS LEMMA IS THIS ONE AT A TORSION-FREE CONNECTION** — the
hypothesis discharged by `KoszulManifold.leviCivita_torsion`, exactly as that file discharges it,
and the two curvatures identified because `LeviCivitaRegular.riemann` is an `abbrev` for
`curvEndo leviCivita`. A theorem rather than a remark so the subsumption is checked. -/
theorem riemann_corrections_cyclic_leviCivita {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    LeviCivitaRegular.riemann I x (leviCivita Y x (X x)) (Z x)
        + LeviCivitaRegular.riemann I x (Y x) (leviCivita Z x (X x))
      + (LeviCivitaRegular.riemann I x (leviCivita Z x (Y x)) (X x)
        + LeviCivitaRegular.riemann I x (Z x) (leviCivita X x (Y x)))
      + (LeviCivitaRegular.riemann I x (leviCivita X x (Z x)) (Y x)
        + LeviCivitaRegular.riemann I x (X x) (leviCivita Y x (Z x)))
      = LeviCivitaRegular.riemann I x (mlieBracket I X Y x) (Z x)
        + LeviCivitaRegular.riemann I x (mlieBracket I Y Z x) (X x)
        + LeviCivitaRegular.riemann I x (mlieBracket I Z X x) (Y x) :=
  riemann_corrections_cyclic _ KoszulManifold.leviCivita_torsion hX hY hZ

end LeviCivita

end CovariantOrderCovCyclic
