import CovariantOrderApply
import CovariantOrderMono
import CurvatureOrder

/-!
# The curvature of ANY connection of class `C^(k+1)` is a `C^k` field

**The first result of the abstract chain, and the first one that is new mathematics rather than
plumbing.** `CurvatureOrder.contMDiffAt_curvAux` makes `y ↦ (∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]}Z)(y)`
a `C^k` field **for the Levi-Civita connection of a `C^(k+2)` metric**, and that restriction was
never about the curvature: it came from the one lemma underneath it, the regularity of `∇_Y Z`,
which was proved from the Koszul formula. Entry 120 made that lemma abstract
(`CovariantOrderApply`, on entry 104's class). **This file spends it**, and the Levi-Civita theorem
comes back as a corollary on the same hypotheses.

**Three applications and two subtractions is the whole proof**, exactly as in the Levi-Civita case:
`∇_X (∇_Y Z)` and `∇_Y (∇_X Z)` at order `k` from the abstract lemma applied twice, `∇_{[X,Y]} Z`
from the bracket's own regularity (`CurvatureOrder.contMDiffAt_mlieBracket_succ`, which is about
`mlieBracket` and not about any connection), and `sub_section` twice. What is not free is the
bookkeeping: the inner derivative is needed at order `k + 1`, so the class is needed at `k + 1`,
and the outer application then needs it at `k` — which is `CovariantOrderMono`'s order-lowering
theorem, entry 105, used here as an instance for the first time.

## What is proved

**`isLocallyCk_down`** — `IsLocallyCk (k+1) cov` gives `IsLocallyCk k cov`. Entry 105 proved the
lowering as a statement about `ContMDiffCovariantDerivativeOn`; this is it as a class instance,
which is the form a proof needs.

**`contMDiffAt_covApply_succ`** — `∇_Y Z` is a `C^(k+1)` section for `Y, Z` of class `C^(k+2)`:
entry 120's theorem at the shifted order, with the `↑(k+1) = ↑k + 1` cast that every order-shifted
statement in this chain carries.

**`contMDiffAt_curvAux_of_isLocallyCk`** — **THE CURVATURE OF ANY `C^(k+1)` CONNECTION IS A
`C^k` FIELD**, for fields of class `C^(k+2)` at the point. No metric, no Koszul formula, no
Levi-Civita. The name carries `_of_isLocallyCk` because `CurvatureOrder`'s theorem has the bare
name and keeps it: the two are the same statement at different generality, the suffix names the
hypothesis that is the difference, and `contMDiffAt_curvAux_leviCivita` below proves that this
one implies that one.

**`contMDiffAt_curvAux_leviCivita`** — **AND `CurvatureOrder`'S THEOREM IS THAT, SPECIALISED**, on
the same hypotheses: `isLocallyCk_leviCivita` at order `k+1` wants a `C^(k+3)` manifold and a
`C^(k+2)` metric, which is what that file wants. Recorded as a theorem rather than as a remark, so
the subsumption is checked.

## What is NOT here

* **THE CURVATURE AS A SECTION OF `Hom(TM, TM)`, ABSTRACTLY.** `CurvatureEndoOrder` and
  `RicciOrder` make the curvature a `C^k` section of the endomorphism bundle and the Ricci
  curvature a `C^k` function, both for the Levi-Civita connection, and both go through the chart's
  local frame. The frame lemma (`LeviCivitaOrder.contMDiffAt_hom_of_localFrame`) is about an
  arbitrary field of endomorphisms and carries no connection, so those two are the next files of
  this rewrite and they are **not attempted here** (`ERRATUM 246`), and they are the
  `UNLOCK_WATCHLIST` residue **(R-REWRITE)** on the curvature-regularity item.
* **NO REPLACEMENT OF `CurvatureOrder.contMDiffAt_curvAux`.** It stays: four files quote it, its
  proof is self-contained where this one routes through a class and an order-lowering instance, and
  `ERRATUM 465`'s rule is to compare what each establishes rather than only its hypotheses.
* **NOTHING ABOUT THE RICCI OR SCALAR CURVATURE**, which need a trace and therefore a metric — a
  general connection has no trace of its curvature in this estate.
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number, for entry 120's reason.
⚠ **`∞` IS REACHED ON 2026-09-11 AND `ω` IS NOT, kept as written** (`ERRATUM 505`):
`CovariantOrderInfty` states this file's results at the **smooth** order — the class at `∞` is the
class at every finite order (`isLocallyCk_infty_of_nat`), the Levi-Civita connection of a `C^∞`
metric is in it, and the curvature, `∇R` and the second Bianchi identity follow. **The sentence is
still true of `ω`**, which has no *`C^n` for every `n`* characterisation, and true of this file,
which proves nothing at either.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`), **and the paragraph is
`binder_scan.py`'s table**: `E` normed over `ℝ` with `[CompleteSpace E]` and
`[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]` and `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]` — and **no
`[IsManifold I 3 M]`**, which `CurvatureOrder` carries and which the linter reported unused in all
four declarations here, so it was removed from the block rather than `omit`ted. **Three of the
four** declarations take `[IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]`; the fourth is the
order-lowering instance itself. Two local instances from `CurvatureOrder` for the manifold's
order shifts, and two more for the metric's inside the Levi-Civita section only.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderCurv

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CovariantOrderClass
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self

/-- **THE ORDER OF THE CLASS CAN BE LOWERED**: `IsLocallyCk (k+1)` gives `IsLocallyCk k`, by
`CovariantOrderMono`'s order-lowering theorem. -/
theorem isLocallyCk_down [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov] :
    IsLocallyCk (k : WithTop ℕ∞) cov :=
  ⟨fun u hu ↦ CovariantOrderMono.contMDiffCovariantDerivativeOn_of_le
    (j := k) (n := (k : WithTop ℕ∞) + 1) le_self_add IsLocallyCk.on_open u hu⟩

attribute [local instance] isLocallyCk_down

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- **`∇_Y Z` IS A `C^(k+1)` SECTION** for `Y, Z` of class `C^(k+2)`, which is
`CovariantOrderApply.contMDiffAt_covApply` at the shifted order. -/
theorem contMDiffAt_covApply_succ [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CMDiffAt ((k : WithTop ℕ∞) + 1) (T% (covApply cov Y Z)) x := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  haveI : IsLocallyCk (((k + 1 : ℕ) : WithTop ℕ∞)) cov := by rw [e]; infer_instance
  have h := CovariantOrderApply.contMDiffAt_covApply (k := k + 1) cov
    (by rw [e]; exact hY.of_le le_self_add) (by rw [e]; exact hZ)
  rw [e] at h
  exact h

/-- **THE CURVATURE OF ANY `C^(k+1)` CONNECTION IS A `C^k` FIELD**: for `X, Y, Z` of class
`C^(k+2)` at the point, `y ↦ (∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z)(y)` is `C^k` at `x`. -/
theorem contMDiffAt_curvAux_of_isLocallyCk [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞) (T% (curvAux cov X Y Z)) x := by
  have hXk : CMDiffAt (k : WithTop ℕ∞) (T% X) x :=
    (hX.of_le (le_self_add : (k : WithTop ℕ∞) + 1 ≤ (k : WithTop ℕ∞) + 1 + 1)).of_le le_self_add
  have hYk : CMDiffAt (k : WithTop ℕ∞) (T% Y) x :=
    (hY.of_le (le_self_add : (k : WithTop ℕ∞) + 1 ≤ (k : WithTop ℕ∞) + 1 + 1)).of_le le_self_add
  have hZ1 : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x := hZ.of_le le_self_add
  have h1 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ cov (covApply cov Y Z) y (X y))) x :=
    CovariantOrderApply.contMDiffAt_covApply cov hXk (contMDiffAt_covApply_succ cov hY hZ)
  have h2 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ cov (covApply cov X Z) y (Y y))) x :=
    CovariantOrderApply.contMDiffAt_covApply cov hYk (contMDiffAt_covApply_succ cov hX hZ)
  have h3 : CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ cov Z y (mlieBracket I X Y y))) x :=
    CovariantOrderApply.contMDiffAt_covApply cov
      ((CurvatureOrder.contMDiffAt_mlieBracket_succ hX hY).of_le le_self_add) hZ1
  exact (h1.sub_section h2).sub_section h3

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self

/-- **AND `CurvatureOrder`'S THEOREM IS THE LEVI-CIVITA CASE OF IT**, on the same hypotheses:
`CovariantOrderClass.isLocallyCk_leviCivita` at order `k + 1` asks for a `C^(k+3)` manifold and a
`C^(k+2)` metric, which is exactly what that file asks. Recorded as a theorem rather than as a
remark (`NormedIsometryOnto`'s precedent), so the subsumption is checked and not asserted. -/
theorem contMDiffAt_curvAux_leviCivita {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞)
      (T% (curvAux (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
        X Y Z)) x := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  haveI : IsLocallyCk ((k : WithTop ℕ∞) + 1)
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) := by
    rw [← e]
    exact CovariantOrderClass.isLocallyCk_leviCivita (k := k + 1)
  exact contMDiffAt_curvAux_of_isLocallyCk _ hX hY hZ

end LeviCivita

end CovariantOrderCurv
