import CurvatureCovDeriv

/-!
# The correction terms of `∇R` in closed form, and what the second Bianchi identity reduces to

**The cyclic sum of the corrections is a sum of brackets, and after that the identity is one
statement about third derivatives.** `CurvatureCovDeriv` defines
`(∇_u R)(Y, Z) = (∇_u A) − R(∇_u Y, Z) − R(Y, ∇_u Z)` with `A y = R(Y y, Z y)`, and
`CurvatureCovTensor` makes it a tensor in `Y` and `Z`. The `UNLOCK_WATCHLIST` item for the second
Bianchi identity lists three steps and calls the third — **the cyclic sum** — what is left. This
file does not prove it. It removes the correction terms from it: summed cyclically over three
differentiable fields, the six corrections are exactly the three curvatures on the brackets,

`R(∇_X Y, Z) + R(Y, ∇_X Z) + (cyc) = R([X, Y], Z) + R([Y, Z], X) + R([Z, X], Y)`,

so that **the identity `∑_cyc (∇_X R)(Y, Z) = 0` is equivalent to
`∑_cyc ∇_X (R(Y, Z)) = ∑_cyc R([X, Y], Z)`** (`covRiemann_cyclic_eq_zero_iff`), an equation in
which no covariant derivative of a direction field appears.

**And the equation that is left is the identity as the literature states it for vector fields** —
`∑_cyc [∇_X (R(Y, Z)) − R([X, Y], Z)] = 0`, the vanishing of the exterior covariant derivative of
the curvature — so the reduction lands on the textbook statement and not beside it. **No exterior
covariant derivative is defined here**, in this estate or in the pinned library, and that sentence
is a remark about where the target sits and not a claim that the object exists.

**The mechanism is torsion-freeness and skew-symmetry, and nothing else.** Each correction pairs
with the correction from the *next* cyclic term: `R(∇_X Y, Z)` with `R(Z, ∇_Y X)`, which
`CurvatureTensor.curvEndo_swap` turns into `−R(∇_Y X, Z)`, so the pair is
`R(∇_X Y − ∇_Y X, Z)` by additivity in the first slot, and `∇_X Y − ∇_Y X` is `[X, Y]` because the
Levi-Civita connection is torsion-free (`KoszulManifold.leviCivita_torsion`, through Mathlib's
`CovariantDerivative.torsion_eq_zero_iff`). The three pairings are the whole proof, and the
hypotheses are three differentiabilities and nothing else: `X`, `Y`, `Z` **differentiable** at the
point, with **no lower bound on `k`** — where all six theorems of `CurvatureCovDeriv` take
`k ≠ 0`, and four of `CurvatureCovTensor`'s eight declarations do, because the induced connection
needs an argument it can differentiate. Nothing here differentiates anything twice, which is why
the bound is absent rather than suppressed.

## What is proved

**`riemann_sub_left`** — the curvature is additive in its first slot on a *difference*, which is
`CurvatureTensor.curvEndo_add_left` and `curvEndo_smul_left` at `−1` and is not stated anywhere.

**`riemann_corrections_cyclic`** — **THE SIX CORRECTIONS ARE THREE BRACKETS**, the display above,
for `X`, `Y`, `Z` differentiable at the point. This is the file's content.

**`covRiemann_cyclic_eq`** — and so the cyclic sum of `∇R` is the cyclic sum of the induced
derivative of the curvature field **minus** the three brackets. A definitional unfolding and
`riemann_corrections_cyclic`.

**`covRiemann_cyclic_eq_zero_iff`** — **WHAT THE SECOND BIANCHI IDENTITY IS EQUIVALENT TO**:
`∑_cyc (∇_X R)(Y, Z) = 0` iff `∑_cyc ∇_X (R(Y, Z)) = ∑_cyc R([X, Y], Z)`. Both sides of that
equivalence are unproved; what is proved is that they are the same question.

## What is NOT here

* **THE SECOND BIANCHI IDENTITY IS NOT PROVED, AND NOTHING HERE MAKES IT LIKELY.** The remaining
  statement is the classical computation: expand `R(Y, Z)W = ∇_Y ∇_Z W − ∇_Z ∇_Y W − ∇_{[Y,Z]} W`
  inside `∇_X`, sum cyclically, and cancel against the bracket terms using the Jacobi identity of
  `mlieBracket`. It involves **third** covariant derivatives of a section where
  `CurvatureBianchi`'s first identity involved second ones, and that file spent seven declarations
  on the second-order case. **Not attempted here, no cost claimed** (`ERRATUM 246`), and the
  watchlist item stays open on step (3).
* **NO NORMAL COORDINATES, AND THE PINNED LIBRARY HAS NONE EITHER.** The textbook one-line proof
  evaluates at the centre of a normal coordinate system, where the connection coefficients vanish.
  Neither this estate nor the pinned Mathlib has normal coordinates, an exponential map or a
  geodesic: `AlgebraicCurvature`'s header records the same search over `paper_f`, and in Mathlib
  the only occurrences of *geodesic* are about quivers (`Combinatorics/Quiver/Arborescence`,
  `GroupTheory/FreeGroup/NielsenSchreier`) with nothing in `Geometry/` at all. So that route is
  not available, and it is not costed.
* **NOTHING ABOUT THE CONTRACTED IDENTITY**, so nothing about the divergence of the Einstein
  tensor: that needs a trace, which contraction is meant is the author's decision
  (`ASSUMPTIONS 56`), and neither is on any item.
* **NO WALL MOVES.** `W5`'s rung 4 needs the heat semigroup and a parametrix, which `WALLS`
  §W5.1 §4 prices as research; the second Bianchi identity is not on that path and neither is
  this reduction of it.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`), **and the paragraph is
`binder_scan.py`'s table**: the section context is `CurvatureCovDeriv`'s, unchanged and unrelaxed —
a normed space `E` over `ℝ` with `[CompleteSpace E]` and `[FiniteDimensional ℝ E]`, a
`ChartedSpace H M` with model `I`, the four `IsManifold` instances, `[RiemannianBundle …]` and the
two `IsContMDiffRiemannianBundle` instances, with the same six local instances. Of the four
declarations, **three take all three differentiabilities** and `riemann_sub_left` takes none;
**`k ≠ 0` appears nowhere in the file**, which is the one respect in which these hypotheses are
lighter than the chain's. One `set_option linter.unusedSectionVars false`, scoped to
`riemann_sub_left` and carrying its reason: the linter names two `IsManifold` binders and the
`omit` it suggests is **rejected by the elaborator**, both being reached through the instances
`leviCivita` needs in order to be named at all — `CurvatureCovTensor.riemann_zero_left` carries the
same option for the same reason, and the suggestion was tried before the option was set.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureCovCyclic

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

set_option linter.unusedSectionVars false in
-- the linter names `[IsManifold I 1 M]` and `[IsManifold I 2 M]`, and `omit`ting them is rejected
-- by the elaborator: both are referenced through the instances that `leviCivita` needs to be NAMED
-- (`CurvatureCovTensor.riemann_zero_left` carries the same option for the same reason)
/-- The curvature of the Levi-Civita connection is additive in its first slot on a difference:
`CurvatureTensor.curvEndo_add_left` with `curvEndo_smul_left` at `−1`. -/
theorem riemann_sub_left (x : M) (a b c : TangentSpace I x) :
    LeviCivitaRegular.riemann I x (a - b) c
      = LeviCivitaRegular.riemann I x a c - LeviCivitaRegular.riemann I x b c := by
  have hadd : LeviCivitaRegular.riemann I x (a + (-1 : ℝ) • b) c
      = LeviCivitaRegular.riemann I x a c
        + LeviCivitaRegular.riemann I x ((-1 : ℝ) • b) c :=
    CurvatureTensor.curvEndo_add_left _ x a ((-1 : ℝ) • b) c
  have hsmul : LeviCivitaRegular.riemann I x ((-1 : ℝ) • b) c
      = (-1 : ℝ) • LeviCivitaRegular.riemann I x b c :=
    CurvatureTensor.curvEndo_smul_left _ x (-1 : ℝ) b c
  have hb : a - b = a + (-1 : ℝ) • b := by module
  rw [hb, hadd, hsmul]
  module

/-- **THE SIX CORRECTION TERMS OF THE CYCLIC SUM ARE THREE CURVATURES ON BRACKETS.** Each
correction pairs with the one from the next cyclic term, skew-symmetry turns the pair into a
difference of covariant derivatives in the first slot, and torsion-freeness turns that into the
bracket. `X`, `Y`, `Z` differentiable at the point is all that is used. -/
theorem riemann_corrections_cyclic {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    LeviCivitaRegular.riemann I x (leviCivita Y x (X x)) (Z x)
        + LeviCivitaRegular.riemann I x (Y x) (leviCivita Z x (X x))
      + (LeviCivitaRegular.riemann I x (leviCivita Z x (Y x)) (X x)
        + LeviCivitaRegular.riemann I x (Z x) (leviCivita X x (Y x)))
      + (LeviCivitaRegular.riemann I x (leviCivita X x (Z x)) (Y x)
        + LeviCivitaRegular.riemann I x (X x) (leviCivita Y x (Z x)))
      = LeviCivitaRegular.riemann I x (mlieBracket I X Y x) (Z x)
        + LeviCivitaRegular.riemann I x (mlieBracket I Y Z x) (X x)
        + LeviCivitaRegular.riemann I x (mlieBracket I Z X x) (Y x) := by
  have hzero : (leviCivita (I := I) (M := M)).torsion = 0 :=
    KoszulManifold.leviCivita_torsion
  have t1 : mlieBracket I X Y x = leviCivita Y x (X x) - leviCivita X x (Y x) :=
    ((CovariantDerivative.torsion_eq_zero_iff _).mp hzero hX hY).symm
  have t2 : mlieBracket I Y Z x = leviCivita Z x (Y x) - leviCivita Y x (Z x) :=
    ((CovariantDerivative.torsion_eq_zero_iff _).mp hzero hY hZ).symm
  have t3 : mlieBracket I Z X x = leviCivita X x (Z x) - leviCivita Z x (X x) :=
    ((CovariantDerivative.torsion_eq_zero_iff _).mp hzero hZ hX).symm
  rw [t1, t2, t3, riemann_sub_left, riemann_sub_left, riemann_sub_left]
  have s1 : LeviCivitaRegular.riemann I x (Y x) (leviCivita Z x (X x))
      = - LeviCivitaRegular.riemann I x (leviCivita Z x (X x)) (Y x) :=
    LeviCivitaRegular.riemann_swap (I := I) x (Y x) (leviCivita Z x (X x))
  have s2 : LeviCivitaRegular.riemann I x (Z x) (leviCivita X x (Y x))
      = - LeviCivitaRegular.riemann I x (leviCivita X x (Y x)) (Z x) :=
    LeviCivitaRegular.riemann_swap (I := I) x (Z x) (leviCivita X x (Y x))
  have s3 : LeviCivitaRegular.riemann I x (X x) (leviCivita Y x (Z x))
      = - LeviCivitaRegular.riemann I x (leviCivita Y x (Z x)) (X x) :=
    LeviCivitaRegular.riemann_swap (I := I) x (X x) (leviCivita Y x (Z x))
  rw [s1, s2, s3]
  abel

/-- **AND SO THE CYCLIC SUM OF `∇R` HAS NO CORRECTION TERMS IN IT**: it is the cyclic sum of the
induced derivative of the curvature field, minus the three curvatures on the brackets. -/
theorem covRiemann_cyclic_eq {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    CurvatureCovDeriv.covRiemann Y Z x (X x) + CurvatureCovDeriv.covRiemann Z X x (Y x)
        + CurvatureCovDeriv.covRiemann X Y x (Z x)
      = (HomCovariant.homCovFun
            (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
            (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y)) x (X x)
          + HomCovariant.homCovFun
            (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
            (fun y ↦ LeviCivitaRegular.riemann I y (Z y) (X y)) x (Y x)
          + HomCovariant.homCovFun
            (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
            (fun y ↦ LeviCivitaRegular.riemann I y (X y) (Y y)) x (Z x))
        - (LeviCivitaRegular.riemann I x (mlieBracket I X Y x) (Z x)
          + LeviCivitaRegular.riemann I x (mlieBracket I Y Z x) (X x)
          + LeviCivitaRegular.riemann I x (mlieBracket I Z X x) (Y x)) := by
  rw [← riemann_corrections_cyclic hX hY hZ]
  simp only [CurvatureCovDeriv.covRiemann]
  abel

/-- **WHAT THE SECOND BIANCHI IDENTITY IS EQUIVALENT TO, WITH THE CORRECTIONS REMOVED.** The
cyclic sum of `∇R` vanishes at the point exactly when the cyclic sum of the induced derivative of
the curvature field equals the cyclic sum of the curvature on the brackets. **Neither side is
proved**; what is proved is that they are one question. -/
theorem covRiemann_cyclic_eq_zero_iff {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    CurvatureCovDeriv.covRiemann Y Z x (X x) + CurvatureCovDeriv.covRiemann Z X x (Y x)
          + CurvatureCovDeriv.covRiemann X Y x (Z x) = 0
      ↔ HomCovariant.homCovFun
            (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
            (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y)) x (X x)
          + HomCovariant.homCovFun
            (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
            (fun y ↦ LeviCivitaRegular.riemann I y (Z y) (X y)) x (Y x)
          + HomCovariant.homCovFun
            (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
            (fun y ↦ LeviCivitaRegular.riemann I y (X y) (Y y)) x (Z x)
        = LeviCivitaRegular.riemann I x (mlieBracket I X Y x) (Z x)
          + LeviCivitaRegular.riemann I x (mlieBracket I Y Z x) (X x)
          + LeviCivitaRegular.riemann I x (mlieBracket I Z X x) (Y x) := by
  rw [covRiemann_cyclic_eq hX hY hZ, sub_eq_zero]

end CurvatureCovCyclic
