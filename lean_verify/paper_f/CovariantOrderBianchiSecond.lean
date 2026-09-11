import CovariantOrderCovCyclic
import CurvatureBianchiSecond

/-!
# The second Bianchi identity for any TORSION-FREE connection of class `C^(k+1)`

**The last file of the re-definition `ERRATUM 498` priced, on the target `ERRATUM 500` corrected.**
`CurvatureBianchiSecond` proves `(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0` for the
Levi-Civita connection of a metric; entry 128 removed the metric from the corrections lemma at the
cost of an explicit `cov.torsion = 0`, and this file spends that on the identity itself.

**WHAT HAD TO BE PROVED RATHER THAN SUBSTITUTED, MEASURED WITH `#check` BEFORE WRITING** — which is
`ERRATUM 500`'s rule, and it found one blocker and cleared two suspects:

* **`mlieBracket_cyclic_jacobi'`** — `CurvatureBianchiSecond`'s Jacobi identity **cannot be
  imported**: its statement is purely about Lie brackets and it carries
  `[Bundle.RiemannianBundle …]`, read off the signature and not its `omit` line, which drops two
  other binders and keeps that one. Fourth instance of that pattern in this campaign. Restated here
  with no metric in the context, by the same route: the pinned library's Leibniz form plus two
  swaps.
* **`CurvatureBianchi.mdiffAt_mlieBracket` and `CurvatureTensor.mdiffAt_covApply'` are clean** —
  `#check` shows no metric on either, so both are imported rather than restated. Suspecting them was
  free; assuming them would not have been.

**AND ONE INPUT WAS ALREADY THERE**: `cmdiffAt_covApply_succ` — `∇_Z W` at order `k + 1` for
`C^(k+2)` fields — is entry 121's `CovariantOrderCurv.contMDiffAt_covApply_succ`, so the metric
version's `isMetric_shift1` has **no counterpart here and needs none**: the class is taken at
`k + 1` directly, where the metric had to be shifted into the `↑(k+1) + 1` spelling.

## What is proved

**`riemann_apply_eventually`** — `R(Y, Z)W = ∇_Y ∇_Z W − ∇_Z ∇_Y W − ∇_{[Y,Z]} W` as sections
**near** the point, which is what applying a further covariant derivative to it needs.

**`cov_sub`** — the connection distributes over a difference of differentiable sections. Mathlib's
`IsCovariantDerivativeOn` carries `add` and `smul_const` and no `sub`.

**`mdiffAt_covApply_covApply`** — the second covariant derivative is differentiable at the point.

**`cov_riemann_section`** — **THE THIRD-DERIVATIVE EXPANSION**: `∇_u (R(Y, Z)W)` is
`∇_u ∇_Y ∇_Z W − ∇_u ∇_Z ∇_Y W − ∇_u ∇_{[Y,Z]} W`. This is the analytic step the second Bianchi
identity needs and the first identity did not.

**`mlieBracket_cyclic_jacobi'`** — the Jacobi identity in cyclic form, metric-free.

**`covRiemann_cyclic`** — **THE SECOND BIANCHI IDENTITY**, evaluated on a fourth field, for any
torsion-free connection of class `C^(k+1)` and fields of class `C^(k+2)` at the point with
`k ≠ 0`.

**`covRiemann_cyclic_apply`**, **`covRiemann_cyclic_endo`** — the same on a tangent vector, and as
an identity of endomorphisms in `Hom(TM, TM)`. **The form to quote.**

**`covRiemann_cyclic_endo_leviCivita`** — **AND `CurvatureBianchiSecond`'S IDENTITY IS THIS ONE AT A
TORSION-FREE CONNECTION**, the hypothesis discharged by `KoszulManifold.leviCivita_torsion`. The
seventh checked subsumption in eight units.

## What is NOT here

* **NOTHING FOR A CONNECTION WITH TORSION.** For such a connection the cyclic sum is an expression
  in the torsion and its derivative, and nothing about it is stated here or anywhere in this estate
  — the same fence the metric version carries, with the hypothesis now visible in the statement
  rather than supplied by the metric. **Not attempted, no cost claimed** (`ERRATUM 246`).
* **NO CONTRACTED IDENTITY, NO DIVERGENCE.** Both need a trace of this object, a trace needs a
  metric, and which contraction is meant is the author's decision (`ASSUMPTIONS 56`).
* **NOTHING ON THE BUNDLED `∇R`.** Entry 127's `covRiemannHom` fixes the direction; the cyclic
  identity for three arbitrary tangent vectors is `covRiemann_cyclic_endo` composed with entry
  127's `covRiemannAt_eq`, and that composition is **not made here**.
* **NOTHING AT `k = 0`**, and **nothing at the analytic order**.
* **NO NORMAL COORDINATES**, as in the file generalised: the textbook one-line proof evaluates at
  the centre of a normal coordinate system, and neither this estate nor the pinned library has one.

**No wall moves. No published tag moves.**

**THE NAMES COLLIDE WITH `CurvatureBianchiSecond`'S ON PURPOSE**, as in entries 124 and 126–128, and
for the same machine-checked reason: `CovariantOrderCovDeriv.covRiemann_eq` identifies the two `∇R`s
by `rfl`. Recorded in `newnames_accepted.txt`.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `E` normed over `ℝ` with `[CompleteSpace E]`
and `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, the literal manifold orders,
`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`, `[CurvatureTensor.IsLocallyC1 cov]`,
`[CovariantOrderClass.IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]`, `(hzero : cov.torsion = 0)` and
`k ≠ 0` on the identity itself — **no metric at any order**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderBianchiSecond

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
  CovariantOrderEndo.contMDiffVectorBundle_add_two'

/-! ## 1. The Jacobi identity, metric-free -/

omit [FiniteDimensional ℝ E] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [CurvatureTensor.IsLocallyC1 cov] in
/-- **THE JACOBI IDENTITY IN CYCLIC FORM**: `[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0`, with no metric
in the context. `CurvatureBianchiSecond.mlieBracket_cyclic_jacobi` is this statement and **cannot be
imported**: `#check` shows it carrying `[Bundle.RiemannianBundle …]` in a statement purely about Lie
brackets. The pinned library carries the Leibniz form `[U,[V,W]] = [[U,V],W] + [V,[U,W]]` and not
this one. -/
theorem mlieBracket_cyclic_jacobi' {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    mlieBracket I X (mlieBracket I Y Z) x + mlieBracket I Y (mlieBracket I Z X) x
      + mlieBracket I Z (mlieBracket I X Y) x = 0 := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hX2 : CMDiffAt (minSmoothness ℝ 2) (T% X) x := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact hX
  have hY2 : CMDiffAt (minSmoothness ℝ 2) (T% Y) x := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact hY
  have hZ2 : CMDiffAt (minSmoothness ℝ 2) (T% Z) x := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact hZ
  have j := leibniz_identity_mlieBracket_apply (I := I) hX2 hY2 hZ2
  have s1 : mlieBracket I (mlieBracket I X Y) Z x = - mlieBracket I Z (mlieBracket I X Y) x :=
    mlieBracket_swap_apply
  have s2 : mlieBracket I Y (mlieBracket I X Z) x
      = - mlieBracket I Y (mlieBracket I Z X) x := by
    rw [mlieBracket_swap (V := X) (W := Z)]
    have hneg : mlieBracket I Y (-mlieBracket I Z X) x
        = - mlieBracket I Y (mlieBracket I Z X) x := by
      have h := mlieBracket_const_smul_right (I := I) (V := Y) (W := mlieBracket I Z X)
        (c := (-1 : ℝ)) (CurvatureBianchi.mdiffAt_mlieBracket hZ hX)
      simpa using h
    rw [hneg]
  rw [j, s1, s2]
  abel

/-! ## 2. The third-derivative expansion -/

/-- `R(Y, Z)W = ∇_Y ∇_Z W − ∇_Z ∇_Y W − ∇_{[Y,Z]} W` as sections **near** the point, which is what
applying a further covariant derivative to it needs. -/
theorem riemann_apply_eventually {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) (hW : CMDiffAt 2 (T% W) x) :
    ∀ᶠ y in 𝓝 x, curvEndo cov y (Y y) (Z y) (W y)
      = (covApply cov Y (covApply cov Z W) - covApply cov Z (covApply cov Y W)
          - covApply cov (mlieBracket I Y Z) W) y := by
  filter_upwards [CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hY,
    CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hZ,
    CovariantOrderEndo.eventually_cmdiffAt_two' hW] with y hYy hZy hWy
  simp only [Pi.sub_apply, covApply_apply]
  exact curvEndo_apply cov hYy hZy hWy

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M] in
/-- The connection distributes over a difference of differentiable sections. Mathlib's
`IsCovariantDerivativeOn` carries `add` and `smul_const` and no `sub`. -/
theorem cov_sub {A B : Π x : M, TangentSpace I x} {x : M}
    (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) :
    cov (A - B) x = cov A x - cov B x := by
  have hcov := cov.isCovariantDerivativeOnUniv
  have hneg : cov (-B) x = - cov B x := by
    have h := hcov.smul_const (-1 : ℝ) hB
    simpa using h
  have hadd := hcov.add hA (mdifferentiableAt_neg_section hB)
  rw [sub_eq_add_neg, hadd, hneg, sub_eq_add_neg]

variable [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The second covariant derivative is differentiable at the point, for fields of class `C^(k+2)`
with `k ≠ 0`. -/
theorem mdiffAt_covApply_covApply (hk : k ≠ 0) {Y W D : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x)
    (hD : MDiffAt (T% D) x) :
    MDiffAt (T% (covApply cov D (covApply cov Y W))) x := by
  have h2 : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 := by
    have hk' : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 by omega)
  exact CurvatureTensor.mdiffAt_covApply' cov
    ((CovariantOrderCurv.contMDiffAt_covApply_succ cov hY hW).of_le h2) hD

/-- **THE THIRD DERIVATIVE EXPANSION**: `∇_u (R(Y, Z)W)` is
`∇_u ∇_Y ∇_Z W − ∇_u ∇_Z ∇_Y W − ∇_u ∇_{[Y,Z]} W`, for fields of class `C^(k+2)` with `k ≠ 0`. -/
theorem cov_riemann_section (hk : k ≠ 0) {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) (u : TangentSpace I x) :
    cov (fun y ↦ curvEndo cov y (Y y) (Z y) (W y)) x u
      = cov (covApply cov Y (covApply cov Z W)) x u
        - cov (covApply cov Z (covApply cov Y W)) x u
        - cov (covApply cov (mlieBracket I Y Z) W) x u := by
  have h2 : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 + 1 := by
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 + 1 by omega)
  have hYx : MDiffAt (T% Y) x := (hY.of_le h2).mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := (hZ.of_le h2).mdifferentiableAt two_ne_zero
  have hbr : MDiffAt (T% (mlieBracket I Y Z)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hY.of_le h2) (hZ.of_le h2)
  have d1 : MDiffAt (T% (covApply cov Y (covApply cov Z W))) x :=
    mdiffAt_covApply_covApply cov hk hZ hW hYx
  have d2 : MDiffAt (T% (covApply cov Z (covApply cov Y W))) x :=
    mdiffAt_covApply_covApply cov hk hY hW hZx
  have d3 : MDiffAt (T% (covApply cov (mlieBracket I Y Z) W)) x :=
    CurvatureTensor.mdiffAt_covApply' cov (hW.of_le h2) hbr
  have dR : MDiffAt (T% (covApply cov Y (covApply cov Z W)
      - covApply cov Z (covApply cov Y W) - covApply cov (mlieBracket I Y Z) W)) x :=
    mdifferentiableAt_sub_section (mdifferentiableAt_sub_section d1 d2) d3
  have heq := riemann_apply_eventually cov (hY.of_le h2) (hZ.of_le h2) (hW.of_le h2)
  have dL : MDiffAt (T% (fun y ↦ curvEndo cov y (Y y) (Z y) (W y))) x :=
    dR.congr_of_eventuallyEq (by filter_upwards [heq] with y hy; simp only [hy])
  have hcov := cov.isCovariantDerivativeOnUniv
  have e := hcov.congr_of_eventuallyEq dL dR Filter.univ_mem heq
  rw [e, cov_sub cov (mdifferentiableAt_sub_section d1 d2) d3, cov_sub cov d1 d2]
  simp

/-! ## 3. The identity -/

/-- **THE SECOND BIANCHI IDENTITY**: `(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0`, evaluated
on a fourth field, for any **torsion-free** connection of class `C^(k+1)` and fields of class
`C^(k+2)` at the point with `k ≠ 0`. -/
theorem covRiemann_cyclic (hzero : cov.torsion = 0) (hk : k ≠ 0)
    {X Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (X x) (W x)
        + CovariantOrderCovDeriv.covRiemann cov Z X x (Y x) (W x)
        + CovariantOrderCovDeriv.covRiemann cov X Y x (Z x) (W x) = 0 := by
  have h2 : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 + 1 := by
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 + 1 by omega)
  have h2' : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 := by
    have hk' : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 by omega)
  have hXx : MDiffAt (T% X) x := (hX.of_le h2).mdifferentiableAt two_ne_zero
  have hYx : MDiffAt (T% Y) x := (hY.of_le h2).mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := (hZ.of_le h2).mdifferentiableAt two_ne_zero
  have hWx : MDiffAt (T% W) x := (hW.of_le h2).mdifferentiableAt two_ne_zero
  -- the classical formula on each cyclic term
  have t1 := CovariantOrderCovDeriv.covRiemann_apply cov hk hY hZ hWx (X x)
  have t2 := CovariantOrderCovDeriv.covRiemann_apply cov hk hZ hX hWx (Y x)
  have t3 := CovariantOrderCovDeriv.covRiemann_apply cov hk hX hY hWx (Z x)
  -- the third-derivative expansion of each `∇_u (R(·, ·)W)`
  have e1 := cov_riemann_section cov hk hY hZ hW (X x)
  have e2 := cov_riemann_section cov hk hZ hX hW (Y x)
  have e3 := cov_riemann_section cov hk hX hY hW (Z x)
  -- `R(·, ·)(∇_u W)`, through the curvature's definition on the section `∇_u W`
  have hV1 : CMDiffAt 2 (T% (covApply cov X W)) x :=
    (CovariantOrderCurv.contMDiffAt_covApply_succ cov hX hW).of_le h2'
  have hV2 : CMDiffAt 2 (T% (covApply cov Y W)) x :=
    (CovariantOrderCurv.contMDiffAt_covApply_succ cov hY hW).of_le h2'
  have hV3 : CMDiffAt 2 (T% (covApply cov Z W)) x :=
    (CovariantOrderCurv.contMDiffAt_covApply_succ cov hZ hW).of_le h2'
  have f1 : curvEndo cov x (Y x) (Z x) (cov W x (X x))
      = cov (covApply cov Z (covApply cov X W)) x (Y x)
        - cov (covApply cov Y (covApply cov X W)) x (Z x)
        - cov (covApply cov X W) x (mlieBracket I Y Z x) := by
    simpa [covApply] using curvEndo_apply cov hYx hZx hV1
  have f2 : curvEndo cov x (Z x) (X x) (cov W x (Y x))
      = cov (covApply cov X (covApply cov Y W)) x (Z x)
        - cov (covApply cov Z (covApply cov Y W)) x (X x)
        - cov (covApply cov Y W) x (mlieBracket I Z X x) := by
    simpa [covApply] using curvEndo_apply cov hZx hXx hV2
  have f3 : curvEndo cov x (X x) (Y x) (cov W x (Z x))
      = cov (covApply cov Y (covApply cov Z W)) x (X x)
        - cov (covApply cov X (covApply cov Z W)) x (Y x)
        - cov (covApply cov Z W) x (mlieBracket I X Y x) := by
    simpa [covApply] using curvEndo_apply cov hXx hYx hV3
  -- the curvature on the pair (direction, bracket), which is where the leftovers go
  have hbr1 : MDiffAt (T% (mlieBracket I Y Z)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hY.of_le h2) (hZ.of_le h2)
  have hbr2 : MDiffAt (T% (mlieBracket I Z X)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hZ.of_le h2) (hX.of_le h2)
  have hbr3 : MDiffAt (T% (mlieBracket I X Y)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hX.of_le h2) (hY.of_le h2)
  have g1' : cov (covApply cov (mlieBracket I Y Z) W) x (X x)
      = curvEndo cov x (X x) (mlieBracket I Y Z x) (W x)
        + cov (covApply cov X W) x (mlieBracket I Y Z x)
        + cov W x (mlieBracket I X (mlieBracket I Y Z) x) := by
    have g1 : curvEndo cov x (X x) (mlieBracket I Y Z x) (W x)
        = cov (covApply cov (mlieBracket I Y Z) W) x (X x)
          - cov (covApply cov X W) x (mlieBracket I Y Z x)
          - cov W x (mlieBracket I X (mlieBracket I Y Z) x) := by
      simpa [covApply] using curvEndo_apply cov hXx hbr1 (hW.of_le h2)
    rw [g1]; abel
  have g2' : cov (covApply cov (mlieBracket I Z X) W) x (Y x)
      = curvEndo cov x (Y x) (mlieBracket I Z X x) (W x)
        + cov (covApply cov Y W) x (mlieBracket I Z X x)
        + cov W x (mlieBracket I Y (mlieBracket I Z X) x) := by
    have g2 : curvEndo cov x (Y x) (mlieBracket I Z X x) (W x)
        = cov (covApply cov (mlieBracket I Z X) W) x (Y x)
          - cov (covApply cov Y W) x (mlieBracket I Z X x)
          - cov W x (mlieBracket I Y (mlieBracket I Z X) x) := by
      simpa [covApply] using curvEndo_apply cov hYx hbr2 (hW.of_le h2)
    rw [g2]; abel
  have g3' : cov (covApply cov (mlieBracket I X Y) W) x (Z x)
      = curvEndo cov x (Z x) (mlieBracket I X Y x) (W x)
        + cov (covApply cov Z W) x (mlieBracket I X Y x)
        + cov W x (mlieBracket I Z (mlieBracket I X Y) x) := by
    have g3 : curvEndo cov x (Z x) (mlieBracket I X Y x) (W x)
        = cov (covApply cov (mlieBracket I X Y) W) x (Z x)
          - cov (covApply cov Z W) x (mlieBracket I X Y x)
          - cov W x (mlieBracket I Z (mlieBracket I X Y) x) := by
      simpa [covApply] using curvEndo_apply cov hZx hbr3 (hW.of_le h2)
    rw [g3]; abel
  -- the triple brackets vanish cyclically
  have jac : cov W x (mlieBracket I Z (mlieBracket I X Y) x)
      = - cov W x (mlieBracket I X (mlieBracket I Y Z) x)
        - cov W x (mlieBracket I Y (mlieBracket I Z X) x) := by
    have h := mlieBracket_cyclic_jacobi' (hX.of_le h2) (hY.of_le h2) (hZ.of_le h2)
    have hmap : cov W x (mlieBracket I X (mlieBracket I Y Z) x
          + mlieBracket I Y (mlieBracket I Z X) x + mlieBracket I Z (mlieBracket I X Y) x)
        = cov W x (mlieBracket I X (mlieBracket I Y Z) x)
          + cov W x (mlieBracket I Y (mlieBracket I Z X) x)
          + cov W x (mlieBracket I Z (mlieBracket I X Y) x) := by
      simp only [map_add]
    rw [h, map_zero] at hmap
    have h3 : cov W x (mlieBracket I Z (mlieBracket I X Y) x)
        = 0 - cov W x (mlieBracket I X (mlieBracket I Y Z) x)
          - cov W x (mlieBracket I Y (mlieBracket I Z X) x) := by
      rw [hmap]; abel
    simpa using h3
  -- skew-symmetry moves the bracket into the first slot
  have sw1 : curvEndo cov x (X x) (mlieBracket I Y Z x) (W x)
      = - curvEndo cov x (mlieBracket I Y Z x) (X x) (W x) := by
    rw [curvEndo_swap]; simp
  have sw2 : curvEndo cov x (Y x) (mlieBracket I Z X x) (W x)
      = - curvEndo cov x (mlieBracket I Z X x) (Y x) (W x) := by
    rw [curvEndo_swap]; simp
  have sw3 : curvEndo cov x (Z x) (mlieBracket I X Y x) (W x)
      = - curvEndo cov x (mlieBracket I X Y x) (Z x) (W x) := by
    rw [curvEndo_swap]; simp
  -- the six corrections, applied to `W x`
  have corrW := congrArg
    (fun T : TangentSpace I x →L[ℝ] TangentSpace I x ↦ T (W x))
    (CovariantOrderCovCyclic.riemann_corrections_cyclic cov hzero hXx hYx hZx)
  simp only [ContinuousLinearMap.add_apply] at corrW
  have key : CovariantOrderCovDeriv.covRiemann cov Y Z x (X x) (W x)
        + CovariantOrderCovDeriv.covRiemann cov Z X x (Y x) (W x)
        + CovariantOrderCovDeriv.covRiemann cov X Y x (Z x) (W x)
      = (curvEndo cov x (mlieBracket I X Y x) (Z x) (W x)
          + curvEndo cov x (mlieBracket I Y Z x) (X x) (W x)
          + curvEndo cov x (mlieBracket I Z X x) (Y x) (W x))
        - (curvEndo cov x (cov Y x (X x)) (Z x) (W x)
            + curvEndo cov x (Y x) (cov Z x (X x)) (W x)
          + (curvEndo cov x (cov Z x (Y x)) (X x) (W x)
            + curvEndo cov x (Z x) (cov X x (Y x)) (W x))
          + (curvEndo cov x (cov X x (Z x)) (Y x) (W x)
            + curvEndo cov x (X x) (cov Y x (Z x)) (W x))) := by
    rw [t1, t2, t3, e1, e2, e3, f1, f2, f3, g1', g2', g3', jac, sw1, sw2, sw3]
    abel
  rw [key, corrW]
  abel

/-- **THE SECOND BIANCHI IDENTITY, ON A VECTOR**: the same sum applied to any tangent vector at the
point, through the extension of that vector to a section. -/
theorem covRiemann_cyclic_apply (hzero : cov.torsion = 0) (hk : k ≠ 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (w : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (X x) w
        + CovariantOrderCovDeriv.covRiemann cov Z X x (Y x) w
        + CovariantOrderCovDeriv.covRiemann cov X Y x (Z x) w = 0 := by
  have hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (extend E w)) x :=
    contMDiffAt_extend' (k := (k : WithTop ℕ∞) + 1 + 1) I E w
  simpa using covRiemann_cyclic cov hzero hk hX hY hZ hW

/-- **THE SECOND BIANCHI IDENTITY AS AN IDENTITY OF ENDOMORPHISMS**:
`(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0` in `Hom(TM, TM)` at the point, for any
torsion-free connection of class `C^(k+1)`. **This is the form to quote.** -/
theorem covRiemann_cyclic_endo (hzero : cov.torsion = 0) (hk : k ≠ 0)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x (X x)
        + CovariantOrderCovDeriv.covRiemann cov Z X x (Y x)
        + CovariantOrderCovDeriv.covRiemann cov X Y x (Z x) = 0 := by
  ext w
  simpa using covRiemann_cyclic_apply cov hzero hk hX hY hZ w

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self

/-- **AND `CurvatureBianchiSecond`'S IDENTITY IS THIS ONE AT A TORSION-FREE CONNECTION** — derived
from the abstract statement, with the hypothesis discharged by `KoszulManifold.leviCivita_torsion`
and the two `∇R`s identified by `CovariantOrderCovDeriv.covRiemann_eq` (`rfl`). A theorem rather
than a remark so the subsumption is checked. -/
theorem covRiemann_cyclic_endo_leviCivita (hk : k ≠ 0) {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CurvatureCovDeriv.covRiemann Y Z x (X x) + CurvatureCovDeriv.covRiemann Z X x (Y x)
      + CurvatureCovDeriv.covRiemann X Y x (Z x) = 0 := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  haveI : IsLocallyCk ((k : WithTop ℕ∞) + 1)
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) := by
    rw [← e]
    exact CovariantOrderClass.isLocallyCk_leviCivita (k := k + 1)
  rw [← CovariantOrderCovDeriv.covRiemann_eq Y Z x (X x),
    ← CovariantOrderCovDeriv.covRiemann_eq Z X x (Y x),
    ← CovariantOrderCovDeriv.covRiemann_eq X Y x (Z x)]
  exact covRiemann_cyclic_endo _ KoszulManifold.leviCivita_torsion hk hX hY hZ

end LeviCivita

end CovariantOrderBianchiSecond
