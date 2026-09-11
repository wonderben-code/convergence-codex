import CurvatureCovCyclic
import CurvatureCovOrder
import CurvatureBianchi

/-!
# The second Bianchi identity

**`(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0`**, for the Levi-Civita connection of a
`C^(k+2)` metric and direction fields of class `C^(k+2)` at the point, with `k ≠ 0`. This is the
last of the classical curvature identities the estate did not have: `CurvatureBianchi` has the
first (algebraic) one and `CurvatureSkew` the symmetries, and the `UNLOCK_WATCHLIST` item for this
one has been open since it was filed, with three steps named. Steps (1) and (2) are
`CurvatureCovDeriv` (the object) and `CurvatureCovTensor` (its tensoriality); `CurvatureCovCyclic`
removed the correction terms from step (3), and **this file does step (3)**.

**The proof is the classical computation and it is shorter than the estimate.** The cyclic sum of
`CurvatureCovCyclic`'s reduction is an equation between third covariant derivatives of a section,
and the striking part is that **all nine of them cancel by additive algebra alone** — no Jacobi
identity is needed for the third derivatives, only for the brackets. What is left after they go is
the pair `(X, [Y, Z])`: the leftover combination `∇_X ∇_{[Y,Z]} W − ∇_{[Y,Z]} ∇_X W` is, by the
curvature's own definition on that pair, `R(X, [Y,Z])W + ∇_{[X,[Y,Z]]} W`; the second term dies
cyclically because the connection is linear in its direction and the brackets satisfy the Jacobi
identity, and the first is `−R([Y,Z], X)W`, which is exactly what `CurvatureCovCyclic` produced
from the corrections. **Torsion-freeness is used**, through that file's corrections lemma, and it
is free here because the connection is the Levi-Civita one; nothing is claimed for a connection
with torsion.

**No normal coordinates, and none exist here.** The textbook one-line proof evaluates at the
centre of a normal coordinate system where the connection coefficients vanish. Neither this estate
nor the pinned library has normal coordinates, an exponential map or a geodesic, so the proof below
is the coordinate-free computation on sections, which is why it needs the third-derivative
bookkeeping at all.

## What is proved

**`riemann_apply_eventually`** — `R(Y, Z)W = ∇_Y ∇_Z W − ∇_Z ∇_Y W − ∇_{[Y,Z]} W` **as sections
near the point**, not merely at it. Applying a further covariant derivative to the curvature needs
the identity on a neighbourhood, which is `RicciOrder.eventually_cmdiffAt_two`'s job.

**`isManifold_shift1`, `isMetric_shift1`** — the two order casts that let `LeviCivitaOrder`'s
order-`k` regularity theorem be used at `k + 1`. `CurvatureCovOrder` needed four of these for one
theorem; these are the same device.

**`cmdiffAt_covApply_succ`** — **`∇_Z W` is of class `C^(k+1)` for `Z, W` of class `C^(k+2)`**, and
**`mdiffAt_covApply_covApply`** — **the SECOND covariant derivative is differentiable at the
point** when `k ≠ 0`. This is the analytic content that the first Bianchi identity did not need:
that file differentiates twice, this one three times.

**`cov_sub`** — the connection distributes over a difference of differentiable sections. Mathlib's
`IsCovariantDerivativeOn` carries `add` and `smul_const` and **no `sub`**;
`CurvatureBianchi.cov_covApply_sub` inlines this argument, and it is used three times below.

**`cov_riemann_section`** — **THE THIRD-DERIVATIVE EXPANSION**:
`∇_u (R(Y, Z)W) = ∇_u ∇_Y ∇_Z W − ∇_u ∇_Z ∇_Y W − ∇_u ∇_{[Y,Z]} W`. The connection applied to the
eventual identity above, with the four sections' differentiability supplied by the two lemmas
before it.

**`mlieBracket_cyclic_jacobi`** — **`[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0`**. The pinned library
carries the Leibniz form `[U,[V,W]] = [[U,V],W] + [V,[U,W]]` and **not** the cyclic one;
`CurvatureBianchi.curvAux_cyclic` derives what it needs from the Leibniz form inline, and this
states it once.

**`covRiemann_cyclic`** — **THE SECOND BIANCHI IDENTITY**, evaluated on a fourth field.
**`covRiemann_cyclic_apply`** — on any tangent vector at the point, through its extension.
**`covRiemann_cyclic_endo`** — **as an identity of endomorphisms in `Hom(TM, TM)`**, which is the
form to quote.

## What is NOT here

* **NO CONTRACTED IDENTITY, AND SO NOTHING ABOUT THE EINSTEIN TENSOR.** The contracted second
  Bianchi identity — `div G = 0` — is a trace of this one, **which** contraction is meant is the
  author's decision (`ASSUMPTIONS 56`), and no trace is taken here. **Not attempted, no cost
  claimed** (`ERRATUM 246`).
* **`∇R` IS STILL NOT BUNDLED AS A TENSOR.** The identity is stated for three direction **fields**
  and a fourth field or vector, not for a bundled `(1,3)`-tensor: `CurvatureCovTensor` proves the
  dependence on `Y`, `Z` is through `Y x`, `Z x` and says in its own fence that the bundling is
  plumbing it does not do. That is unchanged, and this file does not need it. ⚠ **SUPERSEDED THE
  SAME DAY, entry 118** (`CurvatureCovBundle`), and kept as written (`ERRATUM 94`): the bundling in
  the two curvature slots is `covRiemannHom`, and `covRiemannAt_cyclic` is **this file's identity
  for three arbitrary tangent vectors**, which is the form the sentence above says is missing. The
  four-deep object, with the direction bundled in too, is not built as of 2026-09-11. **The
  sentence was true
  for four hours.**
* **NOTHING FOR A CONNECTION WITH TORSION.** The corrections lemma this proof rests on is
  torsion-free; for a connection with torsion the cyclic sum is an expression in the torsion and
  its derivative, and nothing about it is stated (`CurvatureBianchi`'s fence, at the first
  identity, says the same).
* **NOTHING AT `k = 0`.** Every theorem that differentiates the curvature takes `hk : k ≠ 0`,
  because the induced connection needs an argument it can differentiate, and a `C²` metric gives a
  `C⁰` curvature.
* **NO WALL MOVES.** `W5`'s rung 4 needs the heat semigroup and a parametrix, which `WALLS`
  §W5.1 §4 prices as research. The second Bianchi identity is not on that path; what it buys is
  the classical identity itself, and the contracted form is one author decision away.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`), **and the paragraph is
`binder_scan.py`'s table**: the section context is `CurvatureCovDeriv`'s, unchanged — a normed
space `E` over `ℝ` with `[CompleteSpace E]` and `[FiniteDimensional ℝ E]`, a `ChartedSpace H M`
with model `I`, the four `IsManifold` instances, `[RiemannianBundle …]` and the two
`IsContMDiffRiemannianBundle` instances, with `CurvatureCovDeriv`'s seven local instances,
`CurvatureCovOrder`'s two downward shifts and this file's two upward casts. **Five of the eleven**
declarations take `hk : k ≠ 0`; the two order casts and the Jacobi identity take no hypothesis
about the curvature at all. Five declarations `omit` binders they do not use, and the Jacobi
identity's first `omit` list was **rejected by the elaborator** (`cannot omit referenced section
variable`) and narrowed to the two the linter actually names, rather than forced with a
`set_option`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureBianchiSecond

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
  CurvatureCovOrder.isManifold_down CurvatureCovOrder.isContMDiffRiemannianBundle_down

/-- Local name for the Levi-Civita connection. -/
local notation "LC" => (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- `R(Y, Z)W = ∇_Y ∇_Z W − ∇_Z ∇_Y W − ∇_{[Y,Z]} W` as sections **near** the point, which is what
applying a further covariant derivative to it needs. -/
theorem riemann_apply_eventually {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) (hW : CMDiffAt 2 (T% W) x) :
    ∀ᶠ y in 𝓝 x, LeviCivitaRegular.riemann I y (Y y) (Z y) (W y)
      = (covApply LC Y (covApply LC Z W) - covApply LC Z (covApply LC Y W)
          - covApply LC (mlieBracket I Y Z) W) y := by
  filter_upwards [CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hY,
    CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hZ,
    RicciOrder.eventually_cmdiffAt_two hW] with y hYy hZy hWy
  simp only [Pi.sub_apply, covApply_apply]
  exact LeviCivitaRegular.riemann_apply hYy hZy hWy

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The cast that lets `LeviCivitaOrder`'s order-`k` theorem be used at `k + 1`: the manifold. -/
theorem isManifold_shift1 : IsManifold I (((k + 1 : ℕ) : WithTop ℕ∞) + 1 + 1) M := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 + 1 = (k : WithTop ℕ∞) + 1 + 1 + 1 := by
    push_cast; ring
  rw [e]; infer_instance

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The same cast for the metric's order. -/
theorem isMetric_shift1 :
    IsContMDiffRiemannianBundle I (((k + 1 : ℕ) : WithTop ℕ∞) + 1) E
      (TangentSpace I : M → Type _) := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  rw [e]; infer_instance

attribute [local instance] isManifold_shift1 isMetric_shift1

omit [IsManifold I 3 M] in
/-- **`∇_Z W` is of class `C^(k+1)`** for `Z, W` of class `C^(k+2)`: `LeviCivitaOrder`'s theorem at
`k + 1`, with the order cast. -/
theorem cmdiffAt_covApply_succ {Y W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) :
    CMDiffAt ((k : WithTop ℕ∞) + 1) (T% (covApply LC Y W)) x := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  have e' : (((k + 1 : ℕ) : WithTop ℕ∞)) + 1 = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; ring
  have h := LeviCivitaOrder.contMDiffAt_leviCivita_apply (k := k + 1)
    (by rw [e']; exact hY) (by rw [e']; exact hW)
  rw [e] at h
  exact h

/-- The second covariant derivative is differentiable at the point, for fields of class `C^(k+2)`
with `k ≠ 0`. -/
theorem mdiffAt_covApply_covApply (hk : k ≠ 0) {Y W D : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x)
    (hD : MDiffAt (T% D) x) :
    MDiffAt (T% (covApply LC D (covApply LC Y W))) x := by
  have h2 : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 := by
    have hk' : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 by omega)
  exact CurvatureTensor.mdiffAt_covApply' LC ((cmdiffAt_covApply_succ hY hW).of_le h2) hD

omit [IsManifold I 3 M] in
/-- The connection distributes over a difference of differentiable sections. Mathlib's
`IsCovariantDerivativeOn` carries `add` and `smul_const` and no `sub`; `CurvatureBianchi`'s
`cov_covApply_sub` inlines this argument. -/
theorem cov_sub {A B : Π x : M, TangentSpace I x} {x : M}
    (hA : MDiffAt (T% A) x) (hB : MDiffAt (T% B) x) :
    LC (A - B) x = LC A x - LC B x := by
  have hcov := (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)
    ).isCovariantDerivativeOnUniv
  have hneg : LC (-B) x = - LC B x := by
    have h := hcov.smul_const (-1 : ℝ) hB
    simpa using h
  have hadd := hcov.add hA (mdifferentiableAt_neg_section hB)
  rw [sub_eq_add_neg, hadd, hneg, sub_eq_add_neg]

/-- **THE THIRD DERIVATIVE EXPANSION**: `∇_u (R(Y, Z)W)` is
`∇_u ∇_Y ∇_Z W − ∇_u ∇_Z ∇_Y W − ∇_u ∇_{[Y,Z]} W`, for fields of class `C^(k+2)` with `k ≠ 0`.
This is the analytic step the second Bianchi identity needs, and it is the one `CurvatureBianchi`
did not need: the first identity differentiates twice. -/
theorem cov_riemann_section (hk : k ≠ 0) {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) (u : TangentSpace I x) :
    LC (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y) (W y)) x u
      = LC (covApply LC Y (covApply LC Z W)) x u
        - LC (covApply LC Z (covApply LC Y W)) x u
        - LC (covApply LC (mlieBracket I Y Z) W) x u := by
  have h2 : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 + 1 := by
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 + 1 by omega)
  have hYx : MDiffAt (T% Y) x := (hY.of_le h2).mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := (hZ.of_le h2).mdifferentiableAt two_ne_zero
  have hbr : MDiffAt (T% (mlieBracket I Y Z)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hY.of_le h2) (hZ.of_le h2)
  have d1 : MDiffAt (T% (covApply LC Y (covApply LC Z W))) x :=
    mdiffAt_covApply_covApply hk hZ hW hYx
  have d2 : MDiffAt (T% (covApply LC Z (covApply LC Y W))) x :=
    mdiffAt_covApply_covApply hk hY hW hZx
  have d3 : MDiffAt (T% (covApply LC (mlieBracket I Y Z) W)) x :=
    CurvatureTensor.mdiffAt_covApply' LC (hW.of_le h2) hbr
  have dR : MDiffAt (T% (covApply LC Y (covApply LC Z W)
      - covApply LC Z (covApply LC Y W) - covApply LC (mlieBracket I Y Z) W)) x :=
    mdifferentiableAt_sub_section (mdifferentiableAt_sub_section d1 d2) d3
  have heq := riemann_apply_eventually (hY.of_le h2) (hZ.of_le h2) (hW.of_le h2)
  have dL : MDiffAt (T% (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y) (W y))) x :=
    dR.congr_of_eventuallyEq (by filter_upwards [heq] with y hy; simp only [hy])
  have hcov := (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)
    ).isCovariantDerivativeOnUniv
  have e := hcov.congr_of_eventuallyEq dL dR Filter.univ_mem heq
  rw [e, cov_sub (mdifferentiableAt_sub_section d1 d2) d3, cov_sub d1 d2]
  simp

omit [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- **THE JACOBI IDENTITY IN CYCLIC FORM**: `[X,[Y,Z]] + [Y,[Z,X]] + [Z,[X,Y]] = 0`. The pinned
library carries the Leibniz form `[U,[V,W]] = [[U,V],W] + [V,[U,W]]` and not this one;
`CurvatureBianchi.curvAux_cyclic` derives what it needs from the Leibniz form inline. -/
theorem mlieBracket_cyclic_jacobi {X Y Z : Π x : M, TangentSpace I x} {x : M}
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

/-- **THE SECOND BIANCHI IDENTITY**: `(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0`,
evaluated on a fourth field, for fields of class `C^(k+2)` at the point with `k ≠ 0`. -/
theorem covRiemann_cyclic (hk : k ≠ 0) {X Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x) :
    CurvatureCovDeriv.covRiemann Y Z x (X x) (W x)
        + CurvatureCovDeriv.covRiemann Z X x (Y x) (W x)
        + CurvatureCovDeriv.covRiemann X Y x (Z x) (W x) = 0 := by
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
  have t1 := CurvatureCovDeriv.covRiemann_apply hk hY hZ hWx (X x)
  have t2 := CurvatureCovDeriv.covRiemann_apply hk hZ hX hWx (Y x)
  have t3 := CurvatureCovDeriv.covRiemann_apply hk hX hY hWx (Z x)
  -- the third-derivative expansion of each `∇_u (R(·, ·)W)`
  have e1 := cov_riemann_section hk hY hZ hW (X x)
  have e2 := cov_riemann_section hk hZ hX hW (Y x)
  have e3 := cov_riemann_section hk hX hY hW (Z x)
  -- `R(·, ·)(∇_u W)`, through the curvature's definition on the section `∇_u W`
  have hV1 : CMDiffAt 2 (T% (covApply LC X W)) x := (cmdiffAt_covApply_succ hX hW).of_le h2'
  have hV2 : CMDiffAt 2 (T% (covApply LC Y W)) x := (cmdiffAt_covApply_succ hY hW).of_le h2'
  have hV3 : CMDiffAt 2 (T% (covApply LC Z W)) x := (cmdiffAt_covApply_succ hZ hW).of_le h2'
  have f1 : LeviCivitaRegular.riemann I x (Y x) (Z x) (leviCivita W x (X x))
      = leviCivita (covApply LC Z (covApply LC X W)) x (Y x)
        - leviCivita (covApply LC Y (covApply LC X W)) x (Z x)
        - leviCivita (covApply LC X W) x (mlieBracket I Y Z x) := by
    simpa [covApply] using LeviCivitaRegular.riemann_apply hYx hZx hV1
  have f2 : LeviCivitaRegular.riemann I x (Z x) (X x) (leviCivita W x (Y x))
      = leviCivita (covApply LC X (covApply LC Y W)) x (Z x)
        - leviCivita (covApply LC Z (covApply LC Y W)) x (X x)
        - leviCivita (covApply LC Y W) x (mlieBracket I Z X x) := by
    simpa [covApply] using LeviCivitaRegular.riemann_apply hZx hXx hV2
  have f3 : LeviCivitaRegular.riemann I x (X x) (Y x) (leviCivita W x (Z x))
      = leviCivita (covApply LC Y (covApply LC Z W)) x (X x)
        - leviCivita (covApply LC X (covApply LC Z W)) x (Y x)
        - leviCivita (covApply LC Z W) x (mlieBracket I X Y x) := by
    simpa [covApply] using LeviCivitaRegular.riemann_apply hXx hYx hV3
  -- the curvature on the pair (direction, bracket), which is where the leftovers go
  have hbr1 : MDiffAt (T% (mlieBracket I Y Z)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hY.of_le h2) (hZ.of_le h2)
  have hbr2 : MDiffAt (T% (mlieBracket I Z X)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hZ.of_le h2) (hX.of_le h2)
  have hbr3 : MDiffAt (T% (mlieBracket I X Y)) x :=
    CurvatureBianchi.mdiffAt_mlieBracket (hX.of_le h2) (hY.of_le h2)
  have g1' : leviCivita (covApply LC (mlieBracket I Y Z) W) x (X x)
      = LeviCivitaRegular.riemann I x (X x) (mlieBracket I Y Z x) (W x)
        + leviCivita (covApply LC X W) x (mlieBracket I Y Z x)
        + leviCivita W x (mlieBracket I X (mlieBracket I Y Z) x) := by
    have g1 : LeviCivitaRegular.riemann I x (X x) (mlieBracket I Y Z x) (W x)
        = leviCivita (covApply LC (mlieBracket I Y Z) W) x (X x)
          - leviCivita (covApply LC X W) x (mlieBracket I Y Z x)
          - leviCivita W x (mlieBracket I X (mlieBracket I Y Z) x) := by
      simpa [covApply] using LeviCivitaRegular.riemann_apply hXx hbr1 (hW.of_le h2)
    rw [g1]; abel
  have g2' : leviCivita (covApply LC (mlieBracket I Z X) W) x (Y x)
      = LeviCivitaRegular.riemann I x (Y x) (mlieBracket I Z X x) (W x)
        + leviCivita (covApply LC Y W) x (mlieBracket I Z X x)
        + leviCivita W x (mlieBracket I Y (mlieBracket I Z X) x) := by
    have g2 : LeviCivitaRegular.riemann I x (Y x) (mlieBracket I Z X x) (W x)
        = leviCivita (covApply LC (mlieBracket I Z X) W) x (Y x)
          - leviCivita (covApply LC Y W) x (mlieBracket I Z X x)
          - leviCivita W x (mlieBracket I Y (mlieBracket I Z X) x) := by
      simpa [covApply] using LeviCivitaRegular.riemann_apply hYx hbr2 (hW.of_le h2)
    rw [g2]; abel
  have g3' : leviCivita (covApply LC (mlieBracket I X Y) W) x (Z x)
      = LeviCivitaRegular.riemann I x (Z x) (mlieBracket I X Y x) (W x)
        + leviCivita (covApply LC Z W) x (mlieBracket I X Y x)
        + leviCivita W x (mlieBracket I Z (mlieBracket I X Y) x) := by
    have g3 : LeviCivitaRegular.riemann I x (Z x) (mlieBracket I X Y x) (W x)
        = leviCivita (covApply LC (mlieBracket I X Y) W) x (Z x)
          - leviCivita (covApply LC Z W) x (mlieBracket I X Y x)
          - leviCivita W x (mlieBracket I Z (mlieBracket I X Y) x) := by
      simpa [covApply] using LeviCivitaRegular.riemann_apply hZx hbr3 (hW.of_le h2)
    rw [g3]; abel
  -- the triple brackets vanish cyclically
  have jac : leviCivita W x (mlieBracket I Z (mlieBracket I X Y) x)
      = - leviCivita W x (mlieBracket I X (mlieBracket I Y Z) x)
        - leviCivita W x (mlieBracket I Y (mlieBracket I Z X) x) := by
    have h := mlieBracket_cyclic_jacobi (hX.of_le h2) (hY.of_le h2) (hZ.of_le h2)
    have hmap : leviCivita W x (mlieBracket I X (mlieBracket I Y Z) x
          + mlieBracket I Y (mlieBracket I Z X) x + mlieBracket I Z (mlieBracket I X Y) x)
        = leviCivita W x (mlieBracket I X (mlieBracket I Y Z) x)
          + leviCivita W x (mlieBracket I Y (mlieBracket I Z X) x)
          + leviCivita W x (mlieBracket I Z (mlieBracket I X Y) x) := by
      simp only [map_add]
    rw [h, map_zero] at hmap
    have h2 : leviCivita W x (mlieBracket I Z (mlieBracket I X Y) x)
        = 0 - leviCivita W x (mlieBracket I X (mlieBracket I Y Z) x)
          - leviCivita W x (mlieBracket I Y (mlieBracket I Z X) x) := by
      rw [hmap]; abel
    simpa using h2
  -- skew-symmetry moves the bracket into the first slot
  have sw1 : LeviCivitaRegular.riemann I x (X x) (mlieBracket I Y Z x) (W x)
      = - LeviCivitaRegular.riemann I x (mlieBracket I Y Z x) (X x) (W x) := by
    rw [LeviCivitaRegular.riemann_swap]; simp
  have sw2 : LeviCivitaRegular.riemann I x (Y x) (mlieBracket I Z X x) (W x)
      = - LeviCivitaRegular.riemann I x (mlieBracket I Z X x) (Y x) (W x) := by
    rw [LeviCivitaRegular.riemann_swap]; simp
  have sw3 : LeviCivitaRegular.riemann I x (Z x) (mlieBracket I X Y x) (W x)
      = - LeviCivitaRegular.riemann I x (mlieBracket I X Y x) (Z x) (W x) := by
    rw [LeviCivitaRegular.riemann_swap]; simp
  -- the six corrections, applied to `W x`
  have corrW := congrArg
    (fun T : TangentSpace I x →L[ℝ] TangentSpace I x ↦ T (W x))
    (CurvatureCovCyclic.riemann_corrections_cyclic hXx hYx hZx)
  simp only [ContinuousLinearMap.add_apply] at corrW
  have key : CurvatureCovDeriv.covRiemann Y Z x (X x) (W x)
        + CurvatureCovDeriv.covRiemann Z X x (Y x) (W x)
        + CurvatureCovDeriv.covRiemann X Y x (Z x) (W x)
      = (LeviCivitaRegular.riemann I x (mlieBracket I X Y x) (Z x) (W x)
          + LeviCivitaRegular.riemann I x (mlieBracket I Y Z x) (X x) (W x)
          + LeviCivitaRegular.riemann I x (mlieBracket I Z X x) (Y x) (W x))
        - (LeviCivitaRegular.riemann I x (leviCivita Y x (X x)) (Z x) (W x)
            + LeviCivitaRegular.riemann I x (Y x) (leviCivita Z x (X x)) (W x)
          + (LeviCivitaRegular.riemann I x (leviCivita Z x (Y x)) (X x) (W x)
            + LeviCivitaRegular.riemann I x (Z x) (leviCivita X x (Y x)) (W x))
          + (LeviCivitaRegular.riemann I x (leviCivita X x (Z x)) (Y x) (W x)
            + LeviCivitaRegular.riemann I x (X x) (leviCivita Y x (Z x)) (W x))) := by
    rw [t1, t2, t3, e1, e2, e3, f1, f2, f3, g1', g2', g3', jac, sw1, sw2, sw3]
    abel
  rw [key, corrW]
  abel

/-- **THE SECOND BIANCHI IDENTITY, ON A VECTOR**: the same sum applied to any tangent vector at
the point, through the extension of that vector to a section. -/
theorem covRiemann_cyclic_apply (hk : k ≠ 0) {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (w : TangentSpace I x) :
    CurvatureCovDeriv.covRiemann Y Z x (X x) w
        + CurvatureCovDeriv.covRiemann Z X x (Y x) w
        + CurvatureCovDeriv.covRiemann X Y x (Z x) w = 0 := by
  have hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (extend E w)) x :=
    contMDiffAt_extend' (k := (k : WithTop ℕ∞) + 1 + 1) I E w
  simpa using covRiemann_cyclic hk hX hY hZ hW

/-- **THE SECOND BIANCHI IDENTITY AS AN IDENTITY OF ENDOMORPHISMS**:
`(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0` in `Hom(TM, TM)` at the point. This is the
form to quote. -/
theorem covRiemann_cyclic_endo (hk : k ≠ 0) {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CurvatureCovDeriv.covRiemann Y Z x (X x) + CurvatureCovDeriv.covRiemann Z X x (Y x)
      + CurvatureCovDeriv.covRiemann X Y x (Z x) = 0 := by
  ext w
  simpa using covRiemann_cyclic_apply hk hX hY hZ w

end CurvatureBianchiSecond
