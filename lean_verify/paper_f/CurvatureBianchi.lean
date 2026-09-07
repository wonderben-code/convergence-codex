import LeviCivitaRegular

/-!
# The first Bianchi identity, and the antisymmetric part of the Ricci form

`LeviCivitaRegular` gave the estate the curvature of a metric and said in its fence that no
identity of it beyond antisymmetry in the two directions was proved — no Bianchi identity, no pair
symmetry, no symmetry of `Ric`. This file is the first of those. **The first Bianchi identity
`R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0`** holds for every torsion-free connection on `TM` that is
locally `C¹` (`curvAux_cyclic` on sections, `curvEndo_cyclic` on the endomorphism), hence for the
Levi-Civita connection of a `C²` metric (`riemann_cyclic`); and its consequence for the Ricci form
is **`Ric(w, z) − Ric(z, w) = −tr R(w, z)`** (`ricci_sub_swap`), which reduces the symmetry of `Ric`
to the vanishing of that trace — the skew-symmetry of `R(w, z)` for a metric connection, which is
not here.

The proof is the textbook one. Torsion-freeness says `∇_Y Z − ∇_Z Y = [Y, Z]` as sections near
the point (`covApply_sub_covApply_eventually`), so `∇_X ∇_Y Z − ∇_X ∇_Z Y = ∇_X [Y, Z]` by the
connection's locality (`cov_covApply_sub`); the cyclic sum of the three curvatures regroups into
`∑ (∇_X [Y, Z] − ∇_{[Y, Z]} X)`, which torsion-freeness turns into `[X, [Y, Z]] + [Y, [Z, X]] +
[Z, [X, Y]]`, and Mathlib's Jacobi identity for the manifold bracket
(`leibniz_identity_mlieBracket_apply`, for `C²` fields on a `C³` manifold) makes that zero. The
Ricci statement is linear algebra on top: `v ↦ R(v, w) z − R(v, z) w` is `−R(w, z)` by the identity
and antisymmetry, and the trace is linear.

## What is proved

**`mdiffAt_mlieBracket`** — the bracket of two `C²` fields is differentiable at the point.

**`covApply_sub_covApply_eventually`** — for a torsion-free connection, `∇_Y Z − ∇_Z Y = [Y, Z]`
as sections near a point where `Y, Z` are `C²`.

**`cov_covApply_sub`** — and so `∇_X ∇_Y Z − ∇_X ∇_Z Y = ∇_X [Y, Z]` there, for a locally `C¹`
connection.

**`curvAux_cyclic`** — **THE FIRST BIANCHI IDENTITY** on sections,
`R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0` at every point where `X, Y, Z` are `C²`, for a torsion-free
locally `C¹` connection.

**`curvEndo_cyclic`** — the same on the curvature endomorphism:
`R(u, v) w + R(v, w) u + R(w, u) v = 0` for all tangent vectors.

**`ricci_sub_swap`** — **the antisymmetric part of the Ricci form is a trace of the curvature**:
`Ric(w, z) − Ric(z, w) = −tr R(w, z)`.

**`riemann_cyclic`** — **THE FIRST BIANCHI IDENTITY FOR THE CURVATURE OF A `C²` METRIC.**

## What is NOT here

**NO SKEW-SYMMETRY, NO PAIR SYMMETRY, NO SYMMETRY OF `Ric`.** `⟨R(u, v) w, z⟩ = −⟨R(u, v) z, w⟩` for
a metric-compatible connection is the computation `X Y⟨Z, W⟩ − Y X⟨Z, W⟩ − [X, Y]⟨Z, W⟩ = 0`
through `IsMetricCompatible` twice and `BracketDerivation.extDerivFun_apply_mlieBracket`, and it is
not started. With it, the right side of `ricci_sub_swap` vanishes (`LinearMap.trace_eq_sum_inner` on
a skew endomorphism) and `Ric` is symmetric; and with `curvEndo_cyclic` the pair symmetry
`⟨R(u, v) w, z⟩ = ⟨R(w, z) u, v⟩` follows by the algebra that
`AlgebraicCurvature.pair_symm_of_bianchi` does on components. **Not attempted, no cost claimed**
(`ERRATUM 246`). ⚠ By entry 74, later the same day, all three are proved:
`CurvatureSkew.curvEndo_inner_skew`, `CurvatureSkew.ricci_symm` and
`CurvatureSkew.inner_curvEndo_pair_symm`, and for a `C²` metric `CurvatureSkew.riemann_inner_skew`,
`CurvatureSkew.ricci_metric_symm` and `CurvatureSkew.riemann_inner_pair_symm`; the sentence is
kept as written (`ERRATUM 94`).

**NO SECOND BIANCHI IDENTITY** — the differential one,
`(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0` — which needs the covariant derivative of the
curvature, an object not defined here or in the pinned Mathlib.

**ONLY TORSION-FREE CONNECTIONS.** For a connection with torsion the cyclic sum is an expression
in the torsion and its derivative, and nothing about it is stated.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]`, a `ChartedSpace H M` with model `I` and
`[IsManifold I 3 M]` throughout (Mathlib's Jacobi identity wants a `C³` manifold and `C²` fields);
`[FiniteDimensional ℝ E]` from `covApply_sub_covApply_eventually` on (Mathlib's hypothesis for
`torsion`); `[IsLocallyC1 cov]` from `cov_covApply_sub` on;
`[RiemannianBundle (fun x ↦ TangentSpace I x)]` and
`[IsContMDiffRiemannianBundle I 2 E (TangentSpace I)]` for `riemann_cyclic` alone, where
`leviCivita` needs them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureBianchi

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial CurvatureTensor
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

/-- The bracket of two `C²` fields is differentiable at the point. -/
theorem mdiffAt_mlieBracket {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    MDiffAt (T% (mlieBracket I Y Z)) x := by
  haveI : IsManifold I (2 + 1) M := inferInstanceAs (IsManifold I 3 M)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hbr : CMDiffAt 1 (T% (mlieBracket I Y Z)) x :=
    ContMDiffAt.mlieBracket_vectorField (m := 1) (n := 2) hY hZ
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  exact hbr.mdifferentiableAt one_ne_zero

variable [FiniteDimensional ℝ E] (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- For a torsion-free connection, `∇_Y Z − ∇_Z Y = [Y, Z]` as sections near a point where
`Y` and `Z` are `C²`. -/
theorem covApply_sub_covApply_eventually (h : cov.torsion = 0)
    {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    ∀ᶠ y in 𝓝 x, (covApply cov Y Z - covApply cov Z Y) y = mlieBracket I Y Z y := by
  filter_upwards [eventually_mdiffAt_of_cmdiffAt hY, eventually_mdiffAt_of_cmdiffAt hZ]
    with y hYy hZy
  simp only [Pi.sub_apply, covApply_apply]
  exact (cov.torsion_eq_zero_iff.mp h) hYy hZy

variable [IsLocallyC1 cov]

/-- For a torsion-free connection, `∇_X ∇_Y Z − ∇_X ∇_Z Y = ∇_X [Y, Z]` at a point where
`Y, Z` are `C²`. -/
theorem cov_covApply_sub (h : cov.torsion = 0) {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    cov (covApply cov Y Z) x (X x) - cov (covApply cov Z Y) x (X x)
      = cov (mlieBracket I Y Z) x (X x) := by
  have hYx : MDiffAt (T% Y) x := hY.mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have h1 := mdiffAt_covApply' cov hZ hYx
  have h2 := mdiffAt_covApply' cov hY hZx
  have hsub := mdifferentiableAt_sub_section h1 h2
  have hbr := mdiffAt_mlieBracket hY hZ
  have e := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hsub hbr Filter.univ_mem
    (covApply_sub_covApply_eventually cov h hY hZ)
  have hneg : cov (- covApply cov Z Y) x = - cov (covApply cov Z Y) x := by
    have := cov.isCovariantDerivativeOnUniv.smul_const (-1 : ℝ) h2
    simpa using this
  have hadd := cov.isCovariantDerivativeOnUniv.add h1 (mdifferentiableAt_neg_section h2)
  rw [sub_eq_add_neg] at e
  rw [hadd, hneg] at e
  have := congrArg (fun L ↦ L (X x)) e
  simpa [sub_eq_add_neg] using this

/-- **THE FIRST BIANCHI IDENTITY** for a torsion-free connection that is locally `C¹`:
`R(X, Y)Z + R(Y, Z)X + R(Z, X)Y = 0` at every point where `X, Y, Z` are `C²`. -/
theorem curvAux_cyclic (h : cov.torsion = 0) {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    curvAux cov X Y Z x + curvAux cov Y Z X x + curvAux cov Z X Y x = 0 := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hX2 : CMDiffAt (minSmoothness ℝ 2) (T% X) x := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact hX
  have hY2 : CMDiffAt (minSmoothness ℝ 2) (T% Y) x := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact hY
  have hZ2 : CMDiffAt (minSmoothness ℝ 2) (T% Z) x := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact hZ
  have hXx : MDiffAt (T% X) x := hX.mdifferentiableAt two_ne_zero
  have hYx : MDiffAt (T% Y) x := hY.mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  -- the three second-derivative differences
  have a1 := cov_covApply_sub cov h (X := X) hY hZ
  have a2 := cov_covApply_sub cov h (X := Y) hZ hX
  have a3 := cov_covApply_sub cov h (X := Z) hX hY
  -- torsion-freeness on the pairs (X, [Y, Z]) and cyclic
  have t1 := (cov.torsion_eq_zero_iff.mp h) hXx (mdiffAt_mlieBracket hY hZ)
  have t2 := (cov.torsion_eq_zero_iff.mp h) hYx (mdiffAt_mlieBracket hZ hX)
  have t3 := (cov.torsion_eq_zero_iff.mp h) hZx (mdiffAt_mlieBracket hX hY)
  -- Jacobi
  have j := leibniz_identity_mlieBracket_apply (I := I) hX2 hY2 hZ2
  have s1 : mlieBracket I (mlieBracket I X Y) Z x = - mlieBracket I Z (mlieBracket I X Y) x :=
    mlieBracket_swap_apply
  have s2 : mlieBracket I Y (mlieBracket I X Z) x = - mlieBracket I Y (mlieBracket I Z X) x := by
    rw [mlieBracket_swap (V := X) (W := Z)]
    have hneg : mlieBracket I Y (-mlieBracket I Z X) x
        = - mlieBracket I Y (mlieBracket I Z X) x := by
      have := mlieBracket_const_smul_right (I := I) (V := Y) (W := mlieBracket I Z X)
        (c := (-1 : ℝ)) (mdiffAt_mlieBracket hZ hX)
      simpa using this
    rw [hneg]
  simp only [curvAux]
  -- unfold to the sum and close by linear arithmetic in the tangent space
  have key : (cov (covApply cov Y Z) x (X x) - cov (covApply cov X Z) x (Y x)
        - cov Z x (mlieBracket I X Y x))
      + (cov (covApply cov Z X) x (Y x) - cov (covApply cov Y X) x (Z x)
        - cov X x (mlieBracket I Y Z x))
      + (cov (covApply cov X Y) x (Z x) - cov (covApply cov Z Y) x (X x)
        - cov Y x (mlieBracket I Z X x))
      = (cov (mlieBracket I Y Z) x (X x) - cov X x (mlieBracket I Y Z x))
      + (cov (mlieBracket I Z X) x (Y x) - cov Y x (mlieBracket I Z X x))
      + (cov (mlieBracket I X Y) x (Z x) - cov Z x (mlieBracket I X Y x)) := by
    rw [← a1, ← a2, ← a3]; abel
  rw [key, t1, t2, t3]
  rw [j, s1, s2]
  abel

/-- **THE FIRST BIANCHI IDENTITY ON THE CURVATURE ENDOMORPHISM**: for a torsion-free connection
that is locally `C¹`, `R(u, v) w + R(v, w) u + R(w, u) v = 0` at every point. -/
theorem curvEndo_cyclic (h : cov.torsion = 0) (x : M) (u v w : TangentSpace I x) :
    curvEndo cov x u v w + curvEndo cov x v w u + curvEndo cov x w u v = 0 := by
  simp only [curvEndo_apply_extend]
  exact curvAux_cyclic cov h (cmdiffAt_extend x u) (cmdiffAt_extend x v) (cmdiffAt_extend x w)

/-- **THE ANTISYMMETRIC PART OF THE RICCI FORM IS A TRACE OF THE CURVATURE**: for a torsion-free
connection that is locally `C¹`, `Ric(w, z) − Ric(z, w) = −tr R(w, z)`. -/
theorem ricci_sub_swap (h : cov.torsion = 0) (x : M) (w z : TangentSpace I x) :
    RicciScalar.ricci cov x w z - RicciScalar.ricci cov x z w
      = - LinearMap.trace ℝ (TangentSpace I x)
          (curvEndo cov x w z : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
  have hL : RicciScalar.curvLeft cov x w z - RicciScalar.curvLeft cov x z w
      = - (curvEndo cov x w z : TangentSpace I x →ₗ[ℝ] TangentSpace I x) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.neg_apply, RicciScalar.curvLeft_apply,
      ContinuousLinearMap.coe_coe]
    have hc := curvEndo_cyclic cov h x v w z
    rw [curvEndo_swap cov x v z, ContinuousLinearMap.neg_apply]
    -- `hc : R(v, w) z + R(w, z) v + R(z, v) w = 0`
    have : curvEndo cov x v w z - - curvEndo cov x z v w = - curvEndo cov x w z v := by
      rw [sub_neg_eq_add]; exact eq_neg_of_add_eq_zero_left (by rw [← hc]; abel)
    exact this
  simp only [RicciScalar.ricci]
  rw [← map_sub, hL, map_neg]

section Metric

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- **THE FIRST BIANCHI IDENTITY FOR THE CURVATURE OF A `C²` METRIC.** -/
theorem riemann_cyclic (x : M) (u v w : TangentSpace I x) :
    LeviCivitaRegular.riemann I x u v w + LeviCivitaRegular.riemann I x v w u
      + LeviCivitaRegular.riemann I x w u v = 0 :=
  curvEndo_cyclic _ leviCivita_torsion x u v w

end Metric

end CurvatureBianchi
