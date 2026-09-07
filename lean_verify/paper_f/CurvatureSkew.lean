import CurvatureBianchi

/-!
# The curvature of a metric is skew, its Ricci form is symmetric, and it has the pair symmetry

`CurvatureBianchi` reduced the symmetry of the Ricci form of a metric to one statement: that the
curvature operator `R(w, z)` is traceless, which for a metric-compatible connection is its
skew-symmetry `⟨R(u, v) w, z⟩ = −⟨R(u, v) z, w⟩`. This file proves that skew-symmetry and takes
what follows. **The curvature of a metric-compatible, locally `C¹` connection is skew in its last
two slots** (`curvAux_inner_skew` on `C²` sections, `curvEndo_inner_skew` on the endomorphism),
so **`R(v, w)` is traceless** (`trace_curvEndo`), so **the Ricci form of a torsion-free
metric-compatible connection is symmetric** (`ricci_symm`), and with the first Bianchi identity
**the pair symmetry `⟨R(u, v) w, z⟩ = ⟨R(w, z) u, v⟩`** holds (`inner_curvEndo_pair_symm`). For the
Levi-Civita connection of a `C²` metric these are `riemann_inner_skew`, `ricci_metric_symm` and
`riemann_inner_pair_symm`: **the Riemann curvature of a metric has all four classical symmetries,
and its Ricci curvature is a symmetric form.**

The skew-symmetry is metric compatibility differentiated twice. Compatibility says
`Y⟨Z, W⟩ = ⟨∇_Y Z, W⟩ + ⟨Z, ∇_Y W⟩` at every point where `Z, W` are differentiable, so as functions
near a point where they are `C²` (`extDerivFun_inner_eventually`); differentiating again along `v`,
`v(Y⟨Z, W⟩) = ⟨∇ᵥ∇_Y Z, W⟩ + ⟨∇_Y Z, ∇ᵥW⟩ + ⟨∇ᵥZ, ∇_Y W⟩ + ⟨Z, ∇ᵥ∇_Y W⟩`
(`extDerivFun_extDerivFun_inner`). Antisymmetrising in `X, Y` kills the two cross terms, and
`BracketDerivation`'s `[X, Y]f = X(Yf) − Y(Xf)` for the `C²` function `f = ⟨Z, W⟩`, with
compatibility once more in the direction `[X, Y]`, leaves `⟨R(X, Y)Z, W⟩ + ⟨Z, R(X, Y)W⟩ = 0`.
The trace vanishes because `⟨eᵢ, R eᵢ⟩ = −⟨eᵢ, R eᵢ⟩` in an orthonormal basis
(`LinearMap.trace_eq_sum_inner`); the pair symmetry is the classical sum of four Bianchi
identities, closed by `linarith` once the fourteen instances of the three symmetries are in `ℝ`.

## What is proved

**`extDerivFun_congr`** — the exterior derivative of a scalar function at a point depends only on
the function near the point.

**`extDerivFun_inner_apply`**, **`extDerivFun_inner_eventually`** — compatibility, at a point and
as functions near a point.

**`extDerivFun_extDerivFun_inner`** — **the second derivative of the metric along two fields**,
the four-term formula above, for `Y, Z, W` of class `C²`.

**`curvAux_inner_skew`**, **`curvEndo_inner_skew`**, **`inner_curvEndo_skew`** — **THE CURVATURE
OF A METRIC-COMPATIBLE CONNECTION IS SKEW**: `⟨R(u, v) w, z⟩ + ⟨w, R(u, v) z⟩ = 0`.

**`trace_curvEndo`** — **`R(v, w)` is traceless.**

**`ricci_symm`** — **THE RICCI FORM OF A TORSION-FREE METRIC-COMPATIBLE CONNECTION IS SYMMETRIC**,
through `CurvatureBianchi.ricci_sub_swap`.

**`inner_curvEndo_swap`**, **`inner_curvEndo_cyclic`**, **`inner_curvEndo_pair_symm`** — **THE PAIR
SYMMETRY** `⟨R(u, v) w, z⟩ = ⟨R(w, z) u, v⟩`, from the first Bianchi identity and the two
antisymmetries.

**`ricci_metric_symm`**, **`riemann_inner_pair_symm`**, **`riemann_inner_skew`** — the three for
the curvature of a `C²` metric.

## What is NOT here

**NO BRIDGE TO `AlgebraicCurvature.IsAlgCurv`.** With the two antisymmetries, the pair symmetry
and the first Bianchi identity, the components `⟨R(eₐ, e_b) e_c, e_d⟩` of `riemann` in an
orthonormal frame satisfy the four clauses of `IsAlgCurv` on `Fin n`; that instance is not
written, because the choice of the frame — the model space's basis, an orthonormal basis of the
tangent space, or the chart's — is a modelling decision that belongs to the author, and
`AlgebraicCurvature.ricci` and `scal` would then have to be shown to agree with
`LeviCivitaRegular.ricci` and `scalar` (DECISIONS NEEDED).

**NO SECOND BIANCHI IDENTITY, NO SECTIONAL CURVATURE, NO EINSTEIN TENSOR, NO EXAMPLE**, as in
`CurvatureBianchi` and `LeviCivitaRegular`; the Einstein tensor `Ric − ½ S g` is now writable,
since `Ric` is symmetric, and is not written.

**ONLY `C²` METRICS AND `C²` SECTIONS**, as everywhere since `KoszulRegular`; the skew-symmetry
on sections asks all four of `X, Y, Z, W` to be `C²` at the point, because the bracket rule
needs `X, Y` differentiable and the second derivative of `⟨Z, W⟩` needs it `C²`.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `extDerivFun_congr` takes only a
`ChartedSpace H M` with model `I`; `extDerivFun_inner_apply` and `extDerivFun_inner_eventually`
add `[IsManifold I 3 M]` and `[RiemannianBundle (fun x ↦ TangentSpace I x)]` with
`IsMetricCompatible cov` as a hypothesis, no smoothness of the metric; from
`extDerivFun_extDerivFun_inner` on, `[IsContMDiffRiemannianBundle I 2 E (TangentSpace I)]` and
`[IsLocallyC1 cov]`, and `[CompleteSpace E]` from `curvAux_inner_skew` on (`BracketDerivation`);
`[FiniteDimensional ℝ E]` from `curvEndo_inner_skew` on (`curvEndo`, the trace); torsion-freeness
as a hypothesis where the Bianchi identity enters; the metric instances of `LeviCivitaRegular`
in section `Metric`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureSkew

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial CurvatureTensor
  LeviCivitaUnique
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The exterior derivative of a scalar function at a point depends only on the function near
the point. -/
theorem extDerivFun_congr {f g : M → ℝ} {x : M} (h : f =ᶠ[𝓝 x] g) :
    extDerivFun (I := I) f x = extDerivFun (I := I) g x := by
  ext v
  rw [extDerivFun_apply, extDerivFun_apply, h.mfderiv_eq]
  rfl

variable [IsManifold I 3 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Compatibility in `extDerivFun` form: `v⟨Z, W⟩ = ⟨∇ᵥZ, W⟩ + ⟨Z, ∇ᵥW⟩` at a point where `Z, W`
are differentiable. -/
theorem extDerivFun_inner_apply (hc : IsMetricCompatible cov) {Z W : Π x : M, TangentSpace I x}
    {y : M} (hZ : MDiffAt (T% Z) y) (hW : MDiffAt (T% W) y) (v : TangentSpace I y) :
    extDerivFun (I := I) (fun y ↦ ⟪Z y, W y⟫) y v = ⟪cov Z y v, W y⟫ + ⟪Z y, cov W y v⟫ :=
  hc hZ hW v

/-- Near `x`, `Y⟨Z, W⟩ = ⟨∇_Y Z, W⟩ + ⟨Z, ∇_Y W⟩` as functions, for `Z, W` of class `C²` at `x`. -/
theorem extDerivFun_inner_eventually (hc : IsMetricCompatible cov)
    {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt 2 (T% Z) x) (hW : CMDiffAt 2 (T% W) x) :
    (fun y ↦ extDerivFun (I := I) (fun y ↦ ⟪Z y, W y⟫) y (Y y)) =ᶠ[𝓝 x]
      (fun y ↦ ⟪covApply cov Y Z y, W y⟫) + (fun y ↦ ⟪Z y, covApply cov Y W y⟫) := by
  filter_upwards [eventually_mdiffAt_of_cmdiffAt hZ, eventually_mdiffAt_of_cmdiffAt hW]
    with y hZy hWy
  simp only [Pi.add_apply]
  exact extDerivFun_inner_apply cov hc hZy hWy (Y y)

variable [CompleteSpace E] [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsLocallyC1 cov]

omit [CompleteSpace E] in
/-- **THE SECOND DERIVATIVE OF THE METRIC ALONG TWO FIELDS**: `v(Y⟨Z, W⟩) = ⟨∇ᵥ ∇_Y Z, W⟩ +
⟨∇_Y Z, ∇ᵥ W⟩ + ⟨∇ᵥ Z, ∇_Y W⟩ + ⟨Z, ∇ᵥ ∇_Y W⟩` at a point where `Y, Z, W` are `C²`. -/
theorem extDerivFun_extDerivFun_inner (hc : IsMetricCompatible cov)
    {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) (hW : CMDiffAt 2 (T% W) x)
    (v : TangentSpace I x) :
    extDerivFun (I := I) (fun y ↦ extDerivFun (I := I) (fun y ↦ ⟪Z y, W y⟫) y (Y y)) x v
      = ⟪cov (covApply cov Y Z) x v, W x⟫ + ⟪covApply cov Y Z x, cov W x v⟫
        + (⟪cov Z x v, covApply cov Y W x⟫ + ⟪Z x, cov (covApply cov Y W) x v⟫) := by
  have hYx : MDiffAt (T% Y) x := hY.mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have hWx : MDiffAt (T% W) x := hW.mdifferentiableAt two_ne_zero
  have h1 := mdiffAt_covApply' cov hZ hYx
  have h2 := mdiffAt_covApply' cov hW hYx
  have heq := extDerivFun_inner_eventually cov hc (Y := Y) hZ hW
  rw [extDerivFun_congr heq,
    extDerivFun_apply_add (mdiffAt_inner h1 hWx) (mdiffAt_inner hZx h2),
    extDerivFun_inner_apply cov hc h1 hWx, extDerivFun_inner_apply cov hc hZx h2]

/-- **THE CURVATURE OF A METRIC-COMPATIBLE CONNECTION IS SKEW**: `⟨R(X, Y)Z, W⟩ + ⟨Z, R(X, Y)W⟩ = 0`
at every point where `X, Y, Z, W` are `C²`. -/
theorem curvAux_inner_skew (hc : IsMetricCompatible cov)
    {X Y Z W : Π x : M, TangentSpace I x} {x : M} (hX : CMDiffAt 2 (T% X) x)
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) (hW : CMDiffAt 2 (T% W) x) :
    ⟪curvAux cov X Y Z x, W x⟫ + ⟪Z x, curvAux cov X Y W x⟫ = 0 := by
  have hXx : MDiffAt (T% X) x := hX.mdifferentiableAt two_ne_zero
  have hYx : MDiffAt (T% Y) x := hY.mdifferentiableAt two_ne_zero
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have hWx : MDiffAt (T% W) x := hW.mdifferentiableAt two_ne_zero
  have hg : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ⟪Z y, W y⟫) x :=
    KoszulRegular.contMDiffAt_inner le_rfl hZ hW
  have hbr := BracketDerivation.extDerivFun_apply_mlieBracket hg hXx hYx
  rw [extDerivFun_inner_apply cov hc hZx hWx, extDerivFun_extDerivFun_inner cov hc hY hZ hW,
    extDerivFun_extDerivFun_inner cov hc hX hZ hW] at hbr
  simp only [curvAux, inner_sub_left, inner_sub_right, covApply_apply] at hbr ⊢
  have c1 := real_inner_comm (cov Z x (Y x)) (cov W x (X x))
  have c2 := real_inner_comm (cov Z x (X x)) (cov W x (Y x))
  linarith

/-- The same on the curvature endomorphism: `⟨R(u, v) w, z⟩ + ⟨w, R(u, v) z⟩ = 0`. -/
theorem curvEndo_inner_skew [FiniteDimensional ℝ E] (hc : IsMetricCompatible cov) (x : M)
    (u v w z : TangentSpace I x) :
    ⟪curvEndo cov x u v w, z⟫ + ⟪w, curvEndo cov x u v z⟫ = 0 := by
  simp only [curvEndo_apply_extend]
  have := curvAux_inner_skew cov hc (cmdiffAt_extend x u) (cmdiffAt_extend x v)
    (cmdiffAt_extend x w) (cmdiffAt_extend x z)
  simpa [extend_apply_self] using this

/-- **THE CURVATURE ENDOMORPHISM OF A METRIC-COMPATIBLE CONNECTION IS TRACELESS.** -/
theorem trace_curvEndo [FiniteDimensional ℝ E] (hc : IsMetricCompatible cov) (x : M)
    (v w : TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x)
      (curvEndo cov x v w : TangentSpace I x →ₗ[ℝ] TangentSpace I x) = 0 := by
  haveI := KoszulManifold.finDimTangent (I := I) x
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ (TangentSpace I x))]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h := curvEndo_inner_skew cov hc x v w (stdOrthonormalBasis ℝ (TangentSpace I x) i)
    (stdOrthonormalBasis ℝ (TangentSpace I x) i)
  rw [real_inner_comm] at h
  simp only [ContinuousLinearMap.coe_coe]
  linarith

section Symmetric

variable [FiniteDimensional ℝ E]

/-- **THE RICCI FORM OF A TORSION-FREE METRIC-COMPATIBLE CONNECTION IS SYMMETRIC.** -/
theorem ricci_symm (h : cov.torsion = 0) (hc : IsMetricCompatible cov) (x : M)
    (w z : TangentSpace I x) :
    RicciScalar.ricci cov x w z = RicciScalar.ricci cov x z w := by
  have e := CurvatureBianchi.ricci_sub_swap cov h x w z
  rw [trace_curvEndo cov hc, neg_zero, sub_eq_zero] at e
  exact e

/-- Skew-symmetry in the last two slots, as an equation. -/
theorem inner_curvEndo_skew (hc : IsMetricCompatible cov) (x : M) (a b c d : TangentSpace I x) :
    ⟪curvEndo cov x a b c, d⟫ = - ⟪curvEndo cov x a b d, c⟫ := by
  have e := curvEndo_inner_skew cov hc x a b c d
  rw [real_inner_comm _ c] at e
  exact eq_neg_of_add_eq_zero_left e

omit [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- Antisymmetry in the first two slots, as an equation on pairings. -/
theorem inner_curvEndo_swap (x : M) (a b c d : TangentSpace I x) :
    ⟪curvEndo cov x a b c, d⟫ = - ⟪curvEndo cov x b a c, d⟫ := by
  rw [curvEndo_swap cov x a b, ContinuousLinearMap.neg_apply, inner_neg_left]

omit [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The first Bianchi identity, as an equation on pairings. -/
theorem inner_curvEndo_cyclic (h : cov.torsion = 0) (x : M) (a b c d : TangentSpace I x) :
    ⟪curvEndo cov x a b c, d⟫ + ⟪curvEndo cov x b c a, d⟫ + ⟪curvEndo cov x c a b, d⟫ = 0 := by
  rw [← inner_add_left, ← inner_add_left, CurvatureBianchi.curvEndo_cyclic cov h x a b c,
    inner_zero_left]

/-- **PAIR SYMMETRY OF THE CURVATURE OF A TORSION-FREE METRIC-COMPATIBLE CONNECTION**:
`⟨R(u, v) w, z⟩ = ⟨R(w, z) u, v⟩`, from the first Bianchi identity and the two skew-symmetries
by the classical sum of four cyclic identities. -/
theorem inner_curvEndo_pair_symm (h : cov.torsion = 0) (hc : IsMetricCompatible cov) (x : M)
    (u v w z : TangentSpace I x) :
    ⟪curvEndo cov x u v w, z⟫ = ⟪curvEndo cov x w z u, v⟫ := by
  have b1 := inner_curvEndo_cyclic cov h x u v w z
  have b2 := inner_curvEndo_cyclic cov h x v w z u
  have b3 := inner_curvEndo_cyclic cov h x w z u v
  have b4 := inner_curvEndo_cyclic cov h x z u v w
  have s1 := inner_curvEndo_skew cov hc x v w u z
  have s2 := inner_curvEndo_skew cov hc x w z v u
  have s3 := inner_curvEndo_skew cov hc x u v z w
  have s4 := inner_curvEndo_skew cov hc x z u w v
  have s5 := inner_curvEndo_skew cov hc x u w z v
  have s6 := inner_curvEndo_skew cov hc x v z u w
  have s7 := inner_curvEndo_skew cov hc x z v w u
  have a1 := inner_curvEndo_swap cov x u w v z
  have a2 := inner_curvEndo_swap cov x v z w u
  have a3 := inner_curvEndo_swap cov x z v u w
  linarith

end Symmetric

section Metric

variable [FiniteDimensional ℝ E]

/-- **THE RICCI CURVATURE OF A `C²` METRIC IS SYMMETRIC.** -/
theorem ricci_metric_symm (x : M) (w z : TangentSpace I x) :
    LeviCivitaRegular.ricci I x w z = LeviCivitaRegular.ricci I x z w :=
  ricci_symm _ leviCivita_torsion leviCivita_compatible x w z

/-- **PAIR SYMMETRY OF THE RIEMANN CURVATURE OF A `C²` METRIC.** -/
theorem riemann_inner_pair_symm (x : M) (u v w z : TangentSpace I x) :
    ⟪LeviCivitaRegular.riemann I x u v w, z⟫ = ⟪LeviCivitaRegular.riemann I x w z u, v⟫ :=
  inner_curvEndo_pair_symm _ leviCivita_torsion leviCivita_compatible x u v w z

/-- **THE RIEMANN CURVATURE OF A `C²` METRIC IS SKEW**: `⟨R(u, v) w, z⟩ = −⟨R(u, v) z, w⟩`. -/
theorem riemann_inner_skew (x : M) (u v w z : TangentSpace I x) :
    ⟪LeviCivitaRegular.riemann I x u v w, z⟫ = - ⟪LeviCivitaRegular.riemann I x u v z, w⟫ := by
  have h := curvEndo_inner_skew _ leviCivita_compatible x u v w z
  rw [real_inner_comm _ w] at h
  exact eq_neg_of_add_eq_zero_left h

end Metric

end CurvatureSkew
