import LeviCivitaRegular

/-!
# The curvature of a Euclidean space vanishes

`LeviCivitaRegular` gave the estate the Riemann, Ricci and scalar curvature of a `C²` metric, and
said in its fence that not even the flat example was proved. This file is that example, the one
sanity theorem a definition of curvature has to pass: **on a real inner product space with its
constant metric, the curvature of the Levi-Civita connection is zero** (`riemann_flat`), and so
are its Ricci and scalar curvature (`ricci_flat`, `scalar_flat`).

The proof is the symmetry of the second derivative. On a vector space the Levi-Civita connection
of the constant metric is the ordinary derivative (`KoszulManifold.leviCivita_eq_flatCov`), so
the curvature expression `∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` is
`D(DZ(Y))(X) − D(DZ(X))(Y) − DZ(DY(X) − DX(Y))`; the product rule for a linear-map-valued
function applied to a vector (`fderiv_clm_apply`) expands the first two terms into a second
derivative and a first-order term, the first-order terms cancel against the bracket, and what is
left is `D²Z(X, Y) − D²Z(Y, X)`, zero by Mathlib's `ContDiffAt.isSymmSndFDerivAt` for a `C²`
map (`curvAux_flatCov`). Passing from `leviCivita` to `flatCov` inside the expression uses that
the two agree on every section differentiable at a point and the locality of the flat
connection (`curvAux_leviCivita_eq_flatCov`).

## What is proved

**`cmdiffAt_section_iff`** — on a vector space, a section of the tangent bundle is `C^n` at a
point as a section exactly when it is as a map (the `C^n` form of
`LeviCivitaFlat.mdiffAt_section_iff`).

**`mlieBracket_eq`** — the manifold bracket on a vector space is `DY(X) − DX(Y)`.

**`curvAux_flatCov`** — **THE FLAT CONNECTION HAS ZERO CURVATURE** on every real inner product
space, for `X, Y` differentiable and `Z` of class `C²` at the point.

**`curvAux_leviCivita_eq_flatCov`** — on a finite-dimensional complete inner product space, the
curvature expression of the Levi-Civita connection of the constant metric is that of the flat
connection, at every point where the three sections are `C²`.

**`riemann_flat`**, **`ricci_flat`**, **`scalar_flat`** — **THE CURVATURE OF A EUCLIDEAN SPACE
VANISHES**: `LeviCivitaRegular.riemann`, `ricci` and `scalar` are zero for the constant metric.

## What is NOT here

**NO NON-FLAT EXAMPLE.** No sphere, no hyperbolic space, no surface: the estate has no metric
other than a constant one on a vector space and the abstract `RiemannianBundle` on a manifold,
so no curvature has been computed that is not zero. The converse — a metric with zero curvature
is locally flat — is not stated.

**NO STATEMENT ABOUT A NON-CONSTANT METRIC ON `F`.** `KoszulVectorSpace` builds the Levi-Civita
connection of a metric on `F` varying with the point; its curvature is not computed here, and
`LeviCivitaRegular.riemann` does not see it, since `riemann` is stated for the `RiemannianBundle`
instance on the tangent bundle, which on `F` is the constant one.

**ONLY THE CONSTANT METRIC'S `RiemannianBundle` INSTANCE.** `riemann_flat` is a statement about
Mathlib's instance `riemannianMetricVectorSpace`, and the `IsContMDiffRiemannianBundle` instance
it needs is Mathlib's, from that metric being `C^ω`.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `cmdiffAt_section_iff`,
`mlieBracket_eq` and `curvAux_flatCov` take `[NormedAddCommGroup F]` and
`[InnerProductSpace ℝ F]` only — no finite dimension, no completeness; section `Metric` adds
`[FiniteDimensional ℝ F]` and `[CompleteSpace F]`, the hypotheses of `leviCivita` and of the
curvature tensor, with the tangent bundle registered locally as a `C²` bundle
(`CurvatureTensor.contMDiffVectorBundle_two`).

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FlatCurvature

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial CurvatureTensor
  LeviCivitaFlat
open scoped Bundle ContDiff Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- On a vector space, a section of the tangent bundle is `C^n` at a point as a section exactly
when it is as a map. -/
theorem cmdiffAt_section_iff {n : WithTop ℕ∞} {σ : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F} :
    ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) n (fun y ↦ TotalSpace.mk' F y (σ y)) x ↔
      ContDiffAt ℝ n (σ : F → F) x := by
  rw [contMDiffAt_section, contMDiffAt_iff_contDiffAt]
  simp

/-- The Lie bracket on a vector space, at a point: `[X, Y](x) = DY(x)(X x) − DX(x)(Y x)`. -/
theorem mlieBracket_eq (X Y : Π x : F, TangentSpace 𝓘(ℝ, F) x) (x : F) :
    mlieBracket 𝓘(ℝ, F) X Y x = fderiv ℝ (Y : F → F) x (X x) - fderiv ℝ (X : F → F) x (Y x) := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin, lieBracketWithin_univ]
  rfl

/-- **THE FLAT CONNECTION HAS ZERO CURVATURE**: on a vector space, for `X, Y` differentiable and
`Z` of class `C²` at `x`, `∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z = 0` for the ordinary derivative —
the symmetry of the second derivative. -/
theorem curvAux_flatCov {X Y Z : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F}
    (hX : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (X y)) x)
    (hY : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) (fun y ↦ TotalSpace.mk' F y (Y y)) x)
    (hZ : ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (Z y)) x) :
    curvAux (flatCov (F := F)) X Y Z x = 0 := by
  rw [mdiffAt_section_iff] at hX hY
  rw [cmdiffAt_section_iff] at hZ
  have hZ1 : DifferentiableAt ℝ (fderiv ℝ (Z : F → F)) x :=
    (hZ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have e1 : fderiv ℝ (fun y ↦ fderiv ℝ (Z : F → F) y (Y y)) x
      = (fderiv ℝ (Z : F → F) x).comp (fderiv ℝ (Y : F → F) x)
        + (fderiv ℝ (fderiv ℝ (Z : F → F)) x).flip (Y x) := fderiv_clm_apply hZ1 hY
  have e2 : fderiv ℝ (fun y ↦ fderiv ℝ (Z : F → F) y (X y)) x
      = (fderiv ℝ (Z : F → F) x).comp (fderiv ℝ (X : F → F) x)
        + (fderiv ℝ (fderiv ℝ (Z : F → F)) x).flip (X x) := fderiv_clm_apply hZ1 hX
  have hsymm : IsSymmSndFDerivAt ℝ (Z : F → F) x :=
    hZ.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])
  have h1 : fderiv ℝ (fun y ↦ fderiv ℝ (Z : F → F) y (Y y)) x (X x)
      = fderiv ℝ (Z : F → F) x (fderiv ℝ (Y : F → F) x (X x))
        + fderiv ℝ (fderiv ℝ (Z : F → F)) x (X x) (Y x) := by
    rw [e1]; rfl
  have h2 : fderiv ℝ (fun y ↦ fderiv ℝ (Z : F → F) y (X y)) x (Y x)
      = fderiv ℝ (Z : F → F) x (fderiv ℝ (X : F → F) x (Y x))
        + fderiv ℝ (fderiv ℝ (Z : F → F)) x (Y x) (X x) := by
    rw [e2]; rfl
  have h3 : fderiv ℝ (Z : F → F) x (fderiv ℝ (Y : F → F) x (X x) - fderiv ℝ (X : F → F) x (Y x))
      = fderiv ℝ (Z : F → F) x (fderiv ℝ (Y : F → F) x (X x))
        - fderiv ℝ (Z : F → F) x (fderiv ℝ (X : F → F) x (Y x)) := map_sub _ _ _
  have hs0 : fderiv ℝ (fderiv ℝ (Z : F → F)) x (X x) (Y x)
      - fderiv ℝ (fderiv ℝ (Z : F → F)) x (Y x) (X x) = 0 := sub_eq_zero.2 (hsymm.eq _ _)
  have e : fderiv ℝ (fun y ↦ fderiv ℝ (Z : F → F) y (Y y)) x (X x)
      - fderiv ℝ (fun y ↦ fderiv ℝ (Z : F → F) y (X y)) x (Y x)
      - fderiv ℝ (Z : F → F) x (fderiv ℝ (Y : F → F) x (X x) - fderiv ℝ (X : F → F) x (Y x))
      = (fderiv ℝ (Z : F → F) x (fderiv ℝ (Y : F → F) x (X x))
          + fderiv ℝ (fderiv ℝ (Z : F → F)) x (X x) (Y x))
        - (fderiv ℝ (Z : F → F) x (fderiv ℝ (X : F → F) x (Y x))
          + fderiv ℝ (fderiv ℝ (Z : F → F)) x (Y x) (X x))
        - (fderiv ℝ (Z : F → F) x (fderiv ℝ (Y : F → F) x (X x))
          - fderiv ℝ (Z : F → F) x (fderiv ℝ (X : F → F) x (Y x))) :=
    congrArg₂ (· - ·) (congrArg₂ (· - ·) h1 h2) h3
  simp only [curvAux, flatCov_apply, mlieBracket_eq]
  rw [show covApply flatCov Y Z = fun y ↦ fderiv ℝ (Z : F → F) y (Y y) from rfl,
    show covApply flatCov X Z = fun y ↦ fderiv ℝ (Z : F → F) y (X y) from rfl]
  refine e.trans ?_
  refine Eq.trans ?_ hs0
  abel

section Metric

variable [FiniteDimensional ℝ F] [CompleteSpace F]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

/-- On a Euclidean space, the curvature expression of the Levi-Civita connection is that of the
flat connection, at every point where the three sections are `C²`. -/
theorem curvAux_leviCivita_eq_flatCov {X Y Z : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F}
    (hX : ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (X y)) x)
    (hY : ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (Y y)) x)
    (hZ : ContMDiffAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F)) 2 (fun y ↦ TotalSpace.mk' F y (Z y)) x) :
    curvAux (leviCivita (I := 𝓘(ℝ, F)) (M := F)) X Y Z x = curvAux (flatCov (F := F)) X Y Z x := by
  have hXx := hX.mdifferentiableAt two_ne_zero
  have hYx := hY.mdifferentiableAt two_ne_zero
  have hZx := hZ.mdifferentiableAt two_ne_zero
  -- the inner derivatives agree near `x`
  have eYZ : covApply (leviCivita (I := 𝓘(ℝ, F)) (M := F)) Y Z =ᶠ[𝓝 x] covApply flatCov Y Z := by
    filter_upwards [CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hZ] with y hy
    simp only [covApply_apply]
    rw [leviCivita_eq_flatCov hy]
  have eXZ : covApply (leviCivita (I := 𝓘(ℝ, F)) (M := F)) X Z =ᶠ[𝓝 x] covApply flatCov X Z := by
    filter_upwards [CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hZ] with y hy
    simp only [covApply_apply]
    rw [leviCivita_eq_flatCov hy]
  have h1 := mdiffAt_covApply' (leviCivita (I := 𝓘(ℝ, F)) (M := F)) hZ hYx
  have h2 := mdiffAt_covApply' (leviCivita (I := 𝓘(ℝ, F)) (M := F)) hZ hXx
  have h1' : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
      (fun y ↦ TotalSpace.mk' F y (covApply (flatCov (F := F)) Y Z y)) x :=
    h1.congr_of_eventuallyEq (eYZ.mono fun y hy ↦ by simp [hy])
  have h2' : MDifferentiableAt 𝓘(ℝ, F) (𝓘(ℝ, F).prod 𝓘(ℝ, F))
      (fun y ↦ TotalSpace.mk' F y (covApply (flatCov (F := F)) X Z y)) x :=
    h2.congr_of_eventuallyEq (eXZ.mono fun y hy ↦ by simp [hy])
  simp only [curvAux]
  rw [leviCivita_eq_flatCov h1, leviCivita_eq_flatCov h2, leviCivita_eq_flatCov hZx,
    (flatCov (F := F)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq h1 h1' Filter.univ_mem eYZ,
    (flatCov (F := F)).isCovariantDerivativeOnUniv.congr_of_eventuallyEq h2 h2' Filter.univ_mem eXZ]

/-- **THE CURVATURE OF A EUCLIDEAN SPACE VANISHES**: `riemann = 0` for the constant metric. -/
theorem riemann_flat (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    LeviCivitaRegular.riemann 𝓘(ℝ, F) x v w = 0 := by
  ext z
  have hX := cmdiffAt_extend (I := 𝓘(ℝ, F)) x v
  have hY := cmdiffAt_extend (I := 𝓘(ℝ, F)) x w
  have hZ := cmdiffAt_extend (I := 𝓘(ℝ, F)) x z
  have e : LeviCivitaRegular.riemann 𝓘(ℝ, F) x v w z
      = curvAux (leviCivita (I := 𝓘(ℝ, F)) (M := F)) (extend F v) (extend F w) (extend F z) x :=
    curvEndo_apply_extend _ x v w z
  rw [e, curvAux_leviCivita_eq_flatCov hX hY hZ,
    curvAux_flatCov (hX.mdifferentiableAt two_ne_zero) (hY.mdifferentiableAt two_ne_zero) hZ]
  rfl

/-- The Ricci curvature of a Euclidean space vanishes. -/
theorem ricci_flat (x : F) (w z : TangentSpace 𝓘(ℝ, F) x) :
    LeviCivitaRegular.ricci 𝓘(ℝ, F) x w z = 0 := by
  have : RicciScalar.curvLeft (leviCivita (I := 𝓘(ℝ, F)) (M := F)) x w z = 0 := by
    ext v
    simp only [RicciScalar.curvLeft_apply, LinearMap.zero_apply]
    have := congrArg (fun L ↦ L z) (riemann_flat x v w)
    simpa using this
  simp only [LeviCivitaRegular.ricci, RicciScalar.ricci, this, map_zero]

/-- The scalar curvature of a Euclidean space vanishes. -/
theorem scalar_flat (x : F) : LeviCivitaRegular.scalar 𝓘(ℝ, F) x = 0 := by
  simp only [LeviCivitaRegular.scalar, RicciScalar.scalar]
  exact Finset.sum_eq_zero fun i _ ↦ ricci_flat x _ _

end Metric

end FlatCurvature
