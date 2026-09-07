import BracketDerivation

/-!
# The curvature of a `C¹` covariant derivative on the tangent bundle: tensorial in its two
directions, and a tensor in its third argument among `C²` sections

`KoszulManifold` built the Levi-Civita connection and `WALLS` §W5.1 names curvature as rung 3.
This file writes the curvature expression of any covariant derivative `∇` on the tangent bundle
that is of class `C¹` in Mathlib's sense (`ContMDiffCovariantDerivative cov 1`: `∇` of a `C²`
section is a `C¹` section), `R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z`, as a bare function
of three sections (`curvAux`), and proves the three facts that make it a tensor. **It is
tensorial in `X` and in `Y`** in Mathlib's `TensorialAt` sense, for every `C²` section `Z`
(`curvAux_tensorial₁`, `curvAux_tensorial₂`): the `df` terms of the Leibniz rule and of the
bracket's rule cancel, as in `KoszulManifold`, with one new ingredient — `∇_X Z` must be a
differentiable section, which is what the regularity class gives (`mdiffAt_covApply`). So
`TensorialAt.mkHom₂` makes `(v, w) ↦ R(v, w)Z(x)` a bilinear map on the tangent space
(`curvForm`, `curvForm_apply`), antisymmetric (`curvForm_swap`). **And in `Z` it is a tensor
among `C²` sections**: `R(X, Y)(f • Z) = f • R(X, Y)Z` for `f` of class `C²` at the point
(`curvAux_smul_Z`) and `R(X, Y)(Z + Z') = R(X, Y)Z + R(X, Y)Z'` (`curvAux_add_Z`). The Leibniz
rule in `Z` produces four `df` terms and one `d(df)` term on each side; the `df` terms cancel in
pairs and the second-order terms cancel against `[X, Y] f = X (Y f) − Y (X f)`, which is
`BracketDerivation` — the reason that file was written.

## What is proved

**`fromTangentSpace_mfderiv_eq_extDerivFun`** — the bracket rules' scalar is the exterior
derivative, by `rfl`.

**`covApply`, `covApply_apply`, `covApply_smul_left`, `covApply_add_left`** — `∇_Y Z` as a
section, linear in `Y` pointwise.

**`curvAux`** — the curvature expression at a point, as a function of three sections.

**`covApply_smul_right_eventually`** — near `x`, `∇_Y (f • Z) = df(Y) • Z + f • ∇_Y Z`, for `f`
of class `C²` at `x` and `Z` of class `C²`.

**`mdiffAt_covApply`** — under `ContMDiffCovariantDerivative cov 1`, `∇_Y Z` is differentiable at
`x` for `Z` of class `C²` and `Y` differentiable at `x` (`clm_bundle_apply` on the `C¹` section
`y ↦ ∇Z(y)` of the endomorphism bundle).

**`curvAux_tensorial₁`, `curvAux_tensorial₂`** — **tensorial in `X` and in `Y`**, for `Z` of
class `C²` and the other direction arbitrary.

**`mdifferentiableAt_extDerivFun_apply`** — `y ↦ df(V)(y)` is differentiable at `x` for `f` of
class `C²` at `x` and `V` differentiable there, by the chart identification of
`BracketDerivation`.

**`curvAux_smul_Z`, `curvAux_add_Z`** — **a tensor in `Z` among `C²` sections**: the Leibniz rule
and additivity, with `[X, Y] f = X (Y f) − Y (X f)` closing the second-order terms.

**`curvAux_swap`** — antisymmetry in the two directions.

**`curvForm`, `curvForm_apply`, `curvForm_swap`** — for each `C²` section `Z`, the bilinear
antisymmetric map `(v, w) ↦ R(v, w)Z(x)` on the tangent space, evaluating to `curvAux` on
differentiable sections (finite-dimensional model).

## What is NOT here

**THE CURVATURE 3-TENSOR, AND WHY.** `R(v, w)` as an endomorphism of the tangent space — depending
on `Z` only through `Z x` — is not built. Mathlib's `TensorialAt` asks its `smul` law for every
`f` and `σ` merely differentiable at the point, and the curvature's law in `Z` holds only for `C²`
sections (`∇_Y Z` must itself be differentiable), so the class cannot be instantiated in `Z` and
`mkHom` cannot be applied. What the 3-tensor needs is the `C²` analogue of
`TensorialAt.pointwise` — two `C²` sections with the same value at `x` give the same `R(X, Y)Z(x)`,
by a local frame with `C²` coefficients (`contMDiffAt_localFrame_coeff` is in the library) — and
that is the next object; it is not attempted here. **No cost is claimed** (`ERRATUM 246`). ⚠ By
7 September, entry 68, it is `CurvatureTensor.curvAux_congr_of_eq_Z`, and the endomorphism is
`CurvatureTensor.curvEndo`, under a local form of the regularity class (`IsLocallyC1`) and a `C³`
manifold; this file's global-`C²` lemmas are superseded there by lemmas at the point.

**NO TRACES, NO IDENTITIES BEYOND ANTISYMMETRY.** No Ricci or scalar curvature, no Bianchi
identity, no symmetry of the Riemann tensor of a metric connection.

**NOTHING ABOUT `leviCivita`.** `KoszulManifold.leviCivita` is not shown to satisfy
`ContMDiffCovariantDerivative _ 1`, so nothing here applies to it yet; that regularity — the
Koszul form's differentiable dependence on the point, for a `C²` metric — is its own object and is
not started.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, a `ChartedSpace H M` and a model `I` throughout; `[IsManifold I 2 M]` from
`covApply` on; `[CovariantDerivative.ContMDiffCovariantDerivative cov 1]` — Mathlib's class,
taken as a hypothesis on `cov` — from `mdiffAt_covApply` on; `[CompleteSpace E]` from
`curvAux_tensorial₁` on (Mathlib's hypothesis for the bracket's rules and for pulled-back fields);
`[FiniteDimensional ℝ E]` for `curvForm` (Mathlib's hypothesis for `mkHom₂`). Sections `Z` are
asked to be `C²` globally (`ContMDiff … 2`), not merely at the point, because the regularity
class is stated on `univ`. No metric anywhere in the file.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureTensorial

open Bundle Manifold VectorField FiberBundle Set
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem fromTangentSpace_mfderiv_eq_extDerivFun (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ) f x v) = extDerivFun (I := I) f x v := rfl

variable [IsManifold I 2 M]

section Basic

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- `∇_Y Z` as a section of the tangent bundle. -/
noncomputable def covApply (Y Z : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun y ↦ cov Z y (Y y)

theorem covApply_apply (Y Z : Π x : M, TangentSpace I x) (y : M) :
    covApply cov Y Z y = cov Z y (Y y) := rfl

theorem covApply_smul_left (f : M → ℝ) (X Z : Π x : M, TangentSpace I x) :
    covApply cov (f • X) Z = f • covApply cov X Z := by
  funext y
  simp [covApply, Pi.smul_apply']

theorem covApply_add_left (X X' Z : Π x : M, TangentSpace I x) :
    covApply cov (X + X') Z = covApply cov X Z + covApply cov X' Z := by
  funext y
  simp [covApply]

/-- **The curvature expression** `R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` at `x`, as a bare
function of three sections. -/
noncomputable def curvAux (X Y Z : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  cov (covApply cov Y Z) x (X x) - cov (covApply cov X Z) x (Y x) - cov Z x (mlieBracket I X Y x)

/-- Near `x`, `∇_Y (f • Z) = df(Y) • Z + f • ∇_Y Z`, for `f` of class `C²` at `x` and `Z` of
class `C²`. -/
theorem covApply_smul_right_eventually {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    {Z : Π x : M, TangentSpace I x}
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (Y : Π x : M, TangentSpace I x) :
    covApply cov Y (f • Z) =ᶠ[𝓝 x]
      (fun y ↦ extDerivFun (I := I) f y (Y y)) • Z + f • covApply cov Y Z := by
  filter_upwards [BracketDerivation.eventually_mdifferentiableAt hf] with y hfy
  have hZy : MDiffAt (T% Z) y := (hZ y).mdifferentiableAt two_ne_zero
  simp only [covApply, Pi.add_apply, Pi.smul_apply',
    cov.isCovariantDerivativeOnUniv.leibniz hZy hfy, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

/-- **Antisymmetry** of the curvature expression in its two directions. -/
theorem curvAux_swap (X Y Z : Π x : M, TangentSpace I x) (x : M) :
    curvAux cov X Y Z x = - curvAux cov Y X Z x := by
  simp only [curvAux, mlieBracket_swap_apply (V := Y) (W := X), map_neg]
  abel

end Basic

section Regular

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]

/-- For `Z` of class `C²` and `Y` differentiable at `x`, `∇_Y Z` is differentiable at `x`: the
regularity class gives `y ↦ ∇Z(y)` as a `C¹` section of the endomorphism bundle, and it is
applied to `Y`. -/
theorem mdiffAt_covApply {Z : Π x : M, TangentSpace I x}
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) :
    MDiffAt (T% (covApply cov Y Z)) x := by
  have hZ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 + 1) (fun y ↦ TotalSpace.mk' E y (Z y)) univ := by
    simpa using hZ.contMDiffOn
  have h := (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff (cov := cov)).contMDiff hZ'
  have h2 := (h.contMDiffAt (x := x) Filter.univ_mem).mdifferentiableAt one_ne_zero
  exact MDifferentiableAt.clm_bundle_apply (F₁ := E) (F₂ := E) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) (b := id) h2 hY

/-- **Additivity of the curvature expression in `Z`**, for `X, Y` differentiable at `x` and
`Z, Z'` of class `C²`. -/
theorem curvAux_add_Z {X Y Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (hZ' : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z' y))) :
    curvAux cov X Y (Z + Z') x = curvAux cov X Y Z x + curvAux cov X Y Z' x := by
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt two_ne_zero
  have hZ'x : MDiffAt (T% Z') x := (hZ' x).mdifferentiableAt two_ne_zero
  have hYZ := mdiffAt_covApply cov hZ hY
  have hYZ' := mdiffAt_covApply cov hZ' hY
  have hXZ := mdiffAt_covApply cov hZ hX
  have hXZ' := mdiffAt_covApply cov hZ' hX
  have eA : covApply cov Y (Z + Z') = covApply cov Y Z + covApply cov Y Z' := by
    funext y
    have hZy : MDiffAt (T% Z) y := (hZ y).mdifferentiableAt two_ne_zero
    have hZ'y : MDiffAt (T% Z') y := (hZ' y).mdifferentiableAt two_ne_zero
    simp [covApply, cov.isCovariantDerivativeOnUniv.add hZy hZ'y]
  have eB : covApply cov X (Z + Z') = covApply cov X Z + covApply cov X Z' := by
    funext y
    have hZy : MDiffAt (T% Z) y := (hZ y).mdifferentiableAt two_ne_zero
    have hZ'y : MDiffAt (T% Z') y := (hZ' y).mdifferentiableAt two_ne_zero
    simp [covApply, cov.isCovariantDerivativeOnUniv.add hZy hZ'y]
  simp only [curvAux, eA, eB, cov.isCovariantDerivativeOnUniv.add hYZ hYZ',
    cov.isCovariantDerivativeOnUniv.add hXZ hXZ', cov.isCovariantDerivativeOnUniv.add hZx hZ'x,
    ContinuousLinearMap.add_apply]
  module

variable [CompleteSpace E]

/-- **The curvature expression is tensorial in the direction `X`**, for `Z` of class `C²` and
any `Y`. -/
theorem curvAux_tensorial₁ (Y : Π x : M, TangentSpace I x) {Z : Π x : M, TangentSpace I x}
    {x : M} (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y))) :
    TensorialAt I E (fun X ↦ curvAux cov X Y Z x) x where
  smul {f X} hf hX := by
    have hXZ := mdiffAt_covApply cov hZ hX
    simp only [curvAux, covApply_smul_left, Pi.smul_apply', map_smul,
      cov.isCovariantDerivativeOnUniv.leibniz hXZ hf, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      mlieBracket_smul_left hf hX, fromTangentSpace_mfderiv_eq_extDerivFun, map_add,
      covApply_apply]
    module
  add {X X'} hX hX' := by
    have hXZ := mdiffAt_covApply cov hZ hX
    have hX'Z := mdiffAt_covApply cov hZ hX'
    simp only [curvAux, covApply_add_left, Pi.add_apply, map_add,
      cov.isCovariantDerivativeOnUniv.add hXZ hX'Z, ContinuousLinearMap.add_apply,
      mlieBracket_add_left hX hX']
    module

/-- **The curvature expression is tensorial in the direction `Y`**, for `Z` of class `C²` and
any `X`. -/
theorem curvAux_tensorial₂ (X : Π x : M, TangentSpace I x) {Z : Π x : M, TangentSpace I x}
    {x : M} (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y))) :
    TensorialAt I E (fun Y ↦ curvAux cov X Y Z x) x where
  smul {f Y} hf hY := by
    have hYZ := mdiffAt_covApply cov hZ hY
    simp only [curvAux, covApply_smul_left, Pi.smul_apply', map_smul,
      cov.isCovariantDerivativeOnUniv.leibniz hYZ hf, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      mlieBracket_smul_right hf hY, fromTangentSpace_mfderiv_eq_extDerivFun, map_add,
      covApply_apply]
    module
  add {Y Y'} hY hY' := by
    have hYZ := mdiffAt_covApply cov hZ hY
    have hY'Z := mdiffAt_covApply cov hZ hY'
    simp only [curvAux, covApply_add_left, Pi.add_apply, map_add,
      cov.isCovariantDerivativeOnUniv.add hYZ hY'Z, ContinuousLinearMap.add_apply,
      mlieBracket_add_right hY hY']
    module

/-- `y ↦ df(V)(y)` is differentiable at `x` for `f` of class `C²` at `x` and `V` differentiable
there: it agrees near `x` with a function differentiable within the model's range, composed with
the chart. -/
theorem mdifferentiableAt_extDerivFun_apply {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ extDerivFun (I := I) f y (V y)) x := by
  set g : E → ℝ := fun y' ↦ fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) y'
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) y') with hg
  have heq : (fun y ↦ extDerivFun (I := I) f y (V y)) =ᶠ[𝓝 x] g ∘ (extChartAt I x) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x,
      BracketDerivation.eventually_mdifferentiableAt hf] with y hy hfy
    exact (BracketDerivation.fderivWithin_comp_extChartAt_symm_apply hy hfy V).symm
  have hf2 : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) := by
    have := (contMDiffAt_iff.1 hf).2
    simpa [Function.comp_def] using this
  have hxr : extChartAt I x x ∈ range I := BracketDerivation.extChartAt_apply_mem_range x x
  have hV'd : DifferentiableWithinAt ℝ
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I)) (range I)
      (extChartAt I x x) := by
    have := (mdifferentiableWithinAt_univ.2 hV).differentiableWithinAt_mpullbackWithin_vectorField
    simpa using this
  have hgd : DifferentiableWithinAt ℝ g (range I) (extChartAt I x x) := by
    have h1 : DifferentiableWithinAt ℝ (fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I))
        (range I) (extChartAt I x x) :=
      (hf2.fderivWithin_right (m := 1) I.uniqueDiffOn (by norm_num) hxr).differentiableWithinAt
        one_ne_zero
    exact h1.clm_apply hV'd
  have hcomp : MDifferentiableAt I 𝓘(ℝ) (g ∘ (extChartAt I x)) x := by
    rw [← mdifferentiableWithinAt_univ]
    exact MDifferentiableWithinAt.comp x (mdifferentiableWithinAt_iff_differentiableWithinAt.2 hgd)
      (mdifferentiableAt_extChartAt (mem_chart_source H x)).mdifferentiableWithinAt
      (fun y _ ↦ BracketDerivation.extChartAt_apply_mem_range x y)
  exact hcomp.congr_of_eventuallyEq heq

/-- **The Leibniz rule of the curvature expression in `Z` cancels**: for `X, Y` differentiable
at `x`, `f` of class `C²` at `x` and `Z` of class `C²`, `R(X, Y)(f • Z) = f • R(X, Y)Z` at `x`.
The `df` terms cancel against `[X, Y] f = X (Y f) − Y (X f)` (`BracketDerivation`). -/
theorem curvAux_smul_Z {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    curvAux cov X Y (f • Z) x = f x • curvAux cov X Y Z x := by
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt two_ne_zero
  have hfx : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt two_ne_zero
  have hgY := mdifferentiableAt_extDerivFun_apply hf hY
  have hgX := mdifferentiableAt_extDerivFun_apply hf hX
  have hYZ := mdiffAt_covApply cov hZ hY
  have hXZ := mdiffAt_covApply cov hZ hX
  -- the two inner derivatives, replaced near `x` by their Leibniz expansions
  have hA : MDiffAt (T% ((fun y ↦ extDerivFun (I := I) f y (Y y)) • Z + f • covApply cov Y Z)) x :=
    mdifferentiableAt_add_section (hgY.smul_section hZx) (hfx.smul_section hYZ)
  have hB : MDiffAt (T% ((fun y ↦ extDerivFun (I := I) f y (X y)) • Z + f • covApply cov X Z)) x :=
    mdifferentiableAt_add_section (hgX.smul_section hZx) (hfx.smul_section hXZ)
  have eA := covApply_smul_right_eventually cov hf hZ Y
  have eB := covApply_smul_right_eventually cov hf hZ X
  have hA' : MDiffAt (T% (covApply cov Y (f • Z))) x := by
    refine hA.congr_of_eventuallyEq ?_
    filter_upwards [eA] with y hy
    rw [hy]
  have hB' : MDiffAt (T% (covApply cov X (f • Z))) x := by
    refine hB.congr_of_eventuallyEq ?_
    filter_upwards [eB] with y hy
    rw [hy]
  have h1 : cov (covApply cov Y (f • Z)) x = cov ((fun y ↦ extDerivFun (I := I) f y (Y y)) • Z
      + f • covApply cov Y Z) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hA' hA Filter.univ_mem eA
  have h2 : cov (covApply cov X (f • Z)) x = cov ((fun y ↦ extDerivFun (I := I) f y (X y)) • Z
      + f • covApply cov X Z) x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hB' hB Filter.univ_mem eB
  have hbr := BracketDerivation.extDerivFun_apply_mlieBracket hf hX hY
  have l1 := cov.isCovariantDerivativeOnUniv.leibniz hZx hgY
  have l2 := cov.isCovariantDerivativeOnUniv.leibniz hZx hgX
  have l3 := cov.isCovariantDerivativeOnUniv.leibniz hYZ hfx
  have l4 := cov.isCovariantDerivativeOnUniv.leibniz hXZ hfx
  have l5 := cov.isCovariantDerivativeOnUniv.leibniz hZx hfx
  have a1 := cov.isCovariantDerivativeOnUniv.add (hgY.smul_section hZx) (hfx.smul_section hYZ)
  have a2 := cov.isCovariantDerivativeOnUniv.add (hgX.smul_section hZx) (hfx.smul_section hXZ)
  simp only [curvAux, h1, h2, a1, a2, l1, l2, l3, l4, l5, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, hbr, covApply_apply]
  module

section Form

variable [FiniteDimensional ℝ E]

/-- **The curvature form of a `C²` section**: the bilinear map `(v, w) ↦ R(v, w)Z(x)` on the
tangent space, by `TensorialAt.mkHom₂` in the two directions. -/
noncomputable def curvForm (Z : Π x : M, TangentSpace I x) (x : M)
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y))) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  TensorialAt.mkHom₂ (fun X Y ↦ curvAux cov X Y Z x) x
    (fun Y _ ↦ curvAux_tensorial₁ cov Y hZ) (fun X _ ↦ curvAux_tensorial₂ cov X hZ)

theorem curvForm_apply {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    {X Y : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    curvForm cov Z x hZ (X x) (Y x) = curvAux cov X Y Z x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

theorem curvForm_swap {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun y ↦ TotalSpace.mk' E y (Z y)))
    (v w : TangentSpace I x) : curvForm cov Z x hZ v w = - curvForm cov Z x hZ w v := by
  simp only [curvForm, TensorialAt.mkHom₂_apply_eq_extend]
  exact curvAux_swap cov _ _ Z x

end Form

end Regular

end CurvatureTensorial
