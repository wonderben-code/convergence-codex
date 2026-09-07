import CurvatureTensorial

/-!
# The curvature tensor of a locally `C¹` covariant derivative on the tangent bundle

`CurvatureTensorial` wrote the curvature expression `R(X, Y)Z` and proved it tensorial in `X` and
`Y` and a tensor in `Z` among `C²` sections, and said in its fence why the 3-tensor was not
there: Mathlib's `TensorialAt` asks its law of merely differentiable sections, and the law in
`Z` holds only for `C²` ones. This file supplies what was named as the next object — **the `C²`
analogue of `TensorialAt.pointwise`** (`curvAux_congr_of_eq_Z`) — and with it **the curvature
endomorphism `R(v, w) : T_xM → T_xM`** (`curvEndo`), with the theorem that gives it its meaning:
for `X, Y` differentiable at `x` and `Z` of class `C²` at `x`,
`R(X x, Y x) (Z x) = (∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z)(x)` (`curvEndo_apply`). It is
antisymmetric and bilinear in `(v, w)`.

Two changes of hypothesis against `CurvatureTensorial`, both read off the binders. The
connection is asked to be `C¹` **on every open set** (`IsLocallyC1`, Mathlib's
`ContMDiffCovariantDerivativeOn E 1 cov u` for every open `u`), which implies Mathlib's global
class and is what the local frame needs, because a local frame is a `C²` section only near the
point. And the manifold is `C³`, because sections of class `C²` at a point, extended vectors of
class `C²`, and a local frame with `C²` coefficients all need the tangent bundle to be a `C²`
vector bundle (`contMDiffVectorBundle_two`, Mathlib's `TangentBundle.contMDiffVectorBundle` at
`n = 2`, which the library states but does not register). Every hypothesis on a section is now
*at the point* (`CMDiffAt 2 (T% Z) x`), not global.

The pointwise lemma is Mathlib's proof with `C²` in place of differentiable: in the
trivialisation at `x`, a `C²` section is near `x` the sum of its `C²` coefficients
(`contMDiffAt_localFrame_coeff`) times the frame sections (`contMDiffAt_localFrame_of_mem`);
locality in `Z` (`curvAux_congr_Z`), the sum rule (`curvAux_sum_Z`) and the scalar rule
(`curvAux_smul_Z'`) then reduce `R(X, Y)Z(x)` to the coefficients of `Z x`. The endomorphism is
`z ↦ R(extend v, extend w)(extend z)(x)`, linear in `z` by the tensor laws and the pointwise
lemma, and `curvEndo_apply` is the pointwise lemma in all three slots — Mathlib's in `X` and `Y`,
this file's in `Z`.

## What is proved

**`contMDiffVectorBundle_two`** — the tangent bundle of a `C³` manifold is a `C²` vector bundle.

**`IsLocallyC1`** — the class: `C¹` on every open set; it implies
`ContMDiffCovariantDerivative cov 1`.

**`mdiffAt_covApply'`**, **`eventually_mdiffAt_of_cmdiffAt`** — `∇_Y Z` is differentiable at `x`
for `Z` of class `C²` at `x`, and such a `Z` is differentiable near `x`.

**`curvAux_congr_Z`** — **locality in `Z`**. **`covApply_smul_right_eventually'`**,
**`curvAux_add_Z'`**, **`cov_zero`**, **`curvAux_zero_Z`**, **`curvAux_sum_Z`** — the Leibniz
expansion near `x`, additivity, zero and finite sums in `Z`, all for sections of class `C²` at
the point.

**`curvAux_tensorial₁'`**, **`curvAux_tensorial₂'`**, **`curvAux_smul_Z'`** — `CurvatureTensorial`'s
tensoriality and scalar rule with `Z` of class `C²` at the point.

**`curvAux_congr_of_eq_Z`** — **THE `C²` POINTWISE LEMMA**: sections of class `C²` at `x` with the
same value at `x` have the same `R(X, Y)Z(x)`.

**`cmdiffAt_extend`** — extended vectors are of class `C²` at the point.

**`curvEndo`, `curvEndo_apply_extend`** — **the curvature endomorphism** `R(v, w)`.

**`curvEndo_apply`** — **`R(X x, Y x)(Z x) = (∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z)(x)`** for `X, Y`
differentiable at `x` and `Z` of class `C²` at `x`.

**`curvEndo_add_left`, `curvEndo_smul_left`, `curvEndo_add_right`, `curvEndo_smul_right`,
`curvEndo_swap`** — bilinear and antisymmetric in `(v, w)`.

## What is NOT here

**NOTHING ABOUT `leviCivita`.** `KoszulManifold.leviCivita` is not shown to be `IsLocallyC1`, so
no curvature of a Riemannian metric is computed. That regularity — the Koszul form depends
differentiably on the point when the metric is `C²` — is the object that separates this file
from the Riemann tensor of a metric, and it is not started. **Not attempted, no cost claimed**
(`ERRATUM 246`).

**NO TRACES, NO IDENTITIES BEYOND ANTISYMMETRY.** No Ricci or scalar curvature, no Bianchi
identity, no pair symmetry. ⚠ By 7 September, entry 69, the traces are `RicciScalar.ricci` and
`RicciScalar.scalar`, the latter shown independent of the orthonormal basis; the identities are
still absent there.

**NOT PACKAGED AS ONE CONTINUOUS TRILINEAR MAP.** `curvEndo cov x : T_xM → T_xM → (T_xM →L T_xM)`
is bilinear by the four lemmas above and continuous in each slot by finite dimension, and no
declaration bundles it as `T_xM →L T_xM →L T_xM →L T_xM`.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, a `ChartedSpace H M` and a model `I` throughout; `[IsManifold I 3 M]`
throughout (a `C³` manifold with corners); `[IsLocallyC1 cov]` from `mdiffAt_covApply'` on;
`[CompleteSpace E]` from `curvAux_tensorial₁'` on (Mathlib's hypothesis for the bracket's rules
and for pulled-back fields); `[FiniteDimensional ℝ E]` from `curvAux_congr_of_eq_Z` on (the
local frame, and `LinearMap.toContinuousLinearMap`). No metric anywhere in the file.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureTensor

open Bundle Manifold VectorField FiberBundle Set CurvatureTensorial
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]

/-- The tangent bundle of a `C³` manifold is a `C²` vector bundle (Mathlib states this for `n + 1`
and registers instances only for `1`, `∞` and `ω`). -/
theorem contMDiffVectorBundle_two : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I := by
  have h3 : IsManifold I (2 + 1) M := inferInstanceAs (IsManifold I 3 M)
  exact TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_two

/-- A covariant derivative on the tangent bundle that is of class `C¹` on every open set:
Mathlib's `ContMDiffCovariantDerivativeOn E 1 cov u` for every open `u`. -/
class IsLocallyC1 (cov : CovariantDerivative I E (TangentSpace I : M → Type _)) : Prop where
  on_open : ∀ u : Set M, IsOpen u → ContMDiffCovariantDerivativeOn E 1 cov.toFun u

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Near `x`, a section of class `C²` at `x` is differentiable. -/
theorem eventually_mdiffAt_of_cmdiffAt {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt 2 (T% Z) x) : ∀ᶠ y in 𝓝 x, MDiffAt (T% Z) y := by
  obtain ⟨u, hu, hZu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hZ
  filter_upwards [interior_mem_nhds.2 hu] with y hy
  exact ((hZu y (interior_subset hy)).mdifferentiableWithinAt two_ne_zero).mdifferentiableAt
    (mem_interior_iff_mem_nhds.1 hy)

/-- Near `x`, `∇_Y (f • Z) = df(Y) • Z + f • ∇_Y Z`, for `f` and `Z` of class `C²` at `x`. -/
theorem covApply_smul_right_eventually' {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    {Z : Π x : M, TangentSpace I x} (hZ : CMDiffAt 2 (T% Z) x) (Y : Π x : M, TangentSpace I x) :
    covApply cov Y (f • Z) =ᶠ[𝓝 x]
      (fun y ↦ extDerivFun (I := I) f y (Y y)) • Z + f • covApply cov Y Z := by
  filter_upwards [BracketDerivation.eventually_mdifferentiableAt hf,
    eventually_mdiffAt_of_cmdiffAt hZ] with y hfy hZy
  simp only [covApply, Pi.add_apply, Pi.smul_apply',
    cov.isCovariantDerivativeOnUniv.leibniz hZy hfy, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  exact add_comm _ _

/-- The covariant derivative of the zero section vanishes. -/
theorem cov_zero (y : M) : cov 0 y = 0 := by
  have h := cov.isCovariantDerivativeOnUniv.leibniz (σ := 0) (g := 0)
    (mdifferentiable_zeroSection ..) mdifferentiableAt_const (x := y)
  have h0 : ((0 : M → ℝ) • (0 : Π x : M, TangentSpace I x)) = 0 := by
    funext x'
    simp
  rw [h0] at h
  rw [h]
  ext v
  simp

/-- The curvature expression of the zero section vanishes. -/
theorem curvAux_zero_Z (X Y : Π x : M, TangentSpace I x) (x : M) :
    curvAux cov X Y 0 x = 0 := by
  have h : covApply cov Y 0 = 0 := by
    funext y
    simp [covApply, cov_zero]
  have h' : covApply cov X 0 = 0 := by
    funext y
    simp [covApply, cov_zero]
  simp [curvAux, h, h', cov_zero]

variable [IsLocallyC1 cov]

instance : CovariantDerivative.ContMDiffCovariantDerivative cov 1 :=
  ⟨IsLocallyC1.on_open univ isOpen_univ⟩

/-- For `Z` of class `C²` at `x` and `Y` differentiable at `x`, `∇_Y Z` is differentiable at `x`. -/
theorem mdiffAt_covApply' {Z : Π x : M, TangentSpace I x} {x : M} (hZ : CMDiffAt 2 (T% Z) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    MDiffAt (T% (covApply cov Y Z)) x := by
  obtain ⟨u, hu, hZu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hZ
  have hZ' : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 + 1) (fun y ↦ TotalSpace.mk' E y (Z y))
      (interior u) := by
    simpa using hZu.mono interior_subset
  have h := (IsLocallyC1.on_open (cov := cov) (interior u) isOpen_interior).contMDiff hZ'
  have h2 := (h.contMDiffAt (x := x)
    (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hu))).mdifferentiableAt one_ne_zero
  exact MDifferentiableAt.clm_bundle_apply (F₁ := E) (F₂ := E) (E₁ := TangentSpace I)
    (E₂ := TangentSpace I) (b := id) h2 hY

/-- **Locality in `Z`**: sections of class `C²` at `x` that agree near `x` have the same
curvature expression at `x`. -/
theorem curvAux_congr_Z {X Y Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x)
    (hZ' : CMDiffAt 2 (T% Z') x) (hZZ' : ∀ᶠ y in 𝓝 x, Z y = Z' y) :
    curvAux cov X Y Z x = curvAux cov X Y Z' x := by
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have hZ'x : MDiffAt (T% Z') x := hZ'.mdifferentiableAt two_ne_zero
  have e1 : ∀ W : Π x : M, TangentSpace I x, covApply cov W Z =ᶠ[𝓝 x] covApply cov W Z' := by
    intro W
    filter_upwards [hZZ'.eventually_nhds, eventually_mdiffAt_of_cmdiffAt hZ,
      eventually_mdiffAt_of_cmdiffAt hZ'] with y hy hZy hZ'y
    simp only [covApply]
    rw [cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZy hZ'y Filter.univ_mem hy]
  have h1 := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq (mdiffAt_covApply' cov hZ hY)
    (mdiffAt_covApply' cov hZ' hY) Filter.univ_mem (e1 Y)
  have h2 := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq (mdiffAt_covApply' cov hZ hX)
    (mdiffAt_covApply' cov hZ' hX) Filter.univ_mem (e1 X)
  have h3 := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hZx hZ'x Filter.univ_mem hZZ'
  simp only [curvAux, h1, h2, h3]

/-- **Additivity in `Z`, local form.** -/
theorem curvAux_add_Z' {X Y Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x)
    (hZ' : CMDiffAt 2 (T% Z') x) :
    curvAux cov X Y (Z + Z') x = curvAux cov X Y Z x + curvAux cov X Y Z' x := by
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have hZ'x : MDiffAt (T% Z') x := hZ'.mdifferentiableAt two_ne_zero
  have hYZ := mdiffAt_covApply' cov hZ hY
  have hYZ' := mdiffAt_covApply' cov hZ' hY
  have hXZ := mdiffAt_covApply' cov hZ hX
  have hXZ' := mdiffAt_covApply' cov hZ' hX
  have e : ∀ W : Π x : M, TangentSpace I x,
      covApply cov W (Z + Z') =ᶠ[𝓝 x] covApply cov W Z + covApply cov W Z' := by
    intro W
    filter_upwards [eventually_mdiffAt_of_cmdiffAt hZ, eventually_mdiffAt_of_cmdiffAt hZ']
      with y hZy hZ'y
    simp [covApply, cov.isCovariantDerivativeOnUniv.add hZy hZ'y]
  have hA' : MDiffAt (T% (covApply cov Y (Z + Z'))) x := by
    refine (mdifferentiableAt_add_section hYZ hYZ').congr_of_eventuallyEq ?_
    filter_upwards [e Y] with y hy
    rw [hy]
  have hB' : MDiffAt (T% (covApply cov X (Z + Z'))) x := by
    refine (mdifferentiableAt_add_section hXZ hXZ').congr_of_eventuallyEq ?_
    filter_upwards [e X] with y hy
    rw [hy]
  have h1 := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hA'
    (mdifferentiableAt_add_section hYZ hYZ') Filter.univ_mem (e Y)
  have h2 := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hB'
    (mdifferentiableAt_add_section hXZ hXZ') Filter.univ_mem (e X)
  simp only [curvAux, h1, h2, cov.isCovariantDerivativeOnUniv.add hYZ hYZ',
    cov.isCovariantDerivativeOnUniv.add hXZ hXZ', cov.isCovariantDerivativeOnUniv.add hZx hZ'x,
    ContinuousLinearMap.add_apply]
  module

/-- **Sums in `Z`**, for summands of class `C²` at `x`. -/
theorem curvAux_sum_Z {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) {ι : Type*} (s : Finset ι)
    (σ : ι → Π x : M, TangentSpace I x) (hσ : ∀ i, CMDiffAt 2 (T% (σ i)) x) :
    curvAux cov X Y (fun x' ↦ ∑ i ∈ s, σ i x') x = ∑ i ∈ s, curvAux cov X Y (σ i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact curvAux_zero_Z cov X Y x
  | insert a s ha ih =>
      have h : (fun x' ↦ ∑ i ∈ insert a s, σ i x') = σ a + fun x' ↦ ∑ i ∈ s, σ i x' := by
        funext x'
        simp [Finset.sum_insert ha]
      rw [h, curvAux_add_Z' cov hX hY (hσ a) (ContMDiffAt.sum_section fun i _ ↦ hσ i), ih,
        Finset.sum_insert ha]

section Complete

variable [CompleteSpace E]

/-- **Tensorial in `X`**, for `Z` of class `C²` at `x`. -/
theorem curvAux_tensorial₁' (Y : Π x : M, TangentSpace I x) {Z : Π x : M, TangentSpace I x}
    {x : M} (hZ : CMDiffAt 2 (T% Z) x) :
    TensorialAt I E (fun X ↦ curvAux cov X Y Z x) x where
  smul {f X} hf hX := by
    have hXZ := mdiffAt_covApply' cov hZ hX
    simp only [curvAux, covApply_smul_left, Pi.smul_apply', map_smul,
      cov.isCovariantDerivativeOnUniv.leibniz hXZ hf, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      mlieBracket_smul_left hf hX, fromTangentSpace_mfderiv_eq_extDerivFun, map_add,
      covApply_apply]
    module
  add {X X'} hX hX' := by
    have hXZ := mdiffAt_covApply' cov hZ hX
    have hX'Z := mdiffAt_covApply' cov hZ hX'
    simp only [curvAux, covApply_add_left, Pi.add_apply, map_add,
      cov.isCovariantDerivativeOnUniv.add hXZ hX'Z, ContinuousLinearMap.add_apply,
      mlieBracket_add_left hX hX']
    module

/-- **Tensorial in `Y`**, for `Z` of class `C²` at `x`. -/
theorem curvAux_tensorial₂' (X : Π x : M, TangentSpace I x) {Z : Π x : M, TangentSpace I x}
    {x : M} (hZ : CMDiffAt 2 (T% Z) x) :
    TensorialAt I E (fun Y ↦ curvAux cov X Y Z x) x where
  smul {f Y} hf hY := by
    have hYZ := mdiffAt_covApply' cov hZ hY
    simp only [curvAux, covApply_smul_left, Pi.smul_apply', map_smul,
      cov.isCovariantDerivativeOnUniv.leibniz hYZ hf, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
      mlieBracket_smul_right hf hY, fromTangentSpace_mfderiv_eq_extDerivFun, map_add,
      covApply_apply]
    module
  add {Y Y'} hY hY' := by
    have hYZ := mdiffAt_covApply' cov hZ hY
    have hY'Z := mdiffAt_covApply' cov hZ hY'
    simp only [curvAux, covApply_add_left, Pi.add_apply, map_add,
      cov.isCovariantDerivativeOnUniv.add hYZ hY'Z, ContinuousLinearMap.add_apply,
      mlieBracket_add_right hY hY']
    module

/-- **The tensor law in `Z`, local form**: `R(X, Y)(f • Z) = f • R(X, Y)Z` at `x` for `f` and `Z`
of class `C²` at `x`. -/
theorem curvAux_smul_Z' {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x)
    {f : M → ℝ} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    curvAux cov X Y (f • Z) x = f x • curvAux cov X Y Z x := by
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt two_ne_zero
  have hfx : MDifferentiableAt I 𝓘(ℝ) f x := hf.mdifferentiableAt two_ne_zero
  have hgY := mdifferentiableAt_extDerivFun_apply hf hY
  have hgX := mdifferentiableAt_extDerivFun_apply hf hX
  have hYZ := mdiffAt_covApply' cov hZ hY
  have hXZ := mdiffAt_covApply' cov hZ hX
  have hA : MDiffAt (T% ((fun y ↦ extDerivFun (I := I) f y (Y y)) • Z + f • covApply cov Y Z)) x :=
    mdifferentiableAt_add_section (hgY.smul_section hZx) (hfx.smul_section hYZ)
  have hB : MDiffAt (T% ((fun y ↦ extDerivFun (I := I) f y (X y)) • Z + f • covApply cov X Z)) x :=
    mdifferentiableAt_add_section (hgX.smul_section hZx) (hfx.smul_section hXZ)
  have eA := covApply_smul_right_eventually' cov hf hZ Y
  have eB := covApply_smul_right_eventually' cov hf hZ X
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

end Complete

/-- Extended vectors are sections of class `C²` at the point. -/
theorem cmdiffAt_extend (x : M) (z : TangentSpace I x) : CMDiffAt 2 (T% (extend E z)) x :=
  contMDiffAt_extend' (k := 2) I E z

section Frame

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **THE `C²` POINTWISE LEMMA**: two sections of class `C²` at `x` with the same value at `x`
have the same curvature expression at `x`. Mathlib's `TensorialAt.pointwise` with `C²` in place
of differentiable: a local frame from the trivialisation at `x`, with `C²` coefficients. -/
theorem curvAux_congr_of_eq_Z {X Y Z Z' : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x)
    (hZ' : CMDiffAt 2 (T% Z') x) (hZZ' : Z x = Z' x) :
    curvAux cov X Y Z x = curvAux cov X Y Z' x := by
  classical
  let t := trivializationAt E (TangentSpace I : M → Type _) x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := Module.Basis.ofVectorSpace ℝ E
  let s := t.localFrame b
  let c := t.localFrame_coeff I b
  have hs (i) : CMDiffAt 2 (T% (s i)) x := contMDiffAt_localFrame_of_mem 2 _ b i x_mem
  have hc {σ : (x : M) → TangentSpace I x} (hσ : CMDiffAt 2 (T% σ) x) (i) :
      CMDiffAt 2 (LinearMap.piApply (c i) σ) x :=
    contMDiffAt_localFrame_coeff b x_mem hσ i
  have hΦ_eq {σ : (x : M) → TangentSpace I x} (hσ : CMDiffAt 2 (T% σ) x) :
      curvAux cov X Y σ x
        = curvAux cov X Y (fun x' ↦ ∑ i, ((LinearMap.piApply (c i) σ) • s i) x') x :=
    curvAux_congr_Z cov hX hY hσ
      (ContMDiffAt.sum_section fun i _ ↦ (hc hσ i).smul_section (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  rw [hΦ_eq hZ, hΦ_eq hZ',
    curvAux_sum_Z cov hX hY _ _ (fun i ↦ (hc hZ i).smul_section (hs i)),
    curvAux_sum_Z cov hX hY _ _ (fun i ↦ (hc hZ' i).smul_section (hs i))]
  congr! 1 with i
  calc curvAux cov X Y ((LinearMap.piApply (c i) Z) • (s i)) x
      = c i x (Z x) • curvAux cov X Y (s i) x := curvAux_smul_Z' cov hX hY (hs i) (hc hZ i)
    _ = c i x (Z' x) • curvAux cov X Y (s i) x := by rw [hZZ']
    _ = curvAux cov X Y ((LinearMap.piApply (c i) Z') • (s i)) x :=
        (curvAux_smul_Z' cov hX hY (hs i) (hc hZ' i)).symm

attribute [local instance] KoszulManifold.finDimTangent

/-- **THE CURVATURE ENDOMORPHISM** `R(v, w) : T_xM → T_xM`, linear in `z` by the tensor laws in
`Z` and the `C²` pointwise lemma applied to extended vectors. -/
noncomputable def curvEndo (x : M) (v w : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ curvAux cov (extend E v) (extend E w) (extend E z) x
      map_add' := fun z₁ z₂ ↦ by
        rw [← curvAux_add_Z' cov (mdifferentiableAt_extend (I := I) E v)
          (mdifferentiableAt_extend (I := I) E w) (cmdiffAt_extend x z₁)
          (cmdiffAt_extend x z₂)]
        exact curvAux_congr_of_eq_Z cov (mdifferentiableAt_extend (I := I) E v)
          (mdifferentiableAt_extend (I := I) E w) (cmdiffAt_extend x _)
          ((cmdiffAt_extend x z₁).add_section (cmdiffAt_extend x z₂)) (by simp)
      map_smul' := fun c z ↦ by
        simp only [RingHom.id_apply]
        rw [← curvAux_smul_Z' cov (mdifferentiableAt_extend (I := I) E v)
          (mdifferentiableAt_extend (I := I) E w) (cmdiffAt_extend x z)
          (f := fun _ ↦ c) contMDiffAt_const]
        exact curvAux_congr_of_eq_Z cov (mdifferentiableAt_extend (I := I) E v)
          (mdifferentiableAt_extend (I := I) E w) (cmdiffAt_extend x _)
          (contMDiffAt_const.smul_section (cmdiffAt_extend x z)) (by simp) }

theorem curvEndo_apply_extend (x : M) (v w z : TangentSpace I x) :
    curvEndo cov x v w z = curvAux cov (extend E v) (extend E w) (extend E z) x := rfl

/-- **THE CURVATURE ENDOMORPHISM ON SECTIONS**: for `X, Y` differentiable at `x` and `Z` of class
`C²` at `x`, `R(X x, Y x) (Z x) = (∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z)(x)`. -/
theorem curvEndo_apply {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    curvEndo cov x (X x) (Y x) (Z x) = curvAux cov X Y Z x := by
  rw [curvEndo_apply_extend]
  have hZe := cmdiffAt_extend x (Z x)
  have h1 : curvAux cov (extend E (X x)) (extend E (Y x)) (extend E (Z x)) x
      = curvAux cov X (extend E (Y x)) (extend E (Z x)) x :=
    (curvAux_tensorial₁' cov _ hZe).pointwise (mdifferentiableAt_extend (I := I) E _) hX (by simp)
  have h2 : curvAux cov X (extend E (Y x)) (extend E (Z x)) x
      = curvAux cov X Y (extend E (Z x)) x :=
    (curvAux_tensorial₂' cov _ hZe).pointwise (mdifferentiableAt_extend (I := I) E _) hY (by simp)
  rw [h1, h2]
  exact curvAux_congr_of_eq_Z cov hX hY hZe hZ (by simp)

/-- Linearity of `R(v, w)` in `v`: additivity, from tensoriality in the first direction and
Mathlib's `TensorialAt.pointwise` on extended vectors. -/
theorem curvEndo_add_left (x : M) (v v' w : TangentSpace I x) :
    curvEndo cov x (v + v') w = curvEndo cov x v w + curvEndo cov x v' w := by
  ext z
  simp only [curvEndo_apply_extend, ContinuousLinearMap.add_apply]
  have hT := curvAux_tensorial₁' cov (extend E w) (cmdiffAt_extend x z)
  rw [← hT.add (mdifferentiableAt_extend (I := I) E v) (mdifferentiableAt_extend (I := I) E v')]
  exact hT.pointwise (mdifferentiableAt_extend (I := I) E _)
    (mdifferentiableAt_add_section (mdifferentiableAt_extend (I := I) E v)
      (mdifferentiableAt_extend (I := I) E v')) (by simp)

theorem curvEndo_smul_left (x : M) (c : ℝ) (v w : TangentSpace I x) :
    curvEndo cov x (c • v) w = c • curvEndo cov x v w := by
  ext z
  simp only [curvEndo_apply_extend, ContinuousLinearMap.smul_apply]
  have hT := curvAux_tensorial₁' cov (extend E w) (cmdiffAt_extend x z)
  have h1 : curvAux cov ((fun _ ↦ c) • extend E v) (extend E w) (extend E z) x
      = c • curvAux cov (extend E v) (extend E w) (extend E z) x :=
    hT.smul mdifferentiableAt_const (mdifferentiableAt_extend (I := I) E v)
  rw [← h1]
  exact hT.pointwise (mdifferentiableAt_extend (I := I) E _)
    (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend (I := I) E v)) (by simp)

theorem curvEndo_add_right (x : M) (v w w' : TangentSpace I x) :
    curvEndo cov x v (w + w') = curvEndo cov x v w + curvEndo cov x v w' := by
  ext z
  simp only [curvEndo_apply_extend, ContinuousLinearMap.add_apply]
  have hT := curvAux_tensorial₂' cov (extend E v) (cmdiffAt_extend x z)
  rw [← hT.add (mdifferentiableAt_extend (I := I) E w) (mdifferentiableAt_extend (I := I) E w')]
  exact hT.pointwise (mdifferentiableAt_extend (I := I) E _)
    (mdifferentiableAt_add_section (mdifferentiableAt_extend (I := I) E w)
      (mdifferentiableAt_extend (I := I) E w')) (by simp)

theorem curvEndo_smul_right (x : M) (c : ℝ) (v w : TangentSpace I x) :
    curvEndo cov x v (c • w) = c • curvEndo cov x v w := by
  ext z
  simp only [curvEndo_apply_extend, ContinuousLinearMap.smul_apply]
  have hT := curvAux_tensorial₂' cov (extend E v) (cmdiffAt_extend x z)
  have h1 : curvAux cov (extend E v) ((fun _ ↦ c) • extend E w) (extend E z) x
      = c • curvAux cov (extend E v) (extend E w) (extend E z) x :=
    hT.smul mdifferentiableAt_const (mdifferentiableAt_extend (I := I) E w)
  rw [← h1]
  exact hT.pointwise (mdifferentiableAt_extend (I := I) E _)
    (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend (I := I) E w)) (by simp)

/-- **Antisymmetry**: `R(v, w) = − R(w, v)`. -/
theorem curvEndo_swap (x : M) (v w : TangentSpace I x) :
    curvEndo cov x v w = - curvEndo cov x w v := by
  ext z
  simp only [curvEndo_apply_extend, ContinuousLinearMap.neg_apply]
  exact curvAux_swap cov _ _ _ x

end Frame

end CurvatureTensor
