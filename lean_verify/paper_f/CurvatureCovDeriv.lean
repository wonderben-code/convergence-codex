import CurvatureEndoOrder

/-!
# The covariant derivative of the curvature, on two direction fields

`CurvatureEndoOrder.homCovFun_riemann_apply` differentiates the field `y ↦ R(Y y, Z y)` with
entry 107's induced connection, and that is **not** `∇R`: the field carries `Y` and `Z` inside it,
so the tensor Leibniz rule gives `(∇_u A) = (∇_u R)(Y, Z) + R(∇_u Y, Z) + R(Y, ∇_u Z)` for
`A y = R(Y y, Z y)`. The `UNLOCK_WATCHLIST` item for the second Bianchi identity said the first was
the second, and `ERRATUM 494` records the correction. **This file defines the difference and proves
what a reader needs before trusting it.**

## What is proved

**`covRiemann`** — `(∇_u R)(Y, Z) = (∇_u A) − R(∇_u Y, Z) − R(Y, ∇_u Z)`, as an endomorphism of the
tangent space for each direction `u`.

**`covRiemann_apply`** — **THE CLASSICAL FORMULA**, which is the check against a textbook:
`(∇_u R)(Y, Z)W = ∇_u (R(Y, Z)W) − R(Y, Z)(∇_u W) − R(∇_u Y, Z)W − R(Y, ∇_u Z)W`, for `W` merely
differentiable at the point.

**`covRiemann_swap`** — antisymmetry in the two directions, from `LeviCivitaRegular.riemann_swap`
and the linearity of the induced connection in its argument.

**`covRiemann_smul_left`**, **`covRiemann_add_left`**, **`covRiemann_smul_right`**,
**`covRiemann_add_right`** — **THE REASON THE TWO SUBTRACTIONS ARE THE RIGHT ONES.** In each slot
the `df ⊗ ·` term the induced connection's Leibniz rule produces is **exactly** the one the
corresponding correction term produces, so the two cancel and the expression is additive and
`f`-homogeneous in `Y` and in `Z`. Had either subtraction been wrong, these four would fail.

## What is NOT here

* **THIS IS NOT PROVED TO BE A TENSOR.** Additive and `f`-homogeneous **as an operation on
  sections** is what the four laws above say. That `covRiemann Y Z x u` depends on `Y` and `Z` only
  through `Y x` and `Z x` is a **separate** statement and is not proved. Mathlib's `TensorialAt`
  cannot be used for it, for the reason `CurvatureTensorial` gives about its own `Z` slot: the
  class asks its `smul` law for every section merely differentiable at the point, and these laws
  hold only at `C^(k+2)`. The route is `CurvatureTensor.curvAux_congr_of_eq_Z`'s — a local frame
  with coefficients of the same class — and it is **not attempted, no cost claimed**
  (`ERRATUM 246`).
* **NO SECOND BIANCHI IDENTITY.** The cyclic sum `(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y)`
  is not stated. It is a statement about **fields** and so needs no tensoriality, but it does need
  the computation: expand each term through `R(Y, Z)W = ∇_Y ∇_Z W − ∇_Z ∇_Y W − ∇_{[Y,Z]} W` and
  telescope the cyclic sum against the Jacobi identity — three derivatives of `W`, where
  `CurvatureBianchi`'s **first** Bianchi identity needed two and cost a file of seven
  declarations. Not attempted, no cost claimed.
* **NO REGULARITY.** Nothing says `y ↦ covRiemann Y Z y u` is a `C^(k−1)` anything; `HomCovariant`
  proves no smoothness of the induced connection, so this object exists at a point and is not
  known to vary continuously. ⚠ The clause about `HomCovariant` is false as of entry 112
  (`HomCovariantOrder`), and **the clause about `covRiemann` stands**: the theorem there wants the
  curvature field one order up, which is an instance shift nothing has done. ⚠ And **the second
  clause is false too as of entry 113**: `CurvatureCovOrder.contMDiffAt_covRiemann_hom` does that
  shift and makes `y ↦ (∇_X R)(Y, Z)(y)` a `C^k` section of `Hom(TM, TM)`, for `C^(k+3)` fields on
  a `C^(k+4)` manifold with a `C^(k+3)` metric. **The whole paragraph is now superseded**, and it
  is kept because it is what this file proved and did not prove.
* **NO CONTRACTED FORM.** The divergence of the Einstein tensor, which is what the second Bianchi
  identity is usually wanted for, needs a trace of this object and a metric contraction; neither
  is here, and the modelling decision is the author's.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `CurvatureEndoOrder`'s, which are
`RicciOrder`'s, unchanged — and every theorem here additionally takes `hk : k ≠ 0`, because the
induced connection needs its argument **differentiable** and the curvature is `C^k`. So **nothing
in this file says anything at `k = 0`**: a `C²` metric gives a `C⁰` curvature and there is no
derivative to take. The local instances are `CurvatureEndoOrder`'s six. **There is no `omit` in
this file**: every binder is used by every theorem, and the unused-variable linter reports
nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureCovDeriv

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

/-- **THE COVARIANT DERIVATIVE OF THE CURVATURE, ON TWO DIRECTION FIELDS**:
`(∇_u R)(Y, Z) = (∇_u A) − R(∇_u Y, Z) − R(Y, ∇_u Z)` where `A y = R(Y y, Z y)`. The two
subtractions are what `CurvatureEndoOrder`'s `homCovFun_riemann_apply` does not have: that
differentiates the composite, and the composite carries `Y` and `Z` inside it.
**This is not yet shown to be a TENSOR.** What is proved below is that it is additive and
`f`-homogeneous in `Y` and in `Z` **as an operation on sections**; that it depends on `Y` and `Z`
only through `Y x` and `Z x` is a separate statement, and it is not proved here — see the file's
*What is NOT here*. -/
noncomputable def covRiemann (Y Z : Π x : M, TangentSpace I x) (x : M) (u : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  HomCovariant.homCovFun (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
      (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y)) x u
    - LeviCivitaRegular.riemann I x (leviCivita Y x u) (Z x)
    - LeviCivitaRegular.riemann I x (Y x) (leviCivita Z x u)

/-- **ANTISYMMETRY IN THE TWO DIRECTIONS.** -/
theorem covRiemann_swap {Y Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann Y Z x u = - covRiemann Z Y x u := by
  have hA := CurvatureEndoOrder.mdiffHomAt_riemann hk hZ hY
  have hfield : (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y))
      = -(fun y ↦ LeviCivitaRegular.riemann I y (Z y) (Y y)) := by
    funext y
    exact LeviCivitaRegular.riemann_swap (I := I) y (Y y) (Z y)
  simp only [covRiemann, hfield]
  rw [show (-(fun y ↦ LeviCivitaRegular.riemann I y (Z y) (Y y)))
      = ((-1 : ℝ) • fun y ↦ LeviCivitaRegular.riemann I y (Z y) (Y y)) by
    funext y; simp,
    (HomCovariant.isCovariantDerivativeOn_homCovFun (cov := leviCivita) univ).smul_const
      (-1 : ℝ) hA (mem_univ x)]
  rw [LeviCivitaRegular.riemann_swap (I := I) x (leviCivita Y x u) (Z x),
    LeviCivitaRegular.riemann_swap (I := I) x (Y x) (leviCivita Z x u)]
  ext w
  simp
  abel

/-- **THE LEIBNIZ TERMS CANCEL IN THE FIRST DIRECTION**, which is why the two subtractions in
`covRiemann` are the right ones: the `df ⊗ ·` the induced connection produces is exactly the one
the first correction term produces. -/
theorem covRiemann_smul_left {Y Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M} (hk : k ≠ 0)
    (hf : MDiffAt f x) (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann (f • Y) Z x u = f x • covRiemann Y Z x u := by
  have hA := CurvatureEndoOrder.mdiffHomAt_riemann hk hY hZ
  have hYd : MDiffAt (T% Y) x := hY.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ LeviCivitaRegular.riemann I y ((f • Y) y) (Z y))
      = f • fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y) := by
    funext y
    exact CurvatureTensor.curvEndo_smul_left _ y (f y) (Y y) (Z y)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := leviCivita) univ).leibniz hA hf
      (mem_univ x),
    leviCivita.isCovariantDerivativeOn.leibniz hYd hf (mem_univ x)]
  have h3 : LeviCivitaRegular.riemann I x ((f • Y) x) (leviCivita Z x u)
      = f x • LeviCivitaRegular.riemann I x (Y x) (leviCivita Z x u) :=
    CurvatureTensor.curvEndo_smul_left _ x (f x) (Y x) (leviCivita Z x u)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, CurvatureTensor.curvEndo_add_left,
    CurvatureTensor.curvEndo_smul_left, h3]
  ext w
  simp
  module

/-- **ADDITIVITY IN THE FIRST DIRECTION.** -/
theorem covRiemann_add_left {Y Y' Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hY' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y') x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann (Y + Y') Z x u = covRiemann Y Z x u + covRiemann Y' Z x u := by
  have hA := CurvatureEndoOrder.mdiffHomAt_riemann hk hY hZ
  have hA' := CurvatureEndoOrder.mdiffHomAt_riemann hk hY' hZ
  have hYd : MDiffAt (T% Y) x := hY.mdifferentiableAt (by simp)
  have hYd' : MDiffAt (T% Y') x := hY'.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ LeviCivitaRegular.riemann I y ((Y + Y') y) (Z y))
      = (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y))
        + fun y ↦ LeviCivitaRegular.riemann I y (Y' y) (Z y) := by
    funext y
    exact CurvatureTensor.curvEndo_add_left _ y (Y y) (Y' y) (Z y)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := leviCivita) univ).add hA hA'
      (mem_univ x),
    leviCivita.isCovariantDerivativeOn.add hYd hYd' (mem_univ x)]
  simp only [Pi.add_apply, ContinuousLinearMap.add_apply, CurvatureTensor.curvEndo_add_left]
  ext w
  simp
  abel

/-- **THE CLASSICAL FORMULA**, which is what a reader checks against a textbook:
`(∇_u R)(Y, Z)W = ∇_u (R(Y, Z)W) − R(Y, Z)(∇_u W) − R(∇_u Y, Z)W − R(Y, ∇_u Z)W`. -/
theorem covRiemann_apply {Y Z W : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (hW : MDiffAt (T% W) x)
    (u : TangentSpace I x) :
    covRiemann Y Z x u (W x)
      = leviCivita (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y) (W y)) x u
        - LeviCivitaRegular.riemann I x (Y x) (Z x) (leviCivita W x u)
        - LeviCivitaRegular.riemann I x (leviCivita Y x u) (Z x) (W x)
        - LeviCivitaRegular.riemann I x (Y x) (leviCivita Z x u) (W x) := by
  simp only [covRiemann, ContinuousLinearMap.sub_apply,
    CurvatureEndoOrder.homCovFun_riemann_apply hk hY hZ hW u]

/-- **THE SAME CANCELLATION IN THE SECOND DIRECTION.** -/
theorem covRiemann_smul_right {Y Z : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M} (hk : k ≠ 0)
    (hf : MDiffAt f x) (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann Y (f • Z) x u = f x • covRiemann Y Z x u := by
  have hA := CurvatureEndoOrder.mdiffHomAt_riemann hk hY hZ
  have hZd : MDiffAt (T% Z) x := hZ.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ LeviCivitaRegular.riemann I y (Y y) ((f • Z) y))
      = f • fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y) := by
    funext y
    exact CurvatureTensor.curvEndo_smul_right _ y (f y) (Y y) (Z y)
  have h3 : LeviCivitaRegular.riemann I x (leviCivita Y x u) ((f • Z) x)
      = f x • LeviCivitaRegular.riemann I x (leviCivita Y x u) (Z x) :=
    CurvatureTensor.curvEndo_smul_right _ x (f x) (leviCivita Y x u) (Z x)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := leviCivita) univ).leibniz hA hf
      (mem_univ x),
    leviCivita.isCovariantDerivativeOn.leibniz hZd hf (mem_univ x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, CurvatureTensor.curvEndo_add_right,
    CurvatureTensor.curvEndo_smul_right, h3]
  ext w
  simp
  module

/-- **ADDITIVITY IN THE SECOND DIRECTION.** -/
theorem covRiemann_add_right {Y Z Z' : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hZ' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z') x) (u : TangentSpace I x) :
    covRiemann Y (Z + Z') x u = covRiemann Y Z x u + covRiemann Y Z' x u := by
  have hA := CurvatureEndoOrder.mdiffHomAt_riemann hk hY hZ
  have hA' := CurvatureEndoOrder.mdiffHomAt_riemann hk hY hZ'
  have hZd : MDiffAt (T% Z) x := hZ.mdifferentiableAt (by simp)
  have hZd' : MDiffAt (T% Z') x := hZ'.mdifferentiableAt (by simp)
  have hfield : (fun y ↦ LeviCivitaRegular.riemann I y (Y y) ((Z + Z') y))
      = (fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z y))
        + fun y ↦ LeviCivitaRegular.riemann I y (Y y) (Z' y) := by
    funext y
    exact CurvatureTensor.curvEndo_add_right _ y (Y y) (Z y) (Z' y)
  simp only [covRiemann, hfield]
  rw [(HomCovariant.isCovariantDerivativeOn_homCovFun (cov := leviCivita) univ).add hA hA'
      (mem_univ x),
    leviCivita.isCovariantDerivativeOn.add hZd hZd' (mem_univ x)]
  simp only [Pi.add_apply, ContinuousLinearMap.add_apply, CurvatureTensor.curvEndo_add_right]
  ext w
  simp
  abel

end CurvatureCovDeriv
