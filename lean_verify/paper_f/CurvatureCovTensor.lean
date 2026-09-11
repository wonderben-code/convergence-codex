import CurvatureCovDeriv

/-!
# The covariant derivative of the curvature is a tensor in the two directions

`CurvatureCovDeriv` defines `covRiemann` and proves it additive and `f`-homogeneous in each
direction **as an operation on sections**, and says in its own *What is NOT here* that the
statement a reader wants — that the value depends on `Y` and `Z` only through `Y x` and `Z x` — is
separate and unproved. The `UNLOCK_WATCHLIST` item for the second Bianchi identity calls it step
(2). **This file proves it**, by the route `CurvatureTensor.curvAux_congr_of_eq_Z` took for its own
third slot: expand the field in the chart's local frame, whose coefficients are of the same class,
and use the slot laws term by term.

## What is proved

**`mdiffHomAt_congr`** and **`homCovFun_congr`** — **the induced connection of `HomCovariant`
depends only on the germ of its argument**, and differentiability of a section of `Hom(TM, TM)` is
a property of its germ. Neither is in `HomCovariant`, and the frame argument cannot start without
them. Note that `Filter.EventuallyEq` cannot be used for a **dependent** family, so these are
stated with `∀ᶠ y in 𝓝 x, A y = A' y`.

**`covRiemann_congr_left`** — and so `covRiemann` depends only on the germ of `Y`.

**`riemann_zero_left`**, **`covRiemann_zero_left`**, **`covRiemann_sum_left`** — the curvature and
its covariant derivative vanish on a zero direction, and `covRiemann` is additive over a **finite
family**, which is the form the frame expansion consumes.

**`covRiemann_congr_of_eq_left`** — **`covRiemann` IS A TENSOR IN THE FIRST DIRECTION**: `Y x =
Y' x` gives `covRiemann Y Z x u = covRiemann Y' Z x u`, for `Y, Y', Z` of class `C^(k+2)` at the
point and `k ≥ 1`.

**`covRiemann_congr_of_eq_right`** — **AND IN THE SECOND**, through `covRiemann_swap`, which is
what antisymmetry is for.

## What is NOT here

* **THE TENSOR IS NOT BUNDLED.** `covRiemann v w x u` as a continuous linear map in `v` and `w` —
  `CurvatureTensor.curvEndo`'s construction, `LinearMap.toContinuousLinearMap` over `extend` — is
  **not built**. The two theorems above are what that construction consumes, so it is now
  plumbing rather than mathematics, and it is plumbing this file does not do. **Not attempted, no
  cost claimed** (`ERRATUM 246`).
* **NO SECOND BIANCHI IDENTITY**, which is the item's step (3) and needs no tensoriality at all:
  the cyclic sum is a statement about fields. It needs the computation — three derivatives of the
  differentiated field, where the **first** Bianchi identity needed two and cost a file of seven
  declarations.
* **NO REGULARITY.** Nothing makes `y ↦ covRiemann Y Z y u` a section of anything: `HomCovariant`
  proves no smoothness of the induced connection. ⚠ The reason given is false as of entry 112
  (`HomCovariantOrder`); **the statement is still true**, because applying that theorem to the
  curvature needs it one order up and nothing has done the shift. ⚠ And the statement is false as
  of entry 113: `CurvatureCovOrder.contMDiffAt_covRiemann_hom` does the shift. **The paragraph is
  superseded in both halves**, and is kept as the record of what this file did not reach.
* **NOTHING AT `k = 0`.** Every theorem about `covRiemann` here carries `hk : k ≠ 0`, inherited
  from `CurvatureCovDeriv`, for the reason that file gives: a `C²` metric gives a `C⁰` curvature
  and there is no derivative to take.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `CurvatureCovDeriv`'s, which are
`RicciOrder`'s, with the same six local instances. Two declarations `omit` binders they do not
use. **One `set_option linter.unusedSectionVars false`**, scoped to `riemann_zero_left` and
carrying its reason in a comment: the linter names `[IsManifold I 1 M]`, and the `omit` it suggests
is **rejected by the elaborator** — `cannot omit referenced section variable` — because the binder
is reached through the instances `leviCivita` needs in order to be named at all. The suggestion was
tried before the option was set. Otherwise the linter reports nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureCovTensor

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor CurvatureCovDeriv
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

/-! ## 1. The induced connection depends only on the germ -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- Differentiability of a section of `Hom(TM, TM)` is a property of its germ. -/
theorem mdiffHomAt_congr {A A' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (hA : HomCovariant.MDiffHomAt A x) (h : ∀ᶠ y in 𝓝 x, A y = A' y) :
    HomCovariant.MDiffHomAt A' x := by
  refine hA.congr_of_eventuallyEq ?_
  filter_upwards [h] with y hy
  exact congrArg (TotalSpace.mk' (E →L[ℝ] E) y) hy.symm

omit [IsManifold I 3 M] in
/-- **THE INDUCED DERIVATIVE DEPENDS ONLY ON THE GERM OF `A`**, which is what the frame argument
below needs and what `HomCovariant` does not state. -/
theorem homCovFun_congr {A A' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (h : ∀ᶠ y in 𝓝 x, A y = A' y) :
    HomCovariant.homCovFun (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
        A x
      = HomCovariant.homCovFun
          (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) A' x := by
  by_cases hA : HomCovariant.MDiffHomAt A x
  · have hA' := mdiffHomAt_congr hA h
    ext u v
    rw [HomCovariant.homCovFun_apply hA, HomCovariant.homCovFun_apply hA']
    have hσ := mdifferentiableAt_extend (I := I) E v
    have hval : A x = A' x := h.self_of_nhds
    have hfield : ∀ᶠ y in 𝓝 x, A y (extend E v y) = A' y (extend E v y) := by
      filter_upwards [h] with y hy
      exact congrArg (fun T : TangentSpace I y →L[ℝ] TangentSpace I y ↦ T (extend E v y)) hy
    simp only [HomCovariant.homCovAux, hval]
    rw [leviCivita.isCovariantDerivativeOn.congr_of_eventuallyEq
      (HomCovariant.mdiffAt_apply hA hσ) (HomCovariant.mdiffAt_apply hA' hσ)
      Filter.univ_mem hfield]
  · have hA'' : ¬ HomCovariant.MDiffHomAt A' x := fun h' ↦
      hA (mdiffHomAt_congr h' (h.mono fun y hy ↦ hy.symm))
    simp [HomCovariant.homCovFun, dif_neg hA, dif_neg hA'']

/-! ## 2. Germ-locality and finite sums in the first direction -/

/-- **`covRiemann` DEPENDS ONLY ON THE GERM OF `Y`.** -/
theorem covRiemann_congr_left {Y Y' Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (h : ∀ᶠ y in 𝓝 x, Y y = Y' y)
    (u : TangentSpace I x) :
    covRiemann Y Z x u = covRiemann Y' Z x u := by
  have hfield : ∀ᶠ y in 𝓝 x, LeviCivitaRegular.riemann I y (Y y) (Z y)
      = LeviCivitaRegular.riemann I y (Y' y) (Z y) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hval : Y x = Y' x := h.self_of_nhds
  simp only [covRiemann, homCovFun_congr hfield, hval,
    leviCivita.isCovariantDerivativeOn.congr_of_eventuallyEq hY hY' Filter.univ_mem h]

set_option linter.unusedSectionVars false in
-- the linter names `[IsManifold I 1 M]`, and `omit`ting it is rejected by the elaborator:
-- the binder is referenced through the instances that `leviCivita` needs to be NAMED
/-- The curvature vanishes on a zero direction. -/
theorem riemann_zero_left (y : M) (w : TangentSpace I y) :
    LeviCivitaRegular.riemann I y 0 w = 0 := by
  simpa using CurvatureTensor.curvEndo_smul_left
    (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) y (0 : ℝ) 0 w

/-- And so does its covariant derivative. -/
theorem covRiemann_zero_left {Z : Π x : M, TangentSpace I x} {x : M} (u : TangentSpace I x) :
    covRiemann (0 : Π x : M, TangentSpace I x) Z x u = 0 := by
  have hhom : HomCovariant.homCovFun
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
      (fun y : M ↦ (0 : TangentSpace I y →L[ℝ] TangentSpace I y)) x = 0 :=
    (HomCovariant.isCovariantDerivativeOn_homCovFun (cov := leviCivita) univ).zero (mem_univ x)
  simp only [covRiemann, hhom, CovariantDerivative.zero,
    ContinuousLinearMap.zero_apply, Pi.zero_apply, riemann_zero_left, sub_self]

/-- **ADDITIVITY OVER A FINITE FAMILY IN THE FIRST DIRECTION**, which the frame expansion needs. -/
theorem covRiemann_sum_left {ι : Type*} (t : Finset ι) (Y : ι → Π x : M, TangentSpace I x)
    {Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : ∀ i, CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (Y i)) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    covRiemann (fun y ↦ ∑ i ∈ t, Y i y) Z x u = ∑ i ∈ t, covRiemann (Y i) Z x u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using covRiemann_zero_left (Z := Z) (x := x) u
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha, ← ih]
    exact covRiemann_add_left hk (hY a) (ContMDiffAt.sum_section fun i _ ↦ hY i) hZ u

/-! ## 3. Tensoriality -/

/-- **`covRiemann` IS A TENSOR IN THE FIRST DIRECTION**: it depends on `Y` only through `Y x`.
The route is `CurvatureTensor.curvAux_congr_of_eq_Z`'s — expand `Y` in the chart's local frame,
whose coefficients are of the same class, and use the slot laws term by term. Mathlib's
`TensorialAt` cannot be used, because its `smul` field is asked of every section merely
differentiable at the point while these laws need `C^(k+2)`. -/
theorem covRiemann_congr_of_eq_left {Y Y' Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hY' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y') x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hYY' : Y x = Y' x) (u : TangentSpace I x) :
    covRiemann Y Z x u = covRiemann Y' Z x u := by
  classical
  let t := trivializationAt E (TangentSpace I : M → Type _) x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := Module.Basis.ofVectorSpace ℝ E
  let s := t.localFrame b
  let c := t.localFrame_coeff I b
  have hs (i) : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (s i)) x :=
    contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1) _ b i x_mem
  have hc {σ : Π y : M, TangentSpace I y} (hσ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% σ) x) (i) :
      CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (LinearMap.piApply (c i) σ) x :=
    contMDiffAt_localFrame_coeff b x_mem hσ i
  have hexp {σ : Π y : M, TangentSpace I y} (hσ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% σ) x) :
      covRiemann σ Z x u
        = covRiemann (fun y ↦ ∑ i, ((LinearMap.piApply (c i) σ) • s i) y) Z x u :=
    covRiemann_congr_left (hσ.mdifferentiableAt (by simp))
      ((ContMDiffAt.sum_section fun i _ ↦
        (hc hσ i).smul_section (hs i)).mdifferentiableAt (by simp))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem) u
  rw [hexp hY, hexp hY',
    covRiemann_sum_left Finset.univ _ hk (fun i ↦ (hc hY i).smul_section (hs i)) hZ u,
    covRiemann_sum_left Finset.univ _ hk (fun i ↦ (hc hY' i).smul_section (hs i)) hZ u]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc covRiemann ((LinearMap.piApply (c i) Y) • (s i)) Z x u
      = c i x (Y x) • covRiemann (s i) Z x u :=
        covRiemann_smul_left hk ((hc hY i).mdifferentiableAt (by simp)) (hs i) hZ u
    _ = c i x (Y' x) • covRiemann (s i) Z x u := by rw [hYY']
    _ = covRiemann ((LinearMap.piApply (c i) Y') • (s i)) Z x u :=
        (covRiemann_smul_left hk ((hc hY' i).mdifferentiableAt (by simp)) (hs i) hZ u).symm

/-- **AND IN THE SECOND**, through the antisymmetry. -/
theorem covRiemann_congr_of_eq_right {Y Z Z' : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hZ' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z') x)
    (hZZ' : Z x = Z' x) (u : TangentSpace I x) :
    covRiemann Y Z x u = covRiemann Y Z' x u := by
  rw [covRiemann_swap hk hY hZ u, covRiemann_swap hk hY hZ' u,
    covRiemann_congr_of_eq_left hk hZ hZ' hY hZZ' u]

end CurvatureCovTensor
