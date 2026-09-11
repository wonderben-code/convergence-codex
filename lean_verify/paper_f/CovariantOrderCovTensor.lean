import CovariantOrderCovDeriv
import CurvatureCovTensor

/-!
# `∇R` is a tensor in both directions, for ANY connection of class `C^(k+1)`

**The `B` that `PROOF_STRATEGY` §6 named at the end of the last unit**, and the next file of the
re-definition `ERRATUM 498` priced. `CurvatureCovDeriv`'s six slot laws say `∇R` is additive and
`f`-homogeneous in each direction **as an operation on sections**; this file turns that into the
statement that makes it a tensor — **it depends on `Y` and `Z` only through `Y x` and `Z x`** — for
an arbitrary connection, where `CurvatureCovTensor` has it for the Levi-Civita one.

**MEASURED BEFORE WRITING, AS THE LAST FOUR UNITS HAVE BEEN**: `CurvatureCovTensor`'s declarations
use no Levi-Civita-specific **lemma** at all. What they use is `leviCivita` itself (seven times, as
the connection whose induced derivative is being differentiated) and `LeviCivitaRegular.riemann`,
which is an `abbrev` for `curvEndo leviCivita`. Everything else — `HomCovariant`'s induced
operation and its tensoriality, `CurvatureTensor.curvEndo_smul_left`, `CovariantDerivative.zero`,
and Mathlib's frame and `Finset` machinery — is already general. So this is a substitution of
spellings, and the one thing that had to be proved rather than renamed is the curvature's vanishing
on a zero direction, which the Levi-Civita file states for `riemann` and nobody had stated for
`curvEndo`.

**WHY IT IS NOT `TensorialAt`.** Mathlib's class asks its `smul` field of every section merely
differentiable at the point, and these laws need `C^(k+2)`; `CurvatureCovTensor`'s header says so
and the same obstruction applies here, one generality up.

## What is proved

**`mdiffHomAt_congr'`** — differentiability of a section of `Hom(TM, TM)` is a property of its germ.
`CurvatureCovTensor.mdiffHomAt_congr` is this statement, and it is restated here because **its
context carries a `[RiemannianBundle …]` binder the fact does not need** — read from `#check`, not
from its `omit` line, which drops five binders and not that one. Entry 123 found the same thing in
`HomCovariantOrder`'s two neighbourhood helpers, and the watchlist item filed there now has a third
instance.

**`homCovFun_congr`** — **THE INDUCED DERIVATIVE DEPENDS ONLY ON THE GERM OF `A`**, for any
connection, which is what the frame argument needs and what `HomCovariant` does not state. The
`¬ MDiffHomAt` branch is the junk-value convention agreeing with itself on both sides.

**`curvEndo_zero_left`** — the curvature of any connection vanishes on a zero direction, from
`curvEndo_smul_left` at `c = 0`. The general form of `CurvatureCovTensor.riemann_zero_left`, which
that file proves for `riemann` in one line and which no file states for `curvEndo`.

**`covRiemann_congr_left`**, **`covRiemann_zero_left`**, **`covRiemann_sum_left`** — germ-locality,
vanishing, and additivity over a finite family in the first direction: the three facts the frame
expansion consumes.

**`covRiemann_congr_of_eq_left`** — **THE THEOREM: `∇R` IS A TENSOR IN THE FIRST DIRECTION** for any
connection of class `C^(k+1)`. Expand `Y` in the chart's local frame, whose coefficients are of the
same class, and apply the slot laws term by term.

**`covRiemann_congr_of_eq_right`** — **AND IN THE SECOND**, through entry 124's antisymmetry.

**`covRiemann_congr_of_eq_left_leviCivita`** — **AND `CurvatureCovTensor`'S THEOREM IS THAT,
SPECIALISED, ON BINDERS THAT AGREE ONE FOR ONE** — checked with `#check` on both, which print the
same signature from `[IsManifold I 1 M]` through `[IsContMDiffRiemannianBundle I 2 …]` — with
`CovariantOrderCovDeriv.covRiemann_eq` (`rfl`) identifying the objects. The fourth checked
subsumption in five units, and the fourth deliberate duplicate under a different name — recorded by
hand, because `dupname_scan.py` cannot see that kind.

## What is NOT here

* **NO SECOND BIANCHI IDENTITY.** This file is that identity's `B`, not the identity: the cyclic
  sum is a statement about the tensor, and `CurvatureBianchiSecond` proves it for the Levi-Civita
  connection with three derivatives of the differentiated field. **Not attempted, no cost claimed**
  (`ERRATUM 246`).
* **NOTHING ON VECTORS RATHER THAN FIELDS**, and nothing bundled: `CurvatureCovBundle`'s
  `covRiemannAt` takes the extensions of tangent vectors, and this file's theorem is exactly the
  tensoriality such a construction consumes — so it is the next file after this one, not this one.
* **NO TRACE, NO DIVERGENCE**, for the standing reason: a trace needs a metric.
* **NOTHING AT THE ANALYTIC ORDER**, `k` being a natural number.
⚠ **`∞` IS REACHED ON 2026-09-11 AND `ω` IS NOT, kept as written** (`ERRATUM 505`):
`CovariantOrderInfty` states this file's results at the **smooth** order — the class at `∞` is the
class at every finite order (`isLocallyCk_infty_of_nat`), the Levi-Civita connection of a `C^∞`
metric is in it, and the curvature, `∇R` and the second Bianchi identity follow. **The sentence is
still true of `ω`**, which has no *`C^n` for every `n`* characterisation, and true of this file,
which proves nothing at either.

**No wall moves. No published tag moves.**

**THE NAMES COLLIDE WITH `CurvatureCovTensor`'S ON PURPOSE**, as entry 124's did with
`CurvatureCovDeriv`'s, and the reason is the same and is a theorem: `covRiemann_eq` identifies the
two objects by `rfl`, so the names denote one thing at two generalities. Recorded in
`newnames_accepted.txt`.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `E` normed over `ℝ` with `[CompleteSpace E]`
and `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]`, `[IsManifold I 3 M]`, `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]`,
`[CurvatureTensor.IsLocallyC1 cov]`, and `[CovariantOrderClass.IsLocallyCk ((k : WithTop ℕ∞) + 1)
cov]` with `k ≠ 0` wherever entry 124's slot laws are used — **no metric at any order**, where
`CurvatureCovTensor` asks for a `C^(k+2)` metric and its companion at `2`. Counted from the
signatures, over the **nine** declarations: **six** take `[IsLocallyC1 cov]`, **three** also take
the order class, **four** take `k ≠ 0`, and exactly **one** takes a metric — the subsumption, which
takes no connection at all. The two germ lemmas take neither class, which is why they could be
stated before the order hypothesis enters.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CovariantOrderCovTensor

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

/-! ## 1. The induced connection depends only on the germ -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M] [CurvatureTensor.IsLocallyC1 cov] in
/-- Differentiability of a section of `Hom(TM, TM)` is a property of its germ.
`CurvatureCovTensor.mdiffHomAt_congr` is this statement inside a `RiemannianBundle` context; the
fact needs no metric, which is what this restatement demonstrates. -/
theorem mdiffHomAt_congr' {A A' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (hA : HomCovariant.MDiffHomAt A x) (h : ∀ᶠ y in 𝓝 x, A y = A' y) :
    HomCovariant.MDiffHomAt A' x := by
  refine hA.congr_of_eventuallyEq ?_
  filter_upwards [h] with y hy
  exact congrArg (TotalSpace.mk' (E →L[ℝ] E) y) hy.symm

omit [CompleteSpace E] [IsManifold I 3 M] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [CurvatureTensor.IsLocallyC1 cov] in
/-- **THE INDUCED DERIVATIVE DEPENDS ONLY ON THE GERM OF `A`**, for any connection — what the frame
argument below needs and what `HomCovariant` does not state. -/
theorem homCovFun_congr {A A' : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (h : ∀ᶠ y in 𝓝 x, A y = A' y) :
    HomCovariant.homCovFun cov A x = HomCovariant.homCovFun cov A' x := by
  by_cases hA : HomCovariant.MDiffHomAt A x
  · have hA' := mdiffHomAt_congr' hA h
    ext u v
    rw [HomCovariant.homCovFun_apply hA, HomCovariant.homCovFun_apply hA']
    have hσ := mdifferentiableAt_extend (I := I) E v
    have hval : A x = A' x := h.self_of_nhds
    have hfield : ∀ᶠ y in 𝓝 x, A y (extend E v y) = A' y (extend E v y) := by
      filter_upwards [h] with y hy
      exact congrArg (fun T : TangentSpace I y →L[ℝ] TangentSpace I y ↦ T (extend E v y)) hy
    simp only [HomCovariant.homCovAux, hval]
    rw [cov.isCovariantDerivativeOn.congr_of_eventuallyEq
      (HomCovariant.mdiffAt_apply hA hσ) (HomCovariant.mdiffAt_apply hA' hσ)
      Filter.univ_mem hfield]
  · have hA'' : ¬ HomCovariant.MDiffHomAt A' x := fun h' ↦
      hA (mdiffHomAt_congr' h' (h.mono fun y hy ↦ hy.symm))
    simp [HomCovariant.homCovFun, dif_neg hA, dif_neg hA'']

/-! ## 2. Germ-locality, vanishing and finite sums in the first direction -/

/-- **`covRiemann` DEPENDS ONLY ON THE GERM OF `Y`.** -/
theorem covRiemann_congr_left {Y Y' Z : Π x : M, TangentSpace I x} {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (h : ∀ᶠ y in 𝓝 x, Y y = Y' y)
    (u : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x u
      = CovariantOrderCovDeriv.covRiemann cov Y' Z x u := by
  have hfield : ∀ᶠ y in 𝓝 x, curvEndo cov y (Y y) (Z y) = curvEndo cov y (Y' y) (Z y) := by
    filter_upwards [h] with y hy
    rw [hy]
  have hval : Y x = Y' x := h.self_of_nhds
  simp only [CovariantOrderCovDeriv.covRiemann, homCovFun_congr cov hfield, hval,
    cov.isCovariantDerivativeOn.congr_of_eventuallyEq hY hY' Filter.univ_mem h]

omit [IsManifold I 2 M] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M] in
/-- **THE CURVATURE OF ANY CONNECTION VANISHES ON A ZERO DIRECTION**, from `curvEndo_smul_left` at
`c = 0`. `CurvatureCovTensor.riemann_zero_left` is this for `riemann`; no file states it for
`curvEndo`. -/
theorem curvEndo_zero_left (y : M) (w : TangentSpace I y) : curvEndo cov y 0 w = 0 := by
  simpa using curvEndo_smul_left cov y (0 : ℝ) 0 w

/-- And so does its covariant derivative. -/
theorem covRiemann_zero_left {Z : Π x : M, TangentSpace I x} {x : M} (u : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov (0 : Π x : M, TangentSpace I x) Z x u = 0 := by
  have hhom : HomCovariant.homCovFun cov
      (fun y : M ↦ (0 : TangentSpace I y →L[ℝ] TangentSpace I y)) x = 0 :=
    (HomCovariant.isCovariantDerivativeOn_homCovFun (cov := cov) univ).zero (mem_univ x)
  simp only [CovariantOrderCovDeriv.covRiemann, hhom, CovariantDerivative.zero,
    ContinuousLinearMap.zero_apply, Pi.zero_apply, curvEndo_zero_left, sub_self]

variable [IsLocallyCk ((k : WithTop ℕ∞) + 1) cov]

/-- **ADDITIVITY OVER A FINITE FAMILY IN THE FIRST DIRECTION**, which the frame expansion needs. -/
theorem covRiemann_sum_left {ι : Type*} (t : Finset ι) (Y : ι → Π x : M, TangentSpace I x)
    {Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : ∀ i, CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (Y i)) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) (u : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov (fun y ↦ ∑ i ∈ t, Y i y) Z x u
      = ∑ i ∈ t, CovariantOrderCovDeriv.covRiemann cov (Y i) Z x u := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using covRiemann_zero_left cov (Z := Z) (x := x) u
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha, ← ih]
    exact CovariantOrderCovDeriv.covRiemann_add_left cov hk (hY a)
      (ContMDiffAt.sum_section fun i _ ↦ hY i) hZ u

/-! ## 3. Tensoriality -/

/-- **`∇R` IS A TENSOR IN THE FIRST DIRECTION** for any connection of class `C^(k+1)`: it depends on
`Y` only through `Y x`. Expand `Y` in the chart's local frame, whose coefficients are of the same
class, and use entry 124's slot laws term by term. Mathlib's `TensorialAt` cannot be used, because
its `smul` field is asked of every section merely differentiable at the point while these laws need
`C^(k+2)`. -/
theorem covRiemann_congr_of_eq_left {Y Y' Z : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hY' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y') x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hYY' : Y x = Y' x) (u : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x u
      = CovariantOrderCovDeriv.covRiemann cov Y' Z x u := by
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
      CovariantOrderCovDeriv.covRiemann cov σ Z x u
        = CovariantOrderCovDeriv.covRiemann cov
            (fun y ↦ ∑ i, ((LinearMap.piApply (c i) σ) • s i) y) Z x u :=
    covRiemann_congr_left cov (hσ.mdifferentiableAt (by simp))
      ((ContMDiffAt.sum_section fun i _ ↦
        (hc hσ i).smul_section (hs i)).mdifferentiableAt (by simp))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem) u
  rw [hexp hY, hexp hY',
    covRiemann_sum_left cov Finset.univ _ hk (fun i ↦ (hc hY i).smul_section (hs i)) hZ u,
    covRiemann_sum_left cov Finset.univ _ hk (fun i ↦ (hc hY' i).smul_section (hs i)) hZ u]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  calc CovariantOrderCovDeriv.covRiemann cov ((LinearMap.piApply (c i) Y) • (s i)) Z x u
      = c i x (Y x) • CovariantOrderCovDeriv.covRiemann cov (s i) Z x u :=
        CovariantOrderCovDeriv.covRiemann_smul_left cov hk
          ((hc hY i).mdifferentiableAt (by simp)) (hs i) hZ u
    _ = c i x (Y' x) • CovariantOrderCovDeriv.covRiemann cov (s i) Z x u := by rw [hYY']
    _ = CovariantOrderCovDeriv.covRiemann cov ((LinearMap.piApply (c i) Y') • (s i)) Z x u :=
        (CovariantOrderCovDeriv.covRiemann_smul_left cov hk
          ((hc hY' i).mdifferentiableAt (by simp)) (hs i) hZ u).symm

/-- **AND IN THE SECOND**, through entry 124's antisymmetry. -/
theorem covRiemann_congr_of_eq_right {Y Z Z' : Π x : M, TangentSpace I x} {x : M} (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hZ' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z') x)
    (hZZ' : Z x = Z' x) (u : TangentSpace I x) :
    CovariantOrderCovDeriv.covRiemann cov Y Z x u
      = CovariantOrderCovDeriv.covRiemann cov Y Z' x u := by
  rw [CovariantOrderCovDeriv.covRiemann_swap cov hk hY hZ u,
    CovariantOrderCovDeriv.covRiemann_swap cov hk hY hZ' u,
    covRiemann_congr_of_eq_left cov hk hZ hZ' hY hZZ' u]

section LeviCivita

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self

/-- **AND `CurvatureCovTensor`'S TENSORIALITY IS THIS ONE SPECIALISED**, with
`CovariantOrderCovDeriv.covRiemann_eq` (`rfl`) identifying the objects and
`CovariantOrderClass.isLocallyCk_leviCivita` supplying the class. A theorem rather than a remark so
the subsumption is checked; and therefore a deliberate duplicate under a different name. -/
theorem covRiemann_congr_of_eq_left_leviCivita {Y Y' Z : Π x : M, TangentSpace I x} {x : M}
    (hk : k ≠ 0)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y) x)
    (hY' : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Y') x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (hYY' : Y x = Y' x) (u : TangentSpace I x) :
    CurvatureCovDeriv.covRiemann Y Z x u = CurvatureCovDeriv.covRiemann Y' Z x u := by
  have e : (((k + 1 : ℕ) : WithTop ℕ∞)) = (k : WithTop ℕ∞) + 1 := by push_cast; ring
  haveI : IsLocallyCk ((k : WithTop ℕ∞) + 1)
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) := by
    rw [← e]
    exact CovariantOrderClass.isLocallyCk_leviCivita (k := k + 1)
  rw [← CovariantOrderCovDeriv.covRiemann_eq Y Z x u,
    ← CovariantOrderCovDeriv.covRiemann_eq Y' Z x u]
  exact covRiemann_congr_of_eq_left _ hk hY hY' hZ hYY' u

end LeviCivita

end CovariantOrderCovTensor
