import KoszulRegular

/-!
# From `C¹` pairings with a local frame to a `C¹` section: the Gram-inverse leg

`KoszulRegular` proved the first half of the regularity of the Levi-Civita connection — the Koszul
scalar `y ↦ ⟨∇_Y Z, W⟩(y)` is `C¹` for `Y, Z, W` of class `C²` and a `C²` metric — and said in its
fence what the second half still needed: *a local frame `sⱼ` and the inverse of its Gram matrix
`⟨sⱼ, sₖ⟩`*, and after that the Hom-bundle criterion. This file is the Gram matrix. **A section
whose pairings with a `C¹` local frame are `C¹` at a point is itself `C¹` there**
(`contMDiffAt_of_contMDiffAt_inner`), and so **`y ↦ ∇_Y Z(y)` is a `C¹` section for `Y, Z` of
class `C²`** (`contMDiffAt_leviCivita_apply`).

The argument is linear algebra in a moving frame, done once in the ring of operators on `ι → ℝ`.
The Gram operator `G(y)` of the frame — the matrix `⟨sᵢ(y), sⱼ(y)⟩` — is `C¹` in `y` because the
metric and the frame are (`ContMDiffAt.inner_bundle`); it is invertible wherever the frame is
linearly independent, because `G(y)c = 0` forces `⟨∑ cᵢsᵢ, ∑ cⱼsⱼ⟩ = 0`; and the inverse of a unit
is analytic in the operator ring (Mathlib's `contDiffAt_ringInverse`, the Neumann series). The
coefficients of the section `t` in the frame are then `G(y)⁻¹` applied to the pairings
`⟨t(y), sⱼ(y)⟩` (`coeff_eq_inverse_gram`), a `C¹` function of `y`, and Mathlib's
`IsLocalFrameOn.contMDiffAt_of_coeff` turns `C¹` coefficients into a `C¹` section.

## What is proved

**`matrixOp`, `matrixOp_apply`** — a matrix as an operator on `ι → ℝ`, continuously and linearly
in the matrix (`Matrix.toLin'` behind `LinearMap.toContinuousLinearMap`).

**`gram`, `gram_apply`** — the Gram operator of a family of sections at a point,
`(G(y)c)ⱼ = ⟨∑ᵢ cᵢ sᵢ(y), sⱼ(y)⟩`.

**`gram_injective`, `gram_isUnit`** — **where the family is linearly independent, its Gram
operator is a unit** of the operator ring. No spanning is needed.

**`coeff_eq_inverse_gram`** — **the coefficients of a section in a local frame are the inverse
Gram operator applied to its pairings with the frame**, at every point of the frame's domain.

**`contMDiffAt_gram`** — the Gram operator of `C¹` sections is `C¹`, for a `C¹` metric.

**`contMDiffAt_of_contMDiffAt_inner`** — **THE GRAM-INVERSE LEG**: given a `C^n` local frame
(`n ≥ 1`) on a neighbourhood of `x`, a section whose pairings with the frame are `C¹` at `x` is
`C¹` at `x`. A `C¹` metric suffices.

**`contMDiffAt_leviCivita_apply`** — **`y ↦ ∇_Y Z(y)` IS A `C¹` SECTION** for `Y, Z` of class `C²`
at `x` and a `C²` metric, `∇` the Levi-Civita connection of `KoszulManifold`: the frame is
Mathlib's `Trivialization.localFrame` of the tangent bundle's chart at `x`, `C²` there, and the
pairings are `KoszulRegular.contMDiffAt_inner_leviCivita`.

## What is NOT here

**`IsLocallyC1 leviCivita`, AND WHAT IT STILL NEEDS.** What is proved is that `∇_Y Z` is `C¹` for
each `C²` field `Y`; what `CurvatureTensor.IsLocallyC1` asks is that `y ↦ ∇Z(y)`, a section of
the endomorphism bundle `Hom(TM, TM)`, is `C¹` on every open set on which `Z` is `C²`. From the
one to the other is Mathlib's `contMDiffAt_hom_bundle` criterion in coordinates — a `Hom`-valued
section is `C¹` when its coordinate matrix is, and the columns of that matrix are the trivialized
values of `∇_{sᵢ} Z` for the frame `sᵢ` of the chart — and it is not started. **Not attempted, no
cost claimed** (`ERRATUM 246`). ⚠ By entry 72, later the same day, it is started and finished:
`LeviCivitaRegular.contMDiffAt_hom_of_localFrame` is the criterion applied to the chart's frame,
`LeviCivitaRegular.contMDiffAt_leviCivita_hom` is the section, and
`LeviCivitaRegular.isLocallyC1_leviCivita` is the instance.

**NO CURVATURE OF A METRIC**, therefore. `IsLocallyC1` is the hypothesis under which
`CurvatureTensor.curvEndo`, `RicciScalar.ricci` and `RicciScalar.scalar` are defined, and
`leviCivita` is not shown to satisfy it here, so none of the three is yet evaluated on the
Levi-Civita connection of any metric. ⚠ By entry 72 all three are: `LeviCivitaRegular.riemann`,
`LeviCivitaRegular.ricci`, `LeviCivitaRegular.scalar`.

**ONLY `C¹`.** The Gram-inverse leg is stated for `C¹` pairings and a `C¹` conclusion, which is what
one derivative of the connection costs and what curvature needs. The same argument gives `C^k`
from `C^k` pairings, a `C^k` frame and a `C^k` metric — `contDiffAt_ringInverse` is analytic and
`IsLocalFrameOn.contMDiffAt_of_coeff` is stated at every order — and it is not stated here,
because the tangent bundle of the pinned Mathlib is registered as a `C^k` bundle only for
`k = 1, ∞, ω` and, in this estate, locally for `k = 2`; **the higher-order regularity of the
Levi-Civita connection of a `C^{k+1}` metric is untouched**.

**NO ORTHONORMAL FRAME.** Nothing here orthonormalises; the frame is the chart's, its Gram matrix
is whatever the metric makes it, and the inverse is taken in the operator ring.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `matrixOp` and `matrixOp_apply` take a
`Fintype ι` with `DecidableEq ι` (Mathlib's hypotheses for `Matrix.toLin'`) and nothing else;
`gram` to `gram_isUnit` add `[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, a `ChartedSpace H M`
with model `I` and `[RiemannianBundle (fun x ↦ TangentSpace I x)]` — no manifold structure, no
smoothness of the metric; `coeff_eq_inverse_gram` adds `[IsManifold I 1 M]` (the tangent bundle,
for `IsLocalFrameOn`); `contMDiffAt_gram` and `contMDiffAt_of_contMDiffAt_inner` take
`[IsManifold I 2 M]` (the tangent bundle as a `C¹` bundle) and
`[IsContMDiffRiemannianBundle I 1 E (TangentSpace I)]` — a **`C¹`** metric — and the latter
`[FiniteDimensional ℝ E]`, Mathlib's hypothesis for `IsLocalFrameOn.contMDiffAt_of_coeff`, and
only `Finite ι` for its index type;
`contMDiffAt_leviCivita_apply` takes what `KoszulRegular.contMDiffAt_inner_leviCivita` takes:
`[IsManifold I 3 M]`, `[CompleteSpace E]`, `[FiniteDimensional ℝ E]` and a `C²` metric.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FrameRegular

open Bundle Manifold VectorField FiberBundle Set KoszulManifold KoszulRegular
open scoped Bundle ContDiff Topology

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A matrix `A`, as the operator `c ↦ (j ↦ ∑ i, A j i * c i)` on `ι → ℝ`, continuously and
linearly in `A`. -/
noncomputable def matrixOp : (ι → ι → ℝ) →L[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap :
        ((ι → ℝ) →ₗ[ℝ] (ι → ℝ)) ≃ₗ[ℝ] ((ι → ℝ) →L[ℝ] (ι → ℝ))).toLinearMap ∘ₗ
      (Matrix.toLin' : Matrix ι ι ℝ ≃ₗ[ℝ] ((ι → ℝ) →ₗ[ℝ] (ι → ℝ))).toLinearMap)

theorem matrixOp_apply (A : ι → ι → ℝ) (c : ι → ℝ) (j : ι) :
    matrixOp A c j = ∑ i, A j i * c i := by
  change (Matrix.toLin' (Matrix.of A)) c j = _
  simp [Matrix.mulVec, dotProduct]

end Matrix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

section Gram

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Gram operator of a family of sections at a point: the operator on `ι → ℝ` with matrix
`⟪s i y, s j y⟫`, so that `gram s y c = (j ↦ ⟪∑ i, c i • s i y, s j y⟫)`. -/
noncomputable def gram (s : ι → Π x : M, TangentSpace I x) (y : M) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  matrixOp (fun j i ↦ ⟪s i y, s j y⟫)

theorem gram_apply (s : ι → Π x : M, TangentSpace I x) (y : M) (c : ι → ℝ) (j : ι) :
    gram s y c j = ⟪∑ i, c i • s i y, s j y⟫ := by
  simp [gram, matrixOp_apply, sum_inner, real_inner_smul_left, mul_comm]

/-- **Where the family is linearly independent, its Gram operator is injective.** -/
theorem gram_injective {s : ι → Π x : M, TangentSpace I x} {y : M}
    (hli : LinearIndependent ℝ (s · y)) : Function.Injective (gram s y) := by
  refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
  have h1 : ∀ j, ⟪∑ i, c i • s i y, s j y⟫ = 0 := fun j ↦ by
    have := congrFun hc j
    rwa [gram_apply] at this
  have h2 : ⟪∑ i, c i • s i y, ∑ j, c j • s j y⟫ = 0 := by
    rw [inner_sum]
    simp [real_inner_smul_right, h1]
  have hw : (∑ i, c i • s i y) = 0 := inner_self_eq_zero.1 h2
  funext i
  exact Fintype.linearIndependent_iff.1 hli c hw i

/-- **… and so it is a unit of the operator ring on `ι → ℝ`.** -/
theorem gram_isUnit {s : ι → Π x : M, TangentSpace I x} {y : M}
    (hli : LinearIndependent ℝ (s · y)) : IsUnit (gram s y) := by
  have hinj := gram_injective hli
  have hsurj : Function.Surjective (gram s y) :=
    (LinearMap.injective_iff_surjective (f := (gram s y : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)))).1 hinj
  let e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
    (LinearEquiv.ofBijective (gram s y : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
      ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  exact ⟨e.toUnit, ContinuousLinearMap.ext fun c ↦ rfl⟩

end Gram

section Frame

variable [IsManifold I 1 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The coefficients of a section in a local frame are the inverse Gram operator applied to its
pairings with the frame.** -/
theorem coeff_eq_inverse_gram {s : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E 1 s u) (t : Π x : M, TangentSpace I x) {y : M} (hy : y ∈ u) :
    (fun i ↦ hs.coeff i y (t y)) = Ring.inverse (gram s y) (fun j ↦ ⟪t y, s j y⟫) := by
  have hunit : IsUnit (gram s y) := gram_isUnit (hs.linearIndependent hy)
  have hc : gram s y (fun i ↦ hs.coeff i y (t y)) = fun j ↦ ⟪t y, s j y⟫ := by
    funext j
    simp only [gram_apply]
    rw [← hs.coeff_sum_eq t hy]
  calc (fun i ↦ hs.coeff i y (t y))
      = (Ring.inverse (gram s y) * gram s y) (fun i ↦ hs.coeff i y (t y)) := by
        rw [Ring.inverse_mul_cancel _ hunit, ContinuousLinearMap.one_apply]
    _ = Ring.inverse (gram s y) (fun j ↦ ⟪t y, s j y⟫) := by
        rw [ContinuousLinearMap.mul_apply, hc]

end Frame

section Smooth

variable [IsManifold I 2 M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Gram operator of `C¹` sections is `C¹`**, the metric being `C¹`. -/
theorem contMDiffAt_gram {s : ι → Π x : M, TangentSpace I x} {x : M}
    (hs : ∀ i, CMDiffAt 1 (T% (s i)) x) :
    ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) 1 (gram s) x := by
  have hG : ContMDiffAt I 𝓘(ℝ, ι → ι → ℝ) 1 (fun y j i ↦ ⟪s i y, s j y⟫) x :=
    contMDiffAt_pi_space.2 fun j ↦ contMDiffAt_pi_space.2 fun i ↦
      ContMDiffAt.inner_bundle (E := (TangentSpace I : M → Type _)) (hs i) (hs j)
  exact matrixOp.contMDiffAt.comp x hG

variable [FiniteDimensional ℝ E]

omit [Fintype ι] [DecidableEq ι] in
/-- **FROM `C¹` PAIRINGS WITH A LOCAL FRAME TO A `C¹` SECTION.** -/
theorem contMDiffAt_of_contMDiffAt_inner [Finite ι] {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {s : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E n s u) {x : M}
    (hu : u ∈ 𝓝 x) {t : Π x : M, TangentSpace I x}
    (ht : ∀ j, ContMDiffAt I 𝓘(ℝ) 1 (fun y ↦ ⟪t y, s j y⟫) x) :
    CMDiffAt 1 (T% t) x := by
  cases nonempty_fintype ι
  classical
  have hs1 : IsLocalFrameOn I E 1 s u :=
    { linearIndependent := hs.linearIndependent
      generating := hs.generating
      contMDiffOn := fun i ↦ (hs.contMDiffOn i).of_le hn }
  have hsx : ∀ i, CMDiffAt 1 (T% (s i)) x := fun i ↦ (hs1.contMDiffOn i).contMDiffAt hu
  have hunit : IsUnit (gram s x) := gram_isUnit (hs.linearIndependent (mem_of_mem_nhds hu))
  have hg : ContDiffAt ℝ 1 Ring.inverse (gram s x) := contDiffAt_ringInverse ℝ hunit.unit
  have hinv : ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) 1 (fun y ↦ Ring.inverse (gram s y)) x :=
    hg.comp_contMDiffAt (contMDiffAt_gram hsx)
  have hb : ContMDiffAt I 𝓘(ℝ, ι → ℝ) 1 (fun y j ↦ ⟪t y, s j y⟫) x := contMDiffAt_pi_space.2 ht
  have hc : ContMDiffAt I 𝓘(ℝ, ι → ℝ) 1
      (fun y ↦ Ring.inverse (gram s y) (fun j ↦ ⟪t y, s j y⟫)) x := hinv.clm_apply hb
  refine hs1.contMDiffAt_of_coeff (fun i ↦ ?_) hu
  refine (contMDiffAt_pi_space.1 hc i).congr_of_eventuallyEq ?_
  filter_upwards [hu] with y hy
  exact congrFun (coeff_eq_inverse_gram hs1 t hy) i

end Smooth

section LeviCivita

variable [IsManifold I 3 M] [CompleteSpace E] [FiniteDimensional ℝ E]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

/-- **`y ↦ ∇_Y Z (y)` IS `C¹`** for `Y, Z` of class `C²` at `x`, `∇` the Levi-Civita connection of a
`C²` metric. -/
theorem contMDiffAt_leviCivita_apply {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    CMDiffAt 1 (T% (fun y ↦ leviCivita Z y (Y y))) x := by
  haveI : IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := 2) (by norm_num)
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  refine contMDiffAt_of_contMDiffAt_inner (n := 2) (by norm_num)
    (e.isLocalFrameOn_localFrame_baseSet I 2 b) (e.open_baseSet.mem_nhds hx) fun j ↦ ?_
  exact contMDiffAt_inner_leviCivita hY hZ (contMDiffAt_localFrame_of_mem 2 _ b j hx)

end LeviCivita

end FrameRegular
