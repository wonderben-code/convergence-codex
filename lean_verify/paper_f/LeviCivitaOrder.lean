import KoszulOrder
import LeviCivitaRegular

/-!
# The Levi-Civita connection of a `C^(k+1)` metric is `C^k`: the order restriction lifted

`KoszulOrder` carried the first half of the Levi-Civita regularity to every finite order and said
in its fence what was left at one derivative alone: the passage from pairings with a frame to a
section (`FrameRegular`'s Gram-inverse leg) and from there to a section of the endomorphism
bundle (`LeviCivitaRegular`'s leg). Both are lifted here. **For `k : ℕ`, a `C^(k+2)` manifold and
a `C^(k+1)` metric, `y ↦ ∇_Y Z(y)` is a `C^k` section for `Y, Z` of class `C^(k+1)`, `y ↦ ∇Z(y)`
is a `C^k` section of `Hom(TM, TM)`, and the Levi-Civita connection is `C^k` on every open set in
Mathlib's own sense** (`contMDiffCovariantDerivativeOn_leviCivita`). At `k = 1` these are
`FrameRegular`'s, `LeviCivitaRegular`'s and `CurvatureTensor.IsLocallyC1`'s statements.

The two legs generalise without a new idea, which is why they were worth doing at once. The Gram
operator's invertibility never mentioned smoothness (`FrameRegular.gram_isUnit`), the inverse of a
unit is analytic (`contDiffAt_ringInverse`), Mathlib's frame criterion
(`IsLocalFrameOn.contMDiffAt_of_coeff`) and its coordinate criterion for `Hom`-valued sections
(`contMDiffAt_hom_bundle`) are stated at every order, and the coefficient formula needed only the
frame's basis property, so it is restated here with the frame's order as a variable
(`coeff_eq_inverse_gram`). What the order costs is again instances, and they are `KoszulOrder`'s.

## What is proved

**`coeff_eq_inverse_gram`** — the coefficients of a section in a local frame **of any order** are
the inverse Gram operator applied to its pairings with the frame.

**`contMDiffAt_gram`** — the Gram operator of `C^k` sections is `C^k`, for a `C^(k+1)` metric.

**`contMDiffAt_of_contMDiffAt_inner`** — **THE GRAM-INVERSE LEG AT ORDER `k`**: a section whose
pairings with a `C^m` local frame (`m ≥ k`) are `C^k` at a point is `C^k` there.

**`contMDiffAt_hom_of_localFrame`** — **THE ENDOMORPHISM-BUNDLE LEG AT EVERY ORDER**: a section of
`Hom(TM, TM)` is `C^n` at `x` as soon as its values on the chart's local frame are `C^n` sections.

**`contMDiffAt_leviCivita_apply`** — **`y ↦ ∇_Y Z(y)` is a `C^k` section** for `Y, Z` of class
`C^(k+1)` at `x`.

**`contMDiffAt_leviCivita_hom`** — **`y ↦ ∇Z(y)` is a `C^k` section of `Hom(TM, TM)`** for `Z` of
class `C^(k+1)` at `x`.

**`contMDiffCovariantDerivativeOn_leviCivita`** — **THE LEVI-CIVITA CONNECTION OF A `C^(k+1)`
METRIC IS `C^k` ON EVERY OPEN SET**, as Mathlib's `ContMDiffCovariantDerivativeOn E k`.

## What is NOT here

**NO `IsLocallyCk` CLASS, AND SO NO CURVATURE AT ORDER `k`.** `CurvatureTensor` is written against
the class `IsLocallyC1`, whose field is the `k = 1` case of the theorem proved here; an
order-parametrised class and an order-parametrised `curvEndo` are not written, so **the curvature
of a `C^(k+2)` metric is not shown to be `C^(k-1)`**, and the curvature machinery still applies to
`leviCivita` only at `k = 1` (through `LeviCivitaRegular.isLocallyC1_leviCivita`, which this file
does not replace). That is the next object and it is not started. **Not attempted, no cost
claimed** (`ERRATUM 246`).

**NOTHING ABOUT `a₂`.** `WALLS` §W5's last rung needs an asymptotic expansion of `Tr f(D/Λ)`,
which needs derivatives of the curvature — hence this file — and then a parametrix construction,
which no part of this estate has. The order restriction was the first of those two obstacles and
is the only one this file touches.

**ONLY FINITE ORDERS**, as in `KoszulOrder`, and for the same reason: the passage from a point to
a neighbourhood uses `contMDiffAt_iff_contMDiffOn_nhds`, which asks for a finite order.

**NO ORTHONORMAL FRAME AND NO NEW ANALYSIS.** Every step is one of `KoszulOrder`'s theorems, one
of Mathlib's order-parametrised lemmas, or an instance; nothing here is proved by a new estimate.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]`,
`[IsManifold I 2 M]` and `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]` at the top with `omit` on the
lemmas that need fewer; `[RiemannianBundle (fun x ↦ TangentSpace I x)]` from section `Frame`,
`[IsContMDiffRiemannianBundle I (k + 1) E (TangentSpace I)]` from the Gram operator on,
`[FiniteDimensional ℝ E]` from the Gram-inverse leg on, and `[IsContMDiffRiemannianBundle I 1 E
(TangentSpace I)]` in section `LeviCivita` — implied by the `C^(k+1)` metric, and what `leviCivita`
asks for. `KoszulOrder`'s three instances are registered locally.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace LeviCivitaOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold FrameRegular
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]

attribute [local instance] KoszulOrder.isManifold_succ KoszulOrder.contMDiffVectorBundle_succ
  KoszulOrder.contMDiffVectorBundle_self

section Frame

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- **The coefficients of a section in a local frame of any order** are the inverse Gram operator
applied to its pairings with the frame (`FrameRegular.coeff_eq_inverse_gram` with the frame's
order as a variable). -/
theorem coeff_eq_inverse_gram {m : WithTop ℕ∞} {s : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E m s u) (t : Π x : M, TangentSpace I x) {y : M} (hy : y ∈ u) :
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

variable [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- **The Gram operator of `C^k` sections is `C^k`**, the metric being `C^(k+1)`. -/
theorem contMDiffAt_gram {s : ι → Π x : M, TangentSpace I x} {x : M}
    (hs : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s i)) x) :
    ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) k (gram s) x := by
  haveI : IsContMDiffRiemannianBundle I k E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1) le_self_add
  have hG : ContMDiffAt I 𝓘(ℝ, ι → ι → ℝ) k (fun y j i ↦ ⟪s i y, s j y⟫) x :=
    contMDiffAt_pi_space.2 fun j ↦ contMDiffAt_pi_space.2 fun i ↦
      ContMDiffAt.inner_bundle (E := (TangentSpace I : M → Type _)) (hs i) (hs j)
  exact matrixOp.contMDiffAt.comp x hG

variable [FiniteDimensional ℝ E]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- **THE COEFFICIENTS OF A SECTION IN A LOCAL FRAME ARE `C^k`** as soon as its pairings with the
frame are.

**Extracted 2026-09-12 (entry 47) from the proof of `contMDiffAt_of_contMDiffAt_inner` below, where
it had been an unnamed `have` since this file was written** (`ERRATUM 517`). That theorem needs the
coefficients only to feed `IsLocalFrameOn.contMDiffAt_of_coeff`; the coefficients themselves are
what a change of frame is made of, and nothing downstream could reach them. -/
theorem contMDiffAt_coeff [Finite ι] {m : WithTop ℕ∞} (hm : (k : WithTop ℕ∞) ≤ m)
    {s : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u) {x : M}
    (hu : u ∈ 𝓝 x) {t : Π x : M, TangentSpace I x}
    (ht : ∀ j, ContMDiffAt I 𝓘(ℝ) k (fun y ↦ ⟪t y, s j y⟫) x) (i : ι) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ hs.coeff i y (t y)) x := by
  cases nonempty_fintype ι
  classical
  have hsk : IsLocalFrameOn I E (k : WithTop ℕ∞) s u :=
    { linearIndependent := hs.linearIndependent
      generating := hs.generating
      contMDiffOn := fun i ↦ (hs.contMDiffOn i).of_le hm }
  have hsx : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s i)) x := fun i ↦
    (hsk.contMDiffOn i).contMDiffAt hu
  have hunit : IsUnit (gram s x) := gram_isUnit (hs.linearIndependent (mem_of_mem_nhds hu))
  have hg : ContDiffAt ℝ k Ring.inverse (gram s x) := contDiffAt_ringInverse ℝ hunit.unit
  have hinv : ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) k (fun y ↦ Ring.inverse (gram s y)) x :=
    hg.comp_contMDiffAt (contMDiffAt_gram hsx)
  have hb : ContMDiffAt I 𝓘(ℝ, ι → ℝ) k (fun y j ↦ ⟪t y, s j y⟫) x := contMDiffAt_pi_space.2 ht
  have hc : ContMDiffAt I 𝓘(ℝ, ι → ℝ) k
      (fun y ↦ Ring.inverse (gram s y) (fun j ↦ ⟪t y, s j y⟫)) x := hinv.clm_apply hb
  refine (contMDiffAt_pi_space.1 hc i).congr_of_eventuallyEq ?_
  filter_upwards [hu] with y hy
  exact congrFun (coeff_eq_inverse_gram hs t hy) i

omit [CompleteSpace E] [Fintype ι] [DecidableEq ι] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- **THE GRAM-INVERSE LEG AT ORDER `k`**: a section whose pairings with a `C^m` local frame
(`m ≥ k`) are `C^k` at a point is `C^k` there. -/
theorem contMDiffAt_of_contMDiffAt_inner [Finite ι] {m : WithTop ℕ∞}
    (hm : (k : WithTop ℕ∞) ≤ m) {s : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E m s u) {x : M} (hu : u ∈ 𝓝 x)
    {t : Π x : M, TangentSpace I x}
    (ht : ∀ j, ContMDiffAt I 𝓘(ℝ) k (fun y ↦ ⟪t y, s j y⟫) x) :
    CMDiffAt (k : WithTop ℕ∞) (T% t) x := by
  classical
  have hsk : IsLocalFrameOn I E (k : WithTop ℕ∞) s u :=
    { linearIndependent := hs.linearIndependent
      generating := hs.generating
      contMDiffOn := fun i ↦ (hs.contMDiffOn i).of_le hm }
  exact hsk.contMDiffAt_of_coeff (fun i ↦ contMDiffAt_coeff le_rfl hsk hu ht i) hu

end Frame

section Hom

variable [FiniteDimensional ℝ E] {ι : Type*}

omit [CompleteSpace E] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- **A section of `Hom(TM, TM)` is `C^n` at `x` as soon as its values on the chart's local frame
are `C^n` sections** (`LeviCivitaRegular.contMDiffAt_hom_of_localFrame` with the order as a
variable). -/
theorem contMDiffAt_hom_of_localFrame [Finite ι] {n : WithTop ℕ∞}
    (φ : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) {x : M} (b : Module.Basis ι ℝ E)
    (h : ∀ i, CMDiffAt n (T% (fun y ↦
      φ y ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (φ y)) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, LeviCivitaRegular.contMDiffAt_clm_of_basis b fun i ↦ ?_⟩
  refine ((contMDiffAt_section x).1 (h i)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  exact LeviCivitaRegular.inCoordinates_apply_localFrame φ hy b i

end Hom

section LeviCivita

variable [FiniteDimensional ℝ E] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- **`y ↦ ∇_Y Z(y)` IS A `C^k` SECTION** for `Y, Z` of class `C^(k+1)` at `x`. -/
theorem contMDiffAt_leviCivita_apply {Y Z : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ leviCivita Z y (Y y))) x := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  refine contMDiffAt_of_contMDiffAt_inner (m := (k : WithTop ℕ∞) + 1) le_self_add
    (e.isLocalFrameOn_localFrame_baseSet I ((k : WithTop ℕ∞) + 1) b)
    (e.open_baseSet.mem_nhds hx) fun j ↦ ?_
  exact KoszulOrder.contMDiffAt_inner_leviCivita hY hZ
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1) _ b j hx)

/-- **`y ↦ ∇Z(y)` IS A `C^k` SECTION OF `Hom(TM, TM)`** for `Z` of class `C^(k+1)` at `x`. -/
theorem contMDiffAt_leviCivita_hom {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) k
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (leviCivita Z y)) x := by
  refine contMDiffAt_hom_of_localFrame (leviCivita Z) (Module.finBasis ℝ E) fun i ↦ ?_
  exact contMDiffAt_leviCivita_apply (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1) _ _ i
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)) hZ

/-- **THE LEVI-CIVITA CONNECTION OF A `C^(k+1)` METRIC IS `C^k` ON EVERY OPEN SET**, in Mathlib's
sense: `∇_X Z` is a `C^k` section for every `C^(k+1)` section `Z`. -/
theorem contMDiffCovariantDerivativeOn_leviCivita (u : Set M) (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E k
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)).toFun u :=
  ⟨fun {Z} hZ x hx ↦ by
    have hZx : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x := hZ.contMDiffAt (hu.mem_nhds hx)
    exact (contMDiffAt_leviCivita_hom hZx).contMDiffWithinAt⟩

end LeviCivita

end LeviCivitaOrder
