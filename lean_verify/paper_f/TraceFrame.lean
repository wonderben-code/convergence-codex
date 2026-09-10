import LeviCivitaOrder

/-!
# The trace of a field of endomorphisms, in a moving frame

The scalar curvature is a trace, and so is the Ricci form: `RicciScalar.ricci` is the trace of
`v ↦ R(v, w) z` and `RicciScalar.scalar` the trace of the Ricci endomorphism. To say that either
is a **differentiable function of the point** one has to differentiate a trace, and the estate's
own fences have said twice why that is not immediate: a trace is computed in a basis, the
basis that makes it easy is orthonormal, and **neither this estate nor the pinned Mathlib has a
smooth orthonormal frame** — `FrameRegular` was written precisely because no such frame exists.

This file supplies the tool. **The trace of a field of endomorphisms is `C^k` as a function of the
point as soon as the field's values on some `C^m` local frame (`m ≥ k`) are `C^k` sections**
(`contMDiffAt_trace`), with no orthonormality and with no smoothness of the field as a section of
the endomorphism bundle. The frame need not be orthonormal because the trace in an arbitrary
frame is the sum of the frame *coefficients* of the values (`trace_eq_sum_coeff`), and
`LeviCivitaOrder.coeff_eq_inverse_gram` computes those coefficients as the inverse Gram operator
applied to the pairings — which is `FrameRegular`'s construction, at the order `KoszulOrder` and
`LeviCivitaOrder` made available.

## What is proved

**`trace_eq_sum_coeff`** — **THE TRACE IN A LOCAL FRAME**: for a local frame of any order and a
point of its domain, `tr A = ∑ᵢ cᵢ(A sᵢ)`, where `cᵢ` are the frame's coefficient functionals
(Mathlib's `LinearMap.trace_eq_matrix_trace` against `IsLocalFrameOn.toBasisAt`). No metric, no
smoothness, no orthonormality.

**`contMDiffAt_trace`** — **THE TRACE OF A FIELD OF ENDOMORPHISMS IS `C^k`**: if the values
`y ↦ A y (sᵢ y)` on a `C^m` frame are `C^k` sections at `x` and `k ≤ m`, then
`y ↦ tr (A y)` is `C^k` at `x`, for a `C^(k+1)` metric on a `C^(k+2)` manifold.

## What is NOT here

**NO APPLICATION TO THE CURVATURE.** The field this tool exists for is the curvature
endomorphism, and no curvature field is available at any order: `CurvatureTensor.curvEndo` is
built under the class `IsLocallyC1`, which fixes one derivative, and no smoothness statement
about it exists (the watchlist item filed by entry 78). **So neither `RicciScalar.ricci` nor
`RicciScalar.scalar` is shown to be a differentiable function of the point here**, and the
Einstein–Hilbert integrand is exactly as absent as it was. **Not attempted, no cost claimed**
(`ERRATUM 246`).

**THE HYPOTHESIS IS ON THE VALUES, NOT ON THE FIELD.** `contMDiffAt_trace` asks for the frame
values `y ↦ A y (sᵢ y)` to be `C^k` sections; it does not ask `A` to be a `C^k` section of
`Hom(TM, TM)`, and it does not prove that the two are equivalent. The implication from the
`Hom`-bundle side is `LeviCivitaOrder.contMDiffAt_hom_of_localFrame` read backwards, which is not
stated. The weaker hypothesis is deliberate: it is the one the curvature can supply.

**NO ORTHONORMAL FRAME**, still: nothing here orthonormalises, and the Gram operator's inverse
does the work an orthonormal frame would have done.

**ONLY FINITE ORDERS**, inherited from `KoszulOrder` and `LeviCivitaOrder`.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `trace_eq_sum_coeff` takes
`[NormedAddCommGroup E]`, `[NormedSpace ℝ E]`, `[FiniteDimensional ℝ E]`, a `ChartedSpace H M`
with model `I`, `[IsManifold I 1 M]` and the Riemannian bundle — no smoothness of the metric, no
completeness, and the frame's order is a variable it never constrains; `contMDiffAt_trace` adds
`[CompleteSpace E]`, `[IsManifold I 2 M]`, `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]` and
`[IsContMDiffRiemannianBundle I (k + 1) E (TangentSpace I)]`, which are `LeviCivitaOrder`'s, with
`KoszulOrder`'s three instances and `KoszulManifold.finDimTangent` registered locally.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace TraceFrame

open Bundle Manifold VectorField FiberBundle Set KoszulManifold FrameRegular
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {ι : Type*}

attribute [local instance] KoszulOrder.isManifold_succ KoszulOrder.contMDiffVectorBundle_succ
  KoszulOrder.contMDiffVectorBundle_self KoszulManifold.finDimTangent

local notation "⟪" x ", " y "⟫" => inner ℝ x y

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- **THE TRACE IN A LOCAL FRAME**: the trace of an endomorphism of a tangent space is the sum of
the frame coefficients of its values on the frame. -/
theorem trace_eq_sum_coeff [Fintype ι] {m : WithTop ℕ∞} {s : ι → Π x : M, TangentSpace I x}
    {u : Set M} (hs : IsLocalFrameOn I E m s u) {x : M} (hx : x ∈ u)
    (A : TangentSpace I x →ₗ[ℝ] TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) A = ∑ i, hs.coeff i x (A (s i x)) := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (hs.toBasisAt hx) A, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [hs.coeff_apply_of_mem hx (fun y ↦ A (s i x))]
  simp only [IsLocalFrameOn.toBasisAt_coe]

variable [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- **THE TRACE OF A FIELD OF ENDOMORPHISMS IS `C^k`** as a function of the point, as soon as the
field's values on a `C^m` local frame (`m ≥ k`) are `C^k` sections. No orthonormal frame and no
smoothness of the field as a section of the endomorphism bundle are needed. -/
theorem contMDiffAt_trace [Finite ι] {m : WithTop ℕ∞} (hm : (k : WithTop ℕ∞) ≤ m)
    {s : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u)
    {x : M} (hu : u ∈ 𝓝 x) {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    (hA : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ A y (s i y))) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ LinearMap.trace ℝ (TangentSpace I y) (A y)) x := by
  cases nonempty_fintype ι
  classical
  have hsk : IsLocalFrameOn I E (k : WithTop ℕ∞) s u :=
    { linearIndependent := hs.linearIndependent
      generating := hs.generating
      contMDiffOn := fun i ↦ (hs.contMDiffOn i).of_le hm }
  have hsx : ∀ i, CMDiffAt (k : WithTop ℕ∞) (T% (s i)) x := fun i ↦
    (hsk.contMDiffOn i).contMDiffAt hu
  -- the inverse Gram operator is `C^k`
  have hunit : IsUnit (gram s x) := gram_isUnit (hs.linearIndependent (mem_of_mem_nhds hu))
  have hg : ContDiffAt ℝ k Ring.inverse (gram s x) := contDiffAt_ringInverse ℝ hunit.unit
  have hinv : ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) k (fun y ↦ Ring.inverse (gram s y)) x :=
    hg.comp_contMDiffAt (LeviCivitaOrder.contMDiffAt_gram hsx)
  -- each summand is `C^k`
  have hterm : ∀ i, ContMDiffAt I 𝓘(ℝ) k
      (fun y ↦ Ring.inverse (gram s y) (fun j ↦ ⟪A y (s i y), s j y⟫) i) x := by
    intro i
    have hb : ContMDiffAt I 𝓘(ℝ, ι → ℝ) k (fun y j ↦ ⟪A y (s i y), s j y⟫) x :=
      contMDiffAt_pi_space.2 fun j ↦ KoszulOrder.contMDiffAt_inner (hA i) (hsx j)
    exact contMDiffAt_pi_space.1 (hinv.clm_apply hb) i
  have hsum : ContMDiffAt I 𝓘(ℝ) k
      (fun y ↦ ∑ i, Ring.inverse (gram s y) (fun j ↦ ⟪A y (s i y), s j y⟫) i) x :=
    ContMDiffAt.sum fun i _ ↦ hterm i
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hu] with y hy
  rw [trace_eq_sum_coeff hsk hy]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact congrFun (LeviCivitaOrder.coeff_eq_inverse_gram hsk (fun y ↦ A y (s i y)) hy) i

end TraceFrame
