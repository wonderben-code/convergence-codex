import RicciOrder

/-!
# The scalar curvature of a metric is a `C^k` function

**The Einstein–Hilbert integrand, as a differentiable function of position.** `RicciOrder` made the
Ricci curvature `y ↦ Ric(W y, Z y)` a `C^k` function of the point and fenced that the *scalar*
curvature was not, because `RicciScalar.scalar` is the **metric** trace of the Ricci form — the
trace of `RicciScalar.ricciEndo`, which is defined by duality — and nothing said that the dual
vector varies differentiably with the point. **This file removes the dual vector from the answer
instead of differentiating it.** For a `C^(k+2)` metric on a `C^(k+3)` manifold,
`y ↦ S(y)` is `C^k` at every point, **with no hypothesis at all beyond the metric and the
manifold** (`contMDiffAt_scalar`) — no fields to supply, because the scalar curvature is a
function of the point and nothing else, and the frame it is computed in is the tangent bundle's
own chart, which always exists.

The identity that makes it work is `scalar_eq_sum_inverse_gram`: in **any** local frame,

`S = ∑ᵢ (G⁻¹ · (Ric(sᵢ, s_·)))ᵢ`,

the inverse Gram operator of the frame applied to the Ricci pairings and read on the diagonal. It
is `TraceFrame.trace_eq_sum_coeff` (the trace in a frame), then
`LeviCivitaOrder.coeff_eq_inverse_gram` (the coefficients as the inverse Gram operator), then
`RicciScalar.inner_ricciEndo` (which trades `⟪ricciEndo w, z⟫` for `Ric(w, z)`) — and it is the
third step that matters, because it is where `ricciEndo` leaves the statement. **The dual vector
appears in the proof at one point and never as a field**, which is exactly what the watchlist item
filed by the previous unit predicted would be needed. No orthonormality is used, and none is
available: this estate has no smooth orthonormal frame and neither does the pinned library, which
is why `FrameRegular` exists.

Differentiability is then the same three ingredients `TraceFrame` used: the frame's sections are
`C^(k+2)` on the chart's base set, each Ricci pairing `y ↦ Ric(sᵢ y, sⱼ y)` is `C^k` by
`RicciOrder.contMDiffAt_ricci`, and `y ↦ G(y)⁻¹` is `C^k` because `Ring.inverse` is smooth at a
unit and the Gram operator is a unit wherever the frame is independent.

## What is proved

**`scalar_eq_sum_inverse_gram`** — **THE SCALAR CURVATURE IN AN ARBITRARY LOCAL FRAME**: the
Gram-weighted identity above, at a point of the frame's domain, with no smoothness and no
orthonormality.

**`contMDiffAt_scalar_of_localFrame`** — the scalar curvature is `C^k` at a point of any
`C^(k+2)` local frame's domain.

**`contMDiffAt_scalar`, `contMDiffAt_scalar'`** — **THE SCALAR CURVATURE OF A `C^(k+2)` METRIC IS
A `C^k` FUNCTION**, at every point, with no hypothesis beyond the section context, the chart's
local frame supplying what the previous theorem asks for; stated for `RicciScalar.scalar` of
`leviCivita` and again in the estate's own name for it (`LeviCivitaRegular.scalar`).

**`contMDiff_scalar`, `contMDiff_scalar'`** — **AND SO IT IS A `C^k` FUNCTION ON THE WHOLE
MANIFOLD**, since the pointwise statement carries no hypothesis on the point. This is the form to
quote: `ContMDiff I 𝓘(ℝ) k S`.

## What is NOT here

**NO ACTION FUNCTIONAL, AND NO INTEGRAL OF ANY KIND.** The Einstein–Hilbert action is `∫ S dvol`,
and this file gives the **integrand** and nothing else. There is no Riemannian volume measure in
this estate, no `MeasureTheory` statement about a manifold anywhere in it, and therefore no
`∫ S`, no variation of it, and no Euler–Lagrange equation. **A differentiable integrand is not an
action** and must not be reported as one. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NO EINSTEIN TENSOR AND NO FIELD EQUATIONS.** `AlgebraicCurvature.einstein` is stated on
components in a basis, and no bridge from `RicciScalar.scalar` to it exists — that bridge is the
author's modelling decision, recorded as `ASSUMPTIONS_LEDGER` entry 54, which this file does not
settle and does not touch.

**NOTHING ABOUT `a₂`, AND NO HEAT KERNEL.** `WALLS` §W5's rung 4 wants the scalar curvature to
come **out of** a heat-kernel expansion of `Tr f(D/Λ)`, not to be written down and differentiated.
Neither the expansion nor the parametrix construction under it exists here, and §W5.1 §4 prices
them as a research project. **Producing the integrand by hand is not a step on that rung**, and no
wall moves.

**NO SHARPNESS.** `C^(k+2)` for a `C^k` answer is what this route costs; in coordinates the
classical formula needs `C^(k+2)` for the same reason, but nothing here proves that `C^(k+1)`
would fail, and the question is not investigated.

**ONLY FINITE ORDERS**, inherited from `RicciOrder` and everything under it: `k` is a natural
number throughout, so nothing here is a statement about `C^∞`.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with
model `I`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`, `[IsManifold I 3 M]`,
`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]` — a `C^(k+3)` manifold — the Riemannian bundle,
`[IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I)]` — a `C^(k+2)`
metric — and `[IsContMDiffRiemannianBundle I 2 E (TangentSpace I)]`. The frame's index type takes
`[Fintype ι]` and `[DecidableEq ι]` in the identity, because `FrameRegular.gram` is built from
`Matrix.toLin'`, and only `[Finite ι]` in the regularity theorems, where the frame appears under
`classical`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace ScalarOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor FrameRegular
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  {ι : Type*}

attribute [local instance] CurvatureOrder.isManifold_shift CurvatureOrder.isManifold_self
  CurvatureOrder.isContMDiffRiemannianBundle_shift
  CurvatureOrder.isContMDiffRiemannianBundle_self KoszulManifold.finDimTangent
  CurvatureTensor.contMDiffVectorBundle_two RicciOrder.contMDiffVectorBundle_add_two

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Local abbreviation for the Levi-Civita connection of the metric, so that the statements below
fit on a line. It is `LeviCivitaRegular`'s `leviCivita` and nothing else. -/
local notation "LC" => (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- **THE SCALAR CURVATURE IN AN ARBITRARY LOCAL FRAME**: the metric trace of the Ricci form is
the inverse Gram operator applied to the Ricci pairings of the frame, summed on the diagonal. No
orthonormality, no smoothness, and `ricciEndo` never appears in the answer. -/
theorem scalar_eq_sum_inverse_gram [Fintype ι] [DecidableEq ι] {m : WithTop ℕ∞}
    {s : ι → Π x : M, TangentSpace I x} {u : Set M} (hs : IsLocalFrameOn I E m s u)
    {x : M} (hx : x ∈ u) :
    RicciScalar.scalar LC x
      = ∑ i, Ring.inverse (gram s x) (fun j ↦ RicciScalar.ricci LC x (s i x) (s j x)) i := by
  rw [RicciScalar.scalar_eq_trace, TraceFrame.trace_eq_sum_coeff hs hx]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [congrFun (LeviCivitaOrder.coeff_eq_inverse_gram hs
    (fun y ↦ RicciScalar.ricciEndo LC y (s i y)) hx) i]
  simp only [RicciScalar.inner_ricciEndo]

/-- **THE SCALAR CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FUNCTION**, given any local frame of
order `C^(k+2)` around the point. -/
theorem contMDiffAt_scalar_of_localFrame [Finite ι]
    {s : ι → Π x : M, TangentSpace I x} {u : Set M}
    (hs : IsLocalFrameOn I E ((k : WithTop ℕ∞) + 1 + 1) s u) {x : M} (hu : u ∈ 𝓝 x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ RicciScalar.scalar LC y) x := by
  cases nonempty_fintype ι
  classical
  have hsx : ∀ i, CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% (s i)) x := fun i ↦
    (hs.contMDiffOn i).contMDiffAt hu
  have hunit : IsUnit (gram s x) := gram_isUnit (hs.linearIndependent (mem_of_mem_nhds hu))
  have hg : ContDiffAt ℝ k Ring.inverse (gram s x) := contDiffAt_ringInverse ℝ hunit.unit
  have hinv : ContMDiffAt I 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ)) k (fun y ↦ Ring.inverse (gram s y)) x :=
    hg.comp_contMDiffAt (LeviCivitaOrder.contMDiffAt_gram
      (fun i ↦ (hsx i).of_le (le_self_add.trans le_self_add)))
  have hterm : ∀ i, ContMDiffAt I 𝓘(ℝ) k
      (fun y ↦ Ring.inverse (gram s y) (fun j ↦ RicciScalar.ricci LC y (s i y) (s j y)) i) x := by
    intro i
    have hb : ContMDiffAt I 𝓘(ℝ, ι → ℝ) k
        (fun y j ↦ RicciScalar.ricci LC y (s i y) (s j y)) x :=
      contMDiffAt_pi_space.2 fun j ↦ RicciOrder.contMDiffAt_ricci (hsx i) (hsx j)
    exact contMDiffAt_pi_space.1 (hinv.clm_apply hb) i
  have hsum : ContMDiffAt I 𝓘(ℝ) k
      (fun y ↦ ∑ i, Ring.inverse (gram s y)
        (fun j ↦ RicciScalar.ricci LC y (s i y) (s j y)) i) x :=
    ContMDiffAt.sum fun i _ ↦ hterm i
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hu] with y hy
  exact scalar_eq_sum_inverse_gram hs hy

/-- **THE SCALAR CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FUNCTION OF THE POINT**, with no
hypothesis beyond the metric and the manifold: the frame is the tangent bundle's chart at the
point, which always exists. -/
theorem contMDiffAt_scalar {x : M} :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ RicciScalar.scalar LC y) x := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  exact contMDiffAt_scalar_of_localFrame
    (e.isLocalFrameOn_localFrame_baseSet I ((k : WithTop ℕ∞) + 1 + 1) (Module.finBasis ℝ E))
    (e.open_baseSet.mem_nhds hx)

omit [IsManifold I 2 M] in
/-- **THE SCALAR CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FUNCTION OF THE POINT**, in the
estate's own name for it (`LeviCivitaRegular.scalar`). -/
theorem contMDiffAt_scalar' {x : M} :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ LeviCivitaRegular.scalar I y) x :=
  contMDiffAt_scalar

/-- **THE SCALAR CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FUNCTION ON THE WHOLE MANIFOLD**, not
merely at each point: `ContMDiff` is by definition the pointwise statement at every point, and the
pointwise statement here carries no hypothesis on the point. -/
theorem contMDiff_scalar : ContMDiff I 𝓘(ℝ) k (fun y ↦ RicciScalar.scalar LC y) :=
  fun _ ↦ contMDiffAt_scalar

omit [IsManifold I 2 M] in
/-- **THE SCALAR CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FUNCTION ON THE WHOLE MANIFOLD**, in
the estate's own name for it (`LeviCivitaRegular.scalar`). -/
theorem contMDiff_scalar' :
    ContMDiff I 𝓘(ℝ) k (fun y : M ↦ LeviCivitaRegular.scalar I y) :=
  fun _ ↦ contMDiffAt_scalar'

end ScalarOrder
