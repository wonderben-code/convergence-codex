import CurvatureOrder

/-!
# The Ricci curvature of a metric is a `C^k` function

`CurvatureOrder` made the curvature **expression on three sections** a `C^k` section, and its own
fence named what was still missing: the curvature **tensor** as a differentiable field, which is
what `TraceFrame.contMDiffAt_trace` needs before a trace of it can be differentiated. This file
takes that step and the trace after it. **For `W, Z` of class `C^(k+2)` at a point and the
Levi-Civita connection of a `C^(k+2)` metric on a `C^(k+3)` manifold, `y ↦ Ric(W y, Z y)` is a
`C^k` function** (`contMDiffAt_ricci`) — the first statement in this estate that any curvature
scalar varies differentiably with the point.

Two things had to be arranged. The **bridge** is `CurvatureTensor.curvEndo_apply`: the tensor
agrees with the expression at every point where the three fields are regular enough, so the
tensor's field is `C^k` on the neighbourhood where that holds — which needs the *third* field to be
`C²` **near** the point, not merely at it, and `eventually_cmdiffAt_two` supplies that from
`contMDiffAt_iff_contMDiffOn_nhds`. The **trace** is then `TraceFrame.contMDiffAt_trace` against
the local frame of the tangent bundle's chart at the point, available at order `C^(k+2)` because a
`C^(k+3)` manifold has a `C^(k+2)` tangent bundle (`contMDiffVectorBundle_add_two`). **No
orthonormal
frame is used anywhere**, which is the point of the `FrameRegular`–`TraceFrame` route: none exists
in this estate or in the pinned Mathlib, and the trace in an arbitrary frame is computed by the
inverse Gram operator instead.

The Ricci curvature is the trace of `v ↦ R(v, w) z`, and that map is packaged as a *continuous*
linear map here (`ricciOp`) because `contMDiffAt_trace` takes a field of continuous endomorphisms;
on a finite-dimensional tangent space that is only a repackaging (`ricci_eq_trace_ricciOp` is
`rfl`).

## What is proved

**`eventually_cmdiffAt_two`** — a section that is `C²` at a point is `C²` at every point of a
neighbourhood. Needed because the bridge lemma asks for regularity near the point.

**`contMDiffVectorBundle_add_two`** — the tangent bundle of a `C^(k+3)` manifold is a `C^(k+2)`
vector bundle, the order at which the chart's local frame is available. Its name distinguishes it
from `CurvatureTensor.contMDiffVectorBundle_two`, which this file also uses, at the literal
order 2.

**`ricciOp`, `ricciOp_apply`, `ricci_eq_trace_ricciOp`** — `v ↦ R(v, w) z` as a continuous linear
map, and the Ricci curvature as its trace.

**`contMDiffAt_ricciOp_apply`** — **THE CURVATURE TENSOR IS A `C^k` FIELD**: for `W, Z, t` of class
`C^(k+2)` at `x`, `y ↦ R(t y, W y)(Z y)` is a `C^k` section. This is `CurvatureOrder`'s theorem
transported across `curvEndo_apply`, and it is the statement `TraceFrame` was written for.

**`contMDiffAt_riemann`** — the same statement in the estate's own name for the Riemann curvature
(`LeviCivitaRegular.riemann`), which closes the second half of that file's `ONLY C¹` fence.

**`contMDiffAt_ricci`, `contMDiffAt_ricci'`** — **THE RICCI CURVATURE OF A `C^(k+2)` METRIC IS A
`C^k` FUNCTION**, stated for `RicciScalar.ricci` of `leviCivita` and again in the estate's own name
for it (`LeviCivitaRegular.ricci`).

## What is NOT here

**NO SCALAR CURVATURE AS A FUNCTION, AND SO NO EINSTEIN–HILBERT INTEGRAND.** `RicciScalar.scalar`
is the **metric** trace of the Ricci form — the trace of `RicciScalar.ricciEndo`, which is defined
by duality from `ricci` — and nothing here says that `y ↦ ricciEndo y (s y)` is a differentiable
section, because that is the Riesz representation moving with the point and needs the inverse Gram
operator a second time. `scalar_eq_sum` computes the scalar curvature in an **orthonormal** basis,
and no smooth orthonormal frame exists (`FrameRegular`). **Not attempted, no cost claimed**
(`ERRATUM 246`).

**NOTHING ABOUT THE RICCI TENSOR AS A SECTION OF A TENSOR BUNDLE.** What is proved is the
regularity of `y ↦ Ric(W y, Z y)` for **fields** `W, Z` — the same shape as every other
regularity statement in this chain, and the shape the pinned Mathlib's `Hom`-bundle gap forces.
There is no `Ric` as a `C^k` section of `T*M ⊗ T*M`, because that bundle is not in the estate.

**NO SECOND DERIVATIVE, NO `a₂`, NO EINSTEIN EQUATIONS.** `WALLS` §W5's rung 4 needs derivatives of
the curvature inside a heat-kernel coefficient and a parametrix construction; this file supplies
the first derivative of a curvature scalar and nothing beyond it. The gap between here and `a₂` is
not narrowed by one order.

**NO CLAIM THAT THE HYPOTHESES ARE SHARP.** `C^(k+2)` fields for a `C^k` answer is what two
covariant derivatives cost by this route; whether `C^(k+1)` would do — it does in coordinates, for
the classical Christoffel formula — is not investigated.

**ONLY FINITE ORDERS**, inherited from `CurvatureOrder`, `KoszulOrder` and `LeviCivitaOrder`:
`k` is a natural number throughout, so nothing here is a statement about `C^∞`, and the
`contMDiffAt_iff_contMDiffOn_nhds` step in `eventually_cmdiffAt_two` needs a finite order to hold
at all.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]`, `[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with
model `I`, `[IsManifold I 1 M]`, `[IsManifold I 2 M]`, `[IsManifold I 3 M]`,
`[IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]` — a `C^(k+3)` manifold — the Riemannian bundle,
`[IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I)]` — a `C^(k+2)`
metric — and `[IsContMDiffRiemannianBundle I 2 E (TangentSpace I)]`, which is what makes
`LeviCivitaRegular.isLocallyC1_leviCivita` fire, with `omit` on the three lemmas that do not use
the whole context.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace RicciOrder

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
  CurvatureTensor.contMDiffVectorBundle_two

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- A section of class `C²` at a point is `C²` at every point of a neighbourhood. -/
theorem eventually_cmdiffAt_two {Z : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt (2 : WithTop ℕ∞) (T% Z) x) :
    ∀ᶠ y in 𝓝 x, CMDiffAt (2 : WithTop ℕ∞) (T% Z) y := by
  obtain ⟨u, hu, hZu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hZ
  filter_upwards [interior_mem_nhds.2 hu] with y hy
  exact (hZu.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hy)

/-- The Ricci operator of the Levi-Civita connection at a point, as a continuous linear map:
`v ↦ R(v, w) z`, which `RicciScalar.curvLeft` gives as a linear map. -/
noncomputable def ricciOp (x : M) (w z : TangentSpace I x) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  LinearMap.toContinuousLinearMap
    (RicciScalar.curvLeft (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
      x w z)

theorem ricciOp_apply (x : M) (w z v : TangentSpace I x) :
    ricciOp x w z v = curvEndo (leviCivita : CovariantDerivative I E
      (TangentSpace I : M → Type _)) x v w z := rfl

/-- **THE RICCI OPERATOR APPLIED TO A `C^(k+2)` FIELD IS A `C^k` SECTION**: for `W, Z, t` of class
`C^(k+2)` at `x`, `y ↦ R(t y, W y) (Z y)` is `C^k` at `x`, because near `x` it is the curvature
expression on the three fields. -/
theorem contMDiffAt_ricciOp_apply {W Z t : Π x : M, TangentSpace I x} {x : M}
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x)
    (ht : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% t) x) :
    CMDiffAt (k : WithTop ℕ∞) (T% (fun y ↦ ricciOp y (W y) (Z y) (t y))) x := by
  have h2 : (2 : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) + 1 + 1 := by
    exact_mod_cast (show (2 : ℕ) ≤ k + 1 + 1 by omega)
  refine (CurvatureOrder.contMDiffAt_curvAux ht hW hZ).congr_of_eventuallyEq ?_
  filter_upwards [eventually_mdiffAt_of_cmdiffAt (ht.of_le h2),
    eventually_mdiffAt_of_cmdiffAt (hW.of_le h2),
    eventually_cmdiffAt_two (hZ.of_le h2)] with y hty hWy hZy
  simp only [ricciOp_apply]
  rw [curvEndo_apply _ hty hWy hZy]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The tangent bundle of a `C^(k+3)` manifold is a `C^(k+2)` vector bundle, which is the order
the chart's local frame has to be available at. -/
theorem contMDiffVectorBundle_add_two :
    ContMDiffVectorBundle ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_add_two

/-- The estate's Riemann curvature of a metric, applied to a fourth vector, is the Ricci
operator with its arguments in the other order. -/
theorem riemann_eq_ricciOp (x : M) (v w z : TangentSpace I x) :
    LeviCivitaRegular.riemann I x v w z = ricciOp x w z v := rfl

/-- The Ricci curvature is the trace of the Ricci operator, by definition. -/
theorem ricci_eq_trace_ricciOp (x : M) (w z : TangentSpace I x) :
    RicciScalar.ricci (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _))
      x w z = LinearMap.trace ℝ (TangentSpace I x) (ricciOp x w z) := rfl

/-- **THE RICCI CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FUNCTION**: for `W, Z` of class
`C^(k+2)` at `x`, `y ↦ Ric(W y, Z y)` is `C^k` at `x`. The trace is taken in the local frame of
the tangent bundle's chart at `x` — no orthonormal frame is used, and none exists. -/
theorem contMDiffAt_ricci {W Z : Π x : M, TangentSpace I x} {x : M}
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ RicciScalar.ricci
      (leviCivita : CovariantDerivative I E (TangentSpace I : M → Type _)) y (W y) (Z y)) x := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  simp only [ricci_eq_trace_ricciOp]
  exact TraceFrame.contMDiffAt_trace (le_self_add.trans le_self_add)
    (e.isLocalFrameOn_localFrame_baseSet I ((k : WithTop ℕ∞) + 1 + 1) b)
    (e.open_baseSet.mem_nhds hx)
    (A := fun y ↦ ricciOp y (W y) (Z y))
    fun i ↦ contMDiffAt_ricciOp_apply hW hZ
      (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1) _ b i hx)

/-- **THE RIEMANN CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FIELD**, in the estate's own name for
it (`LeviCivitaRegular.riemann`): `y ↦ R(X y, W y)(Z y)` is a `C^k` section. -/
theorem contMDiffAt_riemann {X W Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% X) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    CMDiffAt (k : WithTop ℕ∞)
      (T% (fun y ↦ LeviCivitaRegular.riemann I y (X y) (W y) (Z y))) x := by
  refine (contMDiffAt_ricciOp_apply hW hZ hX).congr_of_eventuallyEq ?_
  filter_upwards with y
  exact congrArg (TotalSpace.mk' E y) (riemann_eq_ricciOp y (X y) (W y) (Z y))

omit [IsManifold I 2 M] in
/-- **THE RICCI CURVATURE OF A `C^(k+2)` METRIC IS A `C^k` FUNCTION**, in the estate's own name
for it (`LeviCivitaRegular.ricci`). -/
theorem contMDiffAt_ricci' {W Z : Π x : M, TangentSpace I x} {x : M}
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% W) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1) (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ LeviCivitaRegular.ricci I y (W y) (Z y)) x :=
  contMDiffAt_ricci hW hZ

end RicciOrder
