import TransitionRegular
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The frame domains are the chart sources, and they carry a partition of unity — at a price

Three units have narrowed the distance between this estate and `∫ S dvol` to *"measure theory and
only measure theory"*: `VolumeDensity` built `√det g` and proved it positive and `C^k`,
`FrameChange` proved it transforms by `|det A|` and that any second family is such a change, and
`TransitionRegular` proved that Jacobian a positive `C^k` function. What remained was a cover, a
partition of unity subordinate to it, and a measure. **This file supplies the first two and prices
the third exactly, which is the point of it.**

## What is proved

> **`chartFrame`, `isLocalFrameOn_chartFrame`** — the frame the whole chain has been using, named.
> `ScalarOrder` built it inline (`trivializationAt`'s `localFrame` against `Module.finBasis`) and no
> statement carried it; here it is a `def` with its frame property at **every** order for which the
> tangent bundle is that smooth.
>
> **AND ITS DOMAIN IS THE CHART SOURCE, BY `rfl`.** `TangentBundle.trivializationAt_baseSet` is
> definitional, so *"the domain of the chart's local frame"* and *"the source of the chart"* are the
> same set with two names. That is what makes the next theorem free: Mathlib's partition of unity
> subordinate to the **chart sources** is already subordinate to the **frame domains**.
>
> **`linearIndependent_chartFrame`, `density_chartFrame_pos`, `contMDiffAt_density_chartFrame`** —
> so the volume density of the chart's frame is defined, **strictly positive** and **`C^k`** at
> every point of every chart source, with no hypothesis beyond the chain's.
>
> **`exists_partitionOfUnity_density`** — **THE LOCAL DATA FOR A RIEMANNIAN MEASURE, ASSEMBLED**:
> a smooth partition of unity subordinate to the cover by chart sources, together with a positive
> `C^k` density on each. With `FrameChange.density_eq_transition` and
> `TransitionRegular.contMDiffAt_abs_det_transition`, the pieces agree on overlaps up to a positive
> `C^k` Jacobian. **Everything a construction of `dvol` would consume, except the integral.**

## The price, named exactly

`exists_partitionOfUnity_density` carries **three hypotheses the rest of the chain does not**:
`[T2Space M]`, `[SigmaCompactSpace M]` and — the one that matters — **`[IsManifold I ∞ M]`**.

**Mathlib's partition of unity is `C^∞` and there is no finite-order version.**
`SmoothPartitionOfUnity`'s field is `toFun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, and `IsManifold I ∞ M` sits in
the `variable` block governing every existence theorem in that file; `IsManifold I n M` at a finite
`n` **matches no line of it**. This chain is finite-order by design — a `C^(k+2)` metric gives a
`C^k` density, and `ScalarOrder` says in capitals that only finite orders appear — so **gluing at
finite order would need a partition of unity that does not exist in the pinned library**, and
gluing at all requires assuming the manifold smooth to infinite order.

That is a sharper statement than *"the estate has no measure on a manifold"*: the missing objects
are now **one integral and one finite-order partition of unity**, and the second is a library gap
with a name rather than a research project.

## What is NOT here

* **NO MEASURE AND NO INTEGRAL, STILL.** Nothing here integrates anything. Building `dvol` needs
  integration in a chart against Lebesgue measure on `E`, the change-of-variables formula for the
  transition maps, and countable additivity across the partition — and this estate has no
  measure-theoretic statement about a manifold at all. **Not attempted, no cost claimed**
  (`ERRATUM 246`).
* **NO CLAIM THAT THE THREE HYPOTHESES ARE SATISFIED BY ANY MANIFOLD IN THIS ESTATE.** They are
  hypotheses of a theorem, not properties established of anything. Whether the estate's model
  spaces are σ-compact and Hausdorff is not investigated here.
* **NO SUM, AND NO STATEMENT THAT THE GLUED OBJECT IS WELL DEFINED.** The last theorem hands over
  the pieces and the compatibility; it does not add them up, and the sum is where the measure
  theory begins.
* **NOTHING ABOUT `a₂`, THE WALL DOES NOT MOVE, AND NO PUBLISHED TAG MOVES.** `WALLS` §W5's rung 4
  wants the curvature integral to come out of an expansion of `Tr f(D/Λ)`; a classical action
  written by hand is not a step on it, and this is not even the action.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): the chain's context unchanged for §§1–2 —
every algebraic statement omits what it does not use and says so — and for §3 the three named above.
The index type is `Fin (Module.finrank ℝ E)`, fixed by the model fibre's basis rather than chosen.
**No orientation, no compactness of `M`, no completeness, no measure.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace DensityCover

open Bundle Manifold VectorField FiberBundle Set KoszulManifold CurvatureTensorial
  CurvatureTensor FrameRegular VolumeDensity FrameChange TransitionRegular
open scoped Bundle ContDiff Topology Matrix

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

/-! ## 1. The chart's frame, named -/

noncomputable def chartFrame (x : M) :
    Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
  (trivializationAt E (TangentSpace I : M → Type _) x).localFrame (Module.finBasis ℝ E)

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem isLocalFrameOn_chartFrame (m : WithTop ℕ∞)
    [ContMDiffVectorBundle m E (TangentSpace I : M → Type _) I] (x : M) :
    IsLocalFrameOn I E m (chartFrame (I := I) x) (chartAt H x).source :=
  (trivializationAt E (TangentSpace I : M → Type _) x).isLocalFrameOn_localFrame_baseSet I m
    (Module.finBasis ℝ E)

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)] in
theorem mem_chartAt_source (x : M) : x ∈ (chartAt H x).source := mem_chart_source H x

/-! ## 2. The density of the chart's frame -/

omit [CompleteSpace E] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem linearIndependent_chartFrame (x : M) {y : M} (hy : y ∈ (chartAt H x).source) :
    LinearIndependent ℝ (chartFrame (I := I) x · y) :=
  (isLocalFrameOn_chartFrame 2 x).linearIndependent hy

omit [CompleteSpace E] [IsManifold I 2 M]
  [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1) M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem density_chartFrame_pos (x : M) {y : M} (hy : y ∈ (chartAt H x).source) :
    0 < density (chartFrame (I := I) x) y :=
  density_pos (linearIndependent_chartFrame x hy)

omit [CompleteSpace E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem contMDiffAt_density_chartFrame (x : M) {y : M} (hy : y ∈ (chartAt H x).source) :
    ContMDiffAt I 𝓘(ℝ) k (density (chartFrame (I := I) x)) y := by
  have hmem : (chartAt H x).source ∈ 𝓝 y := (chartAt H x).open_source.mem_nhds hy
  exact contMDiffAt_density
    (fun i ↦ (((isLocalFrameOn_chartFrame ((k : WithTop ℕ∞) + 1 + 1) x).contMDiffOn
      i).contMDiffAt hmem).of_le (le_self_add.trans le_self_add))
    (linearIndependent_chartFrame x hy)

/-! ## 3. And the cover carries a partition of unity -/

omit [CompleteSpace E] [IsManifold I 2 M]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
theorem exists_partitionOfUnity_density [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M] :
    ∃ ρ : SmoothPartitionOfUnity M I M univ,
      ρ.IsSubordinate (fun x ↦ (chartAt H x).source) ∧
        ∀ x : M, ∀ y ∈ (chartAt H x).source,
          0 < density (chartFrame (I := I) x) y ∧
            ContMDiffAt I 𝓘(ℝ) k (density (chartFrame (I := I) x)) y := by
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I M
  exact ⟨ρ, hρ, fun x y hy ↦ ⟨density_chartFrame_pos x hy, contMDiffAt_density_chartFrame x hy⟩⟩

end DensityCover
