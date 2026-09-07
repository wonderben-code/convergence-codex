import CurvatureTensor

/-!
# The Koszul scalar is `C¹`: the first half of the regularity of the Levi-Civita connection

`CurvatureTensor` and `RicciScalar` built the curvature of any connection on the tangent bundle
that is `C¹` on every open set (`IsLocallyC1`), and said that one statement now separates the
estate from the curvature of a metric: that `KoszulManifold.leviCivita` is such a connection when
the metric is `C²`. That statement has two halves. The first is analysis: **the Koszul scalar
`y ↦ ⟨∇_X Y, Z⟩(y)` is `C¹`** for `X, Y, Z` of class `C²` at the point and a `C²` metric
(`contMDiffAt_koszulAux`), and so **the Levi-Civita derivative paired with any `C²` test section
is `C¹`** (`contMDiffAt_inner_leviCivita`). The second is linear algebra in a moving frame — from
`C¹` pairings with a frame to a `C¹` section of the endomorphism bundle — and it is not here.

The first half is what the Koszul expression is made of. `X⟨Y, Z⟩` is the derivative of the `C²`
function `⟨Y, Z⟩` (`ContMDiffAt.inner_bundle`, for a `C²` metric) along `X`, and the derivative of
a `C²` function paired with a `C¹` field is `C¹` (`contMDiffAt_extDerivFun_apply`) — by the chart,
as in `BracketDerivation`, with `ContDiffWithinAt.fderivWithin_right_apply` on the model space and
Mathlib's `contMDiffWithinAt_mpullbackWithin_extChartAt_symm` for the pulled-back field. The
bracket of two `C²` fields is `C¹` (`ContMDiffAt.mlieBracket_vectorField`), and its inner product
with a `C¹` field is `C¹`. Sums, differences and the factor `½` are Mathlib's.

## What is proved

**`contDiffWithinAt_mpullbackWithin`** — a field of class `C^m` at `x` (`m + 1 ≤ 3`), pulled back
through the chart at `x`, is `C^m` within the model's range at the chart point.

**`contMDiffAt_extDerivFun_apply`** — **`y ↦ df(V)(y)` is `C¹`** for `f` of class `C²` and `V` of
class `C¹` at `x`.

**`contMDiffAt_inner`** — the inner product of two `C^n` sections is `C^n` for `n ≤ 2`.

**`contMDiffAt_dInner`** — `X⟨Z, W⟩` is `C¹` for `X` of class `C¹` and `Z, W` of class `C²`.

**`contMDiffAt_inner_bracket`** — `⟨[X, Y], Z⟩` is `C¹` for `X, Y` of class `C²` and `Z` of class
`C¹`.

**`contMDiffAt_koszulAux`** — **the Koszul scalar is `C¹`** for `X, Y, Z` of class `C²` at `x`.

**`contMDiffAt_inner_leviCivita`** — **`y ↦ ⟨∇_Y Z, W⟩(y)` is `C¹`** for `Y, Z, W` of class `C²` at
`x`, `∇` the Levi-Civita connection of `KoszulManifold`.

## What is NOT here

**`IsLocallyC1 leviCivita`, AND WHAT IT STILL NEEDS.** From `C¹` pairings with every `C²` test
section to a `C¹` section `y ↦ ∇_Y Z(y)` needs a local frame `sⱼ` and the inverse of its Gram
matrix `⟨sⱼ, sₖ⟩` — `C²`, invertible, and its inverse `C²` by the smoothness of `Ring.inverse` on
matrices — or a `C²` orthonormal frame, which neither the estate nor the pinned library has; and
from `C¹` sections `∇_Y Z` for every `C²` field `Y` to a `C¹` section `y ↦ ∇Z(y)` of the
endomorphism bundle needs Mathlib's `contMDiffAt_hom_bundle` criterion in coordinates. Both steps
are linear algebra in a moving frame and neither is started. **Not attempted, no cost claimed**
(`ERRATUM 246`). ⚠ By entry 71, later the same day, the first step is done and the alternative
was not needed: `FrameRegular.contMDiffAt_of_contMDiffAt_inner` is the Gram-inverse leg, the
inverse taken in the operator ring on `ι → ℝ` by Mathlib's `contDiffAt_ringInverse`, with no
orthonormal frame; and `FrameRegular.contMDiffAt_leviCivita_apply` is `y ↦ ∇_Y Z(y)` as a `C¹`
section. The second step — the endomorphism bundle — is exactly as untouched as the paragraph
says.

**NO CURVATURE OF A METRIC**, therefore: `CurvatureTensor` and `RicciScalar` still apply to no
Levi-Civita connection.

**ONLY `C²`.** The metric is asked to be `C²` and the sections `C²`, which is what one derivative
of the connection costs; nothing is said at higher order, and `contMDiffAt_inner` is stated for
`n ≤ 2` for that reason.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]`, a `ChartedSpace H M` and a model `I`, and
`[IsManifold I 3 M]` throughout (a `C³` manifold with corners: `C²` sections at a point and the
bracket's regularity at that order need the tangent bundle to be a `C²` bundle,
`CurvatureTensor.contMDiffVectorBundle_two`); `[RiemannianBundle (fun x ↦ TangentSpace I x)]`
and `[IsContMDiffRiemannianBundle I 2 E (TangentSpace I)]` — a `C²` metric — from
`contMDiffAt_inner` on; `[FiniteDimensional ℝ E]` for `contMDiffAt_inner_leviCivita` alone, where
`leviCivita` needs it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace KoszulRegular

open Bundle Manifold VectorField FiberBundle Set KoszulManifold
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 3 M]

attribute [local instance] CurvatureTensor.contMDiffVectorBundle_two

/-- A field of class `C^m` at `x`, pulled back through the chart at `x`, is `C^m` within the
model's range at the chart point. -/
theorem contDiffWithinAt_mpullbackWithin {m : WithTop ℕ∞} (hm : m + 1 ≤ 3)
    {V : Π x : M, TangentSpace I x} {x : M} (hV : CMDiffAt m (T% V) x) :
    ContDiffWithinAt ℝ m (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I)) (range I)
      (extChartAt I x x) := by
  have h := contMDiffWithinAt_mpullbackWithin_extChartAt_symm (s := univ) (n := 3)
    (by simpa using hV) uniqueMDiffOn_univ (mem_univ x) hm
  have h2 := h.mono_of_mem_nhdsWithin (t := range I)
    (by simpa using extChartAt_target_mem_nhdsWithin (I := I) x)
  exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1 h2

/-- **`y ↦ df(V)(y)` is `C¹`** for `f` of class `C²` at `x` and `V` of class `C¹` at `x`. -/
theorem contMDiffAt_extDerivFun_apply {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    {V : Π x : M, TangentSpace I x} (hV : CMDiffAt 1 (T% V) x) :
    ContMDiffAt I 𝓘(ℝ) 1 (fun y ↦ extDerivFun (I := I) f y (V y)) x := by
  set g : E → ℝ := fun y' ↦ fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) y'
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) y') with hg
  have heq : (fun y ↦ extDerivFun (I := I) f y (V y)) =ᶠ[𝓝 x] g ∘ (extChartAt I x) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x,
      BracketDerivation.eventually_mdifferentiableAt hf] with y hy hfy
    exact (BracketDerivation.fderivWithin_comp_extChartAt_symm_apply hy hfy V).symm
  have hf2 : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) := by
    have := (contMDiffAt_iff.1 hf).2
    simpa [Function.comp_def] using this
  have hxr : extChartAt I x x ∈ range I := BracketDerivation.extChartAt_apply_mem_range x x
  have hV' := contDiffWithinAt_mpullbackWithin (m := 1) (by norm_num) hV
  have hgd : ContDiffWithinAt ℝ 1 g (range I) (extChartAt I x x) :=
    hf2.fderivWithin_right_apply hV' I.uniqueDiffOn (by norm_num) hxr
  have hcomp : ContMDiffAt I 𝓘(ℝ) 1 (g ∘ (extChartAt I x)) x := by
    rw [← contMDiffWithinAt_univ]
    exact ContMDiffWithinAt.comp x (contMDiffWithinAt_iff_contDiffWithinAt.2 hgd)
      contMDiffAt_extChartAt.contMDiffWithinAt
      (fun y _ ↦ BracketDerivation.extChartAt_apply_mem_range x y)
  exact hcomp.congr_of_eventuallyEq heq

section Riemannian

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

omit [CompleteSpace E] in
/-- The inner product of two `C^n` sections is `C^n`, for `n ≤ 2`, the metric being `C²`. -/
theorem contMDiffAt_inner {n : WithTop ℕ∞} (hn : n ≤ 2) {Z W : Π x : M, TangentSpace I x}
    {x : M} (hZ : CMDiffAt n (T% Z) x) (hW : CMDiffAt n (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) n (fun y ↦ ⟪Z y, W y⟫) x := by
  haveI : IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact ContMDiffAt.inner_bundle (E := (TangentSpace I : M → Type _)) hZ hW

/-- **`X⟨Z, W⟩` is `C¹`** for `X` of class `C¹` and `Z, W` of class `C²` at `x`. -/
theorem contMDiffAt_dInner {X Z W : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt 1 (T% X) x) (hZ : CMDiffAt 2 (T% Z) x) (hW : CMDiffAt 2 (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) 1 (fun y ↦ dInner X Z W y) x :=
  contMDiffAt_extDerivFun_apply (contMDiffAt_inner le_rfl hZ hW) hX

/-- **`⟨[X, Y], Z⟩` is `C¹`** for `X, Y` of class `C²` and `Z` of class `C¹` at `x`. -/
theorem contMDiffAt_inner_bracket {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 1 (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) 1 (fun y ↦ ⟪mlieBracket I X Y y, Z y⟫) x := by
  haveI : IsManifold I (2 + 1) M := inferInstanceAs (IsManifold I 3 M)
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  have hbr : CMDiffAt 1 (T% (mlieBracket I X Y)) x :=
    ContMDiffAt.mlieBracket_vectorField (m := 1) (n := 2) hX hY
      (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  exact contMDiffAt_inner (by norm_num) hbr hZ

/-- **THE KOSZUL SCALAR IS `C¹`**: for `X, Y, Z` of class `C²` at `x` and a `C²` metric,
`y ↦ ⟨∇_X Y, Z⟩(y)`, as given by the Koszul expression, is `C¹` at `x`. -/
theorem contMDiffAt_koszulAux {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt 2 (T% X) x) (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) 1 (fun y ↦ koszulAux Y X Z y) x := by
  have hX1 : CMDiffAt 1 (T% X) x := hX.of_le (by norm_num)
  have hY1 : CMDiffAt 1 (T% Y) x := hY.of_le (by norm_num)
  have hZ1 : CMDiffAt 1 (T% Z) x := hZ.of_le (by norm_num)
  simp only [koszulAux, ← smul_eq_mul]
  exact contMDiffAt_const.smul
    ((((((contMDiffAt_dInner hX1 hY hZ).add (contMDiffAt_dInner hY1 hX hZ)).sub
      (contMDiffAt_dInner hZ1 hX hY)).add (contMDiffAt_inner_bracket hX hY hZ1)).sub
      (contMDiffAt_inner_bracket hX hZ hY1)).sub (contMDiffAt_inner_bracket hY hZ hX1))

variable [FiniteDimensional ℝ E]

/-- **THE LEVI-CIVITA DERIVATIVE, PAIRED WITH `C²` TEST SECTIONS, IS `C¹`**: for `Y, Z, W` of class
`C²` at `x`, `y ↦ ⟨∇_{Y} Z, W⟩(y)` is `C¹` at `x` — near `x` it is the Koszul scalar. -/
theorem contMDiffAt_inner_leviCivita {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt 2 (T% Y) x) (hZ : CMDiffAt 2 (T% Z) x) (hW : CMDiffAt 2 (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) 1 (fun y ↦ ⟪leviCivita Z y (Y y), W y⟫) x := by
  refine (contMDiffAt_koszulAux hY hZ hW).congr_of_eventuallyEq ?_
  filter_upwards [CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hY,
    CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hZ,
    CurvatureTensor.eventually_mdiffAt_of_cmdiffAt hW] with y hYy hZy hWy
  exact inner_leviCivitaFun hZy hYy hWy

end Riemannian

end KoszulRegular
