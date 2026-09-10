import KoszulRegular

/-!
# The Koszul scalar at every finite order: `C^k` for a `C^(k+1)` metric

`KoszulRegular` proved the first half of the regularity of the Levi-Civita connection at the one
order curvature needs — the Koszul scalar is `C¹` for `C²` data — and every fence since has said
*only `C¹`*. This file removes that restriction for the Koszul scalar: **for `k : ℕ`, a `C^(k+2)`
manifold, a `C^(k+1)` metric and fields of class `C^(k+1)` at a point, the Koszul scalar is `C^k`
there** (`contMDiffAt_koszulAux`), and so **the Levi-Civita derivative paired with any `C^(k+1)`
test section is `C^k`** (`contMDiffAt_inner_leviCivita`). At `k = 1` these are `KoszulRegular`'s
theorems; the proofs are the same proofs with the order as a variable, because every Mathlib
lemma they rest on — `fderivWithin_right_apply`,
`contMDiffWithinAt_mpullbackWithin_extChartAt_symm`, `ContMDiffAt.mlieBracket_vectorField`,
`ContMDiffAt.inner_bundle` — is stated at every order.

What the order costs is instances. Mathlib registers the tangent bundle as a `C^n` vector bundle
only for `n ∈ {1, ∞, ω}`, so the `C^(k+1)` and `C^k` bundle instances are stated here and
registered locally (`contMDiffVectorBundle_succ`, `contMDiffVectorBundle_self`, from
`TangentBundle.contMDiffVectorBundle`); the `C^(k+1)` manifold instance is derived
(`isManifold_succ`); and the two instances whose statements do not mention `k` — a `C²` manifold,
which `BracketDerivation` and `KoszulManifold` ask for, and a `C¹` metric, which `leviCivita`
asks for — are taken as hypotheses, because an instance whose conclusion does not name `k` cannot
be found by unification. Both are implied by the `C^(k+2)` manifold and the `C^(k+1)` metric.

## What is proved

**`isManifold_succ`**, **`contMDiffVectorBundle_succ`**, **`contMDiffVectorBundle_self`** — the
instances above.

**`contDiffWithinAt_mpullbackWithin`** — a field of class `C^k` at `x`, pulled back through the
chart at `x`, is `C^k` within the model's range at the chart point.

**`contMDiffAt_extDerivFun_apply`** — **`y ↦ df(V)(y)` is `C^k`** for `f` of class `C^(k+1)` and `V`
of class `C^k` at `x`.

**`contMDiffAt_mlieBracket`** — the bracket of two `C^(k+1)` fields is `C^k`.

**`contMDiffAt_inner_succ`**, **`contMDiffAt_inner`** — the inner product of two `C^(k+1)`
(resp. `C^k`) sections is `C^(k+1)` (resp. `C^k`), the metric being `C^(k+1)`.

**`contMDiffAt_dInner`**, **`contMDiffAt_inner_bracket`** — `X⟨Z, W⟩` and `⟨[X, Y], Z⟩` are `C^k`.

**`contMDiffAt_koszulAux`** — **THE KOSZUL SCALAR IS `C^k`** for `X, Y, Z` of class `C^(k+1)`
at `x`.

**`contMDiffAt_inner_leviCivita`** — **`y ↦ ⟨∇_Y Z, W⟩(y)` is `C^k`** for `Y, Z, W` of class
`C^(k+1)` at `x`.

## What is NOT here

**THE SECOND HALF AT ORDER `k`.** From `C^k` pairings with a local frame to a `C^k` section
(`FrameRegular`'s Gram-inverse leg, whose ingredients — `contDiffAt_ringInverse`,
`IsLocalFrameOn.contMDiffAt_of_coeff` — are stated at every order) and then to a `C^k` section of
`Hom(TM, TM)` (`LeviCivitaRegular`'s leg) is not done at order `k`, so **the Levi-Civita
connection of a `C^(k+1)` metric is not shown `C^k`**, and `CurvatureTensor`'s `IsLocallyC1` has
no `C^k` analogue. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING ABOUT THE CURVATURE'S REGULARITY.** `riemann` is defined through `IsLocallyC1`; that it
is `C^(k−1)` as a section of a bundle for a `C^(k+1)` metric needs the second half above and a
regularity statement for `curvEndo`, neither started. `a₂` of `WALLS` §W5 integrates derivatives
of the curvature, which is why this file exists and what it does not yet reach.

**ONLY FINITE ORDERS.** `k : ℕ`; the `C^∞` and analytic cases are not stated, because
`contMDiffAt_iff_contMDiffOn_nhds` — used to pass from a point to a neighbourhood — asks for a
finite order, and the infinite cases would need a different route.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, `[CompleteSpace E]` (Mathlib's hypothesis for pulled-back fields and the
bracket), a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]` and `[IsManifold I 2 M]` (the
tangent bundle, and `BracketDerivation`'s and `KoszulManifold`'s hypothesis; both implied by the
next) and `[IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]` throughout, with `omit` where a lemma needs
fewer; `[RiemannianBundle (fun x ↦ TangentSpace I x)]` and
`[IsContMDiffRiemannianBundle I (k + 1) E (TangentSpace I)]` from section `Riemannian` on;
`[FiniteDimensional ℝ E]` and `[IsContMDiffRiemannianBundle I 1 E (TangentSpace I)]` (implied by the
`C^(k+1)` metric, and what `leviCivita` asks for) for `contMDiffAt_inner_leviCivita` alone.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace KoszulOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M]

omit [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem isManifold_succ : IsManifold I ((k : WithTop ℕ∞) + 1) M :=
  IsManifold.of_le (n := (k : WithTop ℕ∞) + 1 + 1) le_self_add

attribute [local instance] isManifold_succ

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- The tangent bundle of a `C^(k+2)` manifold is a `C^(k+1)` vector bundle (Mathlib states this
and registers it only for `k + 1 ∈ {1, ∞, ω}`). -/
theorem contMDiffVectorBundle_succ :
    ContMDiffVectorBundle ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_succ

omit [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] [IsManifold I 2 M] in
/-- A field of class `C^k` at `x`, pulled back through the chart at `x`, is `C^k` within the
model's range at the chart point. -/
theorem contDiffWithinAt_mpullbackWithin {V : Π x : M, TangentSpace I x} {x : M}
    (hV : CMDiffAt (k : WithTop ℕ∞) (T% V) x) :
    ContDiffWithinAt ℝ k (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I)) (range I)
      (extChartAt I x x) := by
  have h := contMDiffWithinAt_mpullbackWithin_extChartAt_symm (s := univ)
    (n := (k : WithTop ℕ∞) + 1 + 1) (by simpa using hV) uniqueMDiffOn_univ (mem_univ x)
    le_self_add
  have h2 := h.mono_of_mem_nhdsWithin (t := range I)
    (by simpa using extChartAt_target_mem_nhdsWithin (I := I) x)
  exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1 h2

/-- **`y ↦ df(V)(y)` is `C^k`** for `f` of class `C^(k+1)` and `V` of class `C^k` at `x`. -/
theorem contMDiffAt_extDerivFun_apply {f : M → ℝ} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) ((k : WithTop ℕ∞) + 1) f x)
    {V : Π x : M, TangentSpace I x} (hV : CMDiffAt (k : WithTop ℕ∞) (T% V) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ extDerivFun (I := I) f y (V y)) x := by
  set g : E → ℝ := fun y' ↦ fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) y'
    (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) y') with hg
  obtain ⟨u, hu, hfu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hf
  have heq : (fun y ↦ extDerivFun (I := I) f y (V y)) =ᶠ[𝓝 x] g ∘ (extChartAt I x) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x, interior_mem_nhds.2 hu] with y hy hyu
    have hfy : MDifferentiableAt I 𝓘(ℝ) f y :=
      ((hfu.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hyu)).mdifferentiableAt
        (by simp)
    exact (BracketDerivation.fderivWithin_comp_extChartAt_symm_apply hy hfy V).symm
  have hf2 : ContDiffWithinAt ℝ ((k : WithTop ℕ∞) + 1) (f ∘ (extChartAt I x).symm) (range I)
      (extChartAt I x x) := by
    have := (contMDiffAt_iff.1 hf).2
    simpa [Function.comp_def] using this
  have hxr : extChartAt I x x ∈ range I := BracketDerivation.extChartAt_apply_mem_range x x
  have hV' := contDiffWithinAt_mpullbackWithin hV
  have hgd : ContDiffWithinAt ℝ k g (range I) (extChartAt I x x) :=
    hf2.fderivWithin_right_apply hV' I.uniqueDiffOn le_rfl hxr
  have hcomp : ContMDiffAt I 𝓘(ℝ) k (g ∘ (extChartAt I x)) x := by
    rw [← contMDiffWithinAt_univ]
    exact ContMDiffWithinAt.comp x (contMDiffWithinAt_iff_contDiffWithinAt.2 hgd)
      contMDiffAt_extChartAt.contMDiffWithinAt
      (fun y _ ↦ BracketDerivation.extChartAt_apply_mem_range x y)
  exact hcomp.congr_of_eventuallyEq heq

omit [CompleteSpace E] [IsManifold I 2 M] in
/-- The tangent bundle of a `C^(k+2)` manifold is also a `C^k` vector bundle. -/
theorem contMDiffVectorBundle_self :
    ContMDiffVectorBundle (k : WithTop ℕ∞) E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_self

/-- The bracket of two `C^(k+1)` fields is `C^k`. -/
theorem contMDiffAt_mlieBracket {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Y) x) :
    CMDiffAt (k : WithTop ℕ∞) (T% (mlieBracket I X Y)) x := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have e : ((((k + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) + 1) = (k : WithTop ℕ∞) + 1 + 1 := by push_cast; rfl
  haveI : IsManifold I ((((k + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) + 1) M := by rw [e]; infer_instance
  have h := ContMDiffAt.mlieBracket_vectorField (I := I) (m := (k : ℕ∞)) (n := ((k + 1 : ℕ) : ℕ∞))
    (U := X) (V := Y) (x := x) (by exact_mod_cast hX) (by exact_mod_cast hY)
    (by rw [minSmoothness_of_isRCLikeNormedField]; push_cast; exact le_rfl)
  exact_mod_cast h

section Riemannian

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1) E (TangentSpace I : M → Type _)]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- The inner product of two `C^(k+1)` sections is `C^(k+1)`, the metric being `C^(k+1)`. -/
theorem contMDiffAt_inner_succ {Z W : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) ((k : WithTop ℕ∞) + 1) (fun y ↦ ⟪Z y, W y⟫) x :=
  ContMDiffAt.inner_bundle (E := (TangentSpace I : M → Type _)) hZ hW

omit [CompleteSpace E] [IsManifold I 2 M] [IsManifold I ((k : WithTop ℕ∞) + 1 + 1) M] in
/-- The inner product of two `C^k` sections is `C^k`. -/
theorem contMDiffAt_inner {Z W : Π x : M, TangentSpace I x} {x : M}
    (hZ : CMDiffAt (k : WithTop ℕ∞) (T% Z) x) (hW : CMDiffAt (k : WithTop ℕ∞) (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ ⟪Z y, W y⟫) x := by
  haveI : IsContMDiffRiemannianBundle I k E (TangentSpace I : M → Type _) :=
    IsContMDiffRiemannianBundle.of_le (n := (k : WithTop ℕ∞) + 1) le_self_add
  exact ContMDiffAt.inner_bundle (E := (TangentSpace I : M → Type _)) hZ hW

/-- **`X⟨Z, W⟩` is `C^k`** for `X` of class `C^k` and `Z, W` of class `C^(k+1)` at `x`. -/
theorem contMDiffAt_dInner {X Z W : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt (k : WithTop ℕ∞) (T% X) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ dInner X Z W y) x :=
  contMDiffAt_extDerivFun_apply (contMDiffAt_inner_succ hZ hW) hX

/-- **`⟨[X, Y], Z⟩` is `C^k`** for `X, Y` of class `C^(k+1)` and `Z` of class `C^k` at `x`. -/
theorem contMDiffAt_inner_bracket {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Y) x) (hZ : CMDiffAt (k : WithTop ℕ∞) (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ ⟪mlieBracket I X Y y, Z y⟫) x :=
  contMDiffAt_inner (contMDiffAt_mlieBracket hX hY) hZ

/-- **THE KOSZUL SCALAR IS `C^k`** for `X, Y, Z` of class `C^(k+1)` at `x` and a `C^(k+1)`
metric. -/
theorem contMDiffAt_koszulAux {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% X) x)
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ koszulAux Y X Z y) x := by
  have hX1 : CMDiffAt (k : WithTop ℕ∞) (T% X) x := hX.of_le le_self_add
  have hY1 : CMDiffAt (k : WithTop ℕ∞) (T% Y) x := hY.of_le le_self_add
  have hZ1 : CMDiffAt (k : WithTop ℕ∞) (T% Z) x := hZ.of_le le_self_add
  simp only [koszulAux, ← smul_eq_mul]
  exact contMDiffAt_const.smul
    ((((((contMDiffAt_dInner hX1 hY hZ).add (contMDiffAt_dInner hY1 hX hZ)).sub
      (contMDiffAt_dInner hZ1 hX hY)).add (contMDiffAt_inner_bracket hX hY hZ1)).sub
      (contMDiffAt_inner_bracket hX hZ hY1)).sub (contMDiffAt_inner_bracket hY hZ hX1))

variable [FiniteDimensional ℝ E] [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

/-- **THE LEVI-CIVITA DERIVATIVE, PAIRED WITH `C^(k+1)` TEST SECTIONS, IS `C^k`.** -/
theorem contMDiffAt_inner_leviCivita {Y Z W : Π x : M, TangentSpace I x} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% Z) x)
    (hW : CMDiffAt ((k : WithTop ℕ∞) + 1) (T% W) x) :
    ContMDiffAt I 𝓘(ℝ) k (fun y ↦ ⟪leviCivita Z y (Y y), W y⟫) x := by
  refine (contMDiffAt_koszulAux hY hZ hW).congr_of_eventuallyEq ?_
  obtain ⟨u, hu, hYu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hY
  obtain ⟨u', hu', hZu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hZ
  obtain ⟨u'', hu'', hWu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hW
  filter_upwards [interior_mem_nhds.2 hu, interior_mem_nhds.2 hu', interior_mem_nhds.2 hu'']
    with y hy hy' hy''
  have hYy := ((hYu.mono interior_subset).contMDiffAt
    (isOpen_interior.mem_nhds hy)).mdifferentiableAt (by simp)
  have hZy := ((hZu.mono interior_subset).contMDiffAt
    (isOpen_interior.mem_nhds hy')).mdifferentiableAt (by simp)
  have hWy := ((hWu.mono interior_subset).contMDiffAt
    (isOpen_interior.mem_nhds hy'')).mdifferentiableAt (by simp)
  exact inner_leviCivitaFun hZy hYy hWy

end Riemannian

end KoszulOrder
