import HomCovariant

/-!
# A differentiable multiple of the identity has a differentiable multiplier

**The non-vacuity check of `HomCovariant`, with no hypothesis on the function.** Entry 107 proved
`∇_u (f · id) = (df u) · id` for `f` differentiable at the point, and its own header called that
identity *unconditional* — which it was not, as the theorem's binder `hf : MDiffAt f x` says
(`ERRATUM 495`). This file removes the binder, by proving the fact that makes the two junk values
agree: **a section `f · id` of `Hom(TM, TM)` over a nontrivial model space is differentiable at a
point only if `f` is** (`mdiffAt_of_mdiffHomAt_smul_id`). Where `f` is not differentiable, *both*
sides of the identity are then zero — the left by the `dif_neg` branch of `homCovFun`, the right
because `mfderiv` of a non-differentiable function is `0`. The zero model space, where that
argument has no functional to work with, is handled separately and trivially.

**The two reasons are different, and that is the whole point of the exercise.** For a
differentiable `f` the identity is the Leibniz law of the induced connection together with the
parallelism of the identity (`HomCovariant.homCovFun_id`); for a non-differentiable `f` it is an
equality of two junk values, and no connection enters. A summary that drops the hypothesis without
saying which of the two it means is worse than one that keeps it, which is the rule the
`UNLOCK_WATCHLIST` item *whether any other chain states a result in prose without the hypothesis
that makes it non-vacuous* asks to be applied — here applied to this estate's own entry 107, and
answered by proving the statement the prose asserted rather than by softening the prose.

The extraction argument is three steps and needs no frame: read the section in the trivialisation
at the point (`mdifferentiableAt_hom_bundle`), where `f · id` becomes `f y · (id : E →L[ℝ] E)`
because `inCoordinates` is homogeneous in the map it transports (`inCoordinates_smul`) and carries
the identity to the identity (`HomCovariant.inCoordinates_id`); then apply a continuous linear
functional that does not vanish on the identity, which Hahn–Banach supplies as soon as `E` is not
the zero space (`exists_clm_id_ne_zero`). The zero model space is not an exception to the last
theorem: there every fibre is a single point and the identity holds by `Subsingleton.elim`.

## What is proved

**`inCoordinates_smul`** — `ContinuousLinearMap.inCoordinates` is homogeneous in the map it
transports, because it is a composition with fixed maps on both sides. Stated for the tangent
bundle of `M`, which is all this file needs. The pinned library carries `inCoordinates_eq`,
`inCoordinates_apply_eq₂`, `inCoordinates_tangent_bundle_core_model_space` and the
`clm_apply_of_inCoordinates` family, and **no linearity statement of any kind** about the map being
carried, so neither this nor the additivity beside it is quotable from Mathlib.

**`exists_clm_id_ne_zero`** — a continuous linear functional on `E →L[ℝ] E` that does not vanish
on the identity, for `E` nontrivial. Hahn–Banach, and no finite-dimensionality.

**`mdiffAt_of_mdiffHomAt_smul_id`**, **`mdiffHomAt_smul_id_iff`** — **A MULTIPLE OF THE IDENTITY IS
A DIFFERENTIABLE SECTION OF `Hom(TM, TM)` IFF ITS MULTIPLIER IS A DIFFERENTIABLE FUNCTION**, for a
nontrivial model space. **`[Nontrivial E]` is a hypothesis of the proof**, which needs a
functional that does not vanish on the identity and the zero space has none; whether the
*statement* needs it is **not settled here**. It presumably does not: for `E = 0` every fibre is a
single point, so every section is differentiable, and the charts being points, so is every function
`M → ℝ` — but that is a remark and not a theorem, and the last theorem below does not quote this
one where `E = 0`.

**`homCovFun_smul_id'`** — **AND A VALUE THAT IS NOT ZERO, WITH NO HYPOTHESIS AT ALL**:
`∇_u (f · id) = (df u) · id` for every `f : M → ℝ`, differentiable or not, at every point, and
with no *nontriviality* condition on the model space — the section context of the file is
unchanged, finite-dimensionality included. This is entry 107's `homCovFun_smul_id` with the binder
on `f` removed, and nothing else removed.

## What is NOT here

* **NO CLAIM THAT THE UNCONDITIONAL FORM IS THE BETTER ONE TO QUOTE.** `homCovFun_smul_id'` agrees
  with `homCovFun_smul_id` wherever the latter applies and extends it only to junk, and junk is not
  mathematics: a reader who needs the identity needs it for a differentiable `f`. The reason to
  prove it is that entry 107's prose asserted it, and the honest repair of an overclaim is the
  theorem, not a smaller sentence.
* **NOTHING FOR AN ABSTRACT BUNDLE, AND NOTHING FOR AN ABSTRACT SECTION.**
  `mdiffAt_of_mdiffHomAt_smul_id` is about multiples of the *identity* of the tangent bundle. The
  same argument would give "`f · A` is a differentiable section iff `f` is, for a differentiable
  `A` with `A x ≠ 0`", dividing by a functional that does not vanish on `A` near the point. That
  statement is **not proved here**, and nothing in this estate quotes it.
* **NO REGULARITY.** Nothing here is a `C^k` statement; `HomCovariantOrder` (entry 112) is where
  the regularity of the induced derivative lives, and it is not touched.
* **NO SECOND DERIVATIVE, AND NO CURVATURE.** The identity is parallel and its multiples have the
  derivative computed here; nothing is said about `∇∇(f · id)` or about the curvature of the
  induced connection. **Not attempted, no cost claimed** (`ERRATUM 246`).
-/

namespace HomCovariantNonvac

open Bundle Manifold VectorField FiberBundle Set Module HomCovariant
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}

attribute [local instance] KoszulManifold.finDimTangent

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- `ContinuousLinearMap.inCoordinates` is homogeneous in the map it transports: it is that map
composed with two fixed ones, so a scalar passes through. -/
theorem inCoordinates_smul {x y : M} (c : ℝ)
    (φ : TangentSpace I y →L[ℝ] TangentSpace I y) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
        (TangentSpace I : M → Type _) x y x y (c • φ)
      = c • ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
        (TangentSpace I : M → Type _) x y x y φ := by
  ext w
  simp [ContinuousLinearMap.inCoordinates]

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
/-- A continuous linear functional on `E →L[ℝ] E` that does not vanish on the identity, for a
nontrivial model space: pick a nonzero vector, take the dual vector Hahn–Banach gives for it, and
evaluate. -/
theorem exists_clm_id_ne_zero [Nontrivial E] :
    ∃ Φ : (E →L[ℝ] E) →L[ℝ] ℝ, Φ (ContinuousLinearMap.id ℝ E) ≠ 0 := by
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ w hwn
  exact ⟨ℓ.comp (ContinuousLinearMap.apply ℝ E w), by simpa [hℓ] using hwn⟩

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- **A MULTIPLE OF THE IDENTITY IS A DIFFERENTIABLE SECTION ONLY IF ITS MULTIPLIER IS A
DIFFERENTIABLE FUNCTION**: read in the trivialisation at the point the section is
`f y · (id : E →L[ℝ] E)`, and a functional that does not vanish on the identity recovers `f`
from it. -/
theorem mdiffAt_of_mdiffHomAt_smul_id [Nontrivial E] {f : M → ℝ} {x : M}
    (hA : MDiffHomAt (f • fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x) :
    MDiffAt f x := by
  obtain ⟨Φ, hΦ⟩ := exists_clm_id_ne_zero (E := E)
  have h₁ := ((mdifferentiableAt_hom_bundle _).1 hA).2
  have h₂ : MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E)
      (fun y ↦ f y • ContinuousLinearMap.id ℝ E) x := by
    refine h₁.congr_of_eventuallyEq ?_
    filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
    exact (((inCoordinates_smul (x := x) (y := y) (f y)
      (ContinuousLinearMap.id ℝ (TangentSpace I y))).trans
      (by rw [inCoordinates_id hy]))).symm
  have hΦd : MDifferentiableAt 𝓘(ℝ, E →L[ℝ] E) 𝓘(ℝ) Φ
      (f x • ContinuousLinearMap.id ℝ E) :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have h₃ := hΦd.comp x h₂
  simp only [Function.comp_def, map_smul, smul_eq_mul] at h₃
  have hinv : MDifferentiableAt 𝓘(ℝ) 𝓘(ℝ)
      (fun r : ℝ ↦ r * (Φ (ContinuousLinearMap.id ℝ E))⁻¹)
      (f x * Φ (ContinuousLinearMap.id ℝ E)) :=
    mdifferentiableAt_iff_differentiableAt.mpr (by fun_prop)
  have h₄ := hinv.comp x h₃
  simpa [Function.comp_def, mul_assoc, mul_inv_cancel₀ hΦ] using h₄

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- **A MULTIPLE OF THE IDENTITY IS A DIFFERENTIABLE SECTION OF `Hom(TM, TM)` IFF ITS MULTIPLIER IS
A DIFFERENTIABLE FUNCTION**, for a nontrivial model space. The converse direction is the library's
`MDifferentiableAt.smul_section` on the identity section (`HomCovariant.mdiffHomAt_id`). -/
theorem mdiffHomAt_smul_id_iff [Nontrivial E] {f : M → ℝ} {x : M} :
    MDiffHomAt (f • fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x ↔ MDiffAt f x :=
  ⟨mdiffAt_of_mdiffHomAt_smul_id, fun hf ↦ hf.smul_section (mdiffHomAt_id x)⟩

/-- **AND A VALUE THAT IS NOT ZERO, WITH NO HYPOTHESIS AT ALL**: `∇_u (f · id) = (df u) · id` for
every `f : M → ℝ`, differentiable at the point or not. Where `f` is differentiable this is entry
107's `HomCovariant.homCovFun_smul_id`; where it is not, `f · id` is not a differentiable section
(`mdiffAt_of_mdiffHomAt_smul_id`) so the left side is the junk value `0`, and `mfderiv f x = 0` so
the right side is `0` too. For a zero model space every fibre is a single point. -/
theorem homCovFun_smul_id' {f : M → ℝ} {x : M} (u v : TangentSpace I x) :
    homCovFun cov (f • fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x u v
      = (extDerivFun (I := I) f x u) • v := by
  by_cases hf : MDiffAt f x
  · exact homCovFun_smul_id hf u v
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : Subsingleton (TangentSpace I x) := hE
    exact Subsingleton.elim _ _
  have hA : ¬ MDiffHomAt (f • fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x :=
    fun h ↦ hf (mdiffAt_of_mdiffHomAt_smul_id h)
  have hd : extDerivFun (I := I) f x = 0 := by
    simp [extDerivFun, mfderiv_zero_of_not_mdifferentiableAt hf]
  simp [homCovFun, dif_neg hA, hd]

end HomCovariantNonvac
