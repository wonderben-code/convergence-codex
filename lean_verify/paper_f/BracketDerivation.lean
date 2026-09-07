import KoszulManifold

/-!
# The Lie bracket is the commutator of derivations, on a manifold

Mathlib defines the Lie bracket of two vector fields on a manifold through the chart
(`VectorField.mlieBracket`) and proves its Leibniz rules and the Jacobi identity, but not the
identity that makes it a bracket of derivations: **`[X, Y] f = X (Y f) − Y (X f)`** for a function
`f`. On the model space that is `fderiv_apply_lieBracket`, for `f` of class `C²` (the symmetry of
the second derivative is what the identity is). This file transports it to a manifold:
`extDerivFun_apply_mlieBracket`, for `f` of class `C²` at `x` and `X, Y` differentiable at `x`.

The transport is the one Mathlib's own bracket rules use, made explicit for a scalar function.
Write `φ := extChartAt I x`, `f' := f ∘ φ.symm` and `X', Y'` for the fields pulled back to the
model space. At the base point `x` the chart's derivative is the identity
(`mfderiv_extChartAt_self`), so the bracket at `x` is `lieBracketWithin ℝ X' Y' (range I) (φ x)` on
the nose (`hbr` in the proof) and `df` at `x` is `fderivWithin f' (range I) (φ x)`
(`fderivWithin_comp_extChartAt_symm_eq`). What
needs a neighbourhood rather than a point is the *second* derivative: the function `y ↦ df(Y)(y)`
agrees on the chart source with `(y' ↦ fderivWithin f' (range I) y' (Y' y')) ∘ φ`
(`fderivWithin_comp_extChartAt_symm_apply`, at every point of the source where `f` is
differentiable, which `C²` at `x` gives near `x`), so its derivative at `x` is the chart
function's (`extDerivFun_extDerivFun_apply`, through `Filter.EventuallyEq.mfderiv_eq` and the chain
rule). Then `fderivWithin_apply_lieBracket` on the model space, with `range I` as the set, its
uniqueness of derivatives (`ModelWithCorners.uniqueDiffOn`) and its density of interior
(`ModelWithCorners.range_eq_closure_interior`), is the identity.

## What is proved

**`extChartAt_apply_mem_range`** — every chart value lies in the model's range.

**`mpullbackWithin_extChartAt_symm_self`** — a field pulled back through the chart, at the base
point, is the field's value there.

**`fderivWithin_comp_extChartAt_symm_apply`** — on the chart source, `df(V)` is the derivative in
the chart of `f'` along the pulled-back field; **`fderivWithin_comp_extChartAt_symm_eq`** — at the
base point, along any vector.

**`eventually_mdifferentiableAt`** — a function `C²` at `x` is differentiable near `x`.

**`extDerivFun_extDerivFun_apply`** — **the second derivative in the chart**: `d(df(V))(w)` at `x`
is the derivative of `y' ↦ fderivWithin f' (range I) y' (V' y')` at `φ x` along `w`.

**`extDerivFun_apply_mlieBracket`** — **`[X, Y] f = X (Y f) − Y (X f)`** at `x`, for `f` of class
`C²` at `x` and `X, Y` differentiable at `x`, on a `C²` manifold with corners modelled on a
complete real normed space.

## What is NOT here

**THE CURVATURE TENSOR.** This identity is the one ingredient that the tensoriality of
`R(X, Y)Z = ∇_X ∇_Y Z − ∇_Y ∇_X Z − ∇_{[X,Y]} Z` in `Z` needs and the pinned library lacks; the
curvature itself, its tensoriality, and its traces are `W5`'s rung 3 and its watchlist item, and
nothing here writes them. **Not attempted, no cost claimed** (`ERRATUM 246`).

**ONLY SCALAR FUNCTIONS, ONLY THE GLOBAL VERSION.** `f : M → ℝ`; no vector-valued `f`, and no
`mlieBracketWithin` version with a set, though Mathlib's model-space lemma has one.

**`C²` IS USED AND NOT WEAKENED.** The identity is the symmetry of the second derivative, and
Mathlib's `fderivWithin_apply_lieBracket` asks `minSmoothness 𝕜 2 ≤ n`; for `ℝ` that is `C²` at
the point, and this file asks exactly that.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[NormedAddCommGroup E]`,
`[NormedSpace ℝ E]`, a `ChartedSpace H M` and a model `I` throughout; `[IsManifold I 2 M]` from
`mpullbackWithin_extChartAt_symm_self` on; `[CompleteSpace E]` from `extDerivFun_extDerivFun_apply`
on, Mathlib's hypothesis for the differentiability of pulled-back fields. **No finite dimension**,
no compactness, no Riemannian metric: this is a statement about the bracket alone. **No wall
moves. No published tag moves.**

**ON THE PROOFS.** Three steps close by `rfl` or `exact` across the definitional identification of
a tangent space with the model space, where `rw` and `simp` cannot match (`hid`, the inverse of
the identity in `hbr`, and the composition with the identity in `extDerivFun_extDerivFun_apply`);
the pattern is the one `KoszulManifold` recorded.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace BracketDerivation

open Bundle Manifold VectorField FiberBundle Set
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Every chart value lies in the model's range. -/
theorem extChartAt_apply_mem_range (x y : M) : extChartAt I x y ∈ range I := by
  rw [extChartAt_coe]
  exact mem_range_self _

variable [IsManifold I 2 M]

/-- The pulled-back field at the base point is the field itself. -/
theorem mpullbackWithin_extChartAt_symm_self (V : Π x : M, TangentSpace I x) (x : M) :
    mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) (extChartAt I x x) = V x := by
  rw [mpullbackWithin_apply, extChartAt_to_inv]
  exact mfderivWithin_extChartAt_symm_inverse_apply (V x)

/-- On the chart source, the derivative of `f` along `V` is the derivative in the chart of
`f ∘ φ.symm` along the pulled-back field. -/
theorem fderivWithin_comp_extChartAt_symm_apply {f : M → ℝ} {x y : M}
    (hy : y ∈ (extChartAt I x).source) (hf : MDifferentiableAt I 𝓘(ℝ) f y)
    (V : Π x : M, TangentSpace I x) :
    fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x y)
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) (extChartAt I x y))
    = extDerivFun (I := I) f y (V y) := by
  have hyt : extChartAt I x y ∈ (extChartAt I x).target := (extChartAt I x).map_source hy
  have hinv : (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
      (extChartAt I x y)).IsInvertible :=
    isInvertible_mfderivWithin_extChartAt_symm hyt
  have hsymm : MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
      (extChartAt I x y) :=
    mdifferentiableWithinAt_extChartAt_symm hyt
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, E) (range I) (extChartAt I x y) :=
    I.uniqueMDiffOn _ (extChartAt_target_subset_range x hyt)
  have hleft : (extChartAt I x).symm (extChartAt I x y) = y := (extChartAt I x).left_inv hy
  have hchain : mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x y)
      = (mfderiv I 𝓘(ℝ) f y).comp
          (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (extChartAt I x y)) :=
    mfderiv_comp_mfderivWithin_of_eq hf hsymm hu hleft
  rw [← mfderivWithin_eq_fderivWithin, hchain, mpullbackWithin_apply, hleft]
  have hid : (mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (extChartAt I x y))
      ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I) (extChartAt I x y)).inverse (V y))
      = V y :=
    (hinv.inverse_apply_eq.mp rfl).symm
  change mfderiv I 𝓘(ℝ) f y ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
    (extChartAt I x y)) ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (range I)
    (extChartAt I x y)).inverse (V y))) = extDerivFun (I := I) f y (V y)
  rw [hid]
  rfl

/-- The derivative in the chart of `f ∘ φ.symm` is the exterior derivative of `f`, pulled back. -/
theorem fderivWithin_comp_extChartAt_symm_eq {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ) f x) (v : TangentSpace I x) :
    fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) v
      = extDerivFun (I := I) f x v := by
  have h := fderivWithin_comp_extChartAt_symm_apply (mem_extChartAt_source x) hf
    (fun _ ↦ v : Π x : M, TangentSpace I x)
  rwa [mpullbackWithin_extChartAt_symm_self] at h

/-- Near `x`, a `C²` function is differentiable. -/
theorem eventually_mdifferentiableAt {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) :
    ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ) f y := by
  obtain ⟨u, hu, hfu⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).1 hf
  filter_upwards [interior_mem_nhds.2 hu] with y hy
  exact ((hfu y (interior_subset hy)).mdifferentiableWithinAt two_ne_zero).mdifferentiableAt
    (mem_interior_iff_mem_nhds.1 hy)

variable [CompleteSpace E]

/-- **The second derivative in the chart**: the derivative of `y ↦ df(V)(y)` along `w` at `x` is
the derivative, in the chart, of the corresponding function on the model space. -/
theorem extDerivFun_extDerivFun_apply {f : M → ℝ} {x : M} (hf : ContMDiffAt I 𝓘(ℝ) 2 f x)
    {V : Π x : M, TangentSpace I x} (hV : MDiffAt (T% V) x) (w : TangentSpace I x) :
    extDerivFun (I := I) (fun y ↦ extDerivFun (I := I) f y (V y)) x w
      = fderivWithin ℝ (fun y' ↦ fderivWithin ℝ (f ∘ (extChartAt I x).symm) (range I) y'
          (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm V (range I) y')) (range I)
          (extChartAt I x x) w := by
  set φ := extChartAt I x with hφ
  set V' := mpullbackWithin 𝓘(ℝ, E) I φ.symm V (range I) with hV'
  set f' := f ∘ φ.symm with hf'
  set g : E → ℝ := fun y' ↦ fderivWithin ℝ f' (range I) y' (V' y') with hg
  -- the two functions agree near `x`
  have heq : (fun y ↦ extDerivFun (I := I) f y (V y)) =ᶠ[𝓝 x] g ∘ φ := by
    filter_upwards [extChartAt_source_mem_nhds (I := I) x, eventually_mdifferentiableAt hf]
      with y hy hfy
    exact (fderivWithin_comp_extChartAt_symm_apply hy hfy V).symm
  -- `g` is differentiable within the range at `φ x`
  have hf2 : ContDiffWithinAt ℝ 2 f' (range I) (φ x) := by
    have := (contMDiffAt_iff.1 hf).2
    simpa [Function.comp_def] using this
  have hxr : φ x ∈ range I := extChartAt_apply_mem_range x x
  have hV'd : DifferentiableWithinAt ℝ V' (range I) (φ x) := by
    have := (mdifferentiableWithinAt_univ.2 hV).differentiableWithinAt_mpullbackWithin_vectorField
    simpa using this
  have hgd : DifferentiableWithinAt ℝ g (range I) (φ x) := by
    have h1 : DifferentiableWithinAt ℝ (fderivWithin ℝ f' (range I)) (range I) (φ x) :=
      (hf2.fderivWithin_right (m := 1) I.uniqueDiffOn (by norm_num) hxr).differentiableWithinAt
        one_ne_zero
    exact h1.clm_apply hV'd
  have hcomp : mfderiv I 𝓘(ℝ) (g ∘ φ) x
      = (mfderivWithin 𝓘(ℝ, E) 𝓘(ℝ) g (range I) (φ x)).comp (mfderiv I 𝓘(ℝ, E) φ x) := by
    rw [← mfderivWithin_univ, ← mfderivWithin_univ (f := φ)]
    exact mfderivWithin_comp x (mdifferentiableWithinAt_iff_differentiableWithinAt.2 hgd)
      (mdifferentiableAt_extChartAt (mem_chart_source H x)).mdifferentiableWithinAt
      (fun y _ ↦ extChartAt_apply_mem_range x y) (uniqueMDiffWithinAt_univ I)
  change mfderiv I 𝓘(ℝ) (fun y ↦ extDerivFun (I := I) f y (V y)) x w = _
  rw [heq.mfderiv_eq, hcomp, mfderiv_extChartAt_self, mfderivWithin_eq_fderivWithin]
  rfl

/-- **THE LIE BRACKET IS THE COMMUTATOR OF DERIVATIONS, ON A MANIFOLD**: for `f` of class `C²` at
`x` and `X, Y` differentiable there, `[X, Y] f = X (Y f) − Y (X f)`. -/
theorem extDerivFun_apply_mlieBracket {f : M → ℝ} {X Y : Π x : M, TangentSpace I x} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f x) (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    extDerivFun (I := I) f x (mlieBracket I X Y x)
      = extDerivFun (I := I) (fun y ↦ extDerivFun (I := I) f y (Y y)) x (X x)
        - extDerivFun (I := I) (fun y ↦ extDerivFun (I := I) f y (X y)) x (Y x) := by
  have hbr : mlieBracket I X Y x
      = lieBracketWithin ℝ (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (range I))
          (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I)) (range I)
          (extChartAt I x x) := by
    rw [mlieBracket, mlieBracketWithin_apply]
    simp only [preimage_univ, univ_inter, mfderiv_extChartAt_self]
    have hinv : ∀ v : TangentSpace I x,
        (ContinuousLinearMap.id ℝ (TangentSpace I x)).inverse v = v := by
      intro v
      rw [ContinuousLinearMap.inverse_id]
      rfl
    exact hinv _
  have hf2 : ContDiffWithinAt ℝ 2 (f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x) := by
    have := (contMDiffAt_iff.1 hf).2
    simpa [Function.comp_def] using this
  have hxr : extChartAt I x x ∈ range I := extChartAt_apply_mem_range x x
  have hxc : extChartAt I x x ∈ closure (interior (range I)) := by
    rw [← I.range_eq_closure_interior]
    exact hxr
  have hX'd : DifferentiableWithinAt ℝ
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X (range I)) (range I)
      (extChartAt I x x) := by
    have := (mdifferentiableWithinAt_univ.2 hX).differentiableWithinAt_mpullbackWithin_vectorField
    simpa using this
  have hY'd : DifferentiableWithinAt ℝ
      (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y (range I)) (range I)
      (extChartAt I x x) := by
    have := (mdifferentiableWithinAt_univ.2 hY).differentiableWithinAt_mpullbackWithin_vectorField
    simpa using this
  have key := fderivWithin_apply_lieBracket hf2 (by simp) I.uniqueDiffOn hxc hxr hY'd hX'd
  rw [hbr, ← fderivWithin_comp_extChartAt_symm_eq (hf.mdifferentiableAt two_ne_zero), key,
    extDerivFun_extDerivFun_apply hf hY, extDerivFun_extDerivFun_apply hf hX,
    mpullbackWithin_extChartAt_symm_self, mpullbackWithin_extChartAt_symm_self]

end BracketDerivation
