import FieldIsometryLinear

/-!
# The bijectivity hypothesis comes off, and the famous theorem was not needed

`FieldIsometryLinear` proved that a distance-preserving **bijection** preserving the Gaussian field
is linear, routed through Mathlib's **Mazur–Ulam**, and fenced the bijectivity as a real hypothesis:
*"that a distance-preserving map of a finite-dimensional Euclidean space into itself is
automatically surjective is true and is not proved here; Mathlib was searched and it is not there."*
**The search was right and the framing was wrong** (`ERRATUM 463`). The missing statement was filed
at the generality of **normed** spaces, where it is a real gap; the estate only ever needs it for an
**inner product** space, where it is elementary and needs no Mazur–Ulam at all.

## What is proved

**`recentre`, `recentre_apply`, `recentre_zero`, `norm_recentre_sub`, `norm_recentre`** — an
isometry translated to fix the origin, and it still preserves distances and now preserves norms.

**`inner_recentre`** — **AND THEREFORE PRESERVES INNER PRODUCTS**, by polarisation:
`‖u − v‖² = ‖u‖² − 2⟪u,v⟫ + ‖v‖²` read twice and subtracted. This is the step that is available in
an inner product space and not in a general normed space, and it is the whole difference.

**`eq_of_inner_self_sub`, `recentre_add`, `recentre_smul`, `recentreLinear`, `recentreIsometry`** —
**AND IS THEREFORE LINEAR.** `‖g(x+y) − g x − g y‖² = 0` because every term of its expansion is an
inner product of `g`-images, each equal to the corresponding inner product of pre-images, and the
same expansion for `(x+y) − x − y = 0` gives zero; likewise for scalars.
`LinearMap.isometryOfInner` then bundles it.

**`recentre_bijective`, `surjective`, `bijective`, `toIsometryEquiv`, `coe_toIsometryEquiv`** —
**SO IN FINITE DIMENSION A DISTANCE-PRESERVING SELF-MAP IS ONTO**, by
`LinearMap.injective_iff_surjective` on the linear map above, and hence is an `IsometryEquiv`.

**`isometry_apply_zero_of_map`, `exists_linearIsometryEquiv_of_isometry`,
`gaussianField_map_isometry_iff`** — **so `FieldIsometryLinear`'s three statements hold for an
`Isometry`, with bijectivity assumed nowhere.** A distance-preserving map of `ℝ^V` that preserves
the Gaussian field fixes the origin, is linear, and — at `m ≠ 0` — commutes with the propagator.

## WHAT MAZUR–ULAM WAS FOR, and why it is not used here

Mazur–Ulam is a theorem about **normed** spaces, and its strength is that it needs no inner product;
its price is that it needs a **bijection**. Everything in this file is about an **inner product**
space, where the polarisation identity is available and the classical elementary argument applies —
**with no surjectivity assumed, because linearity is proved directly rather than transported across
a translation of the target.** The general section of this file cites Mazur–Ulam nowhere. It is
reached only through `FieldIsometryLinear`'s statements, which are applied to the `IsometryEquiv`
this file constructs.

## What is NOT here

**NOTHING ABOUT NORMED SPACES.** The surjectivity proved here is for a finite-dimensional real
**inner product** space. Whether a distance-preserving self-map of a finite-dimensional normed
space is onto is **untouched**, and the `UNLOCK_WATCHLIST` item that asked for it at that generality
is the subject of `ERRATUM 463`. Not attempted, no cost claimed (`ERRATUM 246`).

**NOTHING ABOUT INFINITE DIMENSION.** `surjective` uses `LinearMap.injective_iff_surjective`, which
is where `[FiniteDimensional ℝ E]` is spent; the shift is a linear isometry in any dimension, and in
infinite dimension it need not be onto.

**STILL NOTHING THAT IS NOT DISTANCE-PRESERVING.** What comes off is *bijectivity*; the isometry
assumption stays and is doing all the work. `FieldSqrtConjugation.exists_nonIsometric` shows the
isometric symmetries are a **proper** part of the linear ones, and the full automorphism group of
the measure is untouched.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`gaussianField_map_isometry_iff` alone — **one of the twenty-one** — and only because
`FieldInvarianceCommutes` takes it. `[FiniteDimensional ℝ E]` is taken by the five declarations of
section 2 and nothing before them. **Four `omit` `[InnerProductSpace ℝ E]`** — `recentre_apply`,
`recentre_zero`, `norm_recentre_sub` and `norm_recentre` — since a translated isometry and its norms
are a normed-group statement; the inner product first appears in `inner_recentre`, which is exactly
where the argument stops working for a general normed space.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace InnerIsometryOnto

open MeasureTheory GraphLaplacian FieldIsometryLinear

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → E}

/-- An isometry translated so that it fixes the origin. -/
def recentre (f : E → E) : E → E := fun x => f x - f 0

omit [InnerProductSpace ℝ E] in
@[simp] theorem recentre_apply (f : E → E) (x : E) : recentre f x = f x - f 0 := rfl

omit [InnerProductSpace ℝ E] in
@[simp] theorem recentre_zero (f : E → E) : recentre f 0 = 0 := by simp [recentre]

omit [InnerProductSpace ℝ E] in
theorem norm_recentre_sub (hf : Isometry f) (x y : E) :
    ‖recentre f x - recentre f y‖ = ‖x - y‖ := by
  have h : recentre f x - recentre f y = f x - f y := by
    simp only [recentre_apply]
    abel
  rw [h, ← dist_eq_norm, ← dist_eq_norm, hf.dist_eq]

omit [InnerProductSpace ℝ E] in
theorem norm_recentre (hf : Isometry f) (x : E) : ‖recentre f x‖ = ‖x‖ := by
  simpa using norm_recentre_sub hf x 0

/-- **AN ISOMETRY FIXING THE ORIGIN PRESERVES INNER PRODUCTS**, by polarisation. -/
theorem inner_recentre (hf : Isometry f) (x y : E) :
    inner ℝ (recentre f x) (recentre f y) = inner ℝ x y := by
  have e1 : ‖recentre f x - recentre f y‖ ^ 2
      = ‖recentre f x‖ ^ 2 - 2 * inner ℝ (recentre f x) (recentre f y) + ‖recentre f y‖ ^ 2 :=
    norm_sub_sq_real _ _
  have e2 : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := norm_sub_sq_real _ _
  rw [norm_recentre hf, norm_recentre hf, norm_recentre_sub hf, e2] at e1
  linarith

/-! ### And an inner-product-preserving map of a real inner product space is linear -/

theorem eq_of_inner_self_sub {u v : E} (h : inner ℝ (u - v) (u - v) = 0) : u = v :=
  sub_eq_zero.mp (inner_self_eq_zero.mp h)

theorem recentre_add (hf : Isometry f) (x y : E) :
    recentre f (x + y) = recentre f x + recentre f y := by
  refine eq_of_inner_self_sub ?_
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    inner_recentre hf, real_inner_comm x y]
  ring

theorem recentre_smul (hf : Isometry f) (c : ℝ) (x : E) :
    recentre f (c • x) = c • recentre f x := by
  refine eq_of_inner_self_sub ?_
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    inner_recentre hf]
  ring

/-- **THE LINEAR MAP AN ISOMETRY FIXING THE ORIGIN IS.** -/
def recentreLinear (hf : Isometry f) : E →ₗ[ℝ] E where
  toFun := recentre f
  map_add' := recentre_add hf
  map_smul' c x := recentre_smul hf c x

@[simp] theorem recentreLinear_apply (hf : Isometry f) (x : E) :
    recentreLinear hf x = f x - f 0 := rfl

/-- **AND IT IS A LINEAR ISOMETRY.** -/
noncomputable def recentreIsometry (hf : Isometry f) : E →ₗᵢ[ℝ] E :=
  (recentreLinear hf).isometryOfInner (inner_recentre hf)

@[simp] theorem recentreIsometry_apply (hf : Isometry f) (x : E) :
    recentreIsometry hf x = f x - f 0 := rfl

end General

/-! ## 2. In finite dimension it is therefore onto -/

section FiniteDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → E}

theorem recentre_bijective (hf : Isometry f) : Function.Bijective (recentre f) := by
  have hinj : Function.Injective (recentreLinear hf) := (recentreIsometry hf).injective
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- **A DISTANCE-PRESERVING SELF-MAP OF A FINITE-DIMENSIONAL REAL INNER PRODUCT SPACE IS ONTO.**
Mathlib has Mazur–Ulam only for bijections; this is the statement that removes the assumption. -/
theorem surjective (hf : Isometry f) : Function.Surjective f := by
  intro y
  obtain ⟨x, hx⟩ := (recentre_bijective hf).2 (y - f 0)
  exact ⟨x, by simpa [recentre, sub_left_inj] using hx⟩

theorem bijective (hf : Isometry f) : Function.Bijective f := ⟨hf.injective, surjective hf⟩

/-- **SO IT IS AN ISOMETRIC EQUIVALENCE**, which is what Mazur–Ulam asks for. -/
noncomputable def toIsometryEquiv (hf : Isometry f) : E ≃ᵢ E where
  toEquiv := Equiv.ofBijective f (bijective hf)
  isometry_toFun := hf

@[simp] theorem coe_toIsometryEquiv (hf : Isometry f) : ⇑(toIsometryEquiv hf) = f := rfl

end FiniteDim

/-! ## 3. The bijectivity hypothesis comes off the field's isometry chain -/

section Field

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}
  {f : EuclideanSpace ℝ V → EuclideanSpace ℝ V}

theorem isometry_apply_zero_of_map (hf : Isometry f)
    (h : Measure.map f (gaussianField G m) = gaussianField G m) : f 0 = 0 :=
  FieldIsometryLinear.isometryEquiv_apply_zero_of_map (toIsometryEquiv hf) h

/-- **A DISTANCE-PRESERVING SYMMETRY OF THE GAUSSIAN FIELD IS LINEAR**, with neither linearity nor
bijectivity assumed. No hypothesis on the mass. -/
theorem exists_linearIsometryEquiv_of_isometry (hf : Isometry f)
    (h : Measure.map f (gaussianField G m) = gaussianField G m) :
    ∃ g : EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V, ⇑g = f :=
  FieldIsometryLinear.exists_linearIsometryEquiv_of_map (toIsometryEquiv hf) h

/-- **AND THE CLASSIFICATION, WITH BOTH HYPOTHESES REMOVED.** -/
theorem gaussianField_map_isometry_iff (hm : m ≠ 0) (hf : Isometry f) :
    Measure.map f (gaussianField G m) = gaussianField G m ↔
      f 0 = 0 ∧ ∀ x : EuclideanSpace ℝ V,
        RayleighMatrix.mv (green G m) (f x) = f (RayleighMatrix.mv (green G m) x) :=
  FieldIsometryLinear.gaussianField_map_isometryEquiv_iff hm (toIsometryEquiv hf)

end Field

end InnerIsometryOnto
