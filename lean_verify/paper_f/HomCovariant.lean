import CovariantJet

/-!
# The induced connection on the endomorphism bundle

Three files of this estate record the same absence. `CurvatureOrder` explains that its route costs
one file and not a subject *because* `curvAux` applies the connection only to plain sections, "so
the induced connection on `Hom(TM, TM)`, which the pinned Mathlib does not have, is never needed".
`CurvatureBianchi` declines the second Bianchi identity because no declaration in `paper_f`
differentiates `curvEndo` covariantly. `CovariantJet` declines the second-order 1-jet statement for
the same reason. **This file builds the object**, for an arbitrary covariant derivative on the
tangent bundle, and bundles it as Mathlib's `CovariantDerivative`.

The formula is the standard one — `(∇_u A)(v) = ∇_u (A σ) − A (∇_u σ)` for any section `σ` through
`v` — and **no metric and no torsion-freeness appear anywhere**.

## What is proved

**`homCovAux`** — the expression `∇_u (A σ) − A (∇_u σ)`, as a continuous linear map in the
direction `u`, taking a **section** `σ`.

**`homCovAux_add`**, **`homCovAux_smul`**, **`tensorialAt_homCovAux`**,
**`homCovAux_congr_of_eq`** — **the reason the object exists**: the expression is tensorial in `σ`,
because the two `df ⊗ ·` terms the Leibniz rule produces cancel, and therefore depends on `σ` only
through `σ x` (Mathlib's `TensorialAt.pointwise`). `mdiffAt_apply` and `comp_smulRight` are the two
small facts that computation needs.

**`homCovHom`**, **`homCovHom_apply_extend`**, **`homCovHom_apply`** — the value as an element of
the fibre: `homCovHom cov A hA : TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x)`,
`u ↦ v ↦ (∇_u A)(v)`, built by `LinearMap.toContinuousLinearMap` over `extend` exactly as
`CurvatureTensor.curvEndo` is, and agreeing with `homCovAux` on every differentiable section.

**`homCovFun`**, **`homCovFun_apply`** — the same as a **total** operation on sections, with the
junk value `0` where `A` is not differentiable. That is `KoszulManifold.leviCivitaFun`'s convention
and it is what `IsCovariantDerivativeOn` asks for.

**`isCovariantDerivativeOn_homCovFun`** — **THE INDUCED OPERATION IS A COVARIANT DERIVATIVE**, in
Mathlib's own `IsCovariantDerivativeOn (E →L[ℝ] E)`, on **every** set; and
**`homCovariantDerivative`** is that bundled as a `CovariantDerivative`.

**`inCoordinates_id`**, **`mdiffHomAt_id`** — **the identity endomorphism is a differentiable
section of `Hom(TM, TM)`**, because it is the constant identity in every trivialisation. The pinned
library states this for no bundle, and it is needed for the last two.

**`homCovFun_id`** — **the identity is parallel for every connection**, and unconditionally: where
`A` is not differentiable the junk value is `0` as well, so the statement needs no hypothesis.

**`homCovFun_smul_id`** — **AND A VALUE THAT IS NOT ZERO**: `∇_u (f · id) = (df u) · id`, for `f`
differentiable at the point (`hf : MDiffAt f x`). This is the non-vacuity check the construction
needs — without it nothing here would distinguish the induced derivative from the zero operation.
⚠ **This sentence ended "and it is unconditional", and the theorem's own binder said otherwise**
(`ERRATUM 495`). The false clause is **replaced rather than annotated in place**, which is a
departure from `ERRATUM 94` and the reason is stated here: `ERRATUM 94` preserves sentences whose
falsity is part of the record, and this one was my own draft of the same day, already contradicted
two lines above by the file's own binder paragraph. Entry 114
(`HomCovariantNonvac.homCovFun_smul_id'`) proves the unconditional identity, and it is a
**different theorem**: where `f` is not differentiable both sides are the junk value `0`, for
reasons that have nothing to do with the Leibniz law that proves this one.

## What is NOT here

* **NO REGULARITY.** Nothing says `homCovFun cov A` is a `C^k` section of `Hom(TM, Hom(TM, TM))`
  when `A` is a `C^(k+1)` one. ⚠ **Not from this file, and only in part**: entry 112
  (`HomCovariantOrder`) proves `∇_X A` a `C^k` section of `Hom(TM, TM)` for a FIXED direction field
  `X`, and for the Levi-Civita connection only. **The sentence as written stands** — no statement
  anywhere makes `homCovFun cov A` a section of the doubly-nested `Hom` bundle, and nothing is
  proved for an abstract `cov`. That is the next object, and it is what the `UNLOCK_WATCHLIST`
  item *the regularity of the curvature of a metric* needs for its residue (i): that item's
  entry-81 status records the curvature being reached as VALUES on fields rather than as a section
  of the endomorphism bundle, and names this `Hom`-bundle gap as the reason. **The gap is now
  closed for the connection and not for the curvature.** Not attempted, no cost claimed
  (`ERRATUM 246`).
* **NOTHING ABOUT `curvEndo`.** No declaration here differentiates the curvature covariantly, so
  **the second Bianchi identity is exactly as unproved as `CurvatureBianchi` says it is** — what
  changes is that the tool it named as missing now exists.
* **ONLY THE ENDOMORPHISM BUNDLE OF THE TANGENT BUNDLE.** `Hom(V, W)` for two other bundles would
  need two connections — one on `V` for the `∇^V σ` term and one on `W` — and the fibrewise
  finite-dimensionality that `LinearMap.toContinuousLinearMap` consumes, which comes here from
  `KoszulManifold.finDimTangent`. The generalisation is mechanical and is **not done**.
* **NO CURVATURE OF THE INDUCED CONNECTION**, no compatibility with a metric, no torsion — none of
  which is asked for by anything above.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a normed space `E` over `ℝ` with
`[FiniteDimensional ℝ E]`, a `ChartedSpace H M` with model `I`, `[IsManifold I 1 M]` and
`[IsManifold I 2 M]` (the tangent bundle as a `C¹` vector bundle, which `TensorialAt.pointwise`
consumes), and a `CovariantDerivative I E (TangentSpace I)`. `KoszulManifold.finDimTangent` is
registered as a local instance for the fibres. **There is no `[CompleteSpace E]`**, which the
neighbouring files all carry for the bracket and for pulled-back fields: it was in the variable
block while this file was written, the unused-variable report named it in every declaration, and it
was removed rather than `omit`ted. Seven declarations `omit` binders they do not use, and the
linter reports nothing. One `set_option synthInstance.maxHeartbeats 80000`, scoped to the one
declaration whose statement lands in the twice-nested `Hom` type.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace HomCovariant

open Bundle Manifold VectorField FiberBundle Set Module
open scoped Bundle ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- Differentiability of a section of `Hom(TM, TM)` at a point, written out: the `T%` elaborator
cannot infer the model fibre for a `Hom` bundle, as Mathlib's own file records in a `TODO`. -/
abbrev MDiffHomAt (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) (x : M) : Prop :=
  MDifferentiableAt I (I.prod 𝓘(ℝ, E →L[ℝ] E))
    (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) y (A y)) x

/-- **THE INDUCED COVARIANT DERIVATIVE ON `Hom(TM, TM)`, EVALUATED ON A SECTION**:
`(∇_u A)(σ) = ∇_u (A σ) − A (∇_u σ)`, as a continuous linear map in the direction `u`. -/
noncomputable def homCovAux (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y)
    (σ : Π y : M, TangentSpace I y) (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  cov.toFun (fun y ↦ A y (σ y)) x - (A x).comp (cov.toFun σ x)

attribute [local instance] KoszulManifold.finDimTangent

variable {cov}

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- Applying a differentiable section of `Hom(TM, TM)` to a differentiable section gives a
differentiable section (Mathlib's `MDifferentiableAt.clm_bundle_apply`). -/
theorem mdiffAt_apply {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {σ : Π y : M, TangentSpace I y} {x : M} (hA : MDiffHomAt A x) (hσ : MDiffAt (T% σ) x) :
    MDiffAt (T% (fun y ↦ A y (σ y))) x :=
  MDifferentiableAt.clm_bundle_apply hA hσ

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
/-- The `df ⊗ v` term passes through a continuous linear map. -/
theorem comp_smulRight {x : M} (A : TangentSpace I x →L[ℝ] TangentSpace I x)
    (t : TangentSpace I x →L[ℝ] ℝ) (v : TangentSpace I x) :
    A.comp (t.smulRight v) = t.smulRight (A v) := by
  ext u
  simp

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- **ADDITIVITY IN THE SECTION.** -/
theorem homCovAux_add {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {σ σ' : Π y : M, TangentSpace I y} {x : M} (hA : MDiffHomAt A x)
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) :
    homCovAux cov A (σ + σ') x = homCovAux cov A σ x + homCovAux cov A σ' x := by
  have hsplit : (fun y ↦ A y ((σ + σ') y))
      = (fun y ↦ A y (σ y)) + (fun y ↦ A y (σ' y)) := by
    funext y; simp
  simp only [homCovAux, hsplit]
  rw [cov.isCovariantDerivativeOn.add (mdiffAt_apply hA hσ) (mdiffAt_apply hA hσ') (mem_univ x),
    cov.isCovariantDerivativeOn.add hσ hσ' (mem_univ x)]
  ext u
  simp
  abel

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- **THE LEIBNIZ LAW IN THE SECTION — WHICH IS TENSORIALITY**, because the two `df ⊗ ·` terms
cancel: this is the whole reason `∇_u (A σ) − A (∇_u σ)` depends on `σ` only through `σ x`. -/
theorem homCovAux_smul {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {σ : Π y : M, TangentSpace I y} {f : M → ℝ} {x : M} (hA : MDiffHomAt A x)
    (hf : MDiffAt f x) (hσ : MDiffAt (T% σ) x) :
    homCovAux cov A (f • σ) x = f x • homCovAux cov A σ x := by
  have hsplit : (fun y ↦ A y ((f • σ) y)) = f • (fun y ↦ A y (σ y)) := by
    funext y; simp
  simp only [homCovAux, hsplit]
  rw [cov.isCovariantDerivativeOn.leibniz (mdiffAt_apply hA hσ) hf (mem_univ x),
    cov.isCovariantDerivativeOn.leibniz hσ hf (mem_univ x),
    ContinuousLinearMap.comp_add, comp_smulRight, ContinuousLinearMap.comp_smul]
  ext u
  simp
  module

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- **THE INDUCED DERIVATIVE IS TENSORIAL IN THE SECTION.** -/
theorem tensorialAt_homCovAux {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (hA : MDiffHomAt A x) :
    TensorialAt I E (fun σ ↦ homCovAux cov A σ x) x where
  smul hf hσ := homCovAux_smul hA hf hσ
  add hσ hσ' := homCovAux_add hA hσ hσ'

/-- **AND SO `∇_u A` DEPENDS ON THE SECTION ONLY THROUGH ITS VALUE AT THE POINT**, which is what
makes the induced derivative an element of the fibre of `Hom(TM, TM)` rather than an operation on
sections (`TensorialAt.pointwise`). -/
theorem homCovAux_congr_of_eq {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {σ σ' : Π y : M, TangentSpace I y} {x : M} (hA : MDiffHomAt A x)
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (h : σ x = σ' x) :
    homCovAux cov A σ x = homCovAux cov A σ' x :=
  (tensorialAt_homCovAux hA).pointwise hσ hσ' h

variable (cov) in
/-- **THE INDUCED COVARIANT DERIVATIVE ON `Hom(TM, TM)`**, as a continuous linear map from the
tangent space into the fibre of `Hom(TM, TM)`: `homCovHom A hA u v = (∇_u A)(v)`. The `v` slot is
linear because the expression is tensorial in the section, and the `u` slot because
`homCovAux` is already a continuous linear map in it. -/
noncomputable def homCovHom (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) {x : M}
    (hA : MDiffHomAt A x) :
    TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u ↦ LinearMap.toContinuousLinearMap
        { toFun := fun v ↦ homCovAux cov A (extend E v) x u
          map_add' := fun v₁ v₂ ↦ by
            have h1 : homCovAux cov A (extend E (v₁ + v₂)) x
                = homCovAux cov A (extend E v₁ + extend E v₂) x :=
              homCovAux_congr_of_eq hA (mdifferentiableAt_extend (I := I) E _)
                (mdifferentiableAt_add_section (mdifferentiableAt_extend (I := I) E v₁)
                  (mdifferentiableAt_extend (I := I) E v₂)) (by simp)
            rw [h1, homCovAux_add hA (mdifferentiableAt_extend (I := I) E v₁)
              (mdifferentiableAt_extend (I := I) E v₂)]
            simp
          map_smul' := fun c v ↦ by
            have h1 : homCovAux cov A (extend E (c • v)) x
                = homCovAux cov A ((fun _ ↦ c) • extend E v) x :=
              homCovAux_congr_of_eq hA (mdifferentiableAt_extend (I := I) E _)
                (mdifferentiableAt_const.smul_section
                  (mdifferentiableAt_extend (I := I) E v)) (by simp)
            rw [h1, homCovAux_smul hA (f := fun _ ↦ c) mdifferentiableAt_const
              (mdifferentiableAt_extend (I := I) E v)]
            simp }
      map_add' := fun u₁ u₂ ↦ by ext v; simp
      map_smul' := fun c u ↦ by ext v; simp }

/-- The value of the induced derivative on an extended vector, by definition. -/
theorem homCovHom_apply_extend {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (hA : MDiffHomAt A x) (u v : TangentSpace I x) :
    homCovHom cov A hA u v = homCovAux cov A (extend E v) x u := rfl

/-- **AND ON A SECTION**: `(∇_u A)(σ x) = (∇_u (A σ) − A (∇_u σ))` for `σ` differentiable at `x`. -/
theorem homCovHom_apply {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y}
    {σ : Π y : M, TangentSpace I y} {x : M} (hA : MDiffHomAt A x) (hσ : MDiffAt (T% σ) x)
    (u : TangentSpace I x) :
    homCovHom cov A hA u (σ x) = homCovAux cov A σ x u := by
  rw [homCovHom_apply_extend]
  rw [homCovAux_congr_of_eq hA (mdifferentiableAt_extend (I := I) E _) hσ (by simp)]

/-! ## The induced operation as a covariant derivative -/

open Classical in
variable (cov) in
/-- The induced derivative as a **total** operation on sections of `Hom(TM, TM)`, with the junk
value `0` where `A` is not differentiable — the convention `KoszulManifold.leviCivitaFun` uses, and
what `IsCovariantDerivativeOn` asks for. -/
noncomputable def homCovFun (A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y) :
    Π x : M, TangentSpace I x →L[ℝ] (TangentSpace I x →L[ℝ] TangentSpace I x) := fun x ↦
  if hA : MDiffHomAt A x then homCovHom cov A hA else 0

theorem homCovFun_apply {A : Π y : M, TangentSpace I y →L[ℝ] TangentSpace I y} {x : M}
    (hA : MDiffHomAt A x) (u v : TangentSpace I x) :
    homCovFun cov A x u v = homCovAux cov A (extend E v) x u := by
  simp only [homCovFun, dif_pos hA]
  rfl

/-- **THE INDUCED OPERATION IS A COVARIANT DERIVATIVE ON `Hom(TM, TM)`** — Mathlib's
`IsCovariantDerivativeOn`, on every set. This is the object `CurvatureOrder`, `CurvatureBianchi`
and `CovariantJet` each record the pinned library as not having. -/
theorem isCovariantDerivativeOn_homCovFun (s : Set M) :
    IsCovariantDerivativeOn (E →L[ℝ] E) (homCovFun cov) s where
  add := by
    intro A A' x hA hA' _
    have hsum : MDiffHomAt (A + A') x := mdifferentiableAt_add_section hA hA'
    ext u v
    rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      homCovFun_apply hsum, homCovFun_apply hA, homCovFun_apply hA']
    have hσ := mdifferentiableAt_extend (I := I) E v
    have hsplit : (fun y ↦ (A + A') y (extend E v y))
        = (fun y ↦ A y (extend E v y)) + (fun y ↦ A' y (extend E v y)) := by
      funext y; simp
    simp only [homCovAux, hsplit]
    rw [cov.isCovariantDerivativeOn.add (mdiffAt_apply hA hσ) (mdiffAt_apply hA' hσ) (by trivial)]
    simp
    abel
  leibniz := by
    intro A g x hA hg _
    have hsmul : MDiffHomAt (g • A) x := hg.smul_section hA
    ext u v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, homCovFun_apply hsmul, homCovFun_apply hA]
    have hσ := mdifferentiableAt_extend (I := I) E v
    have hsplit : (fun y ↦ (g • A) y (extend E v y)) = g • (fun y ↦ A y (extend E v y)) := by
      funext y; simp
    simp only [homCovAux, hsplit]
    rw [cov.isCovariantDerivativeOn.leibniz (mdiffAt_apply hA hσ) hg (by trivial)]
    simp
    module

variable (cov) in
/-- **THE ENDOMORPHISM BUNDLE CARRIES AN INDUCED CONNECTION**, bundled as Mathlib's
`CovariantDerivative`. -/
noncomputable def homCovariantDerivative :
    CovariantDerivative I (E →L[ℝ] E)
      (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) :=
  ⟨homCovFun cov, isCovariantDerivativeOn_homCovFun univ⟩

/-! ## The identity endomorphism, and a value that is not zero -/

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- The identity endomorphism read in a trivialisation is the identity of the model fibre. -/
theorem inCoordinates_id {x y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
        (TangentSpace I : M → Type _) x y x y (ContinuousLinearMap.id ℝ (TangentSpace I y))
      = ContinuousLinearMap.id ℝ E := by
  rw [ContinuousLinearMap.inCoordinates_eq hy hy]
  ext w
  simp

omit [FiniteDimensional ℝ E] [IsManifold I 2 M] in
/-- **THE IDENTITY ENDOMORPHISM IS A DIFFERENTIABLE SECTION OF `Hom(TM, TM)`**, because it is the
constant identity in every trivialisation. The pinned library states this for no bundle. -/
theorem mdiffHomAt_id (x : M) :
    MDiffHomAt (fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x := by
  refine (mdifferentiableAt_hom_bundle _).mpr ⟨mdifferentiableAt_id, ?_⟩
  refine (mdifferentiableAt_const (c := ContinuousLinearMap.id ℝ E)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  exact inCoordinates_id hy

/-- **THE IDENTITY IS PARALLEL FOR EVERY CONNECTION**, and unconditionally: where `A` is not
differentiable the junk value is `0` too, so no hypothesis is needed. -/
theorem homCovFun_id (x : M) :
    homCovFun cov (fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x = 0 := by
  by_cases hA : MDiffHomAt (fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x
  · ext u v
    rw [homCovFun_apply hA]
    simp [homCovAux]
  · simp [homCovFun, dif_neg hA]

set_option synthInstance.maxHeartbeats 80000 in
-- the nested `Hom` type `TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x` is what
-- `smulRight` in the Leibniz law lands in, and its normed-space instance is three synonyms deep
/-- **AND A VALUE THAT IS NOT ZERO**: `∇_u (f · id) = (df u) · id`, so the induced derivative is
nonzero as soon as `f` has a nonzero derivative. This is the non-vacuity check the construction
needs. Nothing is assumed about the *identity* factor, because the identity is differentiable
(`mdiffHomAt_id`); the hypothesis on `f` is assumed here and is removed in
`HomCovariantNonvac.homCovFun_smul_id'` (`ERRATUM 495`). -/
theorem homCovFun_smul_id {f : M → ℝ} {x : M} (hf : MDiffAt f x) (u v : TangentSpace I x) :
    homCovFun cov (f • fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) x u v
      = (extDerivFun (I := I) f x u) • v := by
  have h := (isCovariantDerivativeOn_homCovFun (cov := cov) univ).leibniz
    (σ := fun y ↦ ContinuousLinearMap.id ℝ (TangentSpace I y)) (g := f) (x := x)
    (mdiffHomAt_id x) hf (mem_univ x)
  rw [h]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, homCovFun_id,
    smul_zero, zero_add, ContinuousLinearMap.coe_id', id_eq]

end HomCovariant
