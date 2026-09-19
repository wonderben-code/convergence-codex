import CurvatureCovFull
import CurvatureCovOrder

/-!
# A doubly-nested bundle does carry a section of `∇R`, and the obstacle is which slot, not the depth

The `UNLOCK_WATCHLIST` block *the two residues of `CurvatureCovBundle`* has carried two asks since
2026-09-11. `RE-SWEEP #69` discharged the first — the FOUR-DEEP bundling, built by
`CurvatureCovFull.covRiemannFull`. Its second, residue (b), says:

> Nothing makes `y ↦ covRiemannHom hk y u` a `C^k` section of the doubly-nested bundle, and that
> is **not** plumbing: the extensions are taken at one point and a section statement compares
> points, so the object would have to be rebuilt from a field of directions rather than a vector.

**RESIDUE (b) IS DISCHARGED IN THE FORM IT PRESCRIBES, AND ITS LITERAL SENTENCE IS STILL
UNPROVED.** The distinction is worth the two paragraphs.

**The prescription.** (b) says the object *would have to be rebuilt from a field of directions
rather than a vector*. §3 is that rebuild: `contMDiffAt_covRiemannHom_of_field` makes
`y ↦ covRiemannHom hk y (X y)` — the same two-curvature-slot bundling, with the direction a
**field** — a `C^k` section of `Hom(TM, Hom(TM, Hom(TM, TM)))`. So (b)'s diagnosis was exactly
right and was a description of the route, not of a wall.

**The literal sentence.** (b) is written about `y ↦ covRiemannHom hk y u` for a fixed **vector**
`u`. That is well-typed — `TangentSpace I x` is a type synonym for `E`, so `u` is accepted at
every point, **measured 2026-09-19 by trying it** — and it is **still not proved here**, because
the object it names is chart-dependent: a vector held fixed across points is fixed only through a
trivialisation. Nothing below touches that form.

**And the DEPTH was never the obstacle**, which §2 shows first and at one level less: the
direction-bundled `covRiemannSecDir` takes no extension and no vector at all, so a section
statement about it compares points already, and the doubly-nested statement goes through in three
lemmas.

## What is proved

**`inCoordinates_apply_localFrame'`** and **`contMDiffAt_hom_of_localFrame'`** — **THE FRAME
CRITERION WITH THE CODOMAIN AN ARBITRARY VECTOR BUNDLE.** A section of `Hom(TM, E₂)` is `C^n` at
`x` as soon as its values on the chart's local frame are `C^n` sections of `E₂`.
`LeviCivitaOrder.contMDiffAt_hom_of_localFrame` is the case `E₂ = TM`, and the generalisation was
cheaper than it looks because **two of its three ingredients were already general**: Mathlib's
`contMDiffAt_hom_bundle` quantifies over both fibres, and
`LeviCivitaRegular.contMDiffAt_clm_of_basis` over its codomain. Only the coordinate-matrix lemma
was tangent-specific, and generalising it costs **one extra hypothesis** — membership in the
CODOMAIN trivialisation's base set, which in the tangent case was the same set as the domain's.
The proof body is the original's, unchanged.

**`contMDiffVectorBundle_add_three`** — the tangent bundle of a `C^(k+4)` manifold is a `C^(k+3)`
vector bundle, which is the order the chart's local frame has to be available at once the
direction is a field. One order above `RicciOrder.contMDiffVectorBundle_add_two` and the same
one-liner.

**`contMDiffAt_covRiemannSecDir_hom`** — **THE THEOREM**: for `Y, Z` of class `C^(k+3)` at the
point and the Levi-Civita connection of a `C^(k+3)` metric on a `C^(k+4)` manifold,
`y ↦ (∇_· R)(Y, Z)(y)` is a **`C^k` section of `Hom(TM, Hom(TM, TM))`** — the doubly-nested
bundle, with the direction slot inside it. The frame values are
`covRiemann Y Z y (localFrame b i y)`, and each is
`CurvatureCovOrder.contMDiffAt_covRiemann_hom` with the frame as the direction field.

**AND IT TAKES NO LOWER BOUND ON `k`**, which is the `k`-free core of `ERRATUM 659` reaching the
regularity: `contMDiffAt_covRiemann_hom` carries no `hk`, so neither does this.

**`contMDiffAt_covRiemannHom_of_field`** — **RESIDUE (b)'S PRESCRIBED REBUILD**: with the
direction a **field** `X` of class `C^(k+3)` at the point, `y ↦ covRiemannHom hk y (X y)` is a
`C^k` section of `Hom(TM, Hom(TM, Hom(TM, TM)))`. The frame criterion twice, and at the bottom
`CurvatureCovBundle.covRiemannAt_eq` replaces the one-point extensions by the frame FIELDS on the
trivialisation's base set — which is precisely where the extensions stop mattering. **This one
does take `hk`**, because `covRiemannHom` does.

Of this file's **five** declarations, **three** carry a `k` binder and **one** carries `k ≠ 0`.

## What is NOT here

* **THE FOUR-DEEP OBJECT IS STILL NOT A SECTION, AND THE COST OF EVEN ASKING IS MEASURED.**
  Nothing here makes `x ↦ CurvatureCovFull.covRiemannFull hk x` a `C^k` section of the four-deep
  bundle. **The statement of it typechecks only at `maxHeartbeats 2000000` and
  `synthInstance.maxHeartbeats 1000000`** — measured 2026-09-19 by writing it down with a
  `sorry` — against `1000000` and `400000` for §3 one level below. **Not attempted, no cost
  claimed** (`ERRATUM 246`), and the numbers are here so the next reader starts from a figure.
* **NOR IS THE FIXED-VECTOR FORM**, which is residue (b)'s literal subject: `y ↦ covRiemannHom hk
  y u` for `u` a vector. **As of 2026-09-19** it is well-typed — `TangentSpace I x` reduces to
  `E`, measured by trying it — and nothing in the estate proves it, because the object is
  chart-dependent: a vector held fixed across points is fixed only through a trivialisation.
* **THE TANGENT CASE IS NOT DERIVED FROM THE GENERAL LEMMA, MEASURED 2026-09-19 BY TRYING IT.**
  `LeviCivitaOrder.contMDiffAt_hom_of_localFrame` is the statement above at `E₂ := TangentSpace I`,
  `F₂ := E`, and handing it `contMDiffAt_hom_of_localFrame' φ b h` **fails**: Lean answers
  `failed to synthesize (y : M) → NormedAddCommGroup (TangentSpace I y)`, because the per-fibre
  normed structure on the tangent bundle does not arrive as that instance. So the two lemmas
  **coexist and neither is a copy of the other**; the general one is not a second proof of the
  tangent one, and the tangent one is what four files already call. The attempt and its error are
  recorded rather than the subsumption asserted (`ERRATUM 657`).
* **NO SECOND BIANCHI IDENTITY AT THE SECTION LEVEL.** `CurvatureCovFull.covRiemannFull_cyclic`
  is at a point, on three tangent vectors, and nothing here lifts it to fields.
* **NO REGULARITY IN THE TWO CURVATURE SLOTS.** `covRiemannHom`'s bundling of those needs `hk`,
  and nothing here makes it a section either.
* **NOTHING ABOUT `a₂`, the heat semigroup or a parametrix.** `W5`'s rung 4 is unchanged.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`), **and the arithmetic in it is checked by
`binderclaim_scan.py` as of `ERRATUM 662`**: the file has two section contexts. §1 is minimal — a
normed space `E` over `ℝ`, a `ChartedSpace H M` with model `I`, `[IsManifold I 2 M]`, and a
codomain vector bundle `E₂` with fibre `F₂`; `[FiniteDimensional ℝ E]` is introduced only for the
frame criterion, and `[Finite ι]` with it. §2 is `CurvatureCovOrder`'s, unchanged — the `C^(k+4)`
manifold and the `C^(k+3)` metric, with that file's eight order-shift instances plus
`KoszulManifold.finDimTangent` and `CurvatureTensor.contMDiffVectorBundle_two` as local instances.
One `omit`, on `contMDiffVectorBundle_add_three`, dropping the five binders the linter named.
**Two `set_option`s**, both scoped with `in` to `contMDiffAt_covRiemannHom_of_field` and both
carrying their reason in a comment: `maxHeartbeats 1000000` and
`synthInstance.maxHeartbeats 400000`, needed because the target bundle has three nested `→L`
fibres. The unused-variable linter reports nothing.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace CurvatureCovFullOrder

open Bundle Manifold VectorField FiberBundle Set KoszulManifold
open scoped Bundle ContDiff Topology

/-! ## 1. The frame criterion, with the codomain an arbitrary vector bundle -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {ι : Type*}
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₂ : M → Type*} [∀ y, NormedAddCommGroup (E₂ y)] [∀ y, NormedSpace ℝ (E₂ y)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]

/-- **THE COORDINATE MATRIX OF A SECTION OF `Hom(TM, E₂)`**, with `E₂` an arbitrary vector
bundle: in the chart at `x` its columns are the trivialised values on the chart's local frame.
`LeviCivitaRegular.inCoordinates_apply_localFrame` is this with `E₂ = TM`, and the generalisation
costs one extra hypothesis — membership in the CODOMAIN trivialisation's base set, which in the
tangent case was the same set. -/
theorem inCoordinates_apply_localFrame' (φ : Π y : M, TangentSpace I y →L[ℝ] E₂ y)
    {x y : M} (hy : y ∈ (trivializationAt E (TangentSpace I : M → Type _) x).baseSet)
    (hy₂ : y ∈ (trivializationAt F₂ E₂ x).baseSet)
    (b : Module.Basis ι ℝ E) (i : ι) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) F₂ E₂ x y x y (φ y) (b i) =
      (trivializationAt F₂ E₂ x
        ⟨y, φ y ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame b i y)⟩).2 := by
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Trivialization.symmL_apply, Trivialization.continuousLinearMapAt_apply,
    Trivialization.coe_linearMapAt_of_mem _ hy₂,
    Trivialization.localFrame_apply_of_mem_baseSet _ b hy,
    Trivialization.basisAt, Module.Basis.map_apply, Trivialization.linearEquivAt_symm_apply]

variable [FiniteDimensional ℝ E]

/-- **A SECTION OF `Hom(TM, E₂)` IS `C^n` AT `x` AS SOON AS ITS VALUES ON THE CHART'S LOCAL FRAME
ARE `C^n` SECTIONS OF `E₂`**, for `E₂` an arbitrary vector bundle.
`LeviCivitaOrder.contMDiffAt_hom_of_localFrame` is this with `E₂ = TM`, and the proof is that
one verbatim: `contMDiffAt_hom_bundle` is already general in both fibres and
`LeviCivitaRegular.contMDiffAt_clm_of_basis` is already general in its codomain, so the only
tangent-specific step was the lemma above. -/
theorem contMDiffAt_hom_of_localFrame' [Finite ι] {n : WithTop ℕ∞}
    (φ : Π y : M, TangentSpace I y →L[ℝ] E₂ y) {x : M} (b : Module.Basis ι ℝ E)
    (h : ∀ i, ContMDiffAt I (I.prod 𝓘(ℝ, F₂)) n (fun y ↦ TotalSpace.mk' F₂ y
      (φ y ((trivializationAt E (TangentSpace I : M → Type _) x).localFrame b i y))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F₂)) n
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F₂) y (φ y)) x := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, LeviCivitaRegular.contMDiffAt_clm_of_basis b fun i ↦ ?_⟩
  refine ((contMDiffAt_section x).1 (h i)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x),
    (trivializationAt F₂ E₂ x).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F₂ E₂ x)] with y hy hy₂
  exact inCoordinates_apply_localFrame' φ hy hy₂ b i

end General

/-! ## 2. The order shift, and the theorem -/

section Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I 2 M]
  [IsManifold I 3 M] {k : ℕ} [IsManifold I ((k : WithTop ℕ∞) + 1 + 1 + 1 + 1) M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

attribute [local instance] CurvatureCovOrder.isManifold_up CurvatureCovOrder.isManifold_up_two
  CurvatureCovOrder.isContMDiffRiemannianBundle_up
  CurvatureCovOrder.isContMDiffRiemannianBundle_up_two CurvatureCovOrder.isManifold_down
  CurvatureCovOrder.isManifold_down_two CurvatureCovOrder.isContMDiffRiemannianBundle_down
  CurvatureCovOrder.isContMDiffRiemannianBundle_down_two
  KoszulManifold.finDimTangent CurvatureTensor.contMDiffVectorBundle_two
  RicciOrder.contMDiffVectorBundle_add_two

omit [CompleteSpace E] [FiniteDimensional ℝ E] [IsManifold I 2 M] [IsManifold I 3 M]
  [IsContMDiffRiemannianBundle I ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] in
/-- The tangent bundle of a `C^(k+4)` manifold is a `C^(k+3)` vector bundle — the order the
chart's local frame has to be available at once the DIRECTION is a field. One order above
`RicciOrder.contMDiffVectorBundle_add_two`, and the same one-liner. -/
theorem contMDiffVectorBundle_add_three :
    ContMDiffVectorBundle ((k : WithTop ℕ∞) + 1 + 1 + 1) E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

attribute [local instance] contMDiffVectorBundle_add_three

/-- **THE DIRECTION-BUNDLED `∇R` IS A `C^k` SECTION OF `Hom(TM, Hom(TM, TM))`.** -/
theorem contMDiffAt_covRiemannSecDir_hom {Y Z : Π y : M, TangentSpace I y} {x : M}
    (hY : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Y) x)
    (hZ : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% Z) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) (k : WithTop ℕ∞)
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) y
        (CurvatureCovFull.covRiemannSecDir Y Z y)) x := by
  refine contMDiffAt_hom_of_localFrame'
    (E₂ := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y) (F₂ := E →L[ℝ] E)
    _ (Module.finBasis ℝ E) fun i ↦ ?_
  exact CurvatureCovOrder.contMDiffAt_covRiemann_hom
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1 + 1) _ (Module.finBasis ℝ E) i
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)) hY hZ

/-! ## 3. Residue (b)'s own prescription: the direction as a field -/

-- The two limits below are raised because the target bundle is `Hom(TM, Hom(TM, Hom(TM, TM)))`:
-- unifying a three-deep `→L` fibre against `ContinuousLinearMap.inCoordinates` twice, and
-- synthesising the vector-bundle instances at each level, exceeds the defaults. **Measured, not
-- guessed**: the STATEMENT alone needs `maxHeartbeats 1000000` and
-- `synthInstance.maxHeartbeats 400000` at this depth, and one level further up — the four-deep
-- `covRiemannFull` as a section — needs 2000000 and 1000000 to typecheck at all. This is the
-- elaboration cost the `UNLOCK_WATCHLIST` block predicted for the BUNDLING, where it did not
-- occur; it occurs here, one step later, for the SECTION.
set_option maxHeartbeats 1000000 in
-- and the instance search with it, for the same reason: three nested `→L` fibres.
set_option synthInstance.maxHeartbeats 400000 in
/-- **AND WITH THE DIRECTION A FIELD, THE CURVATURE-SLOT BUNDLING IS A SECTION TOO** —
`y ↦ (∇_{X y} R)(·, ·)` is a `C^k` section of `Hom(TM, Hom(TM, Hom(TM, TM)))`. This is the object
the `UNLOCK_WATCHLIST` block's residue (b) prescribes: it says the object *would have to be
rebuilt from a field of directions rather than a vector*, and this is that rebuild. The proof is
the frame criterion twice, and at the bottom `CurvatureCovBundle.covRiemannAt_eq` replaces the
extensions by the frame fields on the trivialisation's base set — which is exactly where the
one-point extensions stop mattering. -/
theorem contMDiffAt_covRiemannHom_of_field (hk : k ≠ 0) {X : Π y : M, TangentSpace I y} {x : M}
    (hX : CMDiffAt ((k : WithTop ℕ∞) + 1 + 1 + 1) (T% X) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E)))) (k : WithTop ℕ∞)
      (fun y : M ↦ TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))) y
        (CurvatureCovBundle.covRiemannHom (I := I) hk y (X y))) x := by
  refine contMDiffAt_hom_of_localFrame'
    (E₂ := fun y : M ↦ TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] TangentSpace I y))
    (F₂ := E →L[ℝ] (E →L[ℝ] E)) _ (Module.finBasis ℝ E) fun i ↦ ?_
  refine contMDiffAt_hom_of_localFrame'
    (E₂ := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y)
    (F₂ := E →L[ℝ] E) _ (Module.finBasis ℝ E) fun j ↦ ?_
  have hmem := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  refine (CurvatureCovOrder.contMDiffAt_covRiemann_hom hX
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1 + 1) _ (Module.finBasis ℝ E) i hmem)
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1 + 1) _ (Module.finBasis ℝ E) j
      hmem)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
    hmem] with y hy
  congr 1
  simp only [CurvatureCovBundle.covRiemannHom_apply]
  exact (CurvatureCovBundle.covRiemannAt_eq hk
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1) _ (Module.finBasis ℝ E) i hy)
    (contMDiffAt_localFrame_of_mem ((k : WithTop ℕ∞) + 1 + 1) _ (Module.finBasis ℝ E) j hy)
    (X y))

end Curvature

end CurvatureCovFullOrder
