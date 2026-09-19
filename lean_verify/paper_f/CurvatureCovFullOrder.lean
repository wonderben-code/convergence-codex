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

**RESIDUE (b) IS NOT DISCHARGED HERE AND THAT SENTENCE IS STILL TRUE.** It is about
`covRiemannHom`, which bundles the two CURVATURE slots at a fixed direction **vector** `u`, and
every one of its slots comes through `extend`. Nothing below touches it.

**What this file does is show that the DEPTH was never the obstacle.** It proves a `C^k` section
of a doubly-nested bundle — `Hom(TM, Hom(TM, TM))` — for the other pairing of slots:
`CurvatureCovFull.covRiemannSecDir` bundles the DIRECTION slot of `covRiemann Y Z ·` for **FIELDS**
`Y` and `Z`, so it takes no extension and no vector and a section statement about it compares
points already. So residue (b)'s diagnosis is exactly right and is a description of the route
rather than of a wall: **rebuild from fields and the doubly-nested statement goes through**, in
three lemmas. What is left of (b) is to do that for `covRiemannHom`'s pairing, which needs the
direction to become a field there too.

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
regularity: `contMDiffAt_covRiemann_hom` carries no `hk`, so neither does this. Of this file's
**four** declarations, **two** carry a `k` binder at all and **none** carries `k ≠ 0`.

## What is NOT here

* **THE VECTOR-LEVEL OBJECT IS STILL NOT A SECTION, AND THE BLOCK'S OBSTACLE APPLIES TO IT
  UNCHANGED.** `CurvatureCovFull.covRiemannFull` and `covRiemannDir` are built through
  `extend E v` — extensions of a vector at one point — so nothing here makes
  `x ↦ covRiemannFull hk x` a section of anything. What this file shows is that the block's
  *would have to be rebuilt from a field of directions* was a description of the route, not of a
  wall. **Not attempted for the vector form, no cost claimed** (`ERRATUM 246`).
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
One `omit`, on `contMDiffVectorBundle_add_three`, dropping the five binders the linter named. No
`set_option` in this file, and the unused-variable linter reports nothing.

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

end Curvature

end CurvatureCovFullOrder
