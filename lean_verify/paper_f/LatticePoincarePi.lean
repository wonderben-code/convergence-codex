import LatticeCorrelatedPoincare

/-!
# The `n`-dimensional Poincaré inequality off `Fin n`

`SteinGeneralPi.poincare_contDiff` is the estate's multi-dimensional Gaussian Poincaré inequality
and it is stated over `Fin n → ℝ`. That is the **only** thing keeping
`LatticeCorrelatedPoincare.poincare_correlated_field` from applying to `boxGraph` and `torusGraph`,
whose vertex types are products rather than `Fin n` — `LatticeFieldProduct` §0 already removed the
restriction from the measure identity, and the `UNLOCK_WATCHLIST` records the residue in exactly
these words:

> *"someone reindexes `HermitePiPoincare`/`SteinGeneralPi` off `Fin n`."*

**This is that reindexing**, and it is a generalisation of an estate theorem rather than anything
about fields: nothing below mentions a graph, a propagator or a lattice.

## The one friction, and it is bundling rather than mathematics

The relabelling `y ↦ y ∘ f⁻¹` has to be **two things at once**: a measurable equivalence, so that
`measurePreserving_piCongrLeft` applies and integrals transport; and a continuous linear map, so
that `fderiv` has something to chain through. Mathlib supplies the first (`piCongrLeft`) and not
the second, so `relabel` bundles it as a `→L[ℝ]` and `coe_relabel_eq` identifies the two
underlying functions. **For a constant family the dependent casts inside `piCongrLeft` vanish**,
which is why that identification is one `simp`.

## What is proved

* `gaussPiOf` — the product of independent standard Gaussians indexed by an arbitrary `Fintype`;
  note that `relabel`, `coe_relabel_eq` and `measurePreserving_relabel` need **no** `DecidableEq`,
  which the linter established rather than the author;
* `relabel`, `coe_relabel_eq`, `measurePreserving_relabel` — the relabelling in both bundlings and
  the fact that it preserves the measure;
* `relabel_single` — a coordinate direction relabels to a coordinate direction, which is the whole
  reason the right-hand side survives the transport;
* **`poincare_contDiff_pi`** — `Var Ψ ≤ ∑_{v : V} ∫ (∂_v Ψ)²` against `gaussPiOf V`, for every `C¹`
  `Ψ` with the two `L²` side conditions, at **every finite index type**.

## What this is NOT

**It is not a new inequality.** It is `SteinGeneralPi.poincare_contDiff` with the index type freed,
and it is proved *by* that theorem. The constant, the class of test functions and the shape are
unchanged.

**And it does not by itself carry the correlated inequality to `boxGraph`.** That still has to be
assembled — `LatticeCorrelatedPoincare` cites the `Fin n` version throughout, and re-pointing it at
this one is a further edit. **Not costed** (`ERRATUM 183`), and on this chain that blank is
deliberate: four difficulty estimates, four misses.
-/

namespace LatticePoincarePi

open MeasureTheory ProbabilityTheory GaussianProductMeasure

variable {V : Type*} [Fintype V]

/-! Only the two statements that mention `Pi.single` need `DecidableEq V`; it is carried on those
rather than on the section, because the linter pointed out that the other three never use it. -/

/-- The product of independent standard Gaussians indexed by an arbitrary finite type. At
`V = Fin n` this is `GaussianProductMeasure.gaussPi n`, definitionally. -/
noncomputable def gaussPiOf (V : Type*) [Fintype V] : Measure (V → ℝ) :=
  Measure.pi (fun _ : V => gaussianReal 0 1)

/-! ## 1. The relabelling, in both bundlings -/

/-- `y ↦ y ∘ f⁻¹`, as a continuous linear map. Continuity is automatic in finite dimensions; what
is needed downstream is that `fderiv` can chain through it. -/
noncomputable def relabel (f : Fin (Fintype.card V) ≃ V) :
    (Fin (Fintype.card V) → ℝ) →L[ℝ] (V → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y v => y (f.symm v)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem relabel_apply (f : Fin (Fintype.card V) ≃ V)
    (y : Fin (Fintype.card V) → ℝ) (v : V) : relabel f y v = y (f.symm v) := rfl

/-- The same function as Mathlib's measurable equivalence. **For a constant family the dependent
casts inside `piCongrLeft` disappear**, so this is one `simp`. -/
theorem coe_relabel_eq (f : Fin (Fintype.card V) ≃ V) :
    (relabel f : (Fin (Fintype.card V) → ℝ) → (V → ℝ))
      = MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) f := by
  funext y
  funext v
  simp [relabel, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft']

theorem measurePreserving_relabel (f : Fin (Fintype.card V) ≃ V) :
    MeasurePreserving (relabel f) (gaussPi (Fintype.card V)) (gaussPiOf V) := by
  rw [coe_relabel_eq]
  exact measurePreserving_piCongrLeft (fun _ : V => gaussianReal 0 1) f

/-- **A COORDINATE DIRECTION RELABELS TO A COORDINATE DIRECTION.** This is why the right-hand side
of the inequality survives the transport with its shape intact. -/
theorem relabel_single [DecidableEq V] (f : Fin (Fintype.card V) ≃ V)
    (i : Fin (Fintype.card V)) :
    relabel f (Pi.single i (1 : ℝ)) = (Pi.single (f i) (1 : ℝ) : V → ℝ) := by
  funext v
  simp only [relabel_apply, Pi.single_apply]
  by_cases h : v = f i
  · subst h; simp
  · have hne : i ≠ f.symm v := fun hh => h (by rw [hh]; simp)
    simp [h, Ne.symm hne]

/-! ## 2. The inequality at an arbitrary index type -/

/-- **THE ESTATE'S MULTI-DIMENSIONAL GAUSSIAN POINCARÉ INEQUALITY, OFF `Fin n`.**

`∫Ψ² − (∫Ψ)² ≤ ∑_{v : V} ∫ (∂_v Ψ)²` against the product of independent standard Gaussians indexed
by any finite `V`. Same constant, same test-function class, same shape — only the index type is
freed, and it is freed by citing the `Fin n` version rather than by reproving anything. -/
theorem poincare_contDiff_pi [DecidableEq V] {Ψ : (V → ℝ) → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hmem : MemLp Ψ 2 (gaussPiOf V))
    (hgrad : ∀ v : V, MemLp (fun x => fderiv ℝ Ψ x (Pi.single v (1 : ℝ))) 2 (gaussPiOf V)) :
    (∫ x, Ψ x * Ψ x ∂(gaussPiOf V)) - (∫ x, Ψ x ∂(gaussPiOf V)) ^ 2
      ≤ ∑ v : V, ∫ x, fderiv ℝ Ψ x (Pi.single v (1 : ℝ))
          * fderiv ℝ Ψ x (Pi.single v (1 : ℝ)) ∂(gaussPiOf V) := by
  classical
  set f : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm with hf
  have hΨd : Differentiable ℝ Ψ := hΨ.differentiable (by norm_num)
  have hmap : Measure.map (relabel f) (gaussPi (Fintype.card V)) = gaussPiOf V :=
    (measurePreserving_relabel f).map_eq
  -- the chain rule, with the coordinate direction relabelled
  have hchain : ∀ (y : Fin (Fintype.card V) → ℝ) (i : Fin (Fintype.card V)),
      fderiv ℝ (fun z => Ψ (relabel f z)) y (Pi.single i (1 : ℝ))
        = fderiv ℝ Ψ (relabel f y) (Pi.single (f i) (1 : ℝ)) := by
    intro y i
    have h := fderiv_comp (𝕜 := ℝ) y (hΨd (relabel f y)) (relabel f).differentiableAt
    simp only [Function.comp_def] at h
    rw [h]
    simp [relabel_single]
  -- transports
  have hmem' : MemLp (fun y => Ψ (relabel f y)) 2 (gaussPi (Fintype.card V)) := by
    have := (memLp_map_measure_iff (μ := gaussPi (Fintype.card V))
      (f := (relabel f : (Fin (Fintype.card V) → ℝ) → (V → ℝ)))
      (by rw [hmap]; exact hmem.1) (by fun_prop)).mp (by rw [hmap]; exact hmem)
    simpa [Function.comp_def] using this
  have hgrad' : ∀ i, MemLp (fun y => fderiv ℝ (fun z => Ψ (relabel f z)) y
      (Pi.single i (1 : ℝ))) 2 (gaussPi (Fintype.card V)) := by
    intro i
    have hb := (memLp_map_measure_iff (μ := gaussPi (Fintype.card V))
      (f := (relabel f : (Fin (Fintype.card V) → ℝ) → (V → ℝ)))
      (g := fun x => fderiv ℝ Ψ x (Pi.single (f i) (1 : ℝ)))
      (by rw [hmap]; exact (hgrad (f i)).1) (by fun_prop)).mp (by rw [hmap]; exact hgrad (f i))
    simpa [Function.comp_def, hchain] using hb
  have hcomp : ContDiff ℝ 1 (fun y => Ψ (relabel f y)) := hΨ.comp (relabel f).contDiff
  have key := SteinGeneralPi.poincare_contDiff (n := Fintype.card V) hcomp hmem' hgrad'
  -- every integral against `gaussPiOf V` is one against `gaussPi (card V)`, precomposed
  have htrans : ∀ g : (V → ℝ) → ℝ, AEStronglyMeasurable g (gaussPiOf V) →
      ∫ x, g x ∂(gaussPiOf V) = ∫ y, g (relabel f y) ∂(gaussPi (Fintype.card V)) := by
    intro g hg
    rw [← hmap] at hg ⊢
    rw [integral_map (by fun_prop) hg]
  rw [htrans (fun x => Ψ x * Ψ x) (hmem.1.mul hmem.1), htrans Ψ hmem.1]
  refine key.trans (le_of_eq ?_)
  rw [← Equiv.sum_comp f (fun v => ∫ x, fderiv ℝ Ψ x (Pi.single v (1 : ℝ))
    * fderiv ℝ Ψ x (Pi.single v (1 : ℝ)) ∂(gaussPiOf V))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [htrans (fun x => fderiv ℝ Ψ x (Pi.single (f i) (1 : ℝ))
    * fderiv ℝ Ψ x (Pi.single (f i) (1 : ℝ))) ((hgrad (f i)).1.mul (hgrad (f i)).1)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hchain y i]

end LatticePoincarePi
