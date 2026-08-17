import TorusFieldEmbedding
import TorusCycleGraph

/-!
# Two graphs, not one — and a lemma whose second unused hypothesis went the way of its first

`FieldAutInvariance` proves the Gaussian field is invariant under every **automorphism** of its
graph. Everything in it is stated for one graph and one vertex type, and **two of those
restrictions were never used by the proofs beneath them.**

`LatticeReflectionPositive.green_congr` — the covariance step the whole file rests on — was
**already cross-graph** when it was written: it takes `e : V ≃ W` and two graphs. The measure-level
statement above it was not. So the estate could say *the covariance of one graph is the covariance
of another, reindexed* and could not say the corresponding thing about the **measure**.

## The second removal, and it is the same lemma that lost its first

`FieldAutInvariance.charFun_map_isometry` is stated for `T : E ≃ₗᵢ[ℝ] E` — a linear isometry of a
space **with itself**. Its own file records that this lemma already lost one hypothesis it never
used: *"the `FiniteDimensional ℝ E` hypothesis is REMOVED. It was written in because the
application is finite-dimensional, and the proof never used it."*

**The same is true of `E = F`, for the same reason and by the same reading.** The proof is
`integral_map` plus `LinearIsometryEquiv.inner_map_map`, and neither knows whether source and
target are the same space. `charFun_map_isometry'` below is the identical proof with the source and
target allowed to differ, and `charFun_map_isometry` is its special case — checked by the kernel in
the `example` beneath it, not asserted.

## What is proved

* **`charFun_map_isometry'`** — the characteristic function of a pushforward along a linear
  isometry **between two spaces**, at the inverse-image point.
* **`congrField`** — the transport of field configurations along a vertex bijection,
  `EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ W`. `FieldAutInvariance.permField` is this at
  `W = V`.
* **`green_quadForm_congr`** — the covariance quadratic form is carried across, from `green_congr`.
* **`gaussianField_map_congr`** — **THE GAUSSIAN FIELD OF ONE GRAPH IS THE GAUSSIAN FIELD OF ANY
  GRAPH ISOMORPHIC TO IT**, as an equality of measures.
* **`gaussianField_map_iso`** — the same, phrased for a `SimpleGraph.Iso`, which is the form a
  caller holding one actually has.
* **`gaussianField_torus_eq_cycleGraph`** — **the payoff.** `TorusCycleGraph` proved the estate's
  `d = 1` torus **is** Mathlib's `cycleGraph` as a graph. This says the estate's Gaussian field on
  it **is** the Gaussian field on `cycleGraph`, as a measure.

## `ERRATUM 48`: does this reach anything the estate could not reach?

**Yes, and it is not a rephrasing.** `FieldAutInvariance` can only ever equate a measure with
*itself*; every conclusion it reaches has the same measure on both sides. `gaussianField_map_congr`
equates measures on **different types**, which no instance of `gaussianField_map_perm` can state at
all. The payoff theorem is a witness: its two sides live on `EuclideanSpace ℝ (Site 1 (n+1))` and
`EuclideanSpace ℝ (Fin (n+1))`.

## What this is NOT

**It is not OS3**, and `FieldAutInvariance`'s capitals apply here unchanged and for the same
reason: relabelling a finite graph is not the Euclidean group, and a statement relating two finite
graphs is not a statement about `E(d)` either.

**It is not a new covariance fact.** `green_congr` had the mathematics; what was missing was the
passage from a matrix identity to a measure identity across two vertex types, which is the passage
`FieldAutInvariance` built in one type and its header called *"the form the remaining axioms would
need"*.

**`OS4` does not move.** No sequence of measures, no limit, no compactness. **No spectral gap is
claimed and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace FieldIsoInvariance

open Finset Matrix MeasureTheory ProbabilityTheory Complex
open GraphLaplacian

/-! ## 1. The characteristic-function lemma, between two spaces -/

/-- **THE CHARACTERISTIC FUNCTION OF A PUSHFORWARD ALONG AN ISOMETRY**, at the inverse-image
point, **with source and target allowed to differ**.

Word for word `FieldAutInvariance.charFun_map_isometry`'s proof. That statement fixes `E ≃ₗᵢ[ℝ] E`;
`integral_map` and `LinearIsometryEquiv.inner_map_map` are the only steps, and neither knows
whether the two spaces are the same. -/
theorem charFun_map_isometry' {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    (T : E ≃ₗᵢ[ℝ] F) (μ : Measure E) (t : F) :
    charFun (μ.map T) t = charFun μ (T.symm t) := by
  rw [charFun_apply, charFun_apply,
    integral_map (by fun_prop : AEMeasurable (T : E → F) μ) (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hin : (inner ℝ (T ω) t : ℝ) = inner ℝ ω (T.symm t) := by
    have h := T.inner_map_map ω (T.symm t)
    rwa [T.apply_symm_apply] at h
  dsimp only
  rw [hin]

/-- **AND THE ONE-SPACE VERSION IS ITS SPECIAL CASE**, checked by the kernel rather than asserted.
-/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (T : E ≃ₗᵢ[ℝ] E) (μ : Measure E) (t : E) :
    charFun (μ.map T) t = charFun μ (T.symm t) :=
  charFun_map_isometry' T μ t

/-! ## 2. Transport of field configurations across two vertex types -/

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- The action on field configurations of a bijection **between two vertex types**.
`FieldAutInvariance.permField` is this at `W = V`. -/
noncomputable def congrField (e : V ≃ W) :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ W :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

omit [DecidableEq V] [DecidableEq W] in
theorem congrField_symm_apply (e : V ≃ W) (t : EuclideanSpace ℝ W) (p : V) :
    (congrField e).symm t p = t (e p) := by
  rw [congrField, LinearIsometryEquiv.piLpCongrLeft_symm,
    LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Equiv.piCongrLeft']

variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
variable {m : ℝ}

/-! ## 3. The covariance form is carried across -/

/-- **THE COVARIANCE QUADRATIC FORM CROSSES THE ISOMORPHISM.** This is
`FieldAutInvariance.green_quadForm_perm` with the two graphs allowed to differ; the only step that
mentions a graph is `LatticeReflectionPositive.green_congr`, **which was cross-graph already**. -/
theorem green_quadForm_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q) (m : ℝ)
    (t : EuclideanSpace ℝ W) :
    (congrField e).symm t ⬝ᵥ (green G m *ᵥ (congrField e).symm t)
      = t ⬝ᵥ (green G' m *ᵥ t) := by
  classical
  simp only [dotProduct, Matrix.mulVec, congrField_symm_apply]
  calc ∑ p, t (e p) * ∑ q, green G m p q * t (e q)
      = ∑ p, t (e p) * ∑ q, green G' m (e p) (e q) * t (e q) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        exact Finset.sum_congr rfl fun q _ => by
          rw [LatticeReflectionPositive.green_congr (G := G) (G' := G') e he]
    _ = ∑ p, t (e p) * ∑ q, green G' m (e p) q * t q := by
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        exact Equiv.sum_comp e (fun q => green G' m (e p) q * t q)
    _ = ∑ p, t p * ∑ q, green G' m p q * t q :=
        Equiv.sum_comp e (fun p => t p * ∑ q, green G' m p q * t q)

/-! ## 4. Hence the measures agree -/

/-- **THE GAUSSIAN FIELD OF ONE GRAPH IS THE GAUSSIAN FIELD OF ANY ISOMORPHIC GRAPH**, as an
equality of measures on **different** spaces.

`FieldAutInvariance.gaussianField_map_perm` can only equate a measure with itself. This cannot be
phrased there at all. -/
theorem gaussianField_map_congr (e : V ≃ W) (he : ∀ p q, G'.Adj (e p) (e q) ↔ G.Adj p q)
    (hm : m ≠ 0) :
    (gaussianField G m).map (congrField e) = gaussianField G' m := by
  have hps : (green G m).PosSemidef := (green_posDef G hm).posSemidef
  have hps' : (green G' m).PosSemidef := (green_posDef G' hm).posSemidef
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_isometry']
  simp only [gaussianField]
  rw [charFun_multivariateGaussian hps, charFun_multivariateGaussian hps',
    green_quadForm_congr e he]
  simp

/-- **THE SAME, FOR A `SimpleGraph.Iso`** — the form a caller holding one actually has. -/
theorem gaussianField_map_iso (e : G ≃g G') (hm : m ≠ 0) :
    (gaussianField G m).map (congrField e.toEquiv) = gaussianField G' m :=
  gaussianField_map_congr e.toEquiv (fun _ _ => e.map_rel_iff) hm

/-! ## 5. The payoff: the estate's one-dimensional torus field IS Mathlib's cycle-graph field -/

/-- **THE PAYOFF.** `TorusCycleGraph.torusGraph_one_iso` proved the estate's `d = 1` torus **is**
Mathlib's `cycleGraph`, as a graph. This says its Gaussian field **is** the Gaussian field on
`cycleGraph`, as a measure — and the two sides live on different spaces, which is exactly what
`FieldAutInvariance` cannot state. -/
theorem gaussianField_torus_eq_cycleGraph (n : ℕ) (hm : m ≠ 0) :
    (gaussianField (TorusReflection.torusGraph 1 (n + 1)) m).map
        (congrField (TorusCycleGraph.torusGraph_one_iso n).toEquiv)
      = gaussianField (SimpleGraph.cycleGraph (n + 1)) m :=
  gaussianField_map_iso (TorusCycleGraph.torusGraph_one_iso n) hm

end FieldIsoInvariance
