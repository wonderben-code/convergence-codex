/-
  FieldAutInvariance.lean — the Gaussian field is invariant under every graph
  automorphism, at the level of the MEASURE.

  WHY, AND WHAT IT IS NOT. This wall has spent its whole life on OS2. The
  estate has reflection positivity at covariance level, at measure level and on
  the exponential algebra, and **nothing whatever about the other Osterwalder–
  Schrader axioms for the lattice field.** Checked by shape before being
  written (ERRATUM 76): `paper_f` was grepped for `OS0`, `OS1`, `OS3`, `OS4`,
  and every hit is a numeric field of a `CascadeFoundation` structure or an
  `F*` file's commentary — a dimension count, a decay rate. **No theorem about
  `gaussianField` other than OS2 exists.** Nothing outside `paper_f` was
  searched.

  **THIS IS NOT OS3, AND CALLING IT OS3 WOULD BE THE OVERCLAIM THIS PROJECT
  KEEPS CATCHING.** OS3 is invariance under the full Euclidean group `E(d)`.
  A finite graph has no such group; what it has is its automorphism group, and
  on a box that is the reflections and coordinate permutations, on a torus also
  the translations. **Invariance under that group is what OS3 degenerates to in
  finite volume**, and full Euclidean invariance is a continuum statement no
  finite-volume theorem can reach. The file proves the finite-volume statement
  and names the gap rather than the axiom.

  **THE ARGUMENT, AND WHERE THE ESTATE ALREADY WAS.** A centred Gaussian is
  determined by its covariance, so invariance of the measure is invariance of
  the Green function — and
  `LatticeReflectionPositive.green_congr` has said since the lattice was built
  that the Green function is invariant under any adjacency-preserving
  bijection, **with no involutivity hypothesis**. That is the whole
  mathematical content and it was already green. What was missing is the step
  from a matrix identity to a measure identity, and that is four lemmas of
  Mathlib plumbing: the permutation as a linear isometry, characteristic
  functions under an isometry, the Gaussian's characteristic function, and the
  fact that characteristic functions determine a finite measure.

  **WHY IT IS WORTH THE PLUMBING.** Every OS2 theorem in the estate is about a
  measure; every invariance theorem was about a matrix. This is the first
  statement in the estate that says the FIELD, rather than its covariance, has
  a symmetry — and it is the form the remaining OS axioms would have to be
  stated in.

  WHAT THIS FILE PROVES:
  1. **`IsGraphAut`** — adjacency-preserving bijection. `GraphReflection.IsRefl`
     is this plus involutivity, and **the involutivity is not needed here**:
     dropping it is what lets the statement cover translations of the torus and
     coordinate permutations of the box, neither of which is an involution.
     **Mathlib has `SimpleGraph.Iso` and this is not a substitute for it** — the
     bare predicate is used because `green_congr` takes exactly this shape, and
     bundling would mean unbundling at every call. Said so that the definition
     does not read as an absence claim about Mathlib, which it is not.
  2. **`permField`** — the action on field configurations, as a linear isometry
     of `EuclideanSpace ℝ V`.
  3. **`charFun_map_isometry`** — the characteristic function of a pushforward
     along a linear isometry, at the adjoint point. General measure theory; not
     in Mathlib under any name found by search.
  4. **`green_quadForm_perm`** — the covariance quadratic form is invariant.
     `green_congr` reindexed; the only step that touches the graph.
  5. **`gaussianField_map_perm`** — **the Gaussian field is invariant under
     every graph automorphism**, as an equality of measures.
  6. **`gaussianField_map_revSite`** — instantiated at the box reflections,
     the estate's only constructed automorphisms.

  WHAT THIS DOES NOT DO.
  * **It is not OS3.** Said above, and said again because it is the sentence a
    reader will be tempted to shorten.
  * **It proves nothing about OS0, OS1 or OS4.** Those need growth bounds,
    Euclidean covariance and clustering respectively, and none is attempted or
    made easier by this.
  * **It instantiates only at the reflections.** The theorem covers every
    automorphism, but the estate constructs no torus translation and no
    coordinate permutation, so there is nothing else to instantiate at. **The
    generality is therefore untested against a non-involutive example**, which
    is stated because it is the honest weakness of this unit — the hypothesis
    was weakened and no case in the estate exercises the weakening.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import NullSpaceDimension

namespace FieldAutInvariance

open Finset Matrix MeasureTheory ProbabilityTheory Complex
open GraphLaplacian BoxGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Automorphisms, without involutivity

`GraphReflection.IsRefl` bundles adjacency preservation with `Function.Involutive`.
Everything below uses only the first, and saying so is the point of §1:
`LatticeReflectionPositive.green_congr` never needed the second either.
-/

/-- An adjacency-preserving bijection of the vertices. -/
def IsGraphAut (G : SimpleGraph V) (θ : V ≃ V) : Prop :=
  ∀ p q, G.Adj (θ p) (θ q) ↔ G.Adj p q

omit [Fintype V] [DecidableEq V] in
theorem IsGraphAut.of_isRefl {G : SimpleGraph V} {θ : V ≃ V}
    (h : GraphReflection.IsRefl G θ) : IsGraphAut G θ := h.adj

/-! ## 2. The action on field configurations -/

/-- A vertex permutation acting on field configurations, as a linear isometry.
    `Mathlib`'s `piLpCongrLeft` at `p = 2`. -/
noncomputable def permField (θ : V ≃ V) :
    EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ θ

omit [DecidableEq V] in
theorem permField_apply (θ : V ≃ V) (ω : EuclideanSpace ℝ V) (p : V) :
    permField θ ω p = ω (θ.symm p) := rfl

/-! ## 3. Characteristic functions under an isometry

Not found in Mathlib. **Scope of the search, since this is an absence claim**
(ERRATUM 76): `Mathlib/` grepped for `charFun_map`, and the hits are
`charFun_map_smul`, `charFun_map_smul_comp`, `charFun_map_add_prod_eq_mul`,
`charFun_map_sum_pi_eq_prod` and `HasGaussianLaw.charFun_map_eq` — a scalar
multiple, a sum of independents, and a Gaussian law, none of them a linear
isometry. No search was made under other spellings. It is three lines from the
definition either way.
-/

/-- **THE CHARACTERISTIC FUNCTION OF A PUSHFORWARD ALONG AN ISOMETRY**, at the
    inverse-image point. -/
theorem charFun_map_isometry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (T : E ≃ₗᵢ[ℝ] E) (μ : Measure E) (t : E) :
    charFun (μ.map T) t = charFun μ (T.symm t) := by
  rw [charFun_apply, charFun_apply,
    integral_map (by fun_prop : AEMeasurable (T : E → E) μ) (by fun_prop)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hin : (inner ℝ (T ω) t : ℝ) = inner ℝ ω (T.symm t) := by
    have h := T.inner_map_map ω (T.symm t)
    rwa [T.apply_symm_apply] at h
  dsimp only
  rw [hin]

/-! ## 4. The covariance is invariant

`green_congr` with both graphs the same and the bijection the automorphism.
This is the only step that mentions the graph, and it needs no involutivity —
the point §1 exists to make.
-/

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

theorem green_perm (hθ : IsGraphAut G θ) (m : ℝ) (p q : V) :
    GraphLaplacian.green G m (θ p) (θ q) = GraphLaplacian.green G m p q :=
  LatticeReflectionPositive.green_congr (G := G) (G' := G) θ hθ m p q

/-- The covariance quadratic form does not see the permutation. -/
theorem green_quadForm_perm {θ : V ≃ V} (hθ : IsGraphAut G θ) (m : ℝ)
    (t : EuclideanSpace ℝ V) :
    (permField θ).symm t ⬝ᵥ (GraphLaplacian.green G m *ᵥ (permField θ).symm t)
      = t ⬝ᵥ (GraphLaplacian.green G m *ᵥ t) := by
  classical
  have hcoord : ∀ p, ((permField θ).symm t) p = t (θ p) := by
    intro p
    rw [permField, LinearIsometryEquiv.piLpCongrLeft_symm,
      LinearIsometryEquiv.piLpCongrLeft_apply]
    simp [Equiv.piCongrLeft']
  simp only [dotProduct, Matrix.mulVec, hcoord]
  calc ∑ p, t (θ p) * ∑ q, GraphLaplacian.green G m p q * t (θ q)
      = ∑ p, t (θ p) * ∑ q, GraphLaplacian.green G m (θ p) (θ q) * t (θ q) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        exact Finset.sum_congr rfl fun q _ => by rw [green_perm hθ]
    _ = ∑ p, t (θ p) * ∑ q, GraphLaplacian.green G m (θ p) q * t q := by
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        exact Equiv.sum_comp θ (fun q => GraphLaplacian.green G m (θ p) q * t q)
    _ = ∑ p, t p * ∑ q, GraphLaplacian.green G m p q * t q :=
        Equiv.sum_comp θ (fun p => t p * ∑ q, GraphLaplacian.green G m p q * t q)

/-! ## 5. The measure is invariant

A centred Gaussian is determined by its characteristic function, which is
determined by its covariance. §4 says the covariance does not see the
permutation, so neither does the measure.
-/

/-- **THE GAUSSIAN FIELD IS INVARIANT UNDER EVERY GRAPH AUTOMORPHISM.** No
    involutivity: the hypothesis is adjacency preservation alone. This is the
    finite-volume statement OS3 degenerates to, and it is not OS3 — see the
    header. -/
theorem gaussianField_map_perm {θ : V ≃ V} (hθ : IsGraphAut G θ) (hm : m ≠ 0) :
    (GraphLaplacian.gaussianField G m).map (permField θ)
      = GraphLaplacian.gaussianField G m := by
  have hps : (GraphLaplacian.green G m).PosSemidef :=
    (GraphLaplacian.green_posDef G hm).posSemidef
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_map_isometry, GraphLaplacian.gaussianField,
    charFun_multivariateGaussian hps, charFun_multivariateGaussian hps,
    green_quadForm_perm hθ]
  simp

section Box

variable {d n : ℕ}

/-- **AT THE BOX REFLECTIONS**, the estate's only constructed automorphisms.
    The theorem above covers translations and coordinate permutations too;
    nothing in the estate builds one, so nothing else is instantiated and the
    header says so. -/
theorem gaussianField_map_revSite (i : Fin d) {m : ℝ} (hm : m ≠ 0) :
    (GraphLaplacian.gaussianField (boxGraph d n) m).map
        (permField (GraphReflection.revSite (n := n) i))
      = GraphLaplacian.gaussianField (boxGraph d n) m :=
  gaussianField_map_perm
    (IsGraphAut.of_isRefl (GraphReflection.boxGraph_revSite_aut i)) hm

end Box

/-! ## 6. Review — the ways this could be hollow

**"Is this OS3?"** No, and the header says so twice because it is the one
sentence a summary would shorten wrongly. OS3 is invariance under the Euclidean
group. A finite graph has an automorphism group instead, and no theorem in
finite volume can say anything about `E(d)`. What is proved is the honest
finite-volume shadow of OS3 — and it is the first statement in the estate about
a symmetry of the FIELD rather than of its covariance matrix.

**"Is any of it new, given `green_congr`?"** The mathematics is not, and §4
says so: `green_congr` has had the automorphism-invariance of the Green
function since the lattice was built, without involutivity, and this file adds
nothing to it. **What is new is the passage from a matrix identity to a measure
identity.** That is not free — it needs the permutation as an isometry,
characteristic functions under an isometry (which Mathlib does not have and §3
proves), the Gaussian's characteristic function, and the fact that
characteristic functions separate finite measures. A reader who suspects the
result was already there is right about the covariance and wrong about the
measure, and the estate had only the covariance.

**"Does dropping involutivity buy anything?"** In principle a lot — the
translations of the torus are automorphisms and no reflection is — and in
practice, in this estate, nothing yet, **because no non-involutive automorphism
is constructed anywhere.** That is stated in the header as the weakness it is.
A hypothesis weakened without a case exercising the weakening is a promise, not
a result, and it is recorded as a promise.

**"Why `charFun` rather than a direct computation with densities?"** Because
`gaussianField` is defined as `multivariateGaussian`, whose API in Mathlib is
stated through `charFun`, and because the density route needs the covariance
invertible where the characteristic-function route needs it only positive
semidefinite. The proof uses `green_posDef` anyway, so nothing is gained, but
the statement stays closer to the form the other OS axioms would need.
-/

end FieldAutInvariance
