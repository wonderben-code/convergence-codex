import LatticeClustering
import LatticeMoments

/-!
# Independence of two site observables is exactly non-reachability, and the box has none

`LatticeClustering` bundled the exact clustering property as `ClusteringFinVol` and proved it
**empty on any connected graph**: the separation hypotheses force the second test function to zero,
so the independence asserted is independence from a constant. Its §2 is headed *"And where it has
content"* and contains the two emptiness theorems and nothing else. **This file supplies the
content that heading promised, and the price of it turns out to be exact.**

## What is proved

> **`indepFun_eval_iff_not_reachable`** — the field values at two sites are independent **exactly
> when no path joins them**. Not a bound and not a rate: a biconditional, at every finite graph and
> every nonzero mass. The forward half is `IndepFun.covariance_eq_zero` against
> `GreenDisconnected.green_pos_iff_reachable`; the backward half is `ClusteringFinVol` applied at
> the barrier point `p` itself, which is the observation that makes the two halves meet.
>
> **`exists_indepFun_eval_iff_not_preconnected`** — so the field has an independent pair of site
> observables **exactly when the volume falls apart**. Clustering in finite volume, said as a
> property of the graph rather than of a pair, **is** disconnectedness.
>
> **`not_indepFun_eval_lattice`** — and the box is connected, so **no two of its site observables
> are ever independent**, at any side length and any nonzero mass. `LatticeClustering` said the
> property was empty there; this says what is true instead, which is stronger and worse.
>
> **`exists_nondegenerate_clustering`** — the property is nevertheless not empty. On
> `GreenLargeMass.stepGraph` — two three-vertex paths, this estate's disconnected witness — the
> observables at sites `0` and `1` are independent, **both test functions are nonzero and both
> observables have strictly positive variance**, so this is not the `pair g = 0` instance that
> `LatticeClustering.pair_eq_zero_of_preconnected` exhibits.
>
> **`not_indepFun_step_zero_two`** — and the barrier is doing the work: sites `0` and `2` of that
> same graph lie in one component and their observables are **not** independent. The separation
> hypothesis cannot be dropped, and now there is a graph that says so.

## What this settles about the three finite-volume OS shadows

They are not of equal standing, and this estate has been writing as though they were.

* **Regularity** — `LatticeOSPackage.RegularFinVol`, an instance at every finite graph and every
  nonzero mass, with the constant **known optimal** (`LatticeRegularitySharp`).
* **Euclidean covariance** — `LatticeOS1.EuclideanCovariantFinVol`, an instance at every graph
  automorphism and every order, over a group **known to move every site to every other** on the
  torus (`TorusSiteTransitive`).
* **Clustering** — `LatticeClustering.ClusteringFinVol`, an instance at every finite graph, which
  by the theorems above **says nothing whatever about the box**.

So the sentence this estate's file headers have been carrying — *"`W1`'s open part is still `OS0`
and `OS4`, and `OS1` in its continuum sense"* — is wrong in **both** directions (`ERRATUM 513`,
`ERRATUM 514`), and it is **prescribed** in those words by `UNLOCK_WATCHLIST`, which is why 99 files
of `paper_f` carry it. It understates `OS0`, whose shadow is a bundled `Prop` with an unconditional
instance and a sharp constant; and `WALLS.md` prescribes a *different* precise form of the same
fact — *"`OS0` and `OS4` in their continuum senses"* — which overstates `OS4`, whose shadow is empty
on the one object the OS programme is about. **From this unit the sentence reads**: `W1`'s open
part is `OS0`, `OS1` and `OS4` in their continuum senses, and `OS4`'s finite-volume shadow is empty
on the box where the other two's have content.

## What is NOT here

* **THIS IS NOT OS4, AND IT IS FURTHER FROM OS4 THAN THE FILE IT EXTENDS.** `LatticeFieldFactorises`
  could at least be read as clustering with the separation taken to its limit; what is proved here
  is that on a connected graph that reading is unavailable, because the exact property has no
  instances there at all. The quantitative statements are the ones with content on a connected
  graph — `GreenDecay.covariance_abs_le` bounds the correlation by the graph distance — and **they
  carry a uniform degree bound that is not removed here**.
* **NO RATE, NO LIMIT, NO TRANSLATION AND NO INFINITE VOLUME.** Every statement is at one finite
  graph.
* **THE PACKAGE'S TABLE ROW IS STALE AND IS NOT REPAIRED FROM HERE.** `LatticeOSPackage`'s table
  still reads *"clustering | **not bundled — see below**"*, and `LatticeClustering` bundled it
  **the same day** (both 2026-08-28). The package cannot import the file that corrects it, so the
  row is annotated in place under `ERRATUM 94` rather than edited, and `ERRATUM 515` records that
  the file built to stop naming drift drifted first.
* **NOTHING IS WEAKENED.** No theorem loses a hypothesis, `ClusteringFinVol` keeps its statement,
  and `LatticeClustering`'s two emptiness theorems are cited rather than restated.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is `OS0`, `OS1`
  and `OS4` in their continuum senses, as corrected above.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a `Fintype`, a `DecidableEq` and a
`DecidableRel G.Adj`; `m ≠ 0` on everything that names the propagator, and nothing else. The
witness section adds only `GreenLargeMass.stepGraph`. **No reflection, no half, no coupling
hypothesis, no metric and no continuum.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace ClusteringWitness

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open GreenDisconnected LatticeGeneratingFunctional LatticeClustering
open scoped RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The site observable, as a test function -/

/-- The test function that reads off one site: `δₚ`, the unit vector at `p`. -/
noncomputable def siteDelta (p : V) : EuclideanSpace ℝ V := EuclideanSpace.single p (1 : ℝ)

omit [Fintype V] in
/-- Its coordinates. -/
theorem siteDelta_apply (p q : V) : siteDelta p q = if q = p then (1 : ℝ) else 0 := by
  simp [siteDelta, eq_comm]

omit [Fintype V] in
/-- **AND IT IS NOT THE ZERO TEST FUNCTION**, which is what stops the instance built from it
below from being the degenerate one. -/
theorem siteDelta_ne_zero (p : V) : siteDelta (V := V) p ≠ 0 := by
  intro h
  have := congrArg (fun v : EuclideanSpace ℝ V => v p) h
  simp [siteDelta_apply] at this

/-- Pairing against it **is** evaluation at the site, so every statement below can be read either
way. -/
theorem pair_siteDelta (p : V) : (⇑(pair (siteDelta p))) = fun ω : EuclideanSpace ℝ V => ω p := by
  funext ω
  exact LatticeMoments.inner_single p ω

/-! ## 2. Independence of two site observables is exactly non-reachability -/

/-- Every linear observable of the field is square-integrable — a continuous linear functional of a
Gaussian measure, which is what `IsGaussian.memLp_dual` says. Needed because Mathlib's
`IndepFun.covariance_eq_zero` asks for it. -/
theorem memLp_pair (f : EuclideanSpace ℝ V) : MemLp (⇑(pair f)) 2 (gaussianField G m) :=
  IsGaussian.memLp_dual _ (pair f) 2 (by simp)

omit [Fintype V] [DecidableRel G.Adj] in
/-- `δₚ` vanishes off the component of `p`, trivially: it vanishes off `p`. -/
theorem siteDelta_supported_off (p : V) :
    ∀ v, ¬ G.Reachable p v → siteDelta (V := V) p v = 0 := by
  intro v hv
  rw [siteDelta_apply]
  simp only [ite_eq_right_iff]
  rintro rfl
  exact absurd (SimpleGraph.Reachable.refl v) hv

omit [Fintype V] [DecidableRel G.Adj] in
/-- And `δq` vanishes **on** the component of `p` exactly when `q` is not reachable from `p`. **This
is the step that makes the barrier point `p` itself the right one to apply `ClusteringFinVol` at**,
and it is why the biconditional below needs no new analysis. -/
theorem siteDelta_supported_on {p q : V} (h : ¬ G.Reachable p q) :
    ∀ v, G.Reachable p v → siteDelta (V := V) q v = 0 := by
  intro v hv
  rw [siteDelta_apply]
  simp only [ite_eq_right_iff]
  rintro rfl
  exact absurd hv h

/-- **NO PATH ⟹ INDEPENDENT.** `ClusteringFinVol` at the barrier point `p`, with the two `δ`s as its
test functions. -/
theorem indepFun_eval_of_not_reachable (hm : m ≠ 0) {p q : V} (h : ¬ G.Reachable p q) :
    IndepFun (fun ω : EuclideanSpace ℝ V => ω p) (fun ω => ω q) (gaussianField G m) := by
  have hind := gaussianField_clusteringFinVol (G := G) (m := m) hm p _ _
    (siteDelta_supported_off p) (siteDelta_supported_on h)
  rwa [pair_siteDelta, pair_siteDelta] at hind

/-- **INDEPENDENT ⟹ NO PATH**, which is the half the estate did not have. Independent square-
integrable observables have zero covariance; the covariance of two sites is the propagator between
them; and the propagator is strictly positive exactly along paths. -/
theorem not_reachable_of_indepFun_eval (hm : m ≠ 0) {p q : V}
    (h : IndepFun (fun ω : EuclideanSpace ℝ V => ω p) (fun ω => ω q) (gaussianField G m)) :
    ¬ G.Reachable p q := by
  intro hr
  have hcov : cov[fun ω : EuclideanSpace ℝ V => ω p, fun ω => ω q; gaussianField G m] = 0 := by
    have hp := memLp_pair (G := G) (m := m) (siteDelta (V := V) p)
    have hq := memLp_pair (G := G) (m := m) (siteDelta (V := V) q)
    rw [pair_siteDelta] at hp
    rw [pair_siteDelta] at hq
    exact h.covariance_eq_zero hp hq
  rw [covariance_eval hm] at hcov
  exact absurd hcov (ne_of_gt ((green_pos_iff_reachable G hm p q).mpr hr))

/-- **THE EXACT CLUSTERING PROPERTY IS THE COMPONENT DECOMPOSITION, AND NOTHING ELSE.** -/
theorem indepFun_eval_iff_not_reachable (hm : m ≠ 0) (p q : V) :
    IndepFun (fun ω : EuclideanSpace ℝ V => ω p) (fun ω => ω q) (gaussianField G m)
      ↔ ¬ G.Reachable p q :=
  ⟨not_reachable_of_indepFun_eval hm, indepFun_eval_of_not_reachable hm⟩

/-! ## 3. So on a connected graph no two site observables are ever independent -/

/-- **ON A CONNECTED GRAPH NO TWO SITE OBSERVABLES ARE EVER INDEPENDENT** — including a site with
itself, whose variance is positive. `LatticeClustering.clustering_trivial_of_preconnected` said the
exact property has no non-degenerate instances there; this says the conclusion fails for every pair,
which is the stronger statement. -/
theorem not_indepFun_eval_of_preconnected (hG : G.Preconnected) (hm : m ≠ 0) (p q : V) :
    ¬ IndepFun (fun ω : EuclideanSpace ℝ V => ω p) (fun ω => ω q) (gaussianField G m) :=
  fun h => (indepFun_eval_iff_not_reachable hm p q).mp h (hG p q)

/-- **THE FIELD HAS AN INDEPENDENT PAIR OF SITE OBSERVABLES EXACTLY WHEN THE VOLUME FALLS
APART.** -/
theorem exists_indepFun_eval_iff_not_preconnected (hm : m ≠ 0) :
    (∃ p q : V, IndepFun (fun ω : EuclideanSpace ℝ V => ω p) (fun ω => ω q) (gaussianField G m))
      ↔ ¬ G.Preconnected := by
  constructor
  · rintro ⟨p, q, h⟩ hG
    exact not_indepFun_eval_of_preconnected hG hm p q h
  · intro hG
    simp only [SimpleGraph.Preconnected, not_forall] at hG
    obtain ⟨p, q, hpq⟩ := hG
    exact ⟨p, q, indepFun_eval_of_not_reachable hm hpq⟩

/-- **AND THE BOX IS CONNECTED.** At every side length and every nonzero mass. -/
theorem not_indepFun_eval_lattice {n : ℕ} (hn : 0 < n) (hm : m ≠ 0)
    (p q : IsingFiniteVolume.Site n) :
    ¬ IndepFun (fun ω : EuclideanSpace ℝ (IsingFiniteVolume.Site n) => ω p) (fun ω => ω q)
      (gaussianField (IsingContourSeparation.latticeGraph n) m) :=
  not_indepFun_eval_of_preconnected
    (IsingContourSeparation.latticeGraph_connected hn).preconnected hm p q

end ClusteringWitness

namespace ClusteringWitness

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open GreenLargeMass GreenDisconnected LatticeGeneratingFunctional LatticeClustering
open scoped RealInnerProductSpace

variable {m : ℝ}

/-! ## 4. And a graph where the property is not empty -/

/-- Sites `0` and `1` of `stepGraph` are in different components — the two paths have different
parities. -/
theorem not_reachable_zero_one : ¬ stepGraph.Reachable 0 1 := by
  intro h
  have := stepGraph_reachable_parity h
  simp at this

/-- Sites `0` and `2` are joined by an edge. -/
theorem reachable_zero_two : stepGraph.Reachable 0 2 :=
  SimpleGraph.Adj.reachable (by decide : stepGraph.Adj 0 2)

/-- **THE INSTANCE.** Across the barrier: independent. -/
theorem indepFun_step_zero_one (hm : m ≠ 0) :
    IndepFun (fun ω : EuclideanSpace ℝ (Fin 6) => ω 0) (fun ω => ω 1)
      (gaussianField stepGraph m) :=
  indepFun_eval_of_not_reachable hm not_reachable_zero_one

/-- **AND THE BARRIER IS NECESSARY.** Within one component, on the same graph and at the same mass:
not independent. -/
theorem not_indepFun_step_zero_two (hm : m ≠ 0) :
    ¬ IndepFun (fun ω : EuclideanSpace ℝ (Fin 6) => ω 0) (fun ω => ω 2)
      (gaussianField stepGraph m) :=
  fun h => (indepFun_eval_iff_not_reachable hm 0 2).mp h reachable_zero_two

/-- Neither observable is constant. -/
theorem variance_eval_pos (hm : m ≠ 0) (p : Fin 6) :
    0 < Var[fun ω : EuclideanSpace ℝ (Fin 6) => ω p; gaussianField stepGraph m] := by
  rw [variance_eval hm]
  exact green_diag_pos stepGraph hm p

/-- **`ClusteringFinVol` HAS A NON-DEGENERATE INSTANCE.** -/
theorem exists_nondegenerate_clustering (hm : m ≠ 0) :
    ∃ (p : Fin 6) (f g : EuclideanSpace ℝ (Fin 6)),
      f ≠ 0 ∧ g ≠ 0
        ∧ (∀ v, ¬ stepGraph.Reachable p v → f v = 0)
        ∧ (∀ v, stepGraph.Reachable p v → g v = 0)
        ∧ 0 < Var[⇑(pair f); gaussianField stepGraph m]
        ∧ 0 < Var[⇑(pair g); gaussianField stepGraph m]
        ∧ IndepFun (⇑(pair f)) (⇑(pair g)) (gaussianField stepGraph m) := by
  refine ⟨0, siteDelta 0, siteDelta 1, siteDelta_ne_zero 0, siteDelta_ne_zero 1,
    siteDelta_supported_off 0, siteDelta_supported_on not_reachable_zero_one, ?_, ?_, ?_⟩
  · rw [pair_siteDelta]; exact variance_eval_pos hm 0
  · rw [pair_siteDelta]; exact variance_eval_pos hm 1
  · rw [pair_siteDelta, pair_siteDelta]; exact indepFun_step_zero_one hm

end ClusteringWitness
