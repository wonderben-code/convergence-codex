import FieldAutInvariance

/-!
# OS1 in finite volume: every Schwinger function is invariant under every graph automorphism

The `UNLOCK_WATCHLIST` item *"the OS axioms other than OS2, for the lattice field"* has one live
clause left. Clause (a), tightness, closed by proof on 23 August (`LatticeFieldTight`). Clause (b)
reads, verbatim:

> anything at all that makes **OS1** statable in finite volume.

**This file writes that statement down and proves the lattice field satisfies it.**

## First, a numbering that this estate does not use consistently — `ERRATUM 320`

`CascadeFoundation.OSVerification`, `F3_9d_ReflectionPositivity`, `F4_3f_OSReconstruction` and
`F4_4a_OSAxiomsCompact` all place **Euclidean covariance at OS1** and permutation symmetry at OS3.
`FieldAutInvariance`'s header instead says *"OS3 is invariance under the full Euclidean group
`E(d)`"* and delivers what it calls *"the finite-volume shadow of OS3"*, while also saying, of the
same theorem, *"it proves nothing about OS0, **OS1** or OS4"*. **Both sentences describe
`gaussianField_map_perm`, and under the estate's own majority numbering they contradict each
other.** The mathematics was never in question; only the label was. See `ERRATUM 320`.

This file uses the majority numbering — **OS1 = Euclidean covariance** — which is also the one the
watchlist clause is written in.

## What is proved

> **`schwinger_perm`** — for every graph automorphism `θ`, every order `k` and all sites
> `p : Fin k → V`,
>
>     ∫ ∏ i, ω (θ (p i)) ∂(gaussianField G m) = ∫ ∏ i, ω (p i) ∂(gaussianField G m)
>
> **at every order, not just the second.** `LatticeReflectionPositive.green_congr` and
> `GraphLaplacian.twoPoint` give the `k = 2` case between them; `schwinger_two` below checks the
> general statement against them rather than reproving either.
>
> **`gaussianField_euclideanCovariantFinVol`** — the same thing as a `Prop` that is stated once,
> `EuclideanCovariantFinVol`, so the axiom is a definition in this estate and not only a family of
> instances. That is what clause (b) asked for.

The proof is one change of variables. `FieldAutInvariance.gaussianField_map_perm` says the measure
is invariant; `MeasureTheory.integral_map` turns that into invariance of every integral; and
`permField θ ω p = ω (θ.symm p)` turns the integrand into the reindexed product. **The content is
the measure-level theorem, which already existed** — what is new is that it is read on the
Schwinger functions, which is the vocabulary the axiom is stated in.

## What this is NOT

**It is not OS1.** OS1 is covariance of the Schwinger functions of a *continuum* theory under the
Euclidean group `E(d)` — rotations, translations and reflections of `ℝ^d`. A finite graph has no
`E(d)`; what it has is `Aut(G)`, and on a box that is the reflections and coordinate permutations,
on a torus also the translations. **Invariance under `Aut(G)` is what OS1 degenerates to in finite
volume, and full Euclidean covariance is a continuum statement no finite-volume theorem reaches.**
This is the same care `FieldAutInvariance` took, and the same care is owed here.

**It does not enlarge the group.** Which automorphisms exist is a question about `G`, not about the
field; this file constructs none. `FieldAutInvariance.gaussianField_map_revSite` instantiates at
the box reflections and `TorusTranslation` at the torus translations, and nothing here adds to
that.

**It says nothing about OS0 or OS4**, and nothing about the infinite-volume limit. `W2`'s leg does
not move: identifying a limit measure as the `ℤ^d` free field needs `G_n(x,y) → G(x,y)`, which
`FieldTightness` named as where the analysis lives and which nothing here touches.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeOS1

open MeasureTheory FieldAutInvariance

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Automorphisms invert -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **THE INVERSE OF A GRAPH AUTOMORPHISM IS ONE.** `IsGraphAut` is adjacency preservation as a
biconditional, so this is a reindexing and not an argument. -/
theorem isGraphAut_symm {θ : V ≃ V} (hθ : IsGraphAut G θ) : IsGraphAut G θ.symm := by
  intro p q
  have h := hθ (θ.symm p) (θ.symm q)
  simpa using h.symm

/-! ## 2. The Schwinger functions -/

/-- The `k`-point Schwinger function of the lattice field at the sites `p`. -/
noncomputable def schwinger (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) {k : ℕ}
    (p : Fin k → V) : ℝ :=
  ∫ ω, (∏ i, ω (p i)) ∂(GraphLaplacian.gaussianField G m)

omit [Fintype V] [DecidableEq V] in
/-- The integrand is continuous, hence strongly measurable — the one side condition
`integral_map` needs. -/
theorem continuous_prod_eval {k : ℕ} (p : Fin k → V) :
    Continuous fun ω : EuclideanSpace ℝ V => ∏ i, ω (p i) :=
  continuous_finset_prod _ fun i _ => (EuclideanSpace.proj (p i)).continuous

/-! ## 3. Invariance -/

/-- **EVERY SCHWINGER FUNCTION IS INVARIANT UNDER EVERY GRAPH AUTOMORPHISM**, at every order.
One change of variables against `FieldAutInvariance.gaussianField_map_perm`. -/
theorem schwinger_perm {θ : V ≃ V} (hθ : IsGraphAut G θ) (hm : m ≠ 0) {k : ℕ} (p : Fin k → V) :
    schwinger G m (θ ∘ p) = schwinger G m p := by
  have hmap := gaussianField_map_perm (G := G) (m := m) (isGraphAut_symm hθ) hm
  have hmeas : AEMeasurable (permField θ.symm)
      (GraphLaplacian.gaussianField G m) :=
    (permField θ.symm).continuous.measurable.aemeasurable
  have hint : AEStronglyMeasurable (fun ω : EuclideanSpace ℝ V => ∏ i, ω (p i))
      ((GraphLaplacian.gaussianField G m).map (permField θ.symm)) :=
    (continuous_prod_eval p).aestronglyMeasurable
  have h := integral_map (μ := GraphLaplacian.gaussianField G m)
    (φ := permField θ.symm) (f := fun ω : EuclideanSpace ℝ V => ∏ i, ω (p i)) hmeas hint
  rw [hmap] at h
  simp only [permField_apply, Equiv.symm_symm] at h
  exact h.symm

/-- **OS1's finite-volume form, as a statement.** Clause (b) of the watchlist item asked for
*"anything at all that makes OS1 statable in finite volume"*; this is that thing, and
`gaussianField_euclideanCovariantFinVol` is the lattice field's instance of it. -/
def EuclideanCovariantFinVol (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Prop :=
  ∀ θ : V ≃ V, IsGraphAut G θ → ∀ {k : ℕ} (p : Fin k → V),
    schwinger G m (θ ∘ p) = schwinger G m p

/-- **THE LATTICE FIELD IS EUCLIDEAN-COVARIANT IN FINITE VOLUME.** -/
theorem gaussianField_euclideanCovariantFinVol (hm : m ≠ 0) :
    EuclideanCovariantFinVol G m :=
  fun _ hθ _ p => schwinger_perm hθ hm p

/-! ## 4. The second order, checked against what the estate already had -/

/-- **THE TWO-POINT CASE IS THE ESTATE'S TWO-POINT FUNCTION.** `GraphLaplacian.twoPoint` says
`∫ ω p · ω q = green G m p q`; this says the general definition agrees with it at `k = 2`, so
`schwinger_perm` at `k = 2` and `LatticeReflectionPositive.green_congr` are two readings of one
fact and neither is reproved here (`ERRATUM 313`). -/
theorem schwinger_two (hm : m ≠ 0) (p q : V) :
    schwinger G m ![p, q] = GraphLaplacian.green G m p q := by
  rw [← GraphLaplacian.twoPoint G hm p q]
  simp [schwinger, Fin.prod_univ_two]

end LatticeOS1
