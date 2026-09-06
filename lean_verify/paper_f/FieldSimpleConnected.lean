import FieldSimpleConverse
import TorusDecay
import FieldTorusRotation

/-!
# The first necessary condition on the graph: it must be connected — and connectivity is not enough

`FieldSimpleConverse` made four conditions one condition: *every eigenspace of the graph's
Laplacian is at most a line* ⟺ *every eigenspace of `massive` is* ⟺ *the propagator's spectrum is
simple* ⟺ *the Laplacian's spectrum is simple*. It closed by saying plainly what it had **not**
done: **none of the four is shown equal to a property of the graph one could check by looking at
it**, and the path graph and the edgeless graphs remained the only families placed on either side.

This file puts a **graph-theoretic** condition on the list, on the necessary side, and then shows
that condition is not the answer.

## What is proved

**`finrank_ker_lapMatrix_zero_eq_card_component`** — the eigenspace at `0` has dimension equal to
the number of connected components. **This is Mathlib's theorem**
(`SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`) reshaped into the
`ker (L - ν • id)` form the chain is stated in; no mathematics is added and none is claimed.

**`preconnected_of_finrank_le_one`, `connected_of_finrank_le_one`** — **so the hypothesis the whole
symmetry chain runs on forces the graph to be connected.** One eigenvalue does all the work: at
`ν = 0` the bound says the component count is at most one. The `Connected` form needs `Nonempty V`
and the `Preconnected` form needs nothing.

**`preconnected_of_eigenvalues_injective`, `not_eigenvalues_injective_of_not_preconnected`** — **so
a simple propagator spectrum forces the graph to be connected**, at every non-zero mass, and a
disconnected graph has a degenerate propagator spectrum. This is the first statement in this chain
where a property of the **measure** forces a property of the **graph**.

**`not_preconnected_of_no_adj`** — and `FieldSimpleConverse.not_eigenvalues_injective_of_no_adj`,
written an hour ago, **is this statement at one family**: no edges plus two or more vertices is
exactly a failure of connectivity. The older theorem is kept and not deleted (`ERRATUM 94`).

**`not_finrank_massive_le_one_torus`, `not_finrank_lapMatrix_le_one_torus`, `torus_connected`,
`not_eigenvalues_injective_torus`** — **and connectivity is NOT SUFFICIENT, on the graphs the OS
programme is about.** Every periodic lattice of dimension `d ≥ 1` and side `≥ 3` is connected
(`TorusDecay.torusGraph_connected`) and, at the all-ones frequency, has an eigenspace of dimension
at least two (`FieldTorusRotation.two_le_finrank_eigenspace_torus`) at **every** mass — so it fails
the hypothesis in the massive form, in the Laplacian form (`ker_massive_eq` at `m = 0`, exactly as
in `FieldLaplacianInstance.finrank_lapMatrix_le_one_line`) and in the spectral form. **This is a
family in every dimension, not an example**, and at `d = 1` it is the cycle.

## What is NOT here

**STILL NO CHARACTERISATION, AND THIS FILE DOES NOT CLAIM TO NARROW ONE INTO EXISTENCE.**
Connectivity is **necessary and not sufficient**, which is exactly the shape of a condition that
is *not* the answer. The standing `UNLOCK_WATCHLIST` question is unchanged and the path graph is
still the only graph shown to satisfy the hypothesis.

**THE TORUS EIGENSPACE BOUND IS NOT COMPUTED HERE AND THE COMPUTATION IS NOT NEW.**
`FieldTorusRotation.two_le_finrank_eigenspace_torus` did it, and that file already built a rotation
of the field out of it. **What is new is the direction**: turning a two-dimensional eigenspace into
*the propagator's spectrum is degenerate* is the contrapositive of
`FieldSimpleConverse.finrank_massive_le_one_of_eigenvalues_injective`, which did not exist until an
hour ago. The eigenspace fact is old; the spectral sentence is new.

**AND §4 WAS WRITTEN TWICE.** The first version proved this for the **cycle** and defined its own
`oneFreq`; `newnames_scan` flagged the name against `FieldTorusRotation.oneFreq`, which is the same
definition with the dimension free, beside a theorem giving the eigenspace bound on **every**
torus. The specialised version was deleted and this one put in its place (`ERRATUM 465`: chase the
collision, and compare what the two declarations assume before choosing).

**NO SUFFICIENT CONDITION OF ANY KIND.** Nothing here says which connected graphs work. Two
families are now on the failing side — disconnected graphs and periodic lattices — and one graph
on the satisfying side, and **no claim is made that these exhaust anything**, nor that the two
failures
have a common cause, though a cycle's rotation and a disconnected graph's component swap are both
automorphisms of order greater than two, which `FieldSimpleAut.graphAut_involutive` forbids. **That
sentence is an observation and not a theorem**: no such implication is proved here.

**NOTHING ABOUT `FieldSymmetryEdgeless`'s DICHOTOMY.** That file's statement — the two symmetry
groups coincide iff the graph is edgeless — shares a family with this one and nothing else. **No
claim is made that they are two faces of one theorem.**

**NO LOWER BOUND ANYWHERE.** `finrank_ker_lapMatrix_zero_eq_card_component` is an equality, but
every other eigenspace statement here is an upper bound or its negation; no eigenspace is shown
non-trivial.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`). **A non-zero mass is taken by three of the
eleven** — `preconnected_of_eigenvalues_injective`,
`not_eigenvalues_injective_of_not_preconnected` and `not_eigenvalues_injective_torus` — and only
because `green` is defined as an inverse. `preconnected_of_finrank_le_one`,
`connected_of_finrank_le_one`, `not_finrank_lapMatrix_le_one_torus` and `torus_connected` take
**no mass at all**, and `not_finrank_massive_le_one_torus` takes the mass as a **free variable it
never constrains**, which is what lets `ker_massive_eq` be applied at `m = 0`. `Nonempty V` is
taken by `connected_of_finrank_le_one` alone, and `1 ≤ d` by the three torus statements that need
a degenerate eigenvalue — `torus_connected` holds at `d = 0` too, where the graph is a point.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSimpleConnected

open Matrix GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The eigenspace at zero counts the connected components -/

theorem finrank_ker_lapMatrix_zero_eq_card_component :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      = Fintype.card G.ConnectedComponent := by
  rw [zero_smul, sub_zero, ← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]

/-- **AND ON A CONNECTED GRAPH THAT EIGENSPACE IS EXACTLY A LINE.** An explicit multiplicity for an
explicit eigenvalue on every connected graph — added 2026-09-06 by `ERRATUM 469`, which is about
five later files claiming this estate had no such thing. -/
theorem finrank_ker_lapMatrix_zero_connected (hconn : G.Connected) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      = 1 := by
  classical
  haveI : Nonempty V := hconn.nonempty
  rw [finrank_ker_lapMatrix_zero_eq_card_component]
  refine Fintype.card_eq_one_iff.mpr ⟨G.connectedComponentMk (Classical.arbitrary V), ?_⟩
  refine SimpleGraph.ConnectedComponent.ind fun v => ?_
  exact SimpleGraph.ConnectedComponent.sound (hconn.preconnected v _)

/-! ## 2. So the Laplacian hypothesis forces the graph to be connected -/

theorem preconnected_of_finrank_le_one
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :
    G.Preconnected := by
  classical
  have hcard : Fintype.card G.ConnectedComponent ≤ 1 := by
    rw [← finrank_ker_lapMatrix_zero_eq_card_component]
    exact hdim 0
  have hsub : Subsingleton G.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp hcard
  intro u v
  exact SimpleGraph.ConnectedComponent.eq.mp (Subsingleton.elim _ _)

theorem connected_of_finrank_le_one [Nonempty V]
    (hdim : ∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :
    G.Connected :=
  SimpleGraph.Connected.mk (preconnected_of_finrank_le_one hdim)

/-! ## 3. So a simple propagator spectrum forces the graph to be connected -/

theorem preconnected_of_eigenvalues_injective (hm : m ≠ 0) (hH : (green G m).IsHermitian)
    (hsimple : Function.Injective hH.eigenvalues) : G.Preconnected :=
  preconnected_of_finrank_le_one
    (FieldSimpleConverse.finrank_lapMatrix_le_one_of_eigenvalues_injective hm hH hsimple)

theorem not_eigenvalues_injective_of_not_preconnected (hm : m ≠ 0)
    (hH : (green G m).IsHermitian) (h : ¬ G.Preconnected) :
    ¬ Function.Injective hH.eigenvalues := fun hsimple =>
  h (preconnected_of_eigenvalues_injective hm hH hsimple)

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **AND THE EDGELESS COROLLARY OF `FieldSimpleConverse` IS THIS ONE SPECIALISED.**
`FieldSimpleConverse.not_eigenvalues_injective_of_no_adj` takes *no edges* and *two or more
vertices*; those two together are exactly a failure of connectivity, so it is the
`¬ G.Preconnected` statement at one family. -/
theorem not_preconnected_of_no_adj (h : ∀ i j : V, ¬ G.Adj i j) (hcard : 2 ≤ Fintype.card V) :
    ¬ G.Preconnected := by
  have hbot : G = ⊥ := by
    ext u v
    exact ⟨fun huv => absurd huv (h u v), fun huv => huv.elim⟩
  subst hbot
  intro hpre
  obtain ⟨u, v, huv⟩ := Fintype.exists_pair_of_one_lt_card (α := V) (by omega)
  exact huv (SimpleGraph.reachable_bot.mp (hpre u v))

/-! ## 4. And connectivity is not sufficient: every periodic lattice, in every dimension -/

open BoxGraph TorusReflection MassiveTorusSpectrum FieldTorusRotation

theorem not_finrank_massive_le_one_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (mass : ℝ) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) mass) - ν • LinearMap.id)) ≤ 1) := by
  intro hdim
  have h2 := two_le_finrank_eigenspace_torus hd N mass
  have h1 := hdim (nuR N mass (oneFreq d N))
  omega

/-- **AND IT FAILS THE GRAPH-ONLY HYPOTHESIS TOO**, at no mass at all: `ker_massive_eq` at `m = 0`
is the whole step, exactly as in `FieldLaplacianInstance.finrank_lapMatrix_le_one_line`. -/
theorem not_finrank_lapMatrix_le_one_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((torusGraph d (N + 3)).lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) := by
  intro hdim
  refine not_finrank_massive_le_one_torus hd N 0 fun ν => ?_
  rw [FieldLaplacianSimple.ker_massive_eq]
  exact hdim _

theorem torus_connected (d N : ℕ) : (torusGraph d (N + 3)).Connected :=
  TorusDecay.torusGraph_connected (n := N + 3) d (by omega)

/-- **CONNECTIVITY IS NECESSARY AND NOT SUFFICIENT**: every periodic lattice of dimension at least
one is connected (`torus_connected`) and its propagator's spectrum is degenerate. **These are the
graphs the OS programme is about.** -/
theorem not_eigenvalues_injective_torus {d : ℕ} (hd : 1 ≤ d) (N : ℕ) {mass : ℝ} (hm : mass ≠ 0)
    (hH : (green (torusGraph d (N + 3)) mass).IsHermitian) :
    ¬ Function.Injective hH.eigenvalues := fun hsimple =>
  not_finrank_massive_le_one_torus hd N mass
    (FieldSimpleConverse.finrank_massive_le_one_of_eigenvalues_injective hm hH hsimple)

end FieldSimpleConnected
