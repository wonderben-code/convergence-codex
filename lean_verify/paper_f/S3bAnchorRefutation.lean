/-
  S3bAnchorRefutation.lean — widening the anchor does not repair
  `ClusterReachesRim`, at any radius and under any notion of distance.

  WHY. `S3bRefutation` refutes `S3bResidue.ClusterReachesRim` and offers a
  repair *"either"* way: restrict to configurations *"whose cluster has a
  nonempty boundary near `x`"*, **or** weaken *"the plaquette at `x`"* to
  *"some plaquette within `L + 1` of `x`"*. `S3bLocalObstruction` then showed
  the first route at radius zero is close to vacuous, so a usable version of it
  needs a positive radius — which is the second route. **This file shows the
  second route does not work either, and by the refutation's OWN witness.**

  WHAT THIS FILE PROVES:
  1. **`not_reachable_rim_any`** — with every site down, **NO plaquette in the
     box reaches any rim vertex.** `S3bRefutation.not_reachable_rim` says this
     for the plaquette at `x`; the proof never used which plaquette it was, and
     the general statement is what settles the question below
     (`ERRATUM 201` — the original is now its instance).
  2. **`ClusterReachesRimNear`** — route (ii) as a `def`: some plaquette within
     `r` of `x`, in `PlaqLocal.Near`'s sense, reaches a rim.
  3. **`not_clusterReachesRimNear`** — **FALSE FOR EVERY `r`.** The all-down
     configuration satisfies the hypothesis at every site and, having no
     contour, leaves the extended dual graph edgeless, so nothing anywhere
     reaches a rim.

  WHAT THAT SETTLES.
  **The two repair routes are not alternatives; neither is a repair on its
  own.** Route (i) at radius zero excludes almost every site
  (`S3bLocalObstruction`); route (ii) at any radius is refuted here. **A repair
  needs BOTH a hypothesis that excludes the no-contour case AND a positive
  radius**, and `S3bRefutation`'s *"either … or"* is the one word in that
  header that is wrong.

  **AND IT DISSOLVES THE `WHICH DISTANCE` QUESTION FOR NOW, RATHER THAN
  ANSWERING IT.** `UNLOCK_WATCHLIST`'s S3b block carries a DECISION NEEDED —
  explicitly *not* the author's — between `L^∞` distance to the boundary, the
  route map's `2 d(x)` perimeter form, and `PlaqLocal.Near`'s radius. (1) is
  quantified over **all** plaquettes, so it refutes every anchor set whatsoever,
  up to and including the whole box. **No choice among the three repairs
  anything**, so the choice is not yet well-posed: it becomes a real question
  only once a hypothesis is fixed that excludes the empty contour, and it should
  be made then, against that hypothesis. Choosing now would be `ERRATUM 89`
  exactly — settling a decision to tidy the list, before the thing it decides
  between exists.

  **WHAT THE DECISION WILL TURN ON WHEN IT IS LIVE, recorded because it was
  worked out here and would otherwise be lost.** The consumer is
  `DualPathCount.card_walksTo_bdry_le`: at most `4 n · 4 ^ L` dual walks of
  length `L` run **from one fixed plaquette** to the edge. So an anchor SET
  costs its own cardinality as a factor, and `PlaqLocal.card_ball_le` is the
  only one of the three candidates the estate can bound —
  `(ball P r).card ≤ (2r + 1) ^ 2`. With the radius tied to the walk length, as
  in the interior analogue `RayWalk.exists_circuit_near_of_down`, that factor is
  a function of `L` and sits inside the sum over `L`; tied to `d(x, ∂)` instead
  it is box-dependent and multiplies the whole sum. **That is an argument about
  shape and it is not a proof of anything**, which is why it is recorded here
  and not acted on.

  WHAT THIS IS NOT.
  **It is not a repair and does not attempt one.** It removes the second of the
  two candidate shapes. `WALLS` §W3 does not move, `S3bResidue.walk_to_bdry_of_gap`
  is untouched and remains a true implication from a false hypothesis, and
  `IsingBoundaryField` is untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import S3bLocalObstruction

namespace S3bAnchorRefutation

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette PlaquetteLattice
open IsingBoundaryField IsingContourSeparation
open DualObstruction DualGraph ExtendedDual FieldCover FieldBoundaryEnergy PeierlsCover
open S3bResidue S3bRefutation

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. With everything down, no plaquette anywhere reaches a rim

`S3bRefutation.not_reachable_rim` proves this for the plaquette at `x`. Its proof never used
which plaquette that was — the graph is empty — so the statement generalises for free, and the
general form is what rules out every anchor set at once. -/

/-- **NO PLAQUETTE IN THE BOX REACHES A RIM UNDER `allDown`.** -/
theorem not_reachable_rim_any (x : Site n) (P : Plaq n) (d : Fin 4) :
    ¬ (extDual (clusterOn (allDown n) x)).Reachable (Sum.inl P) (Sum.inr d) := by
  rw [extDual_allDown_eq_bot]
  have key : ∀ a b : ExtV n, (⊥ : SimpleGraph (ExtV n)).Walk a b → a = b := by
    intro a b w
    induction w with
    | nil => rfl
    | cons hadj _ => exact hadj.elim
  rintro ⟨w⟩
  exact absurd (key _ _ w) (by simp)

/-! ## 2. Route (ii), stated -/

/-- **THE ANCHOR-WIDENED SPECIFICATION**, `S3bRefutation`'s second repair route as a `def`:
some plaquette within `r` of the one at `x` reaches a rim of the cluster's extended dual graph.
At `r = 0` this is `S3bResidue.ClusterReachesRim` up to `PlaqLocal.Near.refl`.

**NOT PROVED, and §3 proves its negation** — it is written down so that the route can be
referred to and refuted by name rather than by description. -/
def ClusterReachesRimNear (n : ℕ) (r : ℕ) : Prop :=
  ∀ (σ : Config n) (x : Site n) (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n),
    σ x = false → ReachesBoundary σ x →
      ∃ (P : Plaq n) (d : Fin 4), P ∈ PlaqLocal.ball (plaqOf x hi hj) r ∧
        (extDual (clusterOn σ x)).Reachable (Sum.inl P) (Sum.inr d)

/-! ## 3. And refuted, at every radius -/

/-- **WIDENING THE ANCHOR DOES NOT REPAIR THE SPECIFICATION.** For every `r`, and by the same
witness that refuted the original: all sites down, so the hypothesis holds everywhere and the
conclusion fails everywhere, because an empty contour leaves nothing for any plaquette to walk
along — however many plaquettes are offered. -/
theorem not_clusterReachesRimNear (hn : 1 < n) (r : ℕ) : ¬ ClusterReachesRimNear n r := by
  intro h
  have h0 : (0 : ℕ) < n := by omega
  obtain ⟨P, d, -, hreach⟩ :=
    h (allDown n) (⟨0, h0⟩, ⟨0, h0⟩) (by simpa using hn) (by simpa using hn) rfl
      (reachesBoundary_allDown h0 _)
  exact not_reachable_rim_any _ P d hreach

/-- **AND THE ORIGINAL IS THE `r = 0` CASE** (`ERRATUM 201`: the generalisation is instantiated
back at the statement it generalises). -/
theorem not_clusterReachesRim_of_near (hn : 1 < n) : ¬ ClusterReachesRim n := by
  intro h
  refine not_clusterReachesRimNear hn 0 ?_
  intro σ x hi hj hx hb
  obtain ⟨d, hd⟩ := h σ x hi hj hx hb
  exact ⟨plaqOf x hi hj, d, by simp [PlaqLocal.Near.refl], hd⟩

end S3bAnchorRefutation
