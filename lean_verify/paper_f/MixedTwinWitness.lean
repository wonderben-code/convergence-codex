import LaplacianClosedTwins

/-!
# A graph for the mixed-pair theorem, so that it is about something

`LaplacianClosedTwins` proved that **one open twin pair and one closed twin pair, the closed one a
degree lower**, put two independent eigenvectors at one eigenvalue. It then said plainly that the
hypothesis had **no instance anywhere in this estate**, and filed that as an open item rather than
leaving a theorem about nothing. The item is one graph old.

## What is proved

**`mixedGraph`** — seven vertices: a triangle `0–1–2`, and `3, 4` each joined to `2`, `5` and `6`.
**`mixedGraph_connected`** — it is connected, by explicit reachability from `2`.

**`open_pair`** — `3` and `4` have the same **open** neighbourhood, `{2, 5, 6}`, at degree three.
**`closed_pair`** — `0` and `1` have the same **closed** neighbourhood, `{0, 1, 2}`, at degree two.
**`degree_step`** — and two plus one is three, which is what the mixed theorem asks.

**`two_le_finrank_mixed`, `not_injective_lapMatrix_eigenvalues`** — **so the mixed theorem applies,
to a connected graph**, and this graph's Laplacian has a repeated eigenvalue at `3`.

## What is NOT here

**THE OTHER TWO THEOREMS DO NOT APPLY HERE, AND THAT IS THE POINT OF THIS PARTICULAR GRAPH.**
`5` and `6` are also open twins, so a reader might expect
`LaplacianTwins.two_le_finrank_of_twin_pairs` to fire — it does not, because that theorem needs the
two pairs at the **same** degree and `mixedGraph_degrees` gives `3` and `2`. There is only one
closed pair, so `LaplacianClosedTwins.two_le_finrank_of_closed_pairs` has nothing to work with
either. **This is read off `mixedGraph_degrees`, which is a theorem, rather than asserted.** It is
**not** proved that no other route reaches the same conclusion — a claim of that kind would be about
every argument, not about this graph.

**NO EIGENVALUE OTHER THAN `3` IS NAMED**, and its multiplicity is bounded below by two and not
computed. The rest of the spectrum of this graph is untouched.

**THE GRAPH IS NOT CLAIMED TO BE SMALLEST, CANONICAL OR INTERESTING.** It was drawn to satisfy the
hypothesis and nothing else. **A disconnected witness is much easier** — an isolated edge beside a
four-cycle does it — and the connected one is here because a disconnected graph fails the symmetry
chain's hypothesis for a reason already recorded, so a disconnected witness would settle the
inhabitation question while telling a reader nothing.

**THE OTHER OUTCOME THE ITEM ALLOWED FOR DOES NOT ARISE.** That item said the more interesting
result would be a proof that the two conditions **cannot** hold at once. They can, so there is
nothing to prove there, and the item closes rather than turning into a second question.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **nothing here takes a hypothesis at all**
beyond the graph being this graph — no mass, no propagator, no measure, and every fact about
`mixedGraph` is closed by `decide`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace MixedTwinWitness

open SimpleGraph Matrix GraphLaplacian LaplacianClosedTwins

/-! ## 1. The graph -/

/-- Adjacency of `mixedGraph`: a triangle `0–1–2`, and `3, 4` each joined to `2, 5, 6`. -/
def mixedAdj : Fin 7 → Fin 7 → Bool
  | 0, 1 | 1, 0 => true
  | 0, 2 | 2, 0 => true
  | 1, 2 | 2, 1 => true
  | 2, 3 | 3, 2 => true
  | 2, 4 | 4, 2 => true
  | 3, 5 | 5, 3 => true
  | 4, 5 | 5, 4 => true
  | 3, 6 | 6, 3 => true
  | 4, 6 | 6, 4 => true
  | _, _ => false

/-- **A CONNECTED GRAPH CARRYING BOTH KINDS OF TWIN PAIR, AT THE RIGHT DEGREES.** -/
def mixedGraph : SimpleGraph (Fin 7) where
  Adj u v := mixedAdj u v = true
  symm := by intro u v h; revert u v; decide
  loopless := ⟨by intro u h; revert u; decide⟩

instance : DecidableRel mixedGraph.Adj := fun u v =>
  inferInstanceAs (Decidable (mixedAdj u v = true))

theorem mixedGraph_degrees :
    ∀ v : Fin 7, mixedGraph.degree v = ![2, 2, 4, 3, 3, 2, 2] v := by decide

/-! ## 2. It is connected -/

theorem reach_two : ∀ v : Fin 7, mixedGraph.Reachable 2 v := by
  intro v
  fin_cases v
  · exact (by decide : mixedGraph.Adj 2 0).reachable
  · exact (by decide : mixedGraph.Adj 2 1).reachable
  · exact SimpleGraph.Reachable.refl 2
  · exact (by decide : mixedGraph.Adj 2 3).reachable
  · exact (by decide : mixedGraph.Adj 2 4).reachable
  · exact ((by decide : mixedGraph.Adj 2 3).reachable).trans
      ((by decide : mixedGraph.Adj 3 5).reachable)
  · exact ((by decide : mixedGraph.Adj 2 3).reachable).trans
      ((by decide : mixedGraph.Adj 3 6).reachable)

theorem mixedGraph_connected : mixedGraph.Connected :=
  SimpleGraph.Connected.mk fun u v => ((reach_two u).symm).trans (reach_two v)

/-! ## 3. The two pairs -/

/-- `3` and `4` are **open** twins: neither joined to the other, both joined to `2, 5, 6`. -/
theorem open_pair : mixedGraph.neighborFinset 3 = mixedGraph.neighborFinset 4 := by decide

/-- `0` and `1` are **closed** twins: joined to each other and both to `2`. -/
theorem closed_pair :
    insert 0 (mixedGraph.neighborFinset 0) = insert 1 (mixedGraph.neighborFinset 1) := by decide

theorem degree_step : mixedGraph.degree 0 + 1 = mixedGraph.degree 3 := by decide

/-! ## 4. So the mixed theorem is about something -/

/-- **THE MIXED HYPOTHESIS IS INHABITED, AND BY A CONNECTED GRAPH.** -/
theorem two_le_finrank_mixed :
    2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (mixedGraph.lapMatrix ℝ) - (mixedGraph.degree 3 : ℝ) • LinearMap.id)) :=
  two_le_finrank_of_mixed_pairs (u := 3) (v := 4) (x := 0) (y := 1)
    (by decide) (by decide) open_pair closed_pair degree_step
    (by decide) (by decide) (by decide)

theorem not_injective_lapMatrix_eigenvalues :
    ¬ Function.Injective
      (FieldSimpleConverse.lapMatrix_isHermitian mixedGraph).eigenvalues :=
  not_injective_of_mixed_pairs (u := 3) (v := 4) (x := 0) (y := 1)
    (by decide) (by decide) open_pair closed_pair degree_step
    (by decide) (by decide) (by decide)

end MixedTwinWitness
