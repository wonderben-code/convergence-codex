import LaplacianMultiplicityBound

/-!
# Two fences of my own, closed by putting the twin lower bound against the new upper one

`TwinClassNotExact` proved a four-dimensional eigenspace on two disjoint triangles and fenced it:
*"`4 ≤ dim` is proved and **the dimension is not claimed to be four**, though it is."*
`LaplacianClassFamily` proved six on three triangles and fenced the same thing: *"whether the sum
over all classes is **sharp** is not addressed — on three triangles it happens to be … but that is
one graph and this file proves no such thing."* **Both are proved here**, by holding those lower
bounds against `LaplacianMultiplicityBound`'s upper one, which did not exist when either fence was
written.

## What is proved

**`eq_of_reachable`, `not_reachable_of_invariant`, `connectedComponentMk_ne`** — **a function
constant along edges is constant along reachability**, so an invariant separating two vertices puts
them in different components. **This estate takes `¬ G.Reachable p q` as a hypothesis in four places
and produces it nowhere**; this is how, in four lines of `Walk` induction, and it takes no
`Fintype`, no `DecidableEq` and no `DecidableRel`.

**`twoTriangles_comp`, `two_le_card_component_two`** and **`threeTriangles_comp`,
`three_le_card_component_three`** — the invariants (*which side of three*, and *which third*) and
the component counts they give.

**`finrank_twoTriangles_eq`** — **exactly four**, and **`finrank_threeTriangles_eq`** — **exactly
six**. The lower bounds are the twin machinery; the upper bounds are
`multiplicity + components ≤ |V|`, at `6 − 2` and `9 − 3`. **The two meet**, which is the whole
unit.

## What is NOT here

**NO GENERAL THEOREM ABOUT DISJOINT UNIONS OF COMPLETE GRAPHS.** The arithmetic that makes both
cases work is the same — `k` copies of `K_a` give `k(a−1)` from the twin classes and `ka − k` from
the bound, and those are equal — and **the general statement is not made**, because it needs a
family of graphs this estate does not construct: there is no disjoint-union operation on
`SimpleGraph` in use here, and no `K_a` beyond `⊤` on a `Fin`. Not attempted, no cost claimed
(`ERRATUM 246`).

**THE COMPONENT COUNTS ARE LOWER BOUNDS, NOT EQUALITIES.** `2 ≤` and `3 ≤` are what is proved and
all that is needed; **neither graph's component count is computed exactly**, though both are
obvious.

**NO OTHER EIGENVALUE.** Only the eigenvalue `3` is treated on either graph. The rest of both
spectra is untouched, and in particular **the kernel's dimension is not computed** for either.

**NOTHING ABOUT SHARPNESS IN GENERAL.** Two graphs where the twin bound is sharp does not say when
it is sharp. `TwinClassNotExact`'s finding — that the **one-class** bound is not sharp even for a
maximal class — is unaffected: what is sharp here is the sum over **all** classes, on these two
graphs.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **no statement takes a mass, a propagator
or a measure**. §1 takes no finiteness and no decidability at all — three `omit`s — and is about
walks; §§2–3 take nothing beyond the graph being the graph named.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace LaplacianTriangleUnion

open SimpleGraph Matrix GraphLaplacian

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. An invariant constant along edges separates components -/

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **A FUNCTION CONSTANT ALONG EDGES IS CONSTANT ALONG REACHABILITY.** The estate takes
`¬ G.Reachable p q` as a hypothesis in four places and produces it nowhere; this is how. -/
theorem eq_of_reachable {W : Type*} {f : V → W} (hf : ∀ u v, G.Adj u v → f u = f v)
    {p q : V} (h : G.Reachable p q) : f p = f q := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => rfl
  | cons hadj _ ih => exact (hf _ _ hadj).trans ih

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem not_reachable_of_invariant {W : Type*} {f : V → W} (hf : ∀ u v, G.Adj u v → f u = f v)
    {p q : V} (hne : f p ≠ f q) : ¬ G.Reachable p q :=
  fun h => hne (eq_of_reachable hf h)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem connectedComponentMk_ne {W : Type*} {f : V → W} (hf : ∀ u v, G.Adj u v → f u = f v)
    {p q : V} (hne : f p ≠ f q) :
    G.connectedComponentMk p ≠ G.connectedComponentMk q :=
  fun h => not_reachable_of_invariant hf hne (SimpleGraph.ConnectedComponent.exact h)

/-! ## 2. Two triangles: the eigenvalue three has multiplicity exactly four -/

theorem twoTriangles_comp (u v : Fin 6) (h : TwinClassNotExact.twoTriangles.Adj u v) :
    decide (u.val < 3) = decide (v.val < 3) := by
  revert h
  revert u v
  decide

theorem two_le_card_component_two :
    2 ≤ Fintype.card TwinClassNotExact.twoTriangles.ConnectedComponent := by
  refine Fintype.one_lt_card_iff_nontrivial.mpr
    ⟨⟨TwinClassNotExact.twoTriangles.connectedComponentMk 0,
      TwinClassNotExact.twoTriangles.connectedComponentMk 3, ?_⟩⟩
  exact connectedComponentMk_ne twoTriangles_comp (by decide)

/-- **THE EIGENSPACE `TwinClassNotExact` COULD ONLY BOUND BELOW IS EXACTLY FOUR-DIMENSIONAL.** -/
theorem finrank_twoTriangles_eq :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (TwinClassNotExact.twoTriangles.lapMatrix ℝ) - (3 : ℝ) • LinearMap.id))
      = 4 := by
  have hlow := LaplacianTwoClasses.four_le_finrank_twoTriangles
  have hup := LaplacianMultiplicityBound.finrank_add_card_component_le
    (G := TwinClassNotExact.twoTriangles) (ν := (3 : ℝ)) (by norm_num)
  have hcomp := two_le_card_component_two
  rw [Fintype.card_fin] at hup
  omega

/-! ## 3. Three triangles: exactly six -/

theorem threeTriangles_comp (u v : Fin 9) (h : LaplacianClassFamily.threeTriangles.Adj u v) :
    u.val / 3 = v.val / 3 := by
  revert h
  revert u v
  decide

theorem three_le_card_component_three :
    3 ≤ Fintype.card LaplacianClassFamily.threeTriangles.ConnectedComponent := by
  classical
  have hinj : Function.Injective
      (![LaplacianClassFamily.threeTriangles.connectedComponentMk 0,
         LaplacianClassFamily.threeTriangles.connectedComponentMk 3,
         LaplacianClassFamily.threeTriangles.connectedComponentMk 6] :
        Fin 3 → LaplacianClassFamily.threeTriangles.ConnectedComponent) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | rfl
        | exact absurd hab (connectedComponentMk_ne threeTriangles_comp (by decide))
  have h := Fintype.card_le_of_injective _ hinj
  simpa using h

/-- **AND THE SUM THAT `LaplacianClassFamily` COULD ONLY BOUND BELOW IS EXACTLY SIX.** -/
theorem finrank_threeTriangles_eq :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (LaplacianClassFamily.threeTriangles.lapMatrix ℝ) - (3 : ℝ) • LinearMap.id))
      = 6 := by
  have hlow := LaplacianClassFamily.six_le_finrank_threeTriangles
  have hup := LaplacianMultiplicityBound.finrank_add_card_component_le
    (G := LaplacianClassFamily.threeTriangles) (ν := (3 : ℝ)) (by norm_num)
  have hcomp := three_le_card_component_three
  rw [Fintype.card_fin] at hup
  omega

end LaplacianTriangleUnion
