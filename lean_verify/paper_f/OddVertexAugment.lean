import CycleDecomposition

/-!
# Every finite graph is one vertex away from having all degrees even

`CycleDecomposition.evenDegrees_iff_exists_cycle_decomposition` is this estate's Euler theorem:
a finite graph's edges are an edge-disjoint union of cycles **exactly when every degree is even**.
That hypothesis is the whole restriction, and it is the one the Peierls chain keeps running into:
`ExtendedDual.not_evenDegrees_extDual` exhibits a configuration whose extended dual has two
vertices of degree **one**, so the decomposition does not apply to it, and both `ExtendedDual`
and `WALLS.md` §W3 record that what the picture wants there — circuits **plus paths between the
odd vertices** — exists neither in this estate nor in Mathlib. **That second half is checked
here and not inherited** (`ERRATUM 458`): Mathlib's `Combinatorics/SimpleGraph/Trails.lean`
proves only the **necessary** direction — `IsEulerian.card_odd_degree`, that an Eulerian trail
forces at most two odd vertices — and its own module to-do list reads *"Prove that there exists
an Eulerian trail when the conclusion to `card_odd_degree` holds"*. **The converse is an open
item in Mathlib, in writing, as of 2026-09-06.**

**This file removes the hypothesis, in the only direction it can be removed: by changing the
graph.**

## What is proved

**`augment`** — adjoin **one** vertex to `G`, joined to exactly the vertices of odd degree. In
`V ⊕ Unit`, so no parallel edge is ever needed and simplicity is free; this is the standard device,
and the reason it is a single vertex rather than a pairing of the odd vertices is that a pairing can
ask for an edge the graph already has.

**`degree_inl`, `degree_inr`** — the two degrees, exactly: an old vertex gains `1` if its degree was
odd and nothing otherwise, and the new vertex's degree is the **number of odd-degree vertices**.

**`evenDegrees_augment`** — **so every degree of `augment G` is even, for every finite `G`, with no
hypothesis at all.** The old vertices by parity, the new one by Mathlib's handshaking lemma
`SimpleGraph.even_card_odd_degree_vertices`, which is exactly the fact that makes this work and is
the reason one vertex suffices.

**`exists_cycle_decomposition_augment`** — **hence every finite graph's edges, together with that
one star, are an edge-disjoint union of cycles.** The estate's Euler theorem, with its hypothesis
paid for rather than assumed.

**`isolated_inr_of_even`, `augment_eq_of_even`** — and when `G` already has all degrees even the new
vertex is **isolated**, so the construction adds a spare point and nothing else. The even case is
recovered exactly, which is what says the device is not doing something to it.

## What is NOT here

**THIS IS NOT THE EULER DECOMPOSITION WITH ODD VERTICES, AND IT IS FURTHER FROM IT THAN IT LOOKS.**
What is produced is a decomposition of `augment G`, whose cycles run **through the new vertex**.
Cutting them there to get **paths in `G`** between odd vertices is **not done**: the list returned
is a list of subgraphs of `V ⊕ Unit`, and **no statement here transports anything back along
`Sum.inl`**. That transport is the actual content of the classical theorem, and it is **not
attempted, no cost claimed** (`ERRATUM 246`).

**⚠ THE TRANSPORT WAS ATTEMPTED AND DONE THE SAME DAY, IN FIVE FILES THAT IMPORT THIS ONE.
Annotated 6 September 2026** (`ERRATUM 478`). The paragraph above is kept unedited: *"no statement
**here** transports anything back along `Sum.inl`"* is still true of this file, and the geometry it
describes is still the right description. **The closing clause is not.**
`paper_f/CycleRestriction.lean` — which imports this file — defines `leftPart` as
`SimpleGraph.comap Sum.inl` and is the transport; `LeftPartWalk`, `CyclePathExtract` and
`LeftPartPathGraph` carry walks, paths and edges across it; and
**`LeftPartDecomposition.exists_path_cycle_decomposition`** is the classical theorem itself —
*every finite graph's edges are an edge-disjoint union of paths and cycles*. All five were
committed on **2026-09-06**, the same day as this file. Nothing above is wrong as mathematics; the
sentence about what was attempted was overtaken within hours and left standing, which is the defect
`ERRATUM 471` exists for. **What is still not proved is the count and the endpoint identification**
— *paths between the odd vertices*, with a count — and `ERRATUM 97`'s point below is untouched.

**W3 DOES NOT MOVE, AND THIS FILE SUPPLIES LESS THAN THE THEOREM THAT WOULD NOT MOVE IT EITHER.**
`ExtendedDual`'s header records (`ERRATUM 97`) that a decomposition into circuits and paths **would
not by itself give** `S3b-ii`'s covering, because it does not say which piece the plaquette at `x`
lies on. What is proved here is one step **before** that insufficient theorem. **No claim is made
that the Peierls chain gains anything**, and none should be read.

**THIS IS NOT `ExtendedDual`'s CONSTRUCTION.** That adjoins **four** vertices to a **specific**
dual graph, indexed by direction, and its rim degrees are the ones that fail to be even. This
adjoins **one** vertex to an **arbitrary** finite graph and says nothing about plaquettes, rims or
configurations. **The two are not compared and no theorem relates them.**

**NOTHING IS SAID ABOUT CONNECTIVITY.** `augment G` may be disconnected, the new vertex is isolated
exactly when `G` has all even degrees, and **no Eulerian circuit is produced** — the estate's
decomposition is into a list of cycles, not a single closed trail, and that distinction is
`CycleDecomposition`'s and not this file's.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `Fintype V` and `DecidableRel G.Adj`
throughout, because degrees are counted, and **`DecidableEq V` is not among them** — the linter
reported it unused on every declaration and it came off, which is a small generalisation and is
recorded because it was not noticed when the file was written. **No connectivity, no bound on the
degree, and no hypothesis whatever on `G`** beyond finiteness. `evenDegrees_augment` in particular
takes **nothing about `G`**, which is the point of it.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace OddVertexAugment

open Finset

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The odd vertices, and the one extra point -/

/-- The vertices of odd degree. -/
def oddSet : Finset V := Finset.univ.filter fun v => Odd (G.degree v)

/-- **THE NUMBER OF ODD-DEGREE VERTICES IS EVEN** — Mathlib's handshaking lemma, in this file's
vocabulary. It is the whole reason **one** extra vertex is enough. -/
theorem even_card_oddSet : Even (oddSet G).card :=
  G.even_card_odd_degree_vertices

/-- **`G` WITH ONE EXTRA VERTEX, JOINED TO EXACTLY THE ODD-DEGREE VERTICES.** -/
def augment : SimpleGraph (V ⊕ Unit) where
  Adj x y :=
    match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inl u, Sum.inr _ => Odd (G.degree u)
    | Sum.inr _, Sum.inl v => Odd (G.degree v)
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (u | u) (v | v) h
    · exact G.symm h
    · exact h
    · exact h
    · exact h
  loopless := ⟨by
    intro x hx
    cases x with
    | inl u => exact G.irrefl hx
    | inr t => exact hx⟩

instance : DecidableRel (augment G).Adj := fun x y =>
  match x, y with
  | Sum.inl u, Sum.inl v => inferInstanceAs (Decidable (G.Adj u v))
  | Sum.inl u, Sum.inr _ => inferInstanceAs (Decidable (Odd (G.degree u)))
  | Sum.inr _, Sum.inl v => inferInstanceAs (Decidable (Odd (G.degree v)))
  | Sum.inr _, Sum.inr _ => inferInstanceAs (Decidable False)

theorem adj_inl_inl (u v : V) : (augment G).Adj (Sum.inl u) (Sum.inl v) ↔ G.Adj u v := Iff.rfl

theorem adj_inl_inr (u : V) (t : Unit) :
    (augment G).Adj (Sum.inl u) (Sum.inr t) ↔ Odd (G.degree u) := Iff.rfl

theorem adj_inr_inl (t : Unit) (v : V) :
    (augment G).Adj (Sum.inr t) (Sum.inl v) ↔ Odd (G.degree v) := Iff.rfl

theorem not_adj_inr_inr (s t : Unit) : ¬ (augment G).Adj (Sum.inr s) (Sum.inr t) := id

/-! ## 2. The two degrees, exactly -/

/-- **AN OLD VERTEX GAINS ONE EXACTLY WHEN ITS DEGREE WAS ODD.** -/
theorem degree_inl (v : V) :
    (augment G).degree (Sum.inl v) = G.degree v + (if Odd (G.degree v) then 1 else 0) := by
  have h1 : ∑ u : V, (if (augment G).Adj (Sum.inl v) (Sum.inl u) then 1 else 0)
      = G.degree v := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter]
    exact Finset.sum_congr rfl fun u _ => by simp [adj_inl_inl]
  have h2 : ∑ _t : Unit, (if (augment G).Adj (Sum.inl v) (Sum.inr _t) then 1 else 0)
      = (if Odd (G.degree v) then 1 else 0) := by simp [adj_inl_inr]
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type, h1, h2]

/-- **AND THE NEW VERTEX'S DEGREE IS THE NUMBER OF ODD-DEGREE VERTICES.** -/
theorem degree_inr (t : Unit) : (augment G).degree (Sum.inr t) = (oddSet G).card := by
  have hcard : (oddSet G).card = ∑ u : V, (if Odd (G.degree u) then 1 else 0) :=
    Finset.card_filter _ _
  have h2 : ∑ _s : Unit, (if (augment G).Adj (Sum.inr t) (Sum.inr _s) then 1 else 0) = 0 := by
    simp
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter,
    Fintype.sum_sum_type, hcard, h2, add_zero]
  exact Finset.sum_congr rfl fun u _ => by simp [adj_inr_inl]

/-! ## 3. So every degree is even, with no hypothesis on `G` -/

theorem even_degree_inl (v : V) : Even ((augment G).degree (Sum.inl v)) := by
  rw [degree_inl]
  by_cases h : Odd (G.degree v)
  · rw [if_pos h]
    exact Odd.add_one h
  · rw [if_neg h, add_zero]
    exact Nat.not_odd_iff_even.mp h

theorem even_degree_inr (t : Unit) : Even ((augment G).degree (Sum.inr t)) := by
  rw [degree_inr]
  exact even_card_oddSet G

/-- **EVERY DEGREE OF `augment G` IS EVEN, FOR EVERY FINITE `G`, WITH NO HYPOTHESIS AT ALL.** -/
theorem evenDegrees_augment : SimpleGraph.EvenDegrees (augment G) := by
  rw [SimpleGraph.evenDegrees_iff_forall_even_degree]
  rintro (v | t)
  · exact even_degree_inl G v
  · exact even_degree_inr G t

/-- **HENCE EVERY FINITE GRAPH'S EDGES, TOGETHER WITH THAT ONE STAR, ARE AN EDGE-DISJOINT UNION OF
CYCLES.** The estate's Euler theorem with its hypothesis paid for rather than assumed. -/
theorem exists_cycle_decomposition_augment :
    ∃ L : List (SimpleGraph (V ⊕ Unit)), (∀ H ∈ L, SimpleGraph.IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ L.foldr (· ⊔ ·) ⊥ = augment G :=
  (SimpleGraph.evenDegrees_iff_exists_cycle_decomposition _).mp (evenDegrees_augment G)

/-! ## 4. And on a graph that was already even, the new vertex is isolated -/

theorem isolated_inr_of_even (h : ∀ v, Even (G.degree v)) (t : Unit) (v : V) :
    ¬ (augment G).Adj (Sum.inr t) (Sum.inl v) := by
  rw [adj_inr_inl]
  exact Nat.not_odd_iff_even.mpr (h v)

/-- **SO ON AN EVEN GRAPH THE CONSTRUCTION ADDS A SPARE POINT AND NOTHING ELSE**: the new
vertex has degree zero. -/
theorem augment_eq_of_even (h : ∀ v, Even (G.degree v)) (t : Unit) :
    (augment G).degree (Sum.inr t) = 0 := by
  rw [degree_inr]
  simp only [oddSet, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun {v} _ => Nat.not_odd_iff_even.mpr (h v)

end OddVertexAugment
