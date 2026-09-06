import OddVertexAugment

/-!
# The `V`-part of the cycles, and the degree signature that says where the paths would end

`OddVertexAugment` adjoins one vertex to a finite graph, joined to exactly its odd-degree
vertices, and gets a cycle decomposition of the result. It fences the step that matters:
**nothing transports those cycles back along `Sum.inl`.** This file takes that step as far as it
goes **without touching a single walk**, and says exactly where the walks become unavoidable.

## What is proved

**`leftPart`** — the `V`-part of a graph on `V ⊕ Unit`, which is `SimpleGraph.comap Sum.inl`, with
`restrict_sup`, `restrict_inf`, `restrict_bot` and `disjoint_restrict`: it is a lattice
homomorphism on the parts that matter, and it preserves edge-disjointness. **`restrict_augment`** —
and it undoes the augmentation exactly: `leftPart (augment G) = G`.

**`exists_cycle_parts_decomposition`** — **so every finite graph's edges are the disjoint union of
the `V`-parts of cycles**, the cycles being the ones through the added vertex and around it. This
is the **edge-partition half** of the decomposition `WALLS.md` §W3 and `UNLOCK_WATCHLIST` call
residue (a), and it needs no walk at all: the join and the disjointness both come from `comap`
commuting with `⊔` and `⊓`. It takes **`Finite` and no decidability**, both being produced inside
the proof — the linter reported them unused in the statement and the generalisation was free.

**`degree_restrict`, `odd_degree_restrict_iff`, `odd_degree_restrict_cycle_iff`** — **and the
degree signature is exact: in the `V`-part of a cycle, a vertex has odd degree exactly when it was
joined to the added vertex.** Since the added vertex is joined to exactly the odd-degree vertices
of `G`, that is the statement *"the pieces' loose ends are the odd vertices"* — at the level of
degrees, which is the level at which it can be said without walks.

## What is NOT here

**THIS IS NOT THE CIRCUITS-PLUS-PATHS DECOMPOSITION, AND THE GAP IS PRECISELY ONE THING.** **No
piece is shown to be a path.** `leftPart H` is shown to have the degree signature of a path or a
cycle — two odd vertices or none — and **a degree signature is not a path**: a disjoint union of a
path and a cycle has it too, and so does a graph with a vertex of degree four. Producing an actual
walk requires moving a `Walk` in `V ⊕ Unit` whose support avoids `Sum.inr` into a `Walk` in `V`,
and **nothing here does that**. **Not attempted in this file, no cost claimed** (`ERRATUM 246`).

**W3 DOES NOT MOVE, AND WOULD NOT MOVE IF THIS WERE FINISHED.** `ExtendedDual` records
(`ERRATUM 97`) that the full circuits-plus-paths theorem is **necessary and not sufficient** for
`S3b-ii`'s covering, because it does not say which piece the plaquette at `x` lies on; residue (b),
the open-path analogue of the ray argument, is untouched here and everywhere. **No claim is made
that the Peierls chain gains anything.**

**NOTHING IS SAID ABOUT HOW MANY PIECES THERE ARE**, or about which odd vertices are paired with
which. The added vertex's degree is the number of odd vertices, and **no theorem here relates that
to the length of the list.**

**`leftPart` LOSES INFORMATION AND THAT IS NOT REPAIRED.** Two different graphs on `V ⊕ Unit` can
have the same `V`-part, and `leftPart` is not injective; the decomposition returned names the
`V`-parts and **the original cycles are not recoverable from them**, which is why
`exists_cycle_parts_decomposition` returns the list of cycles as well.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): §1's lattice lemmas take **no finiteness
and no decidability at all** — they are `comap` facts and hold for any `V`. Finiteness enters only
where degrees are counted and where `OddVertexAugment`'s decomposition is invoked.

**A NOTE ON THE NAME.** This operation was called `restrict` in draft, and `newnames_scan` found
the name taken twice — `FibrewiseStabiliser.restrict` and `PairingRestrict.restrict`. **Neither is
a shared object**: both restrict a **permutation** to a subtype via `Equiv.Perm.subtypePerm`, where
this restricts a **graph** along an inclusion. Four collisions earlier in this campaign did reveal a
shared object (`ERRATUM 465`); this one does not, and the answer is a name that says which
restriction it is rather than an accept-file entry.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace CycleRestriction

open OddVertexAugment

/-! ## 1. The `V`-part, and that it is a lattice map preserving disjointness -/

variable {V : Type*}

/-- The `V`-part of a graph on `V ⊕ Unit`. -/
def leftPart (H : SimpleGraph (V ⊕ Unit)) : SimpleGraph V := SimpleGraph.comap Sum.inl H

theorem restrict_adj (H : SimpleGraph (V ⊕ Unit)) (u v : V) :
    (leftPart H).Adj u v ↔ H.Adj (Sum.inl u) (Sum.inl v) := Iff.rfl

theorem restrict_sup (H K : SimpleGraph (V ⊕ Unit)) :
    leftPart (H ⊔ K) = leftPart H ⊔ leftPart K := rfl

theorem restrict_inf (H K : SimpleGraph (V ⊕ Unit)) :
    leftPart (H ⊓ K) = leftPart H ⊓ leftPart K := rfl

theorem restrict_bot : leftPart (⊥ : SimpleGraph (V ⊕ Unit)) = ⊥ := rfl

/-- **AND IT PRESERVES EDGE-DISJOINTNESS**, which is what the decomposition needs. -/
theorem disjoint_restrict {H K : SimpleGraph (V ⊕ Unit)} (h : Disjoint H K) :
    Disjoint (leftPart H) (leftPart K) := by
  rw [disjoint_iff] at h ⊢
  rw [← restrict_inf, h, restrict_bot]

theorem foldr_restrict (L : List (SimpleGraph (V ⊕ Unit))) :
    (L.map leftPart).foldr (· ⊔ ·) ⊥ = leftPart (L.foldr (· ⊔ ·) ⊥) := by
  induction L with
  | nil => exact restrict_bot.symm
  | cons H t ih => rw [List.map_cons, List.foldr_cons, List.foldr_cons, ih, restrict_sup]

/-! ## 2. It undoes the augmentation, so the pieces join to `G` -/

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem restrict_augment : leftPart (augment G) = G := by
  ext u v
  exact adj_inl_inl G u v

section Decomposition

variable {W : Type*} [Finite W]

/-- **EVERY FINITE GRAPH'S EDGES ARE THE DISJOINT UNION OF THE `V`-PARTS OF CYCLES.** The
edge-partition half of the circuits-plus-paths decomposition, with no walk moved. It takes
**`Finite` and no decidability at all** — both are produced inside the proof, which is where
`OddVertexAugment` needs them. -/
theorem exists_cycle_parts_decomposition (G : SimpleGraph W) :
    ∃ L : List (SimpleGraph (W ⊕ Unit)), (∀ H ∈ L, SimpleGraph.IsCycleGraph H) ∧
      L.Pairwise Disjoint ∧ (L.map leftPart).Pairwise Disjoint ∧
      (L.map leftPart).foldr (· ⊔ ·) ⊥ = G := by
  classical
  have : Fintype W := Fintype.ofFinite W
  obtain ⟨L, hcyc, hdisj, hjoin⟩ := exists_cycle_decomposition_augment G
  refine ⟨L, hcyc, hdisj, hdisj.map _ fun _ _ h => disjoint_restrict h, ?_⟩
  rw [foldr_restrict, hjoin, restrict_augment]

end Decomposition

/-! ## 3. The degree signature: the loose ends are exactly the odd vertices -/

instance instDecidableRestrict (H : SimpleGraph (V ⊕ Unit)) [DecidableRel H.Adj] :
    DecidableRel (leftPart H).Adj :=
  fun u v => inferInstanceAs (Decidable (H.Adj (Sum.inl u) (Sum.inl v)))

/-- **RESTRICTING DROPS EXACTLY THE EDGE TO THE ADDED VERTEX, WHEN THERE IS ONE.** -/
theorem degree_restrict (H : SimpleGraph (V ⊕ Unit)) [DecidableRel H.Adj] (v : V) :
    (leftPart H).degree v + (if H.Adj (Sum.inl v) (Sum.inr ()) then 1 else 0)
      = H.degree (Sum.inl v) := by
  have h1 : ∑ u : V, (if H.Adj (Sum.inl v) (Sum.inl u) then 1 else 0)
      = (leftPart H).degree v := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter]
    exact (Finset.sum_congr rfl fun u _ => by simp [restrict_adj]).symm
  have h2 : ∑ _t : Unit, (if H.Adj (Sum.inl v) (Sum.inr _t) then 1 else 0)
      = (if H.Adj (Sum.inl v) (Sum.inr ()) then 1 else 0) := Fintype.sum_unique _
  have h3 : H.degree (Sum.inl v)
      = (∑ u : V, (if H.Adj (Sum.inl v) (Sum.inl u) then 1 else 0))
        + ∑ _t : Unit, (if H.Adj (Sum.inl v) (Sum.inr _t) then 1 else 0) := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter,
      Fintype.sum_sum_type]
  rw [h3, h1, h2]

/-- **SO WHERE THE WHOLE DEGREE IS EVEN, THE PART'S DEGREE IS ODD EXACTLY AT THE ADDED VERTEX'S
NEIGHBOURS.** -/
theorem odd_degree_restrict_iff (H : SimpleGraph (V ⊕ Unit)) [DecidableRel H.Adj] {v : V}
    (h : Even (H.degree (Sum.inl v))) :
    Odd ((leftPart H).degree v) ↔ H.Adj (Sum.inl v) (Sum.inr ()) := by
  rw [← degree_restrict H v] at h
  by_cases hadj : H.Adj (Sum.inl v) (Sum.inr ())
  · rw [if_pos hadj] at h
    simp only [hadj, iff_true]
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp h)
  · rw [if_neg hadj, add_zero] at h
    simp only [hadj, iff_false]
    exact Nat.not_odd_iff_even.mpr h

/-- **AND ON A CYCLE THAT IS UNCONDITIONAL**, since a cycle graph has every degree even. -/
theorem odd_degree_restrict_cycle_iff (H : SimpleGraph (V ⊕ Unit))
    [DecidableRel H.Adj] (hH : SimpleGraph.IsCycleGraph H) (v : V) :
    Odd ((leftPart H).degree v) ↔ H.Adj (Sum.inl v) (Sum.inr ()) :=
  odd_degree_restrict_iff H
    ((SimpleGraph.evenDegrees_iff_forall_even_degree H).mp hH.evenDegrees _)

/-! ## 4. So the pieces carry the degree signature of a path or a cycle -/

/-- **A CYCLE GRAPH HAS EVERY DEGREE AT MOST TWO** — `2` on its support and `0` off it. The
companion of `CycleDecomposition.even_ncard_neighborSet_cycle`, which this estate had only in the
evenness form. -/
theorem degree_le_two_of_isCycleGraph {H : SimpleGraph V} [DecidableRel H.Adj]
    (hH : SimpleGraph.IsCycleGraph H) (x : V) : H.degree x ≤ 2 := by
  obtain ⟨u, p, hp, hEq⟩ := hH
  rw [SimpleGraph.degree_eq_ncard_neighborSet]
  by_cases hx : x ∈ p.support
  · rw [← hEq, SimpleGraph.ncard_neighborSet_cycle_of_mem hp hx]
  · rw [← hEq, SimpleGraph.neighborSet_spanningCoe_toSubgraph_eq_empty p hx, Set.ncard_empty]
    omega

/-- **THE ODD-DEGREE VERTICES OF THE PART ARE EXACTLY THE ADDED VERTEX'S NEIGHBOURS, AND THERE ARE
AS MANY OF THEM AS IT HAS.** -/
theorem card_odd_restrict_eq_degree_inr (H : SimpleGraph (V ⊕ Unit))
    [DecidableRel H.Adj] (hH : SimpleGraph.IsCycleGraph H) :
    (Finset.univ.filter fun v : V => Odd ((leftPart H).degree v)).card
      = H.degree (Sum.inr ()) := by
  classical
  have hR : H.degree (Sum.inr ())
      = (∑ u : V, (if H.Adj (Sum.inr ()) (Sum.inl u) then 1 else 0))
        + ∑ _t : Unit, (if H.Adj (Sum.inr ()) (Sum.inr _t) then 1 else 0) := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_filter,
      Fintype.sum_sum_type]
  have h2 : ∑ _t : Unit, (if H.Adj (Sum.inr ()) (Sum.inr _t) then 1 else 0) = 0 := by simp
  rw [hR, h2, add_zero, Finset.card_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : H.Adj (Sum.inl v) (Sum.inr ())
  · rw [if_pos ((odd_degree_restrict_cycle_iff H hH v).mpr hv), if_pos hv.symm]
  · rw [if_neg (fun hodd => hv ((odd_degree_restrict_cycle_iff H hH v).mp hodd)),
      if_neg (fun hcon => hv hcon.symm)]

/-- **SO EVERY PIECE HAS EITHER NO ODD VERTEX OR EXACTLY TWO** — the degree signature of a cycle or
of a path, which is as far as degrees can take this. **It is not a path**: a disjoint union of a
path and a cycle has the same signature, and no walk is produced anywhere in this file. -/
theorem card_odd_restrict_le_two (H : SimpleGraph (V ⊕ Unit))
    [DecidableRel H.Adj] (hH : SimpleGraph.IsCycleGraph H) :
    (Finset.univ.filter fun v : V => Odd ((leftPart H).degree v)).card = 0 ∨
      (Finset.univ.filter fun v : V => Odd ((leftPart H).degree v)).card = 2 := by
  have hle : (Finset.univ.filter fun v : V => Odd ((leftPart H).degree v)).card ≤ 2 := by
    rw [card_odd_restrict_eq_degree_inr H hH]
    exact degree_le_two_of_isCycleGraph hH _
  have heven : Even (Finset.univ.filter fun v : V => Odd ((leftPart H).degree v)).card := by
    rw [card_odd_restrict_eq_degree_inr H hH]
    exact (SimpleGraph.evenDegrees_iff_forall_even_degree H).mp hH.evenDegrees _
  rcases heven with ⟨k, hk⟩
  omega

end CycleRestriction
