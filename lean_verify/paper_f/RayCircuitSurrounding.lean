import RayBondsParity

/-!
# The enclosure step, off `+`: some piece of the dual graph is crossed oddly by the ray

`RayBondsParity` proved that along a ray in any row above the bottom, the dual graph's bond set is
crossed an odd number of times **exactly when the ray's two ends disagree** — for every
configuration, with no boundary condition. That is the input `DualUnique`'s enclosure step has
always had to obtain from `PlusBoundary`. This file feeds it in.

## What is proved

**`odd_count_circuits_leftRay_iff`** — `DualUnique.odd_count_circuits_iff_down`'s statement along a
ray, **with the boundary condition removed**. For any pairwise-disjoint decomposition of the dual
graph, the number of pieces crossed oddly by the ray is odd **exactly when the ray's two ends carry
different spins**. The conclusion is not word-for-word that theorem's: its walk ends at the corner
and its right-hand side is `σ x = false`, which is what `PlusBoundary` turns *the ends disagree*
into.
Every ingredient — `bonds_foldr`, `pairwise_disjoint_bonds`,
`SurroundsParity.even_countP_odd_pieces_iff` — was already free of `PlusBoundary`; the hypothesis
entered that theorem only through the crossing count, and `RayBondsParity` supplies that.

**`exists_odd_path_or_cycle_piece_leftRay`** — **and with no hypothesis on `σ` at all**, beyond the
ray's two endpoint spins, some piece of the dual graph is crossed oddly and is the edge set of a
**single path or a single cycle**. This is `OddPieceSelect.exists_odd_path_or_cycle_piece`
composed with the ray theorem, and it is the first time that theorem has been given an odd count
that costs nothing. **Counted, not remembered** (`ERRATUM 477`): five theorems in `paper_f`
conclude `¬ Even (crossings (bonds σ (dualGraph σ)) w)`, and four of them ask something of `σ` —
`PlusBoundary` in `DualBonds.odd_crossings_bonds_of_down`, `NoBrokenOutward` in
`BondsContourCriterion.odd_crossings_bonds_of_down_of_no_outward` and in
`BondsDeficit.odd_crossings_bonds_of_down_of_no_outward'`, an even outward parity along the walk
in `BondsDeficit.odd_crossings_bonds_of_ne_of_even_outwardPart`. The fifth,
`RayBondsParity.odd_crossings_bonds_leftRay_of_down`, asks nothing.

**`exists_circuit_surrounding_leftRay`** — and under **`EvenDegrees (dualGraph σ)`** the piece is a
**cycle**: `DualUnique.exists_circuit_surrounding` with `PlusBoundary` replaced by the one thing
its decomposition step used it for. That hypothesis is strictly weaker —
`DualDegreeExact.cornerDown_evenDegrees` and `DualDegreeExact.flip_strict_extension` hold it off
`+` — and it is **not** vacuous, `PieceBranchesRealised.not_evenDegrees_dualGraph_sigmaEdge` being
a configuration that fails it.

**`exists_circuit_surrounding_leftRay_of_plusBoundary`** — **nothing is lost**: under `+` both
hypotheses are free, the even degrees by `DualGraph.evenDegrees_dualGraph` and the endpoint spin
by `RayWalk.isBoundary_edge`.

**`no_spin_from_evenDegrees`** — and the endpoint hypothesis survives this replacement too. The
even-degree condition is invariant under the global flip (`DualDegreeExact.dualGraph_flip`), so
`RayBondsParity.no_spin_from_flip_invariant` applies to it: it cannot imply that a boundary site
is up. **Both** hypotheses of the main theorem are therefore irreducible in their own way — the
first because the decomposition needs it, the second because no flip-invariant condition supplies
it.

## What is NOT here

**A PATH SURROUNDS NOTHING, AND THAT IS THE PRICE OF DROPPING THE EVEN DEGREES.**
`exists_odd_path_or_cycle_piece_leftRay` asks nothing of `σ` and delivers a piece that may be a
**path**. A path crossed an odd number of times is a parity fact and **not** an enclosure: the
Peierls estimate counts *closed* contours around a site. `ERRATUM 97` is the entry that says a
decomposition into paths and cycles is **necessary and not sufficient** for the covering, and this
file is a direct instance of it — the hypothesis-free statement is strictly weaker in content, not
merely in hypotheses. **Which of the two branches occurs is not decided here**, and no theorem
here rules out the path branch on any configuration.

**IT IS ONE RAY, NOT EVERY WALK.** The piece produced depends on the walk, and the walk is fixed.
`SurroundsParity.crossings_parity_indep` gives walk-independence for the **contour**, not for
`bonds σ H`, and **nothing here supplies it for a piece.** So *this piece is crossed oddly by this
ray* is what is proved; *this piece encircles the site* is the reading the estate's own
`SurroundsParity` header calls a **stand-in**, and this file does not improve on it.

**THE `3 ^ |γ|` COUNT IS UNTOUCHED**, and so is `IsingBoundaryField.MagnetisationBound`. **W3 does
not move.** What moves is the boundary condition on one step of the chain.

**NOTHING IS REPAIRED.** The outward bonds are still missing from the dual graph;
`ExtendedDual`'s four-rim construction is still the repair and is still untouched. The ray simply
does not meet them.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `odd_count_circuits_leftRay_iff` takes
**a disjoint decomposition of the dual graph** and the row conditions `0 < b.val`,
`b.val + 1 < n` — **nothing about `σ`**; `exists_odd_path_or_cycle_piece_leftRay` takes the row
conditions and **the two endpoint spins**; `exists_circuit_surrounding_leftRay` adds
**`EvenDegrees (dualGraph σ)`**; `no_spin_from_evenDegrees` takes **`0 < n`** and a configuration
satisfying the condition. No `PlusBoundary` outside §4, which exists to recover it.

## ⚠ WHAT `EvenDegrees (dualGraph σ)` ACTUALLY ASKS FOR. Annotated 6 September 2026

Nothing above is superseded; this is a forward pointer, because *"no boundary condition"* is an
easy thing to read into the main theorem and it would be wrong.
`paper_f/EvenDegreesReach.lean`, which imports this file, shows the hypothesis is **a condition on
the boundary spins and nothing else** (`evenDegrees_congr_boundary`), and that on the boundary it
is severe: **no bond along the interior of a rim may be broken** (`left_rim_const` and its three
partners) and **the two rim neighbours of each corner must agree** (`corner_bl_coupling` and its
three). The interior is free.

So the class reached here is strictly larger than `+` and is **not** all configurations. That file
offers **no count and no proportion**, and neither does this one.

## ⚠ AND THAT CLASS IS ASYMPTOTICALLY INVISIBLE. Annotated 7 September 2026

The annotation above says the class reached here is strictly larger than `+` and is not all
configurations. `paper_f/EvenDegreesClassVanishes.lean` measures it:
**`tendsto_classProb_zero`** — the probability that the boundary is constant away from its corners
tends to `0` as the box grows, at every `β ≥ 0` and every `h`, and by `EvenDegreesConverse` that is
the probability of `EvenDegrees (dualGraph σ)` itself.

So `PlusClassVanishes`'s objection to conditioning on `+` applies verbatim to the hypothesis used
here. **Nothing above is refuted** — every theorem in this file is pointwise and stands — but a
reader taking *strictly weaker than `+`* as *escapes the obstruction* would be wrong.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace RayCircuitSurrounding

open IsingFiniteVolume IsingContourEnergy IsingContourClosed IsingContourPlaquette
open PlaquetteLattice IsingBoundaryField IsingContourSeparation
open DualObstruction DualGraph DualBonds DualUnique BondsDeficit
open OddPieceSelect RowParity RayWalk RayBondsParity SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The sharp count, on every configuration -/

theorem odd_count_circuits_leftRay_iff {σ : Config n} (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n)
    {L : List (SimpleGraph (Plaq n))} (hp : L.Pairwise Disjoint)
    (hsup : L.foldr (· ⊔ ·) ⊥ = dualGraph σ) :
    ¬ Even ((L.map (bonds σ)).countP fun γ =>
        decide ¬ Even (crossings γ (leftRay b k hk)))
      ↔ σ (col b k hk) ≠ σ (edge b.val b.isLt) := by
  rw [SurroundsParity.even_countP_odd_pieces_iff (pairwise_disjoint_bonds hp),
    ← bonds_foldr, hsup, even_crossings_bonds_leftRay_iff σ b hb0 hj k hk]

/-! ## 2. The piece, with no hypothesis on the configuration at all

`OddPieceSelect.exists_odd_path_or_cycle_piece` has been waiting for an odd crossing count it
could take without a boundary condition. The four theorems in the estate that produce one — in
`DualBonds`, `BondsContourCriterion`, `BondsDeficit` and `RayBondsParity` — ask respectively for
`PlusBoundary`, `NoBrokenOutward`, an even outward parity along the walk, and **nothing**. -/

/-- **SOME PIECE OF THE DUAL GRAPH IS CROSSED ODDLY BY THE RAY, AND IT IS A SINGLE PATH OR A
SINGLE CYCLE.** No hypothesis on `σ` beyond the ray's two endpoints. -/
theorem exists_odd_path_or_cycle_piece_leftRay (σ : Config n) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n)
    (hx : σ (col b k hk) = false) (he : σ (edge b.val b.isLt) = true) :
    ∃ H : SimpleGraph (Plaq n), (SimpleGraph.IsPathGraph H ∨ SimpleGraph.IsCycleGraph H) ∧
      ¬ Even (crossings (bonds σ H) (leftRay b k hk)) :=
  exists_odd_path_or_cycle_piece σ (leftRay b k hk)
    (odd_crossings_bonds_leftRay_of_down σ b hb0 hj k hk hx he)

/-! ## 3. And so a down site has a circuit around it, off `+` -/

theorem exists_circuit_surrounding_leftRay {σ : Config n}
    (hev : SimpleGraph.EvenDegrees (dualGraph σ)) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n)
    (hx : σ (col b k hk) = false) (he : σ (edge b.val b.isLt) = true) :
    ∃ (L : List (SimpleGraph (Plaq n))) (H : SimpleGraph (Plaq n)),
      (∀ K ∈ L, SimpleGraph.IsCycleGraph K) ∧ L.Pairwise Disjoint ∧
        L.foldr (· ⊔ ·) ⊥ = dualGraph σ ∧ H ∈ L ∧
        ¬ Even (crossings (bonds σ H) (leftRay b k hk)) := by
  obtain ⟨L, hcyc, hp, hsup⟩ := (dualGraph σ).exists_cycle_decomposition hev
  have hodd : ¬ Even (crossings ((L.map (bonds σ)).foldr (· ∪ ·) ∅) (leftRay b k hk)) := by
    rw [← bonds_foldr, hsup]
    exact odd_crossings_bonds_leftRay_of_down σ b hb0 hj k hk hx he
  obtain ⟨γ, hγmem, hγ⟩ :=
    SurroundsParity.exists_odd_of_odd_sum (pairwise_disjoint_bonds hp) (leftRay b k hk) hodd
  obtain ⟨H, hHL, rfl⟩ := List.mem_map.mp hγmem
  exact ⟨L, H, hcyc, hp, hsup, hHL, hγ⟩

/-! ## 4. Nothing is lost: under `+` both hypotheses are free -/

theorem exists_circuit_surrounding_leftRay_of_plusBoundary {σ : Config n}
    (hσ : DualObstruction.PlusBoundary σ) (b : Fin n) (hb0 : 0 < b.val)
    (hj : b.val + 1 < n) (k : ℕ) (hk : k < n) (hx : σ (col b k hk) = false) :
    ∃ (L : List (SimpleGraph (Plaq n))) (H : SimpleGraph (Plaq n)),
      (∀ K ∈ L, SimpleGraph.IsCycleGraph K) ∧ L.Pairwise Disjoint ∧
        L.foldr (· ⊔ ·) ⊥ = dualGraph σ ∧ H ∈ L ∧
        ¬ Even (crossings (bonds σ H) (leftRay b k hk)) :=
  exists_circuit_surrounding_leftRay (evenDegrees_dualGraph hσ) b hb0 hj k hk hx
    (hσ _ (isBoundary_edge b.val b.isLt))

/-! ## 5. And the even-degree hypothesis cannot supply the endpoint spin either -/

theorem no_spin_from_evenDegrees (hn : 0 < n) {τ₀ : Config n}
    (h0 : SimpleGraph.EvenDegrees (dualGraph τ₀)) :
    ¬ ∀ (τ : Config n) (b : Site n), SimpleGraph.EvenDegrees (dualGraph τ) →
        isBoundary b = true → τ b = true :=
  no_spin_from_flip_invariant hn
    (p := fun τ => SimpleGraph.EvenDegrees (dualGraph τ))
    (fun τ h => show SimpleGraph.EvenDegrees (dualGraph (flip τ)) by
      rw [DualDegreeExact.dualGraph_flip]; exact h) h0

end RayCircuitSurrounding
