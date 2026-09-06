import NoBrokenOutwardCharacterised

/-!
# What the dual graph misses, exactly, on every configuration — and the spin recovered from a
condition on the walk instead of on the box

`BondsContourCriterion` proved `bonds σ (dualGraph σ) = contour σ ↔ NoBrokenOutward σ`, and
`NoBrokenOutwardCharacterised` proved that criterion is `PlusBoundary σ ∨ PlusBoundary (flip σ)`.
So the equality is now understood completely, and so is its failure: it fails **exactly** when the
configuration changes value somewhere along the edge of the box. A biconditional that fails is not
a description of the failure.

This file replaces it with an equation that holds on **every** configuration:

> **`bonds_dualGraph_eq_filter`** — `bonds σ (dualGraph σ)` is the contour with the
> **outward-facing bonds deleted**, and nothing else is missing.

and takes the one consequence that matters for the Peierls step:

> **`odd_crossings_bonds_of_ne_of_even_outwardPart`** — a walk from a down site to an up site
> crosses the dual graph's bonds an odd number of times **as soon as it crosses the outward part
> evenly**. No boundary condition anywhere: the hypothesis is about the **walk**, not about the
> configuration.

`BondsContourCriterion.odd_crossings_bonds_of_down_of_no_outward` is the special case where the
outward part is empty, and `NoBrokenOutwardCharacterised.noBrokenOutward_iff` says that special
case asks for the whole edge of the box to be constant. This asks for nothing of the sort.

## What is proved

**`OutwardBond`, `outwardPart`** — a bond is *outward* when some plaquette has it as a side facing
out of the box; `outwardPart σ` is the part of the contour made of them.

**`bonds_dualGraph_eq_filter`** — **the equation**, unconditional. One inclusion is
`BondsContourGap.sideOf_notMem_bonds_of_outward`; the other is
`BondsContourCriterion.bonds_dualGraph_of_no_outward`'s argument run at a single bond instead of
under a global hypothesis, which is the whole trick — that proof never needed the criterion
globally, only at the bond in front of it.

**`contour_eq_union`, `disjoint_bonds_outwardPart`, `crossings_contour_split`** — so the contour
splits as a disjoint union and the crossing count splits with it
(`SurroundsParity.crossings_union`).

**`even_crossings_bonds_iff`** — **the parity, for every configuration and every walk**: the dual
graph's crossings and the outward crossings have the **same parity exactly when the endpoints
agree**. Any two of the three facts determine the third.

**`odd_crossings_bonds_of_ne_of_even_outwardPart`** — **the Peierls step with the boundary
condition replaced by a condition on the walk.**

**`outwardPart_eq_empty_iff`, `outwardPart_eq_empty_iff_plusBoundary_or_flip`** — and the old
hypotheses recovered: the outward part is empty exactly when `NoBrokenOutward` holds, which is
exactly when the configuration is constant along the edge of the box.
**`even_crossings_outwardPart_of_noBrokenOutward`, `odd_crossings_bonds_of_down_of_no_outward'`**
— **and nothing is lost**: the criterion makes the outward crossings zero on every walk, so the
previous unit's theorem is a two-line corollary of this one. The implication is machine-checked
rather than asserted.

**`outwardPart_isBoundary`** — **and the deficit lives on the edge of the box**
(`RimBoundary.outward_side_isBoundary`): every bond of it has both ends on the boundary.

**`outwardBond_sideL_origin`, `outwardBond_sideD_origin`, `outwardBond_of_adj_origin`** — **and
every bond at the corner is one of them**, so on the walk `DualBonds.odd_crossings_bonds_of_down`
uses, which ends at that corner, the new hypothesis cannot be met by routing around the outward
bonds. It is a parity condition and only that.

## What is NOT here

**THE HYPOTHESIS IS NOT DISCHARGED, IT IS MOVED.** `Even (crossings (outwardPart σ) w)` is a real
condition and nothing here says when it holds. **No theorem in this file exhibits a walk
satisfying it on a configuration that fails the criterion**, and for the walk
`DualBonds.odd_crossings_bonds_of_down` uses, the obvious route — routing around the outward
bonds — is **closed**, not merely unexamined: `outwardBond_of_adj_origin` proves **every** bond at
`SurroundsParity.origin` is an outward bond, and that walk ends there. So on that walk the
condition has to be met by **parity across broken bonds**, never by avoidance. **This is said of
the corner only.** `BondsContourCriterion.odd_crossings_bonds_of_down_of_no_outward` allows any up
site `b` as the endpoint, and at a general boundary site it is **false** that every incident bond
faces out — in a `3 × 3` box the bond from `(0,1)` to `(1,1)` does not. Which walks meet the
condition is **not attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING IS REPAIRED.** `ExtendedDual`'s four-rim construction is still the repair for the
missing bonds and is still untouched. This file **names** what is missing; it does not put it
back.

**W3 DOES NOT MOVE.** `IsingBoundaryField.MagnetisationBound` needs the `3 ^ |γ|` count and the
circuit decomposition, and neither is touched. What moves is one hypothesis of one step, from a
condition on the whole box to a condition on one walk.

**NO CLAIM THAT THE NEW HYPOTHESIS IS WEAKER IN PRACTICE.** It is formally weaker — the criterion
implies it, and `even_crossings_outwardPart_of_noBrokenOutward` is that implication — and **that
is all that is shown**. Whether it is ever
satisfied where the criterion is not is exactly the question the paragraph above leaves open.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): every theorem here takes **nothing**
about `n`, nothing about `PlusBoundary`, and no decidability beyond the classical instance the
`Finset.filter` needs — the same one `DualBonds` opens for the same reason.
`odd_crossings_bonds_of_ne_of_even_outwardPart` takes **the walk's outward parity and the two
endpoint spins**, and those three are its entire hypothesis.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace BondsDeficit

open IsingFiniteVolume IsingContourEnergy IsingContourClosed IsingContourPlaquette
open PlaquetteLattice IsingBoundaryField IsingContourSeparation
open DualObstruction DualGraph ExtendedDual DualBonds
open BondsContourGap BondsContourCriterion RimBoundary SimpleGraph

/- `OutwardBond` quantifies over `Plaq n`, whose `Fintype` instance is itself noncomputable, so
there is no decidable instance to state instead and the classical one is the honest choice —
`DualBonds` opens it for the same predicate and the same reason. -/
set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The bonds that face out of the box -/

/-- A bond of the box **faces out** when some plaquette has it as a side whose partner is that
plaquette itself — `DualGraph`'s way of recording "there is no square on the other side". -/
def OutwardBond (e : Sym2 (Site n)) : Prop :=
  ∃ (P : Plaq n) (d : Fin 4), sideOf P d = e ∧ Outward P d

/-- The part of the contour the dual graph cannot see. -/
noncomputable def outwardPart (σ : Config n) : Finset (Sym2 (Site n)) :=
  (contour σ).filter OutwardBond

theorem mem_outwardPart {σ : Config n} {e : Sym2 (Site n)} :
    e ∈ outwardPart σ ↔ e ∈ contour σ ∧ OutwardBond e := by
  simp [outwardPart]

/-- **AND IT LIES ALONG THE EDGE OF THE BOX**, both ends of every one of its bonds. -/
theorem outwardPart_isBoundary {σ : Config n} {e : Sym2 (Site n)} (he : e ∈ outwardPart σ) :
    ∀ y ∈ e, isBoundary y = true := by
  obtain ⟨-, P, d, hside, hout⟩ := mem_outwardPart.mp he
  subst hside
  exact outward_side_isBoundary hout

/-! ## 2. The equation, on every configuration

`bonds_dualGraph_of_no_outward` uses `NoBrokenOutward` at exactly one place — the bond it is
looking at — and never again. Run at a single bond it needs no global hypothesis, and that is
what turns a biconditional into an equation. -/

theorem bonds_subset_filter (σ : Config n) :
    bonds σ (dualGraph σ) ⊆ (contour σ).filter (fun e => ¬ OutwardBond e) := by
  intro e he
  rw [Finset.mem_filter]
  refine ⟨bonds_subset _ _ he, ?_⟩
  rintro ⟨P, d, hside, hout⟩
  exact sideOf_notMem_bonds_of_outward σ hout (hside ▸ he)

theorem filter_subset_bonds (σ : Config n) :
    (contour σ).filter (fun e => ¬ OutwardBond e) ⊆ bonds σ (dualGraph σ) := by
  intro e he
  rw [Finset.mem_filter] at he
  obtain ⟨hc, hno⟩ := he
  rw [mem_bonds]
  refine ⟨hc, ?_⟩
  induction e using Sym2.ind with
  | _ p q =>
    have hadj : adj p q := ((mem_contour σ p q).mp hc).1
    have key : ∀ (P : Plaq n) (d : Fin 4), sideOf P d = s(p, q) →
        ∃ (P' : Plaq n) (d' : Fin 4), (dualGraph σ).Adj P' (partnerOf P' d') ∧
          sideOf P' d' = s(p, q) := by
      intro P d hside
      have hmem : sideOf P d ∈ contour σ := hside ▸ hc
      exact ⟨P, d, ⟨d, hmem, rfl, fun hout => hno ⟨P, d, hside, hout⟩⟩, hside⟩
    rcases exists_side_eq hadj with ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩
    · exact key P 0 hP
    · exact key P 1 hP
    · exact key P 2 hP
    · exact key P 3 hP

/-- **THE CONTOUR WITH THE OUTWARD BONDS DELETED, AND NOTHING ELSE MISSING.** No hypothesis. -/
theorem bonds_dualGraph_eq_filter (σ : Config n) :
    bonds σ (dualGraph σ) = (contour σ).filter (fun e => ¬ OutwardBond e) :=
  Finset.Subset.antisymm (bonds_subset_filter σ) (filter_subset_bonds σ)

theorem contour_eq_union (σ : Config n) :
    contour σ = bonds σ (dualGraph σ) ∪ outwardPart σ := by
  rw [bonds_dualGraph_eq_filter, outwardPart]
  ext e
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro he
    by_cases h : OutwardBond e
    · exact Or.inr ⟨he, h⟩
    · exact Or.inl ⟨he, h⟩
  · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he

theorem disjoint_bonds_outwardPart (σ : Config n) :
    Disjoint (bonds σ (dualGraph σ)) (outwardPart σ) := by
  rw [Finset.disjoint_left]
  intro e he hd
  obtain ⟨-, P, d, hside, hout⟩ := mem_outwardPart.mp hd
  exact sideOf_notMem_bonds_of_outward σ hout (hside ▸ he)

/-! ## 3. So the crossing count splits, and the parity is readable on every configuration -/

theorem crossings_contour_split (σ : Config n) {x b : Site n}
    (w : (latticeGraph n).Walk x b) :
    crossings (contour σ) w
      = crossings (bonds σ (dualGraph σ)) w + crossings (outwardPart σ) w := by
  have h := SurroundsParity.crossings_union (disjoint_bonds_outwardPart σ) w
  rw [← contour_eq_union σ] at h
  exact h

/-- **THE PARITY, FOR EVERY CONFIGURATION AND EVERY WALK.** The dual graph's crossings and the
outward crossings have the **same parity exactly when the endpoints agree** — so any two of the
three facts determine the third, on every configuration, with no boundary condition. -/
theorem even_crossings_bonds_iff (σ : Config n) {x b : Site n}
    (w : (latticeGraph n).Walk x b) :
    (Even (crossings (bonds σ (dualGraph σ)) w) ↔ Even (crossings (outwardPart σ) w))
      ↔ σ x = σ b := by
  have hC : Even (crossings (contour σ) w) ↔ σ x = σ b := even_crossings_iff σ w
  rwa [crossings_contour_split σ w, Nat.even_add] at hC

/-- **THE PEIERLS STEP, WITH THE BOUNDARY CONDITION REPLACED BY A CONDITION ON THE WALK.**
`BondsContourCriterion.odd_crossings_bonds_of_down_of_no_outward` is the case where the outward
part is empty — which, by `NoBrokenOutwardCharacterised.noBrokenOutward_iff`, asks the whole edge
of the box to be constant. This asks only that one walk cross the outward part evenly. -/
theorem odd_crossings_bonds_of_ne_of_even_outwardPart (σ : Config n) {x b : Site n}
    (w : (latticeGraph n).Walk x b) (hd : Even (crossings (outwardPart σ) w))
    (hb : σ b = true) (hx : σ x = false) :
    ¬ Even (crossings (bonds σ (dualGraph σ)) w) := by
  intro hA
  have hxb := (even_crossings_bonds_iff σ w).mp (iff_of_true hA hd)
  rw [hx, hb] at hxb
  exact Bool.noConfusion hxb

/-! ## 3b. Every bond at the corner is an outward bond

`SurroundsParity.origin` is the corner of the box, and every walk in this chain ends there. Both
bonds meeting it are sides of the corner plaquette facing out, so `crossings (outwardPart σ) w`
cannot be made zero by routing: the new hypothesis is a **parity** condition on broken bonds and
nothing weaker. -/

theorem outwardBond_sideL_origin (hn : 1 < n) :
    OutwardBond (sideL (⟨0, 0, by omega, by omega⟩ : Plaq n)) :=
  ⟨⟨0, 0, by omega, by omega⟩, 0, rfl, (leftP_eq_self_iff _).mpr rfl⟩

theorem outwardBond_sideD_origin (hn : 1 < n) :
    OutwardBond (sideD (⟨0, 0, by omega, by omega⟩ : Plaq n)) :=
  ⟨⟨0, 0, by omega, by omega⟩, 3, rfl, (downP_eq_self_iff _).mpr rfl⟩

/-- **EVERY BOND AT THE CORNER FACES OUT OF THE BOX.** The corner has exactly two neighbours and
each bond to one of them is a side of the corner plaquette whose partner is that plaquette. -/
theorem outwardBond_of_adj_origin (hn : 1 < n) {q : Site n}
    (h : adj (SurroundsParity.origin (by omega)) q) :
    OutwardBond (s(SurroundsParity.origin (by omega), q) : Sym2 (Site n)) := by
  have hq1 := q.1.isLt
  have hq2 := q.2.isLt
  simp only [SurroundsParity.origin, adj, Fin.ext_iff] at h
  refine ⟨⟨0, 0, by omega, by omega⟩, ?_⟩
  rcases h with ⟨hfst, h1 | h1⟩ | ⟨hsnd, h1 | h1⟩
  · refine ⟨0, ?_, (leftP_eq_self_iff _).mpr rfl⟩
    change sideL (⟨0, 0, by omega, by omega⟩ : Plaq n) = _
    simp only [sideL, bl, tl, SurroundsParity.origin, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff,
      true_and]
    omega
  · omega
  · refine ⟨3, ?_, (downP_eq_self_iff _).mpr rfl⟩
    change sideD (⟨0, 0, by omega, by omega⟩ : Plaq n) = _
    simp only [sideD, br, bl, SurroundsParity.origin, Sym2.eq_iff, Prod.ext_iff, Fin.ext_iff,
      and_true]
    omega
  · omega

/-! ## 4. The old hypotheses, recovered as the empty case -/

theorem outwardPart_eq_empty_iff (σ : Config n) :
    outwardPart σ = ∅ ↔ NoBrokenOutward σ := by
  constructor
  · intro h P d hmem hout
    have : sideOf P d ∈ outwardPart σ := mem_outwardPart.mpr ⟨hmem, P, d, rfl, hout⟩
    rw [h] at this
    exact absurd this (Finset.notMem_empty _)
  · intro hno
    refine Finset.eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨hc, P, d, hside, hout⟩ := mem_outwardPart.mp he
    exact hno P d (hside ▸ hc) hout

/-- And so the empty case is exactly `+` or `−` on the edge of the box. -/
theorem outwardPart_eq_empty_iff_plusBoundary_or_flip (σ : Config n) :
    outwardPart σ = ∅ ↔ (PlusBoundary σ ∨ PlusBoundary (flip σ)) :=
  (outwardPart_eq_empty_iff σ).trans (NoBrokenOutwardCharacterised.noBrokenOutward_iff σ)

/-- Under the criterion there is nothing to cross. -/
theorem even_crossings_outwardPart_of_noBrokenOutward {σ : Config n}
    (hno : NoBrokenOutward σ) {x b : Site n} (w : (latticeGraph n).Walk x b) :
    Even (crossings (outwardPart σ) w) := by
  rw [(outwardPart_eq_empty_iff σ).mpr hno, SurroundsParity.crossings_empty]
  exact ⟨0, rfl⟩

/-- **AND SO NOTHING IS LOST.** `BondsContourCriterion.odd_crossings_bonds_of_down_of_no_outward`
recovered as a corollary of the unconditional statement. -/
theorem odd_crossings_bonds_of_down_of_no_outward' {σ : Config n} (hno : NoBrokenOutward σ)
    {x b : Site n} (w : (latticeGraph n).Walk x b) (hb : σ b = true) (hx : σ x = false) :
    ¬ Even (crossings (bonds σ (dualGraph σ)) w) :=
  odd_crossings_bonds_of_ne_of_even_outwardPart σ w
    (even_crossings_outwardPart_of_noBrokenOutward hno w) hb hx

end BondsDeficit
