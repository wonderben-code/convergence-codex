import BondsContourGap

/-!
# When the dual graph crosses exactly the contour, and it is not `+`

`DualBonds.bonds_dualGraph` proves that under `PlusBoundary` the dual graph's bond set **is** the
contour. `BondsContourGap` proves that an outward-facing broken side is never a bond, on any
configuration, and exhibits a configuration where the two sets differ. Between them the exact
criterion is one step away, and `bonds_dualGraph`'s own proof says which step: **the `+` hypothesis
enters in exactly one place**, `DualGraph.partnerOf_ne_of_mem`, and all that is taken from it is
that a broken side's partner is not the plaquette itself — which is `¬ Outward`.

**So the hypothesis is stronger than the argument needs**, in the same way and in the same corner as
`EvenRowParity`'s was, and the criterion it should carry is a biconditional.

## What is proved

**`NoBrokenOutward`** — the criterion, as a `Prop`: no broken side faces out of the box.

**`bonds_dualGraph_of_no_outward`** — **the dual graph crosses exactly the contour whenever no
broken side faces out.** `DualBonds.bonds_dualGraph`'s proof with `partnerOf_ne_of_mem hσ` replaced
by the hypothesis itself; nothing else in it looks at `σ`'s boundary.

**`bonds_dualGraph_iff`** — **and only then.** The reverse is `BondsContourGap`'s general theorem: a
broken outward side lies in the contour and in no bond, so the two sets differ. **This is the
converse `BondsContourGap` fenced as missing.**

**`noBrokenOutward_of_plusBoundary`, `bonds_dualGraph_plusBoundary`** — the original recovered, from
`DualGraph.partnerOf_ne_of_mem`. **Nothing is lost.**

**`not_noBrokenOutward_sigmaEdge`** — and `PieceBranchesRealised.sigmaEdge` fails the criterion, so
the biconditional has a witness on the failing side as well as the holding one.

**`crossings_bonds_dualGraph_of_no_outward`, `odd_crossings_bonds_of_down_of_no_outward`** — **and
the spin theorem splits into the two facts `PlusBoundary` was supplying.**
`DualBonds.odd_crossings_bonds_of_down` uses it twice: once to identify the bond set with the
contour, which the criterion replaces, and once for the walk's **endpoint being up**, which turns
crossing parity into the site's spin. The second is carried here as the explicit hypothesis
`σ b = true` — **not weakened, isolated**.

## What is NOT here

**THE CRITERION IS NOT COMPARED TO `PlusBoundary` IN STRENGTH.** It is implied by it, and
`sigmaEdge` shows the implication is strict in one direction; **whether some configuration
satisfies the criterion without satisfying `PlusBoundary` is not settled here**, and
`MinimumContour.cornerDown` — which `DualDegreeExact` records as passing the even-degree test
while failing `PlusBoundary` — is **not** checked against this criterion. **Not attempted, no
cost claimed** (`ERRATUM 246`).

**NOTHING IS REPAIRED, AGAIN.** The criterion says when the bond set is the whole contour; on a
configuration that fails it, the missing bonds are still missing, and `ExtendedDual`'s four-rim
construction is still the repair and is still untouched.

**THE CRITERION DOES NOT REPLACE `PlusBoundary` IN THE SPIN THEOREM, AND §4 SAYS WHY.**
`DualBonds.odd_crossings_bonds_of_down` uses `PlusBoundary` **twice, for two different jobs**:
once through `crossings_bonds_dualGraph`, which is the bond/contour identification and which
this criterion **does** replace; and once through `SurroundsParity.odd_crossings_iff_down`,
which needs the walk's **endpoint to be up** — a fact about `σ` at one site that no criterion
about outward sides can supply. §4 separates them, and **the second is not weakened**: it is
carried as the explicit hypothesis it always was.

**W3 DOES NOT MOVE.** A hypothesis is replaced by the weakest one the proof uses.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `bonds_dualGraph_of_no_outward` and
`bonds_dualGraph_iff` take **`NoBrokenOutward σ` and nothing else** — no `PlusBoundary`, no
finiteness beyond the box. `PlusBoundary` appears in exactly the two theorems that recover the
original.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace BondsContourCriterion

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds ExtendedDual
open BondsContourGap PieceBranchesRealised SimpleGraph

variable {n : ℕ}

/-! ## 1. The criterion -/

/-- **NO BROKEN SIDE FACES OUT OF THE BOX.** -/
def NoBrokenOutward (σ : Config n) : Prop :=
  ∀ (P : Plaq n) (d : Fin 4), sideOf P d ∈ contour σ → ¬ Outward P d

/-! ## 2. It is exactly what makes the bond set the contour -/

/-- **THE DUAL GRAPH CROSSES EXACTLY THE CONTOUR WHENEVER NO BROKEN SIDE FACES OUT.**
`DualBonds.bonds_dualGraph`'s argument with the `+` hypothesis replaced by the one thing it was
used for. -/
theorem bonds_dualGraph_of_no_outward {σ : Config n} (hno : NoBrokenOutward σ) :
    bonds σ (dualGraph σ) = contour σ := by
  refine Finset.Subset.antisymm (bonds_subset _ _) fun e he => ?_
  rw [mem_bonds]
  refine ⟨he, ?_⟩
  induction e using Sym2.ind with
  | _ p q =>
    have hadj : adj p q := ((mem_contour σ p q).mp he).1
    have key : ∀ (P : Plaq n) (d : Fin 4), sideOf P d = s(p, q) →
        ∃ (P' : Plaq n) (d' : Fin 4), (dualGraph σ).Adj P' (partnerOf P' d') ∧
          sideOf P' d' = s(p, q) := by
      intro P d hside
      have hmem : sideOf P d ∈ contour σ := hside ▸ he
      exact ⟨P, d, ⟨d, hmem, rfl, hno P d hmem⟩, hside⟩
    rcases exists_side_eq hadj with ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩ | ⟨P, hP⟩
    · exact key P 0 hP
    · exact key P 1 hP
    · exact key P 2 hP
    · exact key P 3 hP

/-- **AND ONLY THEN.** The converse `BondsContourGap` fenced as missing: a broken outward side is in
the contour and in no bond. -/
theorem bonds_dualGraph_iff (σ : Config n) :
    bonds σ (dualGraph σ) = contour σ ↔ NoBrokenOutward σ := by
  refine ⟨fun hEq P d hmem hout => ?_, bonds_dualGraph_of_no_outward⟩
  exact sideOf_notMem_bonds_of_outward σ hout (hEq ▸ hmem)

/-! ## 3. Nothing is lost, and the failing side has a witness -/

theorem noBrokenOutward_of_plusBoundary {σ : Config n} (hσ : PlusBoundary σ) :
    NoBrokenOutward σ := fun P d hmem => partnerOf_ne_of_mem hσ P d hmem

/-- The original, recovered. -/
theorem bonds_dualGraph_plusBoundary {σ : Config n} (hσ : PlusBoundary σ) :
    bonds σ (dualGraph σ) = contour σ :=
  bonds_dualGraph_of_no_outward (noBrokenOutward_of_plusBoundary hσ)

/-- **AND THE CRITERION GENUINELY FAILS SOMEWHERE.** -/
theorem not_noBrokenOutward_sigmaEdge : ¬ NoBrokenOutward sigmaEdge := fun hno =>
  (bonds_dualGraph_iff sigmaEdge).mpr hno |> bonds_ne_contour_sigmaEdge

/-! ## 4. Which half of `+` does which job -/

/-- **THE BOND/CONTOUR HALF OF `crossings_bonds_dualGraph` NEEDS ONLY THE CRITERION.** -/
theorem crossings_bonds_dualGraph_of_no_outward {σ : Config n} (hno : NoBrokenOutward σ)
    {x b : Site n} (w : (IsingContourSeparation.latticeGraph n).Walk x b) :
    IsingContourClosed.crossings (bonds σ (dualGraph σ)) w =
      IsingContourClosed.crossings (contour σ) w := by
  rw [bonds_dualGraph_of_no_outward hno]

/-- **AND THE SPIN THEOREM SPLITS INTO THE TWO FACTS `PlusBoundary` WAS SUPPLYING.** The criterion
identifies the bond set with the contour; the endpoint being **up** is what turns crossing parity
into the site's spin, and it is a fact about `σ` at one site that no criterion about outward sides
can give. -/
theorem odd_crossings_bonds_of_down_of_no_outward {σ : Config n} (hno : NoBrokenOutward σ)
    {x b : Site n} (hb : σ b = true) (hx : σ x = false)
    (w : (IsingContourSeparation.latticeGraph n).Walk x b) :
    ¬ Even (IsingContourClosed.crossings (bonds σ (dualGraph σ)) w) := by
  rw [crossings_bonds_dualGraph_of_no_outward hno]
  rw [SurroundsParity.odd_crossings_iff_ne, hb, hx]
  exact Bool.noConfusion

end BondsContourCriterion
