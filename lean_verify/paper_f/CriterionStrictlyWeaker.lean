import BondsContourCriterion
import DualDegreeExact
import IsingContourInvariant

/-!
# The criterion is strictly weaker than `+`, and the named candidate is settled

`BondsContourCriterion` replaced `PlusBoundary` by `NoBrokenOutward` — no broken side faces out
of the box — and showed that is exactly when the dual graph's bond set is the contour. It left
two questions, both named and small: **does anything satisfy the criterion without satisfying
`PlusBoundary`?**, and **what happens at `MinimumContour.cornerDown`?** Until the first is
answered the biconditional could be a restatement of `+` in other words.

**The answer to the first is yes**, and the witness costs nothing:
`IsingContourInvariant.contour_flip` says **flipping every spin leaves the contour alone**, and
`NoBrokenOutward` is a statement about the contour and nothing else. So the flip of any `+`
configuration satisfies the criterion, and `DualDegreeExact.not_plusBoundary_flip` already says
it fails `PlusBoundary`.

**The answer to the second is that `cornerDown` fails the criterion**, and that too was already
paid for: `DualDegreeExact.outward_of_mem_cornerDown` says **every** broken side of `cornerDown`
faces outwards, and its contour is not empty.

## What is proved

**`noBrokenOutward_congr`** — the criterion depends only on the contour. One line, and it is the
whole reason the flip works. It is the `NoBrokenOutward` analogue of
`DualDegreeExact.dualGraph_congr`, which says the same of the dual graph.

**`noBrokenOutward_flip`** — **so the criterion survives flipping every spin**, where
`PlusBoundary` of course does not.

**`flip_strictly_weaker`** — **at every `n > 0` and every `+` configuration**: the flip satisfies
the criterion and fails `PlusBoundary`. Not one witness — the whole `+` class, moved.

**`exists_noBrokenOutward_not_plusBoundary`** — **so the criterion is strictly weaker than `+`, at
every box size.**

**`contour_flip_nonempty`, `contour_flip_sigmaPlus_nonempty`** — **and not vacuously**: the flip
preserves the contour, so a witness with a non-empty contour exists as soon as a `+` configuration
with one does, and `DualGraph.sigmaPlus` is one. The witness is not the all-down configuration
with nothing broken.

**`not_noBrokenOutward_cornerDown`** — **and `cornerDown` fails the criterion**, at every `n > 1`.
This is the candidate `BondsContourCriterion` named and left unchecked; it is now checked, and it
is not a witness.

## What is NOT here

**NO CHARACTERISATION OF THE CRITERION.** *Which* configurations satisfy `NoBrokenOutward` is not
described — the flips of `+` configurations are one family, and **nothing says it is all of them**.
The obvious guess, that it holds exactly when every edge of the box is constant, is **not proved**.
**Not attempted, no cost claimed** (`ERRATUM 246`).

**NOTHING FOLLOWS FOR THE SPIN.** `BondsContourCriterion.odd_crossings_bonds_of_down_of_no_outward`
still needs the walk's endpoint `b` to satisfy `σ b = true`, and on a flipped `+` configuration
every boundary site is `false` — so this witness satisfies the criterion and is exactly the wrong
shape for that theorem. **The two jobs `PlusBoundary` was doing are independent, and this file
shows the independence rather than removing either.**

**THIS IS NOT A NEW WITNESS CLASS FOR THE DUAL GRAPH.** `DualDegreeExact.flip_strict_extension`
already moved the `+` class by the same flip, for the *even-degree* hypothesis, and recorded that
the flip carries the **same** dual graph. The graphs reachable here are the graphs reachable
there. What is new is only that the *bond-set* criterion, which is a different hypothesis, is
also survived.

**W3 DOES NOT MOVE.** A hypothesis is shown strictly weaker than the one it replaced, and a
candidate is ruled out.

**No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `noBrokenOutward_congr` and
`noBrokenOutward_flip` take **nothing but the equality of contours**; `flip_strictly_weaker` and
`exists_noBrokenOutward_not_plusBoundary` take **`0 < n`**; `not_noBrokenOutward_cornerDown` takes
**`1 < n`**; the two `sigmaPlus` theorems take **nothing at all**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace CriterionStrictlyWeaker

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph ExtendedDual
open BondsContourCriterion SimpleGraph

variable {n : ℕ}

/-! ## 1. The criterion sees only the contour -/

theorem noBrokenOutward_congr {σ τ : Config n} (h : contour σ = contour τ) :
    NoBrokenOutward σ ↔ NoBrokenOutward τ := by
  constructor <;> intro hno P d hmem
  · exact hno P d (h ▸ hmem)
  · exact hno P d (h ▸ hmem)

/-- **SO IT SURVIVES FLIPPING EVERY SPIN**, which `PlusBoundary` does not. -/
theorem noBrokenOutward_flip {σ : Config n} :
    NoBrokenOutward (flip σ) ↔ NoBrokenOutward σ :=
  noBrokenOutward_congr (IsingContourInvariant.contour_flip σ)

/-! ## 2. The whole `+` class moves off the hypothesis and stays inside the criterion -/

theorem noBrokenOutward_flip_of_plusBoundary {σ : Config n} (hσ : PlusBoundary σ) :
    NoBrokenOutward (flip σ) :=
  noBrokenOutward_flip.mpr (noBrokenOutward_of_plusBoundary hσ)

/-- **THE CRITERION IS STRICTLY WEAKER THAN `+`, ON EVERY `+` CONFIGURATION AT ONCE.** -/
theorem flip_strictly_weaker (hn : 0 < n) {σ : Config n} (hσ : PlusBoundary σ) :
    NoBrokenOutward (flip σ) ∧ ¬ PlusBoundary (flip σ) :=
  ⟨noBrokenOutward_flip_of_plusBoundary hσ, DualDegreeExact.not_plusBoundary_flip hn hσ⟩

/-- **AND SO SOMETHING SATISFIES THE CRITERION AND NOT `+`, AT EVERY BOX SIZE.** The cheapest
instance, whose contour is empty; §3 supplies one whose contour is not. -/
theorem exists_noBrokenOutward_not_plusBoundary (hn : 0 < n) :
    ∃ σ : Config n, NoBrokenOutward σ ∧ ¬ PlusBoundary σ :=
  ⟨flip fun _ => true, flip_strictly_weaker hn plusBoundary_allTrue⟩

/-! ## 3. And not vacuously: a witness with a non-empty contour -/

theorem contour_flip_nonempty {σ : Config n} (h : (contour σ).Nonempty) :
    (contour (flip σ)).Nonempty := by
  rw [IsingContourInvariant.contour_flip]
  exact h

theorem noBrokenOutward_flip_sigmaPlus : NoBrokenOutward (flip sigmaPlus) :=
  noBrokenOutward_flip_of_plusBoundary plusBoundary_sigmaPlus

/-- **THE WITNESS HAS A NON-EMPTY CONTOUR**, so it is not the all-down configuration with nothing
broken. `flip sigmaPlus` is up at the one interior site `(1, 1)` of the `4 × 4` box and down
everywhere else. -/
theorem contour_flip_sigmaPlus_nonempty : (contour (flip sigmaPlus)).Nonempty :=
  contour_flip_nonempty ⟨sideR plaq01, sideR_plaq01_mem⟩

/-! ## 4. The candidate `BondsContourCriterion` named, checked

`cornerDown` is not a witness, and the reason is the sharpest possible one: *every* broken side of
it faces outwards, so it is as far from the criterion as a configuration with a non-empty contour
can be. -/

/-- **`cornerDown` FAILS THE CRITERION**, at every `n > 1`. -/
theorem not_noBrokenOutward_cornerDown (hn : 1 < n) :
    ¬ NoBrokenOutward (MinimumContour.cornerDown n) := by
  intro hno
  have hmem : sideOf (OuterFaceObstruction.cornerPlaq hn) 0
      ∈ contour (MinimumContour.cornerDown n) :=
    OuterFaceObstruction.cornerDown_sideL_mem hn
  exact hno _ 0 hmem (DualDegreeExact.outward_of_mem_cornerDown hn hmem)

end CriterionStrictlyWeaker
