/-
  IsingSpin: the `±1` encoding of a Boolean spin, once

  **WHY THIS FILE EXISTS.** `UNLOCK_WATCHLIST` `L23857`, open since 22 August: **`spin` is defined
  twice in this estate with identical bodies, and each copy's lemmas apply to only one of them.**
  `IsingFiniteVolume.spin` serves the box and proves `abs_spin` and `spin_not`;
  `IsingTransfer2D.spin` serves the transfer-matrix chain and proves `spin_sq`. They are DISTINCT
  CONSTANTS, so no lemma about one applies to the other, and writing `IsingFlipSymmetry` meant
  re-proving `spin_not` for the second copy — one line that already existed eleven files away.

  **WHAT THE ESTATE HAD ALREADY DONE, AND IT IS MORE THAN THIS FILE'S FIRST DRAFT ADMITTED**
  (`ERRATUM 639`, `ERRATUM 640`). **TWO** things, not one. `IsingBoxInteraction.spin_eq :
  IsingFiniteVolume.spin = IsingTransfer2D.spin := rfl`, with a docstring saying *recording that is
  cheaper than choosing a winner*. And **an entire file for the question**,
  `IsingSpinBridge.lean`, which counted the cost (*182 transitive dependents, of which 20 mention
  `spin` at all* — and the point that **importing is not using**), supplied both missing transfers
  by rewriting, and then said in as many words that **the item stays open** and *its remaining
  content is tidiness rather than re-proof*. **This file is that tidiness**, and it is the
  completion of that plan rather than a discovery. `RE-SWEEP #63`'s FINDING 5 proposed it without
  having read either — which is `ERRATUM 640`.

  **WHY THE TIDINESS WAS STILL WORTH DOING.** A bridge is `rfl` **by accident of two bodies
  agreeing**, not by construction: edit either definition and it breaks with no indication that the
  two were ever meant to be one object. It does not let a `simp` set see through the pair. And it
  leaves the re-proof `L23857` was actually written about — `IsingFlipSymmetry.spin_not`, one line
  that already existed eleven files away — still a re-proof. That line is now
  `IsingSpin.spin_not b`. Both earlier bridges are KEPT and annotated.

  **WHAT IS DONE INSTEAD.** One `def`, here. Both files then `export IsingSpin (spin)` inside their
  own namespaces, so `IsingFiniteVolume.spin` and `IsingTransfer2D.spin` remain valid names for the
  same constant and **not one call site moves** — which matters, because 23 modules name `spin`
  inside a `simp`, `simp_all` or `norm_num` set, at about fifty tactic sites, and an alias that did
  not resolve to the real definition's equations would break every one of them. Each file keeps the
  lemmas it proved, now as one-line instantiations of the ones here, so `abs_spin`, `spin_not` and
  `spin_sq` are available to both.

  **WHAT IS NOT CLAIMED.** Nothing mathematical is new; every statement here was already proved in
  one of the two files. This is a deduplication, and the only strengthening is that all three
  lemmas now apply to both spellings.

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace IsingSpin

/-- Spin value: `true ↦ +1`, `false ↦ −1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

theorem spin_true : spin true = 1 := rfl

theorem spin_false : spin false = -1 := rfl

theorem abs_spin (b : Bool) : |spin b| = 1 := by
  cases b <;> simp [spin]

theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> simp [spin]

theorem spin_sq (b : Bool) : spin b * spin b = 1 := by
  cases b <;> norm_num [spin]

end IsingSpin
