/-
  IsingSpinBridge.lean — the two `spin` definitions are one function, so their
  lemmas are one set.

  WHY. `UNLOCK_WATCHLIST` records that `spin` is defined twice in this estate,
  with identical bodies, and that each copy's lemmas apply to only one of them:
  `IsingTransfer2D.spin` carries `spin_sq`, `IsingFiniteVolume.spin` carries
  `abs_spin` and `spin_not`, and writing `IsingFlipSymmetry` had to re-prove
  `spin_not` for the other copy — one line, eleven files from where it already
  existed. The item calls that `ERRATUM 42`'s family: the estate proving
  something for the neighbouring object and not for this one.

  WHAT THE ITEM PROPOSED, AND WHY THIS IS NOT THAT. Its `LIKELY OUTCOME` line
  says *"one of the two definitions deleted and its uses repointed"*, and its
  `ESTIMATE` line says the number of files importing `IsingFiniteVolume` "is the
  whole of the cost and has not been counted here". **Counted: 182 transitive
  dependents, of which 20 mention `spin` at all.** So the cost model in that line
  is wrong by a factor of nine — importing is not using — and the real diff is 20
  files rather than 182.

  **AND IT CAN BE NOTHING.** The two definitions are the same function, so
  `spin_eq` is `rfl`, and every lemma about either transfers by rewriting. This
  file is that bridge and the two transfers that were missing. **No existing file
  changes**, and the cost the item is actually about — paying for a lemma twice —
  is gone.

  WHAT THIS DOES NOT DO. It does not delete either definition. Two constants with
  the same body still exist, `simp` sets still do not see through the pair without
  the bridge, and a reader can still write `spin` meaning the other one. **The
  item stays open**; what changes is that its cost is measured and its remaining
  content is tidiness rather than re-proof.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingTransfer2D
import IsingFiniteVolume

namespace IsingSpinBridge

/-- **THE TWO `spin`s ARE ONE FUNCTION.** Both are `fun b => if b then 1 else -1` at `ℝ`, so this
is `rfl` — which is the whole point: nothing was ever different, only the name. -/
theorem spin_eq : IsingFiniteVolume.spin = IsingTransfer2D.spin := rfl

theorem spin_apply_eq (b : Bool) : IsingFiniteVolume.spin b = IsingTransfer2D.spin b := rfl

/-! ## The two transfers that were missing

Each is the lemma one copy had and the other did not, obtained by rewriting rather than by proving
it again. That is the whole content of the item and it is two lines. -/

/-- `IsingTransfer2D.spin` gains `abs_spin`, which only `IsingFiniteVolume` had. -/
theorem abs_spin (b : Bool) : |IsingTransfer2D.spin b| = 1 := by
  rw [← spin_apply_eq]; exact IsingFiniteVolume.abs_spin b

/-- `IsingFiniteVolume.spin` gains `spin_sq`, which only `IsingTransfer2D` had. -/
theorem spin_sq (b : Bool) : IsingFiniteVolume.spin b * IsingFiniteVolume.spin b = 1 := by
  rw [spin_apply_eq]; exact IsingTransfer2D.spin_sq b

/-- **AND THE RE-PROOF THE ITEM WAS WRITTEN ABOUT, AS ONE REWRITE.**
`IsingFlipSymmetry.spin_not` exists because `IsingFiniteVolume.spin_not` could not be used across
the pair. This is what that line would have been. It is stated rather than used: `IsingFlipSymmetry`
is upstream of nothing here and is not edited, per the item's own note that a rename in the middle
of a proof unit is broadening. -/
theorem spin_not (b : Bool) :
    IsingTransfer2D.spin (!b) = -IsingTransfer2D.spin b := by
  rw [← spin_apply_eq, ← spin_apply_eq]; exact IsingFiniteVolume.spin_not b

end IsingSpinBridge
