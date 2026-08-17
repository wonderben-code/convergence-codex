import ReachKernelDimension

/-!
# The antipodal half's degeneracy is exactly one dimension

`BlockDimension` §5 recorded the exact value here as **NOT DONE**, and said why: the route it tried
— computing `blockClasses` at the concrete half — ran past fifteen minutes and was killed, and the
derived route it kept gives only `0 < finrank`. `ReachKernelDimension` repeated the same NOT DONE.
This closes it.

> **`card_blockClasses_torusHalf`** — the antipodal half's cut has **one block**, and so
> **`finrank_reachKer_torusHalf`**: the reflected form degenerates there in **exactly one**
> direction.

The two halves of `ReflectedFormCongr` §7 are now separated by two *numbers*, `0` against `1`, on
one graph with one reflection at every nonzero mass.

## Why this is fast when the abandoned route was not

`blk` and `cls` filter on a **real** matrix entry, so they are `noncomputable` and `decide` cannot
see them. Both routes push through `BlockCount.mem_blk_iff` / `mem_cls_iff` into adjacency. The
difference is **what is left for `decide` to do afterwards**: here it decides membership
propositions over four sites, one at a time, and the step from *"every class is the whole half"* to
*"there is one class"* is `Finset.image_const` — **a lemma, not a decision**. Nothing ever asks the
kernel to evaluate a `Finset (Finset (Site 1 4))`.

**That is a statement about the two routes, not about the problem.** `ERRATUM 194`: the abandoned
attempt is still a fact about one attempt on one machine, and nothing here says it could not have
been made to work.

## The other half is derived, not computed

`rotHalf`'s count is **not** computed. `BlockCount.blockCount_rotHalf` already proves the count
reaches `|H|` there, so `card_blockClasses_rotHalf` is that theorem read through
`blockCount_eq_card_blockClasses`, and the dimension is `0` because strictness already said so.
**Only the antipodal half needed new work**, which is the half that was open.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusBlockCount

open SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure
open CrossPosSemidef BlockCount BlockDimension ReflectedFormCongr HalfBlockStructure
open ReachKernelDimension TorusReflection

/-! ## 1. The antipodal half has one block -/

/-- **EVERY SITE OF THE ANTIPODAL HALF MEETS THE CUT.** `HalfBlockStructure.touching_torusHalf`
read into `blk`. -/
theorem blk_torusHalf :
    blk (crossMatrix (torusGraph 1 4) torusRho torusHalf) torusHalf = torusHalf := by
  ext k
  simp only [mem_blk_iff]
  exact ⟨fun hk => hk.1, fun hk => ⟨hk, touching_torusHalf k hk⟩⟩

/-- **AND EVERY SITE'S CLASS IS THE WHOLE HALF.** The antipodal pair of the four-cycle is joined,
through the reflection, to *both* of its members: each site is adjacent to the other's mirror image
as well as to its own. **That is the failure of the perfect matching, stated positively** —
`HalfBlockStructure.not_cutPerfect_torusHalf` says the matching fails; this says what it fails
into. -/
theorem cls_torusHalf : ∀ k ∈ torusHalf,
    cls (crossMatrix (torusGraph 1 4) torusRho torusHalf) torusHalf k = torusHalf := by
  intro k hk
  ext i
  rw [mem_cls_iff]
  revert i
  revert hk
  revert k
  decide

/-- **ONE BLOCK.** The image of a constant map on a nonempty set. -/
theorem card_blockClasses_torusHalf :
    (blockClasses (torusGraph 1 4) torusRho torusHalf).card = 1 := by
  have hne : (blk (crossMatrix (torusGraph 1 4) torusRho torusHalf) torusHalf).Nonempty := by
    rw [blk_torusHalf]; decide
  rw [blockClasses, Finset.image_congr (g := fun _ => torusHalf) ?_, Finset.image_const hne]
  · exact Finset.card_singleton _
  · intro k hk
    exact cls_torusHalf k (by rw [blk_torusHalf] at hk; exact hk)

/-- The count itself, upgrading `BlockCount.blockCount_torusHalf_ne` from *not `|H|`* to a value. -/
theorem blockCount_torusHalf : blockCount (torusGraph 1 4) torusRho torusHalf = 1 := by
  rw [blockCount_eq_card_blockClasses isRefl_torusRho isCrossBlock_torusHalf,
    card_blockClasses_torusHalf, Nat.cast_one]

/-! ## 2. And so the degeneracy there is exactly one dimension -/

/-- **THE COUPLING'S KERNEL AT THE ANTIPODAL HALF HAS DIMENSION EXACTLY ONE.**
`BlockDimension.finrank_ker_torusHalf_pos` gave `0 <`; the count gives the value. -/
theorem finrank_ker_torusHalf :
    Module.finrank ℝ (LinearMap.ker (blockSums (torusGraph 1 4) torusRho torusHalf)) = 1 := by
  have hadd := finrank_ker_blockSums_add isRefl_torusRho isCrossBlock_torusHalf
  rw [card_blockClasses_torusHalf, torusHalf_card] at hadd
  omega

/-- **AND SO DOES THE SPACE THE REFLECTED FORM DEGENERATES ON.** Through
`ReachKernelDimension.finrank_reachKer_add`, which is the same number carried onto the object the
strictness criterion is stated about. -/
theorem finrank_reachKer_torusHalf (m : ℝ) :
    Module.finrank ℝ (reachKer (torusGraph 1 4) m torusHalf ∅) = 1 := by
  have hadd := finrank_reachKer_add (m := m) isMirrorHalf_torusHalf isRefl_torusRho
    isCrossBlock_torusHalf
  rw [card_blockClasses_torusHalf, torusHalf_card] at hadd
  omega

/-! ## 3. The contiguous half, derived from strictness rather than computed -/

/-- **TWO BLOCKS, AND NOT ONE LINE OF COMPUTATION.** `BlockCount.blockCount_rotHalf` proves the
count reaches `|H|`; this reads it as a cardinality. -/
theorem card_blockClasses_rotHalf :
    (blockClasses (torusGraph 1 4) torusRho rotHalf).card = 2 := by
  have h := blockCount_rotHalf
  rw [blockCount_eq_card_blockClasses isRefl_torusRho
    (isCrossBlock_of_cross_diag crossDiag_rotHalf)] at h
  have hc : (blockClasses (torusGraph 1 4) torusRho rotHalf).card = rotHalf.card := by
    exact_mod_cast h
  rw [hc]
  decide

/-- **THE REFLECTED FORM DOES NOT DEGENERATE AT ALL ON THE CONTIGUOUS HALF.** -/
theorem finrank_reachKer_rotHalf (m : ℝ) :
    Module.finrank ℝ (reachKer (torusGraph 1 4) m rotHalf ∅) = 0 := by
  have hadd := finrank_reachKer_add (m := m) isMirrorHalf_rotHalf isRefl_torusRho
    (isCrossBlock_of_cross_diag crossDiag_rotHalf)
  rw [card_blockClasses_rotHalf] at hadd
  have hcard : rotHalf.card = 2 := by decide
  omega

/-! ## 4. The pair -/

/-- **ONE GRAPH, ONE REFLECTION, EVERY NONZERO MASS, TWO HALVES: `0` AND `1`.**

`ReflectedFormCongr` §7 reported this as an inequality that holds in one case and fails in the
other. `BlockDimension` §5 sharpened it to *no directions* against *at least one*. This is the
exact pair, and it is the last thing either file recorded as not done. -/
theorem finrank_reachKer_two_halves (m : ℝ) :
    Module.finrank ℝ (reachKer (torusGraph 1 4) m rotHalf ∅) = 0
      ∧ Module.finrank ℝ (reachKer (torusGraph 1 4) m torusHalf ∅) = 1 :=
  ⟨finrank_reachKer_rotHalf m, finrank_reachKer_torusHalf m⟩

/-- **AND THE COUNT SEPARATES THEM BY THE SAME GAP.** `2` against `1` on a half of size `2`:
the contiguous cut is a perfect matching, the antipodal cut fuses its two sites into one block. -/
theorem blockCount_two_halves :
    blockCount (torusGraph 1 4) torusRho rotHalf = 2
      ∧ blockCount (torusGraph 1 4) torusRho torusHalf = 1 := by
  refine ⟨?_, blockCount_torusHalf⟩
  rw [blockCount_rotHalf, show rotHalf.card = 2 from by decide]
  norm_num

end TorusBlockCount
