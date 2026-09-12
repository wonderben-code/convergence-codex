import MultipartiteSignlessKernel

/-!
# A part value that is also a secular root

**FOUR FILES IN THIS CHAIN HAVE WRITTEN THAT NOTHING RULES OUT A PART VALUE COINCIDING WITH A
SECULAR ROOT.** `SecularRootExact`, `SecularPoleMultiplicity`, `SecularPoleNotPartValue` and
`MultipartiteSignlessKernel` all say it, each time as the reason the three counts — part values,
secular roots, poles — cannot simply be added into a count of `Q`'s spectrum. **Nothing rules it
out because it happens**, and this file is the graph where it does.

## What is proved

**`part_value_eq_secular_root`** — at `K_{1,3,3}`, with `N = 7` and part sizes `1, 3, 3`, the part
value `N − 3 = 4` satisfies the secular equation: `1/(5 − 4) + 3/(1 − 4) + 3/(1 − 4) = −1`. The
hedge is now a theorem with a witness, and the shape of any future count is fixed by it — **the
counts overlap, so a statement about `Q`'s spectrum has to be inclusion–exclusion and not
addition.**

**`finrank_signless_part133_four`** — **and this inhabits a branch nobody had reached.**
`UnbalancedMultipartiteSecularEquation.finrank_signless_size_secular_one` was written when the
criterion was proved and has never been applied anywhere in the estate, because its hypothesis is
that the secular equation holds *at a part value*. Applied here it gives `k₃ · (3 − 1) + 1 = 5`:
four dimensions from the two parts of size three, and **one more from the secular root sitting on
top of the part value**. The `+ 1` in that theorem is exactly the overlap, and it was always the
right shape — what was missing was any graph to point at.

**`finrank_signless_part133_one`, `finrank_signless_part133_five`,
`finrank_signless_part133_nine`** — the rest of the spectrum, by three different routes. `1` is a
pole and not a part value, so entry 171's formula gives `|T| − 1 = 2 − 1 = 1`. `5` is a pole too
and gives `1 − 1 = 0`: **a pole that is not an eigenvalue at all**, which is worth having on record
next to one that is. `9` is the other secular root and is neither a part value nor a pole, so the
criterion off the poles gives `1`.

**`finrank_signless_part133_add`** — and `1 + 5 + 1 = 7 = N`. **That is the check that would have
failed if the overlap had been miscounted**, and it does not fail.

## What is NOT here

* **THE SUM DOES NOT PROVE THE SPECTRUM IS EXACTLY `{1, 4, 9}`.** Three eigenspaces for distinct
  eigenvalues are independent and their dimensions add to `N`, so no fourth eigenvalue can exist —
  **but that inference is not in Lean here.** `UnbalancedMultipartiteDiamond` and
  `HermitianRootMultiplicity` do it for the diamond through the characteristic polynomial, and the
  same route would work; it is not written. What §5 establishes is the arithmetic consistency
  check, not the completeness statement. Not attempted (`ERRATUM 246`).
* **THIS IS ONE GRAPH, NOT A CHARACTERISATION.** Nothing here says *when* a part value is a secular
  root — no condition on the part sizes, no count of how often it happens in a family. A single
  witness is what the hedge needed and all it gets.
* **THE THREE COUNTS ARE STILL NOT ADDED.** What changes is the reason: it is no longer that the
  overlap might exist, but that it does, and the statement must handle it.
* **THE ROOT VALUES ARE HERE ONLY AT THIS GRAPH**, found by hand and checked by `norm_num`. There
  is still no general formula, as everywhere in this chain.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): none beyond the concrete graph. Every
statement in this file is about `Part133`, so the side conditions the general theorems take —
nonemptiness, a pole witness, the part values and denominators being what they are — are all
discharged here by `decide`, `fin_cases` and `norm_num` rather than assumed. **No mass, no
propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootAtPartValue

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularPoleNotPartValue

/-! ## 1. The graph: `K_{1,3,3}` -/

/-- Parts of sizes `1, 3, 3`. -/
abbrev Part133 : Fin 3 → Type := fun i => Fin (2 * min i.1 1 + 1)

theorem card_part133 : Fintype.card (Σ i, Part133 i) = 7 := by
  simp [Fintype.card_sigma, Fin.sum_univ_three]

theorem nonempty_part133 (i : Fin 3) : Nonempty (Part133 i) := ⟨⟨0, by omega⟩⟩

/-- The part values are `6, 4, 4`. -/
theorem part_value_ne_part133 {μ : ℝ} (h6 : μ ≠ 6) (h4 : μ ≠ 4) (i : Fin 3) :
    ((Fintype.card (Σ i, Part133 i) : ℝ) - Fintype.card (Part133 i)) ≠ μ := by
  rw [card_part133, Fintype.card_fin]
  fin_cases i
  · intro h; exact h6 (by norm_num at h; linarith)
  · intro h; exact h4 (by norm_num at h; linarith)
  · intro h; exact h4 (by norm_num at h; linarith)

/-- The poles are `5, 1, 1`. -/
theorem denom_ne_zero_part133 {μ : ℝ} (h5 : μ ≠ 5) (h1 : μ ≠ 1) (i : Fin 3) :
    ((Fintype.card (Σ i, Part133 i) : ℝ) - 2 * Fintype.card (Part133 i) - μ) ≠ 0 := by
  rw [card_part133, Fintype.card_fin]
  fin_cases i
  · intro h; exact h5 (by norm_num at h; linarith)
  · intro h; exact h1 (by norm_num at h; linarith)
  · intro h; exact h1 (by norm_num at h; linarith)

/-! ## 2. A part value that is also a secular root -/

theorem secularSum_part133_four : secularSum (V := Part133) 4 = -1 := by
  unfold secularSum
  rw [Fin.sum_univ_three, card_part133]
  norm_num

theorem part_value_four :
    ((Fintype.card (Σ i, Part133 i) : ℝ) - Fintype.card (Part133 1)) = 4 := by
  rw [card_part133]
  norm_num

/-- **IT HAPPENS, AND HERE IT IS.** Four files in this chain have written that nothing rules out a
part value coinciding with a secular root. Nothing does, because at `K_{1,3,3}` the part value
`N − 3 = 4` satisfies the secular equation. -/
theorem part_value_eq_secular_root :
    ∃ μ : ℝ, ((Fintype.card (Σ i, Part133 i) : ℝ) - Fintype.card (Part133 1)) = μ
      ∧ secularSum (V := Part133) μ = -1 :=
  ⟨4, part_value_four, secularSum_part133_four⟩

/-! ## 3. The multiplicity there, and the branch it inhabits -/

theorem card_three_part133 : Fintype.card {i : Fin 3 // Fintype.card (Part133 i) = 3} = 2 := by
  decide

theorem half_part133 (i : Fin 3) : 2 * Fintype.card (Part133 i) ≠ 3 := by
  revert i; decide

/-- **THE FIRST INHABITANT OF THE `+ 1` BRANCH.**
`UnbalancedMultipartiteSecularEquation.finrank_signless_size_secular_one` was written when the
criterion was proved and has never been applied: its hypothesis is that the secular equation holds
*at a part value*, which is exactly the coincidence above. Here `k₃ · (3 − 1) + 1 = 5`. -/
theorem finrank_signless_part133_four :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph Part133)) - (4 : ℝ) • LinearMap.id)) = 5 := by
  have h := finrank_signless_size_secular_one (V := Part133) (n := 3) (by norm_num)
    (by rw [card_part133]; norm_num) nonempty_part133 0 half_part133
    (by rw [card_part133, show ((7 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) = 4 by norm_num]
        exact secularSum_part133_four)
  rw [card_part133, show ((7 : ℕ) : ℝ) - ((3 : ℕ) : ℝ) = 4 by norm_num,
    card_three_part133] at h
  exact h.trans (by norm_num)

/-! ## 4. The rest of the spectrum -/

/-- The pole `1`, which is not a part value: `|T| − 1 = 2 − 1`. -/
theorem finrank_signless_part133_one :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph Part133)) - (1 : ℝ) • LinearMap.id)) = 1 := by
  have hk : Fintype.card {i : Fin 3 // 2 * Fintype.card (Part133 i) = 6} = 2 := by decide
  have h := finrank_signless_at_pole_off_part_values (V := Part133) (n := 6) nonempty_part133 1
    (by decide)
    (by rw [card_part133, show ((7 : ℕ) : ℝ) - ((6 : ℕ) : ℝ) = 1 by norm_num]
        intro i
        have hi := part_value_ne_part133 (μ := 1) (by norm_num) (by norm_num) i
        rwa [card_part133] at hi)
  rw [card_part133, show ((7 : ℕ) : ℝ) - ((6 : ℕ) : ℝ) = 1 by norm_num, hk] at h
  exact h

/-- **AND A POLE THAT IS NOT AN EIGENVALUE AT ALL**: `|T| − 1 = 1 − 1`. -/
theorem finrank_signless_part133_five :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph Part133)) - (5 : ℝ) • LinearMap.id)) = 0 := by
  have hk : Fintype.card {i : Fin 3 // 2 * Fintype.card (Part133 i) = 2} = 1 := by decide
  have h := finrank_signless_at_pole_off_part_values (V := Part133) (n := 2) nonempty_part133 0
    (by decide)
    (by rw [card_part133, show ((7 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) = 5 by norm_num]
        intro i
        have hi := part_value_ne_part133 (μ := 5) (by norm_num) (by norm_num) i
        rwa [card_part133] at hi)
  rw [card_part133, show ((7 : ℕ) : ℝ) - ((2 : ℕ) : ℝ) = 5 by norm_num, hk] at h
  exact h

theorem secularSum_part133_nine : secularSum (V := Part133) 9 = -1 := by
  unfold secularSum
  rw [Fin.sum_univ_three, card_part133]
  norm_num

/-- The other secular root, which is neither a part value nor a pole. -/
theorem finrank_signless_part133_nine :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph Part133)) - (9 : ℝ) • LinearMap.id)) = 1 :=
  finrank_signless_eigenspace_secular_one nonempty_part133 0
    (part_value_ne_part133 (by norm_num) (by norm_num))
    (denom_ne_zero_part133 (by norm_num) (by norm_num)) secularSum_part133_nine

/-! ## 5. The three multiplicities add to the vertex count -/

/-- **THE CHECK THAT WOULD FAIL IF THE OVERLAP HAD BEEN MISCOUNTED.** `1 + 5 + 1 = 7`. -/
theorem finrank_signless_part133_add :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph Part133)) - (1 : ℝ) • LinearMap.id))
    + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph Part133)) - (4 : ℝ) • LinearMap.id))
    + Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (completeMultipartiteGraph Part133)) - (9 : ℝ) • LinearMap.id))
      = Fintype.card (Σ i, Part133 i) := by
  rw [finrank_signless_part133_one, finrank_signless_part133_four,
    finrank_signless_part133_nine, card_part133]

end SecularRootAtPartValue
