import TorusHyperoctahedral
import CycleMultiplicityCount

/-!
# The `2^d · d!` bound is about something, and in one dimension it is exact

`TorusHyperoctahedral` proves `2^d · d! ≤ dim` under three hypotheses on the frequency — the
coordinates pairwise distinct, none at rest, no two mirrors of each other — and its header calls
such a frequency *generic* without ever exhibiting one. **A theorem with three hypotheses and no
witness is a theorem that might be about the empty set**, and this estate has a standing habit of
checking that before moving on (`IndefiniteCoupling` §4 is the same move).

> **`ladderFreq`** — the frequency `(1, 2, …, d)`, at any side length with `2d < n`. Named against
> `LadderStep.ladder`, which is the Stein ladder and unrelated.
>
> **`ladderFreq_injective`, `ladderFreq_pos`, `ladderFreq_sum_ne`** — it satisfies all three
> hypotheses, and each proof is one `omega` from `i < d` and `2d < n`.
>
> **`hyperoctahedral_le_at_ladder`** — hence `2^d · d! ≤ dim` at an actual frequency. **The bound
> is not vacuous** whenever the side length exceeds twice the dimension.

## And the bound is exact in the one case where the exact answer is known

> **`hyperoctahedral_exact_dim_one`** — at `d = 1` the hypotheses reduce to *interior* — `k ≠ 0` and
> `2k ≠ n` — and `CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` says the dimension is
> **exactly** `2`, which is `2^1 · 1!`. So the general lower bound is **attained**, and the estate's
> one exact multiplicity is the `d = 1` case of it.

That is a check rather than a theorem about `d ≥ 2`, and it is worth having for the reason
`ERRATUM 201` gives: a general statement that cannot recover the special case it generalises has
not been checked against anything.

## What is NOT here

**No proportion, and *generic* is still an informal word.** The number of frequencies satisfying
the three hypotheses is a finite combinatorial quantity — `2^d` times a descending factorial in
`⌊(n−1)/2⌋`, by pairing each value with its mirror — and **nothing below counts it**. One witness
is exhibited; a density is not, and none is guessed at (`ERRATUM 194`, `ERRATUM 246`).

**No upper bound at `d ≥ 2`, and `TorusNonReflectionCollision.sporadic_nuR_eq` says none can come
from symmetry.** Exactness at `d = 1` is not evidence of exactness anywhere else — at side `12` in
two dimensions there is a collision outside the group entirely.

**`2d < n` is a sufficient condition on the witness, not a necessary one on the hypotheses.** Other
frequencies satisfy them at smaller side lengths; the ladder is chosen because its three proofs
are one `omega` each.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusGenericFrequency

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusHyperoctahedral

variable {d : ℕ}

/-! ## 1. A frequency the hypotheses are about -/

/-- **THE LADDER `(1, 2, …, d)`**, at any side length with `2d < n`. -/
def ladderFreq {N : ℕ} (hd : 2 * d < N + 3) : Site d (N + 3) :=
  fun i => ⟨i.val + 1, by have := i.isLt; omega⟩

theorem ladderFreq_val {N : ℕ} (hd : 2 * d < N + 3) (i : Fin d) :
    ((ladderFreq (N := N) hd) i).val = i.val + 1 := rfl

/-- The coordinates are pairwise distinct. -/
theorem ladderFreq_injective {N : ℕ} (hd : 2 * d < N + 3) :
    Function.Injective (ladderFreq (N := N) hd) := by
  intro i j hij
  have := congrArg Fin.val hij
  rw [ladderFreq_val, ladderFreq_val] at this
  exact Fin.ext (by omega)

/-- None is at rest. -/
theorem ladderFreq_pos {N : ℕ} (hd : 2 * d < N + 3) (i : Fin d) :
    0 < ((ladderFreq (N := N) hd) i).val := by
  rw [ladderFreq_val]; omega

/-- No two are mirrors of each other — and at `i = j` this is *not the halfway frequency*. -/
theorem ladderFreq_sum_ne {N : ℕ} (hd : 2 * d < N + 3) (i j : Fin d) :
    ((ladderFreq (N := N) hd) i).val + ((ladderFreq (N := N) hd) j).val ≠ N + 3 := by
  rw [ladderFreq_val, ladderFreq_val]
  have hi := i.isLt
  have hj := j.isLt
  omega

/-- **THE BOUND IS NOT VACUOUS.** At the ladder frequency, `2^d · d! ≤ dim`, whenever the side
length exceeds twice the dimension. -/
theorem hyperoctahedral_le_at_ladder (N : ℕ) (m : ℝ) (hd : 2 * d < N + 3) :
    2 ^ d * Nat.factorial d ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m)
        - (nuR N m (ladderFreq (N := N) hd)) • LinearMap.id)) :=
  hyperoctahedral_le_finrank_eigenspace N m _ (ladderFreq_injective hd) (ladderFreq_pos hd)
    (ladderFreq_sum_ne hd)

/-! ## 2. And in one dimension the bound is attained -/

/-- **THE `d = 1` CASE IS EXACT.** The hypotheses reduce to *interior*, and
`CycleMultiplicityCount.finrank_eigenspace_interior_eq_two` gives the dimension as exactly `2`,
which is `2^1 · 1!`. The general bound recovers the estate's one exact multiplicity. -/
theorem hyperoctahedral_exact_dim_one (N : ℕ) (m : ℝ) (k : Site 1 (N + 3))
    (hpos : ∀ i, 0 < (k i).val) (hsum : ∀ i j, (k i).val + (k j).val ≠ N + 3) :
    2 ^ 1 * Nat.factorial 1 = Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph 1 (N + 3)) m) - (nuR N m k) • LinearMap.id)) := by
  have hhalf : 2 * (k 0).val ≠ N + 3 := by
    have := hsum 0 0
    omega
  rw [CycleMultiplicityCount.finrank_eigenspace_interior_eq_two N m k (hpos 0) hhalf]
  norm_num

end TorusGenericFrequency
