import SignlessPart133Complete

/-!
# The secular sum at zero, and why it is never `−1` past two parts

**THREE ENTRIES FENCED THE SAME CASE.** Entries 171, 172 and 174 each say that when **no** part
holds half the vertices the set `T` is empty, the secular statements are silent, and
`UnbalancedMultipartiteSecularEquation.ker_secularMap_eq_bot` would supply the answer if only
`secularSum 0 ≠ −1` were known — *which is not established*. It is established here, and the proof
is graph theory rather than arithmetic.

**The route.** At three or more nonempty parts the graph is connected and not two-colourable, so
`MultipartiteSignlessKernel.finrank_ker_signless_zero_of_three_parts` says `Q`'s kernel is zero. No
part is the whole graph, so `UnbalancedMultipartiteSecular.finrank_signless_eigenspace_of_ne`
identifies that kernel with the secular kernel at `0`. A nontrivial secular kernel is exactly what
`secularSum 0 = −1` would force. So the sum is not `−1`.

## What is proved

**`card_ne_card_sigma`** — no part is the whole graph once there are two of them and both are
inhabited, which is the side condition the identification needs.

**`secularSum_zero_ne_neg_one`** — **`secularSum 0 ≠ −1` at three or more nonempty parts with no
half-sized part.**

**`sum_ne_neg_one`** — the same with the definition unfolded, which is what it looks like as
arithmetic: for any three or more positive integers `n₁, …, n_r` summing to `N`, none of them with
`2nᵢ = N`,
`∑ᵢ nᵢ / (N − 2nᵢ) ≠ −1`. **A statement about a sum of rationals, proved by counting two-colourable
connected components.**

**`ker_secularMap_zero_eq_bot`** — so the complement case closes: the secular kernel at `0` is
trivial exactly where the three fences said nothing.

**`Part13`, `secularSum_part13_zero`** — **and the hypothesis has bite.** At `K_{1,3}` the sum is
exactly `−1` — `1/2 − 3/2` — and every other hypothesis of the theorem holds there: both parts are
inhabited and neither is half of four. The only thing that fails is `3 ≤ r`, so that hypothesis is
doing the work and is not decoration.

## What is NOT here

* **ONLY AT `μ = 0`.** Nothing is said about `secularSum μ` at any other `μ`, and the route used
  here does not generalise: it runs through the kernel of `Q`, which is the eigenvalue `0` and
  nothing else.
* **NO ARITHMETIC PROOF.** The statement `∑ᵢ nᵢ/(N − 2nᵢ) ≠ −1` is elementary to state and this
  file does not prove it elementarily — it proves it by building a graph, counting its
  two-colourable components and reading the answer back. **I do not know a short direct argument**,
  and none is attempted (`ERRATUM 246`). A reader who wants one should not take this file as
  evidence that it is hard.

⚠ **THERE IS ONE, IT IS SHORT, AND THE PARAGRAPH IS KEPT AS WRITTEN** (`ERRATUM 94`, 2026-09-12
entry 182). `SecularSumZeroGap` gives it in two inequalities and an identity, and it proves
**more**: past two parts the sum is either positive or strictly below `−1`, so it avoids the whole
interval `[−1, 0]` and not merely the point. The sentence above was right to invite the search and
right not to price it as hard; what it got wrong is only that no argument was known, which was true
of this unit and not of the mathematics.

* **STILL NO CHARACTERISATION** of when a part value is a secular root, and no family in which the
  coincidence occurs — entry 173's fences on those stand.
* **THE OTHER MULTIPARTITE LEFTOVERS ARE UNTOUCHED**: the exact count of the spectrum, whether the
  `3s` bound is attained, and the root values.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances; `∀ i, Nonempty (V i)` throughout; `3 ≤ Fintype.card ι`, whose necessity `K_{1,3}`
witnesses; and `∀ i, 2nᵢ ≠ N`, which is what makes the sum defined at all. **No mass, no
propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularSumZero

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation MultipartiteSignlessKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- No part is the whole graph, once there are two of them and both are inhabited. -/
theorem card_ne_card_sigma (hne : ∀ i, Nonempty (V i)) (h2 : 2 ≤ Fintype.card ι) (i : ι) :
    Fintype.card (V i) ≠ Fintype.card (Σ i, V i) := by
  classical
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  have hpos : 0 < Fintype.card (V j) := Fintype.card_pos_iff.mpr (hne j)
  have hpair : ∑ k ∈ ({i, j} : Finset ι), Fintype.card (V k)
      = Fintype.card (V i) + Fintype.card (V j) := Finset.sum_pair (Ne.symm hj)
  have hsum : Fintype.card (V i) + Fintype.card (V j) ≤ Fintype.card (Σ i, V i) := by
    rw [Fintype.card_sigma, ← hpair]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  omega

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **THE SECULAR SUM AT ZERO IS NOT `−1` PAST TWO PARTS.** An arithmetic statement about a sum of
rationals, proved by counting two-colourable components. -/
theorem secularSum_zero_ne_neg_one (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι)
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ Fintype.card (Σ i, V i)) :
    secularSum (V := V) 0 ≠ -1 := by
  classical
  intro hs
  have hval : ∀ i : ι, ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) ≠ 0 := by
    intro i h
    exact card_ne_card_sigma hne (by omega) i
      (by exact_mod_cast (by linarith :
        (Fintype.card (V i) : ℝ) = (Fintype.card (Σ i, V i) : ℝ)))
  have hd : ∀ i : ι,
      ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) - 0) ≠ 0 := by
    intro i h
    exact hhalf i (by exact_mod_cast (by push_cast; linarith :
      ((2 * Fintype.card (V i) : ℕ) : ℝ) = (Fintype.card (Σ i, V i) : ℝ)))
  obtain ⟨i₀⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  refine ker_secularMap_ne_bot hne i₀ hd hs ?_
  have hz := finrank_ker_signless_zero_of_three_parts (V := V) hne h3
  rw [show (Matrix.toLin' (signlessLap (completeMultipartiteGraph V)))
      = Matrix.toLin' (signlessLap (completeMultipartiteGraph V)) - (0 : ℝ) • LinearMap.id by simp,
    finrank_signless_eigenspace_of_ne hne hval] at hz
  exact Submodule.finrank_eq_zero.mp hz


omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- The same statement with `secularSum` unfolded, which is what it looks like as arithmetic. -/
theorem sum_ne_neg_one (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι)
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ Fintype.card (Σ i, V i)) :
    ∑ i, (Fintype.card (V i) : ℝ)
        / ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i)) ≠ -1 := by
  classical
  have h := secularSum_zero_ne_neg_one hne h3 hhalf
  unfold secularSum at h
  simpa using h

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **SO THE COMPLEMENT CASE CLOSES.** `MultipartiteSignlessKernel`'s fence said the case with no
half-sized part needed exactly this, and now has it. -/
theorem ker_secularMap_zero_eq_bot (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι)
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ Fintype.card (Σ i, V i)) :
    (secularMap (V := V) 0).ker = ⊥ := by
  classical
  refine ker_secularMap_eq_bot (fun i h => ?_) (secularSum_zero_ne_neg_one hne h3 hhalf)
  exact hhalf i (by exact_mod_cast (by push_cast; linarith :
    ((2 * Fintype.card (V i) : ℕ) : ℝ) = (Fintype.card (Σ i, V i) : ℝ)))

/-! ## 2. And at two parts it is false, so the hypothesis has bite -/

/-- `K_{1,3}`: parts of sizes `1` and `3`. -/
abbrev Part13 : Fin 2 → Type := fun i => Fin (2 * i.1 + 1)

theorem card_part13 : Fintype.card (Σ i, Part13 i) = 4 := by
  simp [Fintype.card_sigma, Fin.sum_univ_two]

theorem half_part13 (i : Fin 2) :
    2 * Fintype.card (Part13 i) ≠ Fintype.card (Σ i, Part13 i) := by
  rw [card_part13]; revert i; decide

/-- **AT `K_{1,3}` THE SUM IS EXACTLY `−1`**: `1/2 − 3/2`. Every hypothesis above holds here
except `3 ≤ r`, so that one is doing the work and is not decoration. -/
theorem secularSum_part13_zero : secularSum (V := Part13) 0 = -1 := by
  unfold secularSum
  rw [Fin.sum_univ_two, card_part13]
  norm_num

end SecularSumZero
