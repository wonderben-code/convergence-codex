import SecularSumZero

/-!
# The secular sum at zero, by arithmetic — and it avoids an interval, not a point

**ENTRY 181 PROVED `secularSum 0 ≠ −1` BY COUNTING TWO-COLOURABLE COMPONENTS AND SAID IT DID NOT
KNOW A DIRECT ARGUMENT.** Its own fence adds: *a reader who wants one should not take this file as
evidence that it is hard.* It is not hard, and the direct argument proves **more** than the detour
did: the sum does not merely avoid `−1`, it avoids the whole interval `[−1, 0]`.

**The two cases.** Write `dᵢ = N − 2nᵢ`. At most one part can exceed half the vertices, so at most
one `dᵢ` is negative.

* **None is.** Then every term `nᵢ/dᵢ` is positive and so is the sum, which is already clear of
  `−1` with room to spare.
* **One is**, say at `i₀`. Put `D = 2n₀ − N > 0`. For every other part, `nᵢ + n₀ < N` — because a
  third part is inhabited — so `dᵢ > D` and hence `nᵢ/dᵢ < nᵢ/D`, **strictly**. The term at `i₀` is
  exactly `−n₀/D`, and the others sum to less than `(N − n₀)/D`. Adding, the total is less than
  `(N − 2n₀)/D = −1`.

The whole argument is two inequalities and one identity, and the place `3 ≤ r` enters is visible:
it is what makes the third part exist, hence what makes the second bound **strict**. At two parts
the bound is an equality, which is why `K_{1,3}` sits exactly on `−1`.

## What is proved

**`card_add_card_lt`** — two distinct parts do not fill the graph when a third is inhabited. This
is the whole content of the hypothesis `3 ≤ r`.

**`secularSum_zero_lt_neg_one`** — with a part exceeding half the vertices, the sum is **strictly
below** `−1`.

**`secularSum_zero_pos`** — with none, the sum is **positive**.

**`secularSum_zero_gap`** — so past two parts the sum is either positive or below `−1`, and **never
in `[−1, 0]`**. That is the sharpening: entry 181 excluded a point and this excludes an interval.

**`secularSum_zero_ne_neg_one_direct`** — entry 181's theorem again, now by arithmetic. Both proofs
are kept: they are independent, and the graph-theoretic one is the reason to believe the arithmetic
one was worth looking for.

## What is NOT here

* **THE GAP IS NOT SHOWN TO BE THE BEST ONE.** `[−1, 0]` is avoided; nothing says how much more is,
  and the examples suggest the bound is asymptotically tight only on the `−1` side — the sum at
  `(n, 1, 1)` tends to `−1` from below as `n` grows, while the positive side is bounded away from
  `0` by nothing this file computes. Not attempted (`ERRATUM 246`).
* **STILL ONLY AT `μ = 0`.** The argument is specific to that value: it uses `dᵢ = N − 2nᵢ` with no
  shift, and the sign analysis is what makes the two cases. Nothing here reaches `secularSum μ` for
  `μ ≠ 0`.
* **NO NEW GRAPH-THEORETIC CONSEQUENCE**, although one reading is available and is worth naming:
  **the sign of the secular sum at zero detects whether some part is a strict majority.** That is a
  restatement of the two cases, not a theorem this file adds.
* **THE OTHER MULTIPARTITE LEFTOVERS ARE UNTOUCHED**: the exact spectrum count, whether the `3s`
  bound is attained, a characterisation of when a part value is a secular root, and the root
  values.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `Fintype ι` and `∀ i, Fintype (V i)` only —
**no `DecidableEq` anywhere**, because nothing here builds a graph; `∀ i, Nonempty (V i)`;
`3 ≤ Fintype.card ι`, whose role is now visible rather than inherited; and on the two halves
separately, the sign hypothesis that splits the cases. **No mass, no propagator, and no metric
anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularSumZeroGap

open Matrix Finset SimpleGraph
open UnbalancedMultipartite UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, Fintype (V i)]

/-- Two distinct parts do not fill the graph when a third is inhabited. -/
theorem card_add_card_lt (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι) {i j : ι}
    (hij : i ≠ j) : Fintype.card (V i) + Fintype.card (V j) < Fintype.card (Σ i, V i) := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, k ∉ ({i, j} : Finset ι) := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    have hle := Finset.card_le_card (fun x _ => hc x : (Finset.univ : Finset ι) ⊆ {i, j})
    rw [Finset.card_univ, Finset.card_insert_of_notMem (by simp [hij]),
      Finset.card_singleton] at hle
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hki, hkj⟩ := hk
  have hpos : 0 < Fintype.card (V k) := Fintype.card_pos_iff.mpr (hne k)
  have hmem : i ∉ ({j, k} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hij, fun h => hki h.symm⟩
  have htrip : ∑ x ∈ ({i, j, k} : Finset ι), Fintype.card (V x)
      = Fintype.card (V i) + Fintype.card (V j) + Fintype.card (V k) := by
    rw [Finset.sum_insert hmem, Finset.sum_pair (Ne.symm hkj)]; ring
  have hle : ∑ x ∈ ({i, j, k} : Finset ι), Fintype.card (V x) ≤ Fintype.card (Σ i, V i) := by
    rw [Fintype.card_sigma]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [htrip] at hle
  omega

/-! ## 2. One part bigger than half: the sum is strictly below `−1` -/

theorem secularSum_zero_lt_neg_one (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι)
    (i₀ : ι) (hbig : Fintype.card (Σ i, V i) < 2 * Fintype.card (V i₀)) :
    secularSum (V := V) 0 < -1 := by
  classical
  set N : ℝ := (Fintype.card (Σ i, V i) : ℝ) with hN
  set D : ℝ := 2 * (Fintype.card (V i₀) : ℝ) - N with hD
  have hcast : ((Fintype.card (Σ i, V i) : ℕ) : ℝ) < ((2 * Fintype.card (V i₀) : ℕ) : ℝ) := by
    exact_mod_cast hbig
  push_cast at hcast
  have hDpos : 0 < D := by rw [hD, hN]; linarith
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  have hsplit : secularSum (V := V) 0
      = (Fintype.card (V i₀) : ℝ) / (N - 2 * Fintype.card (V i₀))
        + ∑ i ∈ Finset.univ.erase i₀,
            (Fintype.card (V i) : ℝ) / (N - 2 * Fintype.card (V i)) := by
    unfold secularSum
    simp only [sub_zero]
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have hnegD : N - 2 * (Fintype.card (V i₀) : ℝ) = -D := by rw [hD]; ring
  have hzero : (Fintype.card (V i₀) : ℝ) / (N - 2 * Fintype.card (V i₀))
      = -((Fintype.card (V i₀) : ℝ) / D) := by rw [hnegD, div_neg]
  have hterm : ∀ i ∈ Finset.univ.erase i₀,
      (Fintype.card (V i) : ℝ) / (N - 2 * Fintype.card (V i)) < (Fintype.card (V i) : ℝ) / D := by
    intro i hi
    have hne' : i ≠ i₀ := (Finset.mem_erase.mp hi).1
    have hlt := card_add_card_lt hne h3 hne'
    have hposi : (0 : ℝ) < Fintype.card (V i) := by
      exact_mod_cast Fintype.card_pos_iff.mpr (hne i)
    have hc : ((Fintype.card (V i) + Fintype.card (V i₀) : ℕ) : ℝ) < N := by
      rw [hN]; exact_mod_cast hlt
    push_cast at hc
    have hDlt : D < N - 2 * (Fintype.card (V i) : ℝ) := by rw [hD]; linarith
    exact div_lt_div_of_pos_left hposi hDpos hDlt
  have hne2 : (Finset.univ.erase i₀).Nonempty := by
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card ι) i₀
    exact ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
  have hsum := Finset.sum_lt_sum_of_nonempty hne2 hterm
  have hs : ∑ i, (Fintype.card (V i) : ℝ) = N := by
    rw [hN, Fintype.card_sigma]; push_cast; rfl
  have hrest : ∑ i ∈ Finset.univ.erase i₀, (Fintype.card (V i) : ℝ) / D
      = (N - Fintype.card (V i₀)) / D := by
    rw [← Finset.sum_div]
    congr 1
    have hadd : ((Fintype.card (V i₀) : ℝ))
        + ∑ i ∈ Finset.univ.erase i₀, (Fintype.card (V i) : ℝ) = N := by
      rw [← hs]
      exact Finset.add_sum_erase _ (fun i => (Fintype.card (V i) : ℝ)) (Finset.mem_univ i₀)
    linarith
  rw [hrest] at hsum
  have hfinal : -((Fintype.card (V i₀) : ℝ) / D) + (N - Fintype.card (V i₀)) / D = -1 := by
    field_simp
    rw [hD]; ring
  rw [hsplit, hzero]
  linarith

/-! ## 3. No part bigger than half: every term is positive -/

theorem secularSum_zero_pos (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    (hsmall : ∀ i, 2 * Fintype.card (V i) < Fintype.card (Σ i, V i)) :
    0 < secularSum (V := V) 0 := by
  classical
  unfold secularSum
  simp only [sub_zero]
  refine Finset.sum_pos (fun i _ => div_pos ?_ ?_) Finset.univ_nonempty
  · exact_mod_cast Fintype.card_pos_iff.mpr (hne i)
  · have hc : ((2 * Fintype.card (V i) : ℕ) : ℝ) < (Fintype.card (Σ i, V i) : ℝ) := by
      exact_mod_cast hsmall i
    push_cast at hc
    linarith

/-! ## 4. So the sum avoids the whole interval `[−1, 0]`, which is more than `≠ −1` -/

/-- **THE GAP.** Past two parts the secular sum at zero is either positive or strictly below `−1`;
it never lands in `[−1, 0]`. -/
theorem secularSum_zero_gap (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι)
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ Fintype.card (Σ i, V i)) :
    0 < secularSum (V := V) 0 ∨ secularSum (V := V) 0 < -1 := by
  classical
  by_cases hb : ∃ i, Fintype.card (Σ i, V i) < 2 * Fintype.card (V i)
  · obtain ⟨i₀, h⟩ := hb
    exact Or.inr (secularSum_zero_lt_neg_one hne h3 i₀ h)
  · refine Or.inl (secularSum_zero_pos hne ?_ (fun i => ?_))
    · exact Fintype.card_pos_iff.mp (by omega)
    · have h1 := not_exists.mp hb i
      have h2 := hhalf i
      omega

/-- **AND THE ARITHMETIC PROOF OF ENTRY 181'S THEOREM.** `SecularSumZero.secularSum_zero_ne_neg_one`
proves this by counting two-colourable components; that file recorded that no direct argument was
known to it, and this is one. -/
theorem secularSum_zero_ne_neg_one_direct (hne : ∀ i, Nonempty (V i)) (h3 : 3 ≤ Fintype.card ι)
    (hhalf : ∀ i, 2 * Fintype.card (V i) ≠ Fintype.card (Σ i, V i)) :
    secularSum (V := V) 0 ≠ -1 := by
  intro h
  rcases secularSum_zero_gap hne h3 hhalf with hp | hn <;> rw [h] at * <;> linarith

end SecularSumZeroGap
