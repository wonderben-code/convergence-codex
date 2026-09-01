import BoxLapBasis
import MultinomialFibreCount

/-!
# How many frequency vectors share a box eigenvalue: at least the multinomial, and sometimes more

`BoxMassiveSpectrum`'s closure of `UNLOCK_WATCHLIST`'s *a BOX is not a circulant* item lists four
things it does **not** prove, and `STATUS (21)`'s item (a) is the first: *"No multiplicity. Which
frequency vectors share an eigenvalue is not asked."* This file asks it, and the answer has the same
shape as on the torus — a group-theoretic lower bound that is **not** the whole story.

> **`boxLapEig_comp_perm`** — the eigenvalue is invariant under **permuting the axes**, because it
> is a sum over axes of a function of one coordinate. One line (`Equiv.sum_comp`).
>
> **`multinomial_le_card_eigFibre`** — hence the set of frequency vectors sharing an eigenvalue has
> at least `d! / ∏ mᵢ!` elements, `mᵢ` the multiplicities of the distinct frequencies.
> `MultinomialFibreCount.card_matching` counts that orbit exactly.
>
> **`sporadic_eq`** and **`sporadic_not_perm`** — **and the bound is not tight.** At `d = 2` and
> side length `6`, the frequency vectors `(0, 3)` and `(2, 2)` give the same eigenvalue —
> `cos 0 + cos(π/2) = 1 + 0` against `cos(π/3) + cos(π/3) = ½ + ½` — and **no permutation carries
> one to the other**, `(2, 2)` being constant. So the fibre there has at least `3` elements where
> the orbit has `2`.

## Where the box differs from the torus, and it is the reflections

`TorusReflectionCount` gets a factor `2^s` on the torus because `k` and `n − k` give the **same**
eigenvalue there. **On the box they do not**: `2 − 2cos((n−k)π/n) = 2 + 2cos(kπ/n)`, which equals
`2 − 2cos(kπ/n)` only when the cosine vanishes. **So the box's symmetry group is `S_d` alone**, and
the multinomial is the whole group-theoretic contribution rather than `2^s · d!/∏mᵢ!`. That is a
real structural difference between the two lattices and not a gap in this file.

## What this is NOT

**It is not the multiplicity**, and the sporadic witness is exactly why: the fibre can exceed the
orbit. **No formula is offered**, no upper bound is proved, and as of 31 Aug 2026 neither is costed
(`ERRATUM 194`, `ERRATUM 246`).

**It is a fibre count, not an eigenspace dimension.** `BoxLapBasis.boxLapBasis` is a basis of
eigenvectors indexed by sites, so the eigenspace for a value ought to be spanned by the basis
vectors in its fibre — **that identification is not proved here**, and nothing here says a
`finrank`.

**The sporadic witness is one witness.** No family is offered and it is not claimed smallest.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BoxLapMultiplicity

open Finset BoxGraph PathLapSpectrum BoxLapSpectrum BoxLapBasis

variable {d n : ℕ}

/-! ## 1. Permuting the axes does not move the eigenvalue -/

/-- **THE EIGENVALUE IS A SUM OVER AXES, SO A PERMUTATION REINDEXES IT.** -/
theorem boxLapEig_comp_perm (d n : ℕ) (k : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) :
    boxLapEig d n (k ∘ σ) = boxLapEig d n k :=
  Equiv.sum_comp σ fun i => 2 - 2 * Real.cos (2 * half n (k i))

/-! ## 2. The fibre, and the multinomial inside it -/

/-- The frequency vectors sharing `k`'s eigenvalue. -/
noncomputable def eigFibre (d n : ℕ) (k : Site d n) : Finset (Site d n) :=
  univ.filter fun l => boxLapEig d n (fun i => (l i).val) = boxLapEig d n (fun i => (k i).val)

/-- **AT LEAST THE MULTINOMIAL.** -/
theorem multinomial_le_card_eigFibre (d n : ℕ) (k : Site d n) :
    Nat.multinomial univ (fun a : Fin n => Fintype.card {i // k i = a})
      ≤ (eigFibre d n k).card := by
  classical
  rw [← MultinomialFibreCount.card_matching k]
  refine Finset.card_le_card fun g hg => ?_
  simp only [mem_filter, mem_univ, true_and] at hg
  obtain ⟨σ, hσ⟩ := MultinomialFibreCount.exists_perm_comp (f := g) (g := k) hg
  have hgk : (fun i => (g i).val) = (fun i => (k i).val) ∘ σ := by
    funext i
    exact congrArg Fin.val (hσ i).symm
  simp only [eigFibre, mem_filter, mem_univ, true_and, hgk]
  exact boxLapEig_comp_perm d n (fun i => (k i).val) σ

/-! ## 3. And it is not tight -/

/-- `cos 0 + cos(π/2) = 1 + 0` and `cos(π/3) + cos(π/3) = ½ + ½`, so at side length `6` the
frequency vectors `(0, 3)` and `(2, 2)` share an eigenvalue. -/
theorem sporadic_eq : boxLapEig 2 6 ![0, 3] = boxLapEig 2 6 ![2, 2] := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have e0 : 2 * half 6 0 = 0 := by rw [half]; push_cast; ring
  have e3 : 2 * half 6 3 = Real.pi / 2 := by rw [half]; push_cast; ring
  have e2 : 2 * half 6 2 = Real.pi / 3 := by rw [half]; push_cast; ring
  simp only [boxLapEig, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    e0, e3, e2, Real.cos_zero, Real.cos_pi_div_two, Real.cos_pi_div_three]
  ring

/-- **AND NO PERMUTATION CARRIES ONE TO THE OTHER**, `(2, 2)` being constant. -/
theorem sporadic_not_perm (σ : Equiv.Perm (Fin 2)) :
    (![0, 3] : Fin 2 → ℕ) ∘ σ ≠ (![2, 2] : Fin 2 → ℕ) := by
  intro hcon
  have h := congrFun hcon 0
  simp only [Function.comp_apply, Matrix.cons_val_zero] at h
  obtain ⟨j, hj⟩ : ∃ j, σ 0 = j := ⟨_, rfl⟩
  rw [hj] at h
  fin_cases j <;> simp_all

end BoxLapMultiplicity
