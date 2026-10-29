import Mathlib

/-!
# R8 · What every matching fixes is the trace: the third lineage from the first two

*The Refined Gaps* v1 §6.6 (R8): the Tree's L7 (POSTULATE) says End, Aut and ⟨·,·⟩ are *the* three
lineages. Chain Theory's Definition 1.6 says "what is known of a qudit is what all its reads, taken
jointly, fix with certainty, whichever way basis directions are matched", and its glossary gives the
nearest standard term as "the set of invariants fixed by the commutant of a stabilizer". R8 asks
whether a carrier (End), its symmetries (Aut), and a knowledge clause of this form are exactly three
aspects, with any fourth a function of them.

The carrier is Mₙ(K), so its automorphisms are conjugations (Skolem–Noether, proved in the estate,
L11). The first question is: what linear "knowledge" of a single element is fixed by every
matching? This file proves that the answer is the trace, and nothing else.

* `eq_smul_trace_of_comm` (the infinitesimal form): a linear functional with f(ab) = f(ba),
  i.e. one vanishing on every commutator, is c · trace.
* `eq_smul_trace_of_conj_invariant` (the finite form): a linear functional invariant under
  conjugation by every invertible matrix is c · trace. Only transvections 1 + Eᵢⱼ are used, so no
  assumption on the characteristic is needed.

From the trace state the GNS construction gives the Hilbert–Schmidt inner product ⟨x, y⟩ =
tr(x*y), which is the Tree's L21 (GNS on the trace state). So the third lineage, the pairing, is
**forced** by the first two (the carrier and its symmetries) under Chain Theory's knowledge clause.
That higher invariants add no fourth primitive (all of them are traces of products) is the First
Fundamental Theorem for matrices (Procesi 1976; Razmyslov 1974). It is cited here and checked by
exact computation for n ≤ 3, k ≤ 3 in `scripts/chain_theory/r8_known_generates_pairing.py`.

Genuine Mathlib proofs; no `sorry`, no `native_decide`, no new axioms.
-/

open Matrix

namespace ChainTheory.R8

variable {K : Type*} [Field K] {n : ℕ}

/-- Every matrix is the sum of its entries placed on matrix units. -/
private lemma apply_eq_sum (f : Matrix (Fin n) (Fin n) K →ₗ[K] K) (x : Matrix (Fin n) (Fin n) K) :
    f x = ∑ i, ∑ j, x i j * f (single i j 1) := by
  conv_lhs => rw [matrix_eq_sum_single x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show single i j (x i j) = x i j • single i j (1 : K) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, smul_eq_mul]

/-- The core: if f kills every off-diagonal matrix unit and takes one value on all diagonal ones,
it is a multiple of the trace. -/
private lemma eq_smul_trace_of_units (f : Matrix (Fin n) (Fin n) K →ₗ[K] K) (c : K)
    (hoff : ∀ i j, i ≠ j → f (single i j 1) = 0) (hdiag : ∀ i, f (single i i 1) = c)
    (x : Matrix (Fin n) (Fin n) K) : f x = c * x.trace := by
  rw [apply_eq_sum, trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [hdiag, mul_comm, diag_apply]
  · intro j _ hji
    rw [hoff i j (Ne.symm hji), mul_zero]
  · simp

/-- **The infinitesimal form.** A linear functional on Mₙ(K) that vanishes on commutators is a
multiple of the trace. -/
theorem eq_smul_trace_of_comm (f : Matrix (Fin n) (Fin n) K →ₗ[K] K)
    (hf : ∀ a b, f (a * b) = f (b * a)) :
    ∃ c : K, ∀ x, f x = c * x.trace := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, fun x => by simp [Subsingleton.elim x 0]⟩
  let i0 : Fin n := ⟨0, hn⟩
  refine ⟨f (single i0 i0 1), eq_smul_trace_of_units f _ ?_ ?_⟩
  · intro i j hij
    have := hf (single i i 1) (single i j 1)
    rw [single_mul_single_same, one_mul, single_mul_single_of_ne (h := Ne.symm hij), map_zero] at this
    exact this
  · intro i
    have := hf (single i i0 1) (single i0 i 1)
    rw [single_mul_single_same, single_mul_single_same] at this
    simpa using this

/-- **The finite form.** A linear functional on Mₙ(K) invariant under conjugation by every
invertible matrix (`g * h = 1`) is a multiple of the trace. Only transvections are used. -/
theorem eq_smul_trace_of_conj_invariant (f : Matrix (Fin n) (Fin n) K →ₗ[K] K)
    (hf : ∀ g h : Matrix (Fin n) (Fin n) K, g * h = 1 → ∀ x, f (g * x * h) = f x) :
    ∃ c : K, ∀ x, f x = c * x.trace := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, fun x => by simp [Subsingleton.elim x 0]⟩
  let i0 : Fin n := ⟨0, hn⟩
  -- products of matrix units used below
  have ss : ∀ i j : Fin n, i ≠ j → single i j (1 : K) * single i j 1 = 0 :=
    fun i j h => by simp [h.symm]
  have js : ∀ i j : Fin n, i ≠ j → single j j (1 : K) * single i j 1 = 0 :=
    fun i j h => by simp [h.symm]
  have u1 : ∀ i j k l : Fin n, j = k → single i j (1 : K) * single k l 1 = single i l 1 := by
    intro i j k l h; subst h; rw [single_mul_single_same, one_mul]
  -- the transvection pair g = 1 + E_ij, h = 1 - E_ij (i ≠ j)
  have inv : ∀ i j : Fin n, i ≠ j →
      (1 + single i j (1 : K)) * (1 - single i j 1) = 1 := by
    intro i j hij
    rw [add_mul, one_mul, mul_sub, mul_one, ss i j hij]
    abel
  -- conjugating E_jj gives E_jj + E_ij, so f(E_ij) = 0
  have hoff : ∀ i j, i ≠ j → f (single i j (1 : K)) = 0 := by
    intro i j hij
    have h := hf _ _ (inv i j hij) (single j j 1)
    have e : (1 + single i j (1 : K)) * single j j 1 * (1 - single i j 1)
        = single j j 1 + single i j 1 := by
      rw [add_mul, one_mul, u1 i j j j rfl, add_mul, mul_sub, mul_sub, mul_one, mul_one,
        js i j hij, ss i j hij]
      abel
    rw [e, map_add] at h
    linear_combination h
  -- conjugating E_ji gives E_ji + E_ii - E_jj - E_ij, so f(E_ii) = f(E_jj)
  have hdiag : ∀ i j, i ≠ j → f (single i i (1 : K)) = f (single j j 1) := by
    intro i j hij
    have h := hf _ _ (inv i j hij) (single j i 1)
    have e : (1 + single i j (1 : K)) * single j i 1 * (1 - single i j 1)
        = single j i 1 + single i i 1 - single j j 1 - single i j 1 := by
      rw [add_mul, one_mul, u1 i j j i rfl, add_mul, mul_sub, mul_sub, mul_one, mul_one,
        u1 j i i j rfl, u1 i i i j rfl]
      abel
    rw [e, map_sub, map_sub, map_add, hoff i j hij] at h
    linear_combination h
  refine ⟨f (single i0 i0 1), eq_smul_trace_of_units f _ hoff fun i => ?_⟩
  by_cases h : i = i0
  · rw [h]
  · exact hdiag i i0 h

end ChainTheory.R8
