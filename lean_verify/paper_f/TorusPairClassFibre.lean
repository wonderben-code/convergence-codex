import TorusOrbitCharacterisation

/-!
# How many coordinates carry a given mirror pair: two, except at the two fixed points

`TorusOrbitCharacterisation.mem_orbit_iff` says the hyperoctahedral orbits are exactly the fibres
of the multiset of mirror pairs, and `MultinomialFibreCount.card_matching_of_sum` counts the
functions with prescribed fibre sizes. Between them and the orbit count
`2^s · d! / (m₁! ⋯ m_r!)` sits one arithmetic fact nobody had written down: **a mirror pair has two
members, except the two that are their own mirror.**

> **`card_pairClass_fibre`** — the coordinates sharing `v₀`'s mirror pair number **2** when `v₀` is
> interior (`0 < v₀` and `2v₀ ≠ n`) and **1** otherwise. The predicate is
> `TorusReflectionCount.mem_interiorAxes`'s, unchanged, which is what makes this the `2^s` the
> orbit formula carries.

**This is where `pairClass_eq_iff` earns its keep**: it turns *"same class"* into *"equal or summing
to `n`"*, and the whole content is then that `n − v₀` is a second, different coordinate exactly
when `v₀` is neither `0` nor `n/2`.

## What this is NOT

**It is not the orbit count.** That needs this, `mem_orbit_iff`, and
`MultinomialFibreCount.card_matching_of_sum` assembled — the orbit fibred over the class function,
each fibre a product of these preimages — and **the assembly is not here**, as of 31 August 2026.
No cost is offered for it (`ERRATUM 194`, `ERRATUM 246`).
-/

namespace TorusPairClassFibre

open Finset TorusOrbitInvariant TorusOrbitCharacterisation

variable {d : ℕ}

/-- **A MIRROR PAIR HAS TWO MEMBERS, EXCEPT AT THE TWO FIXED POINTS OF THE MIRROR.** The condition
is `TorusReflectionCount.mem_interiorAxes`'s, so this is the `2` that the orbit formula's `2^s`
counts. -/
theorem card_pairClass_fibre {N : ℕ} (v₀ : Fin (N + 3)) :
    (univ.filter fun v : Fin (N + 3) => pairClass N v.val = pairClass N v₀.val).card
      = if 0 < v₀.val ∧ 2 * v₀.val ≠ N + 3 then 2 else 1 := by
  classical
  have hmem : ∀ v : Fin (N + 3),
      pairClass N v.val = pairClass N v₀.val ↔ (v.val = v₀.val ∨ v.val + v₀.val = N + 3) :=
    fun v => pairClass_eq_iff v.isLt v₀.isLt
  by_cases hint : 0 < v₀.val ∧ 2 * v₀.val ≠ N + 3
  · rw [if_pos hint]
    obtain ⟨hpos, hne⟩ := hint
    have hwlt : N + 3 - v₀.val < N + 3 := by omega
    set w : Fin (N + 3) := ⟨N + 3 - v₀.val, hwlt⟩ with hw
    have hset : (univ.filter fun v : Fin (N + 3) =>
        pairClass N v.val = pairClass N v₀.val) = {v₀, w} := by
      ext v
      have hv := v.isLt
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, hmem]
      constructor
      · rintro (h | h)
        · exact Or.inl (Fin.ext h)
        · refine Or.inr (Fin.ext ?_)
          simp only [hw]
          omega
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · right
          simp only [hw]
          omega
    rw [hset, card_insert_of_notMem, card_singleton]
    simp only [mem_singleton]
    intro hcon
    have := congrArg Fin.val hcon
    simp only [hw] at this
    omega
  · rw [if_neg hint]
    have hset : (univ.filter fun v : Fin (N + 3) =>
        pairClass N v.val = pairClass N v₀.val) = {v₀} := by
      ext v
      have hv := v.isLt
      have hv₀ := v₀.isLt
      simp only [mem_filter, mem_univ, true_and, mem_singleton, hmem]
      constructor
      · rintro (h | h)
        · exact Fin.ext h
        · refine Fin.ext ?_
          push Not at hint
          omega
      · rintro rfl
        exact Or.inl rfl
    rw [hset, card_singleton]

/-- **THE SAME STATEMENT AS THE ORBIT FORMULA READS IT**: the fibre has two members exactly on the
interior axes, which is the set `2 ^ (interiorAxes k).card` is taken over. -/
theorem card_pairClass_fibre_eq_two_iff {N : ℕ} (v₀ : Fin (N + 3)) :
    (univ.filter fun v : Fin (N + 3) => pairClass N v.val = pairClass N v₀.val).card = 2
      ↔ (0 < v₀.val ∧ 2 * v₀.val ≠ N + 3) := by
  rw [card_pairClass_fibre]
  by_cases hint : 0 < v₀.val ∧ 2 * v₀.val ≠ N + 3 <;> simp [hint]

end TorusPairClassFibre
