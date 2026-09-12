import SignlessSharpBracket

/-!
# Half of the sharpness condition is necessary, and the boundary case is exhibited

`SignlessSharpBracket` proved `#spec = 3s` under three conditions on the part sizes, and fenced the
obvious question: *"**THE THIRD CONDITION IS NOT SHOWN NECESSARY**, only sufficient."* That
condition is **every size less than twice every other**, and it has two halves — *no size is
**exactly** twice another*, and *no size is **more than** twice another*. **The first half is
necessary, and this file proves it.**

**Why, in one sentence.** If `nⱼ = 2nᵢ` then the pole `N − 2nᵢ` **is** the part value `N − nⱼ`, so
two of the three families share a member; the trichotomy's cover is `partValues ∪ poles ∪ roots`,
each of size `s`, and a shared member makes the union at most `3s − 1`. Since every eigenvalue is in
the cover, `#spec < 3s`. **Nothing about the spectrum is computed** — the argument is inclusion–
exclusion on three sets whose sizes the chain already knows.

## What is proved

> **`partValues_inter_poles_nonempty`** — a size that doubles another puts a pole on a part value.
> One `push_cast` and a `ring`.
>
> **`card_spectrum_lt_three_mul`** — hence **`#spec < 3s`** whenever some size is exactly twice
> another, with no other hypothesis on the sizes at all. The cover inclusion is
> `eigenvalue_trichotomy` case by case, with the not-a-pole clause the root set needs supplied by
> the branch that reaches it.
>
> **`P1122`, `card_spectrum_lt_P1122`** — the boundary case exhibited: `K_{1,1,2,2}`, where `2` is
> exactly twice `1` and every other condition that can hold does, has **fewer than six** distinct
> eigenvalues. `SignlessSharpBracket`'s three conditions would have given exactly six.

## What is NOT here

* **THE OTHER HALF IS NOT SHOWN NECESSARY.** *No size is **more than** twice another* is untouched.
  The evidence is one graph: `K_{1,3,3}` has `3 > 2·1`, is not sharp, and is not sharp for a
  **different reason** — there the pole and the part value are distinct and it is a **secular root**
  that lands on a part value (`SecularRootAtPartValue`). Whether every violation of that half costs
  sharpness, or only some, is **open and not attempted** (`ERRATUM 246`). So the third condition is
  now known necessary in one half and merely sufficient in the other.
* **NO EXACT COUNT AT `K_{1,1,2,2}`.** This gives `< 6` and does not say `5`. Pinning it needs the
  overlap counted exactly and the two secular roots shown distinct from everything else, which is
  the same assembly `SignlessSharpBracket` does under its hypotheses and which does not transfer.
* **NO MULTIPLICITIES, NO ROOT VALUES, NOTHING OVER `ℂ`.**
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` and `DecidableEq`
instances, `∀ i, Nonempty (V i)`, `Nonempty ι`, and **one equation between two sizes** — no lower
bound on any size, no multiplicity condition, nothing else. §1 omits both `DecidableEq`s. **No mass,
no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessDoublingFails

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularRootCount SecularRootExact

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. A size that doubles another puts a pole on a part value -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem partValues_inter_poles_nonempty {i j : ι}
    (hdouble : Fintype.card (V j) = 2 * Fintype.card (V i)) :
    ((partValues V) ∩ (poles V)).Nonempty := by
  classical
  refine ⟨(Fintype.card (Σ k, V k) : ℝ) - Fintype.card (V j), ?_⟩
  rw [Finset.mem_inter]
  constructor
  · exact (mem_partValues_iff (V := V) _).mpr ⟨j, rfl⟩
  · refine (mem_poles_iff (V := V) _).mpr ⟨i, ?_⟩
    rw [hdouble]
    push_cast
    ring

/-! ## 2. So the cover is short and the count is strictly below `3s` -/

theorem card_spectrum_lt_three_mul (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι)
    {i j : ι} (hdouble : Fintype.card (V j) = 2 * Fintype.card (V i)) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card < 3 * (Finset.univ.image (fun k : ι => Fintype.card (V k))).card := by
  classical
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  set sizes := Finset.univ.image (fun k : ι => Fintype.card (V k)) with hsizes
  have hsub : S ⊆ partValues V ∪ poles V ∪ R := by
    intro μ hμ
    have hx : IsEigen V μ := (hS μ).mp hμ
    by_cases hval : ∃ k, ((Fintype.card (Σ k, V k) : ℝ) - Fintype.card (V k)) = μ
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ ((mem_partValues_iff (V := V) _).mpr hval))
    by_cases hpole : ∃ k, ((Fintype.card (Σ k, V k) : ℝ) - 2 * Fintype.card (V k)) = μ
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ ((mem_poles_iff (V := V) _).mpr hpole))
    · rcases eigenvalue_trichotomy (V := V) hne (Classical.choice hι) hx with h | h | h
      · exact absurd h hval
      · exact absurd h hpole
      · refine Finset.mem_union_right _ ((hR μ).mpr ⟨h, fun k hk => ?_⟩)
        exact hpole ⟨k, by linarith⟩
  have hPQ : (partValues V ∪ poles V).card < 2 * sizes.card := by
    have h1 : (partValues V).card = sizes.card := card_partValues_eq_card_sizes (V := V)
    have h2 : (poles V).card = sizes.card := card_poles_eq_card_sizes (V := V)
    have hint := partValues_inter_poles_nonempty (V := V) hdouble
    have hcard := Finset.card_union_add_card_inter (partValues V) (poles V)
    have hpos : 0 < ((partValues V) ∩ (poles V)).card := Finset.card_pos.mpr hint
    omega
  have hle : (partValues V ∪ poles V ∪ R).card ≤ (partValues V ∪ poles V).card + R.card :=
    Finset.card_union_le _ _
  have := Finset.card_le_card hsub
  omega

/-! ## 3. The boundary case, exhibited -/

/-- Two parts of one and two parts of two: `2 = 2 · 1`, so the doubling clause fails **at the
boundary** rather than strictly, and every other condition of `SignlessSharpBracket` that can hold
does. -/
abbrev P1122 : Fin 4 → Type := fun i => Fin (1 + i.1 / 2)

theorem card_P1122 (i : Fin 4) : Fintype.card (P1122 i) = 1 + i.1 / 2 := by
  simp [P1122]

theorem sizes_P1122 :
    (Finset.univ.image (fun i : Fin 4 => Fintype.card (P1122 i))).card = 2 := by decide

theorem twice_P1122 : ∀ i : Fin 4, 2 ≤ Fintype.card {j : Fin 4 //
    Fintype.card (P1122 j) = Fintype.card (P1122 i)} := by decide

/-- **AND IT IS NOT SHARP**: fewer than `3s = 6` distinct eigenvalues. -/
theorem card_spectrum_lt_P1122 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1122 μ) ∧ S.card < 6 := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_lt_three_mul (V := P1122) (fun _ => ⟨0⟩) ⟨0⟩
    (i := 0) (j := 2) (by decide)
  rw [sizes_P1122] at hcard
  exact ⟨S, hS, by omega⟩

end SignlessDoublingFails
