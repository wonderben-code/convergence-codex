import SecularRootGap

/-!
# One secular eigenvalue for every distinct part size

**THE PREVIOUS UNIT SAID THE MATHEMATICS WAS FINISHED AND THE STATEMENT WAS NOT.** With a root above
the largest pole, none below the smallest, and exactly one in each gap, the number of solutions of
`∑ᵢ nᵢ/(N − 2nᵢ − μ) = −1` is settled — and saying so needed the distinct poles enumerated and
paired. **That is done here, and without sorting anything**: the successor of a pole `p` is the
`Finset.min'` of the poles above it, which is all "consecutive" ever meant.

## What is proved

**`poles`** — the distinct values `N − 2nᵢ`, as a `Finset ℝ`.
**`exists_root_above`** — for every pole `p` there is a root **above `p` and below every pole above
`p`**: the gap theorem when `p` has a successor, and the above-the-maximum theorem when it does not,
the two cases distinguished by whether the filter of larger poles is empty.

**`exists_roots_finset`** — those roots are **distinct**, and the argument is one line of order:
if `p < p'` then the root chosen at `p` is below `p'`, and the root chosen at `p'` is above `p'`, so
the choice function is strictly increasing on the poles and hence injective. The same two facts show
no chosen root is itself a pole, which is what the eigenvector construction needs.

**`card_poles_eq_card_sizes`** — the poles are in bijection with the **distinct part sizes**,
because `n ↦ N − 2n` is injective.

**`exists_eigenvalues_finset`** — **so `Q` has at least as many distinct eigenvalues off the part
values as the graph has distinct part sizes.** At `K₄` minus an edge that is two (sizes `1` and `2`;
the eigenvalues `3 ± √5`); at the three-vertex path two (`0` and `3`); at the equipartite family one
(`2(r−1)t`). In each the bound is attained.

## What is NOT here

* **THE MATCHING UPPER BOUND IS NOT PROVED**, so this is *at least*, not *exactly*, even though it
  is exactly in all three computed cases. What is missing is that **every** root lies in a gap or
  above the largest pole — which needs a root that is not a pole to be placed between the greatest
  pole below it and the least pole above it, and that placement is not written. Not attempted
  (`ERRATUM 246`); the three data points are data and not a theorem (`ERRATUM 194`).
* **NO STATEMENT ABOUT THE FULL SPECTRUM.** These eigenvalues are the ones the secular equation
  gives. The part values `N − nᵢ` are eigenvalues by a different route with their own
  multiplicities, and **nothing here adds the two counts together** — a part value could in
  principle coincide with a secular root, and no unit rules that out.
* **NO MULTIPLICITY.** Each of these is simple by entry 157, and that is not restated.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` instances;
`∀ i, Nonempty (V i)` and `Nonempty ι` throughout, the latter because a maximum over no poles has no
meaning and the former because a part of size zero contributes a vanishing term. `DecidableEq ι` is
**not** taken — the `Finset.image` and `Finset.filter` here are classical. **No mass, no propagator,
and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootCount

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularRootLocation SecularRootGap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-- The distinct poles of the secular sum: one for each distinct part size. -/
noncomputable def poles (V : ι → Type*) [Fintype ι] [∀ i, Fintype (V i)] : Finset ℝ := by
  classical
  exact Finset.image (fun i : ι => (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i))
    Finset.univ

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem mem_poles_iff (x : ℝ) :
    x ∈ poles V ↔ ∃ i : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) = x := by
  classical
  rw [poles]
  simp

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem pole_mem (i : ι) :
    (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i) ∈ poles V :=
  (mem_poles_iff _).mpr ⟨i, rfl⟩

/-! ## 1. Above each pole, a root below every larger pole -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem exists_root_above (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∀ p ∈ poles V, ∃ μ : ℝ, p < μ ∧ (∀ p' ∈ poles V, p < p' → μ < p')
      ∧ secularSum (V := V) μ = -1 := by
  classical
  intro p hp
  obtain ⟨i₀, hi₀⟩ := (mem_poles_iff (V := V) p).mp hp
  rcases Finset.eq_empty_or_nonempty ((poles V).filter (fun x => p < x)) with hL | hL
  · -- `p` is the largest pole
    have hmax : poleMax (V := V) hι ≤ p := by
      rw [poleMax]
      refine Finset.sup'_le _ _ fun k _ => ?_
      by_contra hcon
      have : (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)
          ∈ (poles V).filter (fun x => p < x) :=
        Finset.mem_filter.mpr ⟨pole_mem k, lt_of_not_ge hcon⟩
      rw [hL] at this
      simp at this
    have hple : p ≤ poleMax (V := V) hι := hi₀ ▸ le_poleMax hι i₀
    have hpeq : p = poleMax (V := V) hι := le_antisymm hple hmax
    obtain ⟨μ, hμp, hμ⟩ := exists_secular_root (V := V) hne hι
    refine ⟨μ, by rw [hpeq]; exact hμp, fun p' hp' hpp' => ?_, hμ⟩
    exfalso
    have hmem : p' ∈ (poles V).filter (fun x => p < x) := Finset.mem_filter.mpr ⟨hp', hpp'⟩
    rw [hL] at hmem
    simp at hmem
  · -- `p` has a successor among the poles
    set q := ((poles V).filter (fun x => p < x)).min' hL with hqdef
    have hqmem : q ∈ (poles V).filter (fun x => p < x) := Finset.min'_mem _ hL
    have hqpoles : q ∈ poles V := (Finset.mem_filter.mp hqmem).1
    have hpq : p < q := (Finset.mem_filter.mp hqmem).2
    obtain ⟨j₀, hj₀⟩ := (mem_poles_iff (V := V) q).mp hqpoles
    have hsep : ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) ≤ p
        ∨ q ≤ (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) := by
      intro k
      rcases le_or_gt ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) p with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨pole_mem k, h⟩))
    obtain ⟨μ, ⟨hμmem, hμ⟩, -⟩ := existsUnique_secular_root_in_gap hne hpq hi₀ hj₀ hsep
    refine ⟨μ, hμmem.1, fun p' hp' hpp' => ?_, hμ⟩
    exact lt_of_lt_of_le hμmem.2 (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hp', hpp'⟩))

/-! ## 2. Those roots are distinct, one for each pole -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem exists_roots_finset (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ R : Finset ℝ, (poles V).card ≤ R.card
      ∧ ∀ μ ∈ R, secularSum (V := V) μ = -1
        ∧ ∀ k : ι, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ) ≠ 0 := by
  classical
  choose! f hf1 hf2 hf3 using exists_root_above (V := V) hne hι
  have hinj : Set.InjOn f (poles V) := by
    intro a ha b hb hab
    by_contra hcon
    rcases lt_or_gt_of_ne hcon with h | h
    · have h1 : f a < b := hf2 a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) h
      have h2 : b < f b := hf1 b (Finset.mem_coe.mp hb)
      linarith
    · have h1 : f b < a := hf2 b (Finset.mem_coe.mp hb) a (Finset.mem_coe.mp ha) h
      have h2 : a < f a := hf1 a (Finset.mem_coe.mp ha)
      linarith
  refine ⟨(poles V).image f, by rw [Finset.card_image_of_injOn hinj], fun μ hμ => ?_⟩
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hμ
  refine ⟨hf3 p hp, fun k => ?_⟩
  rcases le_or_gt ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) p with h | h
  · exact ne_of_lt (by have := hf1 p hp; linarith)
  · exact ne_of_gt (by have := hf2 p hp _ (pole_mem k) h; linarith)

/-! ## 3. The count of poles is the count of distinct part sizes -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem card_poles_eq_card_sizes :
    (poles V).card
      = (Finset.univ.image (fun i : ι => Fintype.card (V i))).card := by
  classical
  have hφ : Function.Injective
      (fun n : ℕ => (Fintype.card (Σ i, V i) : ℝ) - 2 * n) := by
    intro a b hab
    simp only at hab
    have : (a : ℝ) = b := by linarith
    exact_mod_cast this
  rw [poles, ← Finset.card_image_of_injective (Finset.univ.image
    (fun i : ι => Fintype.card (V i))) hφ, Finset.image_image]
  rfl

/-! ## 4. So `Q` has at least as many eigenvalues off the part values as there are part sizes -/

/-- **AT LEAST ONE EIGENVALUE OF `Q` FOR EACH DISTINCT PART SIZE**, all of them distinct, and none
of them a part value's neighbour in the secular sense. -/
theorem exists_eigenvalues_finset (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ R : Finset ℝ,
      (Finset.univ.image (fun i : ι => Fintype.card (V i))).card ≤ R.card
        ∧ ∀ μ ∈ R, ∃ x : (Σ i, V i) → ℝ, x ≠ 0
          ∧ signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x := by
  classical
  obtain ⟨R, hcard, hR⟩ := exists_roots_finset (V := V) hne hι
  refine ⟨R, by rw [← card_poles_eq_card_sizes]; exact hcard, fun μ hμ => ?_⟩
  obtain ⟨hs, hd⟩ := hR μ hμ
  obtain ⟨x, hx, hxp⟩ :=
    exists_eigenvector_of_mem_ker_secular hne (mem_ker_secularVec (V := V) hd hs)
  exact ⟨x, fun h0 => secularVec_ne_zero hne (Classical.choice hι) hd
    (by rw [← hxp, h0, map_zero]), hx⟩

end SecularRootCount
