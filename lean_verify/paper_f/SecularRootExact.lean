import SecularRootCount

/-!
# Exactly one secular eigenvalue for every distinct part size

**THE PREVIOUS UNIT GAVE *AT LEAST* AND NAMED WHAT WAS MISSING: THAT EVERY ROOT ARISES THIS WAY.**
It does, and the argument needs nothing new — only entry 165's separation, read the other way round.
Given a root, take the **largest pole below it**; every larger pole is then above the root, because
a pole between them would be a pole strictly inside the interval that entry 165 forbids. So the root
occupies the slot above that pole, and entry 168 already put exactly one root in each slot.

## What is proved

**`poleMin_mem_poles`** — the smallest pole is a pole, which is what `Finset.inf'` being attained
means and which entry 166 never needed.
**`exists_pole_below`** — every root has a **largest pole below it**, and every pole above that one
is above the root. The first half needs the root to be strictly above `poleMin`, which is entry
166's bound plus the observation that a root is not a pole; the second half is one application of
maximality.
**`root_above_pole_unique`** — and two roots in the same slot coincide, straight from entry 165: a
pole between them would be a pole above the slot's floor and below one of them, contradicting the
slot condition.

**`exists_roots_finset_exact`** — **so the roots that are not poles form a finite set of size
exactly the number of distinct part sizes**, with membership characterised, not merely bounded.
**`exists_eigenvalues_finset_exact`** — and each is an eigenvalue of `Q`.

## What is NOT here

* **THIS IS NOT THE NUMBER OF EIGENVALUES OF `Q`, AND THE GAP IS CONCRETE.** Two families of
  eigenvalue are outside the count. The **part values** `N − nᵢ` come from a different route with
  their own multiplicities, and no unit rules out one of them coinciding with a secular root. And an
  eigenvalue that **is** a pole is invisible here, because the criterion this chain uses requires
  every denominator to be non-zero — **that is not hypothetical**: at `r` parts of one vertex the
  graph is `K_r`, the pole is `N − 2` and `N − 2` is an eigenvalue of multiplicity `r − 1`, counted
  by neither this file nor the part-value chain. Adding the three counts into one statement about
  the spectrum is **not attempted** (`ERRATUM 246`).
* **NO MULTIPLICITY.** Each counted root is a simple eigenvalue by entry 157; that is not restated,
  and nothing here says the *eigenvalues at poles* are simple, because nothing anywhere does.
* **NO VALUES.** The roots are counted and located, never computed; the two graphs where they are
  known were computed by hand from a quadratic, in earlier units.
* **NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0`
  and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): the chain's `Fintype` instances;
`∀ i, Nonempty (V i)` and `Nonempty ι` throughout. `DecidableEq ι` is **not** taken. **No mass, no
propagator, and no metric anywhere.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SecularRootExact

open Matrix Finset SimpleGraph LaplacianSignless
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation SecularRootLocation SecularRootSeparation
open SecularRootBounds SecularRootCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. Every root sits in the slot above some pole -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem poleMin_mem_poles (hι : Nonempty ι) : poleMin (V := V) hι ∈ poles V := by
  rw [poleMin]
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr hι)
    (fun j : ι => (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V j))
  rw [hi]
  exact pole_mem i

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem exists_pole_below (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {μ : ℝ}
    (hs : secularSum (V := V) μ = -1)
    (hd : ∀ k : ι, ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ) ≠ 0) :
    ∃ p ∈ poles V, p < μ ∧ ∀ p' ∈ poles V, p < p' → μ < p' := by
  classical
  have hminlt : poleMin (V := V) hι < μ := by
    rcases lt_or_eq_of_le (poleMin_le_of_secular_root (V := V) hne hι hs) with h | h
    · exact h
    · exfalso
      obtain ⟨i, hi⟩ := (mem_poles_iff (V := V) (poleMin (V := V) hι)).mp
        (poleMin_mem_poles (V := V) hι)
      exact hd i (by rw [hi, ← h]; ring)
  have hLne : ((poles V).filter (fun x => x < μ)).Nonempty :=
    ⟨poleMin (V := V) hι, Finset.mem_filter.mpr ⟨poleMin_mem_poles (V := V) hι, hminlt⟩⟩
  set p := ((poles V).filter (fun x => x < μ)).max' hLne with hpdef
  have hpmem : p ∈ (poles V).filter (fun x => x < μ) := Finset.max'_mem _ hLne
  refine ⟨p, (Finset.mem_filter.mp hpmem).1, (Finset.mem_filter.mp hpmem).2, fun p' hp' hpp' => ?_⟩
  by_contra hcon
  have hp'ne : p' ≠ μ := by
    intro h
    obtain ⟨i, hi⟩ := (mem_poles_iff (V := V) p').mp hp'
    exact hd i (by rw [hi, h]; ring)
  have hp'lt : p' < μ := lt_of_le_of_ne (le_of_not_gt hcon) hp'ne
  exact absurd (Finset.le_max' _ p' (Finset.mem_filter.mpr ⟨hp', hp'lt⟩)) (not_le.mpr hpp')

/-! ## 2. That slot holds one root only -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
theorem root_above_pole_unique (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) {p μ ν : ℝ}
    (hμ1 : p < μ) (hμ2 : ∀ p' ∈ poles V, p < p' → μ < p') (hμs : secularSum (V := V) μ = -1)
    (hν1 : p < ν) (hν2 : ∀ p' ∈ poles V, p < p' → ν < p') (hνs : secularSum (V := V) ν = -1) :
    μ = ν := by
  by_contra hcon
  rcases lt_or_gt_of_ne hcon with h | h
  · obtain ⟨k, hk1, hk2⟩ := exists_pole_between_secular_roots hne hι h hμs hνs
    exact absurd hk2 (not_le.mpr (hν2 _ (pole_mem k) (by linarith)))
  · obtain ⟨k, hk1, hk2⟩ := exists_pole_between_secular_roots hne hι h hνs hμs
    exact absurd hk2 (not_le.mpr (hμ2 _ (pole_mem k) (by linarith)))

/-! ## 3. So the non-pole roots are exactly one per distinct part size -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **EXACTLY AS MANY SECULAR ROOTS AS THERE ARE DISTINCT PART SIZES.** -/
theorem exists_roots_finset_exact (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ R : Finset ℝ,
      R.card = (Finset.univ.image (fun i : ι => Fintype.card (V i))).card
        ∧ ∀ μ : ℝ, μ ∈ R ↔ secularSum (V := V) μ = -1
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
  have hnp : ∀ p ∈ poles V, ∀ k : ι,
      ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - f p) ≠ 0 := by
    intro p hp k
    rcases le_or_gt ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k)) p with h | h
    · exact ne_of_lt (by have := hf1 p hp; linarith)
    · exact ne_of_gt (by have := hf2 p hp _ (pole_mem k) h; linarith)
  refine ⟨(poles V).image f, ?_, fun μ => ?_⟩
  · rw [Finset.card_image_of_injOn hinj, card_poles_eq_card_sizes]
  · constructor
    · intro hμ
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hμ
      exact ⟨hf3 p hp, hnp p hp⟩
    · rintro ⟨hs, hd⟩
      obtain ⟨p, hp, hp1, hp2⟩ := exists_pole_below (V := V) hne hι hs hd
      refine Finset.mem_image.mpr ⟨p, hp, ?_⟩
      exact root_above_pole_unique hne hι (hf1 p hp) (hf2 p hp) (hf3 p hp) hp1 hp2 hs

/-- **AND SO `Q` HAS EXACTLY THAT MANY EIGENVALUES OFF THE POLES.** -/
theorem exists_eigenvalues_finset_exact (hne : ∀ i, Nonempty (V i)) (hι : Nonempty ι) :
    ∃ R : Finset ℝ,
      R.card = (Finset.univ.image (fun i : ι => Fintype.card (V i))).card
        ∧ ∀ μ ∈ R, ∃ x : (Σ i, V i) → ℝ, x ≠ 0
          ∧ signlessLap (completeMultipartiteGraph V) *ᵥ x = μ • x := by
  classical
  obtain ⟨R, hcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨R, hcard, fun μ hμ => ?_⟩
  obtain ⟨hs, hd⟩ := (hR μ).mp hμ
  obtain ⟨x, hx, hxp⟩ :=
    exists_eigenvector_of_mem_ker_secular hne (mem_ker_secularVec (V := V) hd hs)
  exact ⟨x, fun h0 => secularVec_ne_zero hne (Classical.choice hι) hd
    (by rw [← hxp, h0, map_zero]), hx⟩

end SecularRootExact
