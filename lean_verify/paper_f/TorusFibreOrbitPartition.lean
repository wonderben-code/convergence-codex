import TorusBoundTightIff

/-!
# The eigenvalue's fibre IS a disjoint union of orbits, and the multiplicity is the sum

`TorusBoundTightIff` proved that the estate's degeneracy bound is an equality exactly when the
eigenvalue's fibre is a **single** orbit. The `UNLOCK_WATCHLIST` item it answers phrases the general
picture one step further — *"`dim = ∑ over the orbits the fibre contains` of `card_orbit`"*, so that
*"the bound is an equality exactly when the sum has one term"* — and that file recorded the sum as
**not built**: `TorusEigenspaceLowerBound.orbit_eq_of_mem` was the ingredient and nothing indexed
the partition. **Here it is indexed.**

## What is proved

**`mem_orbit_self`** — `k ∈ orbit k`, which is `mem_orbit_iff` at `fun _ => rfl`. It had no name,
and every step below needs it.

**`orbitsOf`** — the orbits the fibre contains, as a `Finset (Finset (Site d (N + 3)))`: the image
of the fibre under `orbit`. **`biUnion_orbitsOf`** says their union is the fibre exactly, and
**`orbitsOf_pairwiseDisjoint`** that distinct ones are disjoint — both from `orbit_eq_of_mem`, which
is the only property of orbits either uses.

**`card_nuRFibre_eq_sum`** and **`finrank_eq_sum_card_orbit`** — the multiplicity is
`∑ o ∈ orbitsOf, o.card`, and through `TorusOrbitMultinomial.card_orbit` each term is
`2 ^ |interiorAxes| · multinomial` at any of its members. **That is the item's sentence.**

**`card_orbitsOf_eq_one_iff`** and **`bound_eq_finrank_iff_card_orbitsOf`** — the sum has **one
term** exactly when the fibre is the orbit, and hence exactly when the bound is an equality. So the
item's two phrasings are now one theorem apart rather than two informal restatements of each other.

## What this does NOT do

**It does not make the open question easier.** Which frequencies have a one-term sum is the
coincidence question the item describes, unchanged: the partition says the multiplicity is a sum of
orbit sizes, not which orbits occur. `TorusBoundTightIff.orbit_ssubset_nuRFibre_eight` exhibits a
fibre with **more than one** term and that remains the only such witness in the estate. **No cost is
offered** (`ERRATUM 194`, `ERRATUM 246`).

**No orbit is counted that was not counted before.** `card_orbit` is unchanged and is quoted, not
re-proved.

**Nothing is claimed about how many terms there are.** `orbitsOf`'s cardinality is bounded by
nothing here beyond the trivial `≤ (nuRFibre …).card`, and no frequency is exhibited with exactly
two.

**No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusFibreOrbitPartition

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity TorusHyperoctahedral TorusReflectionCount
open TorusOrbitMultinomial TorusEigenspaceLowerBound TorusOrbitCharacterisation
open TorusBoundTightIff

variable {d : ℕ}

/-! ## 1. The one fact about orbits that had no name -/

/-- **`k` IS IN ITS OWN ORBIT.** `mem_orbit_iff` at `fun _ => rfl`; used by every step below and
absent from the estate before this file. -/
theorem mem_orbit_self {N : ℕ} (k : Site d (N + 3)) : k ∈ orbit k :=
  (mem_orbit_iff k k).2 fun _ => rfl

/-- Membership in the fibre is exactly equality of eigenvalues. -/
theorem mem_nuRFibre_iff {N : ℕ} (m : ℝ) (k k' : Site d (N + 3)) :
    k' ∈ nuRFibre N m k ↔ nuR N m k' = nuR N m k := by
  simp [nuRFibre]

/-! ## 2. The orbits the fibre contains -/

/-- **THE ORBITS INSIDE THE FIBRE**, indexed as a `Finset` of `Finset`s. -/
noncomputable def orbitsOf (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    Finset (Finset (Site d (N + 3))) :=
  (nuRFibre N m k).image orbit

/-- Every orbit in the family is a subset of the fibre. -/
theorem subset_nuRFibre_of_mem_orbitsOf {N : ℕ} {m : ℝ} {k : Site d (N + 3)}
    {o : Finset (Site d (N + 3))} (ho : o ∈ orbitsOf N m k) : o ⊆ nuRFibre N m k := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ho
  intro x hx
  rw [mem_nuRFibre_iff] at ha ⊢
  rw [← ha]
  exact (mem_nuRFibre_iff m a x).1 (orbit_subset_nuRFibre N m a hx)

/-- **THE FIBRE IS THE UNION OF THE ORBITS IT CONTAINS**, with nothing left over. -/
theorem biUnion_orbitsOf (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    (orbitsOf N m k).biUnion (fun o => o) = nuRFibre N m k := by
  classical
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨o, ho, hxo⟩ := Finset.mem_biUnion.1 hx
    exact subset_nuRFibre_of_mem_orbitsOf ho hxo
  · intro x hx
    exact Finset.mem_biUnion.2 ⟨orbit x, Finset.mem_image_of_mem _ hx, mem_orbit_self x⟩

/-- **DISTINCT ORBITS IN THE FAMILY ARE DISJOINT.** `orbit_eq_of_mem` and nothing else: a common
member would make both orbits equal to its own. -/
theorem orbitsOf_pairwiseDisjoint (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    ∀ o₁ ∈ orbitsOf N m k, ∀ o₂ ∈ orbitsOf N m k, o₁ ≠ o₂ → Disjoint o₁ o₂ := by
  classical
  rintro o₁ ho₁ o₂ ho₂ hne
  obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 ho₁
  obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 ho₂
  rw [Finset.disjoint_left]
  intro x hxa hxb
  exact hne ((orbit_eq_of_mem hxa).symm.trans (orbit_eq_of_mem hxb))

/-! ## 3. The multiplicity as a sum over orbits -/

/-- **THE FIBRE'S SIZE IS THE SUM OF THE ORBIT SIZES.** -/
theorem card_nuRFibre_eq_sum (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    (nuRFibre N m k).card = ∑ o ∈ orbitsOf N m k, o.card := by
  classical
  rw [← biUnion_orbitsOf N m k]
  exact Finset.card_biUnion (orbitsOf_pairwiseDisjoint N m k)

/-- **AND SO IS THE MULTIPLICITY** — the sentence the watchlist item wrote and left unbuilt. -/
theorem finrank_eq_sum_card_orbit (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id))
      = ∑ o ∈ orbitsOf N m k, o.card := by
  rw [finrank_eq_card_nuRFibre, card_nuRFibre_eq_sum]

/-! ## 4. One term, and the bound -/

/-- **THE SUM HAS ONE TERM EXACTLY WHEN THE FIBRE IS THE ORBIT.** -/
theorem card_orbitsOf_eq_one_iff (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    (orbitsOf N m k).card = 1 ↔ orbit k = nuRFibre N m k := by
  classical
  have hk : k ∈ nuRFibre N m k := (mem_nuRFibre_iff m k k).2 rfl
  constructor
  · intro h
    obtain ⟨o, ho⟩ := Finset.card_eq_one.1 h
    have hko : orbit k = o := Finset.mem_singleton.1 (ho ▸ Finset.mem_image_of_mem orbit hk)
    refine Finset.Subset.antisymm (orbit_subset_nuRFibre N m k) fun x hx => ?_
    have : orbit x = o := Finset.mem_singleton.1 (ho ▸ Finset.mem_image_of_mem orbit hx)
    rw [hko, ← this]
    exact mem_orbit_self x
  · intro h
    refine Finset.card_eq_one.2 ⟨orbit k, Finset.Subset.antisymm (fun o ho => ?_) ?_⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ho
      rw [← h] at ha
      exact Finset.mem_singleton.2 (orbit_eq_of_mem ha)
    · intro o ho
      rw [Finset.mem_singleton.1 ho]
      exact Finset.mem_image_of_mem orbit hk

/-- **THE BOUND IS AN EQUALITY EXACTLY WHEN THE SUM HAS ONE TERM.** The item's two phrasings,
joined. -/
theorem bound_eq_finrank_iff_card_orbitsOf (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    2 ^ (interiorAxes k).card
        * Nat.multinomial univ (fun c : Fin (N + 3) => Fintype.card {i // cls k i = c})
      = Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id))
      ↔ (orbitsOf N m k).card = 1 := by
  rw [bound_eq_finrank_iff, ← card_orbitsOf_eq_one_iff]

end TorusFibreOrbitPartition
