import TorusOrbitMultinomial

/-!
# What the orbit count buys: an explicit degeneracy bound with no hypotheses

`TorusHyperoctahedral.orbit_card_le_finrank_eigenspace` bounds the eigenspace of `νR k` below by
`|orbit k|`, for every frequency and with no hypotheses. `TorusOrbitMultinomial.card_orbit` computes
that orbit. **Nothing had put the two together**, so the estate's standing degeneracy bounds were
still the hypothesis-laden ones: `2^d · d!` under three hypotheses
(`TorusHyperoctahedral.hyperoctahedral_le_finrank_eigenspace`) and `2^s · d!` under `DistinctPairs`.

> **`orbit_eq_of_mem`** — orbits are equal or disjoint, straight off `mem_orbit_iff`: sharing a
> pair multiset is transitive because it is an equality of numbers.
>
> **`orbit_subset_nuR_fibre`** — the orbit sits inside the eigenvalue's fibre, which is the
> inclusion `orbit_card_le_finrank_eigenspace` proves inline and never names.
>
> **`two_pow_mul_multinomial_le_finrank`** — **the bound.**
> `2 ^ |interiorAxes k| · multinomial ≤ dim`, for **every** frequency of **every** torus, with no
> hypotheses at all.

## Where the bound is not tight, and it is known not to be

`TorusRealMultiplicity.finrank_eigenspace_massive_real` makes the dimension **exactly** the size of
the fibre `{k' | νR k' = νR k}`, and `orbit_subset_nuR_fibre` says the orbit is one piece of it. So
the bound is an equality exactly when the fibre is a **single** orbit — and it is not always:
`TorusNonReflectionCollision.sporadic_ne_signed_perm` exhibits two frequencies at side `24` with the
same `νR` and no signed permutation between them, and `TorusEightNotTight.nine_le_finrank_eight`
turns that into a frequency where the bound gives `8` and the dimension is at least `9`.

**Which fibres are single orbits is not settled here and no cost is offered** (`ERRATUM 194`,
`ERRATUM 246`). With `orbit_eq_of_mem` the fibre is a disjoint union of orbits, so the exact
dimension is a sum of `card_orbit`s over the orbits it contains; **that sum is not formed here**,
because which orbits collide is exactly the open question — the sporadic pair above is the only
collision this estate has exhibited, and no classification of them exists.
-/

namespace TorusEigenspaceLowerBound

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity TorusReflectionCount
open TorusHyperoctahedral TorusOrbitInvariant TorusOrbitCharacterisation TorusOrbitMultinomial

variable {d : ℕ}

/-! ## 1. Orbits are equal or disjoint -/

/-- **AN ORBIT IS DETERMINED BY ANY OF ITS MEMBERS.** Sharing a pair multiset is an equality of
numbers, so it is transitive and symmetric, and `mem_orbit_iff` turns that into set equality. -/
theorem orbit_eq_of_mem {N : ℕ} {k k' : Site d (N + 3)} (h : k' ∈ orbit k) :
    orbit k' = orbit k := by
  have hkk' := (mem_orbit_iff k k').1 h
  ext k''
  rw [mem_orbit_iff, mem_orbit_iff]
  constructor
  · intro hk'' c
    rw [hk'' c]
    exact hkk' c
  · intro hk'' c
    rw [hk'' c]
    exact (hkk' c).symm

/-! ## 2. The orbit is one piece of the eigenvalue's fibre -/

/-- **EVERY POINT OF THE ORBIT CARRIES THE SAME EIGENVALUE.** The inclusion
`orbit_card_le_finrank_eigenspace` proves inline, named here so that the partition above can be
stated at all. -/
theorem orbit_subset_nuR_fibre (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    orbit k ⊆ univ.filter fun k' : Site d (N + 3) => nuR N m k' = nuR N m k := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact nuR_signedPerm N m p.1 p.2 k

/-! ## 3. The bound -/

/-- **THE DEGENERACY OF THE MASSIVE LAPLACIAN ON THE DISCRETE TORUS, BOUNDED BELOW EXPLICITLY AND
WITH NO HYPOTHESES.** `2 ^ (number of interior axes)` times the multinomial coefficient of the
mirror-pair multiplicities. -/
theorem two_pow_mul_multinomial_le_finrank (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    2 ^ (interiorAxes k).card
        * Nat.multinomial univ (fun c : Fin (N + 3) => Fintype.card {i // cls k i = c})
      ≤ Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id)) := by
  rw [← card_orbit k]
  exact orbit_card_le_finrank_eigenspace N m k

end TorusEigenspaceLowerBound
