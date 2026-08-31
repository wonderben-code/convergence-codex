import TorusPairClassFibre

/-!
# The number of interior axes does not move along an orbit

`TorusOrbitCount.card_orbit_of_distinctPairs` gives `|orbit k| = 2 ^ (interiorAxes k).card * d!`,
and `TorusPairClassFibre.card_pairClass_fibre` says the `2` is the size of a mirror pair. Assembling
the general orbit count needs one more thing that neither supplies: **that `(interiorAxes k').card`
is the same for every `k'` in the orbit**, so that `2 ^ (interiorAxes k).card` is a property of the
orbit and not of the representative.

> **`interiorAxes_reflectAxes`** — mirroring a set of axes does not change which axes are interior.
> The mirror of `0` is `0`, and `2(n − v) = n` exactly when `2v = n`, so both clauses survive.
>
> **`interiorAxes_comp_perm`** — relabelling permutes them, as the image under `σ⁻¹`.
>
> **`card_interiorAxes_signedPerm`** and **`card_interiorAxes_eq_of_mem_orbit`** — hence the count
> is constant on an orbit.

**Interiority is a property of the mirror PAIR, not of the coordinate**, which is the reason all of
this works, and `interiorAxes_iff_pairClass` says so directly: an axis is interior exactly when its
`pairClass` is neither `0` nor `n/2`. That is also the bridge the orbit count will cross, since
`mem_orbit_iff` speaks about `pairClass` and `interiorAxes` speaks about the coordinate.

## What this is NOT

**It is not the orbit count.** `TorusOrbitCount` computes the orbit only where the mirror pairs are
distinct; the general count `2^s · d! / (m₁! ⋯ m_r!)` needs this together with `mem_orbit_iff`,
`TorusPairClassFibre.card_pairClass_fibre` and
`MultinomialFibreCount.card_matching_of_sum`, and **that assembly is not here** as of
31 August 2026. No cost is offered for it (`ERRATUM 194`, `ERRATUM 246`).
-/

namespace TorusInteriorInvariant

open Finset BoxGraph TorusReflectionCount TorusHyperoctahedral TorusOrbitInvariant

variable {d : ℕ}

/-! ## 1. Interiority is a property of the mirror pair -/

/-- **AN AXIS IS INTERIOR EXACTLY WHEN ITS PAIR IS NEITHER OF THE TWO FIXED ONES.** -/
theorem interiorAxes_iff_pairClass {N : ℕ} (k : Site d (N + 3)) (i : Fin d) :
    i ∈ interiorAxes k ↔ 0 < pairClass N (k i).val ∧ 2 * pairClass N (k i).val ≠ N + 3 := by
  classical
  rw [mem_interiorAxes]
  have hlt := (k i).isLt
  unfold pairClass
  rcases Nat.eq_zero_or_pos (k i).val with h0 | hpos
  · simp [h0]
  · rw [Nat.mod_eq_of_lt (by omega)]
    constructor
    · rintro ⟨_, hne⟩
      omega
    · rintro ⟨h1, h2⟩
      omega

/-! ## 2. Mirroring does not move them -/

/-- **MIRRORING A SET OF AXES LEAVES THE INTERIOR ONES EXACTLY WHERE THEY WERE.** -/
theorem interiorAxes_reflectAxes {N : ℕ} (S : Finset (Fin d)) (k : Site d (N + 3)) :
    interiorAxes (reflectAxes S k) = interiorAxes k := by
  classical
  ext i
  rw [mem_interiorAxes, mem_interiorAxes]
  by_cases hi : i ∈ S
  · rw [reflectAxes_val_of_mem hi]
    have hlt := (k i).isLt
    rcases Nat.eq_zero_or_pos (k i).val with h0 | hpos
    · simp [h0]
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [reflectAxes_of_not_mem hi]

/-! ## 3. Relabelling permutes them -/

/-- **RELABELLING CARRIES THE INTERIOR AXES ALONG.** -/
theorem interiorAxes_comp_perm {N : ℕ} (σ : Equiv.Perm (Fin d)) (k : Site d (N + 3)) :
    interiorAxes (k ∘ σ) = (interiorAxes k).image σ.symm := by
  classical
  ext i
  rw [mem_interiorAxes, mem_image]
  constructor
  · intro h
    exact ⟨σ i, mem_interiorAxes.2 h, σ.symm_apply_apply i⟩
  · rintro ⟨a, ha, rfl⟩
    have := mem_interiorAxes.1 ha
    simpa [Function.comp] using this

/-! ## 4. So the count is constant on an orbit -/

/-- **A SIGNED PERMUTATION HAS AS MANY INTERIOR AXES AS ITS SOURCE.** -/
theorem card_interiorAxes_signedPerm {N : ℕ} (S : Finset (Fin d)) (σ : Equiv.Perm (Fin d))
    (k : Site d (N + 3)) :
    (interiorAxes (signedPerm S σ k)).card = (interiorAxes k).card := by
  classical
  rw [signedPerm, interiorAxes_comp_perm, interiorAxes_reflectAxes,
    card_image_of_injective _ σ.symm.injective]

/-- **SO `2 ^ (interiorAxes k).card` IS A PROPERTY OF THE ORBIT AND NOT OF THE REPRESENTATIVE.** -/
theorem card_interiorAxes_eq_of_mem_orbit {N : ℕ} (k k' : Site d (N + 3)) (h : k' ∈ orbit k) :
    (interiorAxes k').card = (interiorAxes k).card := by
  classical
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 h
  exact card_interiorAxes_signedPerm p.1 p.2 k

end TorusInteriorInvariant
