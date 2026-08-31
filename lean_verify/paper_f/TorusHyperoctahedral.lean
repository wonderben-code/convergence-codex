import TorusNonReflectionCollision

/-!
# The generic degeneracy is at least `2^d · d!`

`TorusReflectionCount` proved `2^s ≤ dim` from the reflections alone, and
`TorusNonReflectionCollision` then showed the reflections are not the whole group: permuting the
axes leaves `νR` alone too, because `νR` is a sum over the axes and a sum does not see their order.
The two families together generate the **hyperoctahedral** group, of order `2^d · d!`, and the
bound that follows is the point of this file.

> **`signedPerm`** — mirror the axes in `S`, then relabel by `σ`. Nothing new: it is
> `reflectAxes S k ∘ σ`, named so it can be counted.
>
> **`nuR_signedPerm`** — `νR` does not move, from `nuR_reflectAxes` and `nuR_comp_perm` in
> succession.
>
> **`signedPerm_injective`** — **the unit.** Distinct `(S, σ)` give distinct frequencies, under two
> hypotheses on `k` and no others.
>
> **`hyperoctahedral_le_finrank_eigenspace`** — hence `2^d · d! ≤ dim`, in every dimension and at
> every side length at least three.

## EXTENDED THE SAME DAY: the bound holds with no hypotheses at all

The three hypotheses were doing one job — **counting** the orbit — and none at all in **bounding**
the dimension by it. Separating the two makes the general statement shorter than the special one.

> **`orbit k`** — the hyperoctahedral orbit of `k`, as a `Finset`.
>
> **`orbit_card_le_finrank_eigenspace`** — **`|orbit k| ≤ dim`, for EVERY frequency, with no
> hypotheses whatever.** The orbit sits inside the eigenvalue's fibre and the fibre's size is the
> dimension; `Finset.card_le_card` needs an inclusion and nothing else. **`signedPerm_injective` is
> not used**, which is the whole content of the generalisation.
>
> **`card_orbit_of_generic`** — and at a generic frequency the orbit is full, `2^d · d!`. **This is
> the only place the three hypotheses are spent.**
>
> **`hyperoctahedral_le_finrank_eigenspace` is now a corollary** of those two rather than a separate
> argument, and its statement is unchanged.
>
> **`one_le_card_orbit`** — the orbit is never empty, so the general bound is not vacuous at any
> frequency: `k` is its own image under the empty reflection and the identity permutation.

**What the general form is worth**: at a frequency with `s` interior axes and repeated coordinates
the orbit is smaller than `2^d · d!` and larger than `1`, and **the bound still applies** where the
old statement said nothing at all. What it does *not* do is compute that orbit — no stabiliser is
described and no orbit-counting formula is proved (`ERRATUM 246`).

## The two hypotheses, and what each is doing

**`Function.Injective k`** — the coordinates are pairwise distinct. Without it a transposition of
two equal coordinates is the identity on frequencies and `d!` collapses.

**`(k i).val + (k j).val ≠ n` for all `i, j`** — no coordinate is the mirror of any coordinate,
*including itself*. Taken at `i = j` it says no coordinate is the halfway frequency `n/2`; combined
with `0 < (k i).val` it says every axis is **interior**, so `interiorAxes k` is everything and the
`2^d` here is `TorusReflectionCount`'s `2^s` at `s = d`.

Together they make the `2d` numbers `k i` and `n − k i` pairwise distinct, which is exactly what the
injectivity argument consumes: reading one coordinate of `signedPerm S σ k` recovers **both** which
axis it came from and whether that axis was mirrored.

## What is NOT here

**It is still a lower bound, and the gap is now known to be real rather than suspected.**
`TorusNonReflectionCollision.sporadic_nuR_eq` exhibits a collision outside the hyperoctahedral
group, so **no group-theoretic argument can ever give an upper bound** — which is a sharper
statement of the obstruction than the chain has had, and it is not a route to one. **No upper bound
is proved at any `d ≥ 2` and none is costed** (`ERRATUM 194`, `ERRATUM 246`).

**The hypotheses are not shown to be generic.** No count of the frequencies satisfying them is
given, and *generic* is used here as an informal word for *the case where nothing collides by
accident*, not as a claim about a proportion.

**No group is constructed.** `signedPerm` is a function of `(S, σ)` and the composition law is not
stated; nothing in this estate would consume a `MulAction` carrier, which is `LovelockReduction`
§1's reason.

**Nothing is transported to `torusGraph`.** `MassiveTorusSpectrum.spectrum_real_eq_range_nuR` is
**not applied below**.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusHyperoctahedral

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity TorusReflectionCount TorusNonReflectionCollision

variable {d : ℕ}

/-! ## 1. Mirror some axes, then relabel them -/

/-- **A SIGNED PERMUTATION OF A FREQUENCY.** Mirror the axes in `S`, then relabel by `σ`. -/
def signedPerm {N : ℕ} (S : Finset (Fin d)) (σ : Equiv.Perm (Fin d)) (k : Site d (N + 3)) :
    Site d (N + 3) :=
  reflectAxes S k ∘ σ

/-- **`νR` DOES NOT MOVE.** Mirroring is `nuR_reflectAxes`, relabelling is `nuR_comp_perm`. -/
theorem nuR_signedPerm (N : ℕ) (m : ℝ) (S : Finset (Fin d)) (σ : Equiv.Perm (Fin d))
    (k : Site d (N + 3)) : nuR N m (signedPerm S σ k) = nuR N m k := by
  rw [signedPerm, nuR_comp_perm N m (reflectAxes S k) σ, nuR_reflectAxes N m S k]

/-! ## 2. Distinct signed permutations give distinct frequencies -/

/-- **THE UNIT.** Under the two hypotheses the `2d` numbers `k i` and `n − k i` are pairwise
distinct, so one coordinate of `signedPerm S σ k` recovers both the axis it came from and whether
that axis was mirrored — and hence `σ`, and hence `S`. -/
theorem signedPerm_injective {N : ℕ} (k : Site d (N + 3)) (hinj : Function.Injective k)
    (hpos : ∀ i, 0 < (k i).val) (hsum : ∀ i j, (k i).val + (k j).val ≠ N + 3) :
    Function.Injective
      (fun p : Finset (Fin d) × Equiv.Perm (Fin d) => signedPerm p.1 p.2 k) := by
  classical
  rintro ⟨S, σ⟩ ⟨T, τ⟩ h
  simp only [signedPerm] at h
  -- Read one coordinate at a time.
  have hval : ∀ j : Fin d,
      ((reflectAxes S k) (σ j)).val = ((reflectAxes T k) (τ j)).val :=
    fun j => congrArg Fin.val (congrFun h j)
  -- Step 1: the permutations agree.
  have hperm : ∀ j : Fin d, σ j = τ j := by
    intro j
    have hv := hval j
    by_cases hS : σ j ∈ S <;> by_cases hT : τ j ∈ T
    · rw [reflectAxes_val_of_mem hS, reflectAxes_val_of_mem hT,
        Nat.mod_eq_of_lt (by have := hpos (σ j); omega),
        Nat.mod_eq_of_lt (by have := hpos (τ j); omega)] at hv
      exact hinj (Fin.ext (by have := (k (σ j)).isLt; have := (k (τ j)).isLt; omega))
    · rw [reflectAxes_val_of_mem hS, reflectAxes_of_not_mem hT,
        Nat.mod_eq_of_lt (by have := hpos (σ j); omega)] at hv
      exact absurd (by have := (k (σ j)).isLt; omega : (k (σ j)).val + (k (τ j)).val = N + 3)
        (hsum (σ j) (τ j))
    · rw [reflectAxes_of_not_mem hS, reflectAxes_val_of_mem hT,
        Nat.mod_eq_of_lt (by have := hpos (τ j); omega)] at hv
      exact absurd (by have := (k (τ j)).isLt; omega : (k (τ j)).val + (k (σ j)).val = N + 3)
        (hsum (τ j) (σ j))
    · rw [reflectAxes_of_not_mem hS, reflectAxes_of_not_mem hT] at hv
      exact hinj (Fin.ext hv)
  have hστ : σ = τ := Equiv.ext hperm
  subst hστ
  -- Step 2: hence the mirrored sets agree, because `σ` is onto.
  have hmem : ∀ i : Fin d, i ∈ S ↔ i ∈ T := by
    intro i
    obtain ⟨j, rfl⟩ : ∃ j, σ j = i := ⟨σ.symm i, σ.apply_symm_apply i⟩
    have hv := hval j
    constructor
    · intro hS
      by_contra hT
      rw [reflectAxes_val_of_mem hS, reflectAxes_of_not_mem hT,
        Nat.mod_eq_of_lt (by have := hpos (σ j); omega)] at hv
      exact hsum (σ j) (σ j) (by omega)
    · intro hT
      by_contra hS
      rw [reflectAxes_of_not_mem hS, reflectAxes_val_of_mem hT,
        Nat.mod_eq_of_lt (by have := hpos (σ j); omega)] at hv
      exact hsum (σ j) (σ j) (by omega)
  simp [Finset.ext hmem]

/-! ## 3. The bound with no hypotheses at all: the orbit -/

/-- **THE ORBIT OF `k` UNDER THE HYPEROCTAHEDRAL GROUP**, as a `Finset`. -/
def orbit {N : ℕ} (k : Site d (N + 3)) : Finset (Site d (N + 3)) :=
  Finset.univ.image fun p : Finset (Fin d) × Equiv.Perm (Fin d) => signedPerm p.1 p.2 k

/-- **`|orbit k| ≤ dim`, WITH NO HYPOTHESES ON `k`.** Every image has `k`'s eigenvalue, so the
orbit sits inside the eigenvalue's fibre and the fibre's size is the dimension. **The three
hypotheses of §4 are used to count the orbit and are not used to bound it**, which is why they are
absent here — `Finset.card_le_card` needs an inclusion and nothing else. -/
theorem orbit_card_le_finrank_eigenspace (N : ℕ) (m : ℝ) (k : Site d (N + 3)) :
    (orbit k).card ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id)) := by
  classical
  rw [finrank_eigenspace_massive_real N m (nuR N m k)]
  have hcard : Nat.card {k' : Site d (N + 3) // nuR N m k' = nuR N m k}
      = (Finset.univ.filter fun k' : Site d (N + 3) => nuR N m k' = nuR N m k).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hcard]
  refine Finset.card_le_card ?_
  intro x hx
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact nuR_signedPerm N m p.1 p.2 k

/-! ## 4. And the generic case, where the orbit is as large as it can be -/

/-- **THE ORBIT IS FULL AT A GENERIC FREQUENCY.** This is where `signedPerm_injective` is spent,
and it is the only place the three hypotheses are used. -/
theorem card_orbit_of_generic {N : ℕ} (k : Site d (N + 3)) (hinj : Function.Injective k)
    (hpos : ∀ i, 0 < (k i).val) (hsum : ∀ i j, (k i).val + (k j).val ≠ N + 3) :
    (orbit k).card = 2 ^ d * Nat.factorial d := by
  classical
  rw [orbit, Finset.card_image_of_injective _ (signedPerm_injective k hinj hpos hsum),
    Finset.card_univ, Fintype.card_prod, Fintype.card_finset, Fintype.card_perm,
    Fintype.card_fin]

/-- **`2^d · d! ≤ dim`.** Now a corollary of §3 rather than a separate argument: the orbit bounds
the dimension for every frequency, and at a generic one the orbit is full. -/
theorem hyperoctahedral_le_finrank_eigenspace (N : ℕ) (m : ℝ) (k : Site d (N + 3))
    (hinj : Function.Injective k) (hpos : ∀ i, 0 < (k i).val)
    (hsum : ∀ i j, (k i).val + (k j).val ≠ N + 3) :
    2 ^ d * Nat.factorial d ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (torusGraph d (N + 3)) m) - (nuR N m k) • LinearMap.id)) :=
  (card_orbit_of_generic k hinj hpos hsum) ▸ orbit_card_le_finrank_eigenspace N m k

/-- **AND THE ORBIT IS NEVER EMPTY**, so §3 is not vacuous at any frequency: `k` is its own image
under the empty reflection and the identity permutation. -/
theorem one_le_card_orbit {N : ℕ} (k : Site d (N + 3)) : 1 ≤ (orbit k).card := by
  classical
  refine Finset.card_pos.2 ⟨k, ?_⟩
  refine Finset.mem_image.2 ⟨(∅, Equiv.refl _), Finset.mem_univ _, ?_⟩
  funext i
  simp [signedPerm, reflectAxes]

end TorusHyperoctahedral
