import TorusHyperoctahedral

/-!
# The orbit at a frequency whose axes carry distinct mirror pairs: `2^s · d!`

`TorusHyperoctahedral` bounds the degeneracy by the hyperoctahedral orbit at **every** frequency and
counts that orbit at a **generic** one, under three hypotheses. Its own closing note names what is
left:

> **What it does NOT do**: compute that orbit — no stabiliser is described and no orbit-counting
> formula is proved.

This file removes the two **interiority** hypotheses and keeps only the one that is really about
distinctness, replacing `2^d` by `2^s`.

> **`DistinctPairs`** — for `i ≠ j` the coordinates neither agree nor mirror: `kᵢ ≠ kⱼ` and
> `kᵢ + kⱼ ≠ n`. It is `TorusHyperoctahedral`'s hypotheses **minus** `0 < kᵢ` and minus the `i = j`
> case of the sum condition, which together are exactly *every axis is interior*.
>
> **`signedPerm_injOn_interior`** — distinct `(S, σ)` with `S ⊆ interiorAxes k` give distinct
> frequencies. Two steps: the class of a coordinate determines its axis, because distinct axes carry
> distinct pairs; and then a mirrored axis differs from an unmirrored one, because an interior axis
> is not its own mirror. **`TorusReflectionCount.reflectAxes_injOn` is the second step at `σ = 1`**
> and this is its extension.
>
> **`card_orbit_of_distinctPairs`** — hence `|orbit k| = 2^s · d!` with `s` the number of interior
> axes.

## Where this sits, exactly

`2^s · d!` recovers `TorusHyperoctahedral.card_orbit_of_generic` at `s = d` and
`CycleMultiplicityCount`'s exact ring count at `d = 1`, `s = 1`. Combined with
`orbit_card_le_finrank_eigenspace` it gives **`2^s · d! ≤ dim` under one hypothesis instead of
three**, and at `d = 1` that is `2`, which is exact.

## What is NOT here, and one thing is measured rather than proved

**The general orbit is still not computed.** When two axes carry the **same** mirror pair,
`DistinctPairs` fails and this says nothing. The general answer, **derived on paper and checked
against a direct enumeration but NOT proved**, is

    |orbit k| = 2^s · d! / (m₁! ⋯ m_r!)

with `mᵢ` the multiplicities of the distinct mirror pairs among the coordinates. **Checked on 3448
frequencies** — every `k` for `3 ≤ n ≤ 10` and `d ≤ 3` — **0 mismatches**. That is an enumeration
outside Lean and is recorded as one: it is a target for a later unit, not a result of this one, and
no cost is offered for proving it (`ERRATUM 194`, `ERRATUM 246`).

**No upper bound on any multiplicity.** Unchanged, and `TorusNonReflectionCollision.sporadic_nuR_eq`
still says none can come from symmetry.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusOrbitCount

open Matrix GraphLaplacian SimpleGraph Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusReflectionCount TorusHyperoctahedral

variable {d : ℕ}

/-! ## 1. The hypothesis -/

/-- **DISTINCT AXES CARRY DISTINCT MIRROR PAIRS.** Neither equal nor mirror, for `i ≠ j`. -/
def DistinctPairs {N : ℕ} (k : Site d (N + 3)) : Prop :=
  ∀ i j, i ≠ j → (k i).val ≠ (k j).val ∧ (k i).val + (k j).val ≠ N + 3

/-! ## 2. The orbit map is injective on the interior subsets -/

/-- **DISTINCT `(S, σ)` GIVE DISTINCT FREQUENCIES**, for `S` a set of interior axes. The class of a
coordinate determines its axis, and then an interior axis is not its own mirror. -/
theorem signedPerm_injOn_interior {N : ℕ} (k : Site d (N + 3)) (hk : DistinctPairs k) :
    Set.InjOn (fun p : Finset (Fin d) × Equiv.Perm (Fin d) => signedPerm p.1 p.2 k)
      (((interiorAxes k).powerset : Finset (Finset (Fin d))) ×ˢ
        (Finset.univ : Finset (Equiv.Perm (Fin d))) : Finset _) := by
  classical
  rintro ⟨S, σ⟩ hS ⟨T, τ⟩ hT h
  have hSsub : S ⊆ interiorAxes k := by simpa using hS
  have hTsub : T ⊆ interiorAxes k := by simpa using hT
  have hval : ∀ j : Fin d,
      ((reflectAxes S k) (σ j)).val = ((reflectAxes T k) (τ j)).val := by
    intro j
    exact congrArg Fin.val (congrFun (h : signedPerm S σ k = signedPerm T τ k) j)
  -- Step 1: the permutations agree, because distinct axes carry distinct pairs.
  have hperm : ∀ j : Fin d, σ j = τ j := by
    intro j
    by_contra hne
    have hv := hval j
    have hlt1 := (k (σ j)).isLt
    have hlt2 := (k (τ j)).isLt
    obtain ⟨hne1, hne2⟩ := hk (σ j) (τ j) hne
    by_cases hS' : σ j ∈ S <;> by_cases hT' : τ j ∈ T
    · obtain ⟨hp1, _⟩ := mem_interiorAxes.1 (hSsub hS')
      obtain ⟨hp2, _⟩ := mem_interiorAxes.1 (hTsub hT')
      rw [reflectAxes_val_of_mem hS', reflectAxes_val_of_mem hT'] at hv
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
      omega
    · obtain ⟨hp1, _⟩ := mem_interiorAxes.1 (hSsub hS')
      rw [reflectAxes_val_of_mem hS', reflectAxes_of_not_mem hT'] at hv
      rw [Nat.mod_eq_of_lt (by omega)] at hv
      omega
    · obtain ⟨hp2, _⟩ := mem_interiorAxes.1 (hTsub hT')
      rw [reflectAxes_of_not_mem hS', reflectAxes_val_of_mem hT'] at hv
      rw [Nat.mod_eq_of_lt (by omega)] at hv
      omega
    · rw [reflectAxes_of_not_mem hS', reflectAxes_of_not_mem hT'] at hv
      omega
  have hστ : σ = τ := Equiv.ext hperm
  subst hστ
  -- Step 2: hence the mirrored sets agree, because an interior axis is not its own mirror.
  have hmem : ∀ i : Fin d, i ∈ S ↔ i ∈ T := by
    intro i
    obtain ⟨j, rfl⟩ : ∃ j, σ j = i := ⟨σ.symm i, σ.apply_symm_apply i⟩
    have hv := hval j
    have hlt := (k (σ j)).isLt
    constructor
    · intro hS'
      by_contra hT'
      obtain ⟨hpos, hhalf⟩ := mem_interiorAxes.1 (hSsub hS')
      rw [reflectAxes_val_of_mem hS', reflectAxes_of_not_mem hT',
        Nat.mod_eq_of_lt (by omega)] at hv
      omega
    · intro hT'
      by_contra hS'
      obtain ⟨hpos, hhalf⟩ := mem_interiorAxes.1 (hTsub hT')
      rw [reflectAxes_of_not_mem hS', reflectAxes_val_of_mem hT',
        Nat.mod_eq_of_lt (by omega)] at hv
      omega
  simp [Finset.ext hmem]

/-! ## 3. So the orbit has exactly `2^s · d!` elements -/

/-- **`|orbit k| = 2^s · d!`**, with `s` the number of interior axes — under one hypothesis where
`TorusHyperoctahedral.card_orbit_of_generic` needed three, and recovering it at `s = d`. -/
theorem card_orbit_of_distinctPairs {N : ℕ} (k : Site d (N + 3)) (hk : DistinctPairs k) :
    (orbit k).card = 2 ^ (interiorAxes k).card * Nat.factorial d := by
  classical
  have hsub : orbit k = (((interiorAxes k).powerset : Finset (Finset (Fin d))) ×ˢ
      (Finset.univ : Finset (Equiv.Perm (Fin d)))).image
        fun p : Finset (Fin d) × Equiv.Perm (Fin d) => signedPerm p.1 p.2 k := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx
      refine Finset.mem_image.2 ⟨(p.1 ∩ interiorAxes k, p.2), ?_, ?_⟩
      · simp [Finset.mem_product, Finset.mem_powerset, Finset.inter_subset_right]
      · funext j
        by_cases hj : p.2 j ∈ p.1 ∩ interiorAxes k
        · have h1 : p.2 j ∈ p.1 := (Finset.mem_inter.1 hj).1
          refine Fin.ext ?_
          simp only [signedPerm, Function.comp]
          rw [reflectAxes_val_of_mem hj, reflectAxes_val_of_mem h1]
        · refine Fin.ext ?_
          simp only [signedPerm, Function.comp]
          rw [reflectAxes_of_not_mem hj]
          by_cases h1 : p.2 j ∈ p.1
          · have hnot : p.2 j ∉ interiorAxes k := fun hc => hj (Finset.mem_inter.2 ⟨h1, hc⟩)
            have hdeg := mem_interiorAxes.not.1 hnot
            have hlt := (k (p.2 j)).isLt
            rw [reflectAxes_val_of_mem h1]
            push Not at hdeg
            rcases Nat.eq_zero_or_pos (k (p.2 j)).val with h0 | hpos
            · simp [h0]
            · rw [Nat.mod_eq_of_lt (by omega)]; omega
          · rw [reflectAxes_of_not_mem h1]
    · intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_image.2 ⟨p, Finset.mem_univ _, rfl⟩
  rw [hsub, Finset.card_image_of_injOn (by simpa using signedPerm_injOn_interior k hk),
    Finset.card_product, Finset.card_powerset, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

end TorusOrbitCount
