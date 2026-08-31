import TorusInteriorInvariant
import MultinomialFibreCount

/-!
# The torus orbit, counted: `2^s · d! / (m₁! ⋯ m_r!)`

Four units built the inputs and this one assembles them.

* `TorusOrbitCharacterisation.mem_orbit_iff` — the orbits are the fibres of the multiset of mirror
  pairs.
* `MultinomialFibreCount.card_matching` — how many class functions have prescribed fibre sizes:
  the multinomial coefficient.
* `TorusPairClassFibre.card_pairClass_fibre` — how many coordinates sit over one class: two, except
  at the two fixed points of the mirror.
* `TorusInteriorInvariant.card_interiorAxes_eq_of_mem_orbit` — so the exponent is a property of the
  orbit.

> **`cls`** — a frequency's class function, valued in `Fin (N + 3)` rather than `ℕ`, because the
> counting theorem needs a `Fintype` codomain. `pairClass N v ≤ v < N + 3` makes that free.
>
> **`mem_orbit_iff_cls`** — `mem_orbit_iff` in those terms. The two directions differ: a class
> `c ≥ N + 3` is carried by no axis at all, which is what lets the `ℕ`-indexed statement come back
> from the `Fin`-indexed one.
>
> **`card_orbit`** — **the count, with NO hypotheses on the frequency.**
> `|orbit k| = 2 ^ |interiorAxes k| · multinomial`, the multinomial taken over the class fibre
> sizes.

**The lifting step is free, and that is the one thing this assembly could have been expensive for.**
A class function with the right fibre sizes must be realised by *some* frequency in the orbit, and
`MultinomialFibreCount.exists_perm_comp` produces a **permutation** carrying one to the other — so
the frequency is `k ∘ σ`, which is `signedPerm ∅ σ k` and already in the orbit. No choice, no
construction.

## What this does NOT do

**IT DOES NOT RECOVER `TorusOrbitCount.card_orbit_of_distinctPairs`, AND THAT IS NOT CLAIMED.**
Under `DistinctPairs` every class fibre should be a singleton, making the multinomial `d!` and this
formula `2^s · d!`; **no such derivation is here**. The two theorems are proved independently and
neither is obtained from the other, as of 31 August 2026. It is the obvious next check on this
statement — a special case that must come out right — and no cost is offered for it
(`ERRATUM 201`, `ERRATUM 194`, `ERRATUM 246`).

**It says nothing about the eigenspace.** `TorusHyperoctahedral.orbit_card_le_finrank_eigenspace`
bounds the degeneracy *below* by the orbit; this computes the orbit, so the bound is now explicit,
but **whether it is tight at `d ≥ 2` is untouched** and `TorusEightNotTight` exhibits a frequency
where the orbit is strictly smaller than the eigenspace. As of 31 August 2026 nothing here changes
that. No cost is offered for the gap (`ERRATUM 194`, `ERRATUM 246`).
-/

namespace TorusOrbitMultinomial

open Finset BoxGraph TorusReflectionCount TorusHyperoctahedral TorusOrbitInvariant
open TorusOrbitCharacterisation TorusPairClassFibre TorusInteriorInvariant

variable {d : ℕ}

/-! ## 1. The class function, with a finite codomain -/

theorem pairClass_lt {N v : ℕ} (h : v < N + 3) : pairClass N v < N + 3 := by
  unfold pairClass
  omega

/-- A coordinate's mirror pair, named inside `Fin (N + 3)`. -/
def clsF {N : ℕ} (v : Fin (N + 3)) : Fin (N + 3) := ⟨pairClass N v.val, pairClass_lt v.isLt⟩

/-- A frequency's class function. -/
def cls {N : ℕ} (k : Site d (N + 3)) : Fin d → Fin (N + 3) := fun i => clsF (k i)

theorem cls_apply_val {N : ℕ} (k : Site d (N + 3)) (i : Fin d) :
    (cls k i).val = pairClass N (k i).val := rfl

/-! ## 2. `mem_orbit_iff`, in those terms -/

theorem card_cls_fibre {N : ℕ} (k : Site d (N + 3)) (c : Fin (N + 3)) :
    Fintype.card {i // cls k i = c}
      = (univ.filter fun i => pairClass N (k i).val = c.val).card := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h; rw [← h, cls_apply_val]
  · intro h; exact Fin.ext (by rw [cls_apply_val, h])

/-- **THE ORBIT, IN TERMS OF THE CLASS FUNCTION.** -/
theorem mem_orbit_iff_cls {N : ℕ} (k k' : Site d (N + 3)) :
    k' ∈ orbit k ↔ ∀ c : Fin (N + 3),
      Fintype.card {i // cls k' i = c} = Fintype.card {i // cls k i = c} := by
  classical
  rw [mem_orbit_iff]
  constructor
  · intro h c
    rw [card_cls_fibre, card_cls_fibre]
    exact h c.val
  · intro h c
    by_cases hc : c < N + 3
    · have := h ⟨c, hc⟩
      rwa [card_cls_fibre, card_cls_fibre] at this
    · have hempty : ∀ k'' : Site d (N + 3),
          (univ.filter fun i => pairClass N (k'' i).val = c) = ∅ := by
        intro k''
        refine Finset.filter_eq_empty_iff.2 fun i _ => ?_
        have := pairClass_lt (k'' i).isLt
        omega
      rw [hempty k', hempty k]

/-! ## 3. Every fibre of `cls` over the orbit has `2 ^ s` elements -/

theorem card_clsF_fibre {N : ℕ} (v₀ : Fin (N + 3)) :
    Fintype.card {v : Fin (N + 3) // clsF v = clsF v₀}
      = if 0 < v₀.val ∧ 2 * v₀.val ≠ N + 3 then 2 else 1 := by
  classical
  rw [Fintype.card_subtype, ← card_pairClass_fibre v₀]
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and, clsF]
  constructor
  · intro h; exact congrArg Fin.val h
  · intro h; exact Fin.ext h

theorem card_cls_eq {N : ℕ} (k' : Site d (N + 3)) :
    (univ.filter fun k'' : Site d (N + 3) => cls k'' = cls k').card
      = 2 ^ (interiorAxes k').card := by
  classical
  have h1 : (univ.filter fun k'' : Site d (N + 3) => cls k'' = cls k').card
      = Fintype.card {k'' : Site d (N + 3) // ∀ i, clsF (k'' i) = cls k' i} := by
    rw [Fintype.card_subtype]
    congr 1
    ext k''
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h i => by rw [← h]; rfl, fun h => funext h⟩
  rw [h1, Fintype.card_congr (Equiv.subtypePiEquivPi
    (p := fun (i : Fin d) (v : Fin (N + 3)) => clsF v = cls k' i)), Fintype.card_pi]
  have h2 : ∀ i : Fin d, Fintype.card {v : Fin (N + 3) // clsF v = cls k' i}
      = if 0 < (k' i).val ∧ 2 * (k' i).val ≠ N + 3 then 2 else 1 := fun i =>
    card_clsF_fibre (k' i)
  rw [Finset.prod_congr rfl fun i _ => h2 i]
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  congr 1

/-! ## 4. The count -/

/-- **THE ORBIT OF A FREQUENCY, COUNTED, WITH NO HYPOTHESES ON THE FREQUENCY.** -/
theorem card_orbit {N : ℕ} (k : Site d (N + 3)) :
    (orbit k).card
      = 2 ^ (interiorAxes k).card
        * Nat.multinomial univ (fun c : Fin (N + 3) => Fintype.card {i // cls k i = c}) := by
  have himg : (orbit k).image cls
      = univ.filter fun g : Fin d → Fin (N + 3) =>
          ∀ c, Fintype.card {i // g i = c} = Fintype.card {i // cls k i = c} := by
    ext g
    simp only [mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨k', hk', rfl⟩
      exact (mem_orbit_iff_cls k k').1 hk'
    · intro hg
      obtain ⟨σ, hσ⟩ := MultinomialFibreCount.exists_perm_comp (f := g) (g := cls k) hg
      refine ⟨signedPerm ∅ σ k, ?_, ?_⟩
      · exact Finset.mem_image.2 ⟨(∅, σ), Finset.mem_univ _, rfl⟩
      · funext i
        have : cls k (σ i) = g i := hσ i
        rw [← this]
        simp [signedPerm, cls, reflectAxes]
  have hsum := Finset.card_eq_sum_card_fiberwise
    (f := fun k' : Site d (N + 3) => cls k') (s := orbit k) (t := (orbit k).image cls)
    (fun k' hk' => Finset.mem_image_of_mem _ hk')
  have hconst : ∀ g ∈ (orbit k).image cls,
      ((orbit k).filter fun k' => cls k' = g).card = 2 ^ (interiorAxes k).card := by
    intro g hg
    obtain ⟨k', hk', rfl⟩ := Finset.mem_image.1 hg
    have hfil : ((orbit k).filter fun k'' => cls k'' = cls k')
        = univ.filter fun k'' : Site d (N + 3) => cls k'' = cls k' := by
      ext k''
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
      refine (mem_orbit_iff_cls k k'').2 fun c => ?_
      rw [h]
      exact (mem_orbit_iff_cls k k').1 hk' c
    rw [hfil, card_cls_eq k', card_interiorAxes_eq_of_mem_orbit k k' hk']
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, himg] at hsum
  rw [hsum, Nat.mul_comm]
  congr 1
  rw [← MultinomialFibreCount.card_matching (cls k)]
  congr 1
  ext g
  simp

end TorusOrbitMultinomial
