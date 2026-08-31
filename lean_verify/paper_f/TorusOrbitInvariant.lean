import TorusOrbitCount

/-!
# What the hyperoctahedral group preserves: the multiplicity of each mirror pair

`TorusOrbitCount` counts the orbit where the axes carry distinct mirror pairs and records the
general answer as a measurement:

> `|orbit k| = 2^s · d! / (m₁! ⋯ m_r!)` with `mᵢ` the multiplicities of the distinct mirror pairs
> — **checked on 3448 frequencies, 0 mismatches**, and **not proved**.

Those `mᵢ` are the subject here. **They are what the group preserves**, and saying so is the first
half of any proof of that formula — and is worth having on its own, because it is the first
statement in this chain about *which* frequencies share an orbit rather than how many.

> **`pairClass`** — a coordinate's mirror pair, named by its smaller member: `min v (n − v mod n)`.
> Reflection is exactly what leaves it alone.
>
> **`pairClass_reflectAxes`** — mirroring an axis does not change its pair. One `omega` from
> `v < n`, and it is where `min` earns its place.
>
> **`card_axes_with_pairClass_eq`** — **the invariant.** For every pair `c`, the number of axes
> whose coordinate lies in `c` is the same for `k` and for any `signedPerm S σ k`. The permutation
> supplies the bijection and `pairClass_reflectAxes` supplies the equality of the predicates.
>
> **`not_mem_orbit_of_card_ne`** — hence a criterion in the useful direction: **two frequencies
> whose pair-multiplicities differ anywhere are in different orbits**, so they are not carried to
> one another by any reflection-and-permutation.

## What is NOT here

**The converse is not proved, and it is the other half of the formula.** Equal multiplicities
everywhere ought to put two frequencies in one orbit — build the permutation matching the axes up,
then choose signs — and **nothing below does it**. Without it `not_mem_orbit_of_card_ne` is a
one-way test: it separates orbits and never merges them.

**No count.** The `mᵢ` are exhibited as cardinalities and **not multiplied together**. The pinned
Mathlib has `Nat.multinomial` and `Nat.multinomial_spec`, which is the arithmetic
`d! / (m₁! ⋯ m_r!)`, and **nothing connecting it to a count of anything** — probed 2026-08-31, zero
names pairing `multinomial` with `card`, `perm` or `equiv`. The combinatorial half must be built and
**no cost is offered for it** (`ERRATUM 194`, `ERRATUM 246`).

**Nothing about eigenvalues.** `νR` does not appear below. That two frequencies in one orbit share
an eigenvalue is `TorusHyperoctahedral.nuR_signedPerm` and is not re-proved; that two frequencies
sharing an eigenvalue need *not* share an orbit is `TorusEightNotTight` and is the reason this
invariant does not settle any multiplicity.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusOrbitInvariant

open Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusReflectionCount TorusHyperoctahedral

variable {d : ℕ}

/-! ## 1. A coordinate's mirror pair -/

/-- **THE MIRROR PAIR OF A COORDINATE, NAMED BY ITS SMALLER MEMBER.** `v` and `n − v` get the same
name, which is the point. -/
def pairClass (N v : ℕ) : ℕ := min v ((N + 3 - v) % (N + 3))

/-- **MIRRORING AN AXIS DOES NOT CHANGE ITS PAIR.** The two members swap and `min` does not see it.
This is where the `% n` in `reflectAxes` has to be unfolded, because at `v = 0` the mirror is `0`
and not `n`. -/
theorem pairClass_reflectAxes {N : ℕ} (S : Finset (Fin d)) (k : Site d (N + 3)) (j : Fin d) :
    pairClass N ((reflectAxes S k) j).val = pairClass N (k j).val := by
  classical
  by_cases hj : j ∈ S
  · rw [reflectAxes_val_of_mem hj]
    have hlt := (k j).isLt
    unfold pairClass
    rcases Nat.eq_zero_or_pos (k j).val with h0 | hpos
    · simp [h0]
    · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [reflectAxes_of_not_mem hj]

/-! ## 2. The invariant -/

/-- **THE NUMBER OF AXES CARRYING EACH MIRROR PAIR IS WHAT THE GROUP PRESERVES.** The permutation is
the bijection and `pairClass_reflectAxes` makes the predicates agree. -/
theorem card_axes_with_pairClass_eq {N : ℕ} (S : Finset (Fin d)) (σ : Equiv.Perm (Fin d))
    (k : Site d (N + 3)) (c : ℕ) :
    (Finset.univ.filter fun i => pairClass N ((signedPerm S σ k) i).val = c).card
      = (Finset.univ.filter fun i => pairClass N (k i).val = c).card := by
  classical
  refine Finset.card_nbij' (fun i => σ i) (fun i => σ.symm i) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
    rw [← hi]
    simp only [signedPerm, Function.comp]
    exact (pairClass_reflectAxes S k (σ i)).symm
  · intro i hi
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
    rw [← hi]
    simp only [signedPerm, Function.comp]
    rw [Equiv.apply_symm_apply]
    exact pairClass_reflectAxes S k i
  · intro i _; simp
  · intro i _; simp

/-- **SO FREQUENCIES WHOSE PAIR-MULTIPLICITIES DIFFER LIE IN DIFFERENT ORBITS.** A one-way test: it
separates orbits and never merges them, because the converse is not proved. -/
theorem not_mem_orbit_of_card_ne {N : ℕ} (k k' : Site d (N + 3)) (c : ℕ)
    (hne : (Finset.univ.filter fun i => pairClass N (k' i).val = c).card
      ≠ (Finset.univ.filter fun i => pairClass N (k i).val = c).card) :
    k' ∉ orbit k := by
  classical
  intro hx
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx
  exact hne (card_axes_with_pairClass_eq p.1 p.2 k c)

end TorusOrbitInvariant
