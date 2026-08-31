import TorusOrbitInvariant

/-!
# The orbit, characterised: same mirror pairs with the same multiplicities

`TorusOrbitInvariant` proved the multiplicity of each mirror pair constant across an orbit and
fenced the other direction:

> **The converse is not proved, and it is the other half of the formula.** Equal multiplicities
> everywhere ought to put two frequencies in one orbit — build the permutation matching the axes up,
> then choose signs — and **nothing below does it**.

It is done here, in exactly those two steps.

> **`pairClass_eq_iff`** — two coordinates have the same mirror pair **iff** they agree or sum to
> `n`. This is `CycleMultiplicity.cos_angle_eq_iff`'s combinatorial content with the analysis
> removed: there it came out of `Real.cos_eq_cos_iff`, here it is arithmetic.
>
> **`mem_orbit_of_card_eq`** — **the converse.** `Equiv.ofFiberEquiv` glues the per-pair
> bijections into one permutation of the axes, `Equiv.ofFiberEquiv_map` says it matches the pairs
> up, and the mirrored set is then read off: mirror exactly the axes where the matched coordinates
> disagree. `pairClass_eq_iff` is what makes *disagree* mean *is the mirror of*.
>
> **`mem_orbit_iff`** — hence the characterisation, in both directions: `k'` is in `k`'s orbit
> **iff** every mirror pair is carried by the same number of axes in each.

## What this settles and what it does not

**CROSS-CHECKED AGAINST A DIRECT ENUMERATION BEFORE THE COMMIT**, outside Lean and labelled as
such: the orbit computed by brute force against the fibre of the pair multiset, for every frequency
with `3 ≤ n ≤ 9` and `d ≤ 3` — **2338 frequencies, 0 mismatches**. Not part of the proof; the check
that the *statement* says what it was meant to say.

**Settled**: which frequencies share an orbit. The hyperoctahedral group's orbits on frequencies are
exactly the fibres of *the multiset of mirror pairs*, and that is now a theorem rather than a
picture.

**NOT settled: how big those orbits are.** `TorusOrbitCount` counts them where the pairs are
distinct; the general count is `2^s · d! / (m₁! ⋯ m_r!)`, **checked on 3448 frequencies and still
not proved**. This file supplies the characterisation that count would be a count *of*, and does
**not** perform it: no multiset arrangement is counted below, and the pinned Mathlib's
`Nat.multinomial` is connected to no count of anything (probed 2026-08-31). **No cost is offered**
(`ERRATUM 194`, `ERRATUM 246`).

**Nothing about eigenvalues.** Frequencies in one orbit share an eigenvalue
(`TorusHyperoctahedral.nuR_signedPerm`); frequencies sharing an eigenvalue need **not** share an
orbit (`TorusEightNotTight`), so this characterises orbits and not eigenspaces, and the upper bound
on multiplicity at `d ≥ 2` is untouched.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusOrbitCharacterisation

open Finset BoxGraph TorusReflection
open MassiveTorusSpectrum TorusReflectionCount TorusHyperoctahedral TorusOrbitInvariant

variable {d : ℕ}

/-! ## 1. Same pair means equal or mirror -/

/-- **TWO COORDINATES HAVE THE SAME MIRROR PAIR IFF THEY AGREE OR SUM TO `n`.** The pair `{v, n−v}`
is determined by its smaller member, which is what `pairClass` records.
`CycleMultiplicity.cos_angle_eq_iff` is this statement reached through `Real.cos_eq_cos_iff`; here
there is no analysis in it. -/
theorem pairClass_eq_iff {N a b : ℕ} (ha : a < N + 3) (hb : b < N + 3) :
    pairClass N a = pairClass N b ↔ a = b ∨ a + b = N + 3 := by
  have hzero : pairClass N 0 = 0 := by unfold pairClass; simp
  have hpos : ∀ v, 0 < v → v < N + 3 → pairClass N v = min v (N + 3 - v) := by
    intro v h1 h2
    unfold pairClass
    rw [Nat.mod_eq_of_lt (by omega)]
  rcases Nat.eq_zero_or_pos a with rfl | hap
  · rcases Nat.eq_zero_or_pos b with rfl | hbp
    · simp
    · rw [hzero, hpos b hbp hb]
      constructor
      · intro h; omega
      · intro h; omega
  · rcases Nat.eq_zero_or_pos b with rfl | hbp
    · rw [hzero, hpos a hap ha]
      constructor
      · intro h; omega
      · intro h; omega
    · rw [hpos a hap ha, hpos b hbp hb]
      constructor
      · intro h; omega
      · intro h; omega

/-! ## 2. The converse -/

/-- **EQUAL MULTIPLICITIES PUT TWO FREQUENCIES IN ONE ORBIT.** `Equiv.ofFiberEquiv` glues the
per-pair bijections into a permutation of the axes and `Equiv.ofFiberEquiv_map` says it matches the
pairs; the mirrored set is then *the axes where the matched coordinates disagree*, and
`pairClass_eq_iff` is what makes disagreement mean mirroring. -/
theorem mem_orbit_of_card_eq {N : ℕ} (k k' : Site d (N + 3))
    (h : ∀ c, (Finset.univ.filter fun i => pairClass N (k' i).val = c).card
      = (Finset.univ.filter fun i => pairClass N (k i).val = c).card) :
    k' ∈ orbit k := by
  classical
  -- One bijection per mirror pair, from the equal cardinalities.
  have hfib : ∀ c : ℕ, {i : Fin d // pairClass N (k' i).val = c}
      ≃ {j : Fin d // pairClass N (k j).val = c} := by
    intro c
    refine Fintype.equivOfCardEq ?_
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h c
  set σ : Fin d ≃ Fin d := Equiv.ofFiberEquiv hfib with hσ
  have hmatch : ∀ i, pairClass N (k (σ i)).val = pairClass N (k' i).val :=
    fun i => Equiv.ofFiberEquiv_map hfib i
  refine Finset.mem_image.2 ⟨(Finset.univ.filter fun j => k' (σ.symm j) ≠ k j, σ),
    Finset.mem_univ _, ?_⟩
  funext i
  have hd := (pairClass_eq_iff (k (σ i)).isLt (k' i).isLt).1 (hmatch i)
  by_cases hmem : σ i ∈ Finset.univ.filter fun j => k' (σ.symm j) ≠ k j
  · have hne : k' i ≠ k (σ i) := by
      have := (Finset.mem_filter.1 hmem).2
      rwa [Equiv.symm_apply_apply] at this
    have hsum : (k (σ i)).val + (k' i).val = N + 3 := by
      rcases hd with heq | hsum
      · exact absurd (Fin.ext heq.symm) hne
      · exact hsum
    refine Fin.ext ?_
    simp only [signedPerm, Function.comp]
    rw [reflectAxes_val_of_mem hmem, Nat.mod_eq_of_lt (by have := (k' i).isLt; omega)]
    omega
  · have heq : k' i = k (σ i) := by
      by_contra hne
      exact hmem (Finset.mem_filter.2 ⟨Finset.mem_univ _, by rwa [Equiv.symm_apply_apply]⟩)
    simp only [signedPerm, Function.comp]
    rw [reflectAxes_of_not_mem hmem, heq]

/-! ## 3. So the orbits are the fibres of the pair multiset -/

/-- **THE CHARACTERISATION.** `k'` lies in `k`'s orbit **iff** every mirror pair is carried by the
same number of axes in each. -/
theorem mem_orbit_iff {N : ℕ} (k k' : Site d (N + 3)) :
    k' ∈ orbit k ↔ ∀ c, (Finset.univ.filter fun i => pairClass N (k' i).val = c).card
      = (Finset.univ.filter fun i => pairClass N (k i).val = c).card := by
  classical
  refine ⟨fun hx c => ?_, mem_orbit_of_card_eq k k'⟩
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.1 hx
  exact card_axes_with_pairClass_eq p.1 p.2 k c

end TorusOrbitCharacterisation
