import PairingBound

/-!
# A crossing pairing crosses an even number of times, and the bound sharpens

**This file exists because of a comparison that came out the wrong way.**
`LatticeTruncatedDecay.truncated_abs_le` bounds the truncated correlation by `ε` times a constant,
**linear in the propagator across the split**. At four test functions the estate already had
`LatticeFourPointClustering.connected_smeared_le`, which is bounded by `2·(…)²` — **quadratic**,
because the connected four-point function is literally twice the square of the cross-propagator.
So the general estimate is *weaker at order four than the special one it looks like it
generalises.* That is recorded rather than left for a reader to assume otherwise, and it is fixed
here.

## Why quadratic and not linear

A pairing splits `S` into the indices paired inside it and the indices paired across. The first
group comes in pairs, so it has even size; hence

```
(number of crossing pairs)  ≡  |S|   (mod 2).
```

**When `|S|` is even a crossing pairing therefore crosses at least TWICE**, and its product carries
two factors from across the split rather than one.

## What is proved

* `invariant_filter` — `σ` preserves `S.filter (σ · ∈ S)`, which is what makes it a matching's
  index type in its own right;
* **`even_card_filter_mem`** — that set has even size, being perfectly matched by `σ`;
* **`card_cross_parity`** — hence the crossing pairs number `|S|` modulo two;
* **`two_le_card_cross`** — so at even `|S|`, a pairing that crosses at all crosses twice.

## What is NOT here

The sharpened estimate itself. Turning `two_le_card_cross` into `ε²·M^(r−2)` needs the two
crossing factors located in the representative set — the set `R.filter (fun i => (i ∈ S) ≠ (σ i ∈
S))` put in bijection with the crossing pairs — and then split off exactly as
`PairingBound.abs_prod_le_of_not_respects` splits off one. **Not done here, and not costed**
(`ERRATUM 194`). No measure, integral or test function appears.
-/

namespace PairingParity

open Equiv Function Involutions PairWeightRep PairingSplit PairingBound

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The indices paired inside `S` -/

omit [Fintype ι] in
/-- `σ` maps `S.filter (σ · ∈ S)` to itself: being in it says `i ∈ S` and `σ i ∈ S`, and at `σ i`
that reads `σ i ∈ S` and `i ∈ S` — the same two facts. -/
theorem invariant_filter {σ : Equiv.Perm ι} (hσ : Function.Involutive σ) (S : Finset ι) (x : ι) :
    σ x ∈ S.filter (fun i => σ i ∈ S) ↔ x ∈ S.filter (fun i => σ i ∈ S) := by
  simp only [Finset.mem_filter, hσ x]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

omit [Fintype ι] in
/-- **THE INDICES PAIRED INSIDE `S` COME IN PAIRS.** `σ` restricted to them is again a perfect
matching, so their number is even. -/
theorem even_card_filter_mem {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) (S : Finset ι) :
    Even (S.filter (fun i => σ i ∈ S)).card := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  set T : Finset ι := S.filter (fun i => σ i ∈ S) with hT
  have hmem : ∀ x, σ x ∈ T ↔ x ∈ T := fun x => invariant_filter hinv S x
  have hpm : σ.subtypePerm hmem ∈ perfectMatchings {x : ι // x ∈ T} := by
    refine ⟨fun x => by ext; simpa using hinv (x : ι), ?_⟩
    intro x hx
    exact hσ.2 (x : ι) (by simpa using congrArg Subtype.val hx)
  have := Involutions.even_card_of_mem_perfectMatchings hpm
  simpa using this

/-! ## 2. The parity of the crossing count -/

omit [Fintype ι] in
/-- **THE CROSSING PAIRS NUMBER `|S|` MODULO TWO.** `S` splits into the indices paired inside it
— an even number — and those paired across, and the second group is the crossing pairs counted at
their `S` endpoint. -/
theorem card_cross_parity {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) (S : Finset ι) :
    (S.filter (fun i => σ i ∉ S)).card % 2 = S.card % 2 := by
  classical
  have hsplit : (S.filter (fun i => σ i ∈ S)).card + (S.filter (fun i => σ i ∉ S)).card
      = S.card := Finset.card_filter_add_card_filter_not (fun i => σ i ∈ S)
  obtain ⟨t, ht⟩ := even_card_filter_mem hσ S
  omega

omit [Fintype ι] in
/-- **SO AT EVEN `|S|`, A PAIRING THAT CROSSES AT ALL CROSSES TWICE.** This is the step the
four-point estimate uses without naming it, and the reason the general bound was weaker. -/
theorem two_le_card_cross {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) {S : Finset ι}
    (hS : Even S.card) (hne : (S.filter (fun i => σ i ∉ S)).Nonempty) :
    2 ≤ (S.filter (fun i => σ i ∉ S)).card := by
  have hp := card_cross_parity hσ S
  obtain ⟨t, ht⟩ := hS
  have h1 : 1 ≤ (S.filter (fun i => σ i ∉ S)).card := Finset.card_pos.mpr hne
  omega

end PairingParity
