import PairingGlue

/-!
# The weight factorises along the split, and the sum becomes a product

`PairingGlue.splitEquiv` moved the INDEX SETS: a perfect matching respecting a split is a pair of
perfect matchings, one per side. **It said nothing about the weight.** This file supplies that,
and with it the thing the three previous files were for:

```
∑ over matchings respecting the split  =  (∑ over one side) · (∑ over the other)
```

and hence, with `PairingSplit.sum_prod_eq_sum_respects`, **the whole pairing sum factorises when
the weight across the split vanishes.**

## Where the work is

`PairWeightRep.prod_repSet_eq` already says a pairing product does not depend on which
representative is taken from each pair, so the `<`-filter is a device. What has to be checked is
that the device **restricts correctly**: `x < g x` inside the subtype is `(x : ι) < σ x` outside
it, because a subtype of a linear order carries the restricted order. That is why the two products
below are over `<`-filters in the subtypes rather than over images of a filter in `ι` — the
statement is then about each side on its own terms, and `Finset.prod_nbij'` carries it across with
the inclusion and its partial inverse.

## What is proved

* **`prod_lt_split`** — a pairing product over `ι` is the product of the two sides' pairing
  products, for a matching respecting the split;
* **`sum_respecting_eq_mul`** — hence the sum over the respecting matchings is a product of the
  two sides' sums, by `Fintype.sum_equiv` along `PairingGlue.splitEquiv` and
  `Finset.sum_mul_sum`;
* **`sum_prod_eq_mul`** — and composing with `PairingSplit.sum_prod_eq_sum_respects`: **when the
  weight across the split vanishes, the whole pairing sum is the product of the two sides' sums.**
* **`prod_lt_split_fin_four`** — **the check**, and it is possible only because `prod_lt_split`
  does NOT assume the weight symmetric: if the `<`-filter inside a subtype picked the other
  representative of a pair, the factor would come out as `w j i` rather than `w i j`, and an
  asymmetric weight sees the difference. The instance is `Fin 4` split as `{0, 2}` — **not an
  interval**, so the subtype's order is not the identity on a block — with the matching pairing
  `0` with `2` and `1` with `3`. `respectsSplit_fin_four` and `mem_perfectMatchings_fin_four`
  establish by `decide` that the instance really is one, rather than asserting it.

## What is NOT here

**The measure.** Turning `sum_prod_eq_mul` into a statement about `∫ ∏ᵢ⟪aᵢ,ω⟫` needs
`IsserlisAll.isserlisGeneral_all` on each side, and `IsserlisGeneral` is stated at `Fin k` while
the sides here are subtypes of `Fin k` — so a relabelling `↥S ≃ Fin S.card` has to be carried
through `perfectMatchings` and `pairProduct`, which is `PairingRecursion`'s transport again and is
**not done here**. **Not costed** (`ERRATUM 194`). No measure, integral or test function appears
below.

**⚠ ANSWERED, pointer added 2026-08-27 (`ERRATUM 314`); kept as written (`ERRATUM 94`).**
`PairingCluster.integral_prod_sub_mul_eq` carries it, with `PairingRelabel.sum_pm_eq_integral`
doing the subtype relabelling this paragraph describes.
-/

namespace PairingWeight

open Equiv Function Involutions PairWeightRep PairingSplit PairingRestrict PairingGlue

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-! ## 1. The product splits -/

/-- **A PAIRING PRODUCT IS THE PRODUCT OF THE TWO SIDES' PAIRING PRODUCTS.** The `<`-filters are
taken inside each subtype, which is the same condition as outside it because a subtype of a linear
order carries the restricted order. -/
theorem prod_lt_split {S : Finset ι} {σ : Equiv.Perm ι} (h : RespectsSplit S σ) (w : ι → ι → ℝ) :
    ∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)
      = (∏ x ∈ Finset.univ.filter (fun x : {x : ι // x ∈ S} => x < restrict S σ h x),
            w x (restrict S σ h x))
        * (∏ y ∈ Finset.univ.filter (fun y : {y : ι // y ∉ S} => y < restrictCompl S σ h y),
            w y (restrictCompl S σ h y)) := by
  classical
  rw [← PairingRestrict.prod_split S (Finset.univ.filter (fun i => i < σ i))
        (fun i => w i (σ i))]
  congr 1
  · refine Finset.prod_bij'
      (fun (a : ι) (ha : a ∈ (Finset.univ.filter (fun i => i < σ i)).filter
        (fun i => i ∈ S)) => (⟨a, (Finset.mem_filter.mp ha).2⟩ : {x : ι // x ∈ S}))
      (fun (b : {x : ι // x ∈ S}) _ => (b : ι)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have h2 := (Finset.mem_filter.mp ha).1
      have hlt : a < σ a := (Finset.mem_filter.mp h2).2
      simpa [Finset.mem_filter, Subtype.coe_lt_coe] using hlt
    · intro b hb
      have hlt : (b : ι) < σ (b : ι) := by
        simpa [Finset.mem_filter, Subtype.coe_lt_coe] using (Finset.mem_filter.mp hb).2
      simp [Finset.mem_filter, hlt, b.2]
    · intro a _; rfl
    · intro b _; rfl
    · intro a _; rfl
  · refine Finset.prod_bij'
      (fun (a : ι) (ha : a ∈ (Finset.univ.filter (fun i => i < σ i)).filter
        (fun i => i ∉ S)) => (⟨a, (Finset.mem_filter.mp ha).2⟩ : {y : ι // y ∉ S}))
      (fun (b : {y : ι // y ∉ S}) _ => (b : ι)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have h2 := (Finset.mem_filter.mp ha).1
      have hlt : a < σ a := (Finset.mem_filter.mp h2).2
      simpa [Finset.mem_filter, Subtype.coe_lt_coe] using hlt
    · intro b hb
      have hlt : (b : ι) < σ (b : ι) := by
        simpa [Finset.mem_filter, Subtype.coe_lt_coe] using (Finset.mem_filter.mp hb).2
      simp [Finset.mem_filter, hlt, b.2]
    · intro a _; rfl
    · intro b _; rfl
    · intro a _; rfl

/-! ## 2. The sum becomes a product -/

omit [LinearOrder ι] in
/-- The filtered sum over `↑(perfectMatchings ι)` read as a sum over the subtype `splitEquiv`
lives on. Bookkeeping, and stated separately so the theorem below is about the bijection. -/
theorem sum_filter_eq_sum_subtype (S : Finset ι) (F : Equiv.Perm ι → ℝ) :
    ∑ σ ∈ Finset.univ.filter (fun σ : ↑(perfectMatchings ι) => RespectsSplit S σ.1), F σ.1
      = ∑ σ : {σ : Equiv.Perm ι // σ ∈ perfectMatchings ι ∧ RespectsSplit S σ}, F σ.1 := by
  classical
  refine Finset.sum_bij'
    (fun (a : ↑(perfectMatchings ι)) ha =>
      (⟨a.1, a.2, (Finset.mem_filter.mp ha).2⟩ :
        {σ : Equiv.Perm ι // σ ∈ perfectMatchings ι ∧ RespectsSplit S σ}))
    (fun b _ => (⟨b.1, b.2.1⟩ : ↑(perfectMatchings ι))) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro b _; simp [Finset.mem_filter, b.2.2]
  · intro a _; rfl
  · intro b _; rfl
  · intro a _; rfl

/-- **THE SUM OVER THE RESPECTING MATCHINGS IS A PRODUCT OF THE TWO SIDES' SUMS.**
`Fintype.sum_equiv` along `PairingGlue.splitEquiv`, with `prod_lt_split` identifying the
summands, then `Finset.sum_mul_sum` read backwards. -/
theorem sum_respecting_eq_mul (S : Finset ι) (w : ι → ι → ℝ) :
    ∑ σ : {σ : Equiv.Perm ι // σ ∈ perfectMatchings ι ∧ RespectsSplit S σ},
        ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), w i (σ.1 i)
      = (∑ g : ↑(perfectMatchings {x : ι // x ∈ S}),
            ∏ x ∈ Finset.univ.filter (fun x => x < g.1 x), w x (g.1 x))
        * (∑ k : ↑(perfectMatchings {y : ι // y ∉ S}),
            ∏ y ∈ Finset.univ.filter (fun y => y < k.1 y), w y (k.1 y)) := by
  classical
  rw [Finset.sum_mul_sum Finset.univ Finset.univ
      (fun g : ↑(perfectMatchings {x : ι // x ∈ S}) =>
        ∏ x ∈ Finset.univ.filter (fun x => x < g.1 x), w x (g.1 x))
      (fun k : ↑(perfectMatchings {y : ι // y ∉ S}) =>
        ∏ y ∈ Finset.univ.filter (fun y => y < k.1 y), w y (k.1 y)),
    ← Fintype.sum_prod_type
      (fun p : ↑(perfectMatchings {x : ι // x ∈ S}) × ↑(perfectMatchings {y : ι // y ∉ S}) =>
        (∏ x ∈ Finset.univ.filter (fun x => x < p.1.1 x), w x (p.1.1 x))
          * ∏ y ∈ Finset.univ.filter (fun y => y < p.2.1 y), w y (p.2.1 y))]
  exact Fintype.sum_equiv (splitEquiv S) _ _ fun σ => prod_lt_split σ.2.2 w

/-- **AND THE WHOLE PAIRING SUM FACTORISES WHEN THE WEIGHT ACROSS THE SPLIT VANISHES.**
`PairingSplit.sum_prod_eq_sum_respects` collapses the sum onto the respecting matchings and this
file turns that into a product. -/
theorem sum_prod_eq_mul {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i) {S : Finset ι}
    (hzero : ∀ i ∈ S, ∀ j ∉ S, w i j = 0) :
    ∑ σ : ↑(perfectMatchings ι), ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), w i (σ.1 i)
      = (∑ g : ↑(perfectMatchings {x : ι // x ∈ S}),
            ∏ x ∈ Finset.univ.filter (fun x => x < g.1 x), w x (g.1 x))
        * (∑ k : ↑(perfectMatchings {y : ι // y ∉ S}),
            ∏ y ∈ Finset.univ.filter (fun y => y < k.1 y), w y (k.1 y)) := by
  rw [PairingSplit.sum_prod_eq_sum_respects hw hzero,
    sum_filter_eq_sum_subtype S (fun σ => ∏ i ∈ Finset.univ.filter (fun i => i < σ i), w i (σ i)),
    sum_respecting_eq_mul S w]

/-! ## 3. The check

`prod_lt_split` does NOT assume the weight symmetric, and that is what makes a check possible:
if the `<`-filter inside a subtype picked the other representative of a pair, the factor would
come out as `w j i` rather than `w i j` and an asymmetric weight would see the difference. The
instance below is chosen so that both failure modes are live — the split `{0, 2}` is **not an
interval**, so the subtype's order is not merely the identity on a block, and the matching pairs
across the gaps. -/

/-- **THE CHECK.** At `Fin 4` split as `{0, 2}` and `{1, 3}`, with the matching pairing `0` with
`2` and `1` with `3`, both sides come out as `w 0 2 · w 1 3` — **in that order**, which is what
would fail if the restricted `<` picked the other representative. -/
theorem prod_lt_split_fin_four (w : Fin 4 → Fin 4 → ℝ) :
    ∏ i ∈ Finset.univ.filter
        (fun i => i < (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i),
      w i ((Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i) = w 0 2 * w 1 3 := by
  have hf : Finset.univ.filter
      (fun i => i < (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i)
      = ({0, 1} : Finset (Fin 4)) := by decide
  have h0 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 0 = 2 := by decide
  have h1 : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) 1 = 3 := by decide
  rw [hf, Finset.prod_insert (by decide), Finset.prod_singleton, h0, h1]

/-- And the matching used above really does respect the split, which is the hypothesis
`prod_lt_split` consumes. By `decide`, so the instance is not merely asserted to be one. -/
theorem respectsSplit_fin_four :
    RespectsSplit ({0, 2} : Finset (Fin 4))
      (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) := by decide

/-- And it is a perfect matching. -/
theorem mem_perfectMatchings_fin_four :
    (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ∈ perfectMatchings (Fin 4) := by
  refine ⟨?_, ?_⟩
  · intro x; revert x; decide
  · intro x; revert x; decide

end PairingWeight
