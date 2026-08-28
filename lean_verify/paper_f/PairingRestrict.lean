import PairingSplit

/-!
# Restricting a matching to one side of a split

`PairingSplit.sum_prod_eq_sum_respects` collapsed the pairing sum onto the matchings that respect
a split, when the weight across the split vanishes. **What the collapsed sum is not yet is a
product.** Turning `∑ over the respecting matchings` into `(∑ over one side)·(∑ over the other)`
needs a matching that respects the split to BE a pair of matchings, one per side, with the weight
product factorising along it. This file is the first direction of that: **restriction**.

Mathlib's `Equiv.Perm.subtypePerm` does the work once the hypothesis is in its shape, and
`RespectsSplit` is already stated as the `Iff` it wants. What has to be checked here is that the
restriction of a perfect matching is a perfect matching — involutive is immediate, **fixed-point
free is the clause that could fail** and does not, because a fixed point of the restriction is a
fixed point of the original at a point of `S`.

## What is proved

* `restrict` — the restriction of `σ` to `↥S`, for `σ` respecting the split;
* `restrict_apply_coe`, `restrict_involutive` — its value and its involutivity;
* **`restrict_mem_perfectMatchings`** — and it is a perfect matching;
* `restrict_compl` — the same on the other side, from `RespectsSplit`'s complement form;
* **`prod_split`** — a product over a representative set is the product over its `S` part times
  the product over its complement part, which is `Finset.prod_filter_mul_prod_filter_not` and is
  stated here so the two halves are named;
* `restrict_isRepSet` — **the `S` part of a representative set is a representative set for the
  restriction**, which is what makes the first factor a pairing product rather than a product
  over an unrelated index set;
* **`even_card_of_respects`**, and its twin at the complement — **the check**. A side of a split
  respected by a perfect matching has EVEN cardinality. Nothing in §1 mentions parity, and
  `Involutions.even_card_of_mem_perfectMatchings` proves it by an argument this file does not
  touch, so a `restrict` producing anything but a genuine perfect matching would not give it.

## What is NOT here

The bijection, and therefore the factorisation. Restriction is one direction; the other is
`Equiv.Perm.subtypeCongr`, and proving the two inverse to each other on perfect matchings is not
done here. Until it is, `∑ over the respecting matchings` is not known to be a product of two
sums and no clustering statement follows. **Not costed** (`ERRATUM 194`). No measure, integral or
test function appears.

**⚠ ANSWERED, pointer added 2026-08-27 (`ERRATUM 314`); kept as written (`ERRATUM 94`).**
`PairingGlue.splitEquiv` is that bijection as an `Equiv`, with `card_respecting` the count it
gives, and `PairingWeight.sum_prod_eq_mul` is the product of two sums this paragraph says does not
follow. Both were built after this file.
-/

namespace PairingRestrict

open Equiv Function Involutions PairWeightRep PairingSplit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The restriction -/

/-- The restriction of `σ` to the side `S` of a split it respects. -/
def restrict (S : Finset ι) (σ : Equiv.Perm ι) (h : RespectsSplit S σ) :
    Equiv.Perm {x : ι // x ∈ S} :=
  σ.subtypePerm fun x => h x

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem restrict_apply_coe {S : Finset ι} {σ : Equiv.Perm ι} (h : RespectsSplit S σ)
    (x : {x : ι // x ∈ S}) : ((restrict S σ h) x : ι) = σ x := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem restrict_involutive {S : Finset ι} {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    (h : RespectsSplit S σ) : Function.Involutive (restrict S σ h) := by
  intro x
  ext
  simp [restrict_apply_coe, hσ (x : ι)]

omit [Fintype ι] [DecidableEq ι] in
/-- **THE RESTRICTION OF A PERFECT MATCHING IS A PERFECT MATCHING.** Involutivity is immediate;
the clause that could fail is fixed-point freeness, and it does not, because a fixed point of the
restriction is a fixed point of `σ` sitting in `S`. -/
theorem restrict_mem_perfectMatchings {S : Finset ι} {σ : Equiv.Perm ι}
    (hσ : σ ∈ perfectMatchings ι) (h : RespectsSplit S σ) :
    restrict S σ h ∈ perfectMatchings {x : ι // x ∈ S} := by
  refine ⟨restrict_involutive hσ.1 h, ?_⟩
  intro x hx
  exact hσ.2 (x : ι) (by simpa using congrArg Subtype.val hx)

/-- The split's other side. `RespectsSplit` is an `Iff`, so its complement form is the same
statement read the other way and needs no separate hypothesis. -/
theorem respectsSplit_compl {S : Finset ι} {σ : Equiv.Perm ι} (h : RespectsSplit S σ) :
    RespectsSplit Sᶜ σ := by
  intro i
  simp only [Finset.mem_compl]
  exact not_congr (h i)

/-! ## 2. The product splits -/

omit [Fintype ι] in
/-- A product over a representative set is its `S` part times its complement part. Named rather
than inlined because the two factors are what the factorisation has to identify. -/
theorem prod_split (S R : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ R.filter (fun i => i ∈ S), f i) * (∏ i ∈ R.filter (fun i => i ∉ S), f i)
      = ∏ i ∈ R, f i :=
  Finset.prod_filter_mul_prod_filter_not R _ f

omit [Fintype ι] in
/-- **AND THE `S` PART OF A REPRESENTATIVE SET IS ONE FOR THE RESTRICTION.** Without this the
first factor of `prod_split` is a product over an index set with no relation to the restricted
matching, and nothing identifies it as that matching's pairing product. -/
theorem restrict_isRepSet {S R : Finset ι} {σ : Equiv.Perm ι} (h : RespectsSplit S σ)
    (hR : IsRepSet σ R) :
    IsRepSet (restrict S σ h)
      (Finset.univ.filter (fun x : {x : ι // x ∈ S} => (x : ι) ∈ R)) := by
  constructor
  · intro x hx
    simp only [Finset.mem_filter] at hx
    intro hfix
    exact hR.1 (x : ι) hx.2 (by simpa using congrArg Subtype.val hfix)
  · intro x hne
    have hne' : σ (x : ι) ≠ (x : ι) := fun hh =>
      hne (by ext; simpa using hh)
    have := hR.2 (x : ι) hne'
    simpa [Finset.mem_filter] using this

/-! ## 3. The check

Restriction is a definition plus two easy proofs, and a definition that is subtly wrong usually
still typechecks. The check is a consequence that would fail if it were: a perfect matching pairs
its index type up, so a side of a split that one respects must have EVEN cardinality. Nothing in
§1 mentions parity, and `Involutions.even_card_of_mem_perfectMatchings` is proved by an argument
about `Fin`-indexed involutions that this file does not touch. -/

omit [Fintype ι] [DecidableEq ι] in
/-- **THE CHECK.** A side of a split respected by a perfect matching has even size. If `restrict`
produced anything but a genuine perfect matching of `↥S`, this would not follow. -/
theorem even_card_of_respects {S : Finset ι} {σ : Equiv.Perm ι}
    (hσ : σ ∈ perfectMatchings ι) (h : RespectsSplit S σ) : Even S.card := by
  have hcard := Involutions.even_card_of_mem_perfectMatchings
    (restrict_mem_perfectMatchings hσ h)
  simpa using hcard

/-- And the other side too, which is the same statement at `Sᶜ` and is stated so that a reader
does not have to notice that `RespectsSplit` is symmetric. -/
theorem even_card_compl_of_respects {S : Finset ι} {σ : Equiv.Perm ι}
    (hσ : σ ∈ perfectMatchings ι) (h : RespectsSplit S σ) : Even Sᶜ.card :=
  even_card_of_respects hσ (respectsSplit_compl h)

end PairingRestrict
