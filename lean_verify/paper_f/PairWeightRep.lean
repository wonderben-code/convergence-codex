import Involutions
import InvolutionSums

/-!
# A pairing's weight is a function of the pairing, not of the order used to write it

`WickPairings.pairProduct` writes the term a perfect matching `σ` contributes to Isserlis as

```
∏_{i : i < σ i} ⟨f i, G f (σ i)⟩,
```

taking one index per pair by **comparing them** — which is why it is stated over `Fin n` and not
over an arbitrary finite index set. The comparison is a device for choosing representatives, and
nothing in this estate says the answer does not depend on the device. This file says it, and the
statement is what makes the pairing recursion writable.

## Why it is needed and not merely tidy

`InvolutionSums.sum_perfectMatchings_option` splits a sum over `perfectMatchings (Option α)` into
one sum per `b : α` over the involutions of `α` fixing only `b`, at the permutation
`swap none (some b) * optionCongr g`. To make that Wick's recursion the WEIGHT has to factor
across the split — `⟨f none, G f (some b)⟩` times the weight of `g` — and to state that at all
one needs the weight at index type `Option α`. **`Option α` carries no `LinearOrder` in Mathlib**,
so the `Fin n`-with-`<` formulation cannot even be written there. Representatives, not
comparisons, are what the recursion needs.

## What is proved

* `IsRepSet σ S` — `S` picks exactly one index out of each pair `σ` moves, and no fixed point;
* `prod_repSet_eq` — **for a SYMMETRIC weight the product over `S` does not depend on `S`.**
  Symmetry is exactly the hypothesis that makes "one of the two" meaningful, and
  `LatticeIsserlisSmeared.dotG_comm` supplies it for the Green form;
* `isRepSet_filter_lt` — and `WickPairings.pairProduct`'s own `filter (· < σ ·)` is such an `S`,
  at any linear order, so `pairProduct` is the general construction seen through one device;
* `isRepSet_option`, `prod_repSet_option` — **the factorisation across the `Option` split**:
  `w none (some b)` times the weight of `g`, for any involution `g` of `α` fixing `b`;
* `sum_prod_perfectMatchings_option` — and therefore, combined with
  `InvolutionSums.sum_perfectMatchings_option`, **the pairing-side recursion at index type
  `Option α`**;
* `repSet_swap_swap` — a concrete case computed by `decide`, so that `IsRepSet` is checked to
  mean what the paragraph above says rather than only to typecheck.

**WHAT IS NOT HERE, AND THERE ARE TWO THINGS.**

**(1) THE BRIDGE TO `Fin n`.** `WickPairings.IsserlisGeneral` sums `pairProduct` over
`perfectMatchings (Fin k)`, and §5's recursion is at `Option α`. Turning one into the other needs
`Fin (n+1) ≃ Option (Fin n)` transported through `perfectMatchings` **together with the order**,
and that is not written here. What §3 does give is that the transport cannot change the value: the
`filter (· < ·)` device is one representative set among many and §2 says they all agree. So the
bridge is bookkeeping rather than mathematics — which is a claim about its KIND and not about its
size, and **no estimate is offered** (`ERRATUM 194`).

**(2) THE OTHER SIDE OF THE EQUATION.** The recursion proved here is obeyed by the RIGHT-hand side
of `IsserlisGeneral`. **The left-hand side — the Gaussian integral — obeys no proved recursion in
this estate at general order**; that is the ladder, whose analytic half is
`LatticeSteinMajorant` and whose closed-form derivative is untouched. The two sides are not
matched and general Isserlis does not follow from anything here.

No measure, integral or test function appears below; the file is pure combinatorics so that the
Gaussian chain can import it.
-/

namespace PairWeightRep

open Equiv Function Involutions

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*} [CommMonoid M]

/-! ## 1. Representative sets -/

/-- `S` picks exactly one index out of every pair `σ` moves, and contains no fixed point. -/
def IsRepSet (σ : Equiv.Perm ι) (S : Finset ι) : Prop :=
  (∀ i ∈ S, σ i ≠ i) ∧ (∀ i, σ i ≠ i → (i ∈ S ↔ σ i ∉ S))

omit [Fintype ι] [DecidableEq ι] in
theorem IsRepSet.ne {σ : Equiv.Perm ι} {S : Finset ι} (h : IsRepSet σ S) {i : ι} (hi : i ∈ S) :
    σ i ≠ i := h.1 i hi

omit [Fintype ι] [DecidableEq ι] in
/-- The partner of a member is not a member. -/
theorem IsRepSet.partner_notMem {σ : Equiv.Perm ι} {S : Finset ι} (h : IsRepSet σ S) {i : ι}
    (hi : i ∈ S) : σ i ∉ S := (h.2 i (h.ne hi)).mp hi

omit [Fintype ι] [DecidableEq ι] in
/-- And the partner of a non-member that `σ` moves IS a member. -/
theorem IsRepSet.partner_mem {σ : Equiv.Perm ι} {S : Finset ι} (h : IsRepSet σ S) {i : ι}
    (hmv : σ i ≠ i) (hi : i ∉ S) : σ i ∈ S := by
  by_contra hc
  exact hi ((h.2 i hmv).mpr hc)

/-! ## 2. The product does not depend on the representatives

The hypothesis doing the work is that `w` is **symmetric**. Without it "one index per pair" is
not a well-posed instruction, since the two choices give `w i (σ i)` and `w (σ i) i`. -/

omit [Fintype ι] [DecidableEq ι] in
/-- **THE INDEPENDENCE.** For an involution and a symmetric weight, any two representative sets
give the same product. The bijection sends a representative to itself when the other set already
contains it, and to its partner otherwise. -/
theorem prod_repSet_eq {σ : Equiv.Perm ι} (hσ : σ ∈ involutions ι) {w : ι → ι → M}
    (hw : ∀ i j, w i j = w j i) {S T : Finset ι} (hS : IsRepSet σ S) (hT : IsRepSet σ T) :
    ∏ i ∈ S, w i (σ i) = ∏ i ∈ T, w i (σ i) := by
  classical
  refine Finset.prod_bij' (fun a _ => if a ∈ T then a else σ a)
    (fun a _ => if a ∈ S then a else σ a) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    by_cases h : a ∈ T
    · simp [h]
    · simpa [h] using hT.partner_mem (hS.ne ha) h
  · intro a ha
    by_cases h : a ∈ S
    · simp [h]
    · simpa [h] using hS.partner_mem (hT.ne ha) h
  · intro a ha
    by_cases h : a ∈ T
    · simp [h, ha]
    · have hmem : σ a ∈ T := hT.partner_mem (hS.ne ha) h
      have hnot : σ a ∉ S := hS.partner_notMem ha
      simp [h, hnot, hσ a]
  · intro a ha
    by_cases h : a ∈ S
    · simp [h, ha]
    · have hmem : σ a ∈ S := hS.partner_mem (hT.ne ha) h
      have hnot : σ a ∉ T := hT.partner_notMem ha
      simp [h, hnot, hσ a]
  · intro a ha
    by_cases h : a ∈ T
    · simp [h]
    · simp only [h, if_false, hσ a]
      exact hw a (σ a)

/-! ## 3. `pairProduct`'s own choice is one of them -/

omit [DecidableEq ι] in
/-- **THE COMPARISON DEVICE IS A REPRESENTATIVE SET.** At any linear order on the index type,
`{i | i < σ i}` picks exactly one index per pair — the two are distinct because `σ` moves them,
and `σ i < σ (σ i) = i` is the negation of `i < σ i`. So `WickPairings.pairProduct` is §2's
construction seen through one device, and by §2 the device does not matter. -/
theorem isRepSet_filter_lt [LinearOrder ι] {σ : Equiv.Perm ι} (hσ : σ ∈ involutions ι) :
    IsRepSet σ (Finset.univ.filter (fun i => i < σ i)) := by
  constructor
  · intro i hi
    simp only [Finset.mem_filter] at hi
    exact ne_of_gt hi.2
  · intro i hmv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ i]
    constructor
    · intro h hc
      exact absurd (h.trans hc) (lt_irrefl i)
    · intro h
      rcases lt_trichotomy i (σ i) with hlt | heq | hgt
      · exact hlt
      · exact absurd heq.symm hmv
      · exact absurd hgt h

/-! ## 3b. A concrete case, so the definition is checked and not only typechecked -/

/-- `swap 0 1 * swap 2 3` on `Fin 4` pairs `0` with `1` and `2` with `3`, so its `<`-device picks
`{0, 2}` — one index per pair and neither partner. Computed by `decide`, because a definition
that merely typechecks has not yet been read against an example. -/
theorem repSet_swap_swap :
    (Finset.univ.filter (fun i : Fin 4 =>
        i < (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) i)) = {0, 2} := by
  decide

/-! ## 4. The factorisation across the `Option` split

`InvolutionSums.sum_perfectMatchings_option` presents each perfect matching of `Option α` as
`swap none (some b) * optionCongr g` with `g` an involution of `α` fixing `b`. Its pairs are
`{none, some b}` together with the pairs of `g`, so a representative set is `none` together with
the image of one for `g`. -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The assembled permutation, named once. -/
abbrev opt (b : α) (g : Equiv.Perm α) : Equiv.Perm (Option α) :=
  Equiv.swap none (some b) * Equiv.optionCongr g

omit [Fintype α] in
theorem opt_none (b : α) (g : Equiv.Perm α) : opt b g none = some b := by
  simp [opt]

omit [Fintype α] in
theorem opt_some_self {b : α} {g : Equiv.Perm α} (hgb : g b = b) :
    opt b g (some b) = none := by
  simp [opt, hgb]

omit [Fintype α] in
/-- Away from `b` the swap does not fire, because an involution fixing `b` sends nothing else
there. -/
theorem opt_some_of_ne {b : α} {g : Equiv.Perm α} (hg : g ∈ involutions α) (hgb : g b = b)
    {i : α} (hi : i ≠ b) : opt b g (some i) = some (g i) := by
  have hne : g i ≠ b := by
    intro hc
    have h2 : g (g i) = i := hg i
    rw [hc, hgb] at h2
    exact hi h2.symm
  simp [opt, Equiv.swap_apply_of_ne_of_ne, hne]

omit [Fintype α] in
/-- **THE REPRESENTATIVE SET FOR THE ASSEMBLED PERMUTATION**: `none`, and one index per pair
of `g`. -/
theorem isRepSet_option {b : α} {g : Equiv.Perm α} (hg : g ∈ involutions α) (hgb : g b = b)
    {S : Finset α} (hS : IsRepSet g S) :
    IsRepSet (opt b g) (insert none (S.image some)) := by
  have hbS : b ∉ S := fun hc => hS.ne hc hgb
  constructor
  · intro x hx
    rcases x with - | i
    · rw [opt_none]; simp
    · have hiS : i ∈ S := by simpa using hx
      have hib : i ≠ b := fun hc => hbS (hc ▸ hiS)
      rw [opt_some_of_ne hg hgb hib]
      simpa using hS.ne hiS
  · intro x hmv
    rcases x with - | i
    · rw [opt_none]
      simp [hbS]
    · by_cases hib : i = b
      · subst hib
        rw [opt_some_self hgb]
        simp [hbS]
      · rw [opt_some_of_ne hg hgb hib]
        have hgi : g i ≠ i := by
          intro hc
          exact hmv (by rw [opt_some_of_ne hg hgb hib, hc])
        have := hS.2 i hgi
        simpa using this

omit [Fintype α] in
/-- **THE WEIGHT FACTORS**: the `none` pair contributes `w none (some b)`, and the rest is the
weight of `g` at the transported index. -/
theorem prod_repSet_option {b : α} {g : Equiv.Perm α} (hg : g ∈ involutions α) (hgb : g b = b)
    {S : Finset α} (hS : IsRepSet g S) (w : Option α → Option α → M) :
    ∏ x ∈ insert none (S.image some), w x (opt b g x)
      = w none (some b) * ∏ i ∈ S, w (some i) (some (g i)) := by
  have hbS : b ∉ S := fun hc => hS.ne hc hgb
  have hnot : (none : Option α) ∉ S.image some := by simp
  rw [Finset.prod_insert hnot, opt_none,
    Finset.prod_image (fun x _ y _ h => Option.some_injective _ h)]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hib : i ≠ b := fun hc => hbS (hc ▸ hi)
  rw [opt_some_of_ne hg hgb hib]

/-! ## 5. The pairing-side recursion, assembled

The statement takes the representative choices as arguments on both sides, which is what makes it
a theorem rather than a definition: §2 is what lets an ARBITRARY choice on the left be replaced by
the structured one §4 factors. -/

/-- **WICK'S RECURSION ON THE PAIRING SIDE.** A symmetric weight summed over the perfect matchings
of `Option α`, each term taken at whatever representatives the caller chose, equals `∑_b` of
`w none (some b)` times the same weight summed over the involutions of `α` whose only fixed point
is `b`. `InvolutionSums.sum_perfectMatchings_option` supplies the index split, §4 the
factorisation, and §2 the fact that neither side depends on the choices. -/
theorem sum_prod_perfectMatchings_option {R : Type*} [CommSemiring R]
    (w : Option α → Option α → R)
    (hw : ∀ x y, w x y = w y x)
    (rep : Equiv.Perm (Option α) → Finset (Option α))
    (hrep : ∀ σ ∈ perfectMatchings (Option α), IsRepSet σ (rep σ))
    (repα : Equiv.Perm α → Finset α)
    (hrepα : ∀ (b : α) (g : Equiv.Perm α), g ∈ onlyFixing b → IsRepSet g (repα g)) :
    ∑ σ : ↑(perfectMatchings (Option α)), ∏ x ∈ rep σ.1, w x (σ.1 x)
      = ∑ b : α, w none (some b) * ∑ g : ↑(onlyFixing b),
          ∏ i ∈ repα g.1, w (some i) (some (g.1 i)) := by
  rw [InvolutionSums.sum_perfectMatchings_option (fun σ => ∏ x ∈ rep σ, w x (σ x))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hgO : g.1 ∈ onlyFixing b := g.2
  have hgi : g.1 ∈ involutions α := hgO.1
  have hgb : g.1 b = b := (hgO.2 b).mpr rfl
  have hmem : opt b g.1 ∈ perfectMatchings (Option α) :=
    (perfectMatching_swap_optionCongr_iff (some b) g.1).mpr ⟨b, rfl, hgO⟩
  have hopt : opt b g.1 ∈ involutions (Option α) := hmem.1
  rw [prod_repSet_eq hopt hw (hrep _ hmem)
      (isRepSet_option hgi hgb (hrepα b g.1 hgO)),
    prod_repSet_option hgi hgb (hrepα b g.1 hgO) w]

end PairWeightRep
