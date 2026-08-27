import Involutions

/-!
# The involution split, carrying a weight

`Involutions` §7 and §9 split the involutions of `Option α` by where `none` goes, and use the
split to **count**: `card_involutions_option` and `card_perfectMatchings_option`. This file
carries the same split with a **weight** attached, so that a sum of anything over the
involutions — not only the constant `1` — obeys the recursion.

## Why this is the next thing and not a generalisation for its own sake

`LatticeSteinMajorant` pays the analytic half of a ladder rung at every order. **The other half
is this.** Rung `k` of that ladder closes as

```
∫ ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫ = (∑_{σ ∈ involutions (Fin k)} pairWeight σ)·exp(½⟨f,Gf⟩),
```

where `σ`'s term pairs the indices `σ` moves and contracts the ones it fixes against `f` — and
the induction on `k` needs exactly a rule for `∑_{σ ∈ involutions (Option α)} w σ` in terms of
sums over `involutions α`. The counting lemmas are that rule at `w = 1`, which is the case that
carries no information about which involution contributed what.

`WickPairings.IsserlisGeneral`'s right-hand side is a sum over `perfectMatchings` of
`pairProduct`, so §3 applies to it verbatim at `w = pairProduct`. **What that gives is the INDEX
recursion and not yet Wick's recursion.** Wick's needs the weight to FACTOR — the `pairProduct`
of the assembled permutation as `⟨a_none, G a_b⟩` times the `pairProduct` of what is left — and
nothing here proves that factorisation or even states it. The index side is one of two halves
and this file claims only that one.

## What is proved

* `sum_involutions_option` — a weight summed over `involutions (Option α)` is its value on the
  involutions fixing `none`, plus, for each `b`, its value on those swapping `none` with `b`;
* `sum_perfectMatchings_option` — the same for `perfectMatchings`, where the `none`-fixing part
  is empty and only the swaps survive;
* `card_involutions_option_of_sum`, `card_perfectMatchings_option_of_sum` — the counting lemmas
  of `Involutions` recovered as the case `w = 1`, proved here from the weighted forms. Stated so
  that the generalisation is checked against what it claims to generalise rather than asserted
  to.

**WHAT IS NOT HERE.** No weight of interest is defined and no ladder rung is closed. This is the
index-side identity; the term a rung actually carries — a product of propagators over the pairs
and of `⟨f,Ga⟩` over the fixed points — is not written down anywhere yet, and neither is its
derivative. **Not costed** (`ERRATUM 194`).

**⚠ SUPERSEDED 2026-08-27, kept as written (`ERRATUM 94`).** *"is not written down anywhere yet,
and neither is its derivative"* — both exist. The term is `SteinSumRecursion.steinTerm`, its
derivative is `LatticeSteinLadder.hasDerivAt_steinSum`, and `LadderStep.ladder` closes the rung at
every order. **One word dated it**: *"anywhere"* is a claim about the estate, which any later file
can falsify, where *"not here"* would have stayed true for ever (`ERRATUM 302`).
-/

namespace InvolutionSums

open Equiv Function Involutions

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## 1. The fibre predicates, and their two values

`Involutions.mem_involutions_option_iff` says `σ` is an involution of `Option α` exactly when the
pair `Equiv.Perm.decomposeOption σ = (a, f)` satisfies `optPred a f` below. Everything in this
file is that statement summed. -/

omit [Fintype α] [DecidableEq α] in
/-- The condition `Involutions.mem_involutions_option_iff` puts on `decomposeOption σ`. -/
def optPred (a : Option α) (f : Equiv.Perm α) : Prop :=
  f ∈ involutions α ∧ ∀ b, a = some b → f b = b

instance decidableOptPred (a : Option α) : DecidablePred (optPred (α := α) a) := fun f => by
  unfold optPred involutions Function.Involutive
  infer_instance

instance decidablePmPred (a : Option α) : DecidablePred (pmPred (α := α) a) := fun f => by
  unfold pmPred
  infer_instance

omit [Fintype α] [DecidableEq α] in
/-- At `none` the side condition is vacuous. -/
theorem optPred_none (f : Equiv.Perm α) : optPred (none : Option α) f ↔ f ∈ involutions α := by
  simp [optPred]

omit [Fintype α] [DecidableEq α] in
/-- At `some b` it is exactly "fixes `b`". -/
theorem optPred_some (b : α) (f : Equiv.Perm α) :
    optPred (some b) f ↔ (f ∈ involutions α ∧ f b = b) := by
  constructor
  · rintro ⟨hf, hb⟩; exact ⟨hf, hb b rfl⟩
  · rintro ⟨hf, hb⟩
    refine ⟨hf, fun c hc => ?_⟩
    cases Option.some_injective _ hc
    exact hb

omit [Fintype α] [DecidableEq α] in
/-- A perfect matching never sends `none` to `none`. -/
theorem pmPred_none (f : Equiv.Perm α) : ¬ pmPred (none : Option α) f := by
  rintro ⟨b, hb, -⟩
  exact absurd hb (by simp)

omit [Fintype α] [DecidableEq α] in
/-- And at `some b` the surviving `f` fixes `b` and nothing else. -/
theorem pmPred_some (b : α) (f : Equiv.Perm α) : pmPred (some b) f ↔ f ∈ onlyFixing b := by
  constructor
  · rintro ⟨c, hc, hf⟩
    cases Option.some_injective _ hc
    exact hf
  · intro hf
    exact ⟨b, rfl, hf⟩

omit [Fintype α] in
/-- The reassembly every weight below is evaluated at: `σ` is recovered from its pair. -/
theorem swap_optionCongr_decomposeOption (σ : Equiv.Perm (Option α)) :
    Equiv.swap none (Equiv.Perm.decomposeOption σ).1
        * Equiv.optionCongr (Equiv.Perm.decomposeOption σ).2 = σ := by
  rw [← Equiv.Perm.decomposeOption_symm_apply, Equiv.symm_apply_apply]

/-! ## 2. The weighted split for involutions -/

/-- **THE SPLIT, CARRYING A WEIGHT.** A sum over the involutions of `Option α` is the sum over
those fixing `none` -- which are the involutions of `α`, embedded by `optionCongr` -- plus, for
each `b : α`, the sum over those swapping `none` with `b`, which are the involutions of `α`
fixing `b`. `Involutions.card_involutions_option` is the case `w = 1`, and §4 proves it is. -/
theorem sum_involutions_option {M : Type*} [AddCommMonoid M]
    (w : Equiv.Perm (Option α) → M) :
    ∑ σ : ↑(involutions (Option α)), w σ.1
      = ∑ g : ↑(involutions α), w (Equiv.optionCongr g.1)
        + ∑ b : α, ∑ g : {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b},
            w (Equiv.swap none (some b) * Equiv.optionCongr g.1) := by
  have hstep : ∑ σ : ↑(involutions (Option α)), w σ.1
      = ∑ p : Σ a : Option α, {f : Equiv.Perm α // optPred a f},
          w (Equiv.swap none p.1 * Equiv.optionCongr p.2.1) := by
    refine Fintype.sum_equiv
      ((Equiv.subtypeEquiv Equiv.Perm.decomposeOption
          (fun σ => mem_involutions_option_iff σ)).trans
        (prodSubtypeEquivSigma (fun (a : Option α) (f : Equiv.Perm α) => optPred a f)))
      _ _ fun σ => ?_
    exact congrArg w (swap_optionCongr_decomposeOption σ.1).symm
  rw [hstep, Fintype.sum_sigma, Fintype.sum_option]
  dsimp only
  congr 1
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight optPred_none) _ _ fun g => ?_
    simp
  · refine Finset.sum_congr rfl fun b _ => ?_
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight (optPred_some b)) _ _ fun g => rfl

/-! ## 3. The weighted split for perfect matchings

Here the `none`-fixing part is **empty**: a perfect matching has no fixed point, so `none` must
be swapped with some `b`, and the surviving `f` fixes `b` **and nothing else**. That is
`Involutions.onlyFixing b`. -/

/-- **THE INDEX RECURSION WICK'S RECURSION RUNS ON.** A weight summed over the perfect matchings
of `Option α` is, for each `b : α`, the sum over the involutions of `α` whose only fixed point is
`b`. `w = 1` is `Involutions.card_perfectMatchings_option`, and §4 proves it is. **This is not
Wick's recursion**: that one also needs the weight to factor across the split, which is a
statement about `WickPairings.pairProduct` and is nowhere here. -/
theorem sum_perfectMatchings_option {M : Type*} [AddCommMonoid M]
    (w : Equiv.Perm (Option α) → M) :
    ∑ σ : ↑(perfectMatchings (Option α)), w σ.1
      = ∑ b : α, ∑ g : ↑(onlyFixing b),
          w (Equiv.swap none (some b) * Equiv.optionCongr g.1) := by
  have hstep : ∑ σ : ↑(perfectMatchings (Option α)), w σ.1
      = ∑ p : Σ a : Option α, {f : Equiv.Perm α // pmPred a f},
          w (Equiv.swap none p.1 * Equiv.optionCongr p.2.1) := by
    refine Fintype.sum_equiv
      ((Equiv.subtypeEquiv Equiv.Perm.decomposeOption
          (fun σ => mem_perfectMatchings_option_iff σ)).trans
        (prodSubtypeEquivSigma (fun (a : Option α) (f : Equiv.Perm α) => pmPred a f)))
      _ _ fun σ => ?_
    exact congrArg w (swap_optionCongr_decomposeOption σ.1).symm
  rw [hstep, Fintype.sum_sigma, Fintype.sum_option]
  dsimp only
  have hnone : ∑ g : {f : Equiv.Perm α // pmPred (none : Option α) f},
      w (Equiv.swap none (none : Option α) * Equiv.optionCongr g.1) = 0 :=
    Finset.sum_eq_zero fun g _ => absurd g.2 (pmPred_none g.1)
  rw [hnone, zero_add]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight (pmPred_some b)) _ _ fun g => rfl

/-! ## 4. The counts recovered, so the generalisation is checked and not merely claimed -/

/-- **A CHECK THE COUNTS CANNOT PERFORM, AND THE REASON IT IS HERE.** §4's two specialisations
take `w = 1`, and **a cardinality is blind to which involution sits in which fibre**: the split
would count correctly with `Equiv.swap none (some b)` replaced by any other permutation of the
same fibres, so `w = 1` tests the sizes and nothing about the embedding. This weight is not
blind. `σ ↦ [σ none = none]` is `1` exactly on the `none`-fixing part, so the first summand has
to carry the whole answer and **every `b`-summand has to vanish** — which happens only because
the `b`-fibre's permutations really do send `none` to `some b`. -/
theorem sum_involutions_option_fixes_none :
    ∑ σ : ↑(involutions (Option α)), (if σ.1 none = none then 1 else 0 : ℕ)
      = Fintype.card ↑(involutions α) := by
  rw [sum_involutions_option (M := ℕ) (fun σ => if σ none = none then 1 else 0)]
  simp [Finset.card_univ]


/-- `Involutions.card_involutions_option` as the case `w = 1`. Stated because a weighted lemma
that did not specialise back to the count it generalises would be a different lemma wearing its
name. -/
theorem card_involutions_option_of_sum :
    Fintype.card ↑(involutions (Option α))
      = Fintype.card ↑(involutions α)
        + ∑ b : α, Fintype.card {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b} := by
  have h := sum_involutions_option (α := α) (M := ℕ) (fun _ => 1)
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] using h

/-- And `Involutions.card_perfectMatchings_option` likewise. -/
theorem card_perfectMatchings_option_of_sum :
    Fintype.card ↑(perfectMatchings (Option α))
      = ∑ b : α, Fintype.card ↑(onlyFixing b) := by
  have h := sum_perfectMatchings_option (α := α) (M := ℕ) (fun _ => 1)
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ] using h

end InvolutionSums
