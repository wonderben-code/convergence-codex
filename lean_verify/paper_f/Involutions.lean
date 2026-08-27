import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.GroupTheory.Perm.Option
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Involutions of a finite type: the carrier general-order Wick has no index type for

`UNLOCK_WATCHLIST`, in the probe block on general-order Isserlis, records a fact about Mathlib
and hands the consequence to whoever needs it:

> Perfect matchings exist only as a **PREDICATE** on `SimpleGraph.Subgraph` — `IsPerfectMatching`
> — and **not as an index type one can sum over**. So the right-hand side of general-order
> Isserlis, a sum over pairings, **has no carrier in Mathlib today and the first person to want
> it will have to give one.**

**This gives one, and it gives the more useful one.** The estate's Wick chain
(`LatticeWickRecursion`, `LatticeWickTwo`, `LatticeWickThree`) computes
`∫⟪a₁,ω⟫⋯⟪a_k,ω⟫⟪f,ω⟫^n` for `k = 1, 2, 3`, and the terms of those right-hand sides are indexed
not by *perfect* matchings of the `aᵢ` but by **partial** ones: some of the `aᵢ` pair with each
other, the rest contract with copies of `f`. A partial matching of a set **is an involution of
it**, and the perfect ones are exactly the involutions with no fixed point — which is
`Mathlib`'s `derangements` intersected with these. So one definition carries both.

**AND THE COUNTS ARE THE ESTATE'S FIRST INDEPENDENT CHECK OF ITS OWN WICK COEFFICIENTS.**
`card_involutions_fin` gives `1, 1, 2, 4, 10, 26, 76` for `k = 0 … 6` — the number of terms the
`k`-factor Wick expansion must have, and `4` is exactly the number `LatticeWickThree.wick_three`
has (three pair-and-contract terms plus one all-to-`f` term). `card_perfectMatchings_fin` gives
`1, 0, 1, 0, 3, 0, 15`, and **the `15` is the `5‼` that `LatticeWickTwo.wick_two_order_six` and
`LatticeWickThree.wick_three_order_six` each arrive at by adding two coefficients.** Those two
theorems were proved by differentiating under an integral sign; this number is counted by
`decide` over a permutation group and shares nothing with them.

## What is proved

* `involutions α` — the involutions of `α`, as a **`Set (Equiv.Perm α)`**, in the shape
  `Mathlib`'s `derangements` uses, with `DecidablePred` and hence a `Fintype` on the coercion;
* `mem_involutions_iff_mul_self`, `inv_eq_self_of_mem` — the three usual phrasings agree;
* `perfectMatchings α := involutions α ∩ derangements α`, and `mem_perfectMatchings_iff`;
* `card_involutions_invariant` — the count depends only on `Fintype.card α`, by transport along
  any equivalence, which is what lets `Option (Fin n)` stand in for `Fin (n+1)`;
* `swapCongr_none`, `swapCongr_some` — what `Equiv.swap none a * Equiv.optionCongr f` does to
  each argument, which is where every case split below is decided;
* **`involutive_swap_optionCongr_iff`** — the structural fact, and the file's mathematical
  content. Every permutation of `Option α` is `Equiv.swap none a * Equiv.optionCongr f` for a
  unique `(a, f)` (`Equiv.Perm.decomposeOption`), and it is an involution **exactly when** `f`
  is an involution and, in the case `a = some b`, `f` fixes `b`. Both directions;
* **`even_card_of_mem_perfectMatchings`** — a fixed-point-free involution forces an even
  cardinality, and `perfectMatchings_eq_empty_of_odd`. `IsingContourEnergy` searched Mathlib
  for this in August, found no lemma of that shape, and concluded that without its graph *"the
  parity would have wanted a strong induction"*. **The absence claim is true and that
  consequence is not**: `Equiv.Perm.card_fixedPoints_modEq` gives it in three lines at the prime
  `2`, and a grep over `Even`, `card` and `Involutive` could not have found it because it is
  phrased in `Nat.ModEq` and mentions none of the three;
* `card_involutions_fin_zero … _six` and `card_perfectMatchings_fin_zero … _six` — the two
  sequences, by `decide` over the permutation group, and
  `card_perfectMatchings_fin_six_eq_doubleFactorial` for the check named above;
* `prodSubtypeEquivSigma`, `mem_involutions_option_iff`, `conj_mem_involutions`,
  `conj_swap_fix`, `fixingCongr`/`card_fixing_congr` (the count of involutions fixing a point
  does not depend on the point, by conjugating with the transposition between them),
  `fixingNoneEquiv`/`card_fixing_none` (an involution of `Option β` fixing `none` **is** an
  involution of `β`), and `card_involutions_option`;
* **`card_involutions_option_option`** and **`card_involutions_fin_add_two`** — the recurrence
  `I(n+2) = I(n+1) + (n+1)·I(n)`;
* `numInvolutions` and **`card_involutions_fin_eq_numInvolutions`** — the numbers as a plain `ℕ`
  recursion and the theorem tying it to the count, in the shape Mathlib gives `derangements`.
  **This is what makes the `decide` table a check rather than a duplicate**: `numInvolutions 6`
  computes `76` without mentioning a permutation, §6 gets `76` by testing all `720` of them, and
  the theorem says they must agree — so those seven values test the whole of §7. It is also what
  extends the table: `card_involutions_fin_seven` (`232`), `_eight` (`764`) and `_twelve`
  (`140152`), none of them reachable by `decide` over the group;
* the same decomposition again for the PERFECT matchings, with one extra condition — a
  fixed-point-free involution of `Option α` cannot fix `none`, so it sends `none` to some `b`,
  and the corresponding `f` fixes `b` **and nothing else**: `onlyFixing`, `pmPred`,
  **`perfectMatching_swap_optionCongr_iff`**, `mem_perfectMatchings_option_iff`,
  `conj_swap_onlyFixing`, `onlyFixingCongr`, `onlyFixingNoneEquiv`, `perfectMatchingsCongr`,
  `card_perfectMatchings_option`, `card_perfectMatchings_option_option`, and
  **`card_perfectMatchings_fin_add_two`** — `P(n+2) = (n+1)·P(n)`;
* **`card_perfectMatchings_fin_eq_doubleFactorial`** — hence `P(2k) = (2k−1)‼`, **the
  coefficient general-order Isserlis carries, proved in general rather than checked at one
  value**, with `card_perfectMatchings_fin_odd` for the odd sizes.
  `card_perfectMatchings_fin_six_eq_doubleFactorial` is now its case `k = 3` and is kept
  because that `15` comes from `decide` over `720` permutations: the two agree, which tests §9's
  decomposition the way §8's values test §7's.

## What is NOT proved here

**The map from an involution to the propagator product its term carries.** That map is the
content of Wick's theorem. This file supplies the index set and the coefficient count and says
nothing about what is summed over them.

## What this is NOT

**It is not general-order Isserlis.** It is the index type that statement needs and does not
have; nothing here mentions a Gaussian, an integral or a test function. The watchlist's other
blocker for that theorem — Gaussian integration by parts for the CORRELATED field at a product
observable, which the estate has only for the exponential (`LatticeSteinIdentity`) and for a
power of one test function (`LatticeWickRecursion`) — **is untouched and this does not shorten
it.**

**And the coefficient is not proved either.** Knowing that the terms are indexed by involutions
says nothing about which propagator product each term carries. That map is the content of Wick's
theorem and none of it is here.

**No wall moves. No published tag moves.**
-/

namespace Involutions

open Equiv Function

/-! ## 1. The carrier -/

/-- The involutions of `α`, in the shape `Mathlib`'s `derangements` uses: a `Set (Equiv.Perm α)`
rather than a structure, so that `Fintype.card ↑(involutions α)` is the count. -/
def involutions (α : Type*) : Set (Equiv.Perm α) := {σ | Function.Involutive σ}

instance decidablePredInvolutions (α : Type*) [DecidableEq α] [Fintype α] :
    DecidablePred (· ∈ involutions α) := fun σ => by
  unfold involutions Function.Involutive
  infer_instance

theorem mem_involutions_iff {α : Type*} {σ : Equiv.Perm α} :
    σ ∈ involutions α ↔ Function.Involutive σ := Iff.rfl

/-- Involutive, `σ * σ = 1`, and `σ⁻¹ = σ` are the same condition. -/
theorem mem_involutions_iff_mul_self {α : Type*} {σ : Equiv.Perm α} :
    σ ∈ involutions α ↔ σ * σ = 1 := by
  constructor
  · intro h
    ext x
    simpa using h x
  · intro h x
    have := congrArg (fun τ : Equiv.Perm α => τ x) h
    simpa using this

theorem inv_eq_self_of_mem {α : Type*} {σ : Equiv.Perm α} (h : σ ∈ involutions α) :
    σ⁻¹ = σ := by
  have := mem_involutions_iff_mul_self.mp h
  exact inv_eq_of_mul_eq_one_right this

@[simp] theorem one_mem_involutions (α : Type*) : (1 : Equiv.Perm α) ∈ involutions α :=
  fun _ => rfl

theorem swap_mem_involutions {α : Type*} [DecidableEq α] (a b : α) :
    Equiv.swap a b ∈ involutions α := Equiv.swap_apply_self a b

/-! ## 2. The fixed-point-free ones are the perfect matchings -/

/-- **THE PERFECT MATCHINGS**, as an index type rather than as a predicate on a subgraph: an
involution with no fixed point pairs every element with exactly one other. -/
def perfectMatchings (α : Type*) : Set (Equiv.Perm α) := involutions α ∩ derangements α

theorem mem_perfectMatchings_iff {α : Type*} {σ : Equiv.Perm α} :
    σ ∈ perfectMatchings α ↔ Function.Involutive σ ∧ ∀ x, σ x ≠ x := Iff.rfl

instance decidablePredPerfectMatchings (α : Type*) [DecidableEq α] [Fintype α] :
    DecidablePred (· ∈ perfectMatchings α) := fun σ => by
  unfold perfectMatchings involutions derangements Function.Involutive
  infer_instance

/-- A perfect matching genuinely pairs: `σ x ≠ x` and `σ (σ x) = x`. -/
theorem pairs_of_mem_perfectMatchings {α : Type*} {σ : Equiv.Perm α}
    (h : σ ∈ perfectMatchings α) (x : α) : σ x ≠ x ∧ σ (σ x) = x :=
  ⟨h.2 x, h.1 x⟩

/-! ## 3. The count depends only on the cardinality -/

/-- Transport along an equivalence. This is what lets `Option (Fin n)` stand in for `Fin (n+1)`
below, and it mirrors `Mathlib`'s `card_derangements_invariant`. -/
def involutionsCongr {α β : Type*} (e : α ≃ β) : involutions α ≃ involutions β where
  toFun σ := ⟨(e.permCongr) σ.1, by
    intro x
    simp [Equiv.permCongr_apply, σ.2 (e.symm x)]⟩
  invFun τ := ⟨(e.symm.permCongr) τ.1, by
    intro x
    simp [Equiv.permCongr_apply, τ.2 (e x)]⟩
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp

theorem card_involutions_invariant {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) :
    Fintype.card ↑(involutions α) = Fintype.card ↑(involutions β) :=
  Fintype.card_congr (involutionsCongr e)

/-! ## 4. The structural fact: what an involution of `Option α` looks like -/

/-- `swap none a * optionCongr f` sends `none` to `a`. -/
theorem swapCongr_none {α : Type*} [DecidableEq α] (a : Option α) (f : Equiv.Perm α) :
    (Equiv.swap none a * Equiv.optionCongr f) none = a := by
  simp [Equiv.Perm.mul_apply]

/-- And it sends `some x` to `some (f x)`, unless that is the point `a` swapped with `none`. -/
theorem swapCongr_some {α : Type*} [DecidableEq α] (a : Option α) (f : Equiv.Perm α) (x : α) :
    (Equiv.swap none a * Equiv.optionCongr f) (some x)
      = if a = some (f x) then none else some (f x) := by
  have h : (Equiv.swap none a * Equiv.optionCongr f) (some x)
      = Equiv.swap none a (some (f x)) := by
    simp [Equiv.Perm.mul_apply]
  rw [h, Equiv.swap_apply_def]
  by_cases hax : a = some (f x)
  · simp [hax]
  · simp [hax, Ne.symm hax]

/-- **THE DECOMPOSITION.** `Equiv.Perm.decomposeOption` writes every permutation of `Option α`
uniquely as `swap none a * optionCongr f`. Such a thing is an involution exactly when `f` is one
and, in the case `a = some b`, `f` fixes `b`.

The second condition is the whole content: `σ none = a`, so `σ` must send `a` back to `none`,
and `σ (some b) = swap none (some b) (some (f b))`, which is `none` precisely when `f b = b`. -/
theorem involutive_swap_optionCongr_iff {α : Type*} [DecidableEq α]
    (a : Option α) (f : Equiv.Perm α) :
    (Equiv.swap none a * Equiv.optionCongr f) ∈ involutions (Option α)
      ↔ (f ∈ involutions α ∧ ∀ b, a = some b → f b = b) := by
  constructor
  · intro h
    have hfix : ∀ b, a = some b → f b = b := by
      intro b hb
      have hbn := h none
      rw [swapCongr_none, hb, swapCongr_some] at hbn
      by_cases hfb : (some b : Option α) = some (f b)
      · exact (Option.some_injective _ hfb).symm
      · rw [if_neg hfb] at hbn
        exact absurd hbn (by simp)
    refine ⟨fun x => ?_, hfix⟩
    have hx := h (some x)
    rw [swapCongr_some] at hx
    by_cases hax : a = some (f x)
    · rw [if_pos hax, swapCongr_none] at hx
      have hxx : f x = x := Option.some_injective _ (hax ▸ hx)
      rw [hxx, hxx]
    · rw [if_neg hax, swapCongr_some] at hx
      by_cases hax2 : a = some (f (f x))
      · rw [if_pos hax2] at hx
        exact absurd hx (by simp)
      · rw [if_neg hax2] at hx
        exact Option.some_injective _ hx
  · rintro ⟨hf, ha⟩ y
    cases y with
    | none =>
        rw [swapCongr_none]
        cases a with
        | none => rw [swapCongr_none]
        | some b =>
            have hfb : f b = b := ha b rfl
            rw [swapCongr_some, hfb, if_pos rfl]
    | some x =>
        rw [swapCongr_some]
        by_cases hax : a = some (f x)
        · -- `a = some (f x)` forces `f x = x`: the hypothesis fixes `f x`, and `f` is
          -- involutive, so `x = f (f x) = f x`.
          have hfix : f (f x) = f x := ha (f x) hax
          have hxx : f x = x := ((hf x).symm.trans hfix).symm
          rw [if_pos hax, swapCongr_none, hax, hxx]
        · rw [if_neg hax, swapCongr_some, hf x]
          have hne : a ≠ some x := fun hax2 => hax (by rw [hax2, ha x hax2])
          rw [if_neg hne]

/-! ## 5. A fixed-point-free involution forces an even cardinality

`IsingContourEnergy` recorded, on 2026-08-15, a Mathlib search for exactly this fact:

> A search for a Mathlib lemma of the shape *"fixed-point-free involution on a `Finset` ⟹ even
> card"* found nothing — `exact?` failed and grepping the `Even`/`card` and `Involutive`
> families turned up only unrelated results — **so without the graph the parity would have
> wanted a strong induction, which is a route, just a longer one.**

**The absence claim is true and the consequence drawn from it is not.** There is no lemma of that
shape, and there is one of a different shape three lines away: `Equiv.Perm.card_fixedPoints_modEq`
says `card α ≡ card (fixedPoints f) [MOD p]` whenever `f ^ p ^ n = 1`. At `p = 2`, `n = 1` that is
this statement, and no induction is wanted. A grep over `Even`, `card` and `Involutive` could not
have found it, because it is phrased in `Nat.ModEq` and mentions none of the three. -/

/-- **A FIXED-POINT-FREE INVOLUTION FORCES AN EVEN CARDINALITY**, in three lines off
`Equiv.Perm.card_fixedPoints_modEq` at the prime `2`. -/
theorem even_card_of_mem_perfectMatchings {α : Type*} [Fintype α]
    {σ : Equiv.Perm α} (h : σ ∈ perfectMatchings α) : Even (Fintype.card α) := by
  classical
  -- no fixed points, so the fixed-point set is empty and its cardinality is `0`. Stated as a
  -- cardinality rather than as a set equation: rewriting a `Set` under `Fintype.card` trips the
  -- motive check, because the `Fintype` instance mentions the set.
  have hzero : Fintype.card ↑(Function.fixedPoints (⇑σ)) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun x => ?_⟩
    have hx : σ x.1 = x.1 := x.2
    exact h.2 x.1 hx
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := (⇑σ : Function.End α))
    (p := 2) (n := 1) (by
      have h21 : (2 : ℕ) ^ (1 : ℕ) = 2 := by norm_num
      rw [h21, pow_two]
      funext x
      exact h.1 x)
  rw [hzero] at hmod
  exact (even_iff_two_dvd).mpr ((Nat.modEq_zero_iff_dvd).mp hmod)

/-- The contrapositive, and the reason three entries of the table below are `0`: an odd set has
no perfect matching at all. -/
theorem perfectMatchings_eq_empty_of_odd {α : Type*} [Fintype α]
    (h : ¬ Even (Fintype.card α)) : perfectMatchings α = ∅ := by
  ext σ
  simp only [Set.mem_empty_iff_false, iff_false]
  exact fun hσ => h (even_card_of_mem_perfectMatchings hσ)

/-! ## 6. The counts, and the one that checks the estate's own Wick coefficients -/

/-- `I(0) … I(6) = 1, 1, 2, 4, 10, 26, 76` — the number of partial matchings of a `k`-element
set, hence **the number of terms the `k`-factor Wick expansion must have**.

`I(3) = 4` is exactly the term count of `LatticeWickThree.wick_three`: three ways to pair two of
`a, b, c` and contract the third with an `f`, plus one way to contract all three. `I(1) = 1` and
`I(2) = 2` likewise match `LatticeWickRecursion.wick_recursion` and `LatticeWickTwo.wick_two`. -/
theorem card_involutions_fin_zero : Fintype.card ↑(involutions (Fin 0)) = 1 := by decide

theorem card_involutions_fin_one : Fintype.card ↑(involutions (Fin 1)) = 1 := by decide

theorem card_involutions_fin_two : Fintype.card ↑(involutions (Fin 2)) = 2 := by decide

theorem card_involutions_fin_three : Fintype.card ↑(involutions (Fin 3)) = 4 := by decide

theorem card_involutions_fin_four : Fintype.card ↑(involutions (Fin 4)) = 10 := by decide

set_option maxRecDepth 4000 in
theorem card_involutions_fin_five : Fintype.card ↑(involutions (Fin 5)) = 26 := by decide

set_option maxRecDepth 20000 in
theorem card_involutions_fin_six : Fintype.card ↑(involutions (Fin 6)) = 76 := by decide

/-- The fixed-point-free ones: `1, 0, 1, 0, 3, 0, 15`. Odd sets have none, and the even counts
are the double factorials `(2n−1)‼`. -/
theorem card_perfectMatchings_fin_zero :
    Fintype.card ↑(perfectMatchings (Fin 0)) = 1 := by decide

theorem card_perfectMatchings_fin_one :
    Fintype.card ↑(perfectMatchings (Fin 1)) = 0 := by decide

theorem card_perfectMatchings_fin_two :
    Fintype.card ↑(perfectMatchings (Fin 2)) = 1 := by decide

theorem card_perfectMatchings_fin_three :
    Fintype.card ↑(perfectMatchings (Fin 3)) = 0 := by decide

theorem card_perfectMatchings_fin_four :
    Fintype.card ↑(perfectMatchings (Fin 4)) = 3 := by decide

set_option maxRecDepth 4000 in
theorem card_perfectMatchings_fin_five :
    Fintype.card ↑(perfectMatchings (Fin 5)) = 0 := by decide

set_option maxRecDepth 20000 in
/-- **THE CHECK.** Fifteen pairings of six objects — counted here over a permutation group by
`decide`, and arrived at in `LatticeWickTwo.wick_two_order_six` (`3 + 12`) and
`LatticeWickThree.wick_three_order_six` (`3·3 + 6`) by differentiating under an integral sign.
The three routes share nothing. -/
theorem card_perfectMatchings_fin_six :
    Fintype.card ↑(perfectMatchings (Fin 6)) = 15 := by decide

/-- And `15 = 5‼`, so the check lands on the coefficient `LatticeWickRecursion.wickCoeff`
actually carries. -/
theorem card_perfectMatchings_fin_six_eq_doubleFactorial :
    Fintype.card ↑(perfectMatchings (Fin 6)) = Nat.doubleFactorial 5 := by
  rw [card_perfectMatchings_fin_six]
  decide

/-! ## 7. The recurrence

`I(n+2) = I(n+1) + (n+1)·I(n)`, which §4 makes a bookkeeping exercise: an involution of
`Option α` either fixes `none`, and is an involution of `α`, or swaps `none` with some `b`, and
is an involution of `α` fixing `b`. The count of those does not depend on which `b`, by
conjugating with the transposition that moves one to the other. -/

/-- Splitting a subtype of a product by its first component. -/
def prodSubtypeEquivSigma {ι β : Type*} (Q : ι → β → Prop) :
    {p : ι × β // Q p.1 p.2} ≃ Σ a : ι, {f : β // Q a f} where
  toFun p := ⟨p.1.1, p.1.2, p.2⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv := by rintro ⟨⟨a, f⟩, h⟩; rfl
  right_inv := by rintro ⟨a, f, h⟩; rfl

/-- §4 restated along `Equiv.Perm.decomposeOption`, which is the form the count needs. -/
theorem mem_involutions_option_iff {α : Type*} [DecidableEq α] (σ : Equiv.Perm (Option α)) :
    σ ∈ involutions (Option α)
      ↔ ((Equiv.Perm.decomposeOption σ).2 ∈ involutions α
          ∧ ∀ b, (Equiv.Perm.decomposeOption σ).1 = some b
              → (Equiv.Perm.decomposeOption σ).2 b = b) := by
  have h : Equiv.swap none (Equiv.Perm.decomposeOption σ).1
      * Equiv.optionCongr (Equiv.Perm.decomposeOption σ).2 = σ := by
    rw [← Equiv.Perm.decomposeOption_symm_apply, Equiv.symm_apply_apply]
  conv_lhs => rw [← h]
  exact involutive_swap_optionCongr_iff _ _

/-- Conjugating an involution by an involution gives an involution. -/
theorem conj_mem_involutions {α : Type*} {f c : Equiv.Perm α}
    (hf : f ∈ involutions α) (hc : c ∈ involutions α) : c * f * c ∈ involutions α := by
  intro x
  simp only [Equiv.Perm.mul_apply]
  rw [hc, hf, hc]

/-- And conjugating by `swap b b'` moves the fixed point from `b` to `b'`. -/
theorem conj_swap_fix {α : Type*} [DecidableEq α] {f : Equiv.Perm α} {b b' : α}
    (hb : f b = b) : (Equiv.swap b b' * f * Equiv.swap b b') b' = b' := by
  simp only [Equiv.Perm.mul_apply]
  rw [Equiv.swap_apply_right, hb, Equiv.swap_apply_left]

/-- **THE COUNT OF INVOLUTIONS FIXING A POINT DOES NOT DEPEND ON THE POINT.** -/
def fixingCongr {α : Type*} [DecidableEq α] (b b' : α) :
    {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b}
      ≃ {f : Equiv.Perm α // f ∈ involutions α ∧ f b' = b'} where
  toFun f := ⟨Equiv.swap b b' * f.1 * Equiv.swap b b',
    ⟨conj_mem_involutions f.2.1 (swap_mem_involutions b b'), conj_swap_fix f.2.2⟩⟩
  invFun g := ⟨Equiv.swap b' b * g.1 * Equiv.swap b' b,
    ⟨conj_mem_involutions g.2.1 (swap_mem_involutions b' b), conj_swap_fix g.2.2⟩⟩
  left_inv f := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.swap_comm b' b]
    rw [Equiv.swap_apply_self, Equiv.swap_apply_self]
  right_inv g := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.swap_comm b' b]
    rw [Equiv.swap_apply_self, Equiv.swap_apply_self]

theorem card_fixing_congr {α : Type*} [Fintype α] [DecidableEq α] (b b' : α) :
    Fintype.card {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b}
      = Fintype.card {f : Equiv.Perm α // f ∈ involutions α ∧ f b' = b'} :=
  Fintype.card_congr (fixingCongr b b')

/-- An involution of `Option β` fixing `none` **is** an involution of `β`. -/
def fixingNoneEquiv {β : Type*} [DecidableEq β] :
    {f : Equiv.Perm (Option β) // f ∈ involutions (Option β) ∧ f none = none}
      ≃ ↑(involutions β) where
  toFun f := ⟨Equiv.removeNone f.1, by
    have h := ((mem_involutions_option_iff f.1).mp f.2.1).1
    rwa [Equiv.Perm.decomposeOption_apply] at h⟩
  invFun g := ⟨Equiv.optionCongr g.1, by
    refine ⟨?_, by simp⟩
    intro x
    cases x with
    | none => simp
    | some y => simp [Equiv.optionCongr_apply, g.2 y]⟩
  left_inv f := by
    refine Subtype.ext ?_
    have hd : Equiv.Perm.decomposeOption f.1 = (none, Equiv.removeNone f.1) := by
      rw [Equiv.Perm.decomposeOption_apply, f.2.2]
    have h := Equiv.Perm.decomposeOption.symm_apply_apply f.1
    rw [hd, Equiv.Perm.decomposeOption_symm_apply] at h
    simpa using h
  right_inv g := Subtype.ext (Equiv.removeNone_optionCongr g.1)

theorem card_fixing_none {β : Type*} [Fintype β] [DecidableEq β] :
    Fintype.card {f : Equiv.Perm (Option β) //
        f ∈ involutions (Option β) ∧ f none = none}
      = Fintype.card ↑(involutions β) :=
  Fintype.card_congr fixingNoneEquiv

/-- The count over `Option α`, split by where `none` goes. -/
theorem card_involutions_option {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card ↑(involutions (Option α))
      = Fintype.card ↑(involutions α)
        + ∑ b : α, Fintype.card {f : Equiv.Perm α // f ∈ involutions α ∧ f b = b} := by
  have e1 : ↑(involutions (Option α)) ≃
      {p : Option α × Equiv.Perm α //
        p.2 ∈ involutions α ∧ ∀ b, p.1 = some b → p.2 b = b} :=
    Equiv.subtypeEquiv Equiv.Perm.decomposeOption (fun σ => mem_involutions_option_iff σ)
  rw [Fintype.card_congr (e1.trans (prodSubtypeEquivSigma
        (fun (a : Option α) (f : Equiv.Perm α) =>
          f ∈ involutions α ∧ ∀ b, a = some b → f b = b))),
    Fintype.card_sigma, Fintype.sum_option]
  congr 1
  · exact Fintype.card_congr (Equiv.subtypeEquivRight (fun f => by simp))
  · exact Finset.sum_congr rfl fun b _ =>
      Fintype.card_congr (Equiv.subtypeEquivRight (fun f => by simp))

/-- **THE RECURRENCE.** -/
theorem card_involutions_option_option {β : Type*} [Fintype β] [DecidableEq β] :
    Fintype.card ↑(involutions (Option (Option β)))
      = Fintype.card ↑(involutions (Option β))
        + (Fintype.card β + 1) * Fintype.card ↑(involutions β) := by
  rw [card_involutions_option (α := Option β)]
  congr 1
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) =>
        card_fixing_congr (α := Option β) b none),
    Finset.sum_const, Finset.card_univ, Fintype.card_option, smul_eq_mul, card_fixing_none]

/-- And at `Fin`, which is the shape the table is in: `I(n+2) = I(n+1) + (n+1)·I(n)`. -/
theorem card_involutions_fin_add_two (n : ℕ) :
    Fintype.card ↑(involutions (Fin (n + 2)))
      = Fintype.card ↑(involutions (Fin (n + 1)))
        + (n + 1) * Fintype.card ↑(involutions (Fin n)) := by
  have e : Fin (n + 2) ≃ Option (Option (Fin n)) :=
    (finSuccEquiv (n + 1)).trans (Equiv.optionCongr (finSuccEquiv n))
  rw [card_involutions_invariant e,
    card_involutions_option_option,
    card_involutions_invariant (finSuccEquiv n) (β := Option (Fin n)) |>.symm,
    Fintype.card_fin]

/-! ## 8. The involution numbers as a `ℕ` recursion, and the two routes checked against each other

Mathlib gives `derangements` a companion `numDerangements : ℕ → ℕ` and a theorem tying the two
together, so that a count can be evaluated without touching a permutation group. The same shape
is what makes the table extend: rewriting under `Fintype.card` at a numeral index forces `whnf`
on the permutation-group instance, and at `Fin 8` that does not finish inside the default budget.
Through `numInvolutions` there is no group to evaluate at all. -/

/-- The involution numbers, as a plain `ℕ` recursion — the shape `numDerangements` has. -/
def numInvolutions : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => numInvolutions (n + 1) + (n + 1) * numInvolutions n

/-- **AND IT COUNTS THEM.** The base cases are two of §6's `decide` results and the step is the
recurrence, so this is the whole table in one statement. -/
theorem card_involutions_fin_eq_numInvolutions (n : ℕ) :
    Fintype.card ↑(involutions (Fin n)) = numInvolutions n := by
  induction n using Nat.twoStepInduction with
  | zero => exact card_involutions_fin_zero
  | one => exact card_involutions_fin_one
  | more n ih0 ih1 =>
      rw [card_involutions_fin_add_two n, ih0, ih1]
      rfl

/-- **THE CHECK ON THE RECURRENCE ITSELF.** `76` was obtained in §6 by enumerating the `720`
permutations of a six-element set and testing each; `numInvolutions 6` computes it from the two
entries below it by a recursion that never mentions a permutation. The theorem above says the two
must agree, so the `decide` values of §6 are a consistency check on the whole chain of §7 — the
`Option`-decomposition, the conjugation, and the sum split. -/
theorem numInvolutions_six : numInvolutions 6 = 76 := by decide

theorem card_involutions_fin_six_two_ways :
    Fintype.card ↑(involutions (Fin 6)) = numInvolutions 6 :=
  card_involutions_fin_eq_numInvolutions 6

/-- `I(7) = 232` and `I(8) = 764`, **neither reachable by `decide` over the group** — that would
enumerate `5040` and `40320` permutations — and both immediate here. -/
theorem card_involutions_fin_seven :
    Fintype.card ↑(involutions (Fin 7)) = 232 := by
  rw [card_involutions_fin_eq_numInvolutions]
  decide

theorem card_involutions_fin_eight :
    Fintype.card ↑(involutions (Fin 8)) = 764 := by
  rw [card_involutions_fin_eq_numInvolutions]
  decide

/-- And at a size where enumeration is hopeless: `I(12) = 140152`. -/
theorem card_involutions_fin_twelve :
    Fintype.card ↑(involutions (Fin 12)) = 140152 := by
  rw [card_involutions_fin_eq_numInvolutions]
  decide

/-! ## 9. The perfect matchings, and the double factorial

The same decomposition again, with one extra condition. A fixed-point-free involution of
`Option α` cannot fix `none`, so it sends `none` to some `b`; the corresponding `f` then fixes
`b` — that is what makes the whole thing an involution — and **fixes nothing else**, because a
second fixed point of `f` would be a fixed point of the whole. So the fibre over `b` is the
involutions of `α` whose fixed-point set is exactly `{b}`, and at `α = Option β` with `b = none`
those are the perfect matchings of `β`. Hence `P(n+2) = (n+1)·P(n)`, the double factorial. -/

/-- Involutions of `α` whose only fixed point is `b`. -/
def onlyFixing {α : Type*} (b : α) : Set (Equiv.Perm α) :=
  {f | f ∈ involutions α ∧ ∀ x, f x = x ↔ x = b}

/-- The condition on `Equiv.Perm.decomposeOption σ` that makes `σ` a perfect matching. -/
def pmPred {α : Type*} (a : Option α) (f : Equiv.Perm α) : Prop :=
  ∃ b : α, a = some b ∧ f ∈ onlyFixing b

/-- **THE STRUCTURAL FACT FOR PERFECT MATCHINGS**, in the shape of
`involutive_swap_optionCongr_iff` and proved off it. -/
theorem perfectMatching_swap_optionCongr_iff {α : Type*} [DecidableEq α]
    (a : Option α) (f : Equiv.Perm α) :
    (Equiv.swap none a * Equiv.optionCongr f) ∈ perfectMatchings (Option α) ↔ pmPred a f := by
  constructor
  · rintro ⟨hinv, hfree⟩
    obtain ⟨hf, hfix⟩ := (involutive_swap_optionCongr_iff a f).mp hinv
    -- `none` is not fixed, so `a = some b`
    have hnone := hfree none
    rw [swapCongr_none] at hnone
    obtain ⟨b, rfl⟩ : ∃ b, a = some b := by
      cases a with
      | none => exact absurd rfl hnone
      | some b => exact ⟨b, rfl⟩
    refine ⟨b, rfl, hf, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · by_contra hxb
      have hne : (some b : Option α) ≠ some (f x) := by rw [hx]; simpa using fun h => hxb h.symm
      have := hfree (some x)
      rw [swapCongr_some, if_neg hne, hx] at this
      exact this rfl
    · subst hx; exact hfix x rfl
  · rintro ⟨b, rfl, hf, hfix⟩
    refine ⟨(involutive_swap_optionCongr_iff _ _).mpr ⟨hf, fun b' hb' => ?_⟩, fun y => ?_⟩
    · have hbb : b = b' := Option.some_injective _ hb'
      subst hbb
      exact (hfix b).mpr rfl
    · cases y with
      | none => rw [swapCongr_none]; simp
      | some x =>
          rw [swapCongr_some]
          by_cases hax : (some b : Option α) = some (f x)
          · rw [if_pos hax]; simp
          · rw [if_neg hax]
            simp only [ne_eq, Option.some.injEq]
            intro hx
            exact hax (by rw [hx, (hfix x).mp hx])

/-- `perfectMatchings (Option α)`, transported along `Equiv.Perm.decomposeOption`. -/
theorem mem_perfectMatchings_option_iff {α : Type*} [DecidableEq α]
    (σ : Equiv.Perm (Option α)) :
    σ ∈ perfectMatchings (Option α)
      ↔ pmPred (Equiv.Perm.decomposeOption σ).1 (Equiv.Perm.decomposeOption σ).2 := by
  have h : Equiv.swap none (Equiv.Perm.decomposeOption σ).1
      * Equiv.optionCongr (Equiv.Perm.decomposeOption σ).2 = σ := by
    rw [← Equiv.Perm.decomposeOption_symm_apply, Equiv.symm_apply_apply]
  conv_lhs => rw [← h]
  exact perfectMatching_swap_optionCongr_iff _ _

instance decidablePredOnlyFixing {α : Type*} [DecidableEq α] [Fintype α] (b : α) :
    DecidablePred (· ∈ onlyFixing b) := fun f => by
  unfold onlyFixing involutions Function.Involutive
  infer_instance

/-- Conjugating by `swap b b'` moves an *only* fixed point from `b` to `b'`. -/
theorem conj_swap_onlyFixing {α : Type*} [DecidableEq α] {f : Equiv.Perm α} {b b' : α}
    (h : ∀ x, f x = x ↔ x = b) :
    ∀ x, (Equiv.swap b b' * f * Equiv.swap b b') x = x ↔ x = b' := by
  intro x
  simp only [Equiv.Perm.mul_apply]
  constructor
  · intro hx
    have h1 : f (Equiv.swap b b' x) = Equiv.swap b b' x := by
      have h0 := congrArg (Equiv.swap b b') hx
      rwa [Equiv.swap_apply_self] at h0
    have h2 : Equiv.swap b b' x = b := (h _).mp h1
    have h3 := congrArg (Equiv.swap b b') h2
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at h3
    exact h3
  · rintro rfl
    rw [Equiv.swap_apply_right, (h b).mpr rfl, Equiv.swap_apply_left]

/-- **THE FIBRE DOES NOT DEPEND ON WHICH POINT**, by the same conjugation as `fixingCongr`. -/
def onlyFixingCongr {α : Type*} [DecidableEq α] (b b' : α) :
    ↑(onlyFixing b) ≃ ↑(onlyFixing b') where
  toFun f := ⟨Equiv.swap b b' * f.1 * Equiv.swap b b',
    ⟨conj_mem_involutions f.2.1 (swap_mem_involutions b b'), conj_swap_onlyFixing f.2.2⟩⟩
  invFun g := ⟨Equiv.swap b' b * g.1 * Equiv.swap b' b,
    ⟨conj_mem_involutions g.2.1 (swap_mem_involutions b' b), conj_swap_onlyFixing g.2.2⟩⟩
  left_inv f := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.swap_comm b' b]
    rw [Equiv.swap_apply_self, Equiv.swap_apply_self]
  right_inv g := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.swap_comm b' b]
    rw [Equiv.swap_apply_self, Equiv.swap_apply_self]

theorem card_onlyFixing_congr {α : Type*} [Fintype α] [DecidableEq α] (b b' : α) :
    Fintype.card ↑(onlyFixing b) = Fintype.card ↑(onlyFixing b') :=
  Fintype.card_congr (onlyFixingCongr b b')

/-- **AND AT `none` IT IS THE PERFECT MATCHINGS ONE SIZE DOWN.** -/
def onlyFixingNoneEquiv {β : Type*} [DecidableEq β] :
    ↑(onlyFixing (none : Option β)) ≃ ↑(perfectMatchings β) where
  toFun f := ⟨Equiv.removeNone f.1, by
    have hnone : f.1 none = none := (f.2.2 none).mpr rfl
    have hd : Equiv.Perm.decomposeOption f.1 = (none, Equiv.removeNone f.1) := by
      rw [Equiv.Perm.decomposeOption_apply, hnone]
    have hinv : Equiv.removeNone f.1 ∈ involutions β := by
      have h := ((mem_involutions_option_iff f.1).mp f.2.1).1
      rwa [Equiv.Perm.decomposeOption_apply] at h
    refine ⟨hinv, fun y hy => ?_⟩
    have hcongr : Equiv.optionCongr (Equiv.removeNone f.1) = f.1 := by
      have h := Equiv.Perm.decomposeOption.symm_apply_apply f.1
      rw [hd, Equiv.Perm.decomposeOption_symm_apply] at h
      simpa using h
    have hfy : f.1 (some y) = some y := by
      have h0 : Equiv.optionCongr (Equiv.removeNone f.1) (some y) = some y := by
        rw [Equiv.optionCongr_apply, Option.map_some, hy]
      rwa [hcongr] at h0
    exact absurd ((f.2.2 (some y)).mp hfy) (by simp)⟩
  invFun g := ⟨Equiv.optionCongr g.1, by
    refine ⟨?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · intro x
      cases x with
      | none => simp
      | some y => simp [Equiv.optionCongr_apply, g.2.1 y]
    · cases x with
      | none => rfl
      | some y =>
          simp only [Equiv.optionCongr_apply, Option.map_some, Option.some.injEq] at hx
          exact absurd hx (g.2.2 y)
    · subst hx; simp⟩
  left_inv f := by
    refine Subtype.ext ?_
    have hnone : f.1 none = none := (f.2.2 none).mpr rfl
    have hd : Equiv.Perm.decomposeOption f.1 = (none, Equiv.removeNone f.1) := by
      rw [Equiv.Perm.decomposeOption_apply, hnone]
    have h := Equiv.Perm.decomposeOption.symm_apply_apply f.1
    rw [hd, Equiv.Perm.decomposeOption_symm_apply] at h
    simpa using h
  right_inv g := Subtype.ext (Equiv.removeNone_optionCongr g.1)

theorem card_onlyFixing_none {β : Type*} [Fintype β] [DecidableEq β] :
    Fintype.card ↑(onlyFixing (none : Option β)) = Fintype.card ↑(perfectMatchings β) :=
  Fintype.card_congr onlyFixingNoneEquiv

/-- Transport of `perfectMatchings` along an equivalence, as `involutionsCongr` is for
`involutions`. -/
def perfectMatchingsCongr {α β : Type*} (e : α ≃ β) :
    ↑(perfectMatchings α) ≃ ↑(perfectMatchings β) where
  toFun σ := ⟨e.permCongr σ.1, by
    refine ⟨fun x => by simp [Equiv.permCongr_apply, σ.2.1 (e.symm x)], fun x hx => ?_⟩
    rw [Equiv.permCongr_apply] at hx
    exact σ.2.2 (e.symm x) (by simpa using congrArg e.symm hx)⟩
  invFun τ := ⟨e.symm.permCongr τ.1, by
    refine ⟨fun x => by simp [Equiv.permCongr_apply, τ.2.1 (e x)], fun x hx => ?_⟩
    rw [Equiv.permCongr_apply] at hx
    exact τ.2.2 (e x) (by simpa using congrArg e hx)⟩
  left_inv σ := by ext x; simp
  right_inv τ := by ext x; simp

theorem card_perfectMatchings_invariant {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) :
    Fintype.card ↑(perfectMatchings α) = Fintype.card ↑(perfectMatchings β) :=
  Fintype.card_congr (perfectMatchingsCongr e)

/-- The count over `Option α`: no `none` term at all, because a perfect matching cannot fix it. -/
theorem card_perfectMatchings_option {α : Type*} [Fintype α] [DecidableEq α] :
    Fintype.card ↑(perfectMatchings (Option α))
      = ∑ b : α, Fintype.card ↑(onlyFixing b) := by
  classical
  have e1 : ↑(perfectMatchings (Option α)) ≃
      {p : Option α × Equiv.Perm α // pmPred p.1 p.2} :=
    Equiv.subtypeEquiv Equiv.Perm.decomposeOption (fun σ => mem_perfectMatchings_option_iff σ)
  rw [Fintype.card_congr (e1.trans (prodSubtypeEquivSigma
        (fun (a : Option α) (f : Equiv.Perm α) => pmPred a f))),
    Fintype.card_sigma, Fintype.sum_option]
  have hnone : Fintype.card {f : Equiv.Perm α // pmPred none f} = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun f => by obtain ⟨b, hb, -⟩ := f.2; exact absurd hb (by simp)⟩
  rw [hnone, zero_add]
  exact Finset.sum_congr rfl fun b _ =>
    Fintype.card_congr (Equiv.subtypeEquivRight (fun f => by
      constructor
      · rintro ⟨b', hb', hf⟩
        cases hb'
        exact hf
      · intro hf
        exact ⟨b, rfl, hf⟩))

/-- **THE DOUBLE-FACTORIAL RECURRENCE.** -/
theorem card_perfectMatchings_option_option {β : Type*} [Fintype β] [DecidableEq β] :
    Fintype.card ↑(perfectMatchings (Option (Option β)))
      = (Fintype.card β + 1) * Fintype.card ↑(perfectMatchings β) := by
  rw [card_perfectMatchings_option (α := Option β),
    Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) =>
      card_onlyFixing_congr (α := Option β) b none),
    Finset.sum_const, Finset.card_univ, Fintype.card_option, smul_eq_mul,
    card_onlyFixing_none]

/-- And at `Fin`: `P(n+2) = (n+1)·P(n)`. -/
theorem card_perfectMatchings_fin_add_two (n : ℕ) :
    Fintype.card ↑(perfectMatchings (Fin (n + 2)))
      = (n + 1) * Fintype.card ↑(perfectMatchings (Fin n)) := by
  have e : Fin (n + 2) ≃ Option (Option (Fin n)) :=
    (finSuccEquiv (n + 1)).trans (Equiv.optionCongr (finSuccEquiv n))
  rw [card_perfectMatchings_invariant e, card_perfectMatchings_option_option, Fintype.card_fin]

/-! ## 10. `P(2k) = (2k−1)‼`, which is the coefficient general-order Isserlis carries -/

/-- The double-factorial recursion in the index shape this induction produces.

**DECLARED DUPLICATE** (`ERRATUM 176`): this is `LatticeWickRecursion.doubleFactorial_step`,
statement for statement. It is restated rather than imported **because the dependency would run
the wrong way** — this file is pure combinatorics and is meant to be importable BY the Gaussian
chain, not the other way round. Six lines is the price of that. -/
theorem doubleFactorial_step_local (j : ℕ) :
    Nat.doubleFactorial (2 * j + 1) = (2 * j + 1) * Nat.doubleFactorial (2 * j - 1) := by
  match j with
  | 0 => decide
  | (i + 1) =>
      have h1 : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
      have h3 : 2 * (i + 1) - 1 = 2 * i + 1 := by omega
      rw [h1, h3, Nat.doubleFactorial_add_two]

/-- **THE PAIRINGS OF `2k` OBJECTS NUMBER `(2k−1)‼`** — the coefficient the estate's Wick
expansions carry, proved rather than checked at one value.

`card_perfectMatchings_fin_six_eq_doubleFactorial` is now the case `k = 3` of this, and it is
kept because its `15` comes from `decide` over `720` permutations: the two agree, and that
agreement tests the decomposition of §9 the way §8's does the one of §7. -/
theorem card_perfectMatchings_fin_eq_doubleFactorial (k : ℕ) :
    Fintype.card ↑(perfectMatchings (Fin (2 * k))) = Nat.doubleFactorial (2 * k - 1) := by
  induction k with
  | zero => simpa using card_perfectMatchings_fin_zero
  | succ k ih =>
      have hidx : 2 * (k + 1) = 2 * k + 2 := by ring
      rw [hidx, card_perfectMatchings_fin_add_two (2 * k), ih]
      have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      rw [hsub, doubleFactorial_step_local k]

/-- And an odd number of objects has no pairing at all. -/
theorem card_perfectMatchings_fin_odd (k : ℕ) :
    Fintype.card ↑(perfectMatchings (Fin (2 * k + 1))) = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun σ => ?_⟩
  have h := even_card_of_mem_perfectMatchings σ.2
  rw [Fintype.card_fin, Nat.even_iff] at h
  omega

/-- The general statement checked against §6's `decide`: `P(6) = 5‼ = 15`. -/
theorem card_perfectMatchings_fin_six_two_ways :
    Fintype.card ↑(perfectMatchings (Fin 6)) = Nat.doubleFactorial 5 := by
  have h := card_perfectMatchings_fin_eq_doubleFactorial 3
  norm_num at h
  exact h

/-! ## 11. Half the elements of a perfect matching lie below their partner

The fact a consumer needs to evaluate a pairing's contribution on the diagonal: a pairing indexed
by *one representative per pair* has exactly half as many representatives as there are elements. -/

/-- **A FIXED-POINT-FREE INVOLUTION MOVES EXACTLY HALF ITS POINTS UPWARD.** `σ` carries
`{i | i < σ i}` bijectively onto `{i | σ i < i}`, the two are disjoint because `σ` has no fixed
point, and together they are everything. -/
theorem two_mul_card_lt_image {α : Type*} [Fintype α] [LinearOrder α]
    {σ : Equiv.Perm α} (h : σ ∈ perfectMatchings α) :
    2 * (Finset.univ.filter (fun i => i < σ i)).card = Fintype.card α := by
  classical
  set A := Finset.univ.filter (fun i : α => i < σ i) with hA
  set B := Finset.univ.filter (fun i : α => σ i < i) with hB
  have hcard : A.card = B.card := by
    refine Finset.card_nbij' (fun i => σ i) (fun i => σ i) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [hA, hB, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
      rw [h.1 i]
      exact hi
    · intro i hi
      simp only [hA, hB, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
      rw [h.1 i]
      exact hi
    · intro i _
      exact h.1 i
    · intro i _
      exact h.1 i
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hA, Finset.mem_filter] at hi
    simp only [hB, Finset.mem_filter] at hi'
    exact absurd hi.2 (asymm hi'.2)
  have hunion : A ∪ B = Finset.univ := by
    ext i
    simp only [hA, hB, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    rcases lt_trichotomy i (σ i) with hlt | heq | hgt
    · exact Or.inl hlt
    · exact absurd heq.symm (h.2 i)
    · exact Or.inr hgt
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, hcard] at this
  omega

end Involutions
