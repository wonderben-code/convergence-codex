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
  `card_perfectMatchings_fin_six_eq_doubleFactorial` for the check named above.

## What is NOT proved here, and it is the next rung

**The recurrence `I(n+2) = I(n+1) + (n+1)·I(n)` is not proved.** Its two ingredients are, and
they are exactly `involutive_swap_optionCongr_iff` plus the observation that the count of
involutions fixing a given point does not depend on which point (conjugate by a transposition).
What is missing is the bookkeeping between them: the subtype equivalence
`involutions (Option α) ≃ {(a, f) // f ∈ involutions α ∧ ∀ b, a = some b → f b = b}` induced by
`Equiv.Perm.decomposeOption`, and the sum over the first component. **No estimate of that cost
is offered** (`ERRATUM 194`); what can be said is that the mathematics of the step is done and
the residue is `Equiv`/`Fintype.card` plumbing. Until it is proved the table above stops at six,
by `decide`, and every entry of it is checked rather than asserted.

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

end Involutions
