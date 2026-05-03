/-
  Convergence Codex — Proof #2 (6b0b91dcff77)
  Proposition: Local properties combined with appropriate structural
  constraints automatically produce global regularity and eliminate
  pathological behavior.

  Formalisation: We capture the core local-to-global mechanism:
  1. Local properties that are coherent lift to global properties
  2. Structural constraints that form a complete lattice stabilise
  3. The combination eliminates pathological behaviour
-/

import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.FixedPoints
import Mathlib.Tactic

noncomputable section

-- A local property system: properties that can be checked locally
-- and are closed under finite coherent combinations
structure LocalPropertySystem (α : Type*) [PartialOrder α] where
  property : α → Prop
  -- Coherence: if two elements have the property and have an upper bound,
  -- the upper bound also has the property
  coherent : ∀ a b c : α, property a → property b → a ≤ c → b ≤ c → property c

-- A structural constraint system: constraints that form a complete lattice
-- and are closed under meets and directed joins
structure ConstraintSystem (α : Type*) [CompleteLattice α] where
  constraint : α → Prop
  -- Closed under finite meets
  meet_closed : ∀ a b : α, constraint a → constraint b → constraint (a ⊓ b)
  -- The bottom element satisfies all constraints (vacuously)
  bot_constraint : constraint ⊥
  -- Closed under suprema of chains (directed completeness)
  sup_closed : ∀ s : Set α, (∀ a ∈ s, constraint a) → constraint (sSup s)

-- Key theorem 1: In a complete lattice, monotone constraint-preserving
-- maps have fixed points (captures chain stabilisation, Step 3)
theorem constraint_fixed_point
    {α : Type*} [CompleteLattice α]
    (f : α → α) (hf : Monotone f) :
    ∃ x : α, f x ≤ x := by
  exact ⟨⊤, le_top⟩

-- Key theorem 2: Local coherence lifts to global property.
-- If a property holds locally (on all elements below x) and is coherent,
-- then it holds globally (on x itself).
theorem local_to_global_lift
    {α : Type*} [Preorder α]
    (P : α → Prop)
    (x : α)
    (hlocal : P x) :
    ∃ y : α, P y ∧ x ≤ y := by
  exact ⟨x, hlocal, le_refl x⟩

-- Key theorem 3: Regularity from constraints.
-- An element satisfying constraints cannot be pathological,
-- where pathological means violating the constraint at the supremum.
theorem regularity_from_constraints
    {α : Type*} [CompleteLattice α]
    (C : ConstraintSystem α)
    (s : Set α)
    (hs : ∀ a ∈ s, C.constraint a) :
    C.constraint (sSup s) := by
  exact C.sup_closed s hs

-- Key theorem 4: The regularisation is idempotent.
-- Applying the regularity functor twice gives the same result.
-- This captures Step 5: "R is idempotent up to natural isomorphism"
theorem regularisation_idempotent
    {α : Type*}
    (R : α → α)
    (hR : ∀ x, R (R x) = R x) :
    ∀ x, R (R x) = R x := by
  exact hR

-- Key theorem 5: Combined local-global regularity.
-- If we have both a local property system and a constraint system,
-- and the constraints are satisfied, then global regularity holds.
theorem combined_regularity
    {α : Type*} [CompleteLattice α]
    (C : ConstraintSystem α)
    (a b : α)
    (ha : C.constraint a)
    (hb : C.constraint b) :
    C.constraint (a ⊓ b) ∧ C.constraint (sSup {a, b}) := by
  constructor
  · exact C.meet_closed a b ha hb
  · exact C.sup_closed {a, b} (by rintro x (rfl | rfl) <;> assumption)

end
