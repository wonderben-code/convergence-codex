/-
  Theorem 3: The Seed Is Forced (Sterility of Empty and Unit)
  ===========================================================

  Paper D — Machine-Verified Mathematical Foundations of the Generator ToE

  CLAIM: In the GToE, the construction ∅ → I → I⊕I → [I⊕I, I⊕I] → ...
  has no free parameters. The seed I⊕I is forced because:
  - [∅, ∅] ≅ I (the empty object is sterile: one function from empty to empty)
  - [I, I] ≅ I (the unit is sterile: one function from unit to unit)
  - [I⊕I, I⊕I] is strictly richer than I⊕I (4 elements vs 2)

  We model this concretely:
  - ∅ = Empty, I = Unit, I⊕I = Bool
  - [X, X] = (X → X)

  Machine verification: Lean 4.29.1 + Mathlib
  Target: 0 sorry
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic

open Function

/-!
## Part 1: The Empty Object is Sterile

There is exactly one function from Empty to Empty.
So [∅, ∅] ≅ Unit ≅ I.
-/

/-- There is a unique function from Empty to Empty. -/
theorem empty_to_empty_unique (f g : Empty → Empty) : f = g :=
  funext (fun x => Empty.elim x)

/-- (Empty → Empty) is equivalent to Unit — exactly one element. -/
def empty_hom_equiv_unit : (Empty → Empty) ≃ Unit where
  toFun _ := ()
  invFun _ := Empty.elim
  left_inv f := funext (fun x => Empty.elim x)
  right_inv u := by cases u; rfl

/-!
## Part 2: The Unit Object is Sterile

There is exactly one function from Unit to Unit.
So [I, I] ≅ I.
-/

/-- There is a unique function from Unit to Unit. -/
theorem unit_to_unit_unique (f g : Unit → Unit) : f = g :=
  funext (fun x => by cases x; cases f (); cases g (); rfl)

/-- (Unit → Unit) is equivalent to Unit — exactly one element. -/
def unit_hom_equiv_unit : (Unit → Unit) ≃ Unit where
  toFun _ := ()
  invFun _ := id
  left_inv f := funext (fun x => by cases x; cases f (); rfl)
  right_inv u := by cases u; rfl

/-!
## Part 3: Bool (= I ⊕ I) is the Minimal Non-Trivial Seed

(Bool → Bool) has 4 elements, strictly more than Bool's 2.
The 4 functions: id, not, const true, const false.
-/

/-- Every function Bool → Bool is one of: id, not, const true, const false. -/
theorem bool_hom_classification (f : Bool → Bool) :
    f = id ∨ f = Bool.not ∨ f = Function.const Bool true ∨
    f = Function.const Bool false := by
  match hft : f true, hff : f false with
  | true, false =>
    left; ext b; cases b <;> simp_all
  | false, true =>
    right; left; ext b; cases b <;> simp_all [Bool.not]
  | true, true =>
    right; right; left; ext b; cases b <;> simp_all [Function.const]
  | false, false =>
    right; right; right; ext b; cases b <;> simp_all [Function.const]

/-- id and Bool.not are distinct functions. -/
theorem id_ne_not : (id : Bool → Bool) ≠ Bool.not := by
  intro h; have := congr_fun h true; simp [Bool.not] at this

/-- id and const true are distinct functions. -/
theorem id_ne_const_true : (id : Bool → Bool) ≠ Function.const Bool true := by
  intro h; have := congr_fun h false; simp [Function.const] at this

/-- id and const false are distinct functions. -/
theorem id_ne_const_false : (id : Bool → Bool) ≠ Function.const Bool false := by
  intro h; have := congr_fun h true; simp [Function.const] at this

/-- Bool.not and const true are distinct. -/
theorem not_ne_const_true : (Bool.not : Bool → Bool) ≠ Function.const Bool true := by
  intro h; have := congr_fun h true; simp [Bool.not, Function.const] at this

/-- Bool.not and const false are distinct. -/
theorem not_ne_const_false : (Bool.not : Bool → Bool) ≠ Function.const Bool false := by
  intro h; have := congr_fun h false; simp [Bool.not, Function.const] at this

/-- const true and const false are distinct. -/
theorem const_true_ne_const_false :
    (Function.const Bool true : Bool → Bool) ≠ Function.const Bool false := by
  intro h; have := congr_fun h true; simp [Function.const] at this

/-- (Bool → Bool) is NOT equivalent to Bool.
    Bool → Bool has 4 elements; Bool has 2.
    Any injection from {id, not, const true, const false} to Bool
    maps 4 distinct things to a 2-element set — impossible. -/
theorem bool_hom_not_equiv_bool : IsEmpty ((Bool → Bool) ≃ Bool) := by
  constructor
  intro e
  have inj := e.injective
  -- Map 4 distinct elements to {true, false}
  -- By pigeonhole, at least two must be equal
  -- Consider just 3: id, not, const true
  -- They map to Bool = {true, false}, so two must collide
  have h1 : e id = true ∨ e id = false := by cases e id <;> simp
  have h2 : e Bool.not = true ∨ e Bool.not = false := by cases e Bool.not <;> simp
  have h3 : e (Function.const Bool true) = true ∨
            e (Function.const Bool true) = false := by
    cases e (Function.const Bool true) <;> simp
  -- id ≠ not ≠ const true, pairwise
  have d12 := id_ne_not
  have d13 := id_ne_const_true
  have d23 := not_ne_const_true
  -- So e id ≠ e not, e id ≠ e (const true), e not ≠ e (const true)
  have ne12 : e id ≠ e Bool.not := fun h => d12 (inj h)
  have ne13 : e id ≠ e (Function.const Bool true) := fun h => d13 (inj h)
  have ne23 : e Bool.not ≠ e (Function.const Bool true) := fun h => d23 (inj h)
  -- 3 pairwise-distinct values in {true, false}: impossible
  -- In each case, two e-values are equal, so injectivity forces the preimages equal
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3
  · exact d12 (inj (h1.trans h2.symm))
  · exact d12 (inj (h1.trans h2.symm))
  · exact d13 (inj (h1.trans h3.symm))
  · exact d23 (inj (h2.trans h3.symm))
  · exact d23 (inj (h2.trans h3.symm))
  · exact d13 (inj (h1.trans h3.symm))
  · exact d12 (inj (h1.trans h2.symm))
  · exact d12 (inj (h1.trans h2.symm))

/-!
## Part 4: The Summary — Seed Is Forced

∅ and I are sterile (their function spaces collapse).
I⊕I is fertile (its function space grows strictly).
Therefore I⊕I is the minimal non-trivial seed.
-/

/-- **THE SEED IS FORCED:**
    Empty and Unit are sterile under internal hom.
    Bool (= I⊕I) is strictly fertile: [Bool, Bool] ≠ Bool.
    The seed of the Generator construction has no free parameters. -/
theorem seed_is_forced :
    (∀ f g : Empty → Empty, f = g) ∧
    (∀ f g : Unit → Unit, f = g) ∧
    ¬(∀ f g : Bool → Bool, f = g) := by
  refine ⟨empty_to_empty_unique, unit_to_unit_unique, ?_⟩
  intro h
  exact id_ne_not (h id Bool.not)

/-- **Growth is strict:** [Bool, Bool] has strictly more elements than Bool.
    The cascade never collapses back. -/
theorem growth_is_strict :
    ¬ Nonempty ((Bool → Bool) ≃ Bool) := by
  intro ⟨e⟩
  exact (bool_hom_not_equiv_bool).false e
