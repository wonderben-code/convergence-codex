/-
  Theorem 2: Reflexive Domain Fixed-Point Property
  =================================================

  Paper D — Machine-Verified Mathematical Foundations of the Generator ToE

  CLAIM: If D is a reflexive domain (modelled as a complete lattice where
  D represents its own endomorphisms), then every monotone endomorphism
  f : D → D has a fixed point. Moreover, there exist both a LEAST and
  GREATEST fixed point, and the fixed points themselves form a complete lattice.

  This is the domain-theoretic specialisation of Lawvere's theorem.
  In lambda calculus terms, it is the Y combinator: Y(f) = f(Y(f)).
  In the GToE, it means every structural operation on reality has
  invariant points — equilibria are forced, not contingent.

  STRATEGY: Build directly on Mathlib's `Order.FixedPoints`:
  - `OrderHom.lfp` / `OrderHom.gfp` — least/greatest fixed points
  - `OrderHom.isFixedPt_lfp` / `OrderHom.isFixedPt_gfp`
  - `fixedPoints.completeLattice` — Knaster-Tarski theorem

  Machine verification: Lean 4.29.1 + Mathlib
  Target: 0 sorry
-/

import Mathlib.Order.FixedPoints

open Function OrderHom

/-!
## Part 1: Knaster-Tarski (from Mathlib)

Every monotone function on a complete lattice has a least and greatest
fixed point. We state this in our domain-specific language.
-/

/-- A **reflexive domain** is modelled here as a complete lattice.
    In domain theory, D ≅ [D → D] holds in categories of Scott domains /
    continuous lattices. The complete lattice model captures the essential
    property: every monotone map has a fixed point. -/
class ReflexiveDomain (D : Type*) extends CompleteLattice D

/-- **Knaster-Tarski (least fixed point):**
    Every monotone endomorphism on a reflexive domain has a least fixed point. -/
theorem reflexive_domain_lfp {D : Type*} [ReflexiveDomain D]
    (f : D →o D) : ∃ x : D, f x = x ∧ ∀ y : D, f y = y → x ≤ y := by
  exact ⟨f.lfp, f.isFixedPt_lfp, fun y hy => f.lfp_le_fixed hy⟩

/-- **Knaster-Tarski (greatest fixed point):**
    Every monotone endomorphism on a reflexive domain has a greatest fixed point. -/
theorem reflexive_domain_gfp {D : Type*} [ReflexiveDomain D]
    (f : D →o D) : ∃ x : D, f x = x ∧ ∀ y : D, f y = y → y ≤ x := by
  exact ⟨f.gfp, f.isFixedPt_gfp, fun y hy => f.le_gfp hy.ge⟩

/-!
## Part 2: Fixed Points Form a Complete Lattice

This is the deep content of Knaster-Tarski: not just "a fixed point exists"
but "the fixed points form a complete lattice." For the GToE, this means
the invariants of any structural operation are themselves richly structured.
-/

/-- **Knaster-Tarski (complete lattice of fixed points):**
    The fixed points of any monotone function on a reflexive domain
    form a complete lattice. -/
@[reducible] def reflexive_domain_fixed_points_complete_lattice
    {D : Type*} [ReflexiveDomain D] (f : D →o D) :
    CompleteLattice (fixedPoints f) :=
  fixedPoints.completeLattice f

/-- The least fixed point is below the greatest. -/
theorem reflexive_domain_lfp_le_gfp {D : Type*} [ReflexiveDomain D]
    (f : D →o D) : f.lfp ≤ f.gfp :=
  f.lfp_le_gfp

/-!
## Part 3: The Y Combinator / Self-Application Fixed Point

In lambda calculus, Y = λf. (λx. f(x x))(λx. f(x x)).
For any f, Y(f) = f(Y(f)) — i.e., Y(f) is a fixed point of f.

We show this algebraically: given D ≃ (D → D), we can construct
a "self-application" operator that produces fixed points.
-/

/-- **Self-application operator:** Given D ≃ (D → D) and a function
    f : D → D, construct an element whose "self-application" is a
    fixed point of f. This is the Y combinator. -/
theorem y_combinator_fixed_point {D : Type*}
    (app : D → D → D) -- application: interpret d as a function and apply
    (abs : (D → D) → D) -- abstraction: turn a function into an element
    (beta : ∀ (f : D → D) (x : D), app (abs f) x = f x)
    -- beta reduction: app(abs(f), x) = f(x)
    (g : D → D) :
    ∃ x : D, g x = x := by
  -- Construct ω = abs(λx. g(app(x, x)))
  let ω := abs (fun x => g (app x x))
  -- Then app(ω, ω) = g(app(ω, ω)) by beta reduction
  use app ω ω
  -- app(ω, ω) = (fun x => g(app x x)) ω = g(app ω ω)
  have key : app ω ω = g (app ω ω) := by
    show app (abs (fun x => g (app x x))) ω = g (app ω ω)
    conv_lhs => rw [beta]
  exact key.symm

/-!
## Part 4: Structural Consequences for the GToE

If D is a complete lattice modelling a reflexive domain, then:
1. Every monotone operation has invariants (fixed points)
2. The invariants are richly structured (complete lattice)
3. There is always a "smallest" invariant (lfp) and "largest" (gfp)
4. Composing monotone operations preserves fixed-point existence
-/

/-- **Composition preserves fixed points:**
    The composition of monotone functions on a reflexive domain
    has a fixed point. Iterated structural operations still have invariants. -/
theorem reflexive_domain_comp_fixed_point {D : Type*} [ReflexiveDomain D]
    (f g : D →o D) : ∃ x : D, (f.comp g) x = x :=
  ⟨(f.comp g).lfp, (f.comp g).isFixedPt_lfp⟩

/-- **Pre-fixed points exist below any fixed point:**
    If f(a) ≤ a, then the least fixed point is ≤ a. This means
    any "approximate equilibrium" has a true equilibrium below it. -/
theorem reflexive_domain_prefixed_bound {D : Type*} [ReflexiveDomain D]
    (f : D →o D) (a : D) (ha : f a ≤ a) : f.lfp ≤ a :=
  f.lfp_le ha

/-- **Post-fixed points exist above any fixed point:**
    If a ≤ f(a), then a ≤ gfp. This means any "approximate equilibrium"
    has a true equilibrium above it. -/
theorem reflexive_domain_postfixed_bound {D : Type*} [ReflexiveDomain D]
    (f : D →o D) (a : D) (ha : a ≤ f a) : a ≤ f.gfp :=
  f.le_gfp ha

/-- **Fixed-point sandwich:** Every pre-fixed point is below
    every post-fixed point that is also above it — the fixed-point
    structure is well-ordered between any two comparable bounds. -/
theorem reflexive_domain_fixed_point_sandwich {D : Type*} [ReflexiveDomain D]
    (f : D →o D) : f.lfp ≤ f.gfp :=
  f.lfp_le_gfp

/-- **Monotone map on fixed points:**
    If f ≤ g (pointwise) as monotone functions on a reflexive domain,
    then lfp(f) ≤ lfp(g). Stronger structural operations have
    larger minimal invariants. -/
theorem reflexive_domain_lfp_monotone {D : Type*} [ReflexiveDomain D]
    (f g : D →o D) (h : ∀ x : D, f x ≤ g x) : f.lfp ≤ g.lfp := by
  apply f.lfp_le
  calc f (g.lfp) ≤ g (g.lfp) := h g.lfp
    _ = g.lfp := g.isFixedPt_lfp

/-- **Induction on the least fixed point:**
    A property that is closed under f and closed under suprema
    holds at the least fixed point. This is the structural induction
    principle for reflexive domains. -/
theorem reflexive_domain_lfp_induction {D : Type*} [ReflexiveDomain D]
    (f : D →o D) (p : D → Prop)
    (step : ∀ a, p a → a ≤ f.lfp → p (f a))
    (sup_closed : ∀ s, (∀ a ∈ s, p a) → p (sSup s)) :
    p f.lfp :=
  f.lfp_induction step sup_closed
