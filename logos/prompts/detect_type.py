"""Formalisation type detection prompts."""

DETECT_TYPE_PROMPT = """You are a mathematical logician. Given a cross-domain structural convergence,
determine the most appropriate type of formal mathematical treatment.

## The Convergence

Structural claim: {structural_claim}
Convergence type: {convergence_type}
Domains: {domains}
Categories: {categories}

Supporting results:
{supporting_results_text}

{enrichment_section}

## Formalisation Types

Choose the MOST APPROPRIATE type:

1. **isomorphism** — The two structures are formally equivalent. There exists a bijective
   structure-preserving map between them. This is the strongest claim and requires the most
   rigorous proof. Use when the convergence asserts that two mathematical structures are
   the SAME structure in different notation.

2. **equivalence** — A weaker structural correspondence. Functorial relationship, natural
   transformation, or Morita equivalence. The structures share important features but are
   not identical. Use when the convergence asserts structural similarity at an abstract level.

3. **categorical** — The convergence is best captured by a universal property, adjunction,
   or characterisation in terms of limits/colimits. Use when the claim is about what role
   a structure plays rather than what it IS.

4. **axiomatic** — The convergence identifies a set of axioms that both structures satisfy.
   The formalisation is to write down the axiom schema and verify both structures are models.
   Use when the convergence identifies shared abstract principles.

5. **constraint_logic** — The convergence is about structures defined by constraint
   satisfaction. Fixed points, optimisation, equilibria. Use when the claim is about
   structures arising from constraints.

6. **custom** — None of the above capture the convergence well. This requires a novel
   approach. Use only when you can explain why the standard types are inadequate.

## What to return

Return JSON:
{{
  "formalisation_type": "one of the six types above",
  "reasoning": "Why this type is most appropriate (2-3 sentences)",
  "alternative_considered": "The next best type and why it was rejected",
  "difficulty_assessment": "straightforward" | "moderate" | "challenging" | "requires_new_mathematics",
  "key_mathematical_challenge": "The hardest part of formalising this convergence"
}}
"""

SELECT_APPARATUS_PROMPT = """You are a mathematical logician selecting the formal apparatus
to prove a cross-domain structural convergence.

## The Convergence

Structural claim: {structural_claim}
Formalisation type: {formalisation_type}
Domains: {domains}

{enrichment_section}

## Task

Select the mathematical frameworks needed for this proof. Consider:

- **Category theory** — functors, natural transformations, adjunctions, limits, Yoneda
- **Type theory** — dependent types, propositions-as-types, HoTT
- **Set theory** — ZFC constructions, ordinals, cardinals, forcing
- **Measure theory** — sigma-algebras, integration, probability spaces
- **Topology** — open sets, continuity, compactness, homology, homotopy
- **Algebraic structures** — groups, rings, fields, modules, algebras
- **Order theory** — lattices, fixed-point theorems, domain theory
- **Mathematical logic** — model theory, proof theory, computability
- **Dynamical systems** — flows, attractors, bifurcation, stability
- **Information theory** — entropy, mutual information, channel capacity
- **Differential geometry** — manifolds, connections, curvature
- **Functional analysis** — Banach spaces, operators, spectral theory
- **Graph theory** — networks, flows, connectivity

Select 1-4 frameworks. Prefer fewer. The selection should be MINIMAL — only what's
actually needed, not everything tangentially related.

Return JSON:
{{
  "primary_apparatus": "The main framework (single string)",
  "supporting_apparatus": ["Additional frameworks needed (list)"],
  "justification": "Why these frameworks, not others (2-3 sentences)",
  "key_theorems": ["Specific established theorems that will be invoked"],
  "mathlib_coverage": "full" | "partial" | "minimal" | "none",
  "mathlib_notes": "What's available in Mathlib and what's missing"
}}
"""
