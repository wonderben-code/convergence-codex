"""Lean 4 code generation prompts."""

LEAN_FEASIBILITY_PROMPT = """You are assessing whether a mathematical proof can be
formalised in Lean 4 with Mathlib.

## The Proof

Proposition: {proposition}
Mathematical apparatus: {apparatus}
Key theorems invoked: {key_theorems}
Mathlib coverage: {mathlib_coverage}

## Task

Assess whether this proof can be expressed in Lean 4:

1. Are the required definitions available in Mathlib?
2. Are the key theorems available in Mathlib?
3. What would need to be defined from scratch?
4. Is the proof structure expressible in Lean's type theory?

Return JSON:
{{
  "feasible": true/false,
  "partial": true/false,
  "available_in_mathlib": ["Definitions/theorems that ARE in Mathlib"],
  "missing_from_mathlib": ["Definitions/theorems that are NOT in Mathlib"],
  "estimated_lean_lines": 0,
  "difficulty": "straightforward" | "moderate" | "challenging" | "infeasible",
  "notes": "Any additional notes about Lean formalisation feasibility"
}}
"""

LEAN_GENERATE_PROMPT = """You are generating Lean 4 code with Mathlib imports for a
mathematical proof.

## The Proof

Proposition: {proposition}
Proof steps: {steps_text}
Available in Mathlib: {available_in_mathlib}
Missing from Mathlib: {missing_from_mathlib}

## Requirements

1. Generate valid Lean 4 syntax
2. Use Mathlib imports where available
3. For missing definitions, write `sorry` with a comment explaining what's needed
4. Structure the proof to match the natural-language proof steps
5. Include type signatures and docstrings
6. If the proof is only partially formalisable, formalise what you can and
   mark the rest with sorry

Return JSON:
{{
  "lean_code": "The full Lean 4 code as a string",
  "imports": ["Required Mathlib imports"],
  "sorry_count": 0,
  "sorry_reasons": ["Why each sorry was needed"],
  "notes": "Any notes about the Lean code"
}}
"""
