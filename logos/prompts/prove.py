"""Proof generation prompts."""

PROOF_PROMPT = """You are a research mathematician writing a formal proof for publication
in a peer-reviewed journal. The proof must be rigorous, step-by-step, with every
step justified.

## The Proposition

{proposition}

Natural language: {proposition_natural}

## Context

This convergence was discovered between: {domains}
Formalisation type: {formalisation_type}
Mathematical apparatus: {apparatus}

Supporting established results:
{supporting_results_text}

## Requirements

1. State the proposition formally and precisely.
2. List ALL assumptions explicitly (including any that might seem obvious).
3. Provide a step-by-step proof where EVERY step is justified by:
   - A previous step
   - An established theorem (named and cited)
   - An axiom of the framework
   - A definition
4. Identify ALL dependencies on established results.
5. Be HONEST about any steps that require hand-waving or are not fully rigorous.
   Mark these as "[Gap: ...]" rather than glossing over them.
6. If the proof requires mathematics that doesn't exist yet, say so explicitly
   rather than pretending it does.

## Output format

Return JSON:
{{
  "proposition_formal": "Precise formal statement of what is being proved",
  "assumptions": ["List every assumption"],
  "proof_steps": [
    {{
      "step_number": 1,
      "statement": "What this step establishes",
      "justification": "Why this step is valid",
      "dependencies": ["Previous steps or literature references"]
    }}
  ],
  "dependencies_literature": [
    {{
      "name": "Theorem/result name",
      "authors": "Who proved it",
      "year": "When",
      "field": "Which field",
      "statement": "What the theorem says",
      "usage": "How it's used in this proof"
    }}
  ],
  "within_standard_mathematics": true/false,
  "new_mathematics_needed": "Description of what new maths is needed, or empty string",
  "gaps": ["Any acknowledged gaps in the proof"],
  "limitations": ["Limitations of this proof"],
  "proof_sketch": "2-3 sentence summary of the proof strategy"
}}
"""

PROOF_NATURAL_PROMPT = """You are writing the natural-language version of a formal proof
for publication. This should read like a proof in a mathematics journal — precise,
elegant, and complete.

## The Proof (structured)

Proposition: {proposition}
Assumptions: {assumptions}
Steps: {steps_text}
Dependencies: {dependencies_text}

## Requirements

Write a flowing natural-language proof that:
1. States the proposition clearly
2. Lists assumptions as "We assume..." or "Let..."
3. Proceeds through the argument with clear logical connectives
4. Names every theorem and result invoked
5. Acknowledges any gaps with "[Note: ...]"
6. Ends with a clear conclusion: "This completes the proof." or QED equivalent

The proof should be 200-800 words. No JSON — write prose.
"""
