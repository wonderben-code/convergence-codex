"""Adversarial validation prompts."""

ADVERSARIAL_PROOF_PROMPT = """You are an adversarial reviewer at a top mathematics journal.
Your job is to BREAK this proof. Find every gap, every unjustified step, every hidden
assumption, every logical error.

## The Proof

Proposition: {proposition}

Proof:
{proof_text}

Assumptions stated: {assumptions}
Dependencies cited: {dependencies}

## Your Task

Attack this proof relentlessly:

1. **Logical gaps** — Are there steps where the conclusion doesn't follow from the premises?
2. **Hidden assumptions** — Are there unstated assumptions the proof relies on?
3. **Circular reasoning** — Does any step depend on what's being proved?
4. **Over-generalisation** — Does the proof claim more than it actually shows?
5. **Citation errors** — Are the cited theorems used correctly? Do they actually say what the proof claims?
6. **Structural issues** — Is the proof structure sound? Could the same argument "prove" something false?
7. **Missing cases** — Are there cases or edge conditions not handled?
8. **Definitional issues** — Are all terms well-defined? Are there ambiguities?

Be HARSH. A proof that survives harsh review is worth more than a proof that only
survived gentle review.

Return JSON:
{{
  "proof_soundness": 0.0-1.0,
  "gaps": [
    {{
      "step": "Which step",
      "issue": "What's wrong",
      "severity": "critical" | "major" | "minor",
      "fixable": true/false,
      "suggested_fix": "How to fix it, if fixable"
    }}
  ],
  "hidden_assumptions": ["Assumptions the proof relies on but doesn't state"],
  "circular_reasoning": true/false,
  "circular_details": "Details if circular",
  "over_generalisation": true/false,
  "over_generalisation_details": "What the proof actually proves vs what it claims",
  "citation_issues": ["Any issues with cited theorems"],
  "structural_soundness": 0.0-1.0,
  "overall_assessment": "2-3 sentence overall assessment",
  "verdict": "accept" | "major_revision" | "reject"
}}
"""

INTERNAL_CONSISTENCY_PROMPT = """You are checking the internal consistency of a formal proof.

## The Proof

Proposition: {proposition}
Proof steps:
{steps_text}

Stated assumptions: {assumptions}

## Checks

1. Does the proof actually prove the stated proposition? (Not something slightly different)
2. Are ALL assumptions explicitly listed? (Check each step for implicit assumptions)
3. Does each step actually follow from its stated justification?
4. Is the proof complete? (No missing cases, no hand-waving at critical points)

Return JSON:
{{
  "proves_stated_proposition": true/false,
  "proves_what_instead": "If false, what does it actually prove?",
  "all_assumptions_listed": true/false,
  "missing_assumptions": ["Any unlisted assumptions found"],
  "steps_valid": true/false,
  "invalid_steps": [
    {{
      "step": "step number",
      "issue": "Why it doesn't follow"
    }}
  ],
  "proof_complete": true/false,
  "completeness_issues": ["What's missing"],
  "internal_score": 0.0-1.0
}}
"""

CROSS_PROOF_PROMPT = """You are checking whether a new proof is consistent with
existing proofs in the Logos corpus.

## New Proof

Proposition: {new_proposition}
Assumptions: {new_assumptions}
Key claims: {new_key_claims}

## Existing Proofs (summaries)

{existing_proofs_text}

## Checks

1. Does the new proof contradict any existing proof?
2. Does it depend on assumptions that conflict with other proofs?
3. If it proves A has property P, and another proof proves A has property Q,
   are P and Q compatible?
4. Are there beneficial connections (the new proof strengthens or extends existing proofs)?

Return JSON:
{{
  "contradictions_found": false,
  "contradiction_details": ["Details of any contradictions"],
  "assumption_conflicts": ["Conflicting assumptions with existing proofs"],
  "beneficial_connections": ["Ways the new proof connects to existing proofs"],
  "consistency_score": 0.0-1.0,
  "notes": "Any additional notes"
}}
"""
