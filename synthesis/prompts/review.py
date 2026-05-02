"""Paper review and quality prompts."""

REVIEW_PROMPT = """You are reviewing a paper draft for the Convergence Codex.

## The Paper

Title: {title}

{full_text}

## Review Criteria

Check for:
1. **Logical consistency** — do claims follow from evidence?
2. **Citation accuracy** — are all citations real and correctly used?
3. **Epistemic accuracy** — are confidence levels correctly represented?
4. **Honest scoping** — is the Honest Scope section complete and honest?
5. **Style consistency** — does it match the Codex voice?
6. **Completeness** — are all required sections present and adequate?
7. **Over-claiming** — does the paper claim more than the evidence supports?

Return JSON:
{{
  "overall_quality": 0.0-1.0,
  "section_scores": {{
    "abstract": 0.0-1.0,
    "introduction": 0.0-1.0,
    "methods": 0.0-1.0,
    "results": 0.0-1.0,
    "discussion": 0.0-1.0,
    "honest_scope": 0.0-1.0,
    "references": 0.0-1.0,
    "conclusion": 0.0-1.0
  }},
  "issues": [
    {{
      "section": "which section",
      "issue": "what's wrong",
      "severity": "critical" | "major" | "minor",
      "suggested_fix": "how to fix"
    }}
  ],
  "strengths": ["what the paper does well"],
  "verdict": "accept" | "minor_revision" | "major_revision"
}}
"""
