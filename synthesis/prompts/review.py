"""Paper review and quality prompts."""

REVIEW_PROMPT = """You are a senior interdisciplinary reviewer assessing a paper for the Convergence Codex.

You are an expert in at least two of the domains covered in this paper. You are also
a demanding editor who cares deeply about clarity, honesty, and accessibility.

## The Paper

Title: {title}

{full_text}

## Review Criteria

Evaluate EACH of the following. Be specific — cite exact sentences or paragraphs.

1. **Logical consistency** — do claims follow from evidence? Are there any logical gaps?
2. **Citation accuracy** — are all citations real and correctly used?
3. **Epistemic accuracy** — are confidence levels correctly represented? Is there ANY over-claiming?
4. **Honest scoping** — is the Honest Scope section complete and genuinely honest? Would a sceptic find anything missing?
5. **Interdisciplinary accessibility** — could a researcher from domain A understand the domain B content? Is every technical term explained on first use? Is mathematical notation accompanied by plain-language interpretation?
6. **Completeness** — are all required sections present and adequate?
7. **Narrative quality** — does the paper tell a coherent story? Does the reader understand WHY each convergence matters, not just WHAT it is?
8. **Self-containedness** — can this paper be understood without reading any other Codex paper?
9. **Readability** — is the prose clear and engaging? Or is it dry, jargon-heavy, or formulaic?
10. **Appendix quality** — are the appendices well-introduced and interpretable by a reader unfamiliar with the pipeline internals?

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
      "issue": "what's wrong — quote the problematic text",
      "severity": "critical" | "major" | "minor",
      "suggested_fix": "specific rewrite or fix"
    }}
  ],
  "strengths": ["what the paper does well — be specific"],
  "readability_score": 0.0-1.0,
  "accessibility_score": 0.0-1.0,
  "verdict": "accept" | "minor_revision" | "major_revision"
}}
"""

REVISION_PROMPT = """You are revising a section of a Convergence Codex paper based on expert review feedback.

## Paper Title
{paper_title}

## Section to Revise
### {section_title}

{section_content}

## Review Issues to Address

{review_issues}

## Instructions

Rewrite this section to address ALL of the issues listed above. Your revision must:

1. Fix every critical and major issue identified
2. Preserve all factual content and data — do NOT remove or alter any evidence, scores, or claims
3. Maintain the same overall structure unless the review specifically criticises it
4. Keep the same level of detail (don't make it shorter to avoid issues — fix the issues)
5. Improve clarity, readability, and interdisciplinary accessibility wherever possible
6. If the review says something is unclear or jargon-heavy, add explanations
7. If the review says there's over-claiming, soften the language to match the evidence
8. If the review says a connection is unexplained, explain it

Return the COMPLETE revised section text (markdown). Not a diff — the full rewritten section.
"""
