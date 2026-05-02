"""Paper boundary detection prompts."""

BOUNDARY_PROMPT = """You are deciding how to group discoveries and proofs into papers.

## Available Material

{n_convergences} convergences across these domain pairs:
{domain_pairs_text}

{n_proofs} formal proofs with these formalisation types:
{proof_types_text}

{n_findings} meta-findings at these levels:
{findings_levels_text}

## Grouping Criteria

Papers should be:
1. **Conceptually coherent** — related discoveries belong together
2. **Appropriately sized** — {min_words}-{max_words} words (roughly 4-10 convergences per paper)
3. **Distinctly contributing** — each paper makes a clear, self-contained contribution
4. **Non-overlapping** — a convergence shouldn't appear in multiple papers as a primary result

Consider grouping by:
- Domain pair (all Physics × Biology convergences)
- Structural theme (all conservation-law convergences)
- Formalisability (all machine-verified proofs together)
- Level (all meta-convergences and fixed points together)

## Output

Return JSON:
{{
  "papers": [
    {{
      "title_suggestion": "Suggested paper title",
      "theme": "What unifies this paper",
      "convergence_ids": ["ids to include"],
      "proof_ids": ["corresponding proof ids"],
      "finding_ids": ["relevant finding ids"],
      "estimated_words": 0,
      "reasoning": "Why these belong together"
    }}
  ],
  "ungrouped_convergence_ids": ["Any that don't fit a natural paper"],
  "grouping_reasoning": "Overall reasoning for the grouping"
}}
"""
