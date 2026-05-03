"""Back-Translation Alignment — catches "proved the wrong thing" failures.

After Logos generates a formal proposition from a convergence claim,
this module translates the proposition BACK to natural language and
compares it with the original claim. If they don't match, the proof
may be correct but prove something different from what was claimed.

Does NOT filter — flags misalignment and scores alignment 0-1.
"""

from __future__ import annotations

import re

from logos.api import ClaudeAPI
from logos.models import ProofRecord, LogRecord


SYSTEM_PROMPT = (
    "You are a mathematical translator. Your job is to take formal mathematical "
    "statements and express them in plain, precise natural language. Be accurate — "
    "do not add interpretation, just describe what the formal statement actually says."
)

BACK_TRANSLATE_PROMPT = """Translate this formal mathematical proposition back into plain natural language.

FORMAL PROPOSITION:
{proposition}

MATHEMATICAL APPARATUS: {apparatus}

ASSUMPTIONS:
{assumptions}

Describe in 1-3 sentences what this proposition actually claims, in plain language
that a scientist (not necessarily a mathematician) would understand.

Do NOT interpret or extend — just describe what the formal statement says.

Return JSON:
{{
    "natural_language": "plain language description of what the proposition says",
    "key_claims": ["list of specific claims the proposition makes"],
    "domain_objects": ["mathematical objects referenced"]
}}"""

ALIGNMENT_PROMPT = """Compare these two statements and score their alignment.

ORIGINAL CONVERGENCE CLAIM (what we intended to prove):
{original_claim}

BACK-TRANSLATED PROPOSITION (what we actually formalised):
{back_translation}

Score the alignment on these dimensions:

1. subject_match (0-1): Are they about the same mathematical objects/structures?
2. claim_match (0-1): Do they make the same claim about those objects?
3. strength_match (0-1): Is the formal proposition the same strength as the
   original claim? (0 = much weaker/stronger, 1 = same strength)
4. overall_alignment (0-1): Overall, does proving the formal proposition
   establish the original convergence claim?

Return JSON:
{{
    "subject_match": 0.0-1.0,
    "claim_match": 0.0-1.0,
    "strength_match": 0.0-1.0,
    "overall_alignment": 0.0-1.0,
    "misalignment_notes": "explain any differences",
    "is_aligned": true/false
}}"""


class BackTranslator:
    """Checks proposition-claim alignment via back-translation."""

    def __init__(self, api: ClaudeAPI):
        self.api = api

    def check_alignment(self, proof: ProofRecord, log: LogRecord) -> dict:
        """Check that the formal proposition matches the original convergence claim.

        1. Translate the formal proposition back to natural language
        2. Compare with the original convergence claim
        3. Score alignment

        Returns dict with alignment scores and back-translation.
        Modifies proof.back_translation_alignment in place.
        """
        proposition = proof.proposition or proof.proposition_natural
        original_claim = proof.source_convergence.get("structural_claim", "")

        if not proposition or not original_claim:
            result = {
                "overall_alignment": 0.5,
                "reason": "missing_data",
                "is_aligned": True,
            }
            proof.back_translation_alignment = result
            return result

        # Step 1: Back-translate the formal proposition
        back_translation = self._back_translate(proof)
        if not back_translation:
            result = {
                "overall_alignment": 0.5,
                "reason": "back_translation_failed",
                "is_aligned": True,
            }
            proof.back_translation_alignment = result
            return result

        # Step 2: Score alignment between original claim and back-translation
        alignment = self._score_alignment(original_claim, back_translation)

        # Step 3: Also compute a quick text-similarity check (external, no Claude)
        text_sim = self._text_similarity(original_claim, back_translation)

        result = {
            "back_translation": back_translation,
            "original_claim": original_claim,
            "subject_match": alignment.get("subject_match", 0.5),
            "claim_match": alignment.get("claim_match", 0.5),
            "strength_match": alignment.get("strength_match", 0.5),
            "overall_alignment": alignment.get("overall_alignment", 0.5),
            "text_similarity": text_sim,
            "is_aligned": alignment.get("is_aligned", True),
            "misalignment_notes": alignment.get("misalignment_notes", ""),
        }

        proof.back_translation_alignment = result

        log.add_decision(
            step="back_translation",
            choice=f"alignment={result['overall_alignment']:.2f}, "
                   f"text_sim={text_sim:.2f}, "
                   f"aligned={result['is_aligned']}",
            alternatives=[],
            reasoning=result.get("misalignment_notes", ""),
        )

        return result

    def _back_translate(self, proof: ProofRecord) -> str:
        """Translate formal proposition back to natural language."""
        prompt = BACK_TRANSLATE_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            apparatus=", ".join(proof.mathematical_apparatus),
            assumptions=", ".join(proof.assumptions) or "(none)",
        )

        try:
            data = self.api.query_json(prompt, system=SYSTEM_PROMPT)
            return data.get("natural_language", "")
        except Exception:
            return ""

    def _score_alignment(self, original_claim: str, back_translation: str) -> dict:
        """Score alignment between original claim and back-translation."""
        prompt = ALIGNMENT_PROMPT.format(
            original_claim=original_claim,
            back_translation=back_translation,
        )

        try:
            data = self.api.query_json(
                prompt,
                system=(
                    "You are a mathematical precision checker. Be strict about alignment. "
                    "If the formal proposition proves something subtly different from the "
                    "original claim, that IS a misalignment — even if both are interesting."
                ),
            )
            return data
        except Exception:
            return {"overall_alignment": 0.5, "is_aligned": True}

    @staticmethod
    def _text_similarity(a: str, b: str) -> float:
        """Simple concept-overlap similarity (external, no AI)."""
        stop = {'the', 'and', 'that', 'this', 'for', 'are', 'was', 'with',
                'has', 'have', 'been', 'from', 'will', 'can', 'not', 'but',
                'which', 'their', 'they', 'its', 'also', 'more', 'than'}
        words_a = set(re.findall(r'\b[a-z]{3,}\b', a.lower())) - stop
        words_b = set(re.findall(r'\b[a-z]{3,}\b', b.lower())) - stop
        if not words_a or not words_b:
            return 0.0
        overlap = words_a & words_b
        return round(len(overlap) / max(len(words_a), len(words_b)), 3)
