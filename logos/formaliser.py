"""The Formaliser — core Logos engine.

Takes a structured convergence and produces a formal mathematical proof.
Three stages: detect type → select apparatus → generate proof.
"""

from __future__ import annotations

from dataclasses import asdict

from logos.api import ClaudeAPI
from logos.models import (
    ProofRecord, LogRecord, FlagRecord,
    FormalisationType, ProofConfidence,
)
from logos.prompts.detect_type import DETECT_TYPE_PROMPT, SELECT_APPARATUS_PROMPT
from logos.prompts.prove import PROOF_PROMPT, PROOF_NATURAL_PROMPT


SYSTEM_PROMPT = (
    "You are Logos, a mathematical formalisation AI. You produce rigorous formal proofs "
    "of cross-domain structural convergences. You are honest about limitations, "
    "acknowledge gaps rather than hiding them, and never claim more rigour than you have."
)


class Formaliser:
    """Core formalisation engine — type detection, apparatus selection, proof generation."""

    def __init__(self, api: ClaudeAPI):
        self.api = api

    def formalise(self, convergence: dict) -> tuple[ProofRecord, LogRecord, FlagRecord]:
        """Formalise a single convergence.

        Args:
            convergence: Dict matching Gnosis Convergence schema.

        Returns:
            Tuple of (ProofRecord, LogRecord, FlagRecord).
        """
        proof = ProofRecord(convergence_id=convergence.get("id", ""))
        proof.source_convergence = convergence
        log = LogRecord(proof_id=proof.id)
        flag = FlagRecord(proof_id=proof.id)

        # Stage 1: Detect formalisation type
        type_result = self._detect_type(convergence, log)
        proof.formalisation_type = type_result["formalisation_type"]

        # Stage 2: Select mathematical apparatus
        apparatus_result = self._select_apparatus(convergence, proof.formalisation_type, log)
        proof.mathematical_apparatus = [apparatus_result["primary_apparatus"]] + apparatus_result.get("supporting_apparatus", [])
        proof.apparatus_justification = apparatus_result.get("justification", "")

        # Stage 3: Generate the proof
        proof_result = self._generate_proof(convergence, proof, log)
        proof.proposition = proof_result.get("proposition_formal", "")
        proof.proposition_natural = convergence.get("structural_claim", "")
        proof.proof_steps = proof_result.get("proof_steps", [])
        proof.dependencies_literature = proof_result.get("dependencies_literature", [])
        proof.assumptions = proof_result.get("assumptions", [])
        proof.within_standard_mathematics = proof_result.get("within_standard_mathematics", True)
        proof.new_mathematics_needed = proof_result.get("new_mathematics_needed", "")
        proof.limitations = proof_result.get("gaps", []) + proof_result.get("limitations", [])

        # Stage 4: Generate natural-language proof
        proof.proof_natural = self._generate_natural_proof(proof, log)

        # Stage 5: Store enrichment metadata
        proof.run_metadata = {
            "model_fast": self.api.config.model_fast,
            "model_deep": self.api.config.model_deep,
            "api_calls": self.api.stats.calls,
            "cost_usd": self.api.stats.cost_usd,
        }

        # Flag if needed
        self._check_flags(proof, flag, type_result)

        return proof, log, flag

    def _detect_type(self, convergence: dict, log: LogRecord) -> dict:
        """Stage 1: Detect the appropriate formalisation type."""

        enrichment = self._build_enrichment_section(convergence)
        supporting_text = self._build_supporting_text(convergence)

        prompt = DETECT_TYPE_PROMPT.format(
            structural_claim=convergence.get("structural_claim", ""),
            convergence_type=convergence.get("convergence_type", ""),
            domains=", ".join(convergence.get("domain_names", convergence.get("domains", []))),
            categories=", ".join(convergence.get("source_categories", [])),
            supporting_results_text=supporting_text,
            enrichment_section=enrichment,
        )

        data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT)

        log.add_decision(
            step="detect_formalisation_type",
            choice=data.get("formalisation_type", "custom"),
            alternatives=[data.get("alternative_considered", "")],
            reasoning=data.get("reasoning", ""),
        )

        return data

    def _select_apparatus(self, convergence: dict, formalisation_type: str, log: LogRecord) -> dict:
        """Stage 2: Select the mathematical apparatus."""

        enrichment = self._build_enrichment_section(convergence)

        prompt = SELECT_APPARATUS_PROMPT.format(
            structural_claim=convergence.get("structural_claim", ""),
            formalisation_type=formalisation_type,
            domains=", ".join(convergence.get("domain_names", convergence.get("domains", []))),
            enrichment_section=enrichment,
        )

        data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT)

        all_apparatus = [data.get("primary_apparatus", "")] + data.get("supporting_apparatus", [])
        log.add_decision(
            step="select_mathematical_apparatus",
            choice=", ".join(all_apparatus),
            alternatives=[],
            reasoning=data.get("justification", ""),
        )

        return data

    def _generate_proof(self, convergence: dict, proof: ProofRecord, log: LogRecord) -> dict:
        """Stage 3: Generate the formal proof."""

        supporting_text = self._build_supporting_text(convergence)

        prompt = PROOF_PROMPT.format(
            proposition=convergence.get("structural_claim", ""),
            proposition_natural=convergence.get("structural_claim", ""),
            domains=", ".join(convergence.get("domain_names", convergence.get("domains", []))),
            formalisation_type=proof.formalisation_type,
            apparatus=", ".join(proof.mathematical_apparatus),
            supporting_results_text=supporting_text,
        )

        data = self.api.query_deep_json(prompt, system=SYSTEM_PROMPT, max_tokens=16384)

        log.add_decision(
            step="generate_proof",
            choice=data.get("proof_sketch", ""),
            alternatives=[],
            reasoning=f"Generated {len(data.get('proof_steps', []))} proof steps",
        )

        return data

    def _generate_natural_proof(self, proof: ProofRecord, log: LogRecord) -> str:
        """Stage 4: Generate a flowing natural-language proof."""

        steps_text = "\n".join(
            f"Step {s.get('step_number', i+1)}: {s.get('statement', '')} "
            f"[Justification: {s.get('justification', '')}]"
            for i, s in enumerate(proof.proof_steps)
        )

        deps_text = "\n".join(
            f"- {d.get('name', '')}: {d.get('statement', '')}"
            for d in proof.dependencies_literature
        )

        prompt = PROOF_NATURAL_PROMPT.format(
            proposition=proof.proposition or proof.proposition_natural,
            assumptions=", ".join(proof.assumptions),
            steps_text=steps_text,
            dependencies_text=deps_text,
        )

        text = self.api.query_deep(prompt, system=SYSTEM_PROMPT, max_tokens=4096)

        log.add_decision(
            step="generate_natural_language_proof",
            choice=f"Generated {len(text)} characters",
            alternatives=[],
            reasoning="Natural-language rendering of structured proof",
        )

        return text.strip()

    def _check_flags(self, proof: ProofRecord, flag: FlagRecord, type_result: dict):
        """Check if the proof needs human review flagging."""

        difficulty = type_result.get("difficulty_assessment", "")

        if not proof.within_standard_mathematics:
            flag.flag(
                reason=f"Requires new mathematics: {proof.new_mathematics_needed}",
                priority="critical",
                expertise=["mathematical foundations", "relevant domain experts"],
            )

        if difficulty == "requires_new_mathematics":
            flag.flag(
                reason="Difficulty assessed as requiring new mathematics",
                priority="critical",
                expertise=["mathematical foundations"],
            )

        if difficulty == "challenging":
            flag.flag(
                reason="Difficulty assessed as challenging",
                priority="recommended",
                expertise=["relevant mathematical domain experts"],
            )

        if proof.limitations:
            gap_count = len(proof.limitations)
            if gap_count >= 3:
                flag.flag(
                    reason=f"{gap_count} gaps/limitations identified in proof",
                    priority="recommended",
                )

        if proof.formalisation_type == "custom":
            flag.flag(
                reason="Custom formalisation type — no standard template applies",
                priority="recommended",
                expertise=["mathematical logic"],
            )

    def _build_enrichment_section(self, convergence: dict) -> str:
        """Build the enrichment section from v2 Gnosis fields (if present)."""
        parts = []

        math_structs = convergence.get("mathematical_structures", [])
        if math_structs:
            parts.append(f"Mathematical structures identified: {', '.join(math_structs)}")

        proposed_eq = convergence.get("proposed_equivalence", "")
        if proposed_eq:
            parts.append(f"Proposed equivalence type: {proposed_eq}")

        hint = convergence.get("formalisability_hint", "")
        if hint:
            parts.append(f"Formalisability assessment: {hint}")

        ea = convergence.get("ea_scores", {})
        if ea:
            parts.append(
                f"EA scores: strength={ea.get('strength', 'N/A')}, "
                f"independence={ea.get('independence', 'N/A')}, "
                f"adversarial={ea.get('adversarial', 'N/A')}, "
                f"confidence={ea.get('confidence', 'N/A')} "
                f"({ea.get('confidence_category', 'N/A')})"
            )

        if parts:
            return "## Enrichment Data (from Gnosis)\n\n" + "\n".join(f"- {p}" for p in parts)
        return ""

    def _build_supporting_text(self, convergence: dict) -> str:
        """Build the supporting results text."""
        results = convergence.get("supporting_results", [])
        if not results:
            return "(No supporting results provided)"

        lines = []
        for r in results:
            domain = r.get("domain_name", r.get("domain_id", "unknown"))
            name = r.get("result_name", "unnamed")
            conclusion = r.get("structural_conclusion", "")
            status = r.get("epistemic_status", "")
            lines.append(f"- [{domain}] {name}: {conclusion} (status: {status})")

        return "\n".join(lines)
