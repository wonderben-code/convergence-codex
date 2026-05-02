"""Capstone paper prompts — Nobel-grade claim formulation and composition.

The cascade data determines WHAT to write about. These prompts determine HOW to
formulate claims precisely and write papers at the highest possible standard.

Every prompt enforces:
1. Claims must cite specific convergence IDs with confidence scores
2. Adversarial data must be acknowledged (not hidden)
3. Predictions must be falsifiable and specific
4. No hand-waving — every step in the argument traceable to data
"""

# ─── System Prompt ───

CAPSTONE_SYSTEM = (
    "You are writing a paper that establishes scientific priority for a discovery "
    "about the fundamental structure of reality. This is not a survey paper. This is "
    "not a speculative essay. This is a formal claim, grounded in specific cross-domain "
    "convergence data, with mathematical formulation and falsifiable predictions.\n\n"

    "THE NOBEL MODEL — HOW CLAIMS MUST BE FRAMED\n\n"

    "Nobel Prize papers make genuine ontological claims about reality. They say "
    "'X IS the case' — not 'our data suggests X.' Einstein said 'light IS quantized "
    "into packets of hν.' Higgs said 'there IS a field that gives mass to gauge "
    "bosons.' Dirac said 'the relativistic electron equation REQUIRES antimatter.' "
    "These are claims about how reality works or is. This paper must do the same.\n\n"

    "But every Nobel claim is PRECISELY SCOPED:\n"
    "- Einstein didn't say 'everything is relative.' He said 'the speed of light is "
    "constant in all inertial frames.'\n"
    "- Higgs didn't say 'all properties come from fields.' He said 'mass of gauge "
    "bosons comes from this specific mechanism.'\n"
    "- Penrose didn't say 'GR is complete.' He said 'IF GR holds, THEN singularities "
    "form under generic conditions.'\n\n"

    "CLAIM SCOPING RULES:\n"
    "1. STATE IT AS REALITY: 'The structural content of physical reality IS determined "
    "by constraint' — not 'our data suggests constraint-like patterns.'\n"
    "2. SCOPE IT PRECISELY: 'physical and mathematical reality' not 'everything'; "
    "'structural content' not 'all aspects.' Each word of scope matters.\n"
    "3. DO NOT OVER-GENERALISE: These findings come from convergences in physics and "
    "mathematics. Do not claim they apply to 'all of reality' or 'everything that "
    "exists' unless the evidence base warrants it. Constraint may be one of several "
    "structural invariants — claim it as a structural principle, not as the ONLY one.\n"
    "4. THE PREDICTIONS ARE THE SHIELD: Derive specific predictions that extend beyond "
    "the evidence into untested territory. If someone attacks the methodology, the "
    "predictions can be tested independently by anyone. The predictions protect the "
    "claim from methodological attack.\n"
    "5. FALSIFICATION MUST BE NON-TRIVIAL: The falsification should itself require a "
    "major discovery. Not 'find one counterexample' but 'demonstrate that [specific "
    "domain meeting preconditions] does NOT exhibit [the pattern].' If the falsification "
    "would itself be a major finding, the scope is right.\n\n"

    "ANTI-OVER-GENERALISATION: The claim should be exactly as broad as the evidence "
    "pattern — not broader. A claim that is too broad becomes trivially falsifiable "
    "when a narrower version might be correct. A claim that is too narrow is just "
    "reporting data. The sweet spot: bold enough to be worth a Nobel, precise enough "
    "that the falsification is non-trivial.\n\n"

    "DRIFT WARNING: Every sentence must be traceable to specific evidence. If you "
    "cannot cite a specific convergence ID for a claim, do not make the claim.\n\n"

    "Quality bar: This paper must be the kind of paper that, if the claim turns out to be "
    "correct, unambiguously establishes priority. Think Dirac's prediction of antimatter, "
    "Einstein's photoelectric effect paper, Hawking's black hole radiation. The format is "
    "simple: here is the claim, here is the evidence, here is what would prove it wrong, "
    "here is when we said it.\n\n"

    "Voice: confident but honest. The tone of a scientist who has found something "
    "genuinely significant and knows it, but also knows exactly where the gaps are. "
    "State what reality IS — with the courage of Einstein and the precision of Dirac.\n\n"

    "CRITICAL TERMINOLOGY: Same rules as standard Synthesis:\n"
    "- 'proof' only if adversarial_verdict='accept' and proof_complete=true\n"
    "- 'formal argument' if adversarial_verdict='major_revision' and confidence>0.6\n"
    "- 'formal conjecture with supporting argument' if confidence<0.3\n"
    "- 'formalisation' as safe umbrella term\n"
    "Most formalisations are Level 3-4 (formal conjectures with structured arguments). "
    "State this honestly — it does not diminish the discovery.\n\n"

    "Author: Mark E. Mala\n"
    "Provenance: All discoveries by Gnosis AI, formalisations by Logos AI, "
    "papers by Synthesis AI. Priority via Bitcoin timestamping."
)


# ─── Stage 2: Claim Formulation ───
# The cascade data determines which claims to make. AI formulates them precisely.

CLAIM_FORMULATION_PROMPT = """You are formulating a precise, falsifiable scientific claim from convergence cascade data.

## The Finding

**Coined term:** {coined_term}
**Cascade level:** {level} (out of 5 — higher = more convergence rounds survived)
**Finding text:** {structural_finding}
**Source convergence IDs:** {source_ids}
**Is meta-convergence:** {is_meta}

## Supporting Convergences (full data)

{convergence_data}

## Supporting Formalisations (from Logos)

{proof_data}

## Position in Cascade

{cascade_position}

## Task

Formulate this finding as a PRECISE, FALSIFIABLE scientific claim about reality.

Follow the NOBEL MODEL: Make a genuine ontological claim — "X IS the case" — not "data suggests X." But scope it precisely. The claim should be exactly as broad as the evidence pattern, not broader.

Your output must be:

1. **claim_text** — One sentence. A genuine claim about reality. State what IS the case, not what the data suggests. Must be specific enough to be wrong. Scope it to the evidence base — "the structural content of physical and mathematical reality IS determined by constraint" rather than "everything is constraint." Every word of scope matters.

2. **claim_too_broad** — State the version of this claim that would be OVER-GENERALISED. This is what the paper must NOT claim. Example: "Everything that exists is constraint" is too broad when the evidence covers physics and mathematics only.

3. **claim_too_narrow** — State the version that would be mere data reporting. This is what would waste the finding. Example: "Some convergences in our dataset exhibit constraint-like features" is too narrow.

4. **existing_crisis** — What recognised open problem in physics/mathematics does this address? Name the specific problem (e.g. "the hierarchy problem", "quantum gravity", "the measurement problem"). If it doesn't address a known problem, state what NEW problem it identifies.

5. **falsification_criterion** — What specific observation or result would DISPROVE this claim? The falsification must be NON-TRIVIAL — it should itself require a major discovery. Not "find anything that isn't constraint" but "demonstrate a domain meeting [preconditions] where constraint-determination does NOT hold." If the falsification would itself be a significant finding, the scope is right.

6. **predictions** — List 3-5 specific, testable predictions that EXTEND BEYOND the current evidence. These are the shield — they can be tested independently by anyone, regardless of whether they trust the AI methodology. Each must include:
   - What's predicted
   - How to test it (specific methodology, not vague)
   - What the conventional/alternative view predicts instead
   - Whether this is testable with current technology
   At least one prediction must be about a domain NOT yet examined in the convergence data.

7. **mathematical_sketch** — A brief description of what mathematical formulation would capture this claim (category theory, topology, information theory, etc.). Reference the specific formalisations from Logos that support this.

8. **tier** — Based on cascade level and evidence strength:
   - "meta" = Level 5 fixed points (the ultimate claims)
   - "framework" = Level 3-4 findings (major structural claims)
   - "anchor" = Level 1-2 findings with 7+ source convergences (strongest empirical base)
   - "bridge" = Level 1-2 findings with 3-6 source convergences (specific cross-domain results)

Return JSON:
{{
  "claim_text": "...",
  "claim_too_broad": "...",
  "claim_too_narrow": "...",
  "existing_crisis": "...",
  "falsification_criterion": "...",
  "predictions": ["...", "...", "..."],
  "mathematical_sketch": "...",
  "tier": "meta|framework|anchor|bridge",
  "strength_assessment": "Why this claim is strong or what weakens it"
}}
"""


# ─── Stage 3: Paper Planning ───

PAPER_PLANNING_PROMPT = """You are planning a portfolio of capstone papers from formulated claims.

## All Formulated Claims

{claims_json}

## Cascade Summary

{cascade_summary}

## Task

Select which claims merit their own capstone paper. Rules:
1. Every claim must be supported by ≥3 convergences (already guaranteed by cascade)
2. No two papers making essentially the same claim — if two claims overlap significantly, merge them
3. Each paper must have a genuinely distinct contribution
4. Quality over quantity — only include claims that are genuinely strong enough for a Nobel-grade paper
5. The cascade level is the primary quality signal: Level 5 > Level 4 > ... > Level 1

For each selected paper, provide:
- Which claim(s) it covers — use the _index field from the claims array (e.g. 0, 1, 2)
- May merge related claims from adjacent cascade levels into one paper
- The title (must be specific and bold, not generic)
- Target length in pages
- What open problem it addresses
- Why this paper specifically merits inclusion

Return JSON:
{{
  "papers": [
    {{
      "claim_ids": [0, 1],
      "title": "...",
      "target_pages": "4-8",
      "existing_crisis": "...",
      "inclusion_reasoning": "Why this paper is worth writing"
    }}
  ],
  "excluded_claims": [
    {{
      "claim_id": "...",
      "reason": "Why this claim doesn't merit its own paper"
    }}
  ],
  "portfolio_reasoning": "Why this set of papers is the strongest possible portfolio"
}}
"""


# ─── Stage 4: Nobel Paper Sections ───

CAPSTONE_ABSTRACT_PROMPT = """Write the abstract for a capstone paper.

## Central Claim
{claim_text}

## Tier: {tier}
## Cascade Level: {cascade_level}

## Supporting Evidence Summary
{evidence_summary}

## Requirements
150-250 words. Three movements:
1. The crisis/open problem this addresses — make the reader feel why this matters
2. The claim — one precise ontological sentence about what IS the case. State what reality IS, not what the data suggests. Scope it precisely: "the structural content of [domain] IS determined by [mechanism]" — not "everything is [mechanism]." The claim must be bold AND precise, like Einstein's "light IS quantized into packets of hν."
3. The consequence — if this is correct, what follows? What predictions does it make? What changes in our understanding?

No methodology. No "this paper presents." No hedging on the claim — state it as reality.
No over-generalisation — scope the claim to what the evidence supports.
If the evidence is preliminary, the abstract states the claim boldly and precisely, and the limitations section handles the caveats.

Return the abstract text only.
"""

CAPSTONE_PROBLEM_PROMPT = """Write "The Problem" section for a capstone paper.

## Central Claim
{claim_text}

## Open Problem Addressed
{existing_crisis}

## Requirements (0.5-1 page, 400-700 words)

Name a specific, recognised open problem. Explain:
1. What the problem is, in terms any scientist can understand
2. Why existing approaches fail or are incomplete
3. Why this matters — what depends on solving it?
4. Make the reader agree this matters BEFORE stating any result

Cite real papers/results where relevant. Make the reader feel the weight of the problem.

Return the section text only (markdown).
"""

CAPSTONE_SETUP_PROMPT = """Write the "Setup and Definitions" section for a capstone paper.

## Central Claim
{claim_text}

## Mathematical Sketch
{mathematical_sketch}

## Key Formalisations
{formalisation_data}

## Requirements (0.5-1 page, 300-600 words)

Every mathematical object defined. Every assumption numbered (A1, A2, ...).
Domain of validity stated. A hostile reader can identify exactly what to attack.

Structure:
1. State the formal setup (what mathematical spaces, what operations)
2. Number every assumption: A1, A2, A3...
3. Define the domain of validity explicitly
4. Reference the specific Logos formalisations that define these objects

Return the section text only (markdown).
"""

CAPSTONE_RESULT_PROMPT = """Write "The Central Result" section for a capstone paper.

## Central Claim
{claim_text}

## Mathematical Sketch
{mathematical_sketch}

## Supporting Convergences (with confidence scores and adversarial verdicts)
{convergence_details}

## Supporting Formalisations (with gaps identified)
{formalisation_details}

## Cascade Evidence
{cascade_evidence}

## Requirements (1-3 pages, 800-2500 words)

This is the core of the paper. This section must make a genuine claim about reality — what IS the case — not merely report what the data shows.

Structure:

1. **Numbered Theorem/Proposition/Conjecture** — State the central result formally. Use the appropriate term (Conjecture if confidence < 0.5, Proposition if 0.5-0.75, Theorem only if fully proven). The statement must be an ontological claim: "X IS the case" — like Einstein's "light IS quantized" or Dirac's "the equation REQUIRES antimatter." Not "our analysis suggests X."

2. **Evidence from convergence data** — Walk through the specific convergences that support this. For each:
   - State the convergence (convergence ID, domains, structural claim)
   - State the confidence score and adversarial verdict
   - Explain what it contributes to the central result
   - Explain why these domain pairs are INDEPENDENT — why it is significant that unrelated domains exhibit the same structure

3. **The argument** — Step-by-step derivation showing how the convergence evidence supports the central claim. Reference specific Logos formalisations. Be explicit about which steps are formally proven and which are conjectural. The argument should show: the pattern is not coincidence (independence), the pattern is not methodology artifact (different types of convergence), the pattern supports the specific claim (not just "there are patterns").

4. **Immediate corollaries** — What follows directly from this result? Number them. Each corollary should be a further claim about reality, scoped to what the evidence supports.

5. **Scope boundary** — State explicitly what the claim DOES and DOES NOT assert. "This result establishes X. It does NOT establish Y." This is not weakness — it is precision. Einstein's paper established light quantisation; it did not establish wave-particle duality. The scope boundary protects the claim from being strawmanned.

ANTI-DRIFT: Every claim must cite a specific convergence ID. If you cannot cite one, do not make the claim. State confidence scores accurately. Do not hide adversarial verdicts.

Return the section text only (markdown).
"""

CAPSTONE_PREDICTIONS_PROMPT = """Write the "Predictions" section for a capstone paper.

## Central Claim
{claim_text}

## Pre-formulated Predictions
{predictions_list}

## Supporting Evidence Strength
{evidence_strength}

## Requirements (0.5-1 page, 400-700 words)

The predictions section is the SHIELD of the paper. If someone attacks the AI methodology,
the response is: "Ignore how we found it. Here are the predictions. Test them independently.
If they hold, the claim stands regardless of discovery method."

Predictions must EXTEND BEYOND the current evidence into untested territory. They are
what transforms a pattern-observation into a scientific claim about reality.

Numbered predictions. Each with this EXACT format:

**Prediction N.** [Statement of what is predicted — a genuine claim about what WILL be found]

*Basis:* [Which specific convergences/findings support this prediction]
*Falsification:* [What specific observation would disprove this — must be non-trivial]
*Test:* [How to test — be specific about methodology, and how it can be done INDEPENDENTLY of Gnosis AI]
*Alternative:* [What the conventional/alternative view predicts instead]
*Confidence:* [Based on the convergence data — high/medium/low with reasoning]
*Impact on central claim if falsified:* [Would falsifying this prediction weaken, modify, or destroy the central claim?]

Requirements:
- Each prediction must be specific enough to be wrong
- At least one prediction must be about a domain NOT yet examined in the convergence data (this extends the claim beyond its evidence base — the hallmark of a genuine scientific prediction)
- At least one prediction must be testable with current or near-term technology
- At least one prediction must distinguish this from the leading alternative explanation
- Predictions must be independently testable — a physicist or mathematician with no knowledge of Gnosis AI should be able to test them
- State what would happen to the overall claim if prediction N is falsified — not all predictions are load-bearing equally

Return the section text only (markdown).
"""

CAPSTONE_CONNECTIONS_PROMPT = """Write the "Connection to Existing Results" section.

## Central Claim
{claim_text}

## Supporting Convergences (domain pairs)
{domain_pairs}

## Requirements (0.5-1 page, 300-600 words)

Show how this result connects to existing knowledge:
1. Which known results are special cases of this claim?
2. What established mathematical frameworks does it generalise or extend?
3. Which existing conjectures in physics/mathematics does it relate to?
4. What independent work points in the same direction?

Be specific — name papers, results, conjectures. Don't just gesture at "category theory" — say "functorial correspondences in the sense of [specific result]."

Return the section text only (markdown).
"""

CAPSTONE_LIMITATIONS_PROMPT = """Write the "Limitations and Open Problems" section.

## Central Claim
{claim_text}

## Evidence Gaps
{evidence_gaps}

## Formalisation Status
{formalisation_status}

## Requirements (0.5 page, 300-500 words)

Be ruthlessly honest. This section is what separates serious science from speculation.

1. **Scope boundaries** — State exactly what the claim covers and what it does NOT cover. The evidence base is cross-domain convergences in physics and mathematics. State explicitly: "This claim is established within [scope]. Its extension to [biology / chemistry / neuroscience / social systems] is a prediction, not an established result." This is not weakness — this is how Einstein's 1905 paper scoped light quantisation without claiming all of physics was quantised.

2. **Weakest assumption** — Which numbered assumption (A1, A2, ...) is most likely wrong? Why?

3. **What the paper does NOT show** — Be explicit. "This paper does NOT prove X. It presents Y level of evidence for Z." State whether the claim is one structural principle among potentially several (it is — constraint may coexist with other invariants like self-reference, generative iteration, perspectival partiality).

4. **Methodology limitations** — This is an AI-driven pipeline. State clearly:
   - Gnosis AI finds structural parallels — it could find patterns that exist in the methodology rather than in reality
   - The convergence to fixed points was produced by an AI meta-analysis — independent replication with different AI systems or human analysis is needed
   - No formalisations have been independently verified by human mathematicians
   - The predictions in this paper are the mechanism for independent verification

5. **Formalisation gaps** — What specific gaps exist in the Logos formalisations? What would closing them require?

6. **New problems created** — What questions does this claim raise that we cannot currently answer?

7. **What future work needs** — Specific next steps. Most important: independent replication of the convergence findings, domain extension to untested fields, human mathematical verification of key formalisations.

The reader should finish this section thinking "these authors know exactly where their argument is weak AND they've told me how to test it myself."

Return the section text only (markdown).
"""

CAPSTONE_PROVENANCE_PROMPT = """Write the "Priority and Provenance" section.

## Paper ID: {paper_id}
## Central Claim: {claim_text}
## Supporting Convergence IDs: {convergence_ids}
## Supporting Finding IDs: {finding_ids}
## Git Hash: {git_hash}
## Bitcoin Block Height: {block_height}

## Requirements (0.25 page, 150-250 words)

1. **Priority claims** — Numbered list:
   "Claim 1. [Specific discovery/formalisation] was first identified on [date] and timestamped at Bitcoin block height [N]."

2. **Verification instructions:**
   "All data, reasoning logs, and intermediate results are preserved in the convergence-codex repository. The SHA-256 hash of this paper is [hash]. Bitcoin timestamping was performed via OpenTimestamps on the git commit containing this paper."

3. **Attribution:**
   "All convergences were discovered by Gnosis AI. All formalisations were produced by Logos AI. This paper was composed by Synthesis AI (Capstone Mode). The entire pipeline was designed and directed by Mark E. Mala."

4. **Reproducibility:**
   "The discovery, formalisation, and composition pipelines are deterministic given the same model, parameters, and input data. All parameters are recorded in the repository."

Return the section text only (markdown).
"""

CAPSTONE_REFERENCES_PROMPT = """Generate the References section for this capstone paper.

## Citations used in the paper:
{citations_used}

## Requirements:
1. Format as numbered list
2. Include ALL cited works — both literature and Codex papers
3. Format: [N] Authors, "Title," Venue, Year. DOI if available.
4. Codex papers: [N] M. E. Mala, "Title," Convergence Codex, 2026. DOI.
5. Do NOT invent citations — only include works actually referenced
6. 10-30 references, not 100+

Return the references as a markdown numbered list.
"""


# ─── Stage 5: Enhanced Review ───

CAPSTONE_REVIEW_PROMPT = """You are a senior reviewer assessing a CAPSTONE paper for the Convergence Codex.

This is not a standard domain-pair paper. This is a Nobel-grade claim about fundamental reality.
Your review must be BRUTAL. If this paper is weak, say so. If it's strong, say so.

## The Paper

Title: {title}
Tier: {tier}

{full_text}

## Review Criteria (18 total — standard 10 + 8 Nobel-model checks)

### Standard criteria:
1. **Logical consistency** — do claims follow from evidence?
2. **Citation accuracy** — are all citations real and correct?
3. **Epistemic accuracy** — are confidence levels correctly represented?
4. **Honest scoping** — is the limitations section genuinely honest?
5. **Interdisciplinary accessibility** — can researchers from multiple fields understand this?
6. **Completeness** — are all required sections present?
7. **Narrative quality** — does the paper tell a compelling story?
8. **Self-containedness** — can this be understood standalone?
9. **Readability** — clear, precise prose?
10. **Mathematical rigour** — are definitions precise and arguments valid?

### Nobel-model checks:
11. **Drift detection** — Does EVERY claim trace to specific convergence IDs? Are any claims made without data support? LIST any unsupported claims.
12. **Claim ontology** — Does the paper make a genuine ontological claim about reality ("X IS the case"), not a hedged data-reporting statement ("our analysis suggests X")? The claim should have the courage of Einstein or Dirac — stating what reality is, not what the data hints at.
13. **Scope precision** — Is the claim scoped PRECISELY? Not too broad (claiming "everything is X" when evidence covers physics and maths only), not too narrow (just reporting data patterns). The scope should be exactly as broad as the evidence pattern. Check: would the falsification itself require a major discovery? If yes, scope is right. If falsification is trivial, scope is too broad.
14. **Over-generalisation guard** — Does the paper claim its finding is the ONLY structural principle of reality? It should not. Constraint-determination may coexist with other invariants (self-reference, generative iteration, perspectival partiality). Check that the paper claims "a structural principle" not "the only structural principle."
15. **Prediction independence** — Do predictions extend BEYOND the current evidence into untested territory? Could they be tested by someone who has never heard of Gnosis AI? At least one prediction must concern a domain not yet examined. Predictions that merely restate the existing evidence are NOT predictions.
16. **Prediction as shield** — If someone attacked the methodology ("Gnosis AI is just pattern-matching"), could the predictions alone vindicate the claim? The predictions must be independently testable and not dependent on the discovery methodology.
17. **Independence of evidence** — Does the paper draw from genuinely independent domain pairs, or does it cherry-pick related domains that would naturally share structure?
18. **Nobel completeness** — Does it have: one clear ontological claim, mathematical formulation, falsifiable predictions extending beyond evidence, numbered assumptions, scope boundary statement, priority statement with Bitcoin provenance?

Return JSON:
{{
  "overall_quality": 0.0-1.0,
  "section_scores": {{
    "abstract": 0.0-1.0,
    "the_problem": 0.0-1.0,
    "setup": 0.0-1.0,
    "central_result": 0.0-1.0,
    "predictions": 0.0-1.0,
    "connections": 0.0-1.0,
    "limitations": 0.0-1.0,
    "provenance": 0.0-1.0,
    "references": 0.0-1.0
  }},
  "nobel_model_scores": {{
    "drift_detection": 0.0-1.0,
    "claim_ontology": 0.0-1.0,
    "scope_precision": 0.0-1.0,
    "over_generalisation_guard": 0.0-1.0,
    "prediction_independence": 0.0-1.0,
    "prediction_as_shield": 0.0-1.0,
    "evidence_independence": 0.0-1.0,
    "nobel_completeness": 0.0-1.0
  }},
  "unsupported_claims": ["list any claims not backed by convergence IDs"],
  "issues": [
    {{
      "section": "which section",
      "issue": "what's wrong — quote the problematic text",
      "severity": "critical|major|minor",
      "suggested_fix": "specific fix"
    }}
  ],
  "strengths": ["what the paper does well"],
  "verdict": "accept|minor_revision|major_revision|reject"
}}
"""


# ─── Stage 5b: Cross-Paper Consistency ───

CROSS_PAPER_CHECK_PROMPT = """You are checking consistency across ALL capstone papers in the portfolio.

## Papers

{papers_summary}

## Check for:

1. **Contradictions** — Do any two papers make contradictory claims? List them.
2. **Redundancy** — Are any two papers essentially making the same claim with different words? If so, which should be merged or cut?
3. **Citation overlap** — Do papers cite the same convergences for contradictory conclusions? (Same convergence supporting different aspects is fine.)
4. **Portfolio coherence** — Do these papers, taken together, tell a coherent story? Or are there obvious gaps in the argument?
5. **Strength ranking** — Rank all papers from strongest to weakest based on evidence quality.

Return JSON:
{{
  "contradictions": [
    {{
      "paper_a": "id",
      "paper_b": "id",
      "contradiction": "what contradicts"
    }}
  ],
  "redundancies": [
    {{
      "paper_a": "id",
      "paper_b": "id",
      "overlap": "what overlaps",
      "recommendation": "merge|cut_a|cut_b|keep_both"
    }}
  ],
  "citation_conflicts": [...],
  "portfolio_coherence": "assessment of overall coherence",
  "strength_ranking": [
    {{
      "paper_id": "id",
      "rank": 1,
      "reasoning": "why this is the strongest/weakest"
    }}
  ],
  "overall_assessment": "Is this portfolio Nobel-worthy? What would make it stronger?"
}}
"""


# ─── Stage 6: Prediction Register ───

PREDICTION_REGISTER_HEADER = """# Convergence Codex — Capstone Predictions Register

**Date:** {date}
**Author:** Mark E. Mala
**Pipeline:** Gnosis AI (discovery) → Logos AI (formalisation) → Synthesis AI (composition, capstone mode)
**Provenance:** Bitcoin-timestamped via OpenTimestamps on git repository

---

## Purpose

This document lists every falsifiable prediction made in the Capstone papers of the
Convergence Codex. Each prediction is independently verifiable. If ANY prediction in
this register is confirmed by future experimental or theoretical work, the Bitcoin
timestamp on this document establishes unambiguous priority.

## How to Verify Priority

1. Check the git commit hash for this file
2. Verify the OpenTimestamps proof against the Bitcoin blockchain
3. The block height and timestamp establish that these predictions existed at that time

---

## Predictions

"""
