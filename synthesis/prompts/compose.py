"""Paper composition prompts."""

SECTION_SYSTEM = (
    "You are Synthesis, a scientific paper composition AI for the Convergence Codex. "
    "Your papers are read by researchers across many fields — a topologist, a quantum "
    "physicist, a biologist, and a number theorist may all read the same paper. "
    "Write for this interdisciplinary audience: every domain-specific concept must be "
    "briefly explained when first introduced, every piece of mathematical notation must "
    "be accompanied by a plain-language interpretation, and every convergence must be "
    "explained in terms of what it means for EACH domain involved, not just stated. "
    "\n\n"
    "Quality bar: Nature / Science / PNAS. Clear, precise prose. No jargon without "
    "explanation. No hand-waving. Every claim must be traceable to specific evidence. "
    "Honest about confidence levels — never overstate. Each paper must be fully "
    "self-contained: a reader should not need to read any other Codex paper to "
    "understand this one. "
    "\n\n"
    "Voice: authoritative but not arrogant. The tone of a researcher presenting "
    "genuinely surprising findings with appropriate excitement AND appropriate caution. "
    "Never invent citations or claim more than the evidence supports. When a result is "
    "preliminary, say so clearly — but also explain why it is still worth reporting."
)

ABSTRACT_PROMPT = """Write the abstract for a paper with this content:

Title: {title}
Theme: {theme}
Key discoveries:
{discoveries_summary}

Key proofs:
{proofs_summary}

The abstract should be 200-300 words. It must:
1. Open with a sentence that ANY scientist can understand — the core insight in plain language
2. State what was discovered and across which domains (2-3 sentences)
3. State how it was formalised and what the formal result establishes (1-2 sentences)
4. State the significance — why should a researcher care? (1-2 sentences)
5. Close with an honest confidence statement (e.g. "supported at high confidence" or "preliminary but structurally robust")
6. A non-specialist should be able to read the abstract and understand the main contribution

Return the abstract text only, no JSON.
"""

INTRODUCTION_PROMPT = """Write the Introduction section for this paper.

Title: {title}
Abstract: {abstract}
Theme: {theme}

Discoveries covered:
{discoveries_text}

Corpus context (existing papers in the Convergence Codex):
{corpus_context}

The Introduction should:
1. Open with a motivating question or observation that connects to the reader's intuition — why might these domains be structurally related?
2. Define "cross-domain structural convergence" in plain language with a concrete analogy (e.g. how the same differential equation governs both predator-prey dynamics and chemical oscillations)
3. Briefly introduce EACH domain involved, assuming the reader is expert in at most one of them. A topologist needs a one-sentence primer on quantum decoherence; a physicist needs a one-sentence primer on category theory
4. Preview what this paper discovers, what it proves formally, and why it matters
5. Situate within the Convergence Codex corpus — what has been established before, what this paper adds
6. Be 500-800 words
7. The reader should finish the introduction thinking "I understand what they found, I understand why it matters, and I want to see the proof"

Return the section text only (markdown), no JSON.
"""

METHODS_PROMPT = """Write the Methods section for this paper.

This paper's discoveries were produced by:
- Gnosis AI (autonomous knowledge discovery system)
- Discovery method: {discovery_method}
- Validation: EA Engine (5-dimensional adversarial validation)
- Formalisation: Logos AI (formal mathematical proof generation)

Formalisation details:
{formalisation_details}

The Methods section should:
1. **Discovery pipeline**: Explain how Gnosis AI discovers convergences. The CI Engine surveys domains, extracts structural features, and performs pairwise comparison. The EA Engine then validates each candidate convergence across 5 dimensions:
   - Strength (how strong is the structural parallel?)
   - Independence (could this arise by coincidence?)
   - Adversarial (does the convergence survive deliberate attack?)
   - Reproducibility (would a different analysis find the same result?)
   - Depth-consistency (does the parallel hold at deeper levels of analysis?)
   Explain each dimension in one sentence so the reader understands the validation rigour.

2. **Formalisation pipeline**: Explain how Logos AI formalises discoveries: type detection (what kind of mathematical relationship is this?), apparatus selection (what mathematical tools are needed?), proof generation (natural language + Lean 4 where possible), and 5-layer validation (mechanical verification, adversarial review, internal consistency, cross-proof consistency, calibration).

3. **Honest methodology note**: This is an AI-driven pipeline. State this clearly. Explain what this means for reproducibility (fully deterministic given the same model and parameters) and what it means for trust (all reasoning logs and intermediate steps are preserved in the appendices for human audit).

4. Be 400-700 words

Return the section text only (markdown), no JSON.
"""

RESULTS_PROMPT = """Write the Results section for this paper.

The discoveries and their proofs:
{results_text}

The Results section should:
1. Present each convergence as a narrative, not a data dump. For each:
   a. State the convergence in plain language first — "We find that X in domain A shares the same formal structure as Y in domain B"
   b. Explain what this means for EACH domain — why is this interesting to a specialist in domain A? Why to a specialist in domain B?
   c. Present the formal proof — state the proposition, walk through the key proof steps in natural language, then reference the formal notation
   d. Interpret the confidence score — don't just say "0.74", say "supported at moderate-to-high confidence (0.74), with the strongest signal in structural independence (0.82) and the weakest in reproducibility (0.59), suggesting the result is robust but would benefit from independent verification"
   e. State the verification status honestly
2. Use mathematical notation where appropriate (LaTeX-compatible), but ALWAYS accompany it with a plain-language interpretation on the same line or immediately after
3. Present results in a logical order — either strongest first, or thematically grouped if there is a natural narrative arc
4. If multiple convergences share a theme, draw that connection explicitly
5. Be {target_words} words

Return the section text only (markdown), no JSON.
"""

DISCUSSION_PROMPT = """Write the Discussion section for this paper.

Title: {title}
Results summary:
{results_summary}

Key themes: {themes}

The Discussion should:
1. **What do these convergences mean?** — Not just "we found structural parallels" but WHY might these domains share this structure? Is there a deeper organising principle? Or is it a mathematical coincidence (the same equation can describe unrelated phenomena)?
2. **Implications for each domain** — What does a topologist learn from knowing their structure appears in quantum mechanics? What does a biologist gain from a formal proof that their population dynamics mirror thermodynamic phase transitions? Be specific and concrete.
3. **The broader pattern** — If multiple convergences in this paper point to the same underlying structure, name it. If they don't, say that too.
4. **Connection to existing literature** — Where do these results connect to known mathematical unification efforts (e.g. category theory as a unifying language, renormalisation group universality, topological data analysis)?
5. **Open questions** — What would it take to move these from "structural convergence" to "proven deep connection"? What experiments or proofs would confirm or refute the deeper claim?
6. **What this does NOT mean** — Explicitly guard against over-interpretation. A structural parallel between two domains does not mean they are "the same thing."
7. Be 500-900 words

Return the section text only (markdown), no JSON.
"""

NOVEL_CONTRIBUTIONS_PROMPT = """Write the Novel Contributions section for this paper.

Title: {title}

Convergences discovered and formalised in this paper:
{convergences_text}

Existing Codex corpus context:
{corpus_context}

This section establishes scientific priority. It is the timestamped, permanent record
of what this paper contributes that did not exist before. Write it for a patent examiner,
a grant reviewer, and a historian of science.

The Novel Contributions section MUST:
1. **Numbered list of novel contributions** — Each contribution is one specific claim.
   Format each as:
   "**N.** To the authors' knowledge, [specific structural convergence / formal result]
   has not been previously identified or formalised in the literature."
   Be precise — name the domains, the structure, and the formal result.

2. **Distinguish discovery from formalisation** — Some contributions are the discovery
   itself (Gnosis AI identified this convergence), others are the formalisation
   (Logos AI proved it formally). State which is which.

3. **Note any partial precedents** — If a convergence is related to known work (e.g.
   "the connection between X and Y has been noted informally by [Author, Year], but
   no formal proof existed"), state this. DO NOT claim novelty for something that is
   well-known — only for the SPECIFIC formal result or newly-identified structural parallel.

4. **State the provenance** — "All contributions in this paper were discovered by
   Gnosis AI and formalised by Logos AI as part of the Convergence Codex project.
   Priority is established via Bitcoin timestamping of the GitHub repository
   (commit hash and OpenTimestamps proof)."

5. Be 200-500 words depending on number of convergences.

Return the section text only (markdown), no JSON.
"""

HONEST_SCOPE_PROMPT = """Write the Honest Scope section for this paper.

This is a REQUIRED section in every Convergence Codex paper. It is the most important
section for scientific integrity. Write it as if a sceptical reviewer is reading it.

Results and their confidence:
{results_confidence}

Known limitations:
{limitations}

Proof verification status:
{verification_status}

The Honest Scope section MUST:
1. **What IS established** — List each result with its confidence level, stated plainly. e.g. "Convergence C1 between topology and quantum mechanics is supported at high confidence (0.84). The formal proof is logically sound and has been adversarially tested."
2. **What is NOT established** — Be specific. e.g. "This paper does NOT prove that topology and quantum mechanics share a common foundation. It proves that a specific structural parallel exists and can be formally stated. The deeper causal question remains open."
3. **Methodology limitations** — This is an AI-driven discovery pipeline. State clearly:
   - The pipeline can find structural parallels that a human might miss, but it can also find spurious patterns
   - Natural-language proofs have been adversarially reviewed but NOT independently verified by human mathematicians (unless machine-verified via Lean 4 — state which proofs have been)
   - Confidence scores are calibrated against the pipeline's own standards, not against an external benchmark
4. **What would change our conclusions** — What kind of evidence would strengthen or weaken these results?
5. Be 300-500 words
6. The reader should finish this section thinking "these authors are being completely honest with me"

Return the section text only (markdown), no JSON.
"""

CONCLUSION_PROMPT = """Write the Conclusion for this paper.

Title: {title}
Key results:
{key_results}

The Conclusion should:
1. Restate the main contribution in one clear sentence that a non-specialist can understand
2. State what is now formally established that was not before
3. State the most important implication for each domain involved
4. Point to the most promising direction for future work — be specific (not "further research is needed" but "a Lean 4 formalisation of Theorem 2 would elevate this from natural-language proof to machine-verified result")
5. End with a sentence that captures WHY this matters — the vision, not just the result
6. Be 200-350 words

Return the section text only (markdown), no JSON.
"""

REFERENCES_PROMPT = """Generate the References section for this paper.

Citations used in the paper:
{citations_used}

Requirements:
1. Format as a numbered markdown list
2. Include ALL cited works
3. Use format: [N] Authors, "Title," Venue, Year. DOI/URL if available.
4. Corpus papers use format: [N] M. E. Mala, "Title," Convergence Codex, Year. DOI.
5. Do NOT invent citations — only include works actually cited

Return the references as a markdown numbered list, no JSON.
"""
