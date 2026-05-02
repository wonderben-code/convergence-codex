"""Paper composition prompts."""

SECTION_SYSTEM = (
    "You are Synthesis, a scientific paper composition AI for the Convergence Codex. "
    "You write in the precise, structured style of the existing corpus: careful, "
    "honest about limitations, with specific section conventions. "
    "You never invent citations or claim more than the evidence supports."
)

ABSTRACT_PROMPT = """Write the abstract for a paper with this content:

Title: {title}
Theme: {theme}
Key discoveries:
{discoveries_summary}

Key proofs:
{proofs_summary}

The abstract should be 150-250 words. It must:
1. State what was discovered (1-2 sentences)
2. State how it was formalised (1 sentence)
3. State the significance (1-2 sentences)
4. Be honest about confidence levels

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
1. Situate the contribution within the Convergence Codex corpus
2. Explain what cross-domain convergences are and why they matter
3. Briefly preview what this paper discovers and proves
4. Be 300-600 words
5. Reference relevant prior Codex papers where appropriate

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
1. Describe how Gnosis discovers convergences (CI Engine + EA Engine)
2. Describe how Logos formalises them (type detection → apparatus selection → proof)
3. Describe the validation pipeline (5 layers)
4. Be honest about the AI-driven methodology
5. Be 200-500 words

Return the section text only (markdown), no JSON.
"""

RESULTS_PROMPT = """Write the Results section for this paper.

The discoveries and their proofs:
{results_text}

The Results section should:
1. Present each convergence with its formal proof
2. Include confidence scores and verification status
3. Use mathematical notation where appropriate (LaTeX-compatible)
4. Present results in a logical order (strongest first, or thematically grouped)
5. Be {target_words} words

Return the section text only (markdown), no JSON.
"""

DISCUSSION_PROMPT = """Write the Discussion section for this paper.

Title: {title}
Results summary:
{results_summary}

Key themes: {themes}

The Discussion should:
1. Interpret what the convergences mean
2. Connect to broader scientific context
3. Identify implications for the fields involved
4. Identify open questions raised by the results
5. Be 300-600 words

Return the section text only (markdown), no JSON.
"""

HONEST_SCOPE_PROMPT = """Write the Honest Scope section for this paper.

This is a REQUIRED section in every Convergence Codex paper. It lists what the paper
does and does not establish, with complete honesty.

Results and their confidence:
{results_confidence}

Known limitations:
{limitations}

Proof verification status:
{verification_status}

The Honest Scope section should:
1. State clearly what IS established (with confidence levels)
2. State clearly what is NOT established
3. Acknowledge the AI-driven methodology and its limitations
4. Acknowledge where proofs are natural-language only (not machine-verified)
5. Be 200-400 words

Return the section text only (markdown), no JSON.
"""

CONCLUSION_PROMPT = """Write the Conclusion for this paper.

Title: {title}
Key results:
{key_results}

The Conclusion should:
1. Restate the main contribution (1-2 sentences)
2. Note the significance (1 sentence)
3. Point to future work (1-2 sentences)
4. Be 100-200 words

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
