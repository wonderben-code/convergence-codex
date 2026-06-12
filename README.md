# The Convergence Codex

**An open, exploratory mapping of cross-domain structural relationships across science, mathematics, and physics — discovered with custom AI, formalised in Lean 4, and timestamped for provenance.**

This is independent, AI-collaborative research, not peer-reviewed. Some of it is genuine structural discovery; some is preliminary or wrong. Everything is open and Bitcoin-timestamped so it can be checked. Read it in that light.

---

## What This Is

Custom-built AI components form a research pipeline:

- **Gnosis** — discovers structural convergences across scientific fields ([its own repo](https://github.com/wonderben-code/gnosis-ai)).
- **Logos** — attempts to formalise discoveries as Lean 4 / Mathlib proofs.
- **Synthesis** — *retired as an autonomous system.* Papers are now composed manually with Claude Code, because the higher-rigour writing benefits from a human in the loop.

Discoveries are validated, formalised where genuinely possible, published as papers on Zenodo, and mapped on an interactive website. Everything is Bitcoin-timestamped with cryptographic provenance.

**An honest note on the formalisation.** A May 2026 internal audit found that a large fraction of the Lean theorems were arithmetic proxies or type-level tautologies — they compiled with zero `sorry` but did not establish the physics their docstrings claimed. Around twenty files are the genuinely Mathlib-backed core; the rest is honest work-in-progress. See `lean_verify/MATHS_ORG_STATE.md` for the audited state. Claims throughout carry status tags (PROVED / PARTIAL / CLAIMED / PREDICTED / SPECULATIVE / DOWNSTREAM / META) so nothing has to be taken on trust.

## The Pipeline

```
Established Knowledge
        │
        ▼
   ┌─────────┐
   │  GNOSIS  │  Survey fields → find convergences → validate → meta-converge
   └────┬─────┘
        │ Structured discoveries (JSON)
        ▼
   ┌─────────┐
   │  LOGOS   │  Detect proof type → select apparatus → prove (Lean 4) → adversarial check
   └────┬─────┘
        │ Formal proofs (Lean 4 + natural language), with honest status tags
        ▼
   Manual composition (Claude Code) → Zenodo + Bitcoin timestamp
```

Each component is independently runnable, coordinated by a thin orchestrator with human-in-the-loop checkpoints.

## The Scope

The combinatorial design is exhaustive *within the set of fields surveyed* — not "all of science". As coverage grows toward dozens of fields:
- Cross-domain pairwise comparisons (cross-domain first)
- Multi-field groups (3+ fields simultaneously)
- Meta-convergence levels (combinatorial at each level)
- A recursive cascade toward fixed points

Compute runs on Claude (API or Claude Code Max-plan, ~$0 in the latter). Cost figures quoted in the papers are for the specific runs reported there, not for "all of science".

## Repository Structure

```
convergence-codex/
├── docs/           ← Architecture, the Tree of Reality spec, contributing guide
├── logos/          ← Logos (formaliser)
├── orchestrator/   ← pipeline orchestrator
├── lean_verify/    ← Lean 4 proofs + the audited integrity state
├── data/           ← outputs (convergences, proofs, paper drafts)
└── papers/         ← published papers
```

Gnosis lives in its own repo: [wonderben-code/gnosis-ai](https://github.com/wonderben-code/gnosis-ai).

## Status

Active, exploratory. Gnosis (v1 published; v2 cross-domain in development) and Logos are built; papers are published on Zenodo; the Lean codebase is partially genuine and honestly tagged (see the audit note above). This is a living research repository, not a finished product.

## Papers

Published on [Zenodo](https://zenodo.org), CERN's open-access repository, each with a permanent DOI and Bitcoin timestamp.

## Open Source

MIT License. Code, data, and papers are open. To audit a claim: find its node in the Tree of Reality, follow it to the Lean file, run `lake build`, watch it compile.

## Author

Mark E. Mala (pen name of Ekram Alam). Part of the [Infinitography](https://infinitography.com) research programme.
