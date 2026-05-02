# The Convergence Codex — Build Roadmap

**Last updated:** 2 May 2026

This is the build roadmap for the Convergence Codex. For the full architecture, see `ARCHITECTURE.md`.

---

## Build Order

| Step | What | Status | Depends On |
|------|------|--------|------------|
| 1 | Gnosis v2 upgrade | NOT STARTED | — |
| 2 | Logos AI build | NOT STARTED | — |
| 3 | Synthesis AI build | NOT STARTED | — |
| 4 | Pipeline Orchestrator | NOT STARTED | 1, 2, 3 |
| 5 | Stage A (pipeline validation) | NOT STARTED | 4 |
| 6 | Stage B (the full Codex) | NOT STARTED | 5 |
| 7 | Website wing | NOT STARTED | 6 |
| 8 | QC + stamp + ship | NOT STARTED | 7 |

Steps 1-3 have no dependencies on each other (Gnosis, Logos, Synthesis are independent). But Gnosis v2 is recommended first because it's the most complex and informs the data formats that Logos consumes.

---

## Step 1: Gnosis v2

See `GNOSIS_V2_SPEC.md` for full specification.

Key deliverables:
- [ ] Unified comparison engine (any field set, any category)
- [ ] Cross-category Auto mode
- [ ] Multi-field comparison (3+ fields)
- [ ] Search strategy engine (7 strategies)
- [ ] Convergence corpus manager
- [ ] Recursive cascade engine (cross-run, cross-level)
- [ ] Expanded taxonomy (70-100+ fields)
- [ ] Backward-compatible with v1
- [ ] Paper on Zenodo describing v2
- [ ] Bitcoin-stamped

## Step 2: Logos AI

See `LOGOS_SYNTHESIS_SPEC.md` sections 2 + 4 for full specification.

Key deliverables:
- [ ] Auto-detect formalisation type
- [ ] Auto-select mathematical apparatus
- [ ] Lean 4 + Mathlib proofs where possible
- [ ] Natural-language formal proofs where not
- [ ] 5-layer adversarial validation
- [ ] Honest flagging for ambitious cases
- [ ] Human-in-the-loop checkpoints
- [ ] Open source on GitHub (MIT)
- [ ] Paper on Zenodo
- [ ] Bitcoin-stamped

## Step 3: Synthesis AI

See `LOGOS_SYNTHESIS_SPEC.md` sections 3 + 4 for full specification.

Key deliverables:
- [ ] Auto-detect paper boundaries
- [ ] Corpus voice consistency
- [ ] Publication-quality Markdown drafts
- [ ] Rigorous citations
- [ ] Epistemic accuracy
- [ ] Human-in-the-loop (no auto-publish)
- [ ] Open source on GitHub (MIT)
- [ ] Paper on Zenodo
- [ ] Bitcoin-stamped

## Step 4: Pipeline Orchestrator

Key deliverables:
- [ ] Gnosis v2 → Logos → Synthesis end-to-end coordination
- [ ] Standardised JSON data formats documented
- [ ] Human-review checkpoints configurable
- [ ] Each AI independently runnable
- [ ] End-to-end provenance chain

## Step 5: Stage A — Pipeline Validation

- [ ] Feed existing 266 convergences through Logos → Synthesis
- [ ] Test Gnosis v2 on ~10 cross-category pairs + 1-2 triplets
- [ ] Run those through Logos → Synthesis
- [ ] Human review all output
- [ ] Publish papers on Zenodo
- [ ] Bitcoin-stamp everything
- [ ] Assess pipeline quality and adjust before Stage B

## Step 6: Stage B — The Full Codex

- [ ] Phase 1: All pairwise (cross-category first)
- [ ] Phase 2: Codex Analysis (fingerprints, clustering, transitivity, hubs)
- [ ] Phase 3: Multi-field on promising groups
- [ ] Phase 4: Level 2 meta-convergences (multiple groupings)
- [ ] Phase 5: Level 3+ recursive cascade
- [ ] Phase 6: All through Logos → Synthesis → papers → Zenodo
- [ ] Bitcoin-stamp everything

## Step 7: Website Wing

- [ ] New wing on infinitography.com
- [ ] Three AIs + pipeline introduction
- [ ] Interactive discovery explorer (every level)
- [ ] All papers with DOIs
- [ ] Novel contributions catalogue

## Step 8: QC + Ship

- [ ] Full website playtest
- [ ] Content accuracy check
- [ ] Accessibility pass
- [ ] Bitcoin-stamp final state
- [ ] Deploy
