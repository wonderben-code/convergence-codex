# Master Roadmap — All Projects

**Creator:** Mark E. Mala (Ekram Alam)
**Last updated:** 3 May 2026 (capstone quality + catalogue strategy)
**This is THE canonical roadmap. One file. All projects. Always consult this first.**

---

## Overview

| Project | What It Is | Website | Status |
|---------|-----------|---------|--------|
| **AgentCiv** | Collective Machine Intelligence — AI civilisations, engine, creator mode | agentciv.ai | Stage 2 ~70% done |
| **Infinitography** | Research programme on the nature of reality | infinitography.com | All papers done, website Wings 1-4 remaining |
| **Gnosis AI** | Autonomous knowledge discovery product | on infinitography.com | v1 built, all papers published (G16-G19 + 3 synthesis) |
| **Exponential Atlas** | Interactive model of cross-domain tech acceleration | not deployed | Blocked on integrity audit |

**Repos (7 total):**
- `agent-civilisation` — sim (PUBLIC, PyPI: agentciv-sim)
- `agentciv-engine` — engine (PUBLIC, PyPI: agentciv-engine)
- `agentciv-creator` — creator mode (PUBLIC, PyPI: agentciv-creator)
- `agentciv-colony` — Colony + RCI papers (PRIVATE)
- `wonderben-code/infinitography-website` — infinitography.com (PRIVATE)
- `wonderben-code/gnosis-ai` — Gnosis AI product (MIT)
- `wonderben-code/convergence-codex` — The Convergence Codex: Logos, Synthesis, orchestrator, data (PUBLIC, MIT)

**Published:** 43 papers on Zenodo with DOIs. All Bitcoin-timestamped. (35 original + 8 Stage A Capstone)

---

## THE 9 STAGES

### Stage 1: IP Provenance Stamping — COMPLETE
All 6 repos Bitcoin-timestamped. Auto-stamp hooks installed. Colony + Gnosis papers stamped.

### Stage 1b: Academic Preprint Publication — COMPLETE
All 34 papers on Zenodo with DOIs. ORCID: 0009-0007-8760-5553. arXiv deferred (needs Jack's cs.AI endorsement). Language audit done. Paper dates specified.

---

### Stage 2: Creator Mode — 70% DONE

| Step | Task | Status |
|------|------|--------|
| 1 | Build Plan | DONE |
| 2 | Build (Phases 1-5, ~1,400 lines) | DONE |
| 3 | Push + Stamp + PyPI (agentciv-creator v0.1.0) | DONE |
| 4 | Website Creator Mode Wing (10 sections) | DONE (agentciv.ai/creator) |
| 4a | Science page: add Creator Mode papers | NOT DONE |
| 4b | Anthropic-style paper pages for ALL AgentCiv papers | NOT DONE |
| 4c | Homepage: Creator Mode reference | NOT DONE |
| 5 | Deploy | DONE |
| **6** | **Dogfood Validation ($20-40)** — real campaigns | **NOT DONE** |
| **7** | **Update Papers 5+6 → Zenodo v2 → stamp** | **NOT DONE** |

**Content workflow:** Same as Infinitography — user creates ALL paper page content via consumer Claude web app by reading actual AgentCiv papers, then shares for implementation. Do NOT generate page content independently. AgentCiv has 12 papers (Papers 1-12).

---

### Stage 3: Infinitography + Gnosis AI — IN PROGRESS

#### Gnosis AI v1 — COMPLETE
- Built: CI Engine + EA Engine, 3 modes, 52-field taxonomy, CLI
- Results: 266 convergences, 26 meta-findings, 4 terminal fixed points, $28.99
- Paper 16 published (DOI: 10.5281/zenodo.19617859)
- GitHub repo public (MIT), README + LICENSE added, CWD bug fixed, API key validation added

#### Infinitography Website (infinitography.com)

| Task | Status |
|------|--------|
| Website built + deployed on Netlify | DONE |
| 6-tier quality upgrade | DONE |
| Papers 5-15 rewritten from source papers | DONE (17 Apr) |
| Jargon removal pass (all 15 papers) | DONE (17 Apr) |
| Discovery landing page rewritten | DONE (17 Apr) |
| Theory of Everything page rewritten (Generator Thesis, progressive disclosure) | DONE (17 Apr) |
| Paper 15 falsifiability framing fixed | DONE (17 Apr) |
| **Wing 1 (Discovery) — ALL 22 paper pages from fresh** | **NOT DONE** |
| **Wing 2 (ToE) — landing page from ToE papers** | **NOT DONE** |
| **Wing 3 (Discoveries + New Fields) — extract from all 22 papers** | **NOT DONE** |
| **Wing 4 (Gnosis) — landing page + discovery explorer** | **DONE** (29 Apr) |
| **QC Pass (all 4 wings)** | **NOT DONE** |
| **Paper 12 upgrade (Subsequent Advancements → Zenodo v2)** | **NOT DONE** |

**Content workflow:** User creates ALL content via consumer Claude web app by reading actual papers, then shares for implementation. Do NOT generate page content independently. Existing paper pages (5-15) kept for reference only — all 22 pages recreated from scratch.

**The 22 papers:** Papers 1-15 (Infinitography) + G16-G19 (Gnosis AI) + 3 synthesis papers (A, B, C). No AgentCiv papers on infinitography.com.

**Wing definitions:**
- Wing 1 (Discovery) = The full research programme: 22 Anthropic-style paper pages + landing page
- Wing 2 (ToE) = Landing page built from ToE-relevant papers (7, 12-15, synthesis), links to paper pages
- Wing 3 (Discoveries + New Fields) = Every discovery made + every new field coined across all 22 papers
- Wing 4 (Gnosis) = The AI tool: open source, features, architecture, discoveries from test runs

#### Gnosis AI Research Programme

| Step | Task | Est. Cost | Status |
|------|------|-----------|--------|
| 6b | Paper 16 final proofread | $0 | NOT DONE |
| 7 | Papers 17-19 (Physics, Maths, Fixed Points) | $0 | **DONE** (18 Apr) |
| 7b | 3 new papers (replacing Checkpoint Alpha) — publish to Zenodo + add to gnosis-ai repo | $0 | **DONE** (27 Apr) |
| 8 | v1.1 improvements (depth scoring, parallel, resume) | $0 | NOT DONE |
| 8b | Playtest + UX/UI overhaul (pip install, Rich CLI) | $0 | PARTIAL (API key validation + CWD fix done, rest NOT DONE) |
| 9 | Gnosis landing page (11 sections, "Why This Matters", honest status) | $0 | **DONE** (29 Apr) |
| 10 | Gnosis paper pages (Anthropic-style, Papers G16+) | $0 | NOT DONE |
| 11 | "Suggested Future Runs" section on website | $0 | **DONE** (29 Apr, in landing page "What's Next" + suggested explorations) |
| 12 | Discovery catalogue (browsable, filterable, searchable) | $0 | **DONE** (29 Apr, /gnosis/discoveries catalogue view) |
| 13 | Discovery explorer (cascade view, domain map, full hierarchy) | $0 | **DONE** (29 Apr, /gnosis/discoveries with 3 views) |
| 14 | Final QC + ship | $0 | **DONE** (29 Apr, all numbers verified, deployed live) |

#### Checkpoint Alpha — SCRAPPED → 3 New Papers — COMPLETE

Original plan was a single "Theory vs Evidence" paper. Replaced by 3 new synthesis papers, all published 27 April 2026:
- **Paper A:** The Structural Character of Reality (DOI: 10.5281/zenodo.19829108)
- **Paper B:** The Generator Theory of Everything (DOI: 10.5281/zenodo.19829195)
- **Paper C:** A New Mathematics for Reality and the Multi-Angled Theory of Everything (DOI: 10.5281/zenodo.19829201)

All added to gnosis-ai repo, Bitcoin-timestamped, and published on Zenodo.

---

#### CHECKPOINT OMEGA — SUPERSEDED BY CONVERGENCE CODEX

Original idea was a "potential future use" of Gnosis AI. Now realised as Stage 3b: The Convergence Codex.

---

### Stage 3b: THE CONVERGENCE CODEX — IN PROGRESS

**Repo:** `wonderben-code/convergence-codex` (PUBLIC, MIT, Bitcoin-timestamped)
**Full architecture:** `convergence-codex/docs/ARCHITECTURE.md` ← THE CANONICAL DOC
**Local:** `/Users/ekramalam/convergence-codex/`

The world's first and largest systematic mapping of cross-domain structural relationships across established science, mathematics, and physics. Three custom AIs form a pipeline: **Gnosis** (discovery) → **Logos** (formalisation) → **Synthesis** (communication).

#### The Multi-Level Recursive Architecture

Not just pairwise comparisons — combinatorial at EVERY level:

**Level 1: ALL field convergences**
- Within-category pairs (~225, 7% of space)
- Cross-category pairs (~2,935, 93% — THIS IS WHERE THE SERIOUS DISCOVERIES ARE)
- Multi-field groups (3+ fields simultaneously, gated by pairwise results)

**Level 2: Meta-convergences (combinatorial across groupings)**
- Multiple grouping strategies on Level 1 output
- Pairwise comparison of convergences themselves
- Cross-level comparisons (Level 1 ↔ Level 2)

**Level 3+: Recursive cascade to fixed points**
- Same combinatorial process applied recursively
- Continue until fixed points or diminishing returns

#### Build Order (11 Nobel-clearing checkpoints)

| Step | What | Status |
|------|------|--------|
| 1 | **Gnosis v2** — cross-domain, multi-field, recursive cascade, 81 fields | **DONE** |
| 2 | **Logos AI** — 2,162 lines, 14 files, Lean 4 formalisation, 5-layer adversarial validation | **DONE** |
| 3 | **Synthesis AI** — 1,448 lines, 11 files, publication-quality paper generation | **RETIRED** (see note below) |
| 4 | **Pipeline Orchestrator** — 479 lines, 3 files, thin coordination, human checkpoints | **DONE** |
| 5 | **Stage A** — 266 existing convergences through Logos | **DONE** (256/266 proofs, 2 May) |
| 5c | **Stage A CAPSTONE** — 22 papers across all cascade levels (L5→L1). Genuine ontological claims about reality, precisely scoped, with predictions extending into untested domains. **Papers composed manually with AI (Claude Code) — NOT Synthesis AI.** Each paper individually proofread to top 0.00001% quality. | **8/22 DONE** (2 May) |
| 5c-i | Clean up 8 completed capstone papers for Zenodo publication | **DONE** (fixed fake IDs, DOIs, headers) |
| 5c-ii | Publish 8 capstone papers to Zenodo with DOIs (v2 with PDFs) | **DONE** (3 May) |
| 5c-0 | **PAPER QUALITY BIBLE** — Write the definitive reference document for capstone paper quality. **The standard: if the claim is later proven correct, a Nobel committee reading this paper would unambiguously establish priority — the paper alone proves we had the discovery first.** Covers: paper structure (exact sections + requirements), mathematical standards (formalisations written out in full, LaTeX, theorem formatting), evidence standards (cite by domain pair not hex ID, honest confidence), prediction format (specific enough that confirmation can only come from this theory), provenance (SHA-256, Bitcoin timestamp, irrefutable proof-of-existence), reference format (no fake DOIs), anti-drift rules, prose standards (standalone scientific paper any physicist could evaluate), honest limitations, 20+ point final checklist. Every paper measured against this before publication. Saved at `convergence-codex/docs/PAPER_QUALITY_BIBLE.md`. | **FIRST** |
| 5c-v | **PROOFREAD all 8 capstone papers to top 0.00001% quality** — Using the Paper Quality Bible. Remove all inline hex IDs, write actual formalisation mathematics, fix fake Codex DOIs, ensure standalone publishable quality. One-by-one manual review with AI. | **NEXT** |
| 5c-vi | Publish v3 of 8 proofread capstone papers to Zenodo | NOT DONE |
| 5c-iii | Compose remaining 14 capstone papers manually with AI (Claude Code) — use cached claims + plans, write each paper directly with actual formalisation mathematics, no Synthesis AI | NOT DONE |
| 5c-iv | Proofread + publish remaining 14 capstone papers to Zenodo | NOT DONE |
| 5d | **Stage A FORMALISATION CATALOGUE** — Instead of ~70 individual papers, create ONE comprehensive catalogue document listing ALL 256 formalisations with their mathematical propositions, proof sketches, confidence scores, adversarial verdicts, and domain pairs. Published as a single Zenodo deposit. Much more useful as a reference work than hundreds of thin papers. AI-composed (no API cost). | NOT DONE |
| 6 | **Stage B — THE BIG RUN** — Full Codex across ALL 81 fields of science, maths, physics (6 phases): all pairwise convergences (cross-category first), codex analysis, multi-field groups, meta-convergences, recursive cascade to fixed points, everything through Logos (NOT Synthesis). 10x more data than Stage A. | NOT DONE |
| 6c | **Stage B CAPSTONE** — Capstone papers from the broader Stage B dataset, composed manually with AI (Claude Code). Each paper individually proofread. Do Stage A claims hold? Strengthen? New ones emerge? | NOT DONE |
| 6d | **Stage B FORMALISATION CATALOGUE** — Same as Stage A: ONE comprehensive catalogue of all new formalisations from the 81-field run, not hundreds of individual papers. AI-composed (no API cost). | NOT DONE |
| 7 | **Stage C — THE CROWN JEWELS** — The capstone of capstones. From ALL of Stage A + B, identify the 3-5 MOST terminal, MOST unifying, MOST revolutionary claims — the absolute top of the cascade. These are the claims that, if correct, would each individually transform our understanding of reality. Write the definitive, focused papers for each. Not broad surveys — laser-focused on the single most powerful version of each claim. | NOT DONE |
| 7b | **Stage C PUBLICATION** — 3-5 crown jewel papers → Zenodo. These are THE papers. | NOT DONE |
| 8 | **Stage D — HARDEN** — Take Stage C's 3-5 crown jewel claims and make them airtight. Formal mathematical proofs (Lean 4 where possible), exhaustive prediction derivation, detailed experimental proposals, address every possible objection. Close every gap the adversarial review identified. The goal: if a physicist reads this paper, they cannot find a flaw — only test it. | NOT DONE |
| 8b | **Stage D PUBLICATION** — Publish hardened crown jewel papers as **v2 of the Stage C papers on Zenodo** (same records, new version with formal proofs + predictions added). Pre-registration prediction papers Bitcoin-stamped BEFORE any confirmation. | NOT DONE |
| 9 | **Stage E — THE GRAND FINALE** — Synthesise EVERYTHING from Stages A through D into one paper. Validate, strengthen, or upgrade the existing Theory of Everything (Paper 15) using the full Codex evidence base. This is where 266+ convergences, thousands of formal conjectures, the cascade structure, the fixed points, the crown jewel claims, and the hardened proofs all converge into a single unified proposal. THE Nobel paper. | NOT DONE |
| 9b | **Stage E PUBLICATION** — THE capstone paper: the updated, evidence-backed Theory of Everything → Zenodo | NOT DONE |
| 10 | **Website wing** — Convergence Codex on infinitography.com | NOT DONE |
| 11 | **QC + stamp + ship** | NOT DONE |
| 12 | **Open Source + Production Grade** — Release **Gnosis AI + Logos AI only** (NOT Synthesis). Make both AIs production-ready: PyPI packages, `pyproject.toml`, CLI entry points, config file system (no hardcoded paths), comprehensive README with quickstart, example data for dry runs without API credits, CI/CD (tests + linting), Docker option, framing audit, license decision (MIT/Apache 2.0). **Dual-mode backend: `--max-plan` flag uses Claude Code CLI (free via Max plan subscription) alongside standard API mode.** World-class dev tool UI/UX polish (rich output, progress bars, clear error messages, beautiful CLI experience). Goal: a researcher anywhere can `pip install` and run Gnosis + Logos on their own domains. | NOT DONE |

**Strategy pivot (3 May 2026) — Synthesis AI RETIRED from workflow:**
- **Problem:** Synthesis AI ($60-120 per run) produced papers with raw database hex IDs in body text, fake DOIs, missing actual mathematics, duplicate headers, and fabricated convergence IDs. Every run required extensive manual cleanup that cost more time than writing from scratch.
- **Solution:** All papers now composed manually with AI (Claude Code) — no API cost, better quality, actual formalisation mathematics included. Synthesis AI code remains in repo for reference but is NOT used and NOT included in open source release.
- **What we release open source:** Gnosis AI (discovery) + Logos AI (formalisation) only. These are the two engines that actually work well. Researchers run Gnosis + Logos on their own domains, then write their own papers from the structured output.
- **Formalisation Catalogues:** Instead of 300-500+ individual papers, publish ONE comprehensive catalogue per stage. Much more useful as a reference work.
- **Net effect:** ~40-50 high-quality papers + 2 comprehensive catalogues instead of hundreds of thin AI-generated papers with errors. Better science, zero API cost for paper composition.

**MaxPlanAPI (3 May 2026) — $0 cost backend for Gnosis + Logos:**
- Both Gnosis AI and Logos AI now support `--max-plan` flag: runs queries via Claude Code CLI (`claude -p`) using Max plan subscription instead of Anthropic API.
- Drop-in replacement: same interface (`query`, `query_json`, `query_deep`, `query_deep_json`), same retry logic, same model selection.
- API mode kept for open source users who don't have Max plan. Dual mode: `--max-plan` for us, default API for everyone else.
- Stage B can now run entirely free (previously estimated $3,500-6,000 in API costs).

**Stage B Phases:**
1. All pairwise (cross-category FIRST)
2. Codex Analysis (fingerprints, clustering, transitivity, hubs)
3. Multi-field on promising groups (cross-category first)
4. Level 2 meta-convergences (multiple groupings, combinatorial)
5. Level 3+ recursive cascade
6. Everything through Logos → Synthesis

**Estimated total cost (all stages): ~$3,500-6,000**

#### Repos

| Repo | What |
|------|------|
| `wonderben-code/gnosis-ai` | Gnosis AI (v2 upgrade in place) |
| `wonderben-code/convergence-codex` | Logos, Synthesis, Orchestrator, Codex data, papers, docs |
| `wonderben-code/infinitography-website` | Website (includes Codex wing) |

---

### Stage 3c: Pansophia Wing — NOT STARTED

After the Convergence Codex is complete, add a Pansophia wing to infinitography.com.

**Paper:** "Pansophia: A Theoretical Architecture for Autonomous Knowledge Integration at Civilisational Scale"
**Zenodo:** https://zenodo.org/records/19974680 (DOI: 10.5281/zenodo.19974680)
**Bitcoin-stamped:** 2 May 2026 (in convergence-codex repo)

| Task | Status |
|------|--------|
| Paper written + published on Zenodo | DONE |
| Add `/pansophia` wing to infinitography.com | NOT DONE |
| Landing page explaining the architecture in plain language | NOT DONE |
| Link to Zenodo paper | NOT DONE |

**Wing concept:** "Pansophia: An AI Architecture at Civilisational Scale" — a single landing page explaining the 4-component architecture (Gnosis + Logos + Synthesis + Praxis + meta-layer) and its 6 defining features, with a link to the full paper on Zenodo.

---

### Stage 3d: Remaining Infinitography Website — NOT STARTED

These were originally part of Stage 3 but should happen AFTER the Codex and Pansophia (so homepage, playtest, etc. can reference everything).

| Task | Status |
|------|--------|
| Wing 2 (ToE) — DONE (2 May, built from proposal doc) | DONE |
| Papers 1-4 rewrite (user creates content via consumer Claude) | NOT DONE |
| Homepage content update (Landing.tsx, including Codex references) | NOT DONE |
| Full website playtest (all wings including Codex wing) | NOT DONE |
| QC Pass all wings | NOT DONE |
| Paper 12 upgrade (Subsequent Advancements → Zenodo v2) | NOT DONE |

---

### Stage 4: Polish Both Projects — NOT STARTED

**AgentCiv:**
- 9 NotebookLM podcasts
- Disclaimers page
- Professional email (agentciv.ai)
- Homepage quote update
- Repo cleanup + consistent READMEs
- Copy audit (every claim verified)
- Add Infinitography section to agentciv.ai

**Infinitography/Gnosis:**
- Copy audit
- Repo cleanup
- File "Gnosis AI" trademark (Nice Class 9 + 42) — MUST be before outreach
- Website refinements

---

### Stage 5: QA/QC — Pre-Outreach Audit — NOT STARTED

**5A. Papers:**
- Final version sync (GitHub vs Zenodo vs arXiv)
- LaTeX formatting (all 34 papers — fixes Unicode in current PDFs)
- Re-upload to Zenodo as v2 (LaTeX PDFs)
- arXiv submission (all 34, needs Jack's endorsement)
- Cross-reference DOIs in paper text
- Zenodo metadata polish

**5B. Websites:**
- Science page upgrade (provenance section + per-paper links)
- Homepage credibility (arXiv + Zenodo logos)
- **CLARITY PASS — BOTH WEBSITES** (7 layers: jargon audit, 10-second test, sentence rewriting, assumed knowledge, consistent vocabulary, explanation hierarchy, every surface)
- Full 10-layer QA audit — AgentCiv
- Full 10-layer QA audit — Infinitography
- Disclaimers pages — both sites

**5B-extra. Software Playtest:**
- agentciv-creator: pip install → real campaigns
- agentciv-engine: pip install → all presets, Max Plan + API
- agentciv-sim: pip install → configs, chronicler
- **Convergence Codex AIs:** Basic playtest (does `python3 scripts/run_stage_a.py --help` work from clean clone?). Full production-grade packaging is Step 12 in the Convergence Codex roadmap.

**5C. Repo + Infrastructure:**
- ORCID populated with all DOIs
- OTS upgrade verification (all stamps finalized)
- Repo hygiene (remove internal docs from public repos)
- README quality pass

**5D. Decisions:**
- Colony + Gnosis repo visibility (public before outreach?)
- Paper 3 figures (references fig1-fig8 that don't exist)
- **Capstone AI framing** — public repo contains "Nobel-grade" language in prompts/code. QC must ensure this is framed properly: papers written in the FORMAT of landmark scientific papers (Einstein, Dirac, Higgs model — genuine claims about reality with precise scoping and falsifiable predictions), NOT "AI that wins Nobel Prizes." The quality standard is clear; the branding should be about the scientific rigour, not the prize.

**5E. Outreach Prep:**
- AgentCiv outreach email (full rewrite from v0.1)
- Infinitography outreach email (separate, philosophy/physics audience)
- AgentCiv target list (70+ people)
- Infinitography target list (200+ people, Dana Scott priority)

---

### Stage 6: Outreach — NOT STARTED

- **6a. AgentCiv** — AI researchers, MAS labs, frontier labs, 70+
- **6b. Infinitography/Gnosis** — mathematicians, physicists, philosophers, 200+
- **6c. Combined narrative** — for people spanning both
- **6d. Logistics** — tracking, disclaimers, follow-ups

---

### Stage 7: Recursive Configuration Loop — NOT STARTED

- Build Engine ↔ Simulation self-improving loop
- Run experiments: does the loop converge?
- Update Papers 8+9 with empirical results → Zenodo v2
- Own wing on agentciv.ai

### Stage 8: The Colony — NOT STARTED

- Architecture design (queen function, stigmergic memory, Alam's Razor)
- Build Colony product
- Commercial license (open research, commercial usage)
- Website Colony wing
- Stamp and deploy

### Stage 9: The Full Stack

| Product | Level | License |
|---------|-------|---------|
| agentciv-sim | Base (civilisation substrate) | MIT |
| agentciv-engine | Base (task substrate) | MIT |
| agentciv-creator | Meta (single intelligence) | MIT |
| Creator Mode Civilisation | Meta-meta (VISION) | — |
| Recursive Triad | Recursive (VISION) | — |
| The Colony | Capstone | Commercial |
| Gnosis AI | Knowledge discovery | MIT |
| Infinitography website | Research programme | — |

---

## EXPONENTIAL ATLAS — SEPARATE PROJECT

- Location: `/Users/ekramalam/Singularity Is Now/exponential-atlas/`
- 22 pages built, 42 domains, 326 data points, 334KB gzipped
- **BLOCKED on integrity audit** (model data, cost items, website claims)
- RSI toggle needs Python model re-runs at 3 settings
- Sobol sensitivity analysis stub needs wiring
- Deploy to Netlify blocked until audit complete
- Feeds into "Better Than Kings" book — not part of outreach pipeline

---

## PAPER COUNT

| Series | Count | Status |
|--------|-------|--------|
| AgentCiv (Papers 1-12) | 12 | Published |
| Infinitography (Papers 13-27) | 15 | Published |
| Gnosis AI (Paper G16) | 1 | Published |
| Gnosis AI (Papers G17-G19) | 3 | Published (18 Apr) |
| New papers (replacing Checkpoint Alpha) | 3 | Published (27 Apr) |
| Pansophia | 1 | Published (2 May) |
| **Convergence Codex — Stage A Capstone (8 of 22)** | **8** | **Published (2 May)** |
| **Total published** | **43** | |
| *Convergence Codex — Stage A Capstone (remaining 14)* | *14* | *NOT DONE* |
| *Convergence Codex — Stage A Standard (~70 papers)* | *~70* | *NOT DONE* |

---

## EXECUTION PRIORITY

```
ALL PAPERS DONE (34 published, all Bitcoin-timestamped + Zenodo DOIs)
INFINITOGRAPHY WEBSITE — Wings 1-4 DONE (Discovery, ToE, New Contributions, Gnosis)

NOW ━━━━━━ STAGE 3b: THE CONVERGENCE CODEX ━━━━━━━━━━━━━━━━━

  ✅ Gnosis v2 (cross-domain, multi-field, recursive cascade, 81 fields)
  ✅ Logos AI (2,162 lines, Lean 4 formalisation, 5-layer adversarial validation)
  ✅ Synthesis AI (1,448 lines, publication-quality papers, auto boundaries)
  ✅ Pipeline Orchestrator (479 lines, thin coordination, checkpoints)
  ✅ Stage A — DONE (256/266 proofs through Logos)
  ▶  Stage A CAPSTONE — 8/22 papers DONE, v2 PDFs on Zenodo (3 May 2026)
     → FIRST: Write Paper Quality Bible (reference doc for every paper)
     → NEXT: Proofread all 8 papers against the Bible to top 0.00001% (manual AI, no API cost)
     → Publish v3 proofread versions to Zenodo
     → Fix pipeline prompts (no inline hex IDs, include formalisation maths)
     → Compose remaining 14 capstone papers (~$60-80)
     → Proofread + publish remaining 14 to Zenodo
     Stage A FORMALISATION CATALOGUE — ONE document with all 256 formalisations (no API cost)
     Stage B — THE BIG RUN: full Codex across 81 fields (10x more data)
     Stage B CAPSTONE — capstone papers from the big run (manual proofread each)
     Stage B FORMALISATION CATALOGUE — ONE document with all new formalisations (no API cost)
     Stage C — THE CROWN JEWELS: 3-5 most terminal/unifying claims get definitive papers
     Stage C PUBLICATION → Zenodo
     Stage D — HARDEN: formal proofs, predictions, close every gap in Stage C papers
     Stage D PUBLICATION — hardened papers + pre-registration predictions
     Stage E — GRAND FINALE: everything → one updated Theory of Everything
     Stage E PUBLICATION — THE Nobel paper
     Website — Convergence Codex wing on infinitography.com
     QC + stamp + ship

━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

THEN    Stage 3c — Pansophia wing on infinitography.com
THEN    Stage 3d — Remaining Infinitography website
            Papers 1-4 rewrite (user creates content)
            Homepage update (including Codex references)
            Full website playtest (all wings + Codex)
            Paper 12 upgrade

THEN    Stage 2 remainder (AgentCiv: 4a-4c, dogfood, papers 5+6)
THEN    Stage 4 (Polish both projects + Gnosis AI trademark)
THEN    Stage 5 (QA/QC — the big pre-outreach audit)
THEN    Stage 6 (Outreach — AgentCiv + Infinitography + Convergence Codex)
LATER   Stages 7-9 (Recursive Loop, Colony, Full Stack)
SEPARATE    Exponential Atlas (unblocked by integrity audit)
```

---

## KEY REFERENCES

| What | Where |
|------|-------|
| This roadmap | `/Users/ekramalam/MASTER_ROADMAP.md` |
| Infinitography sub-roadmap | `/Users/ekramalam/infinitography-website/docs/ROADMAP.md` |
| AgentCiv engine roadmap | `/Users/ekramalam/agentciv-engine/ROADMAP.md` |
| Creator Mode v1 build doc | `/Users/ekramalam/agentciv-creator/docs/CREATOR_MODE_V1_BUILD.md` |
| Website plan (AgentCiv) | `/Users/ekramalam/agentciv-engine/docs/WEBSITE_PLAN.md` |
| Apple style guide | `/Users/ekramalam/agentciv-engine/docs/APPLE_STYLE_GUIDE.md` |
| Outreach materials | `/Users/ekramalam/agentciv-website/docs/outreach/` |
| Zenodo DOIs | Memory file: `project_zenodo_dois.md` |
| All Zenodo API token | `gCDoHuu0vDKKaudMkV0FpgCppZvaOrnEJXEZO1udHX2osQrsXU8oe1B92IY4` |
| Exponential Atlas | `/Users/ekramalam/Singularity Is Now/exponential-atlas/` |
