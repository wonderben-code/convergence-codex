# Master Roadmap — All Projects

**Creator:** Mark E. Mala (Ekram Alam)
**Last updated:** 2 May 2026 (capstone progress update)
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

**Published:** 35 papers on Zenodo with DOIs. All Bitcoin-timestamped. 8 capstone papers composed (awaiting Zenodo publication).

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
| 3 | **Synthesis AI** — 1,448 lines, 11 files, publication-quality paper generation | **DONE** |
| 4 | **Pipeline Orchestrator** — 479 lines, 3 files, thin coordination, human checkpoints | **DONE** |
| 5 | **Stage A** — 266 existing convergences through Logos → Synthesis | **DONE** (256/266 proofs, 2 May) |
| 5c | **Stage A CAPSTONE** — 22 Nobel-format papers across all cascade levels (L5→L1). Genuine ontological claims about reality (Einstein/Higgs model), precisely scoped, with predictions extending into untested domains. 6-stage pipeline: census → claim formulation → planning → composition → 18-point review → prediction extraction. Anti-hallucination enforced (real convergence IDs only, deterministic provenance, no fake DOIs). | **8/22 DONE** (2 May) |
| 5c-i | Clean up 8 completed capstone papers for Zenodo publication | **DONE** (fixed fake IDs, DOIs, headers) |
| 5c-ii | Publish 8 capstone papers to Zenodo with DOIs | NOT DONE |
| 5c-iii | Compose remaining 14 capstone papers (resume from paper 9/22) | NOT DONE |
| 5c-iv | Publish remaining 14 capstone papers to Zenodo with DOIs | NOT DONE |
| 5b | **Stage A STANDARD** — ~70 domain-pair papers from 256 formal conjectures → Zenodo with DOIs | NOT DONE |
| 6 | **Stage B** — full Codex across 81 fields (6 phases) | NOT DONE |
| 6b | **Stage B PUBLICATION** — ~300-500 papers, thousands of conjectures → Zenodo | NOT DONE |
| 6c | **Stage B CAPSTONE** — updated fixed points with full 81-field evidence base. Do the Stage A fixed points hold? Strengthen/revise/discover new ones. The "Nobel paper" for Stage B. | NOT DONE |
| 7 | **Stage C** — deep formalisation of fixed points (Lean 4 machine-verified) | NOT DONE |
| 7b | **Stage C PUBLICATION** — standalone principle papers (the crown jewels) | NOT DONE |
| 8 | **Stage D** — derive testable predictions from principles | NOT DONE |
| 8b | **Stage D PUBLICATION** — pre-registration prediction papers, Bitcoin-stamped BEFORE confirmation | NOT DONE |
| 9 | **Stage E** — ToE integration (map Codex evidence against Paper 15) | NOT DONE |
| 9b | **Stage E PUBLICATION** — THE capstone paper: updated Theory of Everything | NOT DONE |
| 10 | **Website wing** — Convergence Codex on infinitography.com | NOT DONE |
| 11 | **QC + stamp + ship** | NOT DONE |
| 12 | **Open Source + Production Grade** — Make all 4 AIs (Gnosis, Logos, Synthesis, Capstone) + Orchestrator production-ready for anyone to clone, install, and run. PyPI packages (`pip install convergence-codex`), proper `pyproject.toml`, CLI entry points, config file system (no hardcoded paths), comprehensive README with quickstart, example data for dry runs without API credits, CI/CD (tests + linting), Docker option, framing audit ("landmark scientific paper format" not "Nobel AI"), license decision (MIT/Apache 2.0). Goal: a researcher anywhere in the world can `pip install` and run the full pipeline on their own domains. | NOT DONE |

**Every convergence, every formalisation, every meta-convergence is a publishable formal conjecture.** The corpus from Stages A+B alone could be 300-500+ papers with thousands of novel formal mathematical conjectures, all Bitcoin-stamped for priority.

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
| **Total published** | **34** | |

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
  ▶  Stage A CAPSTONE — 8/22 Nobel-format papers DONE + cleaned (2 May 2026)
     → Publish 8 to Zenodo
     → Compose remaining 14 capstone papers (~$60-80)
     → Publish remaining 14 to Zenodo
     Stage A STANDARD — ~70 domain-pair papers → Zenodo with DOIs
     Stage B — Full Codex across 81 fields (6 phases)
     Stage B PUBLICATION — ~300-500 papers → Zenodo
     Stage B CAPSTONE — updated fixed points with full evidence base
     Stage C — Deep formalisation of fixed points
     Stage C PUBLICATION — Principle papers (crown jewels)
     Stage D — Testable predictions from principles
     Stage D PUBLICATION — Pre-registration papers (Higgs mechanism)
     Stage E — ToE integration
     Stage E PUBLICATION — THE capstone ToE paper
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
