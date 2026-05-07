# THE MATHS ORG — Systematic Mathematics Research Lab

**Created:** 7 May 2026
**Purpose:** Organisational workflow for upgrading every Lean file to genuine, world-class mathematics.
**Scope:** All 67 files in `lean_verify/paper_f/`
**Goal:** Every theorem in every file is REAL mathematics — a world-class mathematician would accept it.

---

## Core Principles

### 1. The Caesar Principle (Strategic Decomposition → FULL Solution)
Not all problems are equal. Some problems, once conquered, cause 3-4 other problems to fall easily. When a problem is hard, decompose it into a staircase of sub-problems, then attack the EASIEST stair that unlocks the most territory.

**CRITICAL: The staircase is a STRATEGY for solving the ENTIRE original problem, not just one step.** Agents must:
1. Decompose the hard problem into a staircase of sub-problems
2. Attack the easiest stair first (it unlocks others)
3. **Climb the ENTIRE staircase** — solve every step
4. **Arrive at the top** — the original hard problem is now solved

Finding the decomposition is not the goal. SOLVING the full problem via the decomposition IS the goal. An agent who decomposes brilliantly but only solves step 1 of 5 has not finished. They continue until all 5 steps are proven and the original theorem compiles.

### 2. The Key Generator Principle (Intermediate Steps)
If you can't prove A → C directly, find B such that A → B → C works. Every hard theorem has a staircase of intermediate lemmas. Find the staircase. Each step should be manageable. The staircase IS the proof. **But you must prove EVERY step of the staircase — A → B, then B → C — and chain them together. The job is done when A → C compiles, not when you've identified B.**

### 3. Relentless — No Arbitrary Limits
There is NO attempt limit. Agents do not stop after 3 tries. They try every strategy, every decomposition, every Mathlib path, every web resource. They stop ONLY when:
- **SOLVED** — the proof compiles, Grade A confirmed, or
- **SUBSTANTIVE BLOCK** — a detailed document explaining exactly WHY this cannot be done in current Lean 4 + Mathlib, citing the specific missing infrastructure

"I tried 3 times" is NOT a stopping condition. "Mathlib has no theory of X, which is prerequisite for Y" IS a stopping condition.

### 4. Nothing Left Behind
Even OUT OF SCOPE theorems get a precise specification: "Here's the exact Lean type we need. Here's the exact Mathlib gap. Here's what would need to exist." This is a roadmap for future work, not a failure.

---

## The Org Structure

### Overview

```
COORDINATOR
|
+-- BATCH 1 (15 files in parallel)
|   +-- File Team 1:  [Triage] -> [5-6 Mathematicians] -> [Synthesis] -> [5-6 Reviewers] -> [Revision] -> [Build] -> [Certify]
|   +-- File Team 2:  (same)
|   +-- ...
|   +-- File Team 15: (same)
|
+-- BATCH 2 (next 15 files) -> same structure
+-- BATCH 3 (next 15 files) -> same structure
+-- BATCH 4 (next 15 files) -> same structure
+-- BATCH 5 (remaining 7 files) -> same structure
```

**67 files total. 5 batches of ~15. Each file gets its own dedicated team.**

---

## The Journey of ONE File

### PHASE 1: TRIAGE (1 agent)

Reads the file completely. For every theorem, records:

| Field | What to record |
|-------|----------------|
| Theorem name | Verbatim from source |
| Current Lean type | Verbatim — this is what's ACTUALLY proven |
| Proof method | What tactics/terms are used (norm_num, simp, rfl, etc.) |
| Docstring claim | What the file SAYS it proves |
| Current grade | A/B/C/D per LEAN_INTEGRITY_PROTOCOL.md |
| Target type | The exact Lean type that would make this Grade A |
| Difficulty | EASY / MEDIUM / HARD / OUT OF SCOPE (first estimate) |
| Mathlib path | What Mathlib modules/theorems would be needed |

Output: **Spec Sheet** — the complete diagnosis and target for the mathematician team.

---

### PHASE 2: MATHEMATICIAN TEAM (5-6 agents, parallel, SAME file)

Each mathematician agent gets:
- The original file
- The Triage Spec Sheet (target types for every theorem)
- The grading protocol with 25 calibration examples
- The Caesar Principle and Key Generator Principle
- Full access to all resources (see Resources section below)

**Each agent works independently. They cannot see each other's work.**

| Agent | Primary Strategy |
|-------|-----------------|
| **M1: The Algebraist** | Direct algebraic approach — import the right Mathlib structures, standard tactics |
| **M2: The Librarian** | Exhaustive Mathlib search — find existing lemmas that chain together to prove the target |
| **M3: The Builder** | Bottom-up — prove simpler sub-lemmas first (Caesar staircase), build to the target |
| **M4: The Analogist** | Find similar proven theorems in Mathlib source, adapt their proof structure |
| **M5: The Researcher** | Web search for how this theorem is proven on paper, translate to Lean |
| **M6: The Simplifier** | Find the absolute minimum proof — can this be done in 3 lines with the right import? |

**Each agent is RELENTLESS within their session:**
```
Try direct approach -> fails
  Read error -> adjust -> retry
    Fails differently -> search Mathlib for relevant lemmas
      Find candidates -> try each
        Partially works -> build on it
          Stuck at sub-lemma -> APPLY CAESAR: what's the easiest sub-problem?
            Find it -> prove that first
              APPLY KEY GENERATOR: what intermediate step bridges the gap?
                Find B such that A->B->C works
                  Keep building the staircase...
                    Search web for proof strategies...
                      Check Lean Zulip for similar problems...
                        ...never stop until solved or genuinely blocked...
```

Each agent outputs: their best `.lean` file + a report of what they tried, what worked, what didn't, and why.

---

### PHASE 3: SYNTHESIS (1 agent)

Gets ALL 5-6 mathematician outputs + their reports. Task:

1. For each theorem, pick the **best proof** across all attempts
2. If M1 proved 8/15 and M3 proved 10/15 (different ones), combine -> maybe 13/15
3. If M2 found a key Mathlib lemma that others missed, use it
4. If M4 found a staircase decomposition that M1's proof can walk, combine them
5. Identify theorems that NOBODY solved -> create **Blocker Briefing**

Output:
- ONE unified `.lean` file with best proof for each theorem
- **Blocker Briefing** for unsolved theorems: what was tried, what partially worked, what's missing

---

### PHASE 3b: ROUND 2 (if needed — 5-6 FRESH mathematicians)

**Only triggered if Phase 3 has unsolved theorems.**

Fresh mathematician agents get:
- The synthesized file (with solved theorems)
- The Blocker Briefing (what Round 1 tried and where they got stuck)
- All partial progress from Round 1
- Instruction: "Round 1 couldn't crack these specific theorems. Here's exactly where they got stuck. Find a different way."

They start from the FRONTIER of Round 1, not from scratch. Their job is to break through the specific identified blockers.

**This repeats (Round 3, 4, ...) until either SOLVED or SUBSTANTIVE BLOCK documented.**

---

### PHASE 4: PEER REVIEW TEAM (5-6 agents, parallel, SAME file)

Each reviewer independently:

1. Reads every theorem's type — does it ACTUALLY prove what's claimed?
2. Checks: is the proof correct? Any hidden `sorry`? Any `native_decide`? Any boolean encoding?
3. Checks: does the type use real Mathlib structures or hand-rolled definitions?
4. Checks: would a world-class mathematician accept this proof?
5. Checks: are imports genuine (not shadowing Mathlib with local definitions)?
6. Flags anything suspicious
7. Suggests specific improvements

Each outputs: review report with PASS/FAIL per theorem + detailed feedback.

**Reviewers cannot see each other's reports.**

---

### PHASE 5: REVISION (1 agent)

Gets: the synthesized file + ALL 5-6 peer review reports.

- Applies all valid feedback
- Fixes all flagged issues
- If a reviewer found a better approach, uses it
- If multiple reviewers flagged the same issue, it's definitely real — fix it
- Outputs: the **final** `.lean` file

---

### PHASE 6: BUILD GATE (sequential, 1 agent)

- Add file to `lakefile.toml` roots
- Run `lake build`
- Must pass with: 0 sorry, 0 errors, 0 warnings
- If it fails -> back to Phase 5 with the exact error messages
- If it passes -> proceed to Phase 7

**This phase is sequential across files** (shared Lean build state). But writing proofs (Phases 2-5) runs in parallel across all files.

---

### PHASE 7: FINAL CERTIFICATION (1 fresh agent)

- Has NEVER seen this file before
- Reads the built file cold
- Independently grades every theorem against the LEAN_INTEGRITY_PROTOCOL.md
- Checks every theorem is Grade A
- If ALL Grade A -> **CERTIFIED**
- If ANY theorem < Grade A -> back to Phase 4 with specific flags

---

## Resources Available to All Agents

| Resource | How to access | What it's for |
|----------|---------------|---------------|
| **Mathlib source code** | Grep/Read through `.lake/packages/mathlib/` | Find existing lemmas, see how similar things are proven |
| **Mathlib documentation** | WebSearch "mathlib4 [topic]" | API reference, module structure |
| **Lean 4 documentation** | WebSearch "lean 4 [topic]" | Tactic reference, syntax |
| **Lean Zulip** | WebSearch "site:leanprover.zulipchat.com [topic]" | How-to for specific proof patterns |
| **Mathematical papers** | WebSearch "[theorem name] proof" | Proof strategies to translate to Lean |
| **Textbooks** | WebSearch "[topic] textbook proof" | Standard approaches |
| **`lake build`** | Bash tool | Test if proofs compile |
| **`#check` / `#print`** | Bash (via lake env lean) | Explore Lean types interactively |
| **`lake exe env`** | Bash | Check available Mathlib imports |

**Key resource: Mathlib source is LOCAL.** Agents can grep through hundreds of thousands of lines of real proofs for patterns, lemma names, and proof strategies. This is the most powerful resource available.

---

## Grading Reference

Grades are defined in `docs/LEAN_INTEGRITY_PROTOCOL.md` with 25 calibration examples.

| Grade | Meaning | Example |
|-------|---------|---------|
| **A** | The Lean type IS the claimed mathematics | `Module.finrank C (CliffordAlgebra Q4) = 16` |
| **B** | Real maths but name overclaims | `matrix_assoc` named "octonion_exclusion" |
| **C** | Pure arithmetic | `4 - 1 = 3` named "imaginary_quaternion_dim" |
| **D** | Tautological | `3 = 3` named "exactly_three_division_algebras" |

**The ONLY acceptable final grade is A.** Anything else triggers more rounds of mathematician work or honest relabelling/removal.

---

## Stopping Conditions

| Outcome | When it applies | What's produced |
|---------|----------------|-----------------|
| **CERTIFIED (Grade A)** | All 7 phases passed. Every theorem Grade A. Builds clean. | Final `.lean` file in build |
| **OUT OF SCOPE** | Multiple rounds of mathematicians + substantive block documented | Precise spec: what Lean type is needed, what Mathlib gap exists, what infrastructure would unlock it |
| **RELABELLED** | The type is real maths (Grade B) but can't be upgraded further | Docstring/name changed to honestly match what the type actually proves |
| **REMOVED** | No mathematical value, pure padding | File deleted or theorem removed |

**OUT OF SCOPE requires:** a detailed document citing specific Mathlib gaps. Not "we couldn't do it" but "Mathlib lacks X theory, which would require Y to build, here's what the proof would look like if X existed."

---

## Execution Plan

| Batch | Files | Est. agents per batch |
|-------|-------|----------------------|
| Batch 1 | 15 files (start with EASIEST — files already in build) | ~210 agent runs |
| Batch 2 | 15 files (MEDIUM difficulty) | ~210 |
| Batch 3 | 15 files (MEDIUM-HARD) | ~210 |
| Batch 4 | 15 files (HARD — QG, mass gap, CC) | ~210+ (more rounds likely) |
| Batch 5 | 7 files (remaining) | ~98 |

**Start with Batch 1 (files already in build)** — these are most likely to have genuine maths already. Quick wins build momentum and test the pipeline.

**Caesar Principle at the batch level:** The 13 IN_BUILD files are the easiest targets. Solving these first establishes patterns, discovers useful lemmas, and builds infrastructure that makes the harder files easier.

---

## Anti-Drift Persistence System

**Problem:** Context windows compact and clear. Sessions restart. Without persistent state, agents lose track of where they are and repeat work or skip files.

**Solution:** ALL pipeline state is written to files on disk and committed to git. Nothing lives only in context.

### State Files

| File | Purpose | Updated by |
|------|---------|------------|
| `docs/MATHS_ORG.md` | This document. The workflow spec. Read-only during execution. | Only updated if the workflow itself changes |
| `docs/COORDINATOR_STATE.md` | **THE LIVE STATE FILE.** Current batch, per-file phase, blockers, cross-file discoveries. | Coordinator after EVERY phase completion |
| `docs/LEAN_AUDIT_REPORT.md` | Per-file classification and grading results | Triage agents, Certification agents |
| `docs/file_reports/<filename>_report.md` | Per-file detailed report: what each mathematician tried, synthesis decisions, review findings, blocker details | Each phase agent for that file |

### The Coordinator's Persistence Protocol

After EVERY phase completion for EVERY file, the Coordinator MUST:

1. **Update `COORDINATOR_STATE.md`** with:
   - File name
   - Phase just completed
   - Outcome (success / needs-round-2 / blocker)
   - Next action
   - Any cross-file discoveries (useful lemmas, Mathlib patterns found)

2. **Git commit + push** the state update (per the data provenance rule)

3. **Write per-file report** to `docs/file_reports/` with detailed findings

### Session Recovery Protocol

If context is lost or a new session starts:

1. Read `docs/MATHS_ORG.md` (this document — the workflow spec)
2. Read `docs/COORDINATOR_STATE.md` (**the live state — tells you exactly where you are**)
3. Read `docs/LEAN_INTEGRITY_PROTOCOL.md` (grading system)
4. Read `docs/LEAN_AUDIT_REPORT.md` (per-file classifications)
5. For any file mid-pipeline, read `docs/file_reports/<filename>_report.md`
6. Resume from the recorded checkpoint — **no guessing, no repeating work**

### Anti-Drift Rules

1. **Never rely on context alone.** If it's not in a file on disk, it doesn't exist.
2. **Every decision gets written down.** "We chose proof strategy X because Y" — in the file report.
3. **Every blocker gets documented.** Not "it didn't work" but "Mathlib lacks X, tried Y and Z, here's the exact error."
4. **Cross-file discoveries propagate.** If solving File A reveals a useful lemma, it goes in COORDINATOR_STATE.md under "Discoveries" so agents working on File B can use it.
5. **Commit after every phase.** Not at the end of a batch — after EVERY phase of EVERY file. Granular checkpointing.
6. **State files are the source of truth.** If context says one thing and the state file says another, the state file wins.

---

## Quality Standard

The bar: **a world-class mathematician reading only the Lean types would recognise every theorem as genuine mathematics.** Not arithmetic dressed as physics. Not tautologies with fancy names. Real algebra, real analysis, real topology — proven through Mathlib's trusted kernel.
