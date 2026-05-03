# Compendium of Formally Verified Cross-Domain Convergences

## Reference Format Document

This document defines the exact format for every entry in the Compendium.
It serves as the reference template during assembly. Every entry must
follow this structure precisely, with no omissions.

---

## Purpose

This Compendium establishes **priority and provenance** for a body of
formally verified mathematical convergences discovered by Gnosis AI and
formalised by Logos AI. Each entry contains:

- A novel cross-domain structural claim
- A machine-verified formal proof (Lean 4 + Mathlib)
- A cryptographic provenance chain (SHA-256 → GitHub → Bitcoin blockchain)
- Instructions for independent verification

The document is designed so that any future review body — whether a
Fields Medal committee, Nobel committee, or independent researchers —
can unambiguously determine:

1. **What was claimed** (the precise mathematical statement)
2. **When it was claimed** (Bitcoin-anchored timestamp)
3. **Whether the proof is valid** (by running the Lean code themselves)
4. **What the proof does and does not establish** (honest limitations)

---

## Entry Format

Each convergence occupies one entry. Entries are numbered sequentially
(Entry 1, Entry 2, ...) in the order they were verified.

### Required Sections Per Entry

```
## Entry N: [Short Title]

### Claim

[One sentence: the novel cross-domain structural claim being established.]

### Domains

[The scientific domains this convergence connects, e.g., "Quantum Mechanics, Dynamical Systems"]

### Formal Proposition

[The precise mathematical statement being proved, in standard notation.]

### Verification Status

| Field | Value |
|-------|-------|
| Tier | PROVEN / PROOF_WITH_GAPS / RIGOROUS_ARGUMENT |
| Sorry count | 0 / N |
| Lean 4 type-checks | Yes / No |
| Mathlib version | [from lean-toolchain] |
| What is proven | [Plain English: what the Lean code actually establishes] |
| What is not proven | [Plain English: what remains unformalized and why] |

### Lean 4 Proof

```lean
[The complete Lean 4 code, exactly as verified]
```

### Proof Explanation

[2-5 paragraphs explaining the proof in plain mathematical English.
What each theorem establishes. How they connect to the original claim.
Why specific formalisation choices were made. Accessible to a
mathematician who does not use Lean.]

### Assumptions

[Numbered list of every assumption the proof relies on.]

### Limitations

[Honest statement of what the formalisation does NOT capture from the
original claim. E.g., "The category-theoretic functorial structure
(Steps 6-8) is represented abstractly via composition of real parameters
rather than as an explicit functor between categories, because Mathlib's
category theory library does not yet include quantum system categories."]

### Provenance

| Field | Value |
|-------|-------|
| Convergence ID | [12-char hex ID from Gnosis] |
| Git commit | [Full 40-char SHA-256 hash] |
| Commit timestamp | [ISO 8601 UTC] |
| Repository | github.com/wonderben-code/convergence-codex |
| Proof file | data/logos/proofs/[filename].json |

### Independent Verification

To verify this proof independently:

1. Clone the repository at the commit hash above
2. Install Lean 4 via elan: `curl https://elan.dev | sh`
3. Navigate to `lean_verify/` and run `lake build` (downloads Mathlib)
4. Save the Lean code above to a file in `lean_verify/`
5. Run: `lake env lean [filename].lean`
6. Expected output: no errors (warnings about unused variables are acceptable)

If the code type-checks with zero errors, the proof is valid.

---
```

### Entry Ordering

Entries are added in verification order (the order we prove them).
Each entry is immediately committed and pushed after verification,
creating an immutable provenance record.

### Tier Definitions

| Tier | Meaning | Lean Status |
|------|---------|-------------|
| **PROVEN** | Full formal proof, 0 sorry gaps. Machine verified. | Type-checks, 0 sorry |
| **PROOF_WITH_GAPS** | Partial formal proof. Core structure verified, some steps use sorry. | Type-checks, N sorry |
| **RIGOROUS_ARGUMENT** | Lean code generated but does not type-check. Natural language proof only. | Does not type-check |

All tiers are included in the Compendium. The tier is stated honestly.
A PROOF_WITH_GAPS entry is still valuable — it establishes what CAN be
formally verified and precisely identifies what cannot.

### Honesty Rules

1. Never claim PROVEN if any sorry exists in the code
2. Never omit limitations — state exactly what is and is not formalised
3. Never inflate what the Lean code proves beyond what it actually proves
4. If the Lean formalisation captures only part of the original claim, say so explicitly
5. The "What is not proven" field is mandatory for every entry

### Document Metadata

The Compendium itself carries metadata at the top:

```
# The Convergence Codex: Compendium of Formally Verified Cross-Domain Convergences

**Authors:** Mark E. Mala (Ekram Alam)
**AI Systems:** Gnosis AI (discovery), Logos AI (formalisation)
**Verification:** Lean 4 + Mathlib (machine verification)
**Provenance:** Bitcoin-anchored via GitHub commits
**Repository:** github.com/wonderben-code/convergence-codex
**License:** [TBD]
**Version:** Living document — entries added as proofs are verified

## How to Read This Document

Each entry represents a cross-domain structural convergence — a
mathematical pattern that appears independently across different
scientific fields. The convergences were discovered by Gnosis AI
and formalised by Logos AI using Lean 4, a proof assistant that
provides machine-checkable mathematical verification.

Every proof in this document can be independently verified by
anyone with a computer. Instructions are provided with each entry.

## Provenance Chain

Priority for each claim is established through the following chain:

1. Lean 4 code is written and verified locally
2. The proof is committed to a Git repository (SHA-256 hash)
3. The commit is pushed to GitHub
4. GitHub commits are anchored to the Bitcoin blockchain
   via automated timestamping

This chain is cryptographically tamper-proof. The Bitcoin blockchain
provides an immutable public record that the commit existed at a
specific point in time. No party — including the authors — can
retroactively alter the timestamps.

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total entries | [updated as we go] |
| PROVEN (0 sorry) | [count] |
| PROOF_WITH_GAPS | [count] |
| RIGOROUS_ARGUMENT | [count] |
| Domains covered | [count] |
| Date range | [first commit] to [last commit] |
```

---

## Pipeline: After Each Proof

After verifying each proof, the following steps are executed in order:

1. Save Lean code to proof JSON (`data/logos/proofs/[id].json`)
2. Add entry to Compendium (`data/compendium/compendium.md`)
3. `git add` both files
4. `git commit` with message: `"Compendium entry N: [title] -> [TIER]"`
5. `git push origin main`
6. Record commit hash in the entry's Provenance section
7. Proceed to next proof

This is non-negotiable. Every proof gets all 7 steps. No batching,
no "I'll commit later." Each entry has its own commit for clean provenance.
