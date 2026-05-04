# Paper F — Contributing Guide (Best Practices)

How to add results to Paper F as they are proven.

---

## The Golden Rule

**Prove first, write second, stamp immediately.**

```
1. Write the Lean proof in lean_verify/paper_f/
2. Compile clean (0 sorry, 0 errors)
3. Add to Paper F draft (data/papers/paper_f_generator_toe.md)
4. Commit + push (Bitcoin timestamp)
```

---

## File Organisation

```
lean_verify/paper_f/
├── README.md                        # Index of all Paper F proofs
├── F1_6_PatiSalamForced.lean        # Tier 1, item 6
├── F1_1_FalsificationProps.lean     # (future)
├── F1_2_LawvereInstances.lean       # (future)
├── F2_3_ChiralityForced.lean        # (future)
└── ...
```

**Naming:** `F{tier}_{number}_{ShortName}.lean`

---

## Adding a New Result

### Step 1: Write the Lean file

```lean
/-
  Paper F — Problem F{X}.{Y}: {Title}
  =====================================

  Author: Mark E. Mala (Ekram Alam)
  Roadmap: docs/PAPER_F_ROADMAP.md, Item F{X}.{Y}
  Builds on: {list parent files}

  {Description of what this proves and why it matters}

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1
  Target: 0 sorry
-/
```

### Step 2: Verify clean compilation

```bash
cd lean_verify
~/.elan/bin/lake env lean paper_f/F{X}_{Y}_{Name}.lean
```

Must produce: no errors, no sorry, ideally no warnings.

### Step 3: Update the Paper F draft

Add a new section or extend an existing one in `data/papers/paper_f_generator_toe.md`:
- State the theorem in natural language
- Give the proof structure
- List machine-verified components
- Note any established results invoked
- Update the theorem count in the abstract

### Step 4: Update the README

Add the new file to `lean_verify/paper_f/README.md` table.

### Step 5: Update the roadmap

Mark the item as DONE in `docs/PAPER_F_ROADMAP.md`.

### Step 6: Commit + Push

```bash
git add lean_verify/paper_f/ data/papers/paper_f_generator_toe.md docs/PAPER_F_ROADMAP.md
git commit -m "F{X}.{Y}: {Short description} — {N} theorems, 0 sorry"
git push origin main
```

The push triggers Bitcoin timestamping via GitHub + OpenTimestamps.

---

## Quality Standards

| Criterion | Requirement |
|-----------|-------------|
| Sorry count | 0 (for decidable/arithmetic content) |
| Warnings | 0 (fix unused vars, deprecations) |
| Documentation | Every theorem has a docstring |
| Established results | Clearly marked as invoked, not machine-verified |
| Imports | Only from Mathlib (no sorry-containing local files) |
| Self-contained | Each file compiles independently |

---

## What Goes Where

| Content | Location |
|---------|----------|
| Machine-verified proofs | `lean_verify/paper_f/*.lean` |
| Paper F narrative | `data/papers/paper_f_generator_toe.md` |
| Roadmap (what to prove next) | `docs/PAPER_F_ROADMAP.md` |
| This guide | `docs/PAPER_F_CONTRIBUTING.md` |

---

## When to Publish

Paper F publishes periodically to Zenodo:
- **v0.1:** After F1.6 (Pati-Salam uniqueness) — NOW
- **v1.0:** After all Tier 1 items (F1.1-F1.7)
- **v2.0:** After Tier 2 items
- **v3.0+:** As Tier 3/4 results accumulate

Each version gets its own DOI. Earlier versions remain accessible.

---

## Commit Message Format

```
F{X}.{Y}: {What was proven} — {N} theorems, 0 sorry

{2-3 line description of what this establishes}

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>
```

---

## Linking to Paper E

Paper F BUILDS ON Paper E. The relationship:
- Paper E = existence ("the cascade produces X")
- Paper F = uniqueness + closure ("X is the ONLY possibility")

When a Paper F result strengthens a Paper E result, note this explicitly:
```lean
/-- Strengthens EmergenceTheorem.lean conjunct 5 from existence to uniqueness. -/
```
