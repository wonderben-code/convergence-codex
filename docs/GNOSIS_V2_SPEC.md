# Gnosis AI v2 — Upgrade Specification

**Created:** 2 May 2026
**Purpose:** Upgrade Gnosis AI from within-category pairwise to full cross-domain, multi-field, recursive analysis.

This is the most critical build step in the Convergence Codex. Without this upgrade, the Codex explores only 7% of the possibility space.

---

## 1. Why v2

### The Problem

Gnosis v1 Auto mode works by specifying a CATEGORY (e.g., "physics"), and it compares all fields WITHIN that category. Cross-category comparisons (e.g., physics × biology) require Guided mode — manually specifying each pair.

With 80 fields across 8 categories:
- Within-category pairs: ~225 (7% of total) — reachable in Auto
- Cross-category pairs: ~2,935 (93% of total) — requires manual specification
- Multi-field comparisons: impossible in any mode

The most valuable discoveries — where totally different fields converge in unexpected ways — are structurally unreachable in Auto mode.

### The Fix

v2 makes cross-domain the PRIMARY mode. Multi-field comparisons become first-class. The system explores the full combinatorial space with smart gating.

---

## 2. New Capabilities

### 2.1 Unified Comparison Engine

**Current:** Takes two fields from the same category.
**v2:** Takes ANY set of fields (2, 3, 4, ... N) from ANY categories.

For pairwise (|S|=2): same as current, but works across categories.
For multi-field (|S|≥3): finds structural patterns shared by ALL fields simultaneously, not just pairwise decomposition.

Example for {QM, Evolution, Markets}:
- DON'T just find QM↔Evo, QM↔Markets, Evo↔Markets separately
- DO find the pattern ALL THREE share that no single pair reveals
- "All three are instances of constraint-resolution under uncertainty with selection pressure"

### 2.2 Search Strategy Engine

Decides what to explore next based on results so far. Available strategies:

**Cross-Category Priority (DEFAULT):**
```
Priority 1: Most disparate cross-category pairs
            (Physics × Social, Maths × Biology, etc.)
Priority 2: Moderately disparate cross-category
            (Physics × Maths, Biology × Chemistry, etc.)
Priority 3: Within-category pairs
Priority 4: Multi-field groups (cross-category first)
```

**Exhaustive Pairwise:** All C(N,2) pairs. ~3,160 for 80 fields.

**Transitivity Probing:** If A↔B and B↔C converge on pattern P, test A↔C for P.

**Hub Expansion:** Fields that converge with many others → multi-field groups around them.

**Cluster-Guided:** Pairwise convergence clusters → try those fields as a group.

**Random Sampling:** Explore unexpected corners (essential for serendipity).

**User-Guided:** Manual specification of any set of fields (backward-compatible with v1 Guided).

### 2.3 Convergence Corpus Manager

Persistent store of ALL convergences across ALL runs, indexed and queryable.

Each convergence record:
```json
{
  "id": "unique-id",
  "source_fields": ["quantum_mechanics", "evolutionary_biology"],
  "categories": ["physics", "biology"],
  "comparison_type": "cross-category-pair",
  "structural_claim": "...",
  "supporting_results": [...],
  "ea_scores": { "strength": 0.7, "independence": 0.8, ... },
  "confidence": "supported",
  "level": 1,
  "parent_convergences": [],
  "child_meta_convergences": [],
  "run_id": "...",
  "timestamp": "...",
  "negative": false
}
```

Queryable by: field, category, comparison type, confidence, level, structural pattern.

Also tracks NEGATIVE convergences (expected but not found).

### 2.4 Recursive Cascade Engine

Current meta-convergence: runs within a single Gnosis run.
v2: runs across the ENTIRE corpus.

**Multiple grouping strategies at Level 2:**
- Group by domain pair → meta-convergences
- Group by structural type → meta-convergences
- Group by pattern cluster → meta-convergences
- Group by category → meta-convergences
- Pairwise comparison of convergences → meta-convergences
- Cross-level comparison (Level 1 ↔ Level 2) → meta-convergences

Each grouping produces DIFFERENT meta-convergences. All are explored.

**Level 3+:** Same process applied recursively until fixed points.

**Cross-level comparisons:** Level 1 objects can converge with Level 2 or Level 3 objects. Not restricted to within-level.

---

## 3. Expanded Taxonomy

### Current (52 fields, 8 categories)

| Category | Fields | Count |
|----------|--------|-------|
| Physics | Classical Mechanics, Thermodynamics, Electromagnetism, Quantum Mechanics, Special Relativity, General Relativity, Quantum Field Theory, Particle Physics, Condensed Matter, Statistical Mechanics, Optics, Fluid Dynamics, Nuclear Physics, Plasma Physics | 14 |
| Mathematics | Algebra, Analysis, Topology, Geometry, Number Theory, Combinatorics, Logic & Foundations, Category Theory, Probability, Statistics, Differential Equations, Numerical Methods, Information Theory, Cryptography | 14 |
| Computer Science | Algorithms & Complexity, Programming Languages, Artificial Intelligence, Machine Learning, Distributed Systems, Databases | 6 |
| Biology | Molecular Biology, Genetics, Ecology, Evolutionary Biology, Neuroscience, Systems Biology | 6 |
| Chemistry | Physical Chemistry, Organic Chemistry, Inorganic Chemistry | 3 |
| Earth & Space Sciences | Geology, Atmospheric Science, Astronomy | 3 |
| Social & Cognitive Sciences | Psychology, Sociology, Economics, Cognitive Science | 4 |
| Engineering & Technology | Electrical Engineering, Materials Science | 2 |

### Proposed Expansion (target 70-100+)

**Biology expansion:** Genomics, Cell Biology, Immunology, Developmental Biology, Biophysics, Microbiology, Pharmacology
**Social sciences:** Linguistics, Anthropology, Political Science, Philosophy of Science
**Medicine:** Epidemiology, Physiology, Pathology
**Earth sciences:** Oceanography, Climate Science, Planetary Science
**Engineering:** Chemical Engineering, Mechanical Engineering, Biomedical Engineering
**New category — Information Sciences:** Library Science, Data Science, Knowledge Representation

Review and finalise during build. The taxonomy should be expanded where doing so opens genuinely new cross-domain comparisons.

---

## 4. New Modes (CLI)

### Codex Mode (the main new mode)
```bash
gnosis codex --strategy cross-category-priority --taxonomy expanded
gnosis codex --strategy exhaustive-pairwise
gnosis codex --strategy transitivity-probe --source-run <run-id>
gnosis codex --strategy hub-expansion --hub-field quantum_mechanics
gnosis codex --strategy multi-field --fields "quantum_mechanics,evolutionary_biology,market_economics"
```

### Enhanced Auto Mode (backward-compatible)
```bash
gnosis auto --category physics              # v1 behavior (within-category)
gnosis auto --categories physics,biology    # NEW: cross-category
gnosis auto --all                           # NEW: all fields, all categories
```

### Cascade Mode (corpus-level meta-convergence)
```bash
gnosis cascade --corpus ./data/             # run cascade on entire corpus
gnosis cascade --grouping-strategy domain   # specific grouping
gnosis cascade --level 3                    # cascade to level 3
```

---

## 5. Implementation Notes

- Gnosis v2 is built IN PLACE in the existing `wonderben-code/gnosis-ai` repo
- v1 functionality preserved (backward-compatible)
- New code adds capabilities, doesn't break existing modes
- All new modes produce output in the same convergence format (compatible with Logos)
- Corpus manager uses JSON files (consistent with v1 approach, no database needed)
- Bitcoin-stamped via existing GitHub Actions workflow

---

## 6. Acceptance Criteria

- [ ] Cross-category pairwise works in Auto mode (not just within-category)
- [ ] Multi-field comparison works (3+ fields simultaneously)
- [ ] All search strategies implemented and selectable via CLI
- [ ] Convergence Corpus Manager stores and indexes all convergences
- [ ] Corpus queryable by field, category, type, confidence, level
- [ ] Recursive cascade runs across entire corpus (not just within-run)
- [ ] Multiple grouping strategies produce different meta-convergences
- [ ] Cross-level comparison works (Level 1 ↔ Level 2 objects)
- [ ] Negative convergences tracked
- [ ] Expanded taxonomy integrated
- [ ] All existing v1 modes still work (backward-compatible)
- [ ] Codex mode with cross-category priority works end-to-end
- [ ] Output format compatible with Logos input format
- [ ] Bitcoin-timestamped
- [ ] Tests pass
- [ ] README updated
