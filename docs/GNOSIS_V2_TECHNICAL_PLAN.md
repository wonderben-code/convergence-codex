# Gnosis AI v2 — Technical Architecture Plan

**Created:** 2 May 2026
**Status:** Architecture sprint — this document resolves the 5 hard design problems before any code is written.
**Codebase reference:** `wonderben-code/gnosis-ai` (3,233 lines, 14 Python files)

This is the code-level design for upgrading Gnosis AI from v1 (within-category pairwise) to v2 (full cross-domain, multi-field, recursive cascade). Read this BEFORE writing any v2 code.

---

## 1. What v1 Does (Summary of Existing Code)

### Architecture
```
CLI (cli.py) → Orchestrator (orchestrator.py)
                    ├── Surveyor (ci/surveyor.py)         → surveys fields
                    ├── ConvergenceDetector (ci/convergence.py) → pairwise detection
                    ├── MetaConvergenceEngine (ci/meta.py)     → iterative reduction
                    ├── EAValidator (ea/validator.py)           → 5-check validation
                    ├── Store (data/store.py)                   → JSON file persistence
                    └── Taxonomy (data/taxonomy.py)             → 52 fields, 8 categories
```

### How Auto Mode Works (orchestrator.py lines 161-288)
1. `taxonomy.resolve(scope)` → list of FieldInfo
2. `_survey_domains(fields)` → list of Domain (with caching)
3. `itertools.combinations(domains, 2)` → all pairs (ARBITRARY ORDER)
4. Process in batches of 10: `detector.detect(da, db)` → convergences
5. EA validate each: `validator.validate(c)` → ea_scores
6. Filter by min_confidence (0.3)
7. After all pairs: `meta_engine.meta_converge(all_convergences)` → findings
8. Save run, convergences, findings to Store

### Key Limitations
- Pairs generated in arbitrary order (no priority)
- Multi-field comparison impossible (detector.detect takes exactly 2 domains)
- Meta-convergence only runs once at end, one grouping strategy
- No cross-run analysis
- No negative convergence tracking
- Convergence record doesn't track comparison_type (within vs cross-category)

---

## 2. Design Problem #1: Multi-Field Prompts

### The Problem
`convergence.py` DETECT_PROMPT is structured for exactly two domains:
```
## Field A: {name}
Results: ...
## Field B: {name}
Results: ...
→ "Are there genuine structural convergences?"
```

For 3+ fields, we need a fundamentally different prompt that finds the N-WAY pattern, not just N separate pairwise patterns.

### The Solution: Two-Stage Multi-Field Detection

**Stage 1: Structural Essence Extraction**
For each field in the group, extract a compact "structural essence" — the 3-5 core structural principles that define the field. This uses the existing survey data but compresses it.

**Stage 2: Multi-Field Convergence Detection**
Present all structural essences simultaneously and ask: "What structural pattern do ALL of these fields share that transcends any single pair?"

This avoids the cognitive overload of dumping 15+ results per field × 4 fields into one prompt. Instead, the model works with compressed structural essences.

### New Prompt: MULTI_FIELD_DETECT_PROMPT

```
You are examining {n} fields from different domains of science and mathematics simultaneously.

Your task is NOT to find pairwise convergences between pairs of fields — those have already been found.
Your task is to find MULTI-FIELD CONVERGENCES: structural patterns that ALL {n} fields share
simultaneously, patterns that only become visible when you look at all of them together.

## Fields and their structural essences:

{for each field:}
### {field_name} ({category})
Core structural principles:
{structural_essence — 3-5 bullet points from survey}

---

Consider: Is there a structural pattern that ALL {n} of these fields instantiate?
Not just "A and B share X" — that's pairwise. We need "A, B, C, and D ALL share X,
and X only becomes visible when you see all of them together."

Be CONSERVATIVE. Multi-field convergences are rarer and more significant than pairwise.
If the fields don't share a genuine multi-field pattern, say so.

Return JSON:
{{
  "multi_field_convergences": [
    {{
      "structural_claim": "The multi-field convergence — what ALL fields share",
      "fields_involved": ["field_id_1", "field_id_2", ...],
      "per_field_manifestation": {{
        "field_id_1": "How this pattern manifests in this field",
        "field_id_2": "How this pattern manifests in this field",
        ...
      }},
      "why_multi_field": "Why this pattern is only visible when examining all fields together,
                          not reducible to pairwise convergences",
      "convergence_type": "formal" or "structural_analogy",
      "reasoning": "..."
    }}
  ],
  "no_convergence_reason": "If none found, explain why"
}}
```

### New Prompt: STRUCTURAL_ESSENCE_PROMPT

```
Given the following survey of {field_name}, extract its 3-5 core structural principles.

Survey results:
{domain.results formatted}

Field-level conclusion: {domain.structural_conclusion}

Return JSON:
{{
  "structural_essence": [
    {{
      "principle": "One-sentence structural principle",
      "supporting_results": ["result_name_1", "result_name_2"],
      "abstraction_level": "mathematical" or "structural" or "phenomenological"
    }}
  ]
}}
```

### Implementation

New file: `gnosis/ci/multi_field.py`

```python
class MultiFieldDetector:
    """Detects convergences across 3+ fields simultaneously."""

    def __init__(self, api: ClaudeAPI):
        self.api = api

    def extract_essence(self, domain: Domain) -> list[dict]:
        """Extract structural essence from a surveyed domain."""
        # Uses STRUCTURAL_ESSENCE_PROMPT
        # Returns 3-5 core principles
        # Cache results (one essence per domain, reusable across groups)

    def detect_multi(self, domains: list[Domain]) -> list[Convergence]:
        """Detect multi-field convergences across 3+ domains."""
        # Step 1: Extract/load essence for each domain
        # Step 2: Build MULTI_FIELD_DETECT_PROMPT with all essences
        # Step 3: Parse response into Convergence objects
        # Key: comparison_type = "multi_field", domains = all field IDs
```

### Data Model Change

`Convergence` gets a new field:
```python
comparison_type: str = "pairwise"  # "pairwise" | "multi_field" | "cross_level"
```

This is distinct from `convergence_type` (which is "formal" | "structural_analogy").

---

## 3. Design Problem #2: Search Strategy Algorithm

### The Problem
Currently: `itertools.combinations(domains, 2)` in arbitrary order. No intelligence about WHAT to explore next.

### The Solution: Priority Queue with Dynamic Scoring

New file: `gnosis/strategy.py`

```python
@dataclass
class ComparisonTask:
    """A pending comparison to be executed."""
    fields: list[str]           # Field IDs (2 for pairwise, 3+ for multi-field)
    priority: float             # Higher = run sooner
    strategy: str               # Which strategy generated this task
    reason: str                 # Why this task was generated

class SearchStrategy:
    """Decides what to explore next in the combinatorial space."""

    def __init__(self, taxonomy: Taxonomy, corpus: CorpusManager):
        self.taxonomy = taxonomy
        self.corpus = corpus

    def generate_tasks(self, strategy: str, **kwargs) -> list[ComparisonTask]:
        """Generate comparison tasks for a given strategy."""
        # Dispatches to specific strategy methods

    def _cross_category_priority(self) -> list[ComparisonTask]:
        """All cross-category pairs, ordered by category distance."""
        # Category distance scoring:
        # Physics × Social Science = 1.0 (maximum distance)
        # Physics × Biology = 0.9
        # Physics × Mathematics = 0.5 (closer, expected connections)
        # Within-category = 0.1

    def _exhaustive_pairwise(self) -> list[ComparisonTask]:
        """All C(N,2) pairs, cross-category first."""

    def _transitivity_probe(self) -> list[ComparisonTask]:
        """If A↔B and B↔C share pattern P, test A↔C."""
        # Query corpus for convergences sharing structural patterns
        # Generate tasks for missing links in the transitivity graph

    def _hub_expansion(self) -> list[ComparisonTask]:
        """Fields with many convergences → multi-field groups."""
        # Query corpus for field convergence counts
        # For hubs (>= 5 convergences): create multi-field task
        #   with the hub + its top converging partners

    def _cluster_guided(self) -> list[ComparisonTask]:
        """Convergences that cluster → their fields as a group."""
        # Group convergences by structural pattern similarity
        # For each cluster: create multi-field task with all source fields

    def _random_sample(self, n: int = 20) -> list[ComparisonTask]:
        """Random pairs for serendipity."""

    def update_priorities(self, new_convergences: list[Convergence]):
        """After discoveries, update priorities of remaining tasks."""
        # If field A just produced convergences:
        #   - Boost priority of all tasks involving A
        #   - Generate new multi-field tasks involving A + its partners
```

### Category Distance Matrix

The key scoring function for cross-category priority:

```python
CATEGORY_DISTANCE = {
    # Maximum distance (most disparate, highest discovery value)
    ("Physics", "Social & Cognitive Sciences"): 1.0,
    ("Mathematics", "Biology"): 1.0,
    ("Physics", "Biology"): 0.95,
    ("Mathematics", "Social & Cognitive Sciences"): 0.95,
    ("Computer Science", "Biology"): 0.9,
    ("Computer Science", "Social & Cognitive Sciences"): 0.9,
    ("Physics", "Earth and Space"): 0.7,
    ("Chemistry", "Social & Cognitive Sciences"): 0.85,
    # Moderate distance
    ("Physics", "Chemistry"): 0.6,
    ("Biology", "Chemistry"): 0.5,
    ("Physics", "Mathematics"): 0.5,
    ("Computer Science", "Mathematics"): 0.4,
    # Low distance (within-category treated as 0.1)
}

def pair_priority(field_a: FieldInfo, field_b: FieldInfo) -> float:
    """Score a pair by category distance. Higher = more disparate = more valuable."""
    if field_a.category == field_b.category:
        return 0.1  # Within-category: lowest priority
    key = tuple(sorted([field_a.category, field_b.category]))
    return CATEGORY_DISTANCE.get(key, 0.7)  # Default moderate
```

### Dynamic Priority Updates

After each batch of comparisons:
1. For each new convergence, identify the fields involved
2. Boost priority of all pending tasks involving those fields (+0.1 per convergence found)
3. If a field becomes a "hub" (5+ convergences), generate multi-field tasks
4. If a structural pattern appears in 3+ pairs, generate transitivity probes for missing links

---

## 4. Design Problem #3: Multi-Grouping Meta-Convergence

### The Problem
Current meta-convergence (`ci/meta.py`): takes ALL convergences, asks Claude to reduce. One pass per level. One grouping strategy (implicit: "all together").

v2 needs: multiple grouping strategies at each level, each producing potentially different meta-convergences.

### The Solution: Explicit Grouping Strategies

New file: `gnosis/ci/cascade.py`

```python
class GroupingStrategy(str, Enum):
    BY_DOMAIN = "by_domain"             # Group by shared domain
    BY_CATEGORY = "by_category"         # Group by category pair
    BY_PATTERN = "by_pattern"           # Group by structural similarity
    BY_CONFIDENCE = "by_confidence"     # Group by confidence tier
    PAIRWISE = "pairwise"              # Compare convergences pairwise
    HOLISTIC = "holistic"              # All convergences together (v1 behavior)
    CROSS_LEVEL = "cross_level"        # Compare Level N with Level N-1

class CascadeEngine:
    """Multi-level recursive cascade with multiple grouping strategies."""

    def __init__(self, api: ClaudeAPI, corpus: CorpusManager):
        self.api = api
        self.corpus = corpus
        self.meta_engine = MetaConvergenceEngine(api)

    def run_cascade(
        self,
        convergences: list[Convergence],
        strategies: list[GroupingStrategy] = None,
        max_levels: int = 5,
    ) -> CascadeResult:
        """Run the full multi-level cascade."""

        if strategies is None:
            strategies = [
                GroupingStrategy.BY_DOMAIN,
                GroupingStrategy.BY_CATEGORY,
                GroupingStrategy.BY_PATTERN,
                GroupingStrategy.HOLISTIC,
            ]

        all_findings = []
        current_level_objects = convergences
        level = 1

        while level <= max_levels:
            level_findings = []

            for strategy in strategies:
                groups = self._group(current_level_objects, strategy)
                for group_name, group_items in groups.items():
                    if len(group_items) < 2:
                        continue
                    findings = self.meta_engine._one_round(group_items, level)
                    for f in findings:
                        f.grouping_strategy = strategy.value
                        f.group_name = group_name
                    level_findings.extend(findings)

            if not level_findings:
                break

            # Deduplicate (different strategies may find same pattern)
            level_findings = self._deduplicate(level_findings)
            all_findings.extend(level_findings)

            # Check for fixed points
            if any(f.coined_term and "fixed_point" in (f.coined_term or "").lower()
                   for f in level_findings):
                break

            # Cross-level comparison
            if level > 1:
                cross = self._cross_level_compare(
                    prev_level=[f for f in all_findings if f.level == level - 1],
                    curr_level=level_findings,
                    level=level,
                )
                all_findings.extend(cross)

            # Next level: convert findings to convergence-like objects
            current_level_objects = self._findings_to_convergences(level_findings)
            level += 1

        return CascadeResult(
            findings=all_findings,
            levels_reached=level - 1,
            fixed_point_reached=any(
                f.coined_term and "fixed_point" in (f.coined_term or "").lower()
                for f in all_findings
            ),
        )

    def _group(
        self,
        items: list[Convergence],
        strategy: GroupingStrategy,
    ) -> dict[str, list[Convergence]]:
        """Group convergences by the specified strategy."""

        if strategy == GroupingStrategy.BY_DOMAIN:
            # Group by shared domain: all convergences involving field X
            groups = {}
            for c in items:
                for d in c.domains:
                    groups.setdefault(f"domain:{d}", []).append(c)
            return groups

        elif strategy == GroupingStrategy.BY_CATEGORY:
            # Group by category pair: all physics×biology convergences
            groups = {}
            for c in items:
                cats = sorted(set(
                    self.corpus.field_category(d) for d in c.domains
                ))
                key = "×".join(cats) if len(cats) > 1 else cats[0]
                groups.setdefault(f"category:{key}", []).append(c)
            return groups

        elif strategy == GroupingStrategy.BY_PATTERN:
            # Use Claude to cluster convergences by structural similarity
            return self._cluster_by_pattern(items)

        elif strategy == GroupingStrategy.BY_CONFIDENCE:
            # Group by confidence tier
            groups = {}
            for c in items:
                ea = c.get_ea()
                tier = ConfidenceCategory.from_score(ea.confidence).value
                groups.setdefault(f"confidence:{tier}", []).append(c)
            return groups

        elif strategy == GroupingStrategy.HOLISTIC:
            # All together (v1 behavior)
            return {"all": items}

        elif strategy == GroupingStrategy.CROSS_LEVEL:
            # Handled separately in run_cascade
            return {}

        return {"all": items}

    def _cluster_by_pattern(self, items: list[Convergence]) -> dict[str, list[Convergence]]:
        """Use Claude to cluster convergences by structural similarity."""
        # Prompt: "Group these convergences by structural similarity.
        #          Return clusters of convergences that share structural features."
        # This is an API call — use deep model
        # Returns: {"cluster_name": [convergence_ids]}
        pass

    def _cross_level_compare(
        self,
        prev_level: list[Finding],
        curr_level: list[Finding],
        level: int,
    ) -> list[Finding]:
        """Compare findings across levels — does a Level 1 convergence
        share structure with a Level 2 meta-pattern?"""
        # Prompt: present Level N-1 and Level N findings
        # Ask: "Do any lower-level findings share structure with higher-level patterns?"
        pass

    def _deduplicate(self, findings: list[Finding]) -> list[Finding]:
        """Remove findings that are structurally identical (from different strategies)."""
        # Compare structural_finding text similarity
        # Keep the one with more source_convergence_ids
        pass
```

### New Prompt: CROSS_LEVEL_PROMPT

```
You are comparing findings from different levels of analysis.

## Level {n-1} findings (more specific):
{findings_text_lower}

## Level {n} findings (more abstract):
{findings_text_higher}

Do any lower-level findings share structural features with higher-level patterns?
A lower-level finding might be a SPECIFIC INSTANCE of a higher-level pattern.
Or a higher-level pattern might EXPLAIN why a lower-level finding exists.

Return JSON:
{{
  "cross_level_convergences": [
    {{
      "structural_claim": "The cross-level relationship",
      "lower_finding_ids": ["id1"],
      "higher_finding_ids": ["id2"],
      "relationship_type": "instance_of" | "explained_by" | "structural_parallel",
      "reasoning": "..."
    }}
  ]
}}
```

### New Prompt: PATTERN_CLUSTERING_PROMPT

```
Group these {n} convergences by structural similarity. Convergences that describe
aspects of the same underlying pattern should be in the same cluster.

{convergences_text}

Return JSON:
{{
  "clusters": [
    {{
      "cluster_name": "Descriptive name for this structural pattern",
      "convergence_ids": ["id1", "id2", ...],
      "shared_pattern": "What these convergences have in common structurally"
    }}
  ]
}}
```

---

## 5. Design Problem #4: Corpus Manager

### The Problem
Current Store: simple JSON files, one per object. `list_convergences()` loads ALL files and returns a list. No querying capability beyond "load all, filter in Python."

With 5,000+ convergences this becomes slow and the query patterns for the cascade engine are complex.

### The Solution: Indexed Corpus Manager

New file: `gnosis/data/corpus.py`

```python
class CorpusManager:
    """Indexed convergence corpus for cross-run querying."""

    def __init__(self, store: Store, taxonomy: Taxonomy):
        self.store = store
        self.taxonomy = taxonomy
        self._index: dict = {}    # In-memory index, built on init
        self._build_index()

    def _build_index(self):
        """Build in-memory indexes from stored convergences."""
        self._by_field: dict[str, list[str]] = {}      # field_id → [conv_ids]
        self._by_category_pair: dict[str, list[str]] = {}  # "Physics×Biology" → [conv_ids]
        self._by_run: dict[str, list[str]] = {}         # run_id → [conv_ids]
        self._by_type: dict[str, list[str]] = {}        # comparison_type → [conv_ids]
        self._by_confidence: dict[str, list[str]] = {}  # tier → [conv_ids]
        self._field_convergence_count: dict[str, int] = {}  # field_id → count
        self._negative: list[str] = []                  # conv_ids flagged as negative

        for conv in self.store.list_convergences():
            self._index_convergence(conv)

    def _index_convergence(self, conv: Convergence):
        """Add a convergence to all indexes."""
        cid = conv.id
        for field in conv.domains:
            self._by_field.setdefault(field, []).append(cid)
            self._field_convergence_count[field] = \
                self._field_convergence_count.get(field, 0) + 1

        # Category pair
        cats = sorted(set(self.field_category(d) for d in conv.domains))
        cat_key = "×".join(cats)
        self._by_category_pair.setdefault(cat_key, []).append(cid)

        # Other indexes
        if conv.discovered_in_run:
            self._by_run.setdefault(conv.discovered_in_run, []).append(cid)
        self._by_type.setdefault(
            getattr(conv, 'comparison_type', 'pairwise'), []
        ).append(cid)
        ea = conv.get_ea()
        tier = ConfidenceCategory.from_score(ea.confidence).value
        self._by_confidence.setdefault(tier, []).append(cid)

    # ─── Query Methods ───

    def convergences_for_field(self, field_id: str) -> list[Convergence]:
        """All convergences involving a specific field."""
        ids = self._by_field.get(field_id, [])
        return [self.store.load_convergence(cid) for cid in ids]

    def convergences_for_category_pair(self, cat_a: str, cat_b: str) -> list[Convergence]:
        """All convergences between two categories."""
        key = "×".join(sorted([cat_a, cat_b]))
        ids = self._by_category_pair.get(key, [])
        return [self.store.load_convergence(cid) for cid in ids]

    def hub_fields(self, min_convergences: int = 5) -> list[tuple[str, int]]:
        """Fields with the most convergences (sorted descending)."""
        hubs = [(f, c) for f, c in self._field_convergence_count.items()
                if c >= min_convergences]
        return sorted(hubs, key=lambda x: -x[1])

    def field_category(self, field_id: str) -> str:
        """Look up the category for a field."""
        field = self.taxonomy.get(field_id)
        return field.category if field else "unknown"

    def explored_pairs(self) -> set[tuple[str, str]]:
        """Set of all (field_a, field_b) pairs already compared."""
        pairs = set()
        for conv in self.store.list_convergences():
            if len(conv.domains) == 2:
                pairs.add(tuple(sorted(conv.domains)))
        return pairs

    def transitivity_candidates(self) -> list[tuple[str, str, str]]:
        """Find (A, B, C) where A↔B and B↔C have convergences but A↔C doesn't."""
        explored = self.explored_pairs()
        candidates = []
        # For each field B that appears in 2+ convergences
        for field_b, count in self._field_convergence_count.items():
            if count < 2:
                continue
            # Get all fields that converge with B
            partners = set()
            for conv_id in self._by_field.get(field_b, []):
                conv = self.store.load_convergence(conv_id)
                for d in conv.domains:
                    if d != field_b:
                        partners.add(d)
            # For each pair of B's partners: check if they've been compared
            partner_list = sorted(partners)
            for i, a in enumerate(partner_list):
                for c in partner_list[i+1:]:
                    if tuple(sorted([a, c])) not in explored:
                        candidates.append((a, field_b, c))
        return candidates

    def save_negative(self, field_a: str, field_b: str, reason: str):
        """Record that a comparison found NO convergence (informative absence)."""
        neg = Convergence(
            structural_claim=f"No convergence found: {reason}",
            convergence_type="none",
            domains=[field_a, field_b],
            comparison_type="negative",
        )
        self.store.save_convergence(neg)
        self._negative.append(neg.id)

    def stats(self) -> dict:
        """Corpus statistics."""
        return {
            "total_convergences": sum(len(v) for v in self._by_field.values()) // 2,
            "total_fields_explored": len(self._field_convergence_count),
            "total_category_pairs": len(self._by_category_pair),
            "hubs": self.hub_fields(),
            "negative_count": len(self._negative),
        }
```

### Why Not a Database?

JSON files + in-memory index is the right choice because:
1. Consistent with v1 architecture (no new dependency)
2. Portable (copy the data/ directory to share the corpus)
3. ~5,000 convergences × ~2KB each ≈ 10MB — trivially fits in memory
4. Index builds in <1 second
5. Compatible with git versioning and Bitcoin timestamping

If we ever hit 50,000+ convergences, we can add SQLite. Not now.

---

## 6. Design Problem #5: Logos Integration Format

### The Problem
Logos needs to take a convergence and produce a formal proof. The current Convergence data model has: structural_claim, convergence_type, supporting_results, ea_scores. But Logos needs more:
- What mathematical structures are involved?
- What kind of equivalence is being claimed?
- What level of formality is achievable?

### The Solution: Enriched Convergence Output

During detection (both pairwise and multi-field), we add new fields to the prompt response:

```python
# New fields on Convergence for Logos compatibility
@dataclass
class Convergence:
    # ... existing fields ...

    # NEW v2 fields
    comparison_type: str = "pairwise"       # "pairwise" | "multi_field" | "cross_level" | "negative"
    mathematical_structures: list[str] = field(default_factory=list)  # e.g. ["group theory", "topology"]
    proposed_equivalence: str = ""           # e.g. "isomorphism", "functor", "structural analogy"
    formalisability_hint: str = ""           # "high" | "medium" | "low" | "requires_new_mathematics"
    source_categories: list[str] = field(default_factory=list)  # ["Physics", "Biology"]
    parent_convergence_ids: list[str] = field(default_factory=list)  # for meta-convergences
    negative: bool = False                   # True if this records an absence
```

The detection prompts (both pairwise and multi-field) are updated to request these:

```
For each convergence, also specify:
- "mathematical_structures": Which mathematical frameworks are relevant (e.g. ["category theory", "measure theory"])
- "proposed_equivalence": What kind of formal relationship is claimed (e.g. "isomorphism", "adjunction", "structural analogy")
- "formalisability_hint": How feasible is formal proof? "high" = standard maths, "medium" = requires work, "low" = mostly analogical, "requires_new_mathematics" = beyond current formalism
```

### Logos Input Schema (JSON)

This is what Logos receives for each convergence:

```json
{
  "id": "abc123",
  "structural_claim": "Quantum decoherence and species extinction share a threshold-collapse structure",
  "convergence_type": "structural_analogy",
  "comparison_type": "pairwise",
  "domains": ["quantum_foundations", "evolutionary_biology"],
  "domain_names": ["Quantum Foundations", "Evolutionary Biology"],
  "source_categories": ["Physics", "Biology"],
  "supporting_results": [
    {
      "result_name": "Zurek's Decoherence Programme",
      "domain_id": "quantum_foundations",
      "domain_name": "Quantum Foundations",
      "structural_conclusion": "Superposition collapses irreversibly above a threshold of environmental coupling",
      "epistemic_status": "experimentally_confirmed"
    },
    {
      "result_name": "Extinction Debt Theory",
      "domain_id": "evolutionary_biology",
      "domain_name": "Evolutionary Biology",
      "structural_conclusion": "Population collapse occurs irreversibly above a threshold of habitat fragmentation",
      "epistemic_status": "well_supported_conjecture"
    }
  ],
  "ea_scores": {
    "strength": 0.72,
    "independence": 0.85,
    "adversarial": 0.68,
    "reproducibility": 0.55,
    "confidence": 0.71,
    "confidence_category": "supported"
  },
  "mathematical_structures": ["dynamical systems", "threshold theory", "bifurcation theory"],
  "proposed_equivalence": "structural_analogy",
  "formalisability_hint": "medium"
}
```

---

## 7. Negative Convergence Tracking

### Design

When `ConvergenceDetector.detect()` returns `{"convergences": []}`, we currently discard this information. In v2, we record it:

```python
# In orchestrator, after detection:
if not convergences:
    corpus.save_negative(
        field_a=domain_a.id,
        field_b=domain_b.id,
        reason=data.get("no_convergence_reason", "No genuine convergences found"),
    )
```

The detection prompt already asks for `no_convergence_reason` — we just need to store it.

Negative convergences are valuable for:
1. **Transitivity analysis:** If A↔B and B↔C converge, but A↔C doesn't — why?
2. **Field characterisation:** Which fields are "isolates" (converge with almost nothing)?
3. **Category boundaries:** Do within-category negatives tell us about natural category structure?

---

## 8. Expanded Taxonomy

### Additions (28 new fields → 80 total)

```json
{
  "Biology": [
    "genomics",
    "cell_biology",
    "immunology",
    "developmental_biology",
    "biophysics",
    "microbiology"
  ],
  "Social & Cognitive Sciences": [
    "linguistics",
    "anthropology",
    "political_science"
  ],
  "Medicine & Health": [
    "epidemiology",
    "physiology",
    "pharmacology",
    "neuroscience_clinical"
  ],
  "Earth & Space Sciences": [
    "oceanography",
    "climate_science",
    "planetary_science"
  ],
  "Engineering & Technology": [
    "chemical_engineering",
    "mechanical_engineering",
    "biomedical_engineering"
  ],
  "Information Sciences": [
    "information_theory",
    "data_science",
    "knowledge_representation"
  ]
}
```

This gives 80 fields across 9 categories (new: "Medicine & Health", "Information Sciences").
- C(80, 2) = 3,160 pairwise comparisons
- Cross-category pairs: ~2,935 (93%)

The taxonomy is defined in `taxonomy/fields.json` — straightforward to extend.

---

## 9. New CLI Commands

```bash
# ─── Codex Mode (the main new mode) ───
gnosis codex \
  --strategy cross-category-priority \  # or exhaustive, transitivity, hub, cluster, random
  --max-cost 500 \
  --max-hours 24 \
  [--include-multi-field]               # Also run multi-field after pairwise

gnosis codex --strategy multi-field \
  --fields "quantum_foundations,evolutionary_biology,market_economics" \
  --max-cost 10

# ─── Cascade Mode (corpus-level meta-convergence) ───
gnosis cascade \
  --strategies "by_domain,by_category,by_pattern,holistic" \
  --max-levels 5 \
  [--cross-level]                       # Include cross-level comparisons

# ─── Enhanced Auto Mode (backward-compatible) ───
gnosis auto --scope all                 # Now processes cross-category pairs too
gnosis auto --scope physics,biology     # Cross-category between these two

# ─── Corpus Commands ───
gnosis corpus stats                     # Corpus statistics
gnosis corpus hubs                      # Fields with most convergences
gnosis corpus transitivity              # Transitivity candidates
gnosis corpus negatives                 # Informative absences
gnosis corpus export --format logos     # Export in Logos-compatible format
```

---

## 10. Build Phases

### Phase 1: Cross-Category Auto + Enriched Output (~300 lines changed)

**Files changed:** `orchestrator.py`, `convergence.py`, `models.py`, `cli.py`
**What:** Make Auto mode work across categories (it mostly already does with `--scope all`) + add new Convergence fields (comparison_type, mathematical_structures, etc.) + update detection prompt to request these.
**Test:** Run `gnosis auto --scope physics,biology --max-cost 5` — should produce cross-category convergences with enriched data.
**This is the simplest high-value change.** Gets cross-domain working immediately.

### Phase 2: Search Strategy Engine (~400 lines new)

**New file:** `gnosis/strategy.py`
**What:** Priority queue, category distance scoring, dynamic updates.
**Files changed:** `orchestrator.py` (new codex mode), `cli.py` (new command)
**Test:** Run `gnosis codex --strategy cross-category-priority --max-cost 10` — should process most disparate pairs first.

### Phase 3: Corpus Manager (~250 lines new)

**New file:** `gnosis/data/corpus.py`
**What:** Indexed corpus with query methods, transitivity detection, hub detection, negative tracking.
**Files changed:** `orchestrator.py` (use corpus for negative tracking), `cli.py` (corpus commands)
**Test:** Load all existing convergence data, query by field/category/confidence. Verify hub detection and transitivity candidates.

### Phase 4: Multi-Field Comparison (~300 lines new)

**New file:** `gnosis/ci/multi_field.py`
**What:** Structural essence extraction + multi-field detection prompt.
**Files changed:** `orchestrator.py` (multi-field support in codex mode), `cli.py`
**Test:** Run multi-field on {QM, Topology, Ecology} — should find (or honestly not find) a three-way pattern.

### Phase 5: Recursive Cascade (~350 lines new)

**New file:** `gnosis/ci/cascade.py`
**What:** Multi-grouping cascade engine, cross-level comparison, deduplication.
**Files changed:** `cli.py` (cascade command)
**Test:** Run cascade on existing 266 convergences with multiple grouping strategies. Compare outputs from different strategies. Verify deduplication.

### Phase 6: Taxonomy Expansion (~50 lines changed)

**File changed:** `taxonomy/fields.json`
**What:** Add 28 new fields across expanded/new categories.
**Test:** `gnosis fields` shows 80 fields. `gnosis auto --scope "medicine & health" --max-cost 2` works.

### Total new code: ~1,650 lines across 4 new files
### Total changed code: ~400 lines across 5 existing files
### Estimated total v2: ~5,300 lines (from 3,233)

---

## 11. Testing Strategy

Each phase gets tested against REAL data before moving on:

| Phase | Test | Success Criteria |
|-------|------|-----------------|
| 1 | Cross-category auto (physics × biology, $5) | Produces cross-domain convergences with enriched fields |
| 2 | Codex mode with priority ($10) | Most disparate pairs processed first; priority updates work |
| 3 | Corpus queries on existing data | Correct hub detection, transitivity candidates found |
| 4 | Multi-field on 1 triplet ($2) | Finds or honestly reports no multi-field convergence |
| 5 | Cascade on existing 266 convergences ($5) | Multiple grouping strategies produce different meta-convergences |
| 6 | Taxonomy expansion + small run ($3) | New fields surveyable and comparable |

**Total test budget: ~$25**

---

## 12. Backward Compatibility

All v1 commands continue to work unchanged:
- `gnosis guided` — same behavior
- `gnosis explore` — same behavior
- `gnosis auto --scope physics` — same behavior (within-category)
- `gnosis report` — works with both v1 and v2 runs
- Existing data in `data/` directory is fully compatible

New v2 capabilities are additive:
- `gnosis codex` — new command
- `gnosis cascade` — new command
- `gnosis corpus` — new command
- `gnosis auto --scope all` — now processes cross-category pairs with priority ordering

---

## 13. File Change Summary

| File | Change | Lines |
|------|--------|-------|
| `gnosis/strategy.py` | NEW — search strategy engine | ~400 |
| `gnosis/ci/multi_field.py` | NEW — multi-field detection | ~300 |
| `gnosis/ci/cascade.py` | NEW — recursive cascade engine | ~350 |
| `gnosis/data/corpus.py` | NEW — indexed corpus manager | ~250 |
| `gnosis/data/models.py` | MODIFY — new Convergence fields, Finding fields | ~30 |
| `gnosis/ci/convergence.py` | MODIFY — enriched prompt output | ~20 |
| `gnosis/orchestrator.py` | MODIFY — codex mode, corpus integration | ~200 |
| `gnosis/cli.py` | MODIFY — new commands | ~150 |
| `taxonomy/fields.json` | MODIFY — 28 new fields | ~50 |
| **TOTAL** | | **~1,750** |
