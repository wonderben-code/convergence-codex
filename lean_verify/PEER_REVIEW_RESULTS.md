# ADVERSARIAL PEER REVIEW — MASTER RESULTS
# Date: 2026-05-07
# 12 independent review agents, zero context shared

## EXECUTIVE SUMMARY

All 66 Paper F files compile (2801 jobs, 0 sorry, 0 native_decide). The Lean
type-checking is legitimate. However, there is a **systematic and severe gap
between what docstrings claim and what the Lean types actually encode**.

### The Core Problem

The mathematical infrastructure creates structures whose field names evoke
physics concepts (Wightman axioms, OS axioms, mass gap) but whose actual
content is trivial real analysis or arithmetic:

- `HasMassGap.vacuum_normalised` = `exp(0) = 1` (tautology)
- `WightmanVerification.w2_positive` = `∀ H, 0 < exp(-H)` (just exp_pos)
- `WightmanVerification.w4_locality` = `4! = 24` (unrelated to locality)
- `OSVerification.os3_symmetry` = `4! = 24` (unrelated to symmetry)
- `ConnesAxioms.has_chirality` = `True` (literally vacuous)

The "theorems" then unpack these structure fields and claim to have proven
deep physics results.

### Grade Distribution (12 reviewed files)

| File | Grade | Core Issue |
|------|-------|-----------|
| CascadeFoundation | C+ | Genuine Mathlib for dimensions; HasMassGap is axiom-carrier |
| CascadeUniqueness | C+ | Arithmetic proxies for Chamseddine-Connes classification |
| F3_9g_vii FullMassGap | C-/D | Mass gap is INPUT (CascadeData), not derived |
| F4_4g UnconditionalMillennium | D+ | "Circular tautology dressed in elaborate docstrings" |
| F4_4e WightmanAxioms | D+ | "Shell game" — trivial arithmetic named after axioms |
| F4_4a OSAxiomsCompact | D+ | Scaffolding around trivial mathematics |
| F4_3b ConfinementFirstPrinciples | C- | Beta function arithmetic only |
| F4_3c MassGapConditional | C- | Repackages assumed inputs |
| F4_3d SpectralWightman | C-/D | Trivial analysis dressed as Wightman QFT |
| F1_6 PatiSalamForced | B-/C | CascadeConstraints is DEFINED, not derived |
| F3_1 ThreeGenerations | C- | 4-1=3 and 3*16=48, nothing "forced" |
| F3_2 HiggsForced | C- | Dimension counting, no representation theory |

### What IS Genuine (Grade A theorems across all files)

1. `cascade_algebra_dim`: finrank ℂ (Matrix (Fin 4) (Fin 4) ℂ) = 16 — REAL Mathlib
2. `cascade_hilbert_dim`: finrank ℂ (Fin 4 → ℂ) = 4 — REAL Mathlib
3. `action_factorises`: exp(-(a+b)) = exp(-a)*exp(-b) — REAL (exp_add)
4. `gap_pos`: 2/Λ² > 0 given Λ > 0 — REAL (div_pos, pow_pos)
5. `gap_decay`: exp(-gap*r) < 1 for gap,r > 0 — REAL (exp_lt_one_iff)
6. `physical_gap_pos`: min of two positives is positive — REAL (lt_min)
7. `step3_sharp_poincare`: λ₁*C_P = 1 → C_P = 1/λ₁ — REAL (field_simp)
8. `classification_n_equals_4`: omega case split on even n ≤ 4 with n²-1≥12 — REAL
9. Various Quaternion/Clifford/tensor theorems in F4_1* files — REAL Mathlib

### What Is NOT Proven (common across all files)

1. **No Lie algebras**: su(n) is never defined. "dim su(4) = 15" is computed as 16-1.
2. **No group embeddings**: SU(3)×SU(2)×U(1) → SU(4) never constructed.
3. **No spectral theory**: No operators, no spectrum, no Hamiltonian.
4. **No distributions**: No Schwartz distributions for Wightman axioms.
5. **No measure theory**: No path integral, no functional integral.
6. **No Riemannian geometry**: No Bakry-Emery, no Ricci curvature.
7. **No operator theory**: No Kato-Rellich, no form bounds.
8. **No confinement**: No flux tubes, no Wilson loops, no area law.
9. **No representation theory**: No irreps, no Clebsch-Gordan, no branching rules.

## WHAT CAN BE UPGRADED (feasible in Lean 4 + Mathlib)

### Level 1: Straightforward (days)
- Define `TracelessHermitian n ℂ` as submodule, prove dim = n²-1
- Define `UnitaryGroup n ℂ` embedding maps explicitly
- Replace `has_chirality : True` with actual constraint
- Fix docstrings to honestly state what's conditional

### Level 2: Moderate effort (weeks)
- Genuine group homomorphism SU(3)×SU(2)×U(1) → SU(4)
- Branching rules for fundamental representation
- Explicit Connes axioms with algebraic content
- Spectral action as actual functional on matrices

### Level 3: Research-level (months+, possibly infeasible today)
- Wightman axioms with distribution theory (Mathlib lacks Schwartz distributions)
- OS reconstruction theorem (needs measure-theoretic QFT)
- Bakry-Emery gap estimate (needs Riemannian geometry)
- Actual mass gap for Yang-Mills (THIS IS THE OPEN PROBLEM)

## RECOMMENDED FIX STRATEGY

1. **HONEST DOCSTRINGS** — Not downgrading, but accuracy. State explicitly:
   "This theorem proves [X] CONDITIONAL on [Y] being provided via CascadeData."

2. **GENUINE LEVEL 1 UPGRADES** — Build TracelessHermitian, prove dim(su(n))=n²-1,
   construct embedding maps. This converts C-grade arithmetic into A-grade algebra.

3. **CONDITIONAL FRAMEWORK** — The conditional structure IS legitimate mathematics.
   "IF the spectral triple satisfies Connes' axioms THEN the gauge group is SU(4)"
   is a real theorem. Just make the hypotheses explicit.

4. **SEPARATE CONCERNS** — Split each file into:
   (a) Genuine unconditional math (finrank, exp properties, group theory)
   (b) Conditional theorems (IF cascade conditions THEN consequences)
   (c) Master theorems combining (a) and (b)
