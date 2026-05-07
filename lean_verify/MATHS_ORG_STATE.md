# MATHS ORG — MASTER STATE FILE
# Last updated: 2026-05-07
# READ THIS FIRST if conversation is compacted/cleared

## WHAT WE'RE DOING
Making every Lean 4 + Mathlib proof across 90+ files GENUINELY prove what its docstring claims, at Fields Medal / Millennium Prize committee level. No arithmetic proxies. No tautologies. Real mathematics.

## CURRENT STATUS

### Phase 1: Adversarial Audit — COMPLETE (8/8 teams)
All 90+ files reviewed by independent adversarial agents. Results:

**Paper D/E (root files): 67% Grade A — STRONG**
- 6 perfect files (100% A): ReflexiveDomainFP, SeedForced, SU2Emergence, CauchyFunctional, etc.
- Genuine Lawvere, tensor products, Landau potential, SL₂(ℂ), Kronecker isomorphisms

**Paper F (67 files): 23% Grade A — NEEDS WORK**
- 7 star files (65-100% A): F4_1h, F4_1e_CliffordMatrix, F4_1a, F4_1e_QuatSplit, F4_1b, F4_1f, F3_10a
- Worst: CC cluster (94% C), Millennium files (82% C+D), Mass gap advanced (86% C+D)
- ~600 theorems are arithmetic proxies or tautologies

### Phase 1.5: Mathematician Upgrade Teams — IN PROGRESS (6 teams deployed)
1. **Spacetime Clifford** — F1_7, F1_7b, F1_7c (use real CliffordAlgebra refs)
2. **Mass Gap Conditional** — F3_9a, F3_9d, F3_9e, F3_9f (fix "returns own hypothesis" pattern)
3. **Millennium Files** — F4_3a, F4_3c, F4_3f, F4_4a, F4_4e, F4_4g (fix worst offenders)
4. **CC Cluster** — F3_8d_ii through _xvi (replace bare arithmetic with finrank)
5. **Gravity/Confinement** — F3_9g_iv-vii, F3_8g, F3_8i (fix mass_gap_theorem, qg_100_percent_solved)
6. **Gauge/Particle** — F3_1b, F3_8b, F3_8f, F1_6 (fix spectral_theorem_3x3, etc.)

### Phase 2: Custom Lean Types — PLANNED (next session)
Build the mathematical infrastructure that makes "OUT OF SCOPE" claims provable:

**Level 1 types (straightforward construction):**
- `HermitianMatrix n ℂ` as Submodule → prove finrank = n²
- `TracelessHermitian n ℂ` (= su(n)) → prove finrank = n²-1
- `AdjointRepDim n` → n²-1 from TracelessHermitian
- `FundamentalRepDim n` → n from Fin n → ℂ

**Level 2 types (more work, still feasible):**
- `SpectralTriple` structure (algebra A, Hilbert space H, Dirac operator D)
- `ConnesAxiom` (7 axioms as Props on SpectralTriple)
- `CascadeSpectralTriple` (A = M₄(ℂ), H = ℂ¹⁶, D from gamma matrices)
- Verify all 7 Connes axioms for the cascade instance

**Level 3 types (conditional framework):**
- `YangMillsTheory` structure with required properties
- `HasMassGap` predicate
- `OSAxioms` structure (5 axioms as Props)
- `WightmanAxioms` structure (5 axioms as Props)
- Conditional theorems: IF [cascade conditions] THEN [consequences]

### Phase 3: Second Adversarial Review — PLANNED
Fresh agents re-review every file after upgrades. Zero-context, independent grading.

### Phase 4: Final Certification + Bitcoin Stamp — PLANNED
Build verification, commit, push, timestamp.

## KEY PRINCIPLES (from user)
1. **NEVER downgrade claims** — upgrade the math to reach the claim
2. **Staircase approach** — decompose hard problems, attack easiest stair first
3. **Key Generator Principle** — find intermediate B for A→B→C
4. **Arithmetic theorems are SCAFFOLDING** — specs for mathematician agents, not final product
5. **Out of Scope = build a staircase** — if current tools can't do it, build new tools/types
6. **One file at a time** — build, verify, then move on

## KEY MATHLIB LEMMAS (proven useful)
- `Module.finrank_matrix` + `Fintype.card_fin` → dim(Mₙ(ℂ)) = n²
- `Module.finrank_pi` → dim(Fin n → ℂ) = n
- `finrank_tensorProduct` → dim(V ⊗ W) = dim(V) × dim(W)
- `Matrix.trace_mul_comm` → Tr(AB) = Tr(BA)
- `Quaternion.finrank_eq_four`, `Complex.finrank_real_complex`
- `exp_add`, `exp_zero`, `exp_pos`, `exp_lt_one_iff`, `exp_le_one_iff`
- `Real.Gamma_one`, `Nat.factorial_one`, `Real.Gamma_nat_eq_factorial`
- `kroneckerAlgEquiv`, `reindexAlgEquiv`, `transposeAlgEquiv`
- `CliffordAlgebra.lift` (used in F4_1e_CliffordMatrix)
- `exists_fixed_point_of_surjective` (Lawvere)
- `lt_min` (gap transfer), `mul_pos`, `div_pos`
- `Complex.normSq_nonneg`, `sq_nonneg`

## WORST OFFENDERS (must fix)
1. `millennium_prize_solved` (F4_4g) — proves arithmetic, claims Millennium Prize
2. `mass_gap_conditional` (F4_3c) — returns own hypotheses
3. `mass_gap_theorem` (F3_9g_vii) — proves 0<2, claims mass gap
4. `qg_100_percent_solved` (F3_9g_vii) — proves 10+1=11
5. `os_reconstruction_conditional` (F4_3d) — takes 5 True hypotheses
6. `bolzano_weierstrass` (F4_3h/F4_4d) — proves C>0→C≥0
7. `gns_construction` (F4_3h/F4_4d) — counts to 3
8. `penrose_conditions` (F3_8i) — proves 3=3
9. `spectral_theorem_3x3` (F3_1b) — proves 3=3 four times

## BUILD COMMAND
cd /Users/ekramalam/convergence-codex/lean_verify && lake build PaperF

## GIT NOTES
- Remote often has Bitcoin timestamp bot commits → always `git pull --rebase` before push
- TestProof.lean has sorry but is NOT in build (not in lakefile.toml)
- _proof_004_logos.lean has 1 honest sorry (OUT OF SCOPE)
