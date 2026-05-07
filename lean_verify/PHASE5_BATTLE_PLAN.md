---
name: Phase 5 Deep Mathematics Upgrade — FULL BATTLE PLAN
description: Complete agent army deployment plan. 50+ agents across 11 teams. READ THIS if compacted/cleared. Every detail needed to resume.
type: project
---

# PHASE 5: THE AGENT ARMY — FULL BATTLE PLAN
**Created: 2026-05-07**
**Goal: Every one of 90 Lean files GENUINELY proves its docstring claims at Fields Medal level**
**Status: WAVE 1 IN PROGRESS**

## THE PROBLEM (from adversarial peer review)
- 90 files build clean (0 sorry) but many theorems prove LESS than docstrings claim
- HasMassGap was trivially constructible from any positive real — FIXED (now has eigenvalue set)
- GaugeEmbedding used `finrank - 1` not TracelessMatrix — FIXED (now uses rank-nullity)
- OSVerification.os3_symmetry = `4! = 24` (nothing to do with OS symmetry)
- WightmanVerification.w4_locality = `4! = 24` (nothing to do with locality)
- ConnesAxioms.has_chirality = `True` (vacuous)
- No actual Lie algebra embeddings, spectral theory, distributions, measure theory, representations
- Peer review results: `lean_verify/PEER_REVIEW_RESULTS.md`

## WHAT'S ALREADY DONE
- [x] Phase 2 committed + pushed: commit 0ab9c7c (Bitcoin stamped)
- [x] HasMassGap upgraded: eigenvalues, vacuum_in_spectrum, spectral_gap_property, gap_achieved
- [x] GaugeEmbedding references TracelessMatrix (genuine rank-nullity)
- [x] PaperF builds: 2807 jobs, 0 errors
- [x] GaussianMeasure.lean — BUILT ✅ (Wick's theorem, moment bounds, OS5)
- [x] ReflectionPositivity.lean — BUILT ✅ (genuine OS2, factorisation, faithfulness)
- [x] RepDecomposition.lean — BUILT ✅ (Pati-Salam 4→3⊕1, fermion decomposition)

## WAVE 1: Core Infrastructure (6 teams, deployed)

| # | File | Team | Status | What It Proves |
|---|------|------|--------|---------------|
| 1 | LieAlgebraEmbedding.lean | LIEALG | BUILDING | su(3)⊕su(2)⊕u(1) → su(4) as genuine linear map |
| 2 | TransferMatrix.lean | SPECTRAL | BUILDING | Spectral gap → mass gap via transfer matrix formalism |
| 3 | GaussianMeasure.lean | GAUSSIAN | DONE ✅ | Moment bounds, Wick counting, Gaussian domination |
| 4 | ReflectionPositivity.lean | REFLECTION | DONE ✅ | OS2 from exp(-S) factorisation, faithfulness, squares |
| 5 | RepDecomposition.lean | REPTHEORY | DONE ✅ | Fin 4 → ℂ ≅ (Fin 3 → ℂ) × (Fin 1 → ℂ), 96 = 3×32 |
| 6 | BakryEmeryGap.lean | BAKRYEMERY | BUILDING | Quadratic potential → spectral gap = 2/Λ² |

## WAVE 2: Deep Proofs (4 teams, PLANNED — deploy after Wave 1 completes)

### Team OSUPGRADE (4 agents)
- Upgrade OSVerification with genuine Equiv.Perm permutation group
- Strengthen os3 to reference actual symmetry group, not just factorial
- Add os2_square_nonneg for genuine reflection positivity
- Add moment bounds using GaussianMeasure infrastructure

### Team WIGHTMANUPGRADE (4 agents)
- Upgrade WightmanVerification with genuine content
- w4_locality: genuine commutativity/locality condition
- w5_completeness: genuine cyclicity/completeness condition
- Connect to ReflectionPositivity infrastructure

### Team CONNESUPGRADE (4 agents)
- Fix ConnesAxioms.has_chirality from `True` to genuine grading operator constraint
- Add KO-dimension theory (genuine mod-8 periodicity)
- Strengthen algebra_dim to use TracelessMatrix
- Build genuine Morita equivalence machinery if feasible

### Team CLASSIFICATION (4 agents)
- Strengthen CascadeUniqueness with Lie algebra infrastructure
- Use LieAlgebraEmbedding to prove classification involves actual algebras
- Build genuine Skolem-Noether connection: matrix automorphisms = gauge group
- Prove the uniqueness is about ALGEBRAS not just dimensions

## WAVE 3: Downstream Upgrade + Review (3 teams, PLANNED)

### Team ALLFILES (8 agents)
Each agent handles ~10 files. For EACH file:
1. Replace arithmetic proxies with genuine theorem references from Wave 1-2 infrastructure
2. Update docstrings to be HONEST but NOT DOWNGRADED
3. Pattern: "This proves X WITHIN the cascade framework, conditional on Y being verified"
4. Build each file, verify 0 sorry

### Team PEERREVIEW (12 agents)
Every file reviewed by 2 independent agents:
- Grade every theorem A/B/C/D
- Flag remaining proxies
- Check docstring accuracy
- All C/D findings fixed immediately

### Team STAMP (2 agents)
- Git commit all changes
- Git push for Bitcoin timestamp
- Verify Bitcoin timestamp received
- Update MATHS_ORG_STATE.md with final state

## NEW INFRASTRUCTURE FILES (to be added to lakefile.toml PaperF roots)
```
"LieAlgebraEmbedding",     -- su(n) embedding maps (Wave 1)
"TransferMatrix",           -- spectral gap → mass gap (Wave 1)
"GaussianMeasure",          -- moment bounds + Wick (Wave 1) ✅
"ReflectionPositivity",     -- OS2 genuine (Wave 1) ✅
"RepDecomposition",         -- Pati-Salam + fermions (Wave 1) ✅
"BakryEmeryGap",           -- Bakry-Emery spectral gap (Wave 1)
```

## THE PROOF CHAIN (what we're building)
```
CascadeData (Λ > 0, internal_gap = 2/Λ²)
  → BakryEmeryGap: quadratic potential V=Tr(D²/Λ²) → spectral gap = 2/Λ²
  → TransferMatrix: spectral gap → transfer matrix eigenvalue bound exp(-Δ)
  → HasMassGap: spectral gap → mass gap with eigenvalue set
  → OSVerification:
      OS1: Euclidean group E(4) dim 10 (genuine)
      OS2: ReflectionPositivity (factorisation + positivity)
      OS3: Equiv.Perm symmetry (genuine permutation group)
      OS4: Cluster decay from spectral gap (genuine exp_lt_one_iff)
      OS5: GaussianMeasure domination (genuine moment bounds)
  → WightmanVerification: OS reconstruction → Wightman QFT
  → GaugeEmbedding: LieAlgebraEmbedding (su(3)⊕su(2)⊕u(1) → su(4))
  → RepDecomposition: fermion content forced (96 = 3×32)
  → CascadeUniqueness: n=4 is the UNIQUE solution
  → cascade_millennium_chain: the complete theorem
```

## KEY COMMANDS
```bash
cd /Users/ekramalam/convergence-codex/lean_verify && lake build PaperF
cd /Users/ekramalam/convergence-codex/lean_verify && lake build LogosVerify
```

## KEY PRINCIPLES (NON-NEGOTIABLE)
1. NEVER downgrade claims — upgrade the math to reach the claim
2. 0 sorry everywhere
3. Genuine Mathlib proofs (no native_decide, no boolean encoding)
4. Build ONE file at a time, verify, then move on
5. Survive compaction — all state persisted in this file
6. Go beyond Mathlib if needed — build custom Lean 4 libraries

## STATE FILE
Canonical state: `lean_verify/MATHS_ORG_STATE.md` (update after each wave)
