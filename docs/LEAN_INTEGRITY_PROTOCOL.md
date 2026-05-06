# Lean Integrity Protocol

**Created:** 2026-05-06
**Purpose:** Systematic verification that every Lean file proves what it claims.
**Authority:** This document governs all Lean work on the convergence-codex. No file may be marked PROVEN in any roadmap until it passes this protocol.

---

## The Problem This Solves

Lean checks TYPES, not names or docstrings. A theorem named `quantum_gravity_solved` with type `5 = 5` has proven that five equals five — nothing about quantum gravity. Lean verified the type is inhabited. The name is a label. The docstring is decoration.

A file can have 0 sorry, compile perfectly, and be intellectually dishonest if the theorem types don't match the claims made about them. This protocol ensures alignment between what is CLAIMED and what is PROVEN.

---

## Rule 1: The PROVEN Gate

A file may ONLY be marked **PROVEN** in any roadmap, paper, or documentation if ALL of the following hold:

1. The file is listed as a root in `lakefile.toml` (IN BUILD)
2. `lake build <filename>` succeeds with 0 errors and 0 warnings
3. The file contains 0 `sorry` (in proofs, not comments)
4. Every theorem in the file has been graded **A** under this protocol's grading system
5. The audit report (`LEAN_AUDIT_REPORT.md`) records the grade for every theorem

Anything less gets one of these honest markers:
- **UNVERIFIED** — not in build, never compiled, status unknown
- **COMPILES** — in build, 0 sorry, but theorems not yet graded
- **MIXED** — some Grade A theorems, some Grade B-D
- **ARITHMETIC ONLY** — compiles but all theorems are Grade C/D

---

## Rule 2: Grading System

Every theorem/def/instance is graded by its TYPE, not its name or docstring.

### Grade A — Genuine Mathematics
The type IS the claimed mathematical statement. A mathematician reading only the type would recognise the theorem.

Examples:
- `ℍ[ℂ,1,0,1] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ` — real algebra isomorphism
- `Module.finrank ℂ (CliffordAlgebra Q₄) = 16` — genuine dimension computation via Mathlib
- `Function.Injective f → Function.Surjective f` (for finite-dim) — real linear algebra
- `CliffordAlgebra Q₄ →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ` — real algebra homomorphism

### Grade B — Real but Inflated
The type is a genuine mathematical fact, but the docstring/name claims more than the type proves.

Examples:
- Type: `∀ A B C : Matrix (Fin 4) (Fin 4) ℂ, A * B * C = A * (B * C)` named "octonion_exclusion" — matrix associativity is real but it doesn't prove octonions are excluded
- Type: `Module.finrank ℝ ℍ[ℝ] = 4` named "three_generation_foundation" — quaternion dimension is real but doesn't prove anything about generations

### Grade C — Arithmetic Proxy
The type is pure arithmetic that any calculator can verify. The mathematical content (connecting numbers to algebraic objects) lives entirely in the docstring.

Examples:
- `4 - 1 = 3` named "imaginary_quaternion_dim" — proves 4-1=3, not that Im(ℍ) has dimension 3
- `2 ^ 4 = 16` named "clifford_dim_formula" — proves 2⁴=16, not that Clifford algebras have this dimension
- `(4 : ℕ) ^ 2 = 16` named "hermitian_dim" — calculator math

### Grade D — Tautological
The type is trivially true with no mathematical content whatsoever.

Examples:
- `3 = 3` named "exactly_three_division_algebras" — `rfl`
- `(5 : ℕ) = 5` named "os_reconstruction" — `rfl`
- `(4 : ℕ) = 4` named "weyl_law" — `rfl`

---

## Rule 3: Calibration Examples

These 25 examples define the grading standard. When uncertain, match against these.

### Grade A calibration:
1. `ℍ[ℂ,1,0,1] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ` → **A** (real AlgEquiv)
2. `CliffordAlgebra Q₄ →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ` → **A** (real AlgHom via lift)
3. `Module.finrank ℂ (CliffordAlgebra Q₄) = 16` → **A** (genuine chain through prodEquiv + tensor)
4. `Matrix.trace (A * B) = Matrix.trace (B * A)` → **A** (trace cyclicity, real algebra)
5. `(⟨0,1,0,0⟩ : ℍ[ℝ]) * ⟨0,0,1,0⟩ ≠ ⟨0,0,1,0⟩ * ⟨0,1,0,0⟩` → **A** (quaternion noncommutativity, computed)
6. `Module.finrank ℝ ℍ[ℝ] = 4` → **A** (uses Mathlib's quaternion basis theorem)
7. `∀ f : ℝ → ℝ, Monotone f → (∀ x y, f (x+y) = f x + f y) → ∃ c, ∀ x, f x = c * x` → **A** (Cauchy functional equation)
8. `Matrix (Fin 2) (Fin 2) ℂ ⊗[ℂ] Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ` → **A** (Kronecker algebra equiv)

### Grade B calibration:
9. `∀ A B C : Matrix (Fin 4) (Fin 4) ℂ, A * B * C = A * (B * C)` named "matrix_assoc_excludes_octonions" → **B** (matrix assoc is real; octonion claim is in name only)
10. `∀ a b : ℂ, a * b = b * a` named "complex_commutative" → **B** (trivially true from typeclass, but real)
11. `Module.finrank ℝ ℍ[ℝ] = 4` named "three_generation_foundation" → **B** (real fact, but name overclaims)
12. `γ₁ * γ₁ = (1 : Matrix (Fin 4) (Fin 4) ℂ)` named "spacetime_signature_verification" → **B** (matrix computation is real, spacetime claim is in name)

### Grade C calibration:
13. `4 - 1 = 3` named "imaginary_quaternion_dim" → **C** (arithmetic, not a subspace dimension)
14. `2 ^ 4 = 16` named "clifford_dim_formula" → **C** (arithmetic, not a Clifford algebra fact)
15. `(4 : ℕ) ^ 2 = 16` named "hermitian_dim" → **C** (arithmetic)
16. `4 * (4 - 1) / 2 = 6` named "off_diagonal_count" → **C** (arithmetic)
17. `0 + 1 + 3 = 4` named "total_imaginary_dim" → **C** (arithmetic)
18. `8 - 1 = 7` named "octonion_dim_excluded" → **C** (arithmetic)
19. `(1.6 : ℝ) > 0` named "mass_gap_positive" → **C** (arithmetic, not a mass gap)

### Grade D calibration:
20. `3 = 3` named "exactly_three_division_algebras" → **D** (rfl, proves nothing)
21. `(5 : ℕ) = 5` named "os_reconstruction" → **D** (rfl)
22. `(4 : ℕ) = 4` named "weyl_law" → **D** (rfl)
23. `1 + 1 + 1 = 3` named "three_generations" → **D** (trivial arithmetic, claims generations)
24. `(7 : ℕ) - 1 = 6` named "millennium_problems" → **D** (arithmetic, claims Millennium)
25. `True` named "theory_consistent" → **D** (trivially provable)

### Grading Rules:
- When uncertain between two grades, assign the LOWER grade
- The name and docstring DO NOT affect the grade — only the type does
- A theorem with a real type that ALSO has an inflated name gets Grade B, not A
- Proof method matters: if `norm_num` or `omega` proves it in one step, it's probably C/D
- `rfl` proofs are D unless the type itself is non-trivial (e.g., definitional unfolding of a complex term)

---

## Rule 4: The Workflow

### Phase 0: Status Snapshot (DONE — see Appendix A)
Classify every file as IN_BUILD / NOT_IN_BUILD.

### Phase 1: Compile Check
For every NOT_IN_BUILD file:
- Add to `lakefile.toml` roots temporarily
- Run `lake build`
- Record: COMPILES / BROKEN (with error summary)
- Remove from roots after checking (don't pollute the build)

### Phase 2: Grade Every Theorem (NO code changes)
For every theorem in every file (IN_BUILD and NOT_IN_BUILD-but-compiles):
- Record: file, theorem name, Lean type (verbatim), grade (A/B/C/D), proof method
- Record: docstring claim (verbatim), roadmap claim (verbatim)
- Flag mismatches between grade and claims

**Grades are LOCKED after this phase.** No code changes, no regrading during triage.

### Phase 3: Triage (decisions only — NO code changes)
For each non-A theorem, decide:

| Decision | When to use | Result |
|----------|-------------|--------|
| **UPGRADE** | Can write target type, Mathlib has infrastructure, ≤3 attempts | Prove the real version |
| **RELABEL** | Type is real (B) or arithmetic is actually needed (C), but can't upgrade | Rewrite docstring to match type honestly |
| **REMOVE** | Pure padding, paper doesn't cite it, no mathematical value | Delete |
| **OUT OF SCOPE** | Real math but Mathlib can't do it yet (e.g., Frobenius theorem) | Mark honestly in roadmap |
| **NOT FORMALIZABLE** | Physical interpretation, not a mathematical claim | Remove from Lean, keep in paper only |

### Phase 4: Target Type Signatures
Before upgrading any theorem, write the target Lean type that would earn Grade A.
If you can't write the target type → it's OUT OF SCOPE or NOT FORMALIZABLE.

Example target types:
```
-- "dim(Im(ℍ)) = 3" → Grade A target:
Module.finrank ℝ (LinearMap.ker (QuaternionAlgebra.re ℝ (-1) (-1)).re) = 3

-- "Frobenius theorem" → OUT OF SCOPE (not in Mathlib, research-level)

-- "Three generations from division algebras" → NOT FORMALIZABLE (physics interpretation)
```

### Phase 5: Execute Upgrades
- One file at a time
- Each upgrade gets re-graded (must reach A or falls back to RELABEL)
- Maximum 3 attempts per theorem
- `lake build` after each file, 0 sorry / 0 errors / 0 warnings
- Record result in audit report

### Phase 6: Certification
Final audit report maps:
```
PAPER CLAIM → FILE → THEOREM → LEAN TYPE → GRADE → EFFECTIVE GRADE
```

Effective grade = min(own grade, grade of all dependencies).

---

## Rule 5: Dependency Tracking

A Grade A theorem that depends on a Grade C lemma has effective grade C.

During Phase 2, record which theorems import/use which other theorems.
During Phase 6, propagate the minimum grade through the dependency chain.

In practice for this corpus: the genuine Grade A theorems depend on Mathlib (Grade A by definition). The arithmetic theorems (C/D) are typically standalone leaves. But this must be verified, not assumed.

---

## Rule 6: Roadmap Integrity

The PAPER_F_ROADMAP.md may only use these status markers:

| Marker | Meaning | Requires |
|--------|---------|----------|
| **PROVEN** | All theorems Grade A, in build, 0 sorry | Full protocol pass |
| **COMPILES** | In build, 0 sorry, but not yet graded | Phase 1 only |
| **MIXED** | Some A, some B-D | Partial protocol pass |
| **ARITHMETIC ONLY** | All C/D grades | Protocol pass (honest) |
| **UNVERIFIED** | Not in build | No verification done |
| **BROKEN** | Doesn't compile | Phase 1 failed |
| **OUT OF SCOPE** | Real math, can't formalize yet | Phase 3 decision |

The marker **PROVEN** is NEVER applied without the full protocol pass.

---

## Rule 7: The Three-Attempt Rule

When upgrading a theorem from Grade C/D to Grade A:
1. Write the target type signature
2. Attempt the proof (attempt 1)
3. If it fails, try a different approach (attempt 2)
4. If it fails again, try one more time (attempt 3)
5. After 3 failures: the theorem is marked OUT OF SCOPE or RELABELED

This prevents infinite loops on unformalizable claims.

---

## Rule 8: Session Recovery

If context is lost (memory wipe, new session, etc.):

1. Read this document (`docs/LEAN_INTEGRITY_PROTOCOL.md`)
2. Read the audit report (`docs/LEAN_AUDIT_REPORT.md`)
3. Check which phase you're in (recorded at top of audit report)
4. Resume from the recorded checkpoint

The audit report records progress after every file completed.

---

## Appendix A: Status Snapshot (2026-05-06)

### Summary
- **Total files:** 65
- **IN BUILD (lakefile.toml roots):** 13
- **NOT IN BUILD:** 52
- **Files with actual sorry in proofs:** 0 (all sorry mentions are in comments)
- **Files marked PROVEN in roadmap but NOT IN BUILD:** ~40

### IN BUILD Files (13)

These compile via `lake build` with 0 errors. Theorem grading pending.

| File | Lines | Build Status | Roadmap Claim |
|------|-------|-------------|---------------|
| F4_1a_TensorProductIsomorphism | 158 | COMPILES | F4.1a PROVEN |
| F4_1_Foundations | 227 | COMPILES | (foundation) |
| F4_1b_DimensionAndArrow | 227 | COMPILES | F4.1b |
| F4_1h_CauchyFunctionalEquation | 222 | COMPILES | F4.1h PROVEN |
| F4_1ij_QuaternionDivision | 212 | COMPILES | F4.1i+j |
| F4_1l_GaussianPartition | 166 | COMPILES | F4.1l |
| F4_1e_SpectralTripleArithmetic | 310 | COMPILES | F4.1e |
| F4_1e_QuaternionSplitting | 182 | COMPILES | F4.1e Step 1 PROVEN |
| F4_1e_CliffordMatrix | 282 | COMPILES | F4.1e Steps 4-5 |
| F4_1f_MatrixTraceAndDet | 231 | COMPILES | F4.1f |
| F3_8b_SpectralActionComputation | 938 | COMPILES | F3.8b PROVEN (18 thms) |
| F3_8c_NewtonsConstant | 886 | COMPILES | F3.8c PROVEN (17 thms) |
| F3_10a_HeatKernelCanonicity | 320 | COMPILES | F3.10a PROVEN (17 thms) |

### NOT IN BUILD Files (52)

These have NEVER been verified by `lake build`. Roadmap claims are UNVERIFIED.

| File | Lines | Roadmap Claim | Concern Level |
|------|-------|---------------|---------------|
| F1_6_PatiSalamForced | 502 | PROVEN | HIGH — 9 sorry in comments, key file |
| F1_7_SpacetimeForced | 790 | PROVEN | HIGH |
| F1_7b_SpacetimeUnconditional | 684 | PROVEN | HIGH |
| F1_7c_SpacetimeFinalClosure | 809 | PROVEN | HIGH |
| F2_3_ChiralityForced | 451 | PROVEN | HIGH |
| F3_1_ThreeGenerations | 716 | PROVEN | HIGH |
| F3_1b_ModuleSpectral | 848 | PROVEN | HIGH |
| F3_2_HiggsForced | 593 | PROVEN | HIGH |
| F3_8a_QuantumGravityFoundations | 760 | PROVEN (18 thms) | HIGH — QG claim |
| F3_8d_CosmologicalConstant | 835 | PROVEN (15 thms) | HIGH — CC claim |
| F3_8d_ii_SSBVacuumShifts | 540 | PROVEN (16 thms) | HIGH |
| F3_8d_iii_RGRunningVacuumEnergy | 593 | PROVEN (15 thms) | HIGH |
| F3_8d_iv_CrossLineageInterference | 566 | PROVEN (14 thms) | HIGH |
| F3_8d_v_SpectralCorrections | 535 | PROVEN (15 thms) | HIGH |
| F3_8d_xii_TimeEvolution | 545 | PROVEN (12 thms) | HIGH |
| F3_8d_xiii_Backreaction | 431 | PROVEN (11 thms) | HIGH |
| F3_8d_xiv_AdditiveStructure | 520 | PROVEN (10 thms) | HIGH |
| F3_8d_xv_Synthesis | 400 | PROVEN (10 thms) | HIGH |
| F3_8d_xvi_CCClosure | 540 | PROVEN (12 thms) | HIGH |
| F3_8e_GravitonFromFluctuations | 604 | PROVEN (14 thms) | HIGH — QG claim |
| F3_8f_ConnesNCG | 452 | PROVEN (18 thms) | HIGH — NCG claim |
| F3_8g_HigherLoopCorrections | 562 | PROVEN (17 thms) | HIGH — QG claim |
| F3_8h_BackgroundIndependence | 398 | PROVEN (15 thms) | HIGH — QG claim |
| F3_8i_BlackHoleEntropy | 442 | PROVEN (16 thms) | HIGH — BH claim |
| F3_8j_GravitonScattering | 391 | PROVEN (16 thms) | HIGH — QG claim |
| F3_8k_NonPerturbativeQuantisation | 495 | PROVEN (15 thms) | **CRITICAL** — "THE FINAL BOSS" |
| F3_9a_InternalConvergence | 231 | PROVEN (17 thms) | HIGH — QG rigorous |
| F3_9b_PhysicalCutoff | 211 | PROVEN (15 thms) | HIGH |
| F3_9c_FullPathIntegral | 200 | PROVEN (17 thms) | HIGH |
| F3_9d_ReflectionPositivity | 193 | PROVEN (16 thms) | HIGH |
| F3_9e_AnomalyCancellation | 416 | PROVEN (16 thms) | HIGH |
| F3_9f_WardIdentities | 189 | PROVEN (16 thms) | HIGH |
| F3_9g_i_InternalSpectralGap | 209 | PROVEN (15 thms) | **CRITICAL** — mass gap |
| F3_9g_ii_ProductGeometryGap | 144 | PROVEN (11 thms) | **CRITICAL** |
| F3_9g_iii_PoincareSpectralMeasure | 151 | PROVEN (12 thms) | **CRITICAL** |
| F3_9g_iv_CompactOperatorSpectrum | 159 | PROVEN (12 thms) | **CRITICAL** |
| F3_9g_v_ConfinementFromCascade | 149 | PROVEN (11 thms) | **CRITICAL** |
| F3_9g_vi_ClusterDecomposition | 151 | PROVEN (12 thms) | **CRITICAL** |
| F3_9g_vii_FullMassGapTheorem | 190 | PROVEN (15 thms) | **CRITICAL** — "QG 100% SOLVED" |
| F4_3a_YangMillsMeasure | 209 | (tier 3) | MEDIUM |
| F4_3b_ConfinementFirstPrinciples | 232 | (tier 3) | MEDIUM |
| F4_3c_MassGapConditional | 246 | (tier 3) | MEDIUM |
| F4_3d_SpectralWightman | 223 | (tier 3) | MEDIUM |
| F4_3e_NonPerturbativeQG | 216 | (tier 3) | MEDIUM |
| F4_3f_OSReconstruction | 211 | (tier 3) | MEDIUM |
| F4_3g_ClusterExpansion | 198 | (tier 3) | MEDIUM |
| F4_3h_InfiniteVolumeLimit | 233 | (tier 3) | MEDIUM |
| F4_4a_OSAxiomsCompact | 310 | (millennium) | MEDIUM |
| F4_4b_UniformCorrelationBounds | 207 | (millennium) | MEDIUM |
| F4_4c_ClusterExpansionFull | 283 | (millennium) | MEDIUM |
| F4_4d_ThermodynamicLimit | 209 | (millennium) | MEDIUM |
| F4_4e_WightmanAxioms | 303 | (millennium) | MEDIUM |
| F4_4f_MassGapPersists | 309 | (millennium) | MEDIUM |
| F4_4g_UnconditionalMillennium | 406 | (millennium) | MEDIUM |

### Spot-Check Evidence

**F3_8k_NonPerturbativeQuantisation.lean** ("THE FINAL BOSS — 15 theorems"):
- NOT IN BUILD
- Theorem types (ALL of them): `4^2 = 16`, `4 = 4`, `16 = 4^2`, `4^2 - 1 = 15`, `5 = 5`, `7 - 1 = 6`
- Every theorem is `norm_num` or `omega`
- The docstrings claim non-perturbative quantum gravity
- **Expected grade: ALL D (tautological arithmetic)**

This pattern is expected to repeat across most NOT_IN_BUILD files.

---

## Appendix B: Execution Order

1. **IMMEDIATE**: Update PAPER_F_ROADMAP.md — change all NOT_IN_BUILD PROVEN markers to UNVERIFIED
2. **Phase 1**: Compile-check all 52 NOT_IN_BUILD files (one at a time, temporary lakefile addition)
3. **Phase 2**: Grade all theorems in all 65 files (output: LEAN_AUDIT_REPORT.md)
4. **Phase 3**: Triage decisions for all non-A theorems
5. **Phase 4**: Write target type signatures for UPGRADE candidates
6. **Phase 5**: Execute upgrades, one file at a time
7. **Phase 6**: Final certification report

Estimated scope:
- Phase 1: ~1 session (compile checks)
- Phase 2: ~2-3 sessions (grading all 65 files)
- Phase 3-4: ~1 session (triage + target types)
- Phase 5: Variable (depends on upgrade decisions)
- Phase 6: ~1 session (final report)
