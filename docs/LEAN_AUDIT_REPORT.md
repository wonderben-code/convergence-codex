# LEAN FORMALISATION CORPUS — HONEST AUDIT REPORT

**Date:** 6 May 2026
**Auditor:** Claude Opus 4.6 (at the request of the corpus author)
**Scope:** All .lean files in convergence-codex/lean_verify/ (excluding Mathlib)
**Method:** Automated pattern detection across all files + manual reading of every file in the corpus
**Tone:** Adversarial. No softening. The goal is truth.

---

## 1. FILE COUNT

| Category | Count |
|----------|-------|
| Root-level content files | 23 |
| Paper F files (paper_f/) | 67 |
| Infrastructure (Test, LogosVerify) | 3 |
| **Total content files** | **90** |

The corpus claims "~49 files" in some documents. The actual count is **90 content files**.

---

## 2. THEOREM COUNT

| Metric | Count |
|--------|-------|
| `theorem` statements | 1,339 |
| `def` / `noncomputable def` | 80 |
| `instance` declarations | 7 |
| **Total formal declarations** | **~1,426** |

The corpus claims "1,035 theorems" in Paper F documentation. The actual theorem count is **1,339**. The discrepancy may be due to root-level files not being counted, or differing count methods.

---

## 3. PROOF TACTIC ANALYSIS

This is the most important section. What do the proofs actually consist of?

| Tactic | Occurrences | What it does | Assessment |
|--------|-------------|-------------|------------|
| `by norm_num` | **1,091** | Decides closed-form arithmetic: `4*4=16`, `0<2` | **Arithmetic** |
| `by omega` | **1,041** | Decides natural number arithmetic: `4^2-1=15` | **Arithmetic** |
| `exp_pos` / `exp_zero` / `exp_add` / `exp_lt_one_iff` | 192 | Exponential function properties | **Simple analysis** |
| `Fintype.card_fin` / `finrank` / `TensorProduct` | 172 | Dimension calculations, tensor products | **Partially substantive** |
| `AlgEquiv` / `AlgHom` / `≃ₐ` / `→ₐ` | 145 | Algebra isomorphisms/homomorphisms | **Substantive** |
| `Matrix.*` / `trace_*` / `det_*` | 144 | Matrix trace, determinant, multiplication | **Substantive** |
| `positivity` | 50 | Proves positivity of composed expressions | **Simple** |
| `by ring` | 37 | Ring identity proofs | **Arithmetic** |
| `sub_self` / `mul_pos` / `lt_min` / `le_of_lt` / `pow_pos` / `sq_nonneg` | 33 | Simple real analysis lemmas | **Simple analysis** |
| `by linarith` | 14 | Linear arithmetic over ordered fields | **Arithmetic** |
| `by simp` | 14 | Simplification | **Varies** |
| `:= rfl` | 11 | Definitional equality | **Trivial** |
| `by nlinarith` | 5 | Nonlinear arithmetic | **Arithmetic** |

### Key finding

**81% of theorem proofs (1,091 / 1,339) use `norm_num` as their primary proof technique.** `norm_num` is Mathlib's tactic for deciding closed-form arithmetic. It proves goals like `4 * 4 = (16 : ℕ)` or `(0 : ℝ) < 2`. These are valid propositions — `0 < 2` is genuinely true — but they are arithmetic facts, not the physics claims their theorem names suggest.

---

## 4. CLASSIFICATION: WHAT THE PROOFS ACTUALLY PROVE

### 4A. SUBSTANTIVE files (~15 files, ~17% of corpus)

These files use real Mathlib algebraic structures and prove genuine mathematical theorems about matrices, tensor products, algebra isomorphisms, or categorical structures.

**Example — `F4_1a_TensorProductIsomorphism.lean`** (SUBSTANTIVE):
```lean
noncomputable def cascadeTensorIso :
    Matrix (Fin 2) (Fin 2) ℂ ⊗[ℂ] Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ]
    Matrix (Fin 4) (Fin 4) ℂ :=
  (kroneckerAlgEquiv (Fin 2) (Fin 2) ℂ).trans
    (reindexAlgEquiv ℂ ℂ finProdFinEquiv)
```
This is a genuine algebra isomorphism proven via Mathlib's `kroneckerAlgEquiv` and `reindexAlgEquiv`. The type signature references real mathematical objects. The proof invokes real Mathlib lemmas.

**Example — `F4_1f_MatrixTraceAndDet.lean`** (SUBSTANTIVE):
```lean
theorem trace_commutative {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) :
    trace (A * B) = trace (B * A) :=
  Matrix.trace_mul_comm A B
```
Genuine Mathlib theorem about matrix trace cyclicity, parameterised over arbitrary index types.

**Substantive files include:**
- `F4_1a_TensorProductIsomorphism.lean` — Real algebra isomorphisms (kroneckerAlgEquiv)
- `F4_1f_MatrixTraceAndDet.lean` — Real matrix trace/determinant properties
- `F2_3_ChiralityForced.lean` — Uses AlgEquiv, algebra homomorphisms
- `EmergenceTheorem.lean` — Uses TensorProduct, AlgEquiv, function space arguments
- `ThreeLineages.lean` — Uses TensorProduct, AlgEquiv, unitaryGroup
- `GaugeGroupSelection.lean` — Uses AlgEquiv, algebra structure
- `GravityLineage.lean` — Uses SpecialLinearGroup, group homomorphisms
- `SeedForced.lean` — Uses Equiv, function space cardinality arguments
- `NothingToSeed.lean` — Uses Equiv, function space arguments
- `F4_1e_QuaternionSplitting.lean` — Uses Quaternion from Mathlib
- Parts of `QuantumLineage.lean`, `PreferredDecomposition.lean`

### 4B. ARITHMETIC files (~57 files, ~63% of corpus)

These files have theorem names suggesting deep physics, but the type signatures are conjunctions of arithmetic facts. The docstrings describe the physics; the Lean code proves numbers.

**Example — `F3_9g_vii_FullMassGapTheorem.lean`** (ARITHMETIC):

Docstring says: "Step 1 (F3.9g_i): Internal space has gap. Bakry-Émery: Hess(S) ≥ (2/Λ²)I → λ₁ ≥ 2/Λ²."

Actual theorem:
```lean
theorem step1_internal_gap :
    4 * 4 = (16 : ℕ) ∧        -- Herm₄ ≅ ℝ¹⁶
    (0 : ℝ) < 2               -- gap = 2/Λ² > 0 (normalised)
    := ⟨by norm_num, by norm_num⟩
```

The theorem is named `step1_internal_gap` and the docstring describes Bakry-Émery theory. The Lean code proves `4*4 = 16 ∧ 0 < 2`.

**Example — `F4_4g_UnconditionalMillennium.lean`** (ARITHMETIC):
```lean
theorem millennium_prize_solved :
    ((5 : ℕ) = 5) ∧ ((0 : ℝ) < 2) ∧ (4 ^ 2 - 1 = (15 : ℕ)) ∧
    ((96 : ℕ) > 0) ∧ (11 * 3 - 2 * 6 = (21 : ℕ)) ∧
    (8 + 3 + 1 = (12 : ℕ)) ∧ ((0 : ℕ) = 0) ∧ ((0 : ℕ) = 0) ∧
    (0 < exp (-(16 : ℝ))) ∧ (exp (-(16 : ℝ)) < 1) ∧
    (4 * 4 = (16 : ℕ)) ∧ exp (0 : ℝ) = 1 :=
  ⟨rfl, by norm_num, by norm_num, by norm_num, by norm_num,
   by norm_num, rfl, rfl, exp_pos _, by rw [exp_lt_one_iff]; norm_num,
   by norm_num, exp_zero⟩
```

This theorem is called `millennium_prize_solved`. It proves that 5=5, 0<2, 15=15, 96>0, 21=21, 12=12, 0=0, exp(-16)>0, exp(-16)<1, 16=16, and exp(0)=1.

### 4C. TRIVIAL patterns (~18+ files contain `True`/`trivial`)

Many files use `True` as hypothesis types, conclusion types, or standalone theorems, making the formal statements content-free. This is **more widespread than initially estimated** — a thorough per-file audit found `True`/`trivial` content in at least 18 files across the corpus.

**Example — `F4_3d_SpectralWightman.lean`** (`True` hypotheses):
```lean
theorem os_reconstruction_conditional
    (_ : True)          -- OS1: Euclidean covariance
    (_ : True)          -- OS2: Reflection positivity
    (_ : True)          -- OS3: Symmetry
    (_ : True)          -- OS4: Cluster property
    (_ : True)          -- OS5: Growth bound
    :
    (5 : ℕ) = 5 ∧ (96 : ℕ) > 0
    := ⟨rfl, by norm_num⟩
```

**Example — `F3_8d_iv_CrossLineageInterference.lean`** (`True` conjuncts):
```lean
theorem heat_kernel_factorisation : True ∧ True ∧ True ∧ True
    := ⟨trivial, trivial, trivial, trivial⟩
```
A theorem claiming "heat kernel factorisation" that proves `True ∧ True ∧ True ∧ True`.

**Example — `F3_2_HiggsForced.lean`** (`True` as conclusion):
```lean
theorem prediction_mass_ratio : True := trivial
```
Claims to be a mass ratio prediction. Proves `True`.

**Files containing `True`/`trivial` include:** F1_7b, F1_7c, F2_3 (one `True` among substantive), F3_1, F3_1b, F3_2, F3_8a, F3_8b, F3_8c, F3_8d, F3_8d_ii, F3_8d_iii, F3_8d_iv, F3_8d_v, F3_8d_xiv, F3_8d_xv, F3_8e, F4_3d.

**Note:** Many of these files are classified ARITHMETIC above because `True`/`trivial` appears as one field in a conjunction that is otherwise arithmetic. The `True` pattern is scattered throughout the arithmetic files rather than concentrated in dedicated "trivial" files.

### 4D. MIXED files (~15 files, ~17% of corpus)

Files containing both substantive and arithmetic theorems. Typically a few genuine Mathlib invocations (exp_add, Complex.normSq_nonneg, Real.log_neg, Nonempty algebra hom assertions) surrounded by arithmetic filler.

**Example — `F3_9d_ReflectionPositivity.lean`** (MIXED):
```lean
-- GENUINE: uses Complex.normSq_nonneg from Mathlib
theorem reflection_positivity_key_fact (z : ℂ) :
    0 ≤ Complex.normSq z :=
  Complex.normSq_nonneg z

-- GENUINE: uses exp_add from Mathlib
theorem action_factorisation (S_plus S_minus : ℝ) :
    exp (-(S_plus + S_minus)) = exp (-S_plus) * exp (-S_minus) := by
  rw [neg_add, exp_add]

-- ARITHMETIC: docstring says "OS reconstruction", proves 5=5
theorem os_reconstruction_outputs :
    (5 : ℕ) = 5 ∧ (0 : ℝ) ≤ 0 := ⟨rfl, le_refl 0⟩
```

**Mixed files include:**
- `F1_6_PatiSalamForced.lean` — Genuine `Nonempty` AlgEquiv assertions + arithmetic
- `F3_9d_ReflectionPositivity.lean` — `Complex.normSq_nonneg`, `exp_add`, `Real.log_neg` + arithmetic
- `F3_9g_vi_ClusterDecomposition.lean` — `exp_lt_one_iff`, `exp_le_exp` + arithmetic
- Parts of root-level files (`GaugeGroupSelection.lean`, `PreferredDecomposition.lean`, etc.)
- Several F4 files with some matrix or algebra content mixed with arithmetic

---

## 5. PATTERNS FLAGGED

### Pattern 1: Misleading theorem names (WIDESPREAD)

Across the corpus, theorem names suggest claims the type signatures do not express:

| Theorem name | Suggests | Actually proves |
|-------------|----------|----------------|
| `millennium_prize_solved` | Yang-Mills mass gap solved | 5=5 ∧ 0<2 ∧ 15=15 ∧ ... |
| `mass_gap_persists_master` | Mass gap survives infinite volume | 0<2 ∧ 16=16 ∧ 21=21 ∧ ... |
| `step1_internal_gap` | Bakry-Émery spectral gap | 4*4=16 ∧ 0<2 |
| `gauge_group_forced` | SU(4) gauge group uniquely determined | 4^2-1=15 |
| `confinement_mass` | Confinement generates mass scale | 11*3-2*6=21 ∧ 0<exp(-1) |
| `physical_gap` | Physical mass gap Δ > 0 | min(a,b)>0 if a>0 and b>0 |
| `unconditional_gap` | No axioms needed for gap | 0=0 ∧ 0<2 ∧ 21=21 |
| `cascade_resolves_gap_problem` | Cascade solves YM gap | 4=4 ∧ 16=16 ∧ 0<2 |
| `os_reconstruction_conditional` | OS axioms → Wightman QFT | True → 5=5 ∧ 96>0 |
| `heat_kernel_factorisation` | Heat kernel factorises | True ∧ True ∧ True ∧ True |
| `prediction_mass_ratio` | Higgs mass ratio prediction | True |
| `spectral_theorem_3x3` | Spectral theorem for 3×3 | 3=3 ∧ 3=3 ∧ 3=3 |
| `qg_100_percent_solved` | Quantum gravity 100% solved | 10+1=11 |
| `six_ingredients_complete` | All 6 mass gap ingredients proven | 1+1+1+1+1+1=6 |
| `a1_su4_anomaly_cancellation` | SU(4) anomaly cancellation | 2+(-2)=0 |
| `b2_entropy_coefficient` | Black hole entropy coefficient | 16/4=4 |

This pattern is present in the majority of files. The theorem names are aspirational labels for what the proof SHOULD prove, not descriptions of what it DOES prove.

### Pattern 2: True/trivial standing in for real content (WIDESPREAD)

Initially appeared localised to `F4_3d_SpectralWightman.lean`. Full audit revealed **`True`/`trivial` in 18+ files** across the corpus, in three forms:
- `(_ : True)` hypotheses standing in for axioms (F4_3d)
- `theorem name : True := trivial` — content-free standalone theorems (F3_2, F3_8a, etc.)
- `True` conjuncts within arithmetic conjunctions: `... ∧ True ∧ ...` (F3_8d_iv, F3_8d_xiv, etc.)
- `Bool` fields set to `false` with physics-sounding names: `manifold_assumed = false` (F3_8h)

### Pattern 3: Nonempty assertions (PARTIALLY SUBSTANTIVE)

Several files use `Nonempty (SomeType)` where `SomeType` is a genuine algebraic object:
```lean
Nonempty (Matrix (Fin 4) (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
Nonempty ((Matrix (Fin 2) (Fin 2) ℂ ⊗[ℂ] Matrix (Fin 2) (Fin 2) ℂ) ≃ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
```
These ARE substantive — they assert the existence of specific algebra homomorphisms or equivalences between concrete matrix algebras. The proof must construct the homomorphism. This pattern appears in ~10 files and represents genuine content.

### Pattern 4: Imports never used for their purpose (WIDESPREAD)

Many files import `Mathlib.Analysis.SpecialFunctions.ExpDeriv` or `Mathlib.Analysis.InnerProductSpace.Spectrum` but only use `exp_pos` or `norm_num`. The imports suggest sophisticated analysis but the proofs don't touch the imported structures.

---

## 6. LOAD-BEARING ASSESSMENT: Major Claims

For each major claim of the corpus, which file(s) supposedly establish it and what do they actually prove?

### Claim: Standard Model gauge group derived from cascade

| File | What it claims | What it actually proves | Assessment |
|------|---------------|----------------------|------------|
| `F1_6_PatiSalamForced.lean` | Pati-Salam SU(4)×SU(2)_L×SU(2)_R forced | Arithmetic: 4^2-1=15, 2^2-1=3, etc. Plus some genuine `Nonempty` algebra hom assertions | **MIXED** |
| `GaugeGroupSelection.lean` | Gauge group uniquely selected | Mix of arithmetic and genuine `Nonempty (AlgEquiv ...)` statements | **MIXED** |
| `F4_1a_TensorProductIsomorphism.lean` | M₂⊗M₂ ≃ M₄ (cascade step) | **Genuine algebra isomorphism via Mathlib** | **SUBSTANTIVE** |

The cascade step (M₂⊗M₂ ≅ M₄) is genuinely proven. The gauge group decomposition (su(4) → su(3)⊕su(2)⊕u(1)) is proven only as arithmetic (4^2-1=15, etc.), not as actual Lie algebra decomposition.

### Claim: Three generations of fermions

| File | What it claims | What it actually proves | Assessment |
|------|---------------|----------------------|------------|
| `F3_1_ThreeGenerations.lean` | 3 generations from quaternionic structure | Arithmetic: dim(Im(ℍ))=3 as `4-1=3` | **ARITHMETIC** |
| `F4_1ij_QuaternionDivision.lean` | Quaternion division algebra properties | Mix — some genuine Quaternion usage, mostly arithmetic | **MIXED** |

The claim that quaternionic structure forces exactly 3 generations is encoded as `4-1=3`, not as a genuine proof about complex structures on quaternionic modules.

### Claim: Mass gap Δ > 0

| File | What it claims | What it actually proves | Assessment |
|------|---------------|----------------------|------------|
| `F3_9g_vii_FullMassGapTheorem.lean` | Mass gap theorem | 4*4=16 ∧ 0<2 ∧ exp(-1)>0 | **ARITHMETIC** |
| `F4_4f_MassGapPersists.lean` | Mass gap persists in infinite volume | 0<2 ∧ 16=16 ∧ 21=21 ∧ exp(-x)>0 | **ARITHMETIC** |
| `F4_4g_UnconditionalMillennium.lean` | Millennium Prize solved | 5=5 ∧ 0<2 ∧ 15=15 ∧ 96>0 ∧ ... | **ARITHMETIC** |

**The mass gap claim is entirely arithmetic.** No spectral theory, no operator theory, no functional analysis. The theorems verify numerical values that APPEAR in the argument (dimensions, positivity of constants) but do not formalize the argument itself.

### Claim: Zero free parameters

| File | What it claims | What it actually proves | Assessment |
|------|---------------|----------------------|------------|
| `F4_1h_CauchyFunctionalEquation.lean` | Cauchy equation → unique spectral function | Arithmetic: exp(a+b)=exp(a)*exp(b) (which is `exp_add`, a known Mathlib fact) | **ARITHMETIC** (but uses a real Mathlib lemma) |

The Cauchy functional equation result uses `exp_add` from Mathlib — this IS a real mathematical fact. But the full theorem (unique monotone measurable solution to f(x+y)=f(x)f(y) is exponential) is NOT proven. Only the additive property of exp is verified.

### Claim: Theory of Everything

| File | What it claims | What it actually proves | Assessment |
|------|---------------|----------------------|------------|
| `GToECoherence.lean` | Full ToE coherence | Mix of Nonempty algebra homs + arithmetic | **MIXED** |
| `SMCompleteness.lean` | Standard Model completeness | Arithmetic: dimension counts, particle counts | **ARITHMETIC** |

---

## 7. CROSS-FILE DEPENDENCY CHECK

The substantive files (F4_1a, F4_1f, etc.) are **self-contained** — they import only from Mathlib, not from the arithmetic files. This means:

- The substantive results stand on their own
- The arithmetic files do not contaminate the substantive files
- But the arithmetic files ALSO don't benefit from the substantive files — the "mass gap" files don't import or use the tensor product isomorphism

The corpus does not have a genuine proof chain where substantive results feed into downstream theorems. The substantive files and arithmetic files are largely independent.

---

## 8. AGGREGATE SUMMARY

### Counts

| Classification | Files | % | Theorems (est.) |
|---------------|-------|---|-----------------|
| SUBSTANTIVE | ~15 | ~17% | ~150-200 |
| MIXED | ~15 | ~17% | ~150-200 |
| ARITHMETIC | ~57 | ~63% | ~900-1,000 |
| TRIVIAL (True fields) | ~3 | ~3% | ~20-30 |

### Claimed vs actual theorem content

- **Claimed:** "1,035+ machine-verified theorems proving the Theory of Everything"
- **Actual with non-trivial type signatures:** ~200-250 theorems (~15-19% of total)
- **Actual with genuinely substantive proofs (real Mathlib structural theorems):** ~100-150
- **Arithmetic facts verified:** ~900-1,000

### Honest summary

**The majority of the Lean formalisation corpus — approximately 63% of files and ~70% of theorems — consists of arithmetic facts (4×4=16, 0<2, 11×3−2×6=21, exp(−x)>0) proven by `norm_num` and `omega`, dressed up with theorem names and docstrings that suggest deep physics content (mass gap, gauge group, Wightman axioms). The Lean kernel accepts these as valid proofs because the propositions are true — `0 < 2` is genuinely true. But the propositions are not the claims. A theorem called `millennium_prize_solved` that proves `5=5 ∧ 0<2 ∧ 15=15` has not solved the Millennium Prize.**

**Approximately 17% of files (~15 out of 90) contain genuinely substantive formalisations that invoke real Mathlib theorems about mathematical objects: algebra isomorphisms via `kroneckerAlgEquiv`, matrix trace cyclicity via `Matrix.trace_mul_comm`, determinant multiplicativity via `Matrix.det_mul`, tensor product decompositions, group structure, and `Nonempty` existence proofs for algebra homomorphisms. These files represent real formal mathematics. The cascade's core algebraic step (M₂(ℂ) ⊗ M₂(ℂ) ≃ₐ[ℂ] M₄(ℂ)) is genuinely proven.**

**Another ~17% of files (~15 out of 90) are MIXED — they contain a few genuine Mathlib invocations (e.g., `Complex.normSq_nonneg`, `exp_add`, `Real.log_neg`, `Nonempty (... ≃ₐ[ℂ] ...)`) surrounded by arithmetic filler. These files have real mathematical content but it is diluted by arithmetic theorems that inflate the count.**

**The `True`/`trivial` pattern is more widespread than initially apparent — at least 18 files contain `True` hypotheses, `True` conclusions, or `trivial` proof terms. This includes `prediction_mass_ratio : True := trivial` (F3_2) and `heat_kernel_factorisation : True ∧ True ∧ True ∧ True` (F3_8d_iv). However, the primary issue remains misleading theorem names: the gap between what the names/docstrings claim and what the type signatures express.**

**In summary: the corpus contains approximately 100-150 genuine formal mathematics results and ~100 simple-but-real analysis facts (exp inequalities, log positivity, norm non-negativity), embedded within ~900-1,000 arithmetic facts. The arithmetic facts verify the numerical skeleton of the theoretical framework (dimensions, constants, inequalities) but do not formalize the framework's actual mathematical content (spectral theory, measure theory, functional analysis, Lie algebra decomposition). The corpus is a verified numerical blueprint, not a formal proof of the physics it describes.**

---

## 9. WHAT IS GENUINELY PROVEN (no inflation)

The following mathematical results are genuinely formalised with real Mathlib proofs:

1. **M₂(ℂ) ⊗ M₂(ℂ) ≃ₐ[ℂ] M₄(ℂ)** — The cascade tensor product isomorphism. Proven via `kroneckerAlgEquiv` + `reindexAlgEquiv`. This is the algebraic engine of the cascade.

2. **M₄(ℂ) ⊗ M₄(ℂ) ≃ₐ[ℂ] M₁₆(ℂ)** — The second cascade step. Same technique.

3. **Tr(AB) = Tr(BA)** — Matrix trace cyclicity. Invokes `Matrix.trace_mul_comm`. Foundation of gauge invariance.

4. **Tr(I_n) = n** — Trace of identity gives dimension. Invokes `Matrix.trace_one`.

5. **det(AB) = det(A)·det(B)** — Determinant multiplicativity. Invokes `Matrix.det_mul`.

6. **Existence of algebra homomorphisms/equivalences** between specific matrix algebras — Various `Nonempty (... ≃ₐ[ℂ] ...)` results proven constructively.

7. **Function space cardinality arguments** — `|Bool → Bool| = 4 ≠ 2 = |Bool|`, proving `End(ℂ²) ≇ ℂ²` (the cascade produces genuinely new structure).

8. **Unit type uniqueness** — `∀ f g : Unit → Unit, f = g` (the "nothing" level has trivial endomorphisms).

9. **exp(a+b) = exp(a)·exp(b)** — The multiplicative property of exp. A real Mathlib fact.

10. **Various exponential inequalities** — `exp(-x) > 0`, `exp(-x) < 1` for `x > 0`. Simple but genuine analysis.

These ~10 categories of genuine results are real mathematics. Everything else is arithmetic.

---

## 10. RECOMMENDATIONS

1. **Stop claiming "1,035 machine-verified theorems proving the ToE."** The accurate claim is: "~120 genuine formal mathematics results plus ~1,100 verified arithmetic facts that constitute the numerical skeleton of the framework."

2. **Rename theorems honestly.** `millennium_prize_solved` should be `millennium_numerical_skeleton` or similar. The names should describe what is proven, not what is aspired to.

3. **Separate the genuine proofs.** Create a curated list of the ~120 substantive theorems and present those as the formal verification results. The arithmetic theorems are supporting material, not the headline.

4. **Replace `True` hypotheses with proper axiom declarations.** The OS axioms in `F4_3d_SpectralWightman.lean` should be declared as `axiom` or as `variable` with meaningful types, not `True`.

5. **The F4.5/F4.6 upgrade programme is correctly scoped.** The roadmap already identifies the gap between arithmetic verification and genuine formalisation. The audit confirms this gap is real and large.

---

*This report was generated adversarially at the author's explicit request. The author was aware of many of these findings before the audit, having discussed them honestly in prior sessions. The roadmap (PAPER_F_ROADMAP.md, sections F4.5 and F4.6) explicitly acknowledges the gap and plans the upgrade programme.*

---

## APPENDIX A: COMPLETE PER-FILE CLASSIFICATION

Every .lean content file in the corpus, classified by what its proofs actually do.

**Legend:**
- **S** = SUBSTANTIVE — Uses real Mathlib algebraic/analytic structures (AlgEquiv, Matrix.*, TensorProduct, etc.)
- **M** = MIXED — Some genuine Mathlib invocations + arithmetic filler
- **A** = ARITHMETIC — Proofs are norm_num/omega/rfl on closed-form numbers
- **T** = TRIVIAL — Contains `(_ : True)` hypotheses or content-free assertions
- **Thms** = Number of theorem/def declarations
- **Primary tactics** = What the proofs actually use

### Root-level files (lean_verify/*.lean)

| File | Class | Thms | Primary tactics | Notes |
|------|-------|------|-----------------|-------|
| `EmergenceTheorem.lean` | **S** | ~20 | TensorProduct, AlgEquiv, Function.Bijective | Cascade emergence via tensor products |
| `ThreeLineages.lean` | **S** | ~15 | TensorProduct, AlgEquiv, unitaryGroup | Three lineages from algebra structure |
| `GaugeGroupSelection.lean` | **M** | ~18 | Some AlgEquiv + Nonempty + omega | Gauge group with genuine existence proofs |
| `GravityLineage.lean` | **S** | ~12 | SpecialLinearGroup, group homomorphisms | Uses Mathlib group theory |
| `SeedForced.lean` | **S** | ~10 | Equiv, Fintype.card, function space | Cardinality arguments for seed uniqueness |
| `NothingToSeed.lean` | **S** | ~8 | Equiv, function space, Unit | Function space cardinality |
| `QuantumLineage.lean` | **M** | ~15 | Some TensorProduct + omega | Mix of algebra and arithmetic |
| `PreferredDecomposition.lean` | **M** | ~12 | Some AlgEquiv + omega | Decomposition with algebra + arithmetic |
| `GToECoherence.lean` | **M** | ~18 | Nonempty AlgHom + omega | Coherence with genuine + arithmetic |
| `SMCompleteness.lean` | **A** | ~20 | norm_num, omega | Particle counting arithmetic |
| `SpectralActionForced.lean` | **M** | ~15 | Some exp_add + omega | Spectral action with some analysis |
| `CascadeUniqueness.lean` | **S** | ~10 | AlgEquiv, Function.Bijective | Uniqueness via algebra |
| `DimensionalAnalysis.lean` | **A** | ~12 | omega, norm_num | Dimension counting |
| `FermionContent.lean` | **A** | ~16 | omega, norm_num | Fermion DOF counting |
| `HiggsDoublet.lean` | **M** | ~10 | Some Nonempty + omega | Higgs with some existence proofs |
| `YukawaCouplings.lean` | **A** | ~14 | omega, norm_num | Coupling counting |
| `CKMMatrix.lean` | **M** | ~12 | Some Matrix + omega | Matrix structure + arithmetic |
| `NeutrinoMass.lean` | **A** | ~10 | omega, norm_num | Mass term counting |
| `AnomalyCancellation.lean` | **M** | ~14 | Some algebra + omega | Anomaly with some structure |
| `ProtonDecay.lean` | **A** | ~8 | omega, norm_num | Decay channel counting |
| `CosmologicalConstant.lean` | **A** | ~10 | omega, norm_num | CC value arithmetic |
| `MasterTheorem.lean` | **S** | ~5 | AlgEquiv composition | Master theorem via algebra |
| `LogosVerify.lean` | infra | — | — | Test infrastructure |

### Paper F files: F1.x (lean_verify/paper_f/F1_*.lean)

| File | Class | Thms | Primary tactics | Notes |
|------|-------|------|-----------------|-------|
| `F1_6_PatiSalamForced.lean` | **M** | 27 | 19 AlgEquiv refs, 4 Nonempty, 21 omega | Genuine algebra hom existence + arithmetic |
| `F1_7_SpacetimeForced.lean` | **A** | 24 | 25 norm_num, 22 omega | Spacetime dim as arithmetic |
| `F1_7b_SpacetimeUnconditional.lean` | **A** | 19 | 13 norm_num, 22 omega | Quaternion signs as arithmetic |
| `F1_7c_SpacetimeFinalClosure.lean` | **A** | 18 | 9 norm_num, 20 omega | Signature counting |

### Paper F files: F2.x (lean_verify/paper_f/F2_*.lean)

| File | Class | Thms | Primary tactics | Notes |
|------|-------|------|-----------------|-------|
| `F2_3_ChiralityForced.lean` | **S** | 24 | 14 AlgEquiv, 8 Nonempty, 0 norm_num | Heavy algebra hom usage — genuinely substantive |

### Paper F files: F3.x (lean_verify/paper_f/F3_*.lean)

| File | Class | Thms | Primary tactics | Notes |
|------|-------|------|-----------------|-------|
| `F3_1_ThreeGenerations.lean` | **A** | 27 | 4 norm_num, 24 omega | dim(Im(H))=3 as 4-1=3 |
| `F3_1b_ModuleSpectral.lean` | **A/T** | 26 | 8 norm_num, 30 omega | `spectral_theorem_3x3: 3=3 ∧ 3=3 ∧ 3=3` |
| `F3_2_HiggsForced.lean` | **A/T** | 32 | 1 norm_num, 32 omega, trivial | `prediction_mass_ratio: True` |
| `F3_8a_QuantumGravityFoundations.lean` | **A** | 18 | 14 norm_num, 20 omega | QG concepts as arithmetic |
| `F3_8b_SpectralActionComputation.lean` | **A** | 18 | 10 norm_num, 21 omega | Heat kernel coefficients as arithmetic |
| `F3_8c_NewtonsConstant.lean` | **A** | 17 | 4 norm_num, 19 omega | Beta coefficients as arithmetic |
| `F3_8d_CosmologicalConstant.lean` | **A** | 15 | 5 norm_num, 18 omega | Boson/fermion DOF counting |
| `F3_8d_ii_SSBVacuumShifts.lean` | **A** | 17 | 21 norm_num | Broken generator counting |
| `F3_8d_iii_RGRunningVacuumEnergy.lean` | **A** | 12 | 13 omega | Particle content counting |
| `F3_8d_iv_CrossLineageInterference.lean` | **A/T** | 12 | 2 norm_num, 11 omega, trivial | `heat_kernel_factorisation: True∧True∧True∧True` |
| `F3_8d_v_SpectralCorrections.lean` | **A** | 10 | 2 norm_num, 10 omega | Mass sum terms |
| `F3_8d_xii_TimeEvolution.lean` | **A** | 9 | 11 omega | Time evolution as counting |
| `F3_8d_xiii_Backreaction.lean` | **A** | 7 | 7 omega | Backreaction as counting |
| `F3_8d_xiv_AdditiveStructure.lean` | **A** | 10 | 10 omega | Additivity as counting |
| `F3_8d_xv_Synthesis.lean` | **A** | 7 | 6 omega | Synthesis as counting |
| `F3_8d_xvi_CCClosure.lean` | **A** | 8 | 1 norm_num, 8 omega | Gap closure as counting |
| `F3_8e_GravitonFromFluctuations.lean` | **A** | 14 | 10 norm_num, 15 omega | Graviton DOF counting |
| `F3_8f_ConnesNCG.lean` | **A** | 26 | 16 norm_num | NCG dimensions as arithmetic |
| `F3_8g_HigherLoopCorrections.lean` | **A** | 21 | 19 norm_num | Loop correction numbers |
| `F3_8h_BackgroundIndependence.lean` | **A** | 17 | 8 norm_num | Background independence as counting |
| `F3_8i_BlackHoleEntropy.lean` | **A** | 16 | 14 norm_num | Entropy coefficients |
| `F3_8j_GravitonScattering.lean` | **A** | 16 | 14 norm_num | Scattering components |
| `F3_8k_NonPerturbativeQuantisation.lean` | **A** | 13 | 11 norm_num | Quantisation DOF |
| `F3_9a_InternalConvergence.lean` | **A** | 20 | 12 norm_num, 7 exp | Convergence as exp_pos + arithmetic |
| `F3_9b_PhysicalCutoff.lean` | **A** | 14 | 12 norm_num, 3 exp | Cutoff parameters |
| `F3_9c_FullPathIntegral.lean` | **A** | 11 | 12 norm_num, 5 exp | Path integral dims + exp facts |
| `F3_9d_ReflectionPositivity.lean` | **M** | 13 | Complex.normSq_nonneg, exp_add, Real.log_neg | 3 genuine Mathlib results + arithmetic |
| `F3_9e_AnomalyCancellation.lean` | **A** | 14 | 12 norm_num | Anomaly coefficients |
| `F3_9f_WardIdentities.lean` | **A** | 13 | 14 norm_num | Ward identity counting |
| `F3_9g_i_InternalSpectralGap.lean` | **A** | 15 | 12 norm_num, 3 exp | Internal gap as 0<2 |
| `F3_9g_ii_ProductGeometryGap.lean` | **A** | 11 | 8 norm_num | gap_transfer is just lt_min |
| `F3_9g_iii_PoincareSpectralMeasure.lean` | **A** | 12 | 12 norm_num, 3 exp | Poincare inequality as arithmetic |
| `F3_9g_iv_CompactOperatorSpectrum.lean` | **A** | 12 | 10 norm_num, 2 exp | Operator spectrum as arithmetic |
| `F3_9g_v_ConfinementFromCascade.lean` | **A** | 11 | 10 norm_num, 2 exp | Confinement as arithmetic |
| `F3_9g_vi_ClusterDecomposition.lean` | **M** | 12 | exp_lt_one_iff, exp_le_exp + norm_num | 2-3 genuine analysis facts + arithmetic |
| `F3_9g_vii_FullMassGapTheorem.lean` | **A** | 15 | 13 norm_num, 4 exp | Mass gap as 4*4=16 ∧ 0<2 |
| `F3_10a_HeatKernelCanonicity.lean` | **M** | 25 | Gamma_nat_eq_factorial, exp_add + norm_num | Uses Real.Gamma — genuine Mathlib |

### Paper F files: F4.x (lean_verify/paper_f/F4_*.lean)

| File | Class | Thms | Primary tactics | Notes |
|------|-------|------|-----------------|-------|
| `F4_1a_TensorProductIsomorphism.lean` | **S** | 12 | kroneckerAlgEquiv, reindexAlgEquiv | **Core cascade proof — genuinely substantive** |
| `F4_1b_EndomorphismCascade.lean` | **S** | ~10 | AlgEquiv, TensorProduct | Cascade steps via algebra |
| `F4_1c_CascadeProperties.lean` | **M** | ~15 | Some AlgEquiv + norm_num | Properties mix |
| `F4_1d_AlgebraDimensions.lean` | **A** | ~18 | norm_num, omega | Dimension counting |
| `F4_1e_QuaternionSplitting.lean` | **S** | ~12 | Quaternion from Mathlib | Genuine quaternion algebra |
| `F4_1f_MatrixTraceAndDet.lean` | **S** | ~15 | Matrix.trace_mul_comm, Matrix.det_mul | **Genuine matrix algebra** |
| `F4_1g_GaugeGroupDecomposition.lean` | **A** | ~16 | norm_num, omega | Gauge dim counting |
| `F4_1h_CauchyFunctionalEquation.lean` | **A** | ~10 | exp_add + norm_num | Cauchy eqn as exp_add |
| `F4_1ij_QuaternionDivision.lean` | **M** | ~14 | Some Quaternion + omega | Mix of algebra + arithmetic |
| `F4_2a_96FermionSpectrum.lean` | **A** | ~20 | norm_num, omega | 96 DOF counting |
| `F4_2b_HiggsQuartic.lean` | **A** | ~12 | norm_num, omega | Higgs potential params |
| `F4_2c_ThreeGenerations.lean` | **A** | ~14 | norm_num, omega | Generation counting |
| `F4_2d_GaugeCouplingUnification.lean` | **A** | ~12 | norm_num | Coupling constants |
| `F4_2e_ProtonStability.lean` | **A** | ~10 | norm_num, omega | Proton lifetime bounds |
| `F4_2f_NeutrinoMassStructure.lean` | **A** | ~12 | norm_num, omega | Neutrino mass counting |
| `F4_2g_ZeroFreeParameters.lean` | **A** | ~8 | norm_num | Parameter counting |
| `F4_3a_SpectralTripleConstruction.lean` | **M** | ~16 | Some structure + omega | Spectral triple mix |
| `F4_3b_ActionBounds.lean` | **A** | ~12 | exp_pos, norm_num | Action bounds as exp facts |
| `F4_3c_FunctionalIntegral.lean` | **A** | ~10 | exp_pos, norm_num | Path integral as exp facts |
| `F4_3d_SpectralWightman.lean` | **T** | ~12 | True fields, rfl, norm_num | **True hypotheses — trivially provable** |
| `F4_4a_YMExistence.lean` | **A** | ~15 | norm_num, omega | YM existence as counting |
| `F4_4b_BoundedAction.lean` | **A** | ~10 | exp_pos, norm_num | Bounded action as exp_pos |
| `F4_4c_ClusterExpansion.lean` | **A** | ~12 | norm_num, exp_pos | Cluster expansion as exp facts |
| `F4_4d_InfiniteVolumeLimit.lean` | **A** | ~10 | norm_num | Infinite volume as counting |
| `F4_4e_MassGapExistence.lean` | **A** | ~12 | norm_num, exp_pos | Mass gap as 0<2 |
| `F4_4f_MassGapPersists.lean` | **A** | ~15 | norm_num, exp_pos | Mass gap persistence as arithmetic |
| `F4_4g_UnconditionalMillennium.lean` | **A** | ~8 | norm_num, rfl | `millennium_prize_solved` proves 5=5 |

### Summary by section

| Section | Files | S | M | A | T |
|---------|-------|---|---|---|---|
| Root-level | 23 | 7 | 8 | 7 | 1 |
| F1.x | 4 | 0 | 1 | 3 | 0 |
| F2.x | 1 | 1 | 0 | 0 | 0 |
| F3.x | 37 | 0 | 3 | 34 | 15* |
| F4.x | 25 | 4 | 3 | 16 | 2 |
| **TOTAL** | **90** | **12** | **15** | **60** | **3+** |

*\*15 of the F3.x arithmetic files also contain scattered `True`/`trivial` fields (not counted as separate "trivial" files since their primary content is arithmetic). The T column counts files where `True`/`trivial` is the PRIMARY proof strategy.*

**Note:** The root-level files (written earlier in the project) have the highest concentration of substantive content. The F3.x section (37 files) is almost entirely arithmetic — only 3 files contain any genuine Mathlib analysis (F3_9d, F3_9g_vi, F3_10a). The F3.8d subseries (CC layers, 8 files) is 100% arithmetic with scattered `True`/`trivial`. The F3.9g subseries (mass gap, 7 files) is also almost entirely arithmetic despite claiming to prove the mass gap theorem.

---

## APPENDIX B: THE 10 GENUINELY SUBSTANTIVE RESULTS (expanded)

For complete clarity, here are the actual Lean type signatures of the corpus's strongest results — the ones that reference real mathematical objects, not numbers:

**1. Cascade tensor product isomorphism** (`F4_1a`):
```lean
noncomputable def cascadeTensorIso :
    Matrix (Fin 2) (Fin 2) ℂ ⊗[ℂ] Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ]
    Matrix (Fin 4) (Fin 4) ℂ
```

**2. General cascade step** (`F4_1a`):
```lean
noncomputable def cascadeStepIso (n m : ℕ) :
    Matrix (Fin n) (Fin n) ℂ ⊗[ℂ] Matrix (Fin m) (Fin m) ℂ ≃ₐ[ℂ]
    Matrix (Fin (n * m)) (Fin (n * m)) ℂ
```

**3. Matrix trace cyclicity** (`F4_1f`):
```lean
theorem trace_commutative (A B : Matrix n n ℂ) :
    trace (A * B) = trace (B * A) := Matrix.trace_mul_comm A B
```

**4. Determinant multiplicativity** (`F4_1f`):
```lean
theorem det_multiplicative (A B : Matrix n n ℂ) :
    det (A * B) = det A * det B := Matrix.det_mul A B
```

**5. Left regular representation covariance** (`F2_3`):
```lean
theorem left_is_covariant (a b : Matrix (Fin 2) (Fin 2) ℂ) :
    left_regular_M2 (a * b) = a * left_regular_M2 b
```

**6. Chirality algebra homomorphisms** (`F2_3`):
```lean
Nonempty (Matrix (Fin 4) (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
```

**7. Endomorphism space non-triviality** (`EmergenceTheorem`):
```lean
theorem end_not_equal_seed : ¬ (Nonempty ((Bool → Bool) ≃ Bool))
```

**8. Nothing-level triviality** (`NothingToSeed`):
```lean
theorem unit_end_trivial : ∀ f g : Unit → Unit, f = g
```

**9. Reflection positivity** (`F3_9d`):
```lean
theorem reflection_positivity_key_fact (z : ℂ) :
    0 ≤ Complex.normSq z := Complex.normSq_nonneg z
```

**10. Action factorisation** (`F3_9d`):
```lean
theorem action_factorisation (S_plus S_minus : ℝ) :
    exp (-(S_plus + S_minus)) = exp (-S_plus) * exp (-S_minus)
```

These are the results that a mathematician or another AI can verify as having non-trivial mathematical content in their type signatures. Everything else in the corpus either proves arithmetic or simple analysis facts (exp_pos, lt_min, add_nonneg).
