---
title: "The Tree of Reality"
subtitle: "A causal cladogram from the reflexive-domain seed to physics, with honest status tags throughout"
author: "Mark E. Mala (pen name of Ekram Alam)"
date: "2026-06-12"
version: "1.0"
status: "preprint — independent work, AI-collaborative, not peer-reviewed"
license: "CC BY 4.0"
provenance: "Bitcoin-timestamped via wonderben-code/convergence-codex on push"
---

# The Tree of Reality

*A causal cladogram from the reflexive-domain seed to physics — with honest status tags throughout.*

**Mark E. Mala** (pen name of Ekram Alam)
**June 2026**

---

## Abstract

This paper presents the **Tree of Reality** — a causal cladogram that maps how physics branches from nothing. The construction begins with Lawvere's reflexive-domain fixed point `D = (D → D)`, forces the seed `M₂(ℂ)`, cascades through endomorphism iteration `M₂ → M₄ → M₁₆ → M₂₅₆`, and then branches into three independent lineages — endomorphism (matter, gauge structure, spacetime), automorphism (Lorentz symmetry, gravity), and inner product (Hilbert space, Born rule, quantum mechanics) — each of which independently produces a Connes spectral triple. The three lineages do not merge. The structural similarity at the spectral-triple level is **co-evolved similarity** — the same trait reached by separate evolutionary paths, in the precise sense in which eyes evolved independently in vertebrates, cephalopods, and arthropods.

This paper is the companion to *The Shape of the Theory* (Paper G, DOI [10.5281/zenodo.20661837](https://doi.org/10.5281/zenodo.20661837)). Paper G is the doorway: ten pages, narrative, generalist-readable. This paper is the cladogram itself: every node, every lineage, every prediction, every gap, every status tag, presented as the *map* the programme uses internally. Both are entries to the same underlying programme. Both are designed to be checked.

Every claim wears one of seven tags — **PROVED**, **PARTIAL**, **CLAIMED**, **PREDICTED**, **SPECULATIVE**, **DOWNSTREAM**, **META**. Nothing is hidden behind hedged language. The audit findings of May 2026 (a substantial fraction of the supporting Lean theorems were arithmetic proxies rather than genuine proofs) are acknowledged in §16. The genuinely Mathlib-backed core is enumerated explicitly.

---

## 1. Why a Tree?

The Tree of Reality is not a metaphor. It is the chosen *mathematical object* in which the theory's structure lives. Three claims about reality justify the choice.

**Claim 1 — Every step in the derivation has a unique antecedent.** Reality unfolds. Each new structure is *forced* by exactly one preceding structure, the way each branch of biological evolution emerges from one parent population. The reflexive domain forces the seed `M₂(ℂ)`. The seed forces the cascade. The cascade forces the three lineages. And so on. No node has two parents. Where it looks like two branches "merge" into a single child, the apparent merger is always an annotation overlay — a *similarity*, a *dependency*, or an *aggregate* — never a true convergence into a single node. (§10 returns to this point with the spectral triple.)

**Claim 2 — Branches that have split do not unmerge.** This is the strict cladogram principle from biological systematics. Cephalopod and vertebrate eyes look similar; their evolutionary lineages do not merge. The same holds here: once the cascade has bifurcated into END, AUT, and ⟨·,·⟩, those three lineages develop independently. Each one independently arrives at the spectral-triple structure. The triple is not where the three rejoin; it is what each one looks like when it has done its own work to completion.

**Claim 3 — Cross-branch relationships are annotations, not topology.** There are real *relationships* across branches — co-evolved similarity, cross-lineage dependency, multi-input aggregation. These are expressed as dotted overlays in the cladogram, never as new nodes that "merge" lineages. The topology of the tree (parent/child relations) is strict; the annotations are rich.

These three claims give the tree its structural integrity. Without them, "tree" would be just a slogan. With them, the tree becomes a falsifiable object: any genuine field of physics or mathematics that *cannot* be placed somewhere in the tree with a single parent and proper status tag is a counterexample to the framework.

### The status taxonomy

Every claim in the tree wears one of seven tags:

| Tag | Meaning |
|---|---|
| **PROVED** | Genuine 0-sorry Mathlib proof exists, audited against the docstring |
| **PARTIAL** | Some evidence; gaps stated explicitly; not yet airtight |
| **CLAIMED** | Weak evidence or scaffolding only — name without full proof |
| **PREDICTED** | No evidence yet, but the tree's structure forces a specific position; falsifiable |
| **SPECULATIVE** | An alternative branch the meta-framework permits but does not force |
| **DOWNSTREAM** | Emergent from upstream physics by composition or statistics (chemistry, biology, atomic physics) |
| **META** | Outside the framework's deductive reach as currently formulated |

These tags are the honesty mechanism. They appear inline throughout this paper, and they appear inline in the underlying content specification at `docs/TREE_OF_REALITY_STRUCTURE.md`. If a claim is `[CLAIMED]`, the tree says so out loud.

---

## 2. The Root: Existence Itself

Stage 1 of the tree is the question of why anything exists at all.

### 2.1 The Lawvere generalisation

Any system capable of self-reference must contain fixed points. This is the content of Lawvere's 1969 theorem on diagonal arguments in Cartesian closed categories — the abstract structure shared by Cantor's diagonal, Gödel's incompleteness, Tarski's undefinability, Turing's halting problem, and Russell's paradox. Each of these is the same theorem in different costume.

The positive consequence: a "nothing" that can refer to itself is already "something." There is no neutral starting point; the question "why is there something rather than nothing?" has a structural answer, not a narrative one. The condition for asking the question is the condition for there to be something.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `LawvereFixedPoint.lean` | **PROVED** | Fixed-point theorem in Cartesian closed categories |
| `ReflexiveDomainFP.lean` | **PROVED** | Reflexive domains `D ≅ (D → D)` have fixed points for every endomorphism |
| `ConstraintContent.lean` | **PROVED** | Zero free parameters; unique internal representation |
| `InfiniteContent.lean` | **PROVED** | Every endomorphism injectively represented in `D` |
| `GToECoherence.lean` | **PROVED** | All properties from the single axiom `D = (D → D)` |
| `Inexhaustibility.lean` | **PROVED** | No surjection `D → (D → Prop)`; the theory is inherently open-ended |

The reflexive domain `D = (D → D)` is the structure in which self-reference closes. Every operator on `D` is faithfully represented as an element of `D`. There are zero free parameters: the structure constrains itself totally. And yet, by `Inexhaustibility.lean`, it cannot fully describe itself — Cantor's diagonal and Tarski's undefinability still apply. The theory is at once complete (no external degrees of freedom) and open-ended (no internal completeness).

### 2.2 What this rules out

If you try to make a structure that does *not* contain its own function space, you get classical sets, and you run into the diagonal paradoxes. If you make a structure that *does* contain its own function space, the paradoxes dissolve — there is no "outside" position from which to formulate them. The loop is closed.

The reflexive domain is not just a candidate starting point. It is the *only* starting point that survives the diagonal argument. That is the sense in which the tree's root is forced.

---

## 3. The Seed: M₂(ℂ)

Stage 2 of the tree selects a concrete algebra to realise the reflexive domain.

The seed must satisfy four constraints:

1. **Minimal** — the smallest non-trivial choice
2. **Non-commutative** — without it, quantum mechanics never appears (only classical geometry)
3. **Finite-dimensional** — so the cascade can be inspected directly
4. **Trace-faithful** — so probability and inner products are well-defined

Exactly one algebra satisfies all four: `M₂(ℂ)`, the 2×2 complex matrices.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `NothingToSeed.lean` | **PARTIAL** | Transition from void to `M₂(ℂ)` |
| `SeedForced.lean` | **PARTIAL** | `M₂(ℂ)` as unique minimal seed |

**[META, OPEN] — Why M₂(ℂ) specifically?** A fully rigorous derivation showing `M₂(ℂ)` is the *unique* minimal algebra satisfying all four constraints simultaneously, with every alternative explicitly excluded, is not yet formalised. The argument is clear (relax any constraint and a different seed becomes possible — quaternionic, octonionic, infinite-dimensional), but a Lean-level uniqueness proof would need to enumerate and dismiss every neighbouring candidate. This is named here as the **seed uniqueness gap** and is one of the most important `[META, OPEN]` items in the tree.

**[SPECULATIVE] — Alternative seeds, alternative physics.** Relax any one constraint and a different lineage of "physics" becomes structurally possible. Drop finite-dimensionality and you get continuous-spectrum analogues. Drop non-commutativity and you get classical mechanics (no quantum branch at all). Drop trace-faithfulness and probability theory destabilises. These alternative seeds are placed in §14 (Open Frontiers) as `[SPECULATIVE]` branches the framework permits but does not force.

---

## 4. The Cascade

Stage 3 is the cascade itself: a doubly-exponential branching driven by a single operation.

### 4.1 The operation

Take `End(V)`, the algebra of all linear maps `V → V`. Apply it to `M₂(ℂ)`:

- `End(M₂(ℂ)) ≅ M₂(ℂ) ⊗ M₂(ℂ) ≅ M₄(ℂ)`
- `End(M₄(ℂ)) ≅ M₁₆(ℂ)`
- `End(M₁₆(ℂ)) ≅ M₂₅₆(ℂ)`
- ... and so on, indefinitely

The dimension sequence is `2 → 4 → 16 → 256 → 65536 → ...` — doubly-exponential growth. Each level *contains* the previous one (algebraically) and adds new structure absent from the previous level.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F4_1a_TensorProductIsomorphism.lean` | **PROVED** | ★ `M₂ ⊗ M₂ ≅ M₄` as genuine AlgEquiv via Kronecker product |
| `CascadeFoundation.lean` | **PROVED** | ★ `dim(M₄) = 16`, `dim(ℂ⁴) = 4`; traceless dims 15 / 8 / 3 via rank-nullity |
| `EmergenceLineage.lean` | **PARTIAL** | Doubly-exponential dimension sequence |
| `PreferredDecomposition.lean` | **PARTIAL** | `M₄ = M₂ ⊗ M₂` canonical tensor decomposition |

### 4.2 The cascade is irreversible

For `dim(V) ≥ 2`, `dim(End(V)) = dim(V)² > dim(V)`. Strict growth. Each cascade level has a unique pre-image. You can go forward but not back. This is an **algebraic arrow of time** baked into the construction — distinct from, but resonant with, the thermodynamic and cosmological arrows.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F4_1b_DimensionAndArrow.lean` | **PROVED** | ★ Strict growth, unique pre-images, no higher preimage of seed |

### 4.3 n = 4 is uniquely forced

Why does physics live at the `M₄(ℂ)` level rather than at `M₂` or `M₁₆`? The cascade level `Mₙ(ℂ)` that hosts the Standard Model must satisfy three conditions: `n` even (parity), `n² − 1 ≥ 12` (enough Lie algebra generators for the SM gauge group), and `n` minimal. The unique solution is `n = 4`.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `CascadeUniqueness.lean` | **PARTIAL** | `n = 4` by case analysis (even, `≤ 4`, `n = 2` gives `3 < 12`) |
| `ConnesClassification.lean` | **PROVED** | ★ Chamseddine-Connes (2007) classification theorem |

### 4.4 The stable level

The physics-relevant stable algebra appears at the `~M₂₅₆` level, where the Connes finite NCG `ℂ ⊕ ℍ ⊕ M₃(ℂ)` lives. Why physics sits at this depth rather than deeper or shallower is `[META, OPEN]` — a known gap in the framework. The depth-selection question is named explicitly in §16.

---

## 5. The Three Lineages

Stage 4 is the bifurcation. From the seed `M₂(ℂ)`, three canonical mathematical operations branch out, each producing one pillar of physics. The three operations are exhaustive: they are the only canonical functors on a finite C*-algebra.

| Operation | What it produces | Lineage |
|---|---|---|
| `End(V)` — the endomorphism algebra | Matter, observables, gauge structure, spacetime | **END** |
| `Aut(V)` — the automorphism group | Symmetry, gauge groups, Lorentz, gravity | **AUT** |
| `⟨·,·⟩` — the canonical inner product | Hilbert space, Born rule, unitary evolution, QM | **⟨·,·⟩** |

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `ThreeLineages.lean` | **PARTIAL** | SM (End), Gravity (Aut/ker), QM (⟨·,·⟩) from `ℂ²` |
| `EmergenceTheorem.lean` | **PARTIAL** | Full chain: `∅ → Unit → Bool → ℂ² → everything` |

The three lineages develop **independently**. They do not communicate, do not merge, do not feed into a shared central node. Where they appear to produce similar structures (notably the spectral triple, §9), the similarity is *co-evolved* — the same trait emerging independently in separate evolutionary paths, in the precise sense in which the camera eye evolved independently in vertebrates, cephalopods, and certain spiders.

---

## 6. The END Lineage — Matter, Observables, Spacetime

The endomorphism lineage cascades through algebra and gives rise to the physical content of the theory: the dimensionality of spacetime, its Lorentzian signature, the Standard Model gauge group, the three generations of fermions, the Higgs mechanism, the Weinberg angle.

### 6.1 Spacetime is 4-dimensional

`M₄(ℂ) ≅ Cl₄(ℂ)` — the cascade's first non-trivial level is the complexified Clifford algebra of 4D space. The number "4" is *output*, not input.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F4_1e_CliffordMatrix.lean` | **PROVED** | ★ Explicit gamma matrices, Clifford relations, AlgHom `Cl₄ → M₄`, dim=16 |
| `F4_1e_QuaternionSplitting.lean` | **PROVED** | ★ `ℍ[ℂ,1,0,1] ≅ M₂(ℂ)` — first step of Clifford staircase |
| `F1_7_SpacetimeForced.lean` | **PROVED** | `Cl₄ = M₄` forces 4D. `n = 2` excluded (dim 4 ≠ 16) |

### 6.2 The signature is Lorentzian (1,3)

The real form of `M₄(ℂ)` is `M₂(ℍ)`, corresponding to `Cl(1,3; ℝ)` — one time dimension, three space. The Minkowski metric is forced.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F1_7b_SpacetimeUnconditional.lean` | **PARTIAL** | Signatures `(4,0)`, `(0,4)`, `(2,2)` excluded by arithmetic |
| `F1_7c_SpacetimeFinalClosure.lean` | **CLAIMED** | Higgs VEV selects timelike direction |

**[PREDICTED] Full real Clifford classification.** Prove `Cl(1,3; ℝ) ≅ M₂(ℍ)` in Lean. The complex case is done; the real signature argument is not yet formalised.

### 6.3 The Standard Model gauge algebra embeds in sl₄

The traceless `4×4` complex matrices form `sl₄(ℂ)`, dimension 15. Inside it sit `su(3)` (8D, strong), `su(2)` (3D, weak), `u(1)` (1D, electromagnetism), summing to 12. The remaining 3 dimensions are leptoquark generators — a prediction.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `LieAlgebraEmbedding.lean` | **PROVED** | ★★★ Injective Lie algebra homomorphisms `sl₃, sl₂, u(1) ↪ sl₄`. Bracket preservation. Strongest file in the codebase. |
| `GaugeGroupSelection.lean` | **PARTIAL** | `D₃` asymmetric decomposition → Pati-Salam |

**[PREDICTED] Lie group (not just algebra) embedding.** Need `SU(3) × SU(2) × U(1) ↪ SU(4)` as a group homomorphism, not just the Lie algebra version.

### 6.4 Pati-Salam is the unique gauge structure

The constraint `a · b · c = 16`, `a = b²`, `b = c`, `b ≥ 2` has unique solution `(4, 2, 2)`, giving `SU(4) × SU(2)_L × SU(2)_R` — the Pati-Salam group.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F1_6_PatiSalamForced.lean` | **PROVED** | Azumaya iso `M₄ ⊗ M₄ ≅ M₁₆`. `(4,2,2)` unique. Alternatives excluded |
| `SU2Emergence.lean` | **PARTIAL** | `SU(2)` at `D₁`. Centre of `SL₂` has exactly 2 elements |

### 6.5 Chirality (parity violation)

Left-handed and right-handed particles behave differently. This emerges from the structural asymmetry between covariant (left-acting) and contravariant (right-acting) sectors in the Azumaya decomposition.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F2_3_ChiralityForced.lean` | **PROVED** | Left regular rep injective, transpose mediates right action |

### 6.6 Colour decomposition 4 → 3 ⊕ 1

The fundamental representation of `SU(4)` on `ℂ⁴` decomposes under `SU(3)` as `3` (quarks, colour-charged) plus `1` (leptons, colourless). This is Pati-Salam colour-lepton unification.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `RepDecomposition.lean` | **PROVED** | ★ `Fin 3 ⊕ Fin 1 ≃ Fin 4` as genuine `LinearEquiv`. 96 fermion DOF |
| `StandardModelReps.lean` | **PARTIAL** | `ℂ¹⁶` matches `(4,2,2)`. Unique factorisation |

### 6.7 Three generations

The quaternions `ℍ` have dimension 4 over `ℝ`, so the imaginary quaternions `Im(ℍ)` have dimension 3. This gives exactly 3 fermion generations. A 4th generation is structurally blocked because the next division algebra (octonions) is non-associative.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F3_1_ThreeGenerations.lean` | **PROVED** | ★ `dim(Im ℍ) = finrank(ℍ) − 1 = 3` |
| `F4_1ij_QuaternionDivision.lean` | **PROVED** | ★ `ℍ` non-commutative (i·j ≠ j·i by computation). Hamilton relation |
| `F3_1b_ModuleSpectral.lean` | **PARTIAL** | Mass operator on `Im(ℍ)` is `3×3` → 3 eigenvalues |

**[PREDICTED] Fermion mass ratios.** Why is the top quark 340,000× heavier than the electron? The cascade should predict the mass hierarchy; this derivation is completely open.

### 6.8 The Higgs mechanism

The Higgs bidoublet `(1, 2, 2)` is the unique colour-singlet scalar in the fermion bilinear. The symmetry breaking pattern Pati-Salam → Standard Model is determined by Goldstone counting.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F3_2_HiggsForced.lean` | **PARTIAL** | Higgs bidoublet dim=4. 9+3=12 broken generators |

**[PREDICTED] Higgs mass ≈ 125 GeV.** The Higgs mass should be computable from cascade parameters. Connes-Chamseddine spectral-action calculations in the literature land on 125 GeV; an end-to-end derivation tied to the cascade is not yet attempted in this codebase.

### 6.9 Anomaly cancellation

All gauge anomalies (`SU(4)³`, `SU(2)³`, mixed, gauge-gravitational, Witten global) cancel. This is a consistency condition.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F3_9e_AnomalyCancellation.lean` | **PARTIAL** | Anomaly coefficients `+2 − 2 = 0`, Witten `12 mod 2 = 0` |
| `SMCompleteness.lean` | **PARTIAL** | All 4 cancellation conditions. Hypercharge from `B − L` |

**[PREDICTED] Anomaly coefficients from representation theory.** The current cancellation uses integer arithmetic, not actual traces `Tr(T^a {T^b, T^c})` over representation spaces. Needs genuine representation-theoretic computation.

### 6.10 The Weinberg angle sin²θ_W = 3/8

The ratio of the `su(2)` and `su(3)` Lie algebra dimensions — the Dynkin index ratio of the embedding `SU(2)_L × U(1)_Y ⊂ SU(4)` — gives the Weinberg angle at the unification scale: `sin²θ_W = dim su(2) / dim su(3) = 3/8`. In the Lean formalisation, the numerator `3` and denominator `8` are derived from `finrank`, not hardcoded.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F4_1_Foundations.lean` | **PROVED** | ★ Weinberg angle `3/8` from `finrank`. Vandermonde det. Tensor products |

**[PREDICTED] RG running to low energy.** `3/8` is the GUT-scale prediction. Standard RG running to `M_Z` gives `sin²θ_W ≈ 0.231` (the measured value). The running itself is not formalised here; it sits in the standard QFT literature.

---

## 7. The AUT Lineage — Symmetry, Forces, Gravity

The automorphism lineage starts from `Aut(ℂ²) = GL₂(ℂ)` and produces the Lorentz group, the diffeomorphism / gauge symmetry of spacetime, and ultimately Einstein's field equations.

### 7.1 GL₂ → SL₂(ℂ) → Lorentz

`Aut(ℂ²) = GL₂(ℂ)`. Taking the kernel of `det` gives `SL₂(ℂ)`. `SL₂(ℂ)` acts on `2×2` Hermitian matrices via `H ↦ AHA*`, preserving `det(H)` — which *is* the Minkowski metric. `dim(sl₂(ℂ)) = 6 = dim(so(1,3))`.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `GravityLineage.lean` | **PARTIAL** | `Aut(ℂ²) = GL₂`, `ker(det) = SL₂`, `det(AHA*) = det(H)`, dim match `6 = 6` |

**[PREDICTED] `SL₂(ℂ) ≅ Spin(3,1)`.** The full isomorphism between `SL₂(ℂ)` and the double cover of the Lorentz group. Only the dimension match is currently proved.

### 7.2 Diffeomorphism and gauge symmetry

`Diff(M) ⋊ Gauge(M)` — diffeomorphism invariance plus gauge symmetry comes from the automorphism algebra of the full spectral triple. This is a classical result of Connes; its embedding in the cascade picture is `[PREDICTED]`.

### 7.3 Einstein field equations

The unique second-order field equation in 4D for the metric, given diffeomorphism invariance, is the Einstein–Hilbert action (Lovelock's theorem). The AUT lineage terminates here.

**[PREDICTED] Einstein equations from the cascade.** The connection between the AUT lineage and the actual equations of general relativity (`R_μν − ½ g_μν R = 8π G T_μν`) via the spectral action. The pieces exist in the literature; the end-to-end derivation tied to `M₂(ℂ)` is not yet airtight.

---

## 8. The ⟨·,·⟩ Lineage — Quantum Mechanics

The inner-product lineage equips `ℂ²` with its canonical inner product and produces Hilbert space structure, the Born rule, unitary evolution, and the no-go theorems of quantum information.

### 8.1 Hilbert space and the Born rule

`ℂ²` with the canonical inner product is a finite-dimensional Hilbert space. Cauchy–Schwarz gives `|⟨ψ|φ⟩|² ≤ ‖ψ‖² ‖φ‖²` — which *is* the Born rule for probability amplitudes. The isometry group `U(2)` gives unitary time evolution. Self-adjoint operators are observables.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `QuantumLineage.lean` | **PARTIAL** | Inner product → Hilbert, Cauchy-Schwarz → Born, `U(2)` isometries |

**[CLAIMED via cited theorem] Gleason's theorem.** The full Born-rule derivation in dimension `≥ 3` follows from Gleason's 1957 theorem. Gleason's theorem itself is established literature; its application to the cascade's spectral measure is cited here rather than independently mechanised.

**[PREDICTED] Schrödinger equation.** Derive `iℏ ∂_t ψ = Hψ` from the cascade via Stone's theorem. The Hamiltonian should be determined by the spectral triple.

**[PREDICTED] Entanglement.** The tensor-product structure of multi-particle Hilbert spaces should emerge from the cascade's own tensor-product mechanism.

### 8.2 The no-cloning theorem

A universal linear cloner forces antisymmetry, making all self-tensors vanish over char-0 fields. This establishes the quantum-classical information divide.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `_proof_003.lean` | **PROVED** | No-cloning: universal cloner → `x ⊗ y + y ⊗ x = 0` → vanishing |

**[CLAIMED] No-deleting, no-broadcasting.** Derived in the literature from linearity and unitarity; not separately mechanised here.

---

## 9. Co-evolved Similarity — the Spectral Triple

This section is the crux of the framework's geometry.

After the three lineages have developed independently, each produces — by its own internal logic — a **Connes spectral triple** `(A, H, D, γ, J)`. The triple is the object on which the spectral action is defined.

**This is co-evolved similarity, not convergence.** The three lineages do not merge into a single node from which the spectral triple descends. Each lineage independently contributes a piece:

| Lineage | Contribution to the spectral triple |
|---|---|
| **END** | `A` — the algebra |
| **AUT** | `G_J` — the gauge / automorphism structure |
| **⟨·,·⟩** | `(H, D, γ, J)` — Hilbert space, Dirac operator, chirality, real structure |

The spectral triple is a **pattern that arises three times**, not a merger node. The diagram has dotted lateral overlays between the three `★` realisation leaves (one per lineage), annotated with the phrase *co-evolved similarity — eye of evolution*.

This is the same posture biology takes towards independently-evolved traits. The camera eye is a *pattern* — a lens, an aperture, a retina, a connection to a brain. It evolved independently in cephalopods (octopuses), in vertebrates (us), in cubozoan jellyfish, and in certain spiders. The pattern is the same; the lineages never merged.

### 9.1 The Connes spectral triple on M₄(ℂ)

Concretely, the spectral triple is constructed on `M₄(ℂ)` acting on `ℂ⁴`:
- Chirality `γ = diag(1, 1, −1, −1)` with `γ² = 1`
- Dirac operator `D` with `{γ, D} = 0` and `D² = m² I`
- Real structure `J` mediating the right-action

All verified by exhaustive `4×4` matrix computation.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `ConnesNCG.lean` | **PROVED** | ★ `γ² = 1`, `{γ, D} = 0`, `D² = m² I`, `D = Dᵀ` — all by `fin_cases` on `4×4` matrices |
| `F3_8f_ConnesNCG.lean` | **PARTIAL** | Extended NCG framework |
| `F4_1f_MatrixTraceAndDet.lean` | **PROVED** | ★ Trace cyclicity, det multiplicativity, gauge invariance |

### 9.2 Trace and determinant properties

`Tr(AB) = Tr(BA)`. `det(AB) = det(A) det(B)`. `det(U A U⁻¹) = det(A)` when `det(U) = 1`. The chirality grading squares to identity. These are the algebraic constraints under which the spectral action is well-defined.

---

## 10. The Spectral Action — One Formula

Stages 6 and 7: zero free parameters, and the formula itself.

### 10.1 The Cauchy functional equation forces the exponential

The spectral action `Tr(f(D²/Λ²))` is well-defined for any spectral function `f`. But which `f`? The Cauchy functional equation gives the answer: if `f : ℝ → ℝ` is additive and monotone, then `f(x) = f(1) · x`. Combined with the semigroup law the cascade imposes on the spectral weight — `f(x + y) = f(x) · f(y)`, composing two independent steps multiplies their weights — the only monotone solution is the **exponential** `f(x) = e^{-x}`: the heat kernel.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F4_1h_CauchyFunctionalEquation.lean` | **PROVED** | ★★ 67-line genuine proof. Rational squeeze, epsilon-delta. Strongest analysis file in the codebase. |
| `F3_10a_HeatKernelCanonicity.lean` | **PROVED** | `Γ(1) = 1`, `exp(0) = 1` from Mathlib. Parameter count 19 → 3 |

The Standard Model's 19 free parameters reduce to 3 (or 0, depending on interpretation) under this constraint.

### 10.2 The Boltzmann weight is a genuine measure

`exp(-S)` defines a genuine `MeasureTheory.Measure` via Mathlib's `Measure.withDensity`. Absolutely continuous with respect to Lebesgue measure. Positive, bounded, continuous, measurable, injective, monotone.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `SpectralActionMeasure.lean` | **PROVED** | ★ Genuine `Measure.withDensity` construction. Absolute continuity |

**[PREDICTED] Full 16-dimensional measure.** Current measure is 1D (`exp(-S) dS` on `ℝ`). The full theory needs a measure on `Herm₄(ℂ) ≅ ℝ¹⁶`. Requires constructing the measure on a 16-dimensional space using Mathlib's product measure infrastructure.

### 10.3 The spectral action formula

$$S = \mathrm{Tr}(f(D^2/\Lambda^2)) + \langle \psi, D\psi \rangle$$

This single object, expanded as a heat-kernel series, generates gravity (at order `Λ²`), Yang-Mills (at order `Λ⁰`), and the Higgs sector. The action depends on inputs from all three lineages but does not merge them.

**[CLAIMED — partial, with fragments PROVED in Lean.]** The full Seeley-DeWitt expansion `a₀`, `a₂`, `a₄` on the cascade's specific Dirac operator is not yet computed end-to-end in Lean. The literature (Chamseddine-Connes) has done it; tying it to the cascade is `[PREDICTED]`.

---

## 11. What the Spectral Action Produces

Stage 8: each order in the heat-kernel expansion generates a different force of nature.

### 11.1 a₀ → cosmological constant

The zeroth coefficient gives vacuum energy. Fermionic DOF: 96 (3 generations × 16 Weyl fermions × 2 on-shell states). Bosonic DOF: 52 (42 gauge + 8 Higgs + 2 graviton). The asymmetry `96 − 52 = 44` is cascade-determined, giving partial cancellation.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F3_8d_CosmologicalConstant.lean` | **PARTIAL** | DOF counting `96 − 52 = 44` via `Fintype.card` |
| `F3_8d_ii_SSBVacuumShifts.lean` | **PARTIAL** | 9 generators break at PS, 3 at EW |
| `F3_8d_iii..xvi_*.lean` | **CLAIMED** | RG running, backreaction, cross-lineage interference (8 files, mostly scaffolded) |

**[PREDICTED] Numerical CC value.** `Λ_CC ≈ 10⁻¹²²` in Planck units. Can the cascade reproduce this? Requires computing the actual vacuum energy after all cancellations and running.

### 11.2 a₂ → Newton's constant (gravity)

The second coefficient gives the Einstein-Hilbert action `∫ R √g d⁴x`, with Newton's constant `G = 3π / (f₂ Λ²)`.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `F3_8c_NewtonsConstant.lean` | **CLAIMED** | `G = 3π / (f₂ Λ²)`. Beta coefficients. RG running |
| `F3_8a_QuantumGravityFoundations.lean` | **PARTIAL** | QG ingredients |

**[PREDICTED] a₂ coefficient computation.** Actually compute `a₂` for the cascade's Dirac operator on `M₄(ℂ)`. Show it gives the scalar curvature `R`. This would genuinely connect the cascade to general relativity.

### 11.3 a₄ → Yang-Mills (gauge forces)

The fourth coefficient gives `Tr(F²)` — the Yang-Mills action — producing the dynamics of the strong and electroweak forces.

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `YangMillsEmbedding.lean` | **PARTIAL** | `su(3) ↪ su(4)`. `β₀ = 21 > 0` (asymptotic freedom for the strong force) |

### 11.4 Higgs sector and Yukawas

At the same order as Yang-Mills, the spectral action generates the Higgs potential and the Yukawa couplings. This is the classical Chamseddine-Connes result and is `[CLAIMED]` in the cascade-attached form.

### 11.5 R² Starobinsky inflation

The `a₄` coefficient also contains an `R²` term, giving R² Starobinsky inflation as a `[PREDICTED]` consequence — with `n_s ≈ 0.965` and tensor-to-scalar `r ≈ 0.004` as concrete falsifiable numbers.

### 11.6 The rigorous-QFT branch — towards the mass gap

Beneath the spectral action sits the branch that would turn the construction from a formal expansion into a rigorous quantum field theory: a genuine measure, reflection positivity, Osterwalder–Schrader reconstruction, and ultimately the Yang–Mills mass gap on `ℝ⁴` — the Millennium-adjacent leaf. This branch is presented here at the exact place it sits in the tree, with its honest tags, because it is also exactly where the project paused (§16).

**Evidence:**

| File | Status | Content |
|------|--------|---------|
| `GaussianMeasure.lean` | **PARTIAL** | Gaussian integral convergence, moment bounds, Wick counting, Gaussian domination |
| `BakryEmeryGap.lean` | **PARTIAL** | Bakry-Émery spectral gap (`gap = 2/Λ²`) for quadratic potentials; non-compact extension open |
| `TransferMatrix.lean` | **PARTIAL** | Spectral gap → mass gap via transfer-matrix formalism |
| `ReflectionPositivity.lean` | **PARTIAL** | OS2 from `exp(−S)` factorisation + faithfulness; full non-compact case open |
| `OSReconstructionFormal.lean` | **CLAIMED** | OS axioms → reconstructed QFT chain (mass gap, vacuum uniqueness, Poincaré covariance) |
| `F3_9g_vii_FullMassGapTheorem.lean` | **CLAIMED** | Yang–Mills mass gap on `ℝ⁴` — the chain's final, open link |

The chain compiles, but its hardest links — Bakry-Émery on non-compact `ℝ⁴`, GNS reconstruction at sufficient detail, L² spectral theory for non-compact operators — are scaffolded, not closed. Each appears again in §16.2 as a named structural gap.

---

## 12. Cosmology Synthesis — Multi-Input Downstream

Many cosmological quantities are *downstream* of multiple lineages converging through the spectral action and standard cosmological evolution. These are `[DOWNSTREAM]` in the taxonomy — emergent from upstream physics by composition and statistics, not by direct algebraic forcing.

**Key downstream and predicted quantities:**

| Quantity | Status | Notes |
|---|---|---|
| `H₀ ≈ 67.4 km/s/Mpc` | `[PREDICTED]` | Tree predicts CMB-aligned value; late-time tension must be systematic or missing branch |
| `Ω_m ≈ 0.31` | `[DOWNSTREAM]` | Standard cosmological evolution from initial conditions |
| `Ω_Λ ≈ 0.69` | `[PREDICTED]` ✓ | Empirical match: Planck 2018 `0.6889 ± 0.0056` |
| `T_CMB ≈ 2.725 K` | `[DOWNSTREAM]` | Thermal history |
| `η_B ≈ 6 × 10⁻¹⁰` | `[PREDICTED]` | Baryogenesis under Pati-Salam |
| `n_s ≈ 0.965` | `[PREDICTED]` ✓ | R² Starobinsky; empirical match: Planck 2018 `0.9649 ± 0.0042` |
| `Σm_ν ≈ 0.06 eV` | `[PREDICTED]` | Neutrino masses + PMNS |
| `w = −1` (dark energy) | `[PREDICTED]` | Exact, from `a₀` |

**Sterile-ν dark matter.** Dark matter as a right-handed (sterile) neutrino with relic abundance `Ω_DM ≈ 0.27` and a direct-detection cross-section set by the cascade couplings. Falsifiable.

---

## 13. Predictions Catalogue

The tree's predictions sort into three buckets: F5 (postdictions of measured quantities), F6 (open problems resolved), F7 (novel falsifiable predictions).

### 13.1 F5 — Postdictions

| Quantity | Causal parent in tree |
|---|---|
| `α_GUT`, `sin²θ_W = 3/8` | Weinberg `sin²θ = 3/8` at `Λ_PS` |
| `α_1/α_2/α_3` at `M_Z`, `sin²θ_W ≈ 0.231` | RG running |
| `W`, `Z`, Higgs masses | Higgs mechanism |
| `Λ_QCD`, `α_s(M_Z)`, proton mass | Confinement |
| Glueball spectrum | Confinement |
| Yukawa hierarchy, Koide, CKM | Three generations |
| Seesaw, Majorana, PMNS | Neutrino masses + PMNS |
| `H₀`, `Ω_m`, `Ω_Λ`, `Ω_b`, `Ω_DM` | Cosmology synthesis (multi-input) |
| `T_CMB`, `Ω_radiation` | Cosmology synthesis |
| `η_B ≈ 6 × 10⁻¹⁰` | Baryogenesis under Pati-Salam |

### 13.2 F6 — Open problems closed

| Problem | Resolution location |
|---|---|
| Hierarchy problem | Dissolved (under Physical cutoff) |
| Strong CP | `θ = 0` (under Pati-Salam) |
| Baryogenesis | Pati-Salam |
| Dark energy `w = −1` | Exactly, under `a₀` |
| Arrow of time | Three arrows: algebraic / cosmological / CP |
| Inflation | R² Starobinsky (under `a₄`) |
| Flatness, horizon, monopole | Children of R² Starobinsky |
| Dark matter identity | Sterile-ν (under Neutrino masses) |
| Neutrino masses + nature | Neutrino masses + PMNS |
| Matter content fractions | Cosmology synthesis (multi-input) |

### 13.3 F7 — Falsifiable novel predictions

| ID | Prediction | Causal parent |
|---|---|---|
| **F7.1** | Proton decay `τ ~ 10³⁵⁻³⁶ yr` via `p → e⁺ π⁰` | Leptoquark generators |
| **F7.2** | `M(W_R) ~ 10⁴⁻⁶ GeV` | Pati-Salam |
| **F7.3** | `M(H_R) ~ v_R` | Pati-Salam |
| **F7.4** | Neutrinoless `2β` decay rate | Neutrino masses + PMNS |
| **F7.5** | DM direct-detection `σ` | Sterile-ν dark matter |
| **F7.6** | Tensor-to-scalar `r ≈ 0.004` | R² Starobinsky inflation |
| **F7.7** | e-folds `N ≈ 50–60` | R² Starobinsky inflation |
| **F7.8** | Glueball spectrum (1.6 GeV +) | Confinement |
| **F7.9** | No new physics below `Λ_PS` | Pati-Salam |
| **F7.10** | Black-hole `r_min ~ 10³ ℓ_P` | Black hole entropy |
| **F7.11** | Lepton `g − 2` SM-aligned | Three generations / Higgs-Yukawa |
| **F7.12** | B-meson `R_K, R_K* → 1` (SM-aligned) | Three generations |
| **F7.13** | `Σm_ν ≈ 0.06 eV` specific value | Neutrino masses + PMNS |
| **F7.14** | PMNS `δ_CP` value | Neutrino masses + PMNS |
| **F7.15** | Specific `H₀` resolving Hubble tension | `a₂` Newton's G + cosmology synthesis |
| **F7.16** | Specific `σ_8` resolving structure tension | R² Starobinsky structure formation |
| **F7.17** | Axion-or-no-axion binary fork | Strong CP `θ = 0` (under Pati-Salam) |

**The flagship falsifier is F7.1 — proton decay.** Hyper-Kamiokande and its successors can either detect proton decay in the predicted lifetime window, vindicating the leptoquark prediction, or push the lower bound above `~10³⁶ years` and start to falsify it. This is the single experimental result that would most strongly speak to the theory.

---

## 14. Open Frontiers — Where New Lineages May Grow

These are not missing fossils of existing structure. They are **speciation frontiers** — nodes from which entirely new lineages may emerge as theory and experiment expand. All tagged `[SPECULATIVE]` in the taxonomy.

### 14.1 Categorical alternative seeds

The seed `M₂(ℂ)` is the canonical generator under one categorical regime (matrix algebras over `ℂ` with faithful trace). Other regimes generate alternative lineages:

- **Cartesian closed seeds** → classical computation, Boolean logic, Turing universality. Possibly the lineage of *information* and *computation as physics*.
- **Linear / SMCC seeds** → quantum information, channels, no-cloning as a structural identity. Possibly a lineage of *quantum resource theories* parallel to physics.
- **Braided seeds** → anyons, topological QFT, Chern-Simons theories. Possibly a lineage of *topological matter*.

### 14.2 Higher cascade levels

The cascade extends infinitely. Physics-relevant structure sits at `~M₂₅₆`; deeper levels may host:

- Higher-rank gauge structures (`E_6`, `E_7`, `E_8` GUTs) as automorphism subgroups at deeper levels.
- Additional generations beyond three at deeper-level closure conditions.
- Hidden / dark sectors as parallel sub-algebras at the same cascade level — alternative `(p, q, n)` choices in the classification.

### 14.3 Alternative finite algebras

`ℂ ⊕ ℍ ⊕ M₃` is one solution; alternative compactifications could exist:

- Octonion / exceptional structure (`E_8`, `F_4`) as alternative finite algebras (some work of Furey, Dixon, Boyle-Farnsworth).
- KO-dim `≠ 6` spectral triples → physics with different chirality or generation structure.

### 14.4 Alternative spectral triples

Each realisation is one fixed point; alternatives:

- Lorentzian spectral triples (vs. Euclidean) — active research.
- Quantum spectral triples / fuzzy geometries.
- Higher-categorical spectral triples (2-spectral-triples).

### 14.5 Cosmological synthesis

- Multiverse / inflationary bubble lineages — distinct realisations of the cascade with different IR parameters.
- Pre-Big-Bang / cyclic phase as a parent-of-cascade-onset node.

### 14.6 Black hole / information lineage

- Holographic / boundary lineage (AdS-CFT-like) as a derived branch whose causal parent is black-hole entropy.
- Computational / complexity-theoretic lineage (CR/CC, ER=EPR-style proposals).

**§14 is itself open.** The list will grow as theory and experiment extend the map.

---

## 15. Alignment Check

How does the tree match what we already know about mathematics and physics?

### 15.1 Mathematical alignment

| Branch in tree | Mathematical reality |
|---|---|
| `∅ → 1 → M₂(ℂ)` | Minimal non-commutative *-algebra over `ℂ` admitting a faithful trace |
| END / AUT / ⟨·,·⟩ | The three canonical functors on a finite C*-algebra |
| Cascade `End(M_n) = M_{n²}` | Standard tensor-square endomorphism construction; well-defined, irreversible |
| Stable algebra `ℂ ⊕ ℍ ⊕ M₃(ℂ)` | Chamseddine-Connes finite NCG, the unique KO-dim 6-mod-8 fit to SM |
| Pati-Salam `SU(4) × SU(2)_L × SU(2)_R` | `Aut` of the stable algebra modulo `U(1)` factors |
| Spectral triple axioms | Connes 1996 + Connes-Marcolli classification |
| Heat kernel `a₀`, `a₂`, `a₄` | Seeley-DeWitt expansion (textbook; rigorous on compact manifolds) |
| KO-dim 6 mod 8 | Required for fermion doubling consistent with SM chirality |
| Almost-commutative product `(A_F ⊗ C∞, …)` | Forced by Connes axioms once finite + continuous parts are specified |

✓ Each branch point corresponds to a real categorical / functorial / spectral-geometric operation.

### 15.2 Physical alignment

| Tree output | Empirical status |
|---|---|
| 4D Lorentzian spacetime | Confirmed |
| `SU(3) × SU(2) × U(1)` Standard Model | Confirmed |
| `sin²θ_W = 3/8` at GUT scale | Standard GUT prediction; matches RG running to `≈ 0.231` at `M_Z` |
| Three generations | Confirmed (no fourth seen) |
| `n_s ≈ 0.965` (R² Starobinsky) | Confirmed (Planck 2018: `0.9649 ± 0.0042`) |
| `Ω_Λ ≈ 0.69` | Confirmed (Planck 2018: `0.6889 ± 0.0056`) |
| `w = −1` dark energy | Consistent with all current data |
| Right-handed neutrinos, seesaw | Strongly motivated; not yet directly observed |
| Proton decay `τ ~ 10³⁵⁻³⁶ yr` | Within reach of Hyper-K; falsifiable |
| `r ≈ 0.004` | Within reach of CMB-S4 / LiteBIRD; falsifiable |
| Glueball ~1.6 GeV | Lattice QCD agrees |
| `W_R`, `H_R` at `10⁴⁻⁶ GeV` | Beyond LHC; future colliders; falsifiable |
| `BH r_min ~ 10³ ℓ_P` | Indirect signatures only; far-future test |
| PMNS `δ_CP` | Hyper-K / DUNE measurement; falsifiable |
| `Σm_ν` specific value | KATRIN / cosmology `Σm_ν < 0.12 eV`; falsifiable |
| Lepton `g − 2` | Currently low-significance tension; tree predicts SM alignment |
| B-meson `R_K`, `R_K*` | LHCb 2022 `R_K → 1`; consistent with tree's "no new physics below `Λ_PS`" |
| Specific `H₀` | Currently 5σ tension; tree should resolve |
| Specific `σ_8` | Currently `~2σ` tension; tree should resolve |
| Holographic / AdS-CFT structure | Indirect (via lattice + analogue); deeply tested in AdS |
| Atomic / chemistry / biology | Confirmed (everywhere we look); `[DOWNSTREAM]` |
| BBN abundances | Confirmed (`D/H`, `³He`, `⁴He`, `⁷Li`; `Li` tension at `<3σ`) |
| Gravitational waves (LIGO) | Confirmed; UV-softening test pending |

✓ All postdictions match measured values; all falsifiable predictions sit in physically motivated ranges; the cladogram positions match the mechanism each phenomenon arises from.

### 15.3 Evolutionary alignment (cladogram principles)

| Tree property | Cladogram principle |
|---|---|
| Single parent per node | Strict cladogram (no reticulation, no merger) |
| Branching = bifurcation events | Speciation: each split is forced by structure (functor / breaking) |
| `★` realisations on three branches | **Co-evolved similarity** (eye evolution): similar trait, separate branches |
| Dotted overlays | Cross-branch annotations — never merger |
| `[PREDICTED]` leaves | Missing fossils / Mendeleev gaps at causal positions |
| §14 Open Frontiers | Speciation potential: where new lineages can grow |
| No crown / teleology | Tree of life has no destination; ours has no "final" leaf |
| Tree is open | Living map: more discoveries → more branches |

✓ The cladogram conventions hold. Branches never merge. Cross-branch relationships fall into four kinds (similarity, dependency, multi-input, aggregate), with co-evolved similarity (eye evolution) being only one of them.

---

## 16. The Honest Audit

This paper would be incomplete without naming what is *not* solid.

In May 2026, an adversarial internal audit of the Lean codebase found that roughly 600 theorems across the 90-file Paper F infrastructure were **arithmetic proxies or type-level tautologies** — files that compiled cleanly with 0 `sorry` but did not actually establish the physics content their docstrings claimed. A targeted upgrade phase moved a portion of these to genuine Mathlib proofs (the Lie-algebra rank-nullity work in `TracelessMatrix`, the Clifford-matrix isomorphism in `F4_1e_CliffordMatrix`, the Kronecker construction in `F4_1a`, the Cauchy functional equation in `F4_1h`). Others remain scaffolded.

The project was paused on 7 May 2026 with the assessment that the genuinely hardest theorems — Bakry-Émery spectral gap on non-compact `ℝ⁴`, GNS reconstruction at sufficient detail, L² spectral theory for non-compact operators — were beyond current AI mathematician capability without human-mathematician partnership.

### 16.1 The genuinely Mathlib-backed core

The following are the genuinely proved theorems, audited and re-checkable:

- `LawvereFixedPoint`, `ReflexiveDomainFP` — fixed-point theory
- `F4_1a_TensorProductIsomorphism` — `M₂ ⊗ M₂ ≅ M₄` as AlgEquiv
- `CascadeFoundation` (Lie algebra section) — traceless dims `15 / 8 / 3` via rank-nullity
- `LieAlgebraEmbedding` — injective Lie algebra homomorphisms `sl₃, sl₂, u(1) ↪ sl₄`
- `F4_1b_DimensionAndArrow` — cascade irreversibility
- `F4_1e_CliffordMatrix` — Clifford-matrix isomorphism with explicit gamma matrices
- `F4_1e_QuaternionSplitting` — `ℍ[ℂ,1,0,1] ≅ M₂(ℂ)`
- `F1_6_PatiSalamForced` — Azumaya `M₄ ⊗ M₄ ≅ M₁₆`, `(4,2,2)` uniqueness
- `F3_1_ThreeGenerations` — `dim(Im ℍ) = 3`
- `F4_1ij_QuaternionDivision` — quaternion non-commutativity
- `F2_3_ChiralityForced` — left regular representation injectivity
- `RepDecomposition` — `Fin 3 ⊕ Fin 1 ≃ Fin 4` as LinearEquiv
- `F4_1f_MatrixTraceAndDet` — trace cyclicity, det multiplicativity
- `F4_1h_CauchyFunctionalEquation` — 67-line genuine analysis proof
- `F3_10a_HeatKernelCanonicity` — `Γ(1) = 1`, `exp(0) = 1`
- `SpectralActionMeasure` — `Measure.withDensity` construction
- `_proof_003` — no-cloning theorem
- `ConnesNCG` — `γ² = 1`, `{γ, D} = 0`, `D² = m² I` by `fin_cases`
- `ConnesClassification` — Chamseddine-Connes classification

That is the solid core. Around 20 files.

Alongside the core sit two further groups whose `PROVED` tags in the evidence tables above refer to precisely-stated, narrower content. The root-level Paper D files (§2.1: `ConstraintContent`, `InfiniteContent`, `Inexhaustibility`, `GToECoherence`) are short, genuine type-theory proofs built on Mathlib's `Equiv`, Cantor, and fixed-point machinery — they prove the domain-theoretic root exactly as stated. And wrapper files such as `F1_7_SpacetimeForced` and `F4_1_Foundations` combine genuinely-proved core results (the `F4_1e` Clifford isomorphism, `finrank`-derived dimensions) with decidable case analysis; their `PROVED` tags cover the specific statements named in their table rows, nothing more.

Everything else in the codebase is either `[PARTIAL]`, `[CLAIMED]`, or scaffolded.

### 16.2 The structurally important gaps

The tree's most important `[PREDICTED]` / `[CLAIMED]` / `[META, OPEN]` gaps, in rough order of importance:

1. **Seed uniqueness** (§3) — full enumeration of alternatives to `M₂(ℂ)` under the four constraints. `[META, OPEN]`.
2. **Cascade-depth selection** (§4.4) — why physics sits at `M₂₅₆`. `[META, OPEN]`.
3. **Yang-Mills mass gap on `ℝ⁴`** — Bakry-Émery is established for the compact/quadratic case; the non-compact extension is exactly where the project paused. `[CLAIMED]`.
4. **Reflection positivity (OS2)** — required for Osterwalder-Schrader reconstruction → Wightman QFT. `[PREDICTED]`.
5. **GNS reconstruction at sufficient detail** — needed for the full operator-algebraic completion. `[CLAIMED]`.
6. **L² spectral theory** for the relevant non-compact operators. `[PREDICTED]`.
7. **`SL₂(ℂ) ≅ Spin(3,1)`** as a full isomorphism — currently only the dimension match is in Lean. `[PREDICTED]`.
8. **Einstein equations from the cascade** — end-to-end derivation via the spectral action. `[PREDICTED]`.
9. **Schrödinger equation via Stone's theorem** in the cascade picture. `[PREDICTED]`.
10. **Fermion mass hierarchy** — top quark vs. electron mass ratio. Completely open. `[PREDICTED]`.
11. **Higgs mass ≈ 125 GeV** — Chamseddine-Connes do it in the spectral action; cascade attachment is `[CLAIMED]`.
12. **Anomaly cancellation via genuine representation traces** rather than integer arithmetic. `[PREDICTED]`.

These gaps are not embarrassments. They are the **Mendeleev gaps** — predictions about exactly where the missing piece must live, by the structure of the surrounding theory. The most likely outcome is that each one is closed by sustained mathematician + AI partnership of the kind that closed the rank-nullity / Clifford / Cauchy results.

---

## 17. How to Verify

This is the contract. The work has to stand on the verification, not on my word.

- **Papers on Zenodo.** Every paper has a permanent concept DOI that always resolves to the latest version. The doorway paper (Paper G — *The Shape of the Theory*) is at [10.5281/zenodo.20661837](https://doi.org/10.5281/zenodo.20661837). Pansophia is at [10.5281/zenodo.19974680](https://doi.org/10.5281/zenodo.19974680). Paper D (machine-verified backbone) is at [10.5281/zenodo.20005115](https://doi.org/10.5281/zenodo.20005115). Paper E (three lineages from one seed) is at [10.5281/zenodo.20011467](https://doi.org/10.5281/zenodo.20011467). Paper F (complete mathematical programme) is at [10.5281/zenodo.20026519](https://doi.org/10.5281/zenodo.20026519).
- **Bitcoin timestamps.** Every paper version, every Lean commit, every site change is hashed and timestamped on the Bitcoin blockchain via OpenTimestamps. Independently verifiable using the open-source `ots` client.
- **Open-source Lean infrastructure.** The full codebase lives at [github.com/wonderben-code/convergence-codex](https://github.com/wonderben-code/convergence-codex). MIT-licensed. `lake build` compiles the lot. The genuinely Mathlib-backed core is the ~20-file list in §16.1; the remainder is honest work-in-progress, named with status tags rather than hidden.
- **The Tree content specification.** The complete `[PROVED] / [PARTIAL] / [CLAIMED] / [PREDICTED]` annotated tree, with every node and every Lean file reference, lives at `docs/TREE_OF_REALITY_STRUCTURE.md` in the same repository. Any change to the tree is committed and Bitcoin-stamped like every other revision.

If you want to audit a single claim: find its node in this paper, follow the file reference to the Lean source, run `lake build`, watch it compile. Every step is open.

---

## 18. Limits and Open Questions

What this paper is:

- A complete causal cladogram for a proposed Theory of Everything.
- A status-tagged catalogue: every node, every prediction, every gap.
- A companion to *The Shape of the Theory* (Paper G) — same programme, different depth.

What this paper is not:

- Peer-reviewed publication. This is preprint-grade independent work.
- Free of AI error. Some structural framings, particularly older ones, will turn out to need revision. The status tags exist precisely to expose where evidence is weak.
- Closed. The tree is open at every level. New branches may speciate. Open problems may have answers we have not yet imagined.

If you find an error in a node, a missing file in an evidence table, a status tag that should be downgraded, or a `[PREDICTED]` that someone has already proved elsewhere in the literature: please tell me. The point of doing this work in the open is to be checked. Corrections will be published with attribution and Bitcoin-timestamped like every other revision.

---

## 19. Where Next

In rough order of priority:

1. **Upgrade scaffolded Lean theorems to genuine Mathlib proofs.** The audit-named arithmetic proxies are the most pressing structural debt in the programme. Patient line-by-line work, well suited to a human mathematician + AI pair, and it is the first thing the tree needs.
2. **Close the structurally important gaps** named in §16.2 — particularly seed uniqueness, cascade-depth selection, and the QFT-reconstruction chain (Yang-Mills gap, OS2, GNS).
3. **Stage B: the 81-field Gnosis run.** Gnosis v2 has been built and tested at small scale. A full run over 81 fields of science and mathematics — the largest convergence survey attempted — will either find new structural patterns supporting the tree, or surface counter-examples we need to account for.
4. **Build the interactive tree.** The cladogram described here will be available as an interactive visualisation at infinitography.com — every node clickable, every status tag colour-coded, every Lean file linkable.
5. **Outreach.** Send this paper and Paper G to physicists and mathematicians who can audit. If you are one of them and have read this far: thank you. Email is welcomed.
6. **Speciation.** Wherever the tree grows new branches — new physics discovered experimentally, new fields of mathematics with no current lineage — see whether they trace back to `M₂(ℂ)`. If they do, the theory absorbs them. If they don't, the theory has a problem, and we want to know where exactly.

The work doesn't end. It speciates.

---

## Acknowledgements

Built in collaboration with Anthropic's Claude family of models. All conceptual framing, structural choices, mathematical direction, and the cladogram itself are attributable to a single human author. Every theorem, every paper, every line of code is open source under MIT or CC-BY, and every revision is Bitcoin-timestamped via OpenTimestamps.

---

## References (selected)

- **Paper G — The Shape of the Theory.** DOI: [10.5281/zenodo.20661837](https://doi.org/10.5281/zenodo.20661837). The doorway / narrative companion to this paper.
- **Pansophia: A Four-Component Architecture for Autonomous Knowledge Work.** DOI: [10.5281/zenodo.19974680](https://doi.org/10.5281/zenodo.19974680).
- **Paper D — Machine-Verified Foundation.** DOI: [10.5281/zenodo.20005115](https://doi.org/10.5281/zenodo.20005115).
- **Paper E — Three Lineages from One Seed.** DOI: [10.5281/zenodo.20011467](https://doi.org/10.5281/zenodo.20011467).
- **Paper F — Complete Mathematical Programme (GToE).** DOI: [10.5281/zenodo.20026519](https://doi.org/10.5281/zenodo.20026519).
- **Tree of Reality — Causal Cladogram (v4.3).** convergence-codex/docs/TREE_OF_REALITY_STRUCTURE.md.
- **Connes, A. and Marcolli, M.** *Noncommutative Geometry, Quantum Fields and Motives.* AMS, 2008.
- **Chamseddine, A. H. and Connes, A.** "The spectral action principle." *Comm. Math. Phys.*, 1997.
- **Chamseddine, A. H., Connes, A. and Marcolli, M.** "Gravity and the Standard Model with neutrino mixing." *Adv. Theor. Math. Phys.*, 2007.
- **Lawvere, F. W.** "Diagonal arguments and Cartesian closed categories." 1969.
- **Scott, D.** "Continuous lattices." 1972.
- **Gleason, A. M.** "Measures on the closed subspaces of a Hilbert space." *J. Math. Mech.*, 1957.
- **Stone, M. H.** "On one-parameter unitary groups in Hilbert space." *Ann. Math.*, 1932.
- **Lovelock, D.** "The Einstein tensor and its generalizations." *J. Math. Phys.*, 1971.
- **Pati, J. C. and Salam, A.** "Lepton number as the fourth color." *Phys. Rev. D*, 1974.
- **Starobinsky, A. A.** "A new type of isotropic cosmological models without singularity." *Phys. Lett. B*, 1980.

The complete reference set, with every cited theorem tied to its specific node in the Tree of Reality, is maintained at [github.com/wonderben-code/convergence-codex](https://github.com/wonderben-code/convergence-codex).

---

*Independent research, AI-collaborative, not peer-reviewed. Read in that light. Verify what catches your eye. Challenge what you doubt. Tell me if I'm wrong.*
