# The Emergence Programme: Seed to Standard Model

**Author:** Mark E. Mala
**Date:** 3 May 2026
**Status:** ACTIVE

## Goal

Show a complete, machine-verified mathematical chain proving that the Standard Model gauge group SU(3)×SU(2)×U(1) emerges from the Generator construction in compact closed categories. Each step is a theorem. The whole chain is machine-verified and Bitcoin-timestamped.

```
C² → M₂(C) → M₄(C) → M₁₆(C) → ... → D∞
 |      |        |         |              |
I+I   SU(2)   SU(2)²    SU(n)×?    SU(3)×SU(2)×U(1)
```

## The Claim

The Generator construction in FdVect_C (finite-dimensional complex vector spaces — the category where quantum mechanics lives) produces a sequence of algebras whose automorphism groups, constrained by the iterative structure, yield the Standard Model gauge group SU(3)×SU(2)×U(1) with the correct representations.

---

## Stage 1: The Lineage Is Concrete

**Difficulty:** Undergraduate linear algebra. Fully computable.

In FdVect_C (compact closed), the internal hom is [V, W] = V* tensor W.

```
D₀ = C²                                     (dim 2)
D₁ = [C², C²] = End(C²) = M₂(C)            (dim 4)
D₂ = [M₂(C), M₂(C)] = End(M₂(C)) = M₄(C)  (dim 16)
D₃ = [M₄(C), M₄(C)] = End(M₄(C)) = M₁₆(C) (dim 256)
D₄ = M₂₅₆(C)                                (dim 65536)
```

Dimensions: 2, 4, 16, 256, 65536 — i.e., 2^(2^n).

**Theorems to prove:**

- 1.1: In FdVect_C, I = C and I+I = C²
- 1.2: [C², C²] = End(C²) = M₂(C)
- 1.3: [M₂(C), M₂(C)] = End(M₂(C)) = M₄(C)
- 1.4: [M₄(C), M₄(C)] = End(M₄(C)) = M₁₆(C)
- 1.5: In general, D_{n+1} = M_{dim(D_n)}(C) and dim(D_n) = 2^(2^n)

**Lean deliverable:** `EmergenceLineage.lean`

---

## Stage 2: SU(2) Emerges at D₁

**Difficulty:** Classical algebra. Known results.

**Theorems to prove:**

- 2.1: Every automorphism of M_n(C) is inner (Skolem-Noether)
- 2.2: Aut(M₂(C)) = PGL(2,C), compact form PU(2)
- 2.3: SU(2) double-covers PU(2) = SO(3)
- 2.4: SU(2) is the gauge group of the weak nuclear force (citation, not proof — established physics)

**Significance:** The FIRST iteration produces the weak force gauge group.

**Lean deliverable:** `SU2Emergence.lean`

---

## Stage 3: The Iteration Gives Preferred Decompositions

**Difficulty:** Serious algebra. Double Commutant Theorem.

**Theorems to prove:**

- 3.1: End(A) = A tensor A^op for any finite-dimensional simple algebra A (Double Commutant)
- 3.2: M₂(C)^op = M₂(C) (via transpose)
- 3.3: Therefore D₂ = End(M₂(C)) = M₂(C) tensor M₂(C)
- 3.4: This decomposition is CANONICAL — comes from the iteration (left and right multiplication)
- 3.5: D₃ = M₂(C)^{tensor 4} (four tensor factors)
- 3.6: D_n = M₂(C)^{tensor 2^(n-1)} in general

**Key consequence:** The iteration-compatible automorphisms of D₂ are:

```
Aut_iter(D₂) = (PU(2) × PU(2)) ⋊ Z₂
```

This is SU(2)×SU(2) — the Pati-Salam intermediate symmetry.

**Lean deliverable:** `PreferredDecomposition.lean`

---

## Stage 4: From SU(2)×SU(2) to SU(3)×SU(2)×U(1)

**Difficulty:** This is the research core. Three possible paths.

### Path A: Nested Iteration Approach

At D₃ = M₂^{tensor 4}, the factors come in PAIRS from two levels. The automorphisms compatible with BOTH levels of nesting form a smaller group.

- 4A.1: Compute automorphisms of D₃ compatible with D₁ subset D₂ subset D₃
- 4A.2: Identify the resulting group G
- 4A.3: Show G contains/equals SU(3)×SU(2)×U(1) (if true)

### Path B: Subfactor / Jones Theory

The inclusion D₁ subset D₂ is a subfactor. Jones theory assigns an index and principal graph.

- 4B.1: Jones index of M₂(C) subset M₄(C) is 4
- 4B.2: The principal graph of D₁ subset D₂ subset D₃ determines a representation category
- 4B.3: Match to Standard Model representations

### Path C: Meet in the Middle

**From below:** Iteration-compatible automorphisms at each stage.
**From above:** Known GUT chain: SU(3)×SU(2)×U(1) subset SU(5) subset SO(10) subset SU(16) = Aut(D₃)

- 4C.1: Aut(D₃) = PU(16) superset SU(16)
- 4C.2: Standard GUT embedding: SU(3)×SU(2)×U(1) subset SU(5) subset SU(16)
- 4C.3: The iteration structure selects the GUT chain as maximal iteration-compatible subgroup
- 4C.4: THE EMERGENCE THEOREM

**Lean deliverable:** `GaugeGroupEmergence.lean`

---

## Stage 5: Representation Matching

**Difficulty:** Known representation theory from GUT literature.

- 5.1: D₂ = M₂ tensor M₂ decomposes under SU(2)×SU(2) as (2,2)
- 5.2: Under SU(3)×SU(2)×U(1) subset SU(5), the fundamental 5 = (3,1)_{-1/3} + (1,2)_{1/2}
- 5.3: The 10 of SU(5) = (3-bar,1)_{2/3} + (3,2)_{1/6} + (1,1)_{-1}
- 5.4: One generation of SM fermions = 5-bar + 10 — match with iteration representations

**Lean deliverable:** `StandardModelReps.lean`

---

## Stage 6: The Full Emergence Theorem

```
THEOREM (Standard Model Emergence from the Generator Construction):

Let C = FdVect_C (finite-dimensional complex vector spaces).
Let D₀ = I+I = C².
Let D_{n+1} = [D_n, D_n] (iterated internal hom in C).

Then:
(1) D₁ = M₂(C), with Aut(D₁) containing SU(2)
(2) D₂ = M₂(C) tensor M₂(C), with iteration-compatible Aut = SU(2)×SU(2)
(3) D₃ = M₂(C)^{tensor 4}, with iteration-compatible Aut containing
    SU(3)×SU(2)×U(1)
(4) The natural representations decompose into Standard Model fermions
(5) Zero free parameters — seed, operation, category determine the gauge group

Therefore: the Standard Model gauge group emerges from the Generator
construction via machine-verified theorems, each step a mathematical necessity.
```

**Lean deliverable:** `EmergenceTheorem.lean`

---

## Execution Order

```
Stage 1:  Lineage computation (hours)
Stage 2:  SU(2) emergence (1 day)
Stage 3:  Preferred decomposition + SU(2)×SU(2) (days)
Stage 4:  Gauge group computation — the hard part (days to weeks)
Stage 5:  Representation match (days, if Stage 4 succeeds)
Stage 6:  Full theorem (days)
```

## Tools

- Python/SageMath: computational exploration (fast iteration)
- Lean 4 + Mathlib: formal verification (permanent)
- Paper E: "Emergence of the Standard Model from the Generator Construction"

## What This Proves If It Works

1. Machine-verified proof that SU(3)×SU(2)×U(1) emerges from one construction with zero free parameters
2. Concrete mathematical pathway from the empty set to the Standard Model — every step a theorem
3. Something no other ToE has — a specific, falsifiable, verified prediction
4. If the iteration-compatible automorphisms at D₃ DON'T give SU(3)×SU(2)×U(1), the theory fails cleanly

## Files

All Lean files in: `lean_verify/emergence/`
Plan document: `docs/EMERGENCE_PROGRAMME.md`
Paper: `data/papers/paper_e_emergence.md`
