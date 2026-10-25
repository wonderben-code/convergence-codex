# A two-way dictionary

The two programmes use almost disjoint vocabularies for overlapping objects. This table is a
first attempt at translation. Chain Theory definitions are from its glossary ("the nearest
standard term …") and Definitions 1.1–1.6; Tree definitions are from the capstone §1 and §4.
Entries marked **≈** are approximate and flagged for correction.

## Chain Theory → Tree of Reality

| Chain Theory | Its definition | Nearest Tree object | Notes |
|---|---|---|---|
| **qudit** | a finite-dimensional quantum system, dim ≥ 2 | a level of the cascade, or a factor of one: M_d(ℂ) as the observable algebra of a d-level system | the Tree names the *algebra*; Chain Theory names the *system*. Same thing in two grammars. |
| **the qubit, register two** | d = 2 | **the seed M₂(ℂ)** (L3) | exact |
| **the qutrit, register three** | d = 3 | the **colour triplet** in 4 → 3⊕1 (L13) | the Tree reaches 3 by splitting the 4; Chain Theory takes 3 as an end dimension (Conjecture 0) |
| **the ququart, register four** | d = 4 | **M₄(ℂ)** as a system, the first child of the cascade (L4) | exact |
| **pair / link** | two qudits in the maximally entangled state on their common support | ≈ a tensor factorisation M_a ⊗ M_b inside a level, with the canonical state | the Tree has no primitive "pair"; the closest is the bimodule structure of the spectral triple (L18) |
| **genre (d₁, d₂)** | the pair of end dimensions of a link | ≈ which factors of M₄ ⊗ M₄ = M₁₆ are in play | (2,2) ↔ M₂⊗M₂ = M₄; (4,4) ↔ M₄⊗M₄ = M₁₆; (3,2), (3,3), (4,3) ↔ the sub-blocks after 4 → 3⊕1 |
| **the (2,2) link** | a pair of qubits | **M₄(ℂ) ≅ Cl₄(ℂ)** — spacetime dimension four (L8) | both read it as spacetime; see 03 |
| **shared qudit** | an end of two or more pairs, one copy per pair | ≈ a common tensor factor | the "PEPS site" picture |
| **distill** | project two qudits onto the pair on their common support, one copy, no failure branch | ≈ a conditional expectation / projection onto a sub-algebra | the Tree's "how things are known" lineage (⟨·,·⟩) is where this lives |
| **read** | a distillation in one of the d + 1 mutually unbiased bases, taken at the larger end | ≈ a measurement in a MUB; the Tree's GNS/Born step (L21) | the Tree cites the Born rule; Chain Theory derives it from the wash (35.1, conditional) |
| **known** | what all reads fix jointly under every matching and exchange | ≈ the invariants of the automorphism (Aut) lineage (L7) | gauge invariance "as the known clause" (64.1) is the clearest overlap with Aut |
| **matching** | a change of basis U acting as U ⊗ Ū, leaving the pair fixed | an inner automorphism of the level | Aut lineage |
| **the twirl / the wash** | the average over the basis identifications the definitions leave free | ≈ averaging over the automorphism group; the conditional expectation onto the fixed-point algebra | "measurement as the wash at one act" (28.1) |
| **pair ket** | the twirl-fixed point, the unique pure state the matchings leave fixed | the canonical maximally entangled vector in M_d ⊗ M_d | — |
| **identification algebra** su(d₁) ⊕ su(d₂) ⊕ u(1) | the infinitesimal basis changes at a link's two ends | the Lie algebra of the automorphism group of the two factors — the Tree's **gauge algebra** (L10) | at (3,2) both sides have su(3)⊕su(2)⊕u(1) |
| **face group** | the group of a cell: S(U(d₁) × U(d₂)) | the Tree's Pati–Salam / Standard-Model group on M₁₆ (L11) | (2,3) ↔ SM group; (2,4) ↔ S(U(2)×U(4)), SU(4) = Spin(6), which is the Pati–Salam SU(4)_c |
| **the read cap** d₁d₂ ≤ 6 | a read fixes both ends iff every positive map between them is decomposable | no Tree counterpart | candidate mechanism for the Tree's L23 (see 04) |
| **readable / dark genre** | whether a single read passes at first order | — | — |
| **record** | an invariant all reads of a qudit fix jointly | ≈ an element of the fixed-point algebra of the twirl | — |
| **letter** | the byproduct operator a distillation leaves at a slot (Gell-Mann / Pauli) | a traceless basis element of su(d) | — |
| **office** | (glossary) the coefficient a read carries at a link; "nearest standard term" a coupling or a quantum number | ≈ a coupling constant / Casimir value | the Higgs quartic "as the ratio of offices" (202.1) |
| **hub** | a pair read as a single qudit; the pair of two qubits whose legs open onto the qutrits | **M₄ as M₂ ⊗ M₂** — the cascade's first step read as one system | hub pair as one qudit of dimension four (65.2) is exactly End(M₂) ≅ M₄ (L4) |
| **dock** | a link of two qubits whose far end is washed; the charge register of a body | ≈ a (2,2) factor with one side traced out | — |
| **web** | a network of pairs joined at shared qudits, no stabilizer phase fixed | ≈ a tensor network over levels of the cascade | the Tree has no particle-level webs |
| **body** | a web read as a particle | — | the Tree stops at representations (the chiral 16), not individual particle anatomies |
| **roster** | the family of networks the rules admit; "nearest standard term the particle spectrum" | ≈ the representation content of the chiral 16 ⊗ generations | — |
| **move / join / saturation / sink** | the rewriting dynamics on webs; a sink is a web no move leaves | the Tree's cascade is one move (End), applied once per level; no sink notion | the Tree's irreversibility (L5) is a one-directional version |
| **depth / rung** | growth order of a closure; count of waves to the horizon | ≈ level of the cascade (depth n ↔ M_{2^{2^n}}) | both count "how far up" |
| **order coordinate** | a count of one-steps (50.1) | — | the Tree has no derived time; see *A Note on Time* (book) |
| **first face / second face / parting** | the two sides of a check and where it fails | the Tree's "unproven residue" named in every PARTIAL row | same honesty device |
| **theorem / conditional theorem / open result** | see 01 | **GENUINE / PARTIAL / OPEN** | close match; "conditional theorem" ≈ PARTIAL; POSTULATE has no exact Chain Theory counterpart (nearest: Conjecture 0 and the "by name" correspondences) |
| **"by name"** | a correspondence with physics asserted by name only | a POSTULATE or a cited input (assumptions ledger) | — |

## Tree of Reality → Chain Theory

| Tree | Its definition | Nearest Chain Theory object | Notes |
|---|---|---|---|
| **the root** (L1) | Lawvere's fixed-point theorem: self-reference forces existence | none — the axiom is the starting point | see 05 |
| **the reflexive domain** D ≃ (D → D) (L2) | a structure isomorphic to its own self-maps | none | — |
| **the seed M₂(ℂ)** (L3) | the unique minimal non-commutative algebra over ℂ | the qubit | exact |
| **the cascade** End(M_b) ≅ M_{b²} (L4) | one operation, iterated | the hub step (65.2), applied once | Chain Theory has the step but not the iteration as a law |
| **irreversibility** (L5) | dimension strictly increases up the tower | ≈ the forward edge of a move; saturation terminating at a sink | — |
| **the fourth level** M₂₅₆ (L6) | where the CCM finite algebra fits | no counterpart (Chain Theory stops at register four, dimension 4; the Tree's levels are 2, 4, 16, 256) | the Tree's "4" is a *level index*, Chain Theory's "4" is a *dimension*; both have dimension 4 = ququart = M₄ |
| **three lineages** End · Aut · ⟨·,·⟩ (L7) | what things are / how they transform / how they are known | ≈ pairs / matchings / reads | a surprisingly clean match — see 03 |
| **Cl₄(ℂ) ≅ M₄(ℂ)** (L8) | the Clifford algebra of 4-dimensional space is the two-qubit algebra | the (2,2) link; the spin-c group at the qubit pair (58.1); "the Clifford relation at four generators met" (ch. 3-5) | — |
| **Lorentzian signature** (L9) | — | Lorentz group as isometries of the Hermitian split (54.1); one against three (55.1) | — |
| **Pati–Salam on M₁₆** (L11) | SU(4)_c × SU(2)_L × SU(2)_R from M₄ ⊗ M₄ | the (2,4) and (4,4) face groups: S(U(2)×U(4)) with SU(4) = Spin(6), S(U(4)×U(4)) | — |
| **colour 4 → 3⊕1** (L13) | the fundamental of SU(4) splits into colour triplet + lepton | the qutrit (register three) | the Tree *derives* the 3 that Chain Theory *posits* |
| **three generations ← imaginary quaternions** (L14, POSTULATE) | — | three as a theorem of the valence (83.1); generation bound at hub dimension (197.3); three generations as attach sites (197.5, open) | see 04 |
| **Weinberg ratio 3/8** (L17) | Tr(T₃L²)/Tr(Q²) on the chiral 16 | not found in the compendium | see 05 |
| **spectral triple / spectral action** (L18–L20) | (A, H, D) and Tr f(D/Λ) | none — Chain Theory's gravity is combinatorial (Part VI) | the two gravity routes are disjoint; see 06 |
| **Hilbert space, GNS, Stone, Schrödinger** (L21) | the quantum apparatus from the inner-product lineage | Part III (state space, unitary transport, energy as first power) | Chain Theory has Born as output; the Tree cites it |
| **Einstein equations from the spectral action** (L22, OPEN; gap G5) | heat-kernel a₂ → curvature | curvature as graph Laplacian (90.2, conditional); field equation open | — |
| **Yang–Mills and the mass gap** (L23, OPEN) | — | confinement as dark-genre readability (171.1, conditional) | see 04 |
| **gaps G1–G6** | infinite-volume limit; unbounded self-adjoint operators; Peierls; Dobrushin/cluster; heat kernel; isotypic bimodule/K-theory | the open results register (Table 239.1): 74 open, 48 re-posed, 133 conditional clauses | both keep a public ledger of what is not done |
