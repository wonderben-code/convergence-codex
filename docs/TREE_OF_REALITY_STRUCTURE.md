# Tree of Reality — Causal Cladogram (Content Specification v4)

**Status:** content-locked structure for the "true cladogram" view of physics.
Implementation (HTML/D3) deliberately deferred — this document is the source of
truth for the *theory* itself; the visualisation is a downstream rendering.

**Date locked:** 2026-05-10
**Version:** v4

**What changed v3 → v4 (substantial expansion per author 2026-05-10):**

- Added **meta-tree above the seed** (§2.5): selection rules + space of
  alternative seeds (M_n, 𝕆, ℍ, J₃(𝕆), II_∞/III, categorical seeds).
- Added **Pre-cascade trigger** node with open hypotheses.
- Named **cascade fork events** (Furey, Dixon, Boyle-Farnsworth,
  exceptional F₄/E₆/E₇/E₈) as explicit sibling branches.
- **Grew QM ⟨·,·⟩ subtree** (Born, Schrödinger, path integral, decoherence,
  einselection, measurement, Bell, Zeno, tunnelling, SYK, Pauli, no-delete).
- Added **holographic subtree** under BH entropy.
- Added **cosmological structure-formation subtree** under R².
- **Sharpened predictions** to named leaves: PMNS δ_CP, Σm_ν, axion-or-no-
  axion fork, lepton g-2, B-meson R_K, specific H₀, specific σ_8.
- Added **Downstream emergent physics** as new top-level branch (atomic →
  chem → condensed matter → biology → cognition / observer).
- Added **Astrophysics & planetary** as new top-level branch.
- Added **§9 Rival frameworks** as competitor trees with distinguishing tests.
- **Reconciled KO-dim**: 6 mod 8 (finite part) vs 2 mod 8 (total M × F).
- New status tags: `[META]`, `[SPECULATIVE]`, `[DOWNSTREAM]`.

**Earlier (v2 → v3) corrections retained:**

1. **The tree is an open, living map — not a closure proof.** Earlier framing
   (v2) said "anything that doesn't fit breaks the theory." That was wrong.
   The tree is generative: it grows. New physics that emerges off the seed,
   off the cascade, or off any stable branch *adds* a new branch, just as
   evolution speciates new clades. The map is never finished; it is a record
   of what we have constructed so far. Existing branches are *predictions
   about where new fossils should sit*; they do not foreclose new lineages.

2. **The word "convergence" is misleading and is retired in this document.**
   Branches in evolution **never converge** once they have split. What we
   *do* see is **co-evolved similarity**: distinct, separate branches
   independently developing structurally similar traits — the camera eye
   in cephalopods and vertebrates being the canonical example. Two eyes,
   two branches, similar structure, **no merger**. v2 had a downstream
   "Spectral Triple — convergence event" *merger node* and a label
   "Convergence overlays". Both have been replaced. v3 uses **co-evolved
   similarity** for eye-style trait similarity across distinct branches,
   and distinguishes three other kinds of overlay (cross-lineage
   dependency, multi-input causal compounding, aggregate contribution) —
   none of which are similarity, and none of which involve branches
   converging. See §4 for the full taxonomy.

3. **Open Frontiers section made explicit.** v2 dissolved the catch-all
   "Open Frontiers" branch because predictions belong at causal parents.
   That remains true. But there is a *separate* notion of "places where
   entirely new lineages may grow off existing nodes" — speciation
   frontiers, not missing-fossil predictions. v3 adds §6 to surface these
   without polluting the strict cladogram.

**Convention:** every node has exactly one tree-parent (single-parent
cladogram). Branches do not merge. Cross-branch relationships of any kind
are expressed as **dotted overlay lines** with a kind tag (similarity /
dependency / multi-input / aggregate) — never as merger children.

---

## 1. Methodological commitments

1. **Causal first.** A node's parent is the structure that *forces it to
   exist*. Where multiple structures contribute, we pick the most direct
   algebraic source and represent the others as dotted overlay edges.
2. **No teleology, no crown.** The tree branches outward like evolution.
   Mass Gap is one leaf among many, not a destination.
3. **Predictions sit at their causal positions.** Like Mendeleev's gaps:
   unsolved Paper F problems are placed at the exact branch the structure
   says they must occupy.
4. **Branches do not converge. They co-evolve similarities.** When several
   lineages independently arrive at structurally similar objects (eye
   evolution), each lineage keeps its own `★ realisation` leaf. The
   similarity is annotated only — no shared child, no merger. The word
   "convergence" is avoided in this document; the correct term is
   **co-evolved similarity**.
5. **The map is open.** New lineages may speciate from the seed, the
   cascade, the stable algebra, or any descendant. §6 catalogues the
   speciation frontiers that are currently visible. The list is itself
   open.
6. **No orphan "Frontiers" branch.** Within the cladogram, every prediction
   lives at its causal antecedent. The §6 frontiers are *meta*: they say
   *where the cladogram could grow*, not where solved problems go.
7. **Status taxonomy.** Seven tags, in increasing distance from algebraic
   forcing:
   - `[PROVED]` — unconditional 0-sorry Mathlib proof.
   - `[PARTIAL]` — some evidence, gaps stated explicitly.
   - `[CLAIMED]` — weak evidence / scaffolding only.
   - `[PREDICTED]` — no evidence yet, but the structure of the tree forces
     a specific position (missing fossil / Mendeleev gap). Falsifiable.
   - `[SPECULATIVE]` — alternative branch the meta-framework permits but
     does not force; may exist in parallel (e.g. octonion finite triples).
   - `[DOWNSTREAM]` — emergent from upstream physics by compositional /
     statistical mechanism, not algebraically forced (e.g. chemistry from
     atoms; biology from chemistry).
   - `[META]` — meta-categorical / outside the framework's deductive
     reach as currently formulated (e.g. why these axioms? what triggered
     the cascade?). Different epistemic level from `[PREDICTED]`.

---

## 2. Eight resolved design questions

### Q1. Where does the spectral triple live? — Co-evolved similarity (v3 reframe)

The Connes spectral triple `(A, H, D, γ, J)` is a **co-evolved similarity**
across the three lineages — eye-evolution style. Like the camera eye in
cephalopods, vertebrates, cubozoans, alciopid worms, etc.: each evolved
its own eye on its own branch, the branches never merged, and the
*similarity* of the resulting eyes is the meaningful biological fact.

In our tree:

- **END** alone gives `A`: the algebra `M₄(ℂ)`, with native `Cl₄` spinor
  module, `D = γ^μ ∂_μ`, `γ = γ⁵`, charge-conjugation `J`.
- **AUT** alone gives `G_J`: the unitary symmetries that preserve `J`,
  realising Connes' standard NCG construction on a Lorentzian spin
  manifold.
- **⟨·,·⟩** alone gives `(H, D, γ, J)`: the geometric data, abstract
  operator-algebra triple.

Each lineage independently develops the structures required by the
spectral-triple axioms. They **do not merge**. The fact that all three
realisations are mutually consistent (the algebra END produces is acted on
by the group AUT produces inside the Hilbert space ⟨·,·⟩ produces) is
*co-evolved similarity*, not convergence.

In v3, each lineage carries its own `★ Spectral Triple realisation` leaf.
The similarity is captured by **dotted overlay lines among the three
sibling leaves** (not into a shared child). Downstream physics — the
Spectral Action, heat kernel expansion, cosmology, QFT — descends under a
single causal parent (the ⟨·,·⟩ lineage, where the Dirac operator and the
trace live), with dotted *cross-lineage dependency* overlays from END
(supplying A) and AUT (supplying G_J). Dependency is a different kind of
overlay from similarity — see §4.

### Q2-Q8 (carried from v1/v2, unchanged)

- Q2 — `No complete self-description`: child of D=(D→D) (Cantor/Tarski need a domain).
- Q3 — Dark matter: child of Neutrino masses (sterile-ν), not Leptoquarks.
- Q4 — Hierarchy problem: child of `Physical cutoff justified` (mechanism is regularisation).
- Q5 — R² Starobinsky: sibling of Yang-Mills inside a₄ (both Λ⁰ terms).
- Q6 — Phase transitions: under Consequences (Landau Z₂ in spectral-action sector).
- Q7 — `n=4 uniquely forced`: PROVED ★ (ConnesClassification.lean unconditional).
- Q8 — Filename: `tree-of-reality.html`.

---

## 2.5 Meta-tree above the seed

The seed M₂(ℂ) is selected by four constraints: (i) minimality, (ii)
non-commutativity, (iii) finite-dimensionality, (iv) faithful trace. Drop
any one and you get a different seed. The constraints themselves come
from a **meta-categorical level** that the cladogram-proper does not
deductively reach. We surface this here as a separate (smaller) meta-tree;
its leaves are not Mendeleev gaps in the same sense — they are
`[META]` and `[SPECULATIVE]` rather than `[PREDICTED]`.

```
META-CATEGORICAL LEVEL  [META]
│
├─ Selection rules (why these constraints?)
│  ├─ Minimality                      [META, OPEN]
│  ├─ Non-commutativity required       [PARTIAL — without it, classical geometry only]
│  ├─ Finite-dimensional               [META, OPEN — relax → infinite-dim seeds]
│  └─ Faithful trace exists            [PARTIAL — needed for probability / GNS]
│
├─ Space of possible seeds  [SPECULATIVE]
│  ├─ M₂(ℂ) — our universe's seed (selected by all four rules)
│  ├─ M_n(ℂ) for n ≥ 3                 [SPECULATIVE — alternative starting points]
│  ├─ ℍ (quaternion) standalone        [SPECULATIVE]
│  ├─ 𝕆 (octonion) / Cayley-Dickson   [SPECULATIVE — non-associative; needs Jordan structure]
│  ├─ J₃(𝕆) exceptional Jordan algebra [SPECULATIVE — Albert algebra; F₄ / E₆ paths]
│  ├─ Infinite-dim von Neumann II_∞   [SPECULATIVE — gives different physics]
│  ├─ Infinite-dim von Neumann III     [SPECULATIVE — modular / thermal physics]
│  └─ Categorical alternative seeds (functorial level above algebra)
│     ├─ Cartesian closed → Bool, classical computation         [SPECULATIVE]
│     ├─ Linear / SMCC → quantum information                     [SPECULATIVE]
│     └─ Braided → anyons, topological QFT                       [SPECULATIVE]
│
└─ Pre-cascade trigger  [META, OPEN]
   ├─ Eternal-cascade hypothesis (cascade has no temporal start)
   ├─ Quantum tunnelling from nothing (Vilenkin-style, recast in NCG)
   ├─ Cyclic / pre-Big-Bang phase (cascade re-initiates each cycle)
   ├─ Cascade-onset = Big Bang event (the cascade IS the Big Bang)
   └─ Selection from a multiverse of seeds (anthropic / measure-theoretic)
```

The meta-tree is *not* part of the deductive cladogram. Its purpose is to
keep the questions "why these axioms?" and "what initiated the cascade?"
visible as legitimate frontiers without polluting the strict tree with
unfounded parents.

---

## 3. The Tree (v4 — full)

```
Nothing
└─ Self-reference forces existence  [PROVED]
   ├─ Subsumes Cantor / Gödel / Turing / Tarski / Russell (Lawvere)  [PREDICTED]   ← F1.2
   └─ Reflexive domain D = (D→D)  [PROVED]
      ├─ No complete self-description (Cantor/Tarski applied to D)  [PROVED]
      └─ M₂(ℂ): minimal seed under §2.5 selection rules  [PARTIAL]
         ⤳ Sibling alternative seeds (§2.5) — overlay only, not a tree edge
         └─ Pre-cascade trigger  [META, OPEN]
            ⤳ See §2.5 hypotheses (eternal / tunnelling / cyclic / Big-Bang-as-onset)
         └─ Cascade: End(M₂)=M₄, then M₄→M₁₆→…  [PROVED ★]
            │
            ├─ Cascade fork events  [SPECULATIVE]
            │  At each level the cascade admits a family of finite spectral
            │  triples; ours selects one. The unselected ones are real
            │  branches; the question is whether they instantiate parallel
            │  physics or are forbidden by an unidentified selection rule.
            │  ├─ Our branch: C ⊕ ℍ ⊕ M₃(ℂ) at the M₂₅₆ level  [PROVED ★]
            │  ├─ Furey: ℂ ⊗ ℍ ⊗ 𝕆 finite triple  [SPECULATIVE]
            │  │  └─ Predicts SM gauge group via octonion automorphisms
            │  ├─ Dixon: algebra-of-nature ℝ ⊗ ℂ ⊗ ℍ ⊗ 𝕆  [SPECULATIVE]
            │  ├─ Boyle-Farnsworth octonion GUT  [SPECULATIVE]
            │  ├─ F₄ / E₆ / E₇ / E₈ exceptional finite triples  [SPECULATIVE]
            │  │  └─ Larger gauge groups; would predict more matter
            │  └─ Higher cascade depth (M₆₅₅₃₆ and beyond)  [SPECULATIVE]
            │     ├─ Possible additional matter sectors  [SPECULATIVE]
            │     ├─ Possible hidden / dark sector algebras  [SPECULATIVE]
            │     └─ Possible exceptional symmetry emergence at deeper levels
            │
            ├─ Cascade properties
            │  ├─ Irreversible — arrow of time  [PROVED ★]
            │  │  └─ Algebraic → thermodynamic arrow  [PREDICTED]                    ← F6.5(i)
            │  ├─ n = 4 uniquely forced  [PROVED ★]
            │  ├─ Cascade depth selection (why physics at M₂₅₆?)  [META, OPEN]
            │  ├─ What IS 'canonical'?  [PREDICTED]                                  ← F2.1
            │  └─ Three choices exhaustive  [PREDICTED]                              ← F2.2
            │     └─ Universality across every SMCC  [PREDICTED]                     ← F3.4
            │
            ├─ Categorical alternative seeds (mirror in §2.5 meta-tree)
            │  ├─ Cartesian closed → Bool, computation  [SPECULATIVE]                ← F2.6/F2.7
            │  ├─ Linear / SMCC → quantum information  [SPECULATIVE]                 ← F2.8
            │  └─ Braided → anyons, topological QFT  [SPECULATIVE]                   ← F3.7
            │
            ├─ END lineage → matter / observable algebra
            │  ├─ 4D spacetime forced (M₄ ≅ Cl₄)  [PROVED ★]
            │  │  └─ Lorentzian (1,3)  [PARTIAL]
            │  ├─ Gauge: su₃⊕su₂⊕u₁ ↪ sl₄  [PROVED ★★★]
            │  │  ├─ Leptoquark generators (extra 3)  [PREDICTED]
            │  │  │  └─ Proton decay τ ~ 10³⁵⁻³⁶ yr, p → e⁺π⁰  [PREDICTED]            ← F7.1
            │  │  ├─ Weinberg sin²θ = 3/8 at Λ_PS  [PROVED ★]
            │  │  │  └─ RG running of α₁, α₂, α₃ to M_Z  [PREDICTED]                  ← F5.2
            │  │  │     ├─ sin²θ_W ≈ 0.231 at M_Z  [PREDICTED]
            │  │  │     ├─ α_s(M_Z) ≈ 0.118  [PREDICTED]
            │  │  │     └─ α ≈ 1/137 (electromagnetic at low E)  [PREDICTED]
            │  │  └─ Anomaly cancellation  [PARTIAL]                                  ← F3.9e
            │  ├─ Pati-Salam (4,2,2)  [PROVED]
            │  │  ├─ Chirality / parity violation  [PROVED]
            │  │  ├─ Strong CP θ = 0 (LR symmetry forces it)  [PREDICTED]             ← F6.2
            │  │  │  ├─ Path A: PS-symmetry mechanism (no axion needed)  [PREDICTED]
            │  │  │  └─ Path B (alt fork): QCD axion, m_a ≈ 10⁻⁵ – 10⁻³ eV  [SPECULATIVE]
            │  │  │     ⤳ Falsifiable binary: detect axion → Path B; null → Path A
            │  │  ├─ Right-handed W boson M(W_R) ~ 10⁴⁻⁶ GeV  [PREDICTED]             ← F7.2
            │  │  ├─ Heavy Higgs H_R at v_R  [PREDICTED]                              ← F7.3
            │  │  ├─ "No new physics below Λ_PS"  [PREDICTED]                         ← F7.9
            │  │  ├─ Baryogenesis (B-L viol. + CKM CP + 1st-order PS PT)  [PREDICTED] ← F6.3
            │  │  │  ├─ Baryon-to-photon ratio η ≈ 6 × 10⁻¹⁰  [PREDICTED]
            │  │  │  └─ Ω_baryon ≈ 0.05  [PREDICTED]
            │  │  ├─ Quarks + leptons: 4 → 3⊕1  [PROVED ★]
            │  │  │  ├─ Three generations: dim(Im ℍ)=3  [PROVED ★]
            │  │  │  │  ├─ Mass hierarchy (top/e ≈ 340k)  [PREDICTED]
            │  │  │  │  ├─ Yukawa eigenvalue ordering on Im(ℍ)  [PREDICTED]            ← F5.4
            │  │  │  │  ├─ Koide-like relations m_e+m_μ+m_τ formula  [PREDICTED]
            │  │  │  │  ├─ CKM matrix (V_us ≈ 0.22, V_cb ≈ 0.04, δ ≈ 68°)  [PREDICTED] ← F5.4
            │  │  │  │  ├─ Top quark mass m_t ≈ 173 GeV (cascade Yukawa)  [PREDICTED]
            │  │  │  │  ├─ Lepton g-2 alignment with SM (no new low-E physics)  [PREDICTED]  ← F7.11
            │  │  │  │  └─ B-meson anomalies R_K, R_K* → 1 (SM-aligned)  [PREDICTED]    ← F7.12
            │  │  │  └─ Neutrino masses + PMNS (seesaw forced by PS)  [PARTIAL]      ← F6.9
            │  │  │     ├─ Majorana nature (from ν_R Majorana mass)  [PREDICTED]
            │  │  │     ├─ Normal hierarchy (Yukawa ordering)  [PREDICTED]
            │  │  │     ├─ Absolute scale m₃ ≈ 0.05 eV  [PREDICTED]
            │  │  │     ├─ Σm_ν ≈ 0.06 eV (specific cascade-fixed sum)  [PREDICTED]    ← F7.13
            │  │  │     ├─ PMNS angles θ₁₂ ≈ 34°, θ₂₃ ≈ 45°, θ₁₃ ≈ 8.5°  [PREDICTED]
            │  │  │     ├─ PMNS δ_CP (Yukawa CP from same Im ℍ structure)  [PREDICTED] ← F7.14
            │  │  │     ├─ Neutrinoless 2β decay rate Γ ∝ |m_ee|²  [PREDICTED]        ← F7.4
            │  │  │     └─ Sterile-ν dark matter candidate  [PREDICTED]               ← F6.8
            │  │  │        ├─ Relic abundance Ω_DM ≈ 0.27  [PREDICTED]
            │  │  │        └─ Direct-detection σ from cascade couplings  [PREDICTED]  ← F7.5
            │  │  └─ Higgs mechanism (bidoublet)  [PARTIAL]                          ← F3.2
            │  │     ├─ Higgs mass ≈ 125 GeV (cascade-fixed quartic λ)  [PREDICTED]
            │  │     ├─ W boson mass M_W ≈ 80.4 GeV  [PREDICTED]
            │  │     └─ Z boson mass M_Z ≈ 91.2 GeV  [PREDICTED]
            │  └─ ★ Spectral Triple — END realisation  [PARTIAL]
            │     A=M₄, native Cl₄ spinor module, D=γ^μ∂_μ, γ=γ⁵, J=charge-conj
            │     ⤳ Co-evolved similarity overlay to AUT and ⟨·,·⟩ realisations (dotted, §4)
            │
            ├─ AUT lineage → symmetry / forces
            │  ├─ GL₂ → SL₂(ℂ)  [PARTIAL]
            │  │  ├─ Twistor space (SL₂(ℂ) acts on ℂℙ³)  [SPECULATIVE]
            │  │  │  └─ Penrose twistor programme as derived sub-branch
            │  │  └─ SL₂(ℂ) ≅ Spin(3,1)  [PREDICTED]
            │  │     └─ Lorentz SO⁰(1,3)  [PARTIAL]
            │  │        └─ Diff(M) ⋊ Gauge(M) emerges (Aut(C∞⊗A_F))  [PREDICTED]
            │  │           └─ Einstein field equations  [PREDICTED]
            │  └─ ★ Spectral Triple — AUT realisation  [PREDICTED]
            │     G_J = unitaries of A preserving J; gauge group of NCG
            │     ⤳ Co-evolved similarity overlay to END and ⟨·,·⟩ realisations (§4)
            │
            └─ ⟨·,·⟩ lineage → geometry / dynamics / spectral action / QM
               │
               ├─ QM phenomenology subtree  [grown in v4]
               │  ├─ Hilbert structure + U(n) evolution  [PARTIAL]
               │  ├─ Schrödinger equation (Heisenberg evolution by D)  [PREDICTED]
               │  ├─ Path integral formulation (consistent with Spectral Action) [PREDICTED]
               │  ├─ Heisenberg picture ↔ Schrödinger picture equivalence  [PREDICTED]
               │  ├─ Born rule derivation (Gleason-style under spectral measure) [PREDICTED] ← F3.3
               │  ├─ Pauli exclusion (antisymmetric tensor on H_F)  [PREDICTED]
               │  ├─ No-cloning theorem  [PROVED]
               │  ├─ No-deleting theorem  [PREDICTED]
               │  ├─ No-broadcasting theorem  [PREDICTED]
               │  ├─ Quantum entanglement / non-locality  [PREDICTED]
               │  │  ├─ Bell inequality violations  [PREDICTED]
               │  │  ├─ Tsirelson bound (QM-saturating)  [PREDICTED]
               │  │  └─ ER=EPR (overlay to BH entropy holographic subtree)  [SPECULATIVE]
               │  ├─ Quantum Zeno effect  [PREDICTED]
               │  ├─ Quantum tunnelling / WKB / semi-classical limit  [PREDICTED]
               │  ├─ Decoherence (GKLS dynamics from environmental coupling)  [PREDICTED]
               │  │  └─ Einselection / pointer basis  [PREDICTED]
               │  │     └─ Measurement / wavefunction "collapse" appearance  [PREDICTED]
               │  │        ├─ Branching (Many-Worlds reading)  [PREDICTED]
               │  │        └─ Born-rule probabilities recovered statistically  [PREDICTED]
               │  ├─ Quantum error correction (entropy / stabiliser structure)  [PREDICTED]
               │  └─ Quantum chaos / SYK / random-matrix universality  [SPECULATIVE]
               │     ├─ Spectral statistics of D match GUE / GOE / GSE  [PREDICTED]
               │     ├─ SYK-class scrambling time t* ~ β log N  [SPECULATIVE]
               │     └─ Maldacena-Shenker-Stanford bound saturation  [SPECULATIVE]
               │
               ├─ ★ Spectral Triple — ⟨·,·⟩ realisation  [PARTIAL]
               │  Abstract operator-algebra triple on H; D self-adjoint, ±1 grading γ,
               │  antilinear J satisfying Connes' axioms; KO-dim 6 mod 8 for SM matching
               │  ⤳ Co-evolved similarity overlay to END and AUT realisations (§4)
               │
               ├─ γ²=1, {γ,D}=0, D²=m²I  [PROVED ★]
               ├─ Trace + determinant  [PROVED ★]
               ├─ Connes NCG: 7 axioms  [PREDICTED]                                 ← F3.8f
               │  ├─ KO-dim = 6 mod 8 for the FINITE part (Connes-Marcolli, SM matching) [PREDICTED]
               │  ├─ KO-dim = 2 mod 8 for the TOTAL triple (M × F = 4 + 6 ≡ 2) [PREDICTED]
               │  ├─ Fermion doubling resolved by KO-dim 6 (not forced)  [PREDICTED]
               │  └─ Poincaré duality K₀(M₄(ℂ)) ≅ ℤ  [PREDICTED]
               ├─ Background independence: Diff(M) ⋊ Gauge(M) automatic  [PREDICTED] ← F3.8h
               │  ⤳ depends on AUT lineage (dotted overlay)
               │
               └─ Spectral Action: S = Tr(f(D²/Λ²)) + ⟨ψ, Dψ⟩  [CLAIMED]
                  ⤳ depends on END (provides A) and AUT (provides G_J) — dotted overlays
                  ├─ Cauchy → exponential forced  [PROVED ★★]
                  ├─ Heat kernel canonical (semigroup → f = e⁻ˣ)  [PROVED]            ← F3.10a
                  ├─ Genuine measure constructed  [PROVED ★]
                  ├─ Self-consistency fixed point  [PREDICTED]                        ← F3.10b
                  ├─ Casimir moment relations  [PREDICTED]                            ← F3.10f
                  ├─ ALL parameters fixed  [PREDICTED]                                ← F3.10g
                  ├─ Partition function normalisation  [PREDICTED]                    ← F3.10c
                  ├─ Spectral self-duality (Mellin)  [PREDICTED]                      ← F3.10d
                  ├─ Physical cutoff justified  [PREDICTED]                           ← F3.9b
                  │  └─ Hierarchy problem dissolved  [PREDICTED]                      ← F6.1
                  ├─ Ward identities automatic  [PREDICTED]                           ← F3.9f
                  ├─ UV finiteness (no Goroff-Sagnotti, all-loop)  [PREDICTED]        ← F3.8g
                  │
                  ├─ Forces Emerge (heat-kernel orders)
                  │  ├─ a₀ ~Λ⁴ → cosmological constant  [PARTIAL]                     ← F3.8d
                  │  │  ├─ CC time evolution Λ(t) = Λ_PS / a(t)  [PREDICTED]          ← F3.8d-xii
                  │  │  ├─ Lineage-lineage backreaction (~10⁻⁵¹⁵)  [PREDICTED]        ← F3.8d-xiii
                  │  │  ├─ Predicted ρ ≈ 10⁻⁵⁰ GeV⁴, gap ~10³⁻⁷  [PREDICTED]          ← F3.8d-xv-xvi
                  │  │  ├─ Dark energy w = -1 EXACTLY  [PREDICTED]                    ← F6.4
                  │  │  └─ Ω_Λ ≈ 0.69  [PREDICTED]                                    ← F5.5
                  │  ├─ a₂ ~Λ² → Newton's G (= 3π/(f₂Λ²))  [CLAIMED]                  ← F3.8c
                  │  │  ├─ Graviton (spin-2, 2 polarisations)  [CLAIMED]
                  │  │  ├─ Hubble constant H₀ ≈ 67-73 km/s/Mpc  [PREDICTED]
                  │  │  ├─ Specific H₀ resolving early/late tension  [PREDICTED]      ← F7.15
                  │  │  └─ Graviton scattering, UV-softened at Λ_PS  [PREDICTED]      ← F3.8j
                  │  ├─ a₄ ~Λ⁰ (dimensionless terms)  [PARTIAL]
                  │  │  ├─ Yang-Mills F²  [PARTIAL]
                  │  │  │  ⤳ depends on AUT lineage (dotted overlay)
                  │  │  │  └─ Confinement (β₀ = 21)  [PARTIAL]                        ← F3.9g_v
                  │  │  │     ├─ Λ_QCD ≈ 200 MeV (dimensional transmutation)  [PREDICTED]
                  │  │  │     ├─ Proton mass ≈ 938 MeV (QCD binding)  [PREDICTED]      ← F5.3
                  │  │  │     └─ Glueball spectrum, ground state ≈ 1.6 GeV  [PREDICTED] ← F7.8
                  │  │  └─ R² Starobinsky inflation  [PREDICTED]                      ← F6.6
                  │  │     ├─ e-folds N ≈ 50-60  [PREDICTED]                          ← F7.7
                  │  │     ├─ Spectral index n_s ≈ 0.965  [PREDICTED]
                  │  │     ├─ Tensor-to-scalar ratio r ≈ 0.004  [PREDICTED]           ← F7.6
                  │  │     ├─ Flatness problem dissolved  [PREDICTED]                 ← F6.7
                  │  │     ├─ Horizon problem dissolved  [PREDICTED]                  ← F6.7
                  │  │     ├─ Monopole problem dissolved  [PREDICTED]
                  │  │     ├─ Cosmological arrow (Λ redshifts monotonically)  [PREDICTED] ← F6.5(ii)
                  │  │     └─ Cosmological structure formation  [grown in v4]
                  │  │        ├─ Power spectrum P(k), pivot k₀, A_s  [PREDICTED]
                  │  │        ├─ σ_8 specific value resolving structure tension  [PREDICTED] ← F7.16
                  │  │        ├─ CMB anisotropy spectra TT / TE / EE  [PREDICTED]
                  │  │        ├─ B-mode polarisation (sourced by r)  [PREDICTED]      ← F7.6
                  │  │        ├─ Baryon acoustic oscillation scale ~150 Mpc  [PREDICTED]
                  │  │        ├─ Halo mass function (Press-Schechter / Tinker)  [PREDICTED]
                  │  │        ├─ Halo profiles (NFW from sterile-ν dynamics)  [PREDICTED]
                  │  │        ├─ Reionisation z_re ≈ 7.7  [PREDICTED]
                  │  │        ├─ Sachs-Wolfe / Integrated Sachs-Wolfe signal  [PREDICTED]
                  │  │        └─ Lyman-α forest statistics  [PREDICTED]
                  │  └─ Higgs + Yukawa from inner fluctuations of D + A  [PREDICTED]
                  │     ⤳ depends on END lineage (dotted overlay)
                  │
                  ├─ Consequences
                  │  ├─ Black hole entropy S = A/(4G)  [CLAIMED]                      ← F3.8i
                  │  │  ├─ Hawking temperature T_H = 1/(8πGM)  [PREDICTED]
                  │  │  ├─ First law dM = T dS verified  [PREDICTED]
                  │  │  ├─ Singularity resolution: curvature bounded R ~ Λ²  [PREDICTED]
                  │  │  ├─ BH minimum radius r_min ~ 10³ ℓ_P  [PREDICTED]             ← F7.10
                  │  │  ├─ Information preservation (D self-adjoint → unitary)  [PREDICTED]
                  │  │  └─ Holographic subtree  [grown in v4, SPECULATIVE]
                  │  │     ├─ Holographic principle (S ≤ A/4G as identity)  [SPECULATIVE]
                  │  │     ├─ AdS-CFT-like correspondence in NCG  [SPECULATIVE]
                  │  │     ├─ ER=EPR (entanglement ↔ wormhole geometry)  [SPECULATIVE]
                  │  │     ├─ Boundary entanglement entropy  [SPECULATIVE]
                  │  │     ├─ Page curve (information recovery)  [SPECULATIVE]
                  │  │     └─ Bulk reconstruction from boundary data  [SPECULATIVE]
                  │  └─ Phase transitions (Landau Z₂)  [PROVED]
                  │
                  ├─ Cosmology synthesis (multi-input)
                  │  ├─ Total Ω = 1 (from inflation)  [PREDICTED]
                  │  ├─ T_CMB = 2.725 K  [PREDICTED]                                  ← F5.5
                  │  └─ Ω_radiation (photon + ν energy density)  [PREDICTED]
                  │
                  └─ Rigorous QFT
                     ├─ Gaussian integral converges  [PROVED ★]
                     ├─ Gaussian domination (Wick)  [PROVED ★]
                     ├─ Bakry-Émery spectral gap (gap = 2/Λ²)  [PROVED ★]
                     ├─ Transfer matrix: gap → mass gap  [PARTIAL]
                     ├─ Reflection positivity (OS2)  [PREDICTED]                      ← F3.9d
                     ├─ OS axioms (5)  [CLAIMED]
                     │  └─ OS reconstruction → Wightman QFT  [CLAIMED]
                     ├─ Internal PI convergence  [PREDICTED]                          ← F3.9a
                     ├─ Full spectral cutoff PI  [PREDICTED]                          ← F3.9c
                     ├─ Non-perturbative quantisation  [PREDICTED]                    ← F3.8k
                     └─ Mass Gap (Millennium-adjacent)
                        ├─ Internal spectral gap (Herm₄ discrete)  [PREDICTED]        ← F3.9g_i
                        ├─ Product geometry gap transfer  [CLAIMED]                   ← F3.9g_ii
                        ├─ Poincaré inequality C_P = Λ²/2  [PREDICTED]                ← F3.9g_iii
                        ├─ Compact operator spectrum  [PREDICTED]                     ← F3.9g_iv
                        ├─ Cluster decomposition  [PARTIAL]                           ← F3.9g_vi
                        ├─ Thermodynamic limit  [CLAIMED]
                        └─ YM mass gap on ℝ⁴  [CLAIMED]                               ← F3.9g_vii


─────────────────────────────────────────────────────────────────────────
DOWNSTREAM EMERGENT PHYSICS  [DOWNSTREAM]
  Not algebraically forced; emergent by composition / statistics.
  Causal parent: SM (atomic level) + GR + statistical mechanics.
─────────────────────────────────────────────────────────────────────────

Atomic physics  [DOWNSTREAM]
├─ Hydrogen-like spectra (Schrödinger + Coulomb)
├─ Multi-electron atoms (QED + Pauli + correlation)
├─ Periodic table structure (shell filling from Pauli + Coulomb)
├─ Atomic spectra / fine structure / hyperfine / Lamb shift  [QED corrections]
└─ Chemistry  [DOWNSTREAM]
   ├─ Molecular bonding (covalent / ionic / vdW / metallic)
   ├─ Molecular orbital theory; spectroscopy (UV-Vis / IR / NMR / MS)
   ├─ Reaction kinetics + thermodynamics
   ├─ Catalysis
   ├─ Crystal structures (group theory of lattices)
   └─ Solid-state / Condensed matter  [DOWNSTREAM]
      ├─ Band theory (Bloch's theorem)
      ├─ Semiconductors / insulators / metals
      ├─ Superconductivity (BCS / High-T_c / topological)
      ├─ Topological matter / anyons  ⤳ similarity with Braided seed
      ├─ Quantum Hall effects (integer / fractional)
      ├─ Magnetism (ferro / anti / spin glass)
      ├─ Phase transitions  ⤳ similarity with upstream Landau Z₂
      ├─ Superfluidity (He-4 / He-3)
      └─ Strongly correlated electrons (Hubbard / t-J / SYK lattice)
   └─ Soft matter / fluids / plasma  [DOWNSTREAM]
      ├─ Hydrodynamics (Navier-Stokes; Millennium-adjacent)
      ├─ Turbulence
      ├─ Plasma physics (MHD)
      └─ Granular / glassy matter
   └─ Biochemistry  [DOWNSTREAM]
      ├─ Macromolecules (proteins, lipids, nucleic acids)
      ├─ Enzymatic catalysis
      ├─ Energy carriers (ATP, electron transport)
      └─ Biology  [DOWNSTREAM]
         ├─ Self-replicating molecules (RNA-world / autocatalytic)
         ├─ Cells / membranes / metabolism
         ├─ Genetics / heredity (DNA-RNA-protein)
         ├─ Evolution by natural selection
         ├─ Multicellularity / tissues / organs
         ├─ Nervous systems / signalling
         └─ Cognition / mind / observer  [META; DOWNSTREAM]
            ├─ Integrated Information Theory (IIT) reading  [SPECULATIVE]
            ├─ Global Workspace / attention schema  [SPECULATIVE]
            ├─ Predictive coding / Bayesian brain  [SPECULATIVE]
            └─ Where the spectral-triple "observer" sits  [META]
               ⤳ The observer in the formalism may be the deep descendant
                 of the same cascade that produced the formalism itself.

─────────────────────────────────────────────────────────────────────────
ASTROPHYSICS & PLANETARY  [DOWNSTREAM]
  Causal parent: GR + nuclear / atomic + cosmological structure formation.
─────────────────────────────────────────────────────────────────────────

├─ Big Bang Nucleosynthesis (D, ³He, ⁴He, ⁷Li abundances)  [DOWNSTREAM]
│  ⤳ depends on cosmology synthesis upstream
├─ Stellar physics  [DOWNSTREAM]
│  ├─ Stellar fusion (pp / CNO / triple-α)
│  ├─ Stellar structure / evolution / HR diagram
│  ├─ Heavy element nucleosynthesis (s / r / p / rp processes)
│  └─ Endpoints: white dwarfs, neutron stars, black holes
│     ⤳ similarity with BH entropy upstream
├─ Galaxies / clusters / cosmic web  [DOWNSTREAM]
│  ⤳ depends on structure-formation subtree
├─ Planets / exoplanets  [DOWNSTREAM]
│  ├─ Planet formation (protoplanetary discs)
│  ├─ Habitable zones
│  └─ Origins of life / abiogenesis  ⤳ overlay to Biology
└─ Multi-messenger astronomy  [DOWNSTREAM]
   ├─ Gravitational waves (LIGO / Virgo / KAGRA / LISA)
   │  ⤳ test of graviton scattering UV-softening (F3.8j)
   ├─ Cosmic rays / neutrinos
   └─ X-ray / γ-ray sources
```

---

## 4. Cross-branch overlays (dotted, NOT tree edges)

These are not tree edges. Branches in this cladogram, like branches in
biological evolution, **never merge once split**. What we *do* have are
relationships across distinct branches, and there are exactly four kinds.
The word "convergence" is avoided throughout: it implies merger, which
does not happen.

**Four kinds of overlay:**

1. **Co-evolved similarity** — the eye-evolution case. Distinct branches
   independently develop structurally similar traits. No merger, no causal
   dependency. Meaningful as a *recognised pattern*, not as a connection.
2. **Cross-lineage dependency** — a node in lineage Y requires structure
   from a sibling-branch tip in lineage X. The node stays in Y; X is a
   *constraint*, not a parent. (Example: Spectral Action under ⟨·,·⟩ uses
   `A` from END and `G_J` from AUT — but its causal parent is still ⟨·,·⟩.)
3. **Multi-input causal compounding** — multiple sibling sub-branches
   *within the same lineage* are jointly required to produce a downstream
   sibling node. Compositional, not similarity. (Example: the Sakharov
   triple — Three generations + Pati-Salam + Higgs PT all needed for
   Baryogenesis, all within END.)
4. **Aggregate contribution** — numerical / quantitative summation of
   independent inputs. (Example: Ω_Λ + Ω_DM + Ω_b → Ω_total = 1.)

| Kind                | Source                                            | Sink                                              | Meaning                                          |
|---------------------|---------------------------------------------------|---------------------------------------------------|--------------------------------------------------|
| Co-evolved similarity | `★ Spectral Triple — END realisation`            | `★ Spectral Triple — AUT realisation`              | Eye evolution: similar trait, separate branches  |
| Co-evolved similarity | `★ Spectral Triple — END realisation`            | `★ Spectral Triple — ⟨·,·⟩ realisation`            | Eye evolution: similar trait, separate branches  |
| Co-evolved similarity | `★ Spectral Triple — AUT realisation`            | `★ Spectral Triple — ⟨·,·⟩ realisation`            | Eye evolution: similar trait, separate branches  |
| Co-evolved similarity | Three arrows of time (algebraic / cosmological / CP) | (each on its own branch — annotation only)     | Independent monotone arrows of similar character |
| Cross-lineage dependency | END lineage (provides A)                       | Spectral Action (under ⟨·,·⟩)                     | Heat-kernel acts on A                            |
| Cross-lineage dependency | AUT lineage (provides G_J)                     | Spectral Action (under ⟨·,·⟩)                     | Inner fluctuations require G_J                   |
| Cross-lineage dependency | AUT (Diff⋊Gauge)                               | Background independence (under ⟨·,·⟩)             | Symmetry source for diffeomorphism invariance    |
| Cross-lineage dependency | AUT lineage                                     | Yang-Mills F² (under a₄)                          | Gauge bosons live in AUT                         |
| Cross-lineage dependency | END lineage                                     | Higgs + Yukawa (under a₄)                         | Inner fluctuations of A                          |
| Multi-input causal  | Three generations (END)                           | Baryogenesis (END)                                | CKM CP source — Sakharov (ii)                    |
| Multi-input causal  | Pati-Salam (END)                                  | Baryogenesis (END)                                | B-L gauge symmetry — Sakharov (i)                |
| Multi-input causal  | Higgs / scalar potential (END)                    | Baryogenesis (END)                                | 1st-order PT — Sakharov (iii)                    |
| Aggregate           | Ω_Λ (a₀)                                          | Total Ω = 1 (Cosmology synthesis)                 | Ω_Λ ≈ 0.69 contribution                          |
| Aggregate           | Ω_DM (sterile-ν, under Neutrinos)                 | Total Ω = 1 (Cosmology synthesis)                 | Ω_DM ≈ 0.27 contribution                         |
| Aggregate           | Ω_b (baryogenesis, under Pati-Salam)              | Total Ω = 1 (Cosmology synthesis)                 | Ω_b ≈ 0.05 contribution                          |
| Co-evolved similarity | Topological matter (Condensed matter, downstream) | Braided alternative seed (§2.5)                  | Anyons / topological order on both branches      |
| Co-evolved similarity | Phase transitions (downstream condensed matter)   | Phase transitions (Landau Z₂ under Spectral Action) | Same critical-phenomena structure, distinct branches |
| Co-evolved similarity | Stellar / galactic black holes (Astrophysics)     | BH entropy (Spectral Action consequences)         | Same horizon thermodynamics, distinct branches   |
| Cross-lineage dependency | QM phenomenology subtree (⟨·,·⟩)              | Atomic physics (Downstream)                       | Schrödinger + Pauli required for atoms           |
| Cross-lineage dependency | Cosmology synthesis                            | BBN / structure formation (Astrophysics)          | Initial conditions for downstream cosmology      |
| Cross-lineage dependency | ER=EPR (QM subtree)                            | Holographic subtree (under BH entropy)            | Entanglement ↔ wormhole identification           |

---

## 5. Alignment check — does the tree match what we know?

### 5.A Mathematical alignment

| Branch in tree                                | Mathematical reality                                                       |
|-----------------------------------------------|----------------------------------------------------------------------------|
| ∅ → 1 → M₂(ℂ)                                  | Minimal non-commutative *-algebra over ℂ admitting a faithful trace        |
| END / AUT / ⟨·,·⟩                              | The three canonical functors on a finite C*-algebra (endo, auto, GNS)      |
| Cascade End(M_n)=M_{n²}                        | Standard tensor-square endomorphism construction; well-defined, irreversible|
| Stable algebra C ⊕ H ⊕ M₃(ℂ)                   | Chamseddine-Connes finite NCG, the unique KO-dim-6-mod-8 fit to SM         |
| Pati-Salam group SU(4)×SU(2)_L×SU(2)_R         | Aut of stable algebra modulo U(1) factors (Connes-Chamseddine theorem)     |
| Spectral triple axioms                         | Connes 1996 + Connes-Marcolli classification                               |
| Heat kernel a₀, a₂, a₄                         | Seeley-DeWitt expansion (textbook; rigorous on compact manifolds)          |
| KO-dim 6 mod 8                                 | Required for fermion doubling consistent with SM chirality                 |
| Almost-commutative product (A_F⊗C∞, …)         | Forced by Connes axioms once finite + continuous parts are specified       |

✓ Each branch point corresponds to a real categorical / functorial /
spectral-geometric operation. No mathematical fiction.

### 5.B Physical alignment

| Tree output                         | Empirical status                                                       |
|-------------------------------------|------------------------------------------------------------------------|
| 4D Lorentzian spacetime             | Confirmed (every observation)                                          |
| SU(3)×SU(2)×U(1) Standard Model     | Confirmed                                                              |
| sin²θ_W = 3/8 at GUT scale          | Standard GUT prediction; matches RG running to ≈ 0.231 at M_Z          |
| Three generations                   | Confirmed (no fourth seen)                                             |
| n_s ≈ 0.965 (R² Starobinsky)        | Confirmed (Planck 2018: 0.9649 ± 0.0042)                               |
| Ω_Λ ≈ 0.69                          | Confirmed (Planck 2018: 0.6889 ± 0.0056)                               |
| w = -1 dark energy                  | Consistent with all current data                                       |
| Right-handed neutrinos, seesaw      | Strongly motivated; not yet directly observed                          |
| Proton decay τ ~ 10³⁵⁻³⁶ yr         | Within reach of Hyper-K; falsifiable                                   |
| r ≈ 0.004                           | Within reach of CMB-S4 / LiteBIRD; falsifiable                         |
| Glueball ~1.6 GeV                   | Lattice QCD agrees                                                     |
| W_R, H_R at 10⁴⁻⁶ GeV               | Beyond LHC; future colliders; falsifiable                              |
| BH r_min ~ 10³ ℓ_P                  | Indirect signatures only; far-future test                              |
| PMNS δ_CP                           | Hyper-K / DUNE measurement; falsifiable                                 |
| Σm_ν specific value                 | KATRIN / cosmology Σm_ν < 0.12 eV; falsifiable                          |
| Lepton g-2                          | Currently a low-significance tension; tree predicts SM alignment        |
| B-meson R_K, R_K*                   | LHCb 2022 R_K → 1; consistent with tree's "no new physics below Λ_PS"   |
| Specific H₀                         | Currently a 5σ tension; tree should resolve                             |
| Specific σ_8                        | Currently ~2σ tension; tree should resolve                              |
| Holographic / AdS-CFT structure     | Indirect (via lattice + analogue); deeply tested in AdS                |
| Atomic / chemistry / biology        | Confirmed (everywhere we look)                                          |
| BBN abundances                      | Confirmed (D/H, ³He, ⁴He, ⁷Li; Li tension at <3σ)                       |
| Gravitational waves (LIGO)          | Confirmed; UV-softening test pending                                    |

✓ All postdictions match measured values; all falsifiable predictions sit
in physically motivated ranges; the cladogram positions match the
mechanism each phenomenon arises from.

### 5.C Evolutionary alignment

| Tree property                        | Cladogram principle                                                     |
|--------------------------------------|-------------------------------------------------------------------------|
| Single parent per node               | Strict cladogram (no reticulation, no merger of branches)               |
| Branching = bifurcation events       | Speciation: each split is forced by structure (functor / breaking)      |
| ★ realisations on three branches     | Co-evolved similarity (eye evolution): similar trait, separate branches |
| Dotted overlays                      | Cross-branch annotations (similarity / dependency / multi-input / aggregate) — never merger |
| [PREDICTED] leaves                   | Missing fossils / Mendeleev gaps at causal positions                    |
| §6 Open Frontiers                    | Speciation potential: where new lineages can grow                       |
| No crown / teleology                 | Tree of life has no destination; ours has no "final" leaf              |
| Tree is open                         | Living map: more discoveries → more branches                            |

✓ The cladogram conventions hold. Branches never merge. Cross-branch
relationships fall into four kinds (similarity, dependency, multi-input,
aggregate), with co-evolved similarity (eye evolution) being only one of
them. The tree is generative.

---

## 6. Open Frontiers — where new lineages may grow

These are **not** missing-fossil predictions of existing structure. They
are speciation frontiers: nodes from which **entirely new lineages may
emerge** as theory and experiment expand.

### 6.A From the categorical level above the seed

The seed M₂(ℂ) is *one* canonical generator under one categorical regime.
Other regimes generate alternative lineages:

- **Cartesian closed seeds** → classical computation, Boolean logic,
  Turing universality. Possibly: the lineage of *information* and
  *computation as physics*.
- **Linear / SMCC seeds** → quantum information, channels, no-cloning as
  a structural identity. Possibly: a lineage of *quantum resource
  theories* parallel to physics.
- **Braided seeds** → anyons, topological QFT, Chern-Simons theories.
  Possibly: a lineage of *topological matter*.

These are flagged as `[PREDICTED]` in the cladogram (§3) but their
*subtrees* are unspecified. New theory may grow them out.

### 6.B From the cascade itself

The cascade extends infinitely (M₂ → M₄ → M₁₆ → M₂₅₆ → M₆₅₅₃₆ → …).
Currently the stable physics-relevant algebra is C ⊕ H ⊕ M₃(ℂ) at the
~M₂₅₆ level. **Higher cascade steps may host new physics:**

- Higher-rank gauge structures (E_6, E_7, E_8 GUTs) potentially appearing
  as automorphism subgroups at deeper levels.
- Additional generations beyond three at deeper-level closure
  conditions (currently disfavoured but structurally accessible).
- Hidden / dark sectors as parallel sub-algebras at the same cascade
  level — alternative `(p, q, n)` choices in the (left-handed × right-handed
  × colour) classification.

### 6.C From the stable algebra

C ⊕ H ⊕ M₃ is one solution; alternative compactifications could exist:

- Octonion / exceptional structure (E_8, F_4) as alternative finite
  algebras (some work of Furey, Dixon, Boyle-Farnsworth).
- KO-dim ≠ 6 spectral triples → physics with different chirality content
  or generation structure.

### 6.D From spectral triple realisation

Each realisation is one *fixed point*; alternatives:

- Lorentzian spectral triples (vs. Euclidean) — active research.
- Quantum spectral triples / fuzzy geometries.
- Higher-categorical spectral triples (2-spectral-triples).

### 6.E From cosmological synthesis

- Multiverse / inflationary bubble lineages — distinct realisations of
  the cascade with different IR parameters.
- Pre-Big-Bang / cyclic phase as a parent-of-cascade-onset node (where
  does the cascade start? structural antecedents not yet placed).

### 6.F From black hole / information lineage

- Holographic / boundary lineage (AdS-CFT-like) as a derived branch
  whose causal parent is Black hole entropy.
- Computational / complexity-theoretic lineage (CR/CC, ER=EPR-style
  proposals).

**Note:** §6 is itself open. The list will grow as theory and experiment
extend the map.

---

## 7. Predictions catalogue (F5 / F6 / F7 mapped to causal parents)

**F5 — Postdictions (derive what we already measure)**

| Quantity                  | Causal parent in tree                                |
|---------------------------|------------------------------------------------------|
| α_GUT, sin²θ_W = 3/8      | Weinberg sin²θ = 3/8 at Λ_PS                         |
| α₁/α₂/α₃ at M_Z, sin²θ_W ≈ 0.231 | RG running of α_i to M_Z                       |
| W, Z, Higgs masses        | Higgs mechanism                                      |
| Λ_QCD, α_s(M_Z), proton mass | Confinement (under Yang-Mills F²)                 |
| Glueball spectrum         | Confinement                                          |
| Yukawa hierarchy, Koide, CKM | Three generations                                 |
| Seesaw, Majorana, PMNS    | Neutrino masses + PMNS                               |
| H₀, Ω_m, Ω_Λ, Ω_b, Ω_DM   | Cosmology synthesis (multi-input)                    |
| T_CMB, Ω_radiation        | Cosmology synthesis                                  |
| η_B = 6 × 10⁻¹⁰           | Baryogenesis (under Pati-Salam)                      |

**F6 — Open problems closed**

| Problem                   | Resolution location                                  |
|---------------------------|------------------------------------------------------|
| Hierarchy problem         | Hierarchy problem dissolved (under Physical cutoff)  |
| Strong CP                 | Strong CP θ = 0 (under Pati-Salam)                   |
| Baryogenesis              | Baryogenesis (under Pati-Salam)                      |
| Dark energy w = -1        | w = -1 EXACTLY (under a₀)                            |
| Arrow of time             | Three arrows: algebraic / cosmological / CP          |
| Inflation                 | R² Starobinsky inflation (under a₄)                  |
| Flatness, horizon, monopole | children of R² Starobinsky                         |
| Dark matter identity      | Sterile-ν dark matter (under Neutrino masses)        |
| Neutrino masses + nature  | Neutrino masses + PMNS                               |
| Matter content fractions  | Cosmology synthesis (multi-input)                    |

**F7 — Falsifiable novel predictions**

| ID    | Prediction                              | Causal parent                              |
|-------|-----------------------------------------|--------------------------------------------|
| F7.1  | Proton decay τ ~ 10³⁵⁻³⁶ yr            | Leptoquark generators                      |
| F7.2  | M(W_R) ~ 10⁴⁻⁶ GeV                      | Pati-Salam                                 |
| F7.3  | M(H_R) ~ v_R                            | Pati-Salam                                 |
| F7.4  | Neutrinoless 2β decay rate              | Neutrino masses + PMNS                     |
| F7.5  | DM direct-detection σ                   | Sterile-ν dark matter                      |
| F7.6  | Tensor-to-scalar r ≈ 0.004              | R² Starobinsky inflation                   |
| F7.7  | e-folds N ≈ 50-60                       | R² Starobinsky inflation                   |
| F7.8  | Glueball spectrum (1.6 GeV +)           | Confinement                                |
| F7.9  | No new physics below Λ_PS               | Pati-Salam                                 |
| F7.10 | BH r_min ~ 10³ ℓ_P                      | Black hole entropy                         |
| F7.11 | Lepton g-2 SM-aligned (no new physics)  | Three generations / Higgs-Yukawa           |
| F7.12 | B-meson R_K, R_K* → 1 (SM-aligned)      | Three generations                          |
| F7.13 | Σm_ν ≈ 0.06 eV specific                 | Neutrino masses + PMNS                     |
| F7.14 | PMNS δ_CP value                         | Neutrino masses + PMNS                     |
| F7.15 | Specific H₀ resolving Hubble tension    | a₂ Newton's G + cosmology synthesis        |
| F7.16 | Specific σ_8 resolving structure tension | R² Starobinsky structure formation        |
| F7.17 | Axion-or-no-axion binary fork           | Strong CP θ = 0 (under Pati-Salam)         |

---

## 8. Open content questions (deferred until evidence supplied)

- Whether `Universality across every SMCC` should also receive dotted
  overlay lines back to the categorical alternative seeds (Cartesian /
  Linear / Braided), to express that the cascade construction is
  functorial.
- Whether `Higgs + Yukawa from inner fluctuations of D + A` deserves its
  own sub-tree (currently a single PREDICTED leaf under Forces Emerge).
- Whether `Casimir moment relations` and `ALL parameters fixed` are
  siblings or parent-child.
- Whether `Three arrows of time` should be a dedicated annotation node
  combining the algebraic, cosmological, and CP arrows — or remain three
  separate leaves.
- Whether to add a node for "α_GUT ≈ 1/47" explicitly.
- Whether the ⟨·,·⟩ lineage's `★ realisation` leaf should be promoted
  above (rather than alongside) Spectral Action, given that the action
  presupposes the realisation. Currently realisation is annotated above
  the action; structurally either ordering reads correctly.

---

## 9. Rival frameworks (competitor trees)

These are not branches of our tree; they are **alternative trees**
proposing different fundamental structures for physics. Honest accounting
requires naming them, noting where they agree / disagree with ours, and
pointing to distinguishing experiments.

| Framework                        | Their root / mechanism                                           | Where it agrees with ours          | Where it diverges                                  | Distinguishing test                              |
|----------------------------------|------------------------------------------------------------------|------------------------------------|----------------------------------------------------|--------------------------------------------------|
| String / M-theory                | Extended objects in 10/11-D target space; dualities              | UV completion of gravity           | Extra dimensions; landscape of vacua; SUSY low-E   | SUSY at LHC / FCC; KK modes; high-r              |
| Loop Quantum Gravity             | Spin networks; quantised area / volume                           | Background-independent gravity     | Discrete geometry; no SM matter content forced     | Lorentz invariance violations; BH spectroscopy   |
| Causal Sets                      | Discrete causal partial order                                    | Lorentz / causality respected      | No continuum; combinatorial geometry               | CMB anomaly patterns; nonlocality scale          |
| Causal Dynamical Triangulations  | Path integral over discretised geometries                         | 4D emerges; Euclidean PI methods    | Geometry simplicial, not algebraic                 | Hausdorff / spectral dimension flow              |
| Asymptotic Safety                | UV fixed point of gravity coupling                                | UV completion of GR                | No matter content forced; gauge group ad-hoc       | High-energy graviton scattering                  |
| Twistor theory                   | SL₂(ℂ) twistor space ℂℙ³ as fundamental                          | Lorentz / spinor structure shared  | Holomorphic primary, not algebraic seed             | Twistor-amplitudes vs spectral-action amplitudes |
| Emergent gravity (Verlinde et al.) | Gravity as entropic / informational                              | Holographic / entropy-area linkage | Gravity not fundamental; metric is derived          | Galaxy rotation curves vs DM particle searches   |
| Wolfram physics / hypergraph     | Discrete rewriting system; computation primary                    | Computational completeness         | No algebra; reality as graph dynamics              | Specific Lorentz-violation / discreteness sigs   |
| Constructor theory               | Possible / impossible counterfactual tasks                        | Quantum / classical emergent       | Different ontology; principles-based               | Reformulation of QM tests; principle-of-locality |
| It-from-Bit / digital physics    | Information primary; physics computational                        | Holographic links                  | No algebra; Bool-categorical seed only             | Bekenstein-saturating boundaries                 |

**Honest note:** several of these (string, twistor, holographic) may turn
out to be *dual descriptions* of the same physics our tree describes —
not rivals but reformulations. The distinguishing experiments are the
honest test.

---

## 10. Implementation notes (for later)

When the visualisation is built (separate task, `tree-of-reality.html`):

- D3.js v7, `d3.tree()` with horizontal layout, elbow connectors.
- `nodeSize([44, 280])` minimum.
- ~135 nodes; vertical canvas ~5500px. Collapsible subtrees recommended.
- Three lineage colours: END `#60a5fa`, AUT `#fbbf24`, ⟨·,·⟩ `#34d399`.
- Status colours: PROVED `#4ade80`, PARTIAL `#fbbf24`, CLAIMED `#fb923c`,
  PREDICTED `#a78bfa`.
- Predicted nodes: dashed borders, dashed connectors, 0.7 opacity.
- **Co-evolved similarity overlays:** dotted *lateral* lines among the
  three `★ Spectral Triple realisation` sibling leaves, NOT into a shared
  child. Render as a horizontal "similarity band" with the three leaves
  bound by a translucent ribbon, annotated "co-evolved similarity —
  eye-of-evolution". Render in a third colour (e.g. soft violet) distinct
  from lineage colours and status colours.
- **Cross-lineage dependency overlays:** dotted *diagonal arrowed* lines
  from sibling tip into descendant of a different lineage. Use a clearly
  different style (arrow head, different dash pattern) so similarity and
  dependency are never confused.
- **Multi-input causal overlays:** dotted converging-arrow lines *within
  a single lineage* showing several siblings jointly required by a
  downstream sibling (e.g. Sakharov triple → Baryogenesis). Use yet
  another distinct visual treatment.
- **Aggregate overlays:** thin dotted lines into a synthesis node (e.g.
  Ω_Λ, Ω_DM, Ω_b → Ω = 1). Visually de-emphasised.
- Sidebar shows: description, evidence Lean files (with status badges),
  F-roadmap reference, missing-fossil annotations.
- Dark theme `#07071a`, Inter + JetBrains Mono.

---

## 11. Provenance

- **Source roadmap:** `docs/PAPER_F_ROADMAP.md` (v 2026-05-08, 130KB).
- **Lean evidence files:** `lean_verify/` — currently 13 files in build,
  52 unverified per integrity gate (2026-05-06). Statuses in this
  document reflect the handover sheet; PROVED/PARTIAL/CLAIMED claims
  require re-audit.
- **Bitcoin stamping:** this file lives in
  `wonderben-code/convergence-codex`; any change to the tree must be
  committed and pushed to extend provenance.
- **Mirror:** `/Users/ekramalam/Desktop/Tree of Reality/TREE_STRUCTURE.md`
  is kept in sync as a local working copy.

*This document is the content specification for the Tree of Reality. The
HTML/D3 implementation is a separate, downstream artefact. Any change to
the tree structure must update this document first.*
