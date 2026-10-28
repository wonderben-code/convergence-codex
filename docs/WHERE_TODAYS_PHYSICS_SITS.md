# Where today's physics sits on the Tree of Reality

**Reference table, 25 October 2026.** A map from the physics everyone recognises to the branch of
the tree it grows on, how it emerges there, and how solid that branch is. Grades and link codes
are from the capstone *The Tree of Reality: An Evolutionary Theory of Everything*
(DOI 10.5281/zenodo.23011897, 28 Sep 2026): **GENUINE** = machine-checked theorem on standard
axioms; **PARTIAL** = real theorems cover part of the headline, residue named; **POSTULATE** =
declared modelling choice; **◇ OPEN** = a precisely stated wall with no covering theorem.
Rows marked PREDICTED are leaves on the website's tree (infinitography.com/tree-of-reality)
carried from the June 2026 cladogram; the capstone does not grade them.

The tree's shape: a **trunk** (L1–L7: existence → seed → cascade → three lineages), then three
**lineages** — End (what things are: matter, spacetime, gauge), Aut (how they transform:
symmetry, gravity), ⟨·,·⟩ (how they are known: quantum mechanics) — and a **crown** where the
three meet (the spectral triple and everything built on it).

| Today's physics | Where it sits | How it emerges | Grade |
|---|---|---|---|
| Why anything exists | Trunk, L1 (root) | Lawvere's fixed-point theorem: self-reference forces existence | GENUINE |
| The first thing: a qubit | Trunk, L3 | M₂(ℂ), the smallest algebra over ℂ in which order of operations matters | GENUINE |
| Growth, and the arrow of time | Trunk, L4–L5 | the cascade M₂ → M₄ → M₁₆ → M₂₅₆ → …, by End-iteration; irreversible | GENUINE |
| The three lineages themselves | Trunk, L7 | End · Aut · ⟨·,·⟩ as the only canonical operations | POSTULATE (Chain Theory's three definitions may supply a derivation — Q9) |
| Spacetime is 4-dimensional | End, L8 | the two-qubit algebra M₄ *is* Cl₄(ℂ), and only in dimension 4 | GENUINE |
| Special relativity (one time, three space) | End, L9; Lorentz group SO⁺(1,3) on Aut | the real Clifford algebra of signature (1,3) | PARTIAL (Euclidean alternative not fully excluded; Chain Theory's Pell argument excludes it — R7) |
| Standard Model gauge forces (strong, weak, electromagnetic) | End, L10–L11 | su(3) ⊕ su(2) ⊕ u(1) embedded in M₁₆ = M₄ ⊗ M₄ via Pati–Salam | PARTIAL |
| Colour (three quark colours) | End, L13 | the 4 splits as 3 ⊕ 1 | GENUINE |
| Why the weak force is left-handed | End, L12 | two binaries at M₁₆ = End(M₄): which factor is covariant (exchanged only by anti-automorphisms — charge-conjugation type) and which chiral half SU(2)_L acts on (exchanged only by the improper element — parity); refined 28 Oct, R9′ | POSTULATE |
| Three generations of matter | End, L14 | the three imaginary quaternions inside M₂(ℂ) | POSTULATE. Chain Theory's attach sites are *not* the quaternions (Q5/R2, refuted); its ≤ 3 counting holds as frames (Q4). **Consequence found 28 Oct (R15):** read on the generation space, the quaternion structure forces real Yukawas, hence no CP violation from couplings (Lean) — so CP violation must be *spontaneous*, from the Higgs bidoublet's vacuum phase; this reproduces all quark masses, mixing and the measured CP violation, at the cost of one tuning for strong CP |
| The Higgs | End, L15 | the bidoublet scalar; coupling window g²/N ≤ λ̃ ≤ g² | PARTIAL (no 125 GeV claim is made). **Tension with data, then resolved (28 Oct):** with Standard-Model running alone the window implies m_H ≈ 131–176 GeV, above the measured 125.2. The repair, the scalar σ, turns out to be *forced* on the tree's own Pati–Salam 16 once neutrinos have Majorana masses; with σ (Chamseddine–Connes 2012 boundary conditions) the window gives m_H = 125.20 GeV at a seesaw-consistent σ scale ~10¹⁴ GeV, with the vacuum metastable as in the Standard Model. A computation, not a proof (one-loop above σ, dominant Yukawas). See `docs/chain-theory/09_…` and `10_results_third_pass.md` |
| Weinberg angle (electroweak mixing) | End, L17 | sin²θ_W = 3/8 as an exact trace ratio on the chiral 16 | PARTIAL |
| Anomaly cancellation (why the SM is consistent) | End, L16 | the perturbative anomaly table vanishes on the chiral 16 | PARTIAL |
| Quantum mechanics (Hilbert space, Schrödinger equation, unitary evolution) | ⟨·,·⟩, L21 | GNS on the trace state → Hilbert space; Stone's theorem → Schrödinger | PARTIAL |
| The Born rule (probabilities) | ⟨·,·⟩, under L21 | **cited input, not derived** (Gleason) | POSTULATE (Chain Theory derives it conditionally — Q8) |
| Gravity / general relativity (Einstein's equations) | Aut, L22 | the spectral action's heat-kernel expansion should yield the Einstein–Hilbert term | ◇ OPEN — gap G5, gated on G2 |
| Quantum gravity | not a separate branch | gravity and the Standard Model come from *one* functional (the spectral action) on *one* Dirac operator: L18–L19 together with L22 | PARTIAL + OPEN |
| Quantum field theory (fields, particles, rigorous QFT) | Crown, L18–L20 and L23 | spectral triple → spectral action → Boltzmann measure; Osterwalder–Schrader reconstruction → Wightman QFT | PARTIAL; reconstruction OPEN |
| Yang–Mills and the mass gap (why the strong force's particles are massive) | Crown, L23 | transfer matrix → spectral gap → mass gap; walls W1–W4, gaps G1/G3/G4 | ◇ OPEN (Chain Theory's read cap is a candidate mechanism — Q6) |
| The numbers (what has actually been computed) | Crown, L24 | the Weinberg ratio 3/8 and the Higgs window; no coupling constant | PARTIAL |
| Cosmological constant / dark energy | downstream of the spectral action (a₀ ~ Λ⁴) | the Λ⁴ term of the action | PREDICTED; the one number computed (sign right, ~112 of 120 orders closed; DOI 10.5281/zenodo.23147122) |
| Cosmology (inflation, structure formation, cosmic arrow) | downstream of L19 | the R² (Starobinsky) term of the spectral action | PREDICTED |
| Black holes (entropy S = A/4G, Hawking temperature) | downstream of L22 | consequences of Einstein's equations once L22 exists | PREDICTED |
| Thermodynamics / entropy arrow | trunk, downstream of L5 | algebraic irreversibility → thermodynamic arrow | PREDICTED |
| Neutrino masses, sterile-neutrino dark matter, leptoquarks, proton decay | End-lineage leaves | the extra generators of sl₄ beyond the SM algebra | PREDICTED (June 2026 instrument; the capstone calls these "a separate instrument … not restated here") |
| Fermion mass hierarchy, CKM mixing, strong CP, axions, baryogenesis | End-lineage leaves | Yukawa structure from inner fluctuations of D | PREDICTED / POSTULATE (mass hierarchy carried as POSTULATE in the gaps table) |

## What this table says, honestly

- **Proved:** the trunk and the geometry — existence, the seed, growth, four-dimensional
  spacetime, colour.
- **Partly proved, residue named:** the Standard Model's structure, the Higgs window (proved as
  mathematics; consistent with the measured Higgs mass once the σ field the tree forces is included), the
  Weinberg angle, quantum mechanics (with the Born rule declared as an input).
- **Declared rather than derived:** the three lineages, chirality, three generations.
- **Open, with the missing piece described:** gravity (L22) and rigorous QFT / the mass gap
  (L23) — the two ◇ boxes, staked as predictions in *The Staked Gaps* (G1–G6) and refined in
  *The Refined Gaps* (R1–R12).
- **Predicted downstream:** cosmology, black holes, neutrinos, the cosmological constant —
  consequences of the spectral action once L19/L22 are secured, carried on the website's tree
  from the June 2026 cladogram and not graded by the capstone.

Every branch of contemporary physics has a place on the tree and a stated path to it; the path
is a theorem for the trunk and geometry, a partial theorem for most of the Standard Model and
quantum mechanics, and a named open problem for gravity and rigorous field theory. No branch
is asserted without a grade.

## Not on the tree (as of this date)

Topics with no node: the quantum measurement problem as such (the tree supplies the formalism,
not an interpretation); loop quantum gravity and string theory appear only as *sibling
programmes* compared against, not as branches. Renormalisation appears as the running of the
couplings (L17 → M_Z) but not as a graded link.

Companion pages: infinitography.com/tree-of-reality (interactive, every node linked to its Lean
file) · `docs/chain-theory/` (where Chain Theory lands on each of these).
