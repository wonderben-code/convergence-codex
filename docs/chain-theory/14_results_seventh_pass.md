# Results — seventh pass: the five solve paths

**Date:** 29 October 2026. The sixth pass left five gaps with a clear path to closing them. Each
path was attempted here.
- Lean: `lean_verify/chain_theory/L7L21InvariantPairing.lean` (the `ChainTheory` library; every
  theorem depends only on `propext`, `Classical.choice` and `Quot.sound`).
- Scripts in `scripts/chain_theory/`: `l18b_dirac_operator.py`, `r13d_higgs_hardened.py`,
  `r6b_third_copy_and_exchanges.py`.

## 1 · L7, the three lineages: the pairing is forced and unique (Lean)

**`invariant_bilinear_classification`.** For every n ≥ 2, in characteristic zero, a bilinear form on
Mₙ(K) that is invariant under every matching, in the form B([A,X],Y) + B(X,[A,Y]) = 0, is

> **α·tr(XY) + β·tr(X)·tr(Y).**

The proof works on matrix units:
1. invariance gives one linear relation among the values b(i,j,k,l) = B(Eᵢⱼ, Eₖₗ);
2. diagonal matchings kill every b outside the patterns (i = j, k = l) and (i = l, j = k);
3. off-diagonal matchings force the survivors to two constants.

With the sixth pass's order-one theorem (the only invariant functional is the trace), what every
matching fixes at orders one and two is now machine-checked: the trace, and the two pairings built
from it. So the third lineage ⟨·,·⟩ is derived from the first two (End, Aut) under the knowledge
clause, and is unique up to these two terms. Orders three and higher (the First Fundamental Theorem
for matrices) remain cited; they were checked exactly for n, k ≤ 3 in the sixth pass.

**Status of L7.** The case for POSTULATE → PARTIAL is now firmer. The residue is narrowed to two
items: the knowledge clause as a premise, and the higher orders cited. The move awaits the founder's
ruling.

## 2 · L21, the Born rule: the commutant of the matchings (Lean)

**`equivariant_classification`.** For every n ≥ 2, a linear map φ on Mₙ(K) that commutes with every
matching, φ(AX − XA) = A·φ(X) − φ(X)·A, is

> **α·X + β·tr(X)·1.**

On the GNS space L²(Mₙ) of the trace state, the map X ↦ tr(X)·1/n is the projection onto the GNS
vector Ω = 1/√n, which is the maximally entangled pair. So **the commutant of the matchings is
span{1, |Ω⟩⟨Ω|}, for every n.** The proof routes through the classification above, via
B(X, Y) = tr(φ(X)·Y) and the nondegeneracy of the trace pairing.

The twirl, the projection onto that commutant, therefore leaves weight |⟨Ω, x⟩|² on Ω. That is the
Born square, now resting on a machine-checked commutant at every n (the final step is elementary and
was checked numerically in `r5_born_circle.py`).

**Status of L21.** The Born row moves from "cited (Gleason)" to "derived up to one interpretive step,
reading the weight as a probability". Narrowing assumptions-ledger entry 59 to that step awaits the
founder's ruling. L21 stays PARTIAL.

## 3 · L18, the missing item: the Dirac operator, constructed and checked exactly

`l18b_dirac_operator.py` constructs D on H = M₄ ⊕ M₄ (the cascade's carrier doubled, at Chamseddine–Connes
k = 4), in the particle basis ψ_{sc} (s ∈ 2_R ⊕ 2_L, c ∈ 3 ⊕ 1). It has general complex Yukawas
y_u, y_d, y_ν, y_e and a Majorana mass k_R.

| Check (one generation, exact symbolic arithmetic) | Result |
|---|---|
| D self-adjoint | holds |
| J D = D J, J² = 1, J γ = −γ J (KO-dimension 6) | holds |
| D γ = −γ D | holds |
| order zero, Pati–Salam algebra, all generator pairs | holds |
| first order, Standard-Model algebra ℂ ⊕ ℍ ⊕ M₃, all generator pairs | **holds** |
| first order, Pati–Salam algebra ℍ_R ⊕ ℍ_L ⊕ M₄ | **fails**, through exactly three quantities: y_ν − y_u, y_e − y_d, k_R |

The same holds for three generations (checked numerically, with general complex 3 × 3 Yukawa matrices
and a symmetric Majorana matrix).

**What it shows.**
- **The Dirac operator exists** on the cascade's carrier and satisfies every axiom. L18's fourth item
  is supplied; the values of its Yukawa entries remain inputs.
- **The Pati–Salam first-order condition is a mass relation.** It holds on the Yukawa block exactly
  when lepton Yukawas equal quark Yukawas (y_ν = y_u, y_e = y_d), which is the classic Pati–Salam
  relation. At that relation, the only violation left is the Majorana entry, and that entry is the
  one that generates σ (fifth pass). Two physical facts meet in one computation: quark–lepton
  unification relates the masses, and the neutrino's Majorana mass is what breaks the first-order
  condition and produces σ.

**Status of L18.** Of its four items, one is already ruled (J), one is forced (the grading), and one
is now constructed (D). The quaternionic real form remains a choice, and the Yukawa values remain
inputs. L18 stays PARTIAL with that residue named.

## 4 · L15, the Higgs: three generations, an error budget, and the top-mass test

`r13d_higgs_hardened.py` builds on the third pass's σ running. It uses Chamseddine–Connes 2012's
boundary conditions with σ, decouples σ at its mass, and runs the Standard Model below.

**(a) Three generations.** Chamseddine–Connes's boundary condition uses traces over all Yukawa
matrices (λ_h = 4g²·b/a²).
- The lighter quark and charged-lepton generations shift b/a² by **0.04%**: invisible.
- The one place three generations matter is the **flavour structure of the neutrino Yukawas**, which
  is unmeasured. Spreading the same total across three generations would shift b/a² by **−32%**.
  This is now the main unknown in the boundary condition.

**(b) The error budget** (Λ = 10¹⁶ GeV), for n\*, the value that gives m_H = 125.20 GeV:

| Variation | n\* |
|---|---|
| central | 1.659 |
| matching at m_σ/2, or at 2m_σ | 1.649, 1.670 |
| dominant two-loop Standard-Model terms added above σ | 1.665 |
| m_t ± 0.29 GeV | 1.672, 1.645 |
| α_s ± 0.0009 | 1.642, 1.675 |
| g = g₂ instead of g₃ at Λ | 1.661 |

**n\* = 1.66 ± 0.02 across every variation.** The seesaw-consistent σ scale is 2.46 × 10¹⁴ GeV
(2.47 × 10¹⁴ with the two-loop terms). The third-pass result is robust to every effect tested, apart
from the unmeasured neutrino flavour structure in (a).

**(c) The top-mass test: a negative result.** Chamseddine–Connes's spectral action also fixes the top
Yukawa at Λ, y_t = √(4/(n+3))·g (their eq. 22). With n fixed by the Higgs mass, that predicts the top
mass with no free parameter:

| Λ | g | y_t(Λ) imposed | y_t(Λ) from measurement | predicted m_t |
|---|---|---|---|---|
| 10¹⁶ | g₃ | 0.490 | 0.422 | 184.8 GeV |
| 10¹⁶ | g₂ | 0.486 | 0.422 | 184.2 GeV |
| 10¹⁷ | g₃ | 0.477 | 0.409 | 184.7 GeV |
| 10¹⁷ | g₂ | 0.481 | 0.409 | 185.3 GeV |

The measured value is 172.57 ± 0.29 GeV, so **the relation predicts a top about 7% too heavy.** The
conversion from y_t to m_t extrapolates a linear matching formula over about 12 GeV, so these numbers
carry roughly ±1 GeV; the conclusion does not depend on that. (Chamseddine–Connes 2012 report a top
"a few percent lower" than measured, in a treatment that runs every coupling down to M_Z without
decoupling σ. The two treatments disagree on the sign, and neither gives 172.57.)

**What it means for the Tree.** The Tree's L15 adopts the boundary conditions for the scalar sector
only. It does not adopt the top-Yukawa relation, and this test shows it should not, as things stand.
With σ, the window reproduces m_H = 125.20 GeV robustly, but the full spectral-action package (the
Higgs and the top together) does not reproduce both masses. That is recorded as a **staked test for
the future**: a version of the Tree's spectral action that fixes the top Yukawa must predict 172.6 GeV,
and today's relation predicts about 185.

## 5 · R6, the open half: settled

**(a) The third copy.** The commutant of the two standard-form copies of M₃ on L²(M₃) is the scalars
(dimension 1). No third copy commuting with both fits in the standard form. The held link's copy needs
a new tensor factor, a new qutrit identified with the first only by a matching, which is Chain
Theory's copy model and not a consequence of the inner product.

**(b) The exchanges.** Every automorphism of the operators on a finite space is a conjugation, linear
or antilinear. So the α Letter's exchanges X and Y are operations on the space if and only if some Ψ
satisfies Ψ·r = X(r)·Ψ on every record r. That is a linear system, solved exactly on the 36-dimensional
space L²(M₃) ⊗ ℂ² ⊗ ℂ².

| Exchange | linear solutions | antilinear solutions |
|---|---|---|
| X (of reads) | 0 | 0 |
| Y (of links) | 0 | 0 |
| control 1: the identity on records | 1 | — |
| control 2: the exchange J ⊗ SWAP actually induces | — | 1 (it differs from X on 165 of 169 records) |

The controls show the method finds an implementer whenever one exists.

**Verdict: R6 is settled.** The inner-product lineage supplies exactly the two read copies (sixth
pass: 169 independent products). The third copy and the exchanges X and Y are rules on Chain Theory's
record labels, not operations on the Hilbert space the Tree's lineages build. That part of the α
count belongs to Chain Theory's own structure (Definitions 1.3 and 1.6), as Q3 first indicated.

## Next solve paths (identified 29 October 2026, not yet attempted)

Ranked by how strongly each could move the Tree:

| | Path | What it could do |
|---|---|---|
| A | **L9 signature by KO-dimension.** Build the real structure for each indefinite signature on Cl₄, read off its KO-dimension, and add the Tree's ruled finite KO-dimension 6. Barrett (J. Math. Phys. 48, 012303 (2007)): a total of 0 mod 8 permits the Majorana–Weyl condition that removes fermion doubling. Sign conventions must be checked carefully before any claim. | Close L9's residue: Lorentzian forced, split (2,2) excluded, given the KO-6 ruling and the fermion-doubling condition. |
| B | **A joint (m_H, m_t) fit with three-generation neutrino Yukawas.** One generation cannot fit both masses (n ≈ 1.66 for m_H, n ≈ 3.3 for m_t). Three generations bring two independent traces (tr Y_ν†Y_ν and tr (Y_ν†Y_ν)²) and the Yukawa–Majorana alignment. Add the seesaw with measured mass splittings and mixing (Casas–Ibarra). | Turn the top-mass failure into a fit, and predict the lightest neutrino mass, Σm_ν or the ordering, which JUNO, KATRIN and DESI/Euclid will test. The outcome is unknown; the fit may be under-determined. |
| C | **Busch's theorem in Lean.** Any additive probability assignment on effects is tr(ρE), with a short proof. | Replace "Gleason, cited" in L21 with a proved theorem under one operational premise. |
| D | **Degree-3 invariants in Lean**, then scope a general Schur–Weyl / First Fundamental Theorem formalisation. | Move L7 toward GENUINE. |
| E | **The gauge group of each real form** of M₄ ⊕ M₄. | Show that observation (weak isospin is SU(2)) selects the quaternionic form, which files L18's real form as a fork fixed by observation. |
| F | **The read cap through the vacuum** of a small lattice gauge model, by exact diagonalisation. | Test whether bound entanglement tracks confinement (speculative). |

Out of reach for now: L22 (gravity, gated on the unbounded-operator library, G2) and L23 (the mass gap, G1/G3/G4).
