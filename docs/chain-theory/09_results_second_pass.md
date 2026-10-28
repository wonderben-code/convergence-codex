# Results — second pass on Q4, R9′, Q6, Q1

**Date:** 28 October 2026. Computations in `scripts/chain_theory/`; the Q4 theorems in
`lean_verify/chain_theory/Q4HubBound.lean` (Lean 4.29.1 + Mathlib, built in the estate as the
`ChainTheory` library). As with the first pass, this is one side's reading, and corrections from
the Chain Theory side will be recorded in `07_reading_log.md`. The Chain Theory text used is the
compendium, release 0.1, and the alpha Letter, both of 23 October 2026.

## Q4 · Does the hub bound transfer to M₄? — yes, as a theorem about frames, not about tensor factors

**What 197.3 rests on.** "A hub assembly is a ququart carrying a qubit pair among its qubit legs;
the pair takes two of its four ends and every move applies at a site with spare alone, so a hub
assembly admits at most the third generation at the hub dimension four." The counting is the
**valence law**, "at most d pairs at a qudit of dimension d", and the compendium reads it off
Definition 1.5: a read gives the qudit its only basis, "one direction for each pair the qudit
meets". Monogamy is respected by the copy model: a shared qudit "holds instead one copy of itself
for each of its pairs … much as a four-dimensional system, which has room for two qubits, can be
maximally entangled with two separate qubits at once". So "four ends" can be read two ways, and
the test is which of them M₄ supports.

**File:** `lean_verify/chain_theory/Q4HubBound.lean`. Every theorem depends only on `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, no `native_decide` and no new axiom.

| Theorem | Statement | Reading |
|---|---|---|
| A `card_le_of_orthogonal_idempotents` | nonzero idempotents of Mₙ(K) with PᵢPⱼ = 0 (i ≠ j) number at most n | the valence law, additively: a site of dimension n has at most n ends |
| B `hub_saturated` | an in-leg and three legs at M₄ leave no nonzero idempotent orthogonal to all four | the full hub has no spare, so no move applies there |
| B′ `hub_legs_le_three` | beside an in-leg, at most three legs fit in M₄ | |
| C `core_spare_le_one` | at M₃ with two core ends, at most one further end | the closed triangle leaves room one at each core qutrit |
| C′ `core_attachments_le_three` | three such core qutrits admit at most three attachments in total | **the three** |
| `hub_hypotheses_satisfiable` | the four diagonal units of M₄ meet B's hypotheses | guard against a vacuous theorem |
| D `dvd_of_unital_algHom` | a unital algebra map M_m(K) → M_n(K), char 0, exists only if m ∣ n | the multiplicative reading |
| `no_qutrit_factor_in_ququart`, `no_three_qubit_factor_in_ququart` | no unital M₃(ℂ) → M₄(ℂ); no unital M₈(ℂ) → M₄(ℂ) | a ququart carries no qutrit and no three qubits as tensor factors |

**Verdict.** The bound transfers. The counting behind 197.3 is a theorem about **frames**
(orthogonal idempotents) of M₄ and M₃: the hub assembly saturates M₄ (1 + 3 = 4, no spare), the
closed triangle leaves one direction at each of three qutrits, so at most three attachments. Q4 as
first posed, with "legs" as **tensor factorisations** of M₄, does not go through, and Theorem D says
why: the qubit pair already exhausts M₄ = M₂ ⊗ M₂, and a qutrit fits inside a ququart only as a
corner, never as a tensor factor. That corner is the Tree's L13 split 4 = 3 ⊕ 1. So the definition
carrying the weight is 1.5 ("one direction for each pair"), read on the carrier ℂ⁴, which is
exactly how the compendium states it.

**What it shows for both.**
- **For Chain Theory:** 197.3's arithmetic has a second proof in a different formalism, as a
  theorem of linear algebra on M₄ and M₃, given the network's shape (the closed core triangle,
  the hub assembly's ends). The census and the network still supply that shape.
- **For the Tree:** L14 gains a theorem-grade counting route to "at most three", under Chain
  Theory's identification of a generation with an attachment at a core site with room. That
  identification is still a postulate on both sides; Chain Theory's own 197.5 records the ladder
  as unmet at the sinks. **L14 stays POSTULATE.**
- **Two threes, kept apart.** Chain Theory's three is 3 sites × (3 − 2) room; the Tree's L14 three
  is the dimension of the pure quaternions, 2² − 1. Whether they are one three is Q5, not
  settled here.

## R9′ · The improper element at M₁₆ — the two binaries are different operations

**Script:** `scripts/chain_theory/r9prime_parity_at_M16.py`. The Tree's L12 lives at
M₁₆ = End(M₄) ≅ M₄ ⊗ M₄^op: the left factor 𝓛 acts covariantly (ξ ↦ aξ) and the right factor 𝓡
contravariantly (ξ ↦ ξb). With the Tree's γ₁…γ₄ (squares +1, +1, −1, −1), γ₅ = γ₁γ₂γ₃γ₄ and
P = γ₁, every canonical lift was realised as a 16 × 16 matrix on vec(ξ). Each was then tested on
the two factors and on the carrier's 8 + 8 split into even and odd Clifford elements (the
eigenspaces of the grading Ad γ₅, the only 8 + 8 split the carrier offers):

| Lift | the two factors 𝓛, 𝓡 | the 8 + 8 halves |
|---|---|---|
| L(P): ξ ↦ Pξ (Pin acting on a left module) | preserved; acts on 𝓛 alone | **exchanged** |
| R(P): ξ ↦ ξP | preserved; acts on 𝓡 alone | **exchanged** |
| Ad P: ξ ↦ PξP⁻¹ (the automorphism) | preserved; acts on both | preserved |
| twisted Ad P (the reflection) | preserved; acts on both | preserved |
| grade involution α = Ad γ₅ | preserved; acts on both | preserved |
| reversion (anti-automorphism) | **exchanged** | preserved |
| Clifford conjugation (anti-automorphism) | **exchanged** | preserved |
| transpose (anti-automorphism) | **exchanged** | preserved |
| J: ξ ↦ ξ† (antilinear, the real structure of a spectral triple) | **exchanged** | preserved |

Also: L(P) anticommutes with L(γ₅), while Ad P commutes with Ad γ₅. The automorphism lift loses
the sign that makes P a parity.

**Verdict.** R9's shape (ii), "singles one out", is realised by the improper element's spinor
action. Which factor it singles out is the side the spinor module is taken on, a convention, as at
M₄. The kill-condition (no action) is not met. The new fact is that the two binary choices are
carried by **disjoint classes of operations**:
- exchanging the **factors**, i.e. the Tree's L12 as worded ("which factor is left"), is done by
  anti-automorphisms: transpose, reversion, and J, which in the spectral-triple tradition is charge
  conjugation;
- exchanging the **chiral halves** is done by the improper element's spinor action.

No canonical lift does both.

**What it shows.** L12 as worded in the capstone names a C-type choice: the covariant 4 against
the contravariant 4̄ of (4,2,1) ⊕ (4̄,1,2). The parity choice, which half SU(2)_L acts on, is a
second and separate binary, exchanged by P. **Proposed for the Tree:** re-pose L12 as these two
binaries, with the grade unchanged (POSTULATE). For Chain Theory's handedness reading
("handedness is the orientation at the twirl"), the comparison object is the second binary, not
the first.

## Q6 · Does the read cap give L23 a mechanism? — it gives a location, not a mechanism

**Script:** `scripts/chain_theory/q6_read_cap_on_colour_block.py`.

**Part A, the dark object on the Tree's carrier.** M₁₆ = End(M₄) acts on M₄ = ℂ⁴ ⊗ ℂ⁴*, and L13
splits ℂ⁴ = ℂ³ ⊕ ℂ¹, so the carrier has a **gluon corner** ℂ³ ⊗ ℂ³* (3 ⊗ 3̄ = 8 + 1). Horodecki's
3 × 3 state (a = 0.3) was placed on that corner and checked to be positive with trace 1, to have a
positive partial transpose across the left|right cut (the cut of R9′), and to be entangled
(realignment norm 1.003 > 1). That makes it bound entangled. The read cap's undistillable object
exists on the Tree's own carrier, at the colour block.

**Part B, the partition.** Against d₁d₂ ≤ 6: the isospin pair (2,2) = 4, the quark doublet
(3,2) = 6 (exactly at the cap) and colour–lepton (3,1) = 3 are readable. The gluon corner
(3,3) = 9 and the whole cut (4,4) = 16 are dark. **The cap falls between the quark doublet and
the gluon corner**, and L23 (Yang–Mills, the mass gap) is about the gluon corner.

**Part C, the drafted spectral statement.** "No conditional expectation onto a MUB subalgebra of
the colour factor commutes with D on that block." This was tested on D = 1₃ ⊗ Y, the shape of every
finite Standard-Model Dirac operator, where the Yukawa couplings do not see colour. **It is false.**
Such a D commutes with the whole colour factor, so every conditional expectation onto a colour
subalgebra commutes with it, in the computational and the Fourier basis alike. The finite triple
sees colour only through its unbroken symmetry.

**Verdict.** This is the second of Q6's two stated outcomes, in part. The algebraic picture *does*
see where the read cap bites: exactly at the colour block, where L23 sits. It does not see a
mechanism, since no finite statement about (A, H, D) yields a gap. **L23 stays ◇ OPEN.** Turning
the location into a mechanism needs a continuum statement linking bound entanglement of
gauge-invariant states to clustering or a gap. We know of no such theorem, and it is posed here as
the next question.

## Q1 · The Higgs quartic and the window — computed from the compendium's own numbers

**Script:** `scripts/chain_theory/q1_quartic_vs_window.py`. Exact fractions for Chain Theory's
values. Standard-Model running uses one loop in full, plus the two-loop gauge terms and the dominant
two-loop top/QCD/Higgs terms; boundary values come from Buttazzo et al. (2013). **Validation:**
the script gives λ(M_Pl) = −0.0141 against the published −0.0143, and λ turns negative at
10^9.7 GeV against the published ~10¹⁰.

**Chain Theory's number** (eq. 124, Theorem 202.1): λ = (46656001681/182250000)/V², with V at the
six readings 6561, 81, 65536, 256, 16, 256. At the first reading:
**λ = 46656001681/7845264902250000 ≈ 5.947 × 10⁻⁶.** The convention, m_H² = 2λv², matches the
Tree's (λ = 4λ̃). Chain Theory states no scale ("needs no observed value and no unit"), so three
readings were tested.

| Test | Result |
|---|---|
| **T1** at the Tree's cutoff, window g²/24 ≤ λ ≤ 4g² with g = g₃(Λ), Λ = 10¹³ … M_Pl | first reading: **below** the window at every cutoff (by a factor of about 1,700–2,400). V = 81 (λ ≈ 0.039): **inside** at every cutoff. V = 16 (λ ≈ 1.0000): inside up to 10¹⁷ GeV, above at M_Pl. V = 256 and 65536: below. |
| **T2** as the Standard Model's running coupling | first reading: λ_SM(μ) equals it at μ ≈ 10^10.6 GeV, just below the scale where the measured λ crosses zero. V = 81 at 10^5.7 GeV, V = 256 at 10^9.7 GeV, V = 16 never. This is a weak test, since every value in the Standard Model's range is met at some scale. |
| **T3** the Tree's window as a boundary condition at Λ = 10¹⁶ … M_Pl, Standard-Model running | the lower edge needs λ(m_t) ≈ 0.139, so **m_H ≈ 131–132 GeV**; the upper edge needs m_H ≈ 168–176 GeV. The measured 125.20 GeV (λ(m_t) = 0.126) lies **below** the window. |
| **Robustness** | the window's lower edge is strictly positive for every N (λ̃ = g²b/a² > 0), so no choice of N helps. λ(Λ) > 0 with m_H = 125.20 needs **m_t < 171.0 GeV** (published NNLO: about 171.5), against the measured 172.57 ± 0.29. |

**What it shows.**
- **For the pair of numbers:** read at the cutoff, the first reading and the window do not
  overlap; the reading at V = 81 does. Since Chain Theory fixes no scale and the Tree's window is
  a boundary condition at Λ, this comparison is conditional on reading Chain Theory's number at Λ.
  Chain Theory's choice of reading, and of scale, would settle it.
- **For the Tree, a correction found by our own test.** With Standard-Model field content, the
  L15 window read as a physical boundary condition at a high cutoff **excludes the measured Higgs
  mass**, by about 6 GeV in m_H, or about 1.5 GeV in m_t. This is the known tension of the
  spectral Standard Model: the 2007 version gave about 170 GeV. The literature's resolution adds a
  scalar singlet σ (Chamseddine–Connes 2012). The L15 grade does not move, because the window is a
  theorem about a defined quantity and the capstone makes no 125 GeV claim. But the estate's
  HiggsBridge docstring line, "the RG running from Λ to the electroweak scale producing ≈125 GeV
  (… cited)", is not supported with Standard-Model content and is proposed for correction.

## What changed as a result

- **06 / Q4:** answered, yes in the additive reading. The question as posed (tensor factors)
  closes negatively, with Theorem D.
- **06 / Q6:** answered in part, with location but no mechanism. The next question is posed
  (bound entanglement → clustering).
- **06 / Q1:** run from the compendium's own numbers. The comparison is conditional on scale and
  reading.
- **R9′:** answered. L12 is re-posed as two binaries.
- **Proposed corrections to the Tree:** the L12 wording (two binaries), and the L15 / HiggsBridge
  125 GeV line (tension with data under Standard-Model running, recorded as such).

Nothing in the Tree's scoreboard changes. 6 · 13 · 3 · 2.
