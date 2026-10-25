# Chain Theory in its own words

Everything below is taken from the Chain Theory documents of 23 October 2026 (compendium
release 0.1, the alpha Letter, the introductory slides, `ChainAlpha.lean`). Box and theorem
numbers refer to the compendium. Quotations are verbatim; paraphrase is marked.

## The axiom

> Nothing exists but finitely many maximally entangled pairs of qudits, some qudits shared,
> known only by distilling them.

"The only input. In the spirit of Wheeler's 'it from bit' (1989), with finite quantum systems in
place of bits." (slides)

## The six definitions (Definitions 1.1–1.6)

| | Term | Definition (compendium / slides) |
|---|---|---|
| 1.1 | **the axiom** | as above |
| 1.2 | **qudit** | a finite-dimensional quantum system, of dimension at least two ("a one-dimensional system ends no pair"; the one-dimensional end is excluded at the axiom, Theorem 2.9) |
| 1.3 | **shared** | a qudit that is an end of two or more pairs, carried as one copy per pair; the copies are one qudit |
| 1.4 | **distill** | project two qudits of dimensions d₁, d₂ onto P_m = \|ω_m⟩⟨ω_m\| on their common support, m = min(d₁, d₂) — "a generalized distillation, with one copy, one joint projection, and no failure branch" |
| 1.5 | **read** | an act at one end of a pair that distills the two ends in a basis of that end, one read for each of its d + 1 mutually unbiased bases; the basis reaches the far end whole, so a read is taken at the larger end |
| 1.6 | **known** | what its reads fix jointly, under every matching of its pairs and every exchange of its reads or pairs; two anticommuting reads also fix their product, whose sign flips with their order |

A **matching** — a change of basis by a unitary U of the support — acts on a pair as U ⊗ Ū and
leaves it unchanged. "To fix is to determine with certainty from a single copy, not to estimate
an expectation value over many."

## Three consequences for measurement (slides, "Three consequences settle the measurement theory")

- **The twirl.** The pair state is invariant under every matching, so every readout is invariant
  under their average, the isotropic twirl (envariance, Zurek 2003).
- **One copy.** The pairs are finitely many and distilling creates no qudit, so a read acts once on
  the one copy of its link.
- **A trace.** The operators invariant under every matching are spanned by 1 and P_m
  (Horodecki & Horodecki 1999), so a read delivers its pair projector and nothing finer.
  Readout: ⟨M⟩ = Tr_R M / dim R.

## The read cap

A read fixes two ends only when every positive map between their operator algebras is
decomposable. By Størmer (1963), Woronowicz (1976) and Choi (1975), that holds exactly when
d₁d₂ ≤ 6. So:

- **readable genres:** (2,2) and (3,2) — "of which (3,2) alone has unequal ends";
- **dark genres:** (3,3), (4,2), (4,3), (4,4) — a read passes only at second order.

"No state is bound entangled: what no distillation carries is a relation, not a state."
The same threshold d₁d₂ > 6 is where bound entanglement first appears (Horodecki³ 1998).

## The six genres and their conjectured sectors

The **genre** of a link is the pair of its end dimensions. That ends have dimension 2, 3 or 4 is
**Conjecture 0** (box 1.7), "graded a conditional theorem under its move table".

| Genre | Identification algebra | Dimension | First read | Conjectured sector | Standing of the identification (Part XVI matrix) |
|---|---|---|---|---|---|
| (2,2) | su(2)+su(2)+u(1) | 7 | order one | spacetime | **Conjecture 2** (open result 1.9) |
| (3,2) | su(2)+su(3)+u(1) | 12 | order one | electromagnetism: the photon | **Conjecture 1**, "named at a theorem" |
| (4,2) | su(2)+su(4)+u(1) | 19 | order two | the weak interaction | "by name" (38 supporting results, 14 parting) |
| (3,3) | su(3)+su(3)+u(1) | 17 | order two | the strong interaction | "by name" |
| (4,3) | su(3)+su(4)+u(1) | 24 | order two | the Yukawa sector | "by name" |
| (4,4) | su(4)+su(4)+u(1) | 31 | order two | the Higgs | "by name" |

The face groups, cell by cell (Part XVI): (2,2) Spin^c(4); (2,3) the Standard Model group
S(U(2)×U(3)) ≅ (SU(3)×SU(2)×U(1))/ℤ₆; (2,4) S(U(2)×U(4)) with SU(4) = Spin(6); (3,3) S(U(3)×U(3));
(3,4) S(U(3)×U(4)); (4,4) S(U(4)×U(4)).

## The central charge and the Standard Model group

The identification algebra of a link, su(d₁) ⊕ su(d₂) ⊕ u(1), has centre spanned by
Q = i·diag(d₂·1, −d₁·1), acting on the whole link as the scalar i(d₂ − d₁): zero at (2,2), i at
(3,2). "So exactly one readable genre carries an acting central charge" (Theorem 9.2, abelian
genre uniqueness). At (3,2): Q = 6iY with Y = diag(½, ½; −⅓, −⅓, −⅓) — the hypercharge
generator; the link carries (3,2) with Y = 1/6, "the quantum numbers of the left-handed quark
doublet". The gauge group as the face group of the qutrit–qubit tether: Theorem 64.2; as a
corollary of one construction: Theorem 65.1. Gauge invariance as the known clause: Theorem 64.1.

## The α count (the alpha Letter; Theorems 1 and 2)

**Theorem 1 (uniqueness).** Among configurations of readable links at a shared qudit, exactly one
is a two-point function, is read at the qutrit end, and carries an acting central charge on every
link: a shared qutrit with three links to qubits, two of them read.

**The count.** Each read places a letter (Gell-Mann at the qutrit, 8; Pauli at the qubit, 3) at
either end of its link; slots (8, 3, 8, 3). A record is two letters at two different slots:
64 + 9 + 4·24 = 169 products, plus 3 commutators at the qubits (anticommuting reads) = **172
records**. Two commuting exchanges — X (of reads, at the qutrit, carries 3) and Y (of links,
carries 2) — sort them: (+,+) 79 · weight 1; (+,−) 48 · √2; (−,+) 42 · √3; (−,−) 3 · √6.
Weight law k_r = ½(2 − X_r)(3 − Y_r), entering as √k_r. Readout dimension
N = 24 · 36 · 36 = 31104, where 24 = (3² − 1)(2² − 1) is the unread link's traceless part and
36 = (3·2)² the whole operator space at each read.

**Theorem 2 (value).** The dressed-over-bare two-point function of the object, per unit of its
conserved count, is

> (79 + 48√2 + 42√3 + 3√6) / 31104, inverse 137.035 999 189 566 155 029 183 744…

an element of ℚ(√2, √3) with rational coordinates (79/31104, 1/648, 7/5184, 1/10368).

**Conjecture 1 (the Photon Conjecture).** "The qutrit–qubit link of Theorem 1 is the elementary
link of the photon, and its dressed-over-bare readout is the electromagnetic coupling at zero
momentum transfer, α(0)." Distance from CODATA 2022 (137.035 999 177(21)): +0.6σ; from electron
g−2 (2023): +1.6σ; Rb recoil (2020): −1.5σ; Cs recoil (2018): +5.3σ. "The identification with
α(0) is a conjecture … It appears nowhere in the Lean file."

**What the Lean file checks** (Core Lean 4.35, no Mathlib): builds the 172 records from explicit
matrices, shows each is an eigenvector of the exchange of reads, applies the weight law,
evaluates the readout exactly: `readout objectWorld objectTwoPoint = ([(1,79),(2,48),(3,42),(6,3)], 31104)`.
Main theorem depends on `propext` alone. What it does not check: whether the definitions are the
right physics; the read cap (a named hypothesis citing Størmer, Woronowicz, Choi); the Photon
Conjecture.

**Alternative readings the Letter tabulates** (each excluded by a definition, without comparison
to α): ends swapped 135.89; both exchanges at the qubit end 146.52; both at the qutrit end 127.54;
exchange of reads where the letters sit 139.03; qubit–qubit records moved by Y 134.49;
commutators surviving X alone 138.35; weights k_r in place of √k_r 97.51; read ends in place of
units of charge 70.19; no weights 180.84.

## The grading system

> **Theorem** — derived from the axiom and its definitions, by the derivation given in its chapter.
> **Conditional theorem** — derived under conditions named in its box. A composed claim carries
> the lowest grade in its chain.
> **Open result** — stated, and carried to a named step that remains open: neither established
> nor excluded.

"A caution about the word theorem: many theorems are exhaustive checks over the webs the
compendium records … a census of a finite catalog, not a proof for every web."

Release 0.1 holds **100 theorems** (64 tied to named Lean declarations), **109 conditional
theorems**, **198 open results**, in sixteen Parts, appendices and 52 instrument chapters. Names
from the literature are "correspondences by name"; each box is a statement about the networks.

## Headline results by Part (from the slides' summary tables)

**Quantum mechanics (Parts I, III).** State space of a pair type as the span of act outputs
(35.1, conditional) — "the inner product of the span is the Born readout … Here the Born rule is
an output, conditional on its premises, not an input"; flat pair and unitary transport (40.1,
cond.); uncertainty from the Weyl relation (41.1, cond.); indistinguishability from the twirl
(43.1, cond.); energy as first-power operator and the step (44.1, cond.); Wigner function and
many-body sign (46.1, cond.); measurement as the wash at one act (28.1, theorem); classical limit
as the zero-density register (28.5, theorem).

**Spacetime and symmetry (Part IV).** Order coordinate as a count of one-steps (50.1, cond.);
rotation group as automorphisms of the derived directions (53.1, cond.); Lorentz group as
isometries of the Hermitian split (54.1, cond.) — "a form of signature one against three, is
six-dimensional and equals the Lorentz algebra at every structure constant. Nothing in the axiom
mentions space"; one against three at every step of the chain (55.1, theorem); spin-c group at
the qubit pair (58.1, theorem); parity as the improper element (59.1, cond.); three involutions
and the identity product (61.1, theorem). Time: "counted, not assumed" (Box 50.1, conditional).

**Gauge structure and the number three (Part V).** Gauge invariance as the known clause (64.1,
theorem); gauge group as face group (64.2, theorem); as corollary of one construction (65.1,
theorem); hub pair as one qudit of dimension four (65.2); conserved functionals of the full move
set (74.1, theorem); Ward identity (78.1, cond.); anomaly with every body at its own sink (79.1,
theorem); **three, a theorem of the valence (83.1)** — "the generation count is three at the
three core sites of the closed triangle". In Part X: generation as depth momentum (197.1),
**generation bound at the hub dimension (197.3)** — "a hub assembly admits at most the third
generation at the hub dimension four", generation basis as the attach-site basis (197.4), and
**three generations as attach sites (197.5, open result)** — "the first is why there are at most
three generations and the second is why the Part calls the third a reading rather than a theorem."

**Gravity (Part VI, the (2,2) cell).** Depth metric with the rung term (90.1, cond.); curvature as
the graph Laplacian washed over the ladder (90.2, cond.); horizon at every rung as a seeded
saturation (99.1, cond.); abundances and the rate at the horizon (104.1, theorem); cosmological
term at the depth exponent (115.1, cond.). "At this release the four results of the gravity
program beneath the conjecture stand as open results."

**Confinement (Part IX, the (3,3) cell).** Confinement as dark-genre readability (171.1, cond.);
strong coupling as the gluon closed read (172.1, cond.); nucleon structure as the star record
census (174.1, cond.); hadron spectrum as saturated joined webs (177.1, cond.); quark offices as
the star arm reads (181.5, theorem). "At all 494 qutrit–qutrit links of the roster, no read
survives at first order."

**Mass and Higgs (Parts X, XI).** Mass unit and first power (185.1, cond.); body-alone office rule
(195.1, theorem); unified mass readout (198.3, cond.); Higgs as the closed hub read (200.1,
cond.); Higgs quartic as the ratio of offices (202.1, theorem) — "an exact element of ℚ(√2, √3) at
every one of 10,123 Higgs-form sinks". Lepton ladder as hub assemblies (152.1, cond.); tau's third
hub (154.1, theorem); Koide relation at the dock unit (157.1, open). W and Z as one web, two
reads (159.1, 159.2, open); ratio of the two offices exactly ½ (164.5, cond.); W/Z mass ratio
(160.1, open).

**Beyond the Standard Model (Parts XIII–XV, all theorems).** Second law at the counting face
(217.1); phase transition as change of sink class (221.1); distillation theorem at forward
saturation (220.3); chain of copies and periodic readout (224.1); band at the periodic web
(225.1); Chern number as winding of the wash holonomy; closure of a web as a computation (230.1);
read as the maximal distillation (233.2); holonomy of basis transport (235.2).

**The particle webs.** 17 particles drawn on 16 webs; "1 rests on a theorem, 11 on conditional
theorems, 2 on open results and 3 on results not in this release." The electron's web: a core
triangle of three qutrits ((3,3)), an in-leg joining hub to core ((4,3)), legs of the hub assembly
((4,2)), the qubit pair of the hub assembly ((2,2)), docks at the other two corners ((3,2)). "The
muon carries two hub assemblies and the tau three."

## Related programmes, as Chain Theory names them

"Other programs derive parts of the Standard Model from a finite or algebraic input, braided
ribbons [17], one representation of an exceptional group [18], the division algebras [19] and
the spectral action on a finite noncommutative geometry [20]; here no unification group and no
division algebra is an input, the only algebraic objects being the Weyl operators of
finite-dimensional systems and the identification groups the definitions leave, and the
construction supplies a coupling constant." [20] = Chamseddine & Connes, *The spectral action
principle* (1997).
