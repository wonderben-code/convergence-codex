# The Tree of Reality: The Complete Tree to Date

### The machine-verified state of the Generator programme — the proven trunk, the stated assumptions, and the predicted gaps

**Author:** Mark E. Mala (pen name of Ekram Alam)
**Date:** September 2026
**Series:** the capstone of the Infinitography / Convergence Codex programme. This paper
supersedes the running claim-registers of the programme's earlier documents (in particular the
May 2026 register of *Paper F v5.1*) wherever they disagree; §7 lists every superseded claim
explicitly. The underlying papers keep their DOIs and their history.
**Verification:** every mathematical claim in this paper is backed by a machine-checked Lean 4
proof in the public repository `wonderben-code/convergence-codex`, and §9 gives the exact
branch, commit discipline, and the two commands that let a reader check any of it without
trusting the author.

---

## Abstract

In 1869 Mendeleev published a table with holes in it. He did not apologise for the holes: he
predicted that elements would be found to fill them, and described what those elements would
look like. The gaps were not the table's weakness. They were its testable content.

This paper does the same for a theory of physics. We lay out the **Tree of Reality** — a single
generative structure that begins with nothing but the impossibility of a certain map, forces a
first algebra, and grows by one repeated operation into spacetime, gauge structure, colour,
chirality, generations, and the machinery of quantum mechanics — in **its most complete form to
date**: twenty-four links from nothing to everything, each labelled with exactly what a proof
assistant has verified about it.

The label vocabulary is unforgiving. Of the twenty-four links, **six are GENUINE** — their
headlines are machine-checked theorems, resting on nothing but the three standard axioms of
Lean's mathematics library. **Thirteen are PARTIAL** — real theorems cover part of the
headline, and the unproven residue is named precisely, in every row. **Three are POSTULATES** —
modelling choices we state rather than hide. **Two are OPEN** — and those two are the theory's
gallium and germanium.

The paper's final section states the programme's prediction in Mendeleev's register: the open
gaps are exactly located, their missing mathematics is exactly shaped — down to the failing
step of each staircase — and we predict that as machine reasoning in mathematics improves,
these gaps will be filled and the tree shown whole. The prediction is dated, published,
machine-checked and Bitcoin-anchored. Whoever fills a gap completes this programme.

The evidence discipline behind those labels is itself a result. Over a 45-working-day
verification campaign (28 July – 26 September 2026, 243 numbered units), the estate grew to
**1,230 graded Lean files (312,334 lines), building green in 5,091 jobs, with exactly one
`sorry` and one `axiom` in the entire build** — both predating the campaign, both documented,
neither load-bearing for any claim below. In 169 consecutive units of hardening, **no spine
rating moved**: the work sharpened residues and closed named sub-gaps without inflating a
single headline. Three of the programme's own July headlines were *machine-refuted* by the
campaign and are tagged down in this paper by the same hands that proved everything else. A
theory that keeps its own score this way earns the right to point at its gaps and call them
predictions.

---

## 1. The reader's contract

This section fixes what every label in this paper means, so that no sentence below can say
more than the mathematics does.

**GENUINE.** The link's headline is a machine-checked theorem: no `sorry`, standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`), and the formal statement says what the headline
says. Per-file axiom audits (`#print axioms`) back each one.

**PARTIAL.** Real theorems cover part of the headline; the rest is stated as missing, in the
link's own row. The residue is always one of two kinds — open mathematics, or a postulate —
and the row says which.

**POSTULATE.** The headline is a modelling choice. It is recorded in the assumptions ledger
(§6), with what it bites and which way it cuts. A postulate is not a defect; an *unstated*
postulate is.

**OPEN.** A precisely stated wall (§5) with no covering theorem: the staircase of steps toward
it is climbed as far as it goes, and the exact failing step is named.

Two boundaries matter as much as the labels. **First**, a GENUINE link is a theorem about the
estate's mathematical objects; whether those objects are the physical ones is, link by link,
a modelling question that the assumptions ledger answers separately. Machine verification
removes doubt about the mathematics, not about the physics identification. **Second**, a
wall's failing step marks where the *known* routes stop — it is not a proof that no route
exists. One of the campaign's own walls fell by a route no document had listed.

Everything else in this paper is organised to be checked: §9 gives the repository, the branch,
the stop-point commit, and the verification commands. The reader is never asked to trust; only
to run.

## 2. The method, and why the labels can be believed

The tree was not labelled by opinion. It was labelled by a campaign with the following
discipline, run from 28 July to 26 September 2026 in 243 numbered units.

**Grading.** Every Lean file in the estate carries a grade in a ledger (`TRUE_LEDGER`): GENUINE
(1,142 files at the stop), HOLLOW (59 — files whose theorems compile but do not say what their
prose claims; kept, labelled, and never cited as evidence), MIXED (15), PARTIAL (12), NOT_BUILT
(2). The grade of a file is decided adversarially — by asking what its statements *fail* to
say — and re-audited when touched.

**Gates.** Each unit passed a defect gate (44 modes, 25 scanners at the stop) before it could
land. The gate's own vacuity census asks, of each law, whether it could pass while checking
nothing.

**Errata.** The campaign filed **699 numbered errata** against itself and the estate — each one
a sentence somebody wrote that the mathematics later contradicted, with the correction quoted
beside it. The last erratum was filed forty minutes before stand-down, against the campaign's
own draft ledgers. The errata are part of the published record.

**The stability result.** Across units 75–243 — 169 units of continuous sharpening — **no spine
rating moved**. Five separate recomputations re-read the whole table against the work and each
found no rating change. The natural drift of a long project is upward relabelling; this
campaign's drift was zero. That fact, more than any single theorem, is why the six GENUINE
tags below can be taken at face value.

**The refutations.** The campaign proved theorems *against* three of the programme's own
published July sentences (§7): the reflexive-domain headline over sets, the structural
exclusion of Riemannian signatures, and the Standard-Model-in-su(4) assembly. Each refutation
is itself machine-checked, and each is worth as much as a proof — a labelling system that can
only move in the author's favour measures nothing.

---

## 3. The Tree, whole — the most complete form to date

This section is the paper. Everything before it is calibration; everything after it is
support. The figure below renders the Tree of Reality as of unit 243 — every link of the
nothing→everything chain carrying its audited tag, with the two open gaps drawn **in place**,
marked ◇, the way Mendeleev left conspicuous boxes empty.

**The scoreboard: of 24 links — 6 GENUINE · 13 PARTIAL · 3 POSTULATE · 2 OPEN.**
(Read strictly three ways, the count is 6 GENUINE and 18 not; every PARTIAL row below names
its residue, and the residue is always either open mathematics or a stated postulate.)

```
∅  nothing
└─ L1   GENUINE    existence from self-reference (Lawvere's fixed point)
   └─ L2   PARTIAL    the reflexive domain  D ≃ (D → D)
      └─ L3   GENUINE    the seed: M₂(ℂ), the unique minimal non-commutative algebra
         └─ L4   GENUINE    the cascade: M₂ → M₄ → M₁₆ → M₂₅₆ → …   (End-iteration)
            ├─ L5   GENUINE    irreversibility — the cascade cannot run backwards
            ├─ L6   PARTIAL    why the fourth level — the CCM classification   [gap W9 behind it]
            └─ L7   POSTULATE  three lineages branch: End · Aut · ⟨·,·⟩
               │
               ├─ THE END LINEAGE — matter, spacetime, gauge
               │  ├─ L8   GENUINE    spacetime dimension 4:  Cl₄(ℂ) ≅ M₄(ℂ), and only in dim 4
               │  ├─ L9   PARTIAL    Lorentzian signature (1,3)
               │  ├─ L10  PARTIAL    the gauge algebra, embedded
               │  ├─ L11  PARTIAL    Pati–Salam structure at M₁₆
               │  ├─ L12  POSTULATE  chirality — which factor is "left"
               │  ├─ L13  GENUINE    colour: the 4 splits as 3 ⊕ 1
               │  ├─ L14  POSTULATE  three generations — the imaginary quaternions
               │  ├─ L15  PARTIAL    the Higgs sector and its coupling window
               │  ├─ L16  PARTIAL    anomaly cancellation on the chiral 16
               │  └─ L17  PARTIAL    the Weinberg angle: 3/8 as a trace ratio
               │
               ├─ THE AUT LINEAGE — symmetry and gravity
               │  └─ L22  ◇ OPEN     the Einstein equations from the spectral action   [gap W5]
               │
               └─ THE ⟨·,·⟩ LINEAGE — quantum mechanics
                  └─ L21  PARTIAL    Hilbert space, GNS, Stone, Schrödinger
                     (the Born rule is a cited input, not a theorem — assumption 59)

               THE CO-EVOLVED CROWN — where the three lineages meet
               ├─ L18  PARTIAL    the spectral triple (algebra, space, Dirac operator)
               ├─ L19  PARTIAL    the spectral action — the exponential cutoff forced
               ├─ L20  PARTIAL    the Boltzmann measure of the action
               ├─ L23  ◇ OPEN     Yang–Mills and the mass gap                     [gaps W1–W4]
               └─ L24  PARTIAL    the numbers: what has actually been computed
```

The two ◇ boxes are the subject of §8. They are not embarrassments at the edge of the tree;
they are its most precisely surveyed territory — each carries a climbed staircase and a named
failing step, which is to say: a description of the missing element.

### The 24 links, each in one honest breath

What follows compresses the audited link table. For every link: what the headline says, what
is machine-proved (with the proving files), and what is not — with the residue's kind. The
full statement-level table, with every dated amendment, is in the published ledgers (§9).

**L1 · Existence from self-reference — GENUINE.** The root. Lawvere's fixed-point theorem at
the programme's own domain (proved with *no* axioms at all — the file's axiom print is empty),
with Cantor's theorem as its corollary, and the theorem re-proved in the cartesian closed
category of ω-CPOs where the non-degenerate story lives. *Not proved:* the interpretive gloss
(Gödel and Turing as consequences) — prose, and now labelled as prose.
*(LawvereFixedPoint.lean · paper_f/DInfForces.lean)*

**L2 · The reflexive domain D ≃ (D → D) — PARTIAL.** A non-trivial ordered structure
satisfying D ≃ (D →continuous D) exists — constructed, machine-checked. *Not proved:* the
July headline read D ≃ (D → D) with the **full** function space, and that statement is
machine-refuted over sets: only one-point solutions exist. The continuous reading is the
correct one, and adopting it as the published statement is an author's restatement, recorded
as such. *(CanonicalTower.lean · ReflexiveDomainObstruction.lean)*

**L3 · The seed M₂(ℂ) — GENUINE.** Over ℂ, among finite-dimensional non-commutative algebras
of the relevant class, dimension ≥ 4 is forced, dimension 4 is attained, and dimension 4
implies isomorphism with M₂(ℂ); the ⋆-structure is carried along the isomorphism. *Scope
stated:* over ℝ the uniqueness is false (the quaternions also qualify) — the base field is a
recorded modelling choice, and the Lean discloses it. *(SeedUniqueness.lean ·
paper_f/SeedStarStructure.lean)*

**L4 · The cascade — GENUINE.** The engine of the whole tree: End(M_b) ≅ M_{b·b} at every
size, the tensor isomorphism M_n ⊗ M_m ≅ M_{n·m}, and the tower End(D_k) ≅ D_{k+1} proved at
sizes 2 → 4 → 16 → 256, with a genuinely recursive construction equal to it level by level.
*Not proved:* how deep the cascade runs, and which tensor factor decomposes — postulates,
recorded. *(paper_f/F4_1a · CascadeEnd · SpineSharpenings · CascadeTowerRecursive)*

**L5 · Irreversibility — GENUINE.** Dimension strictly increases up the tower, and the level
below is recoverable from End of it — the cascade is a one-way construction. *Labelled
honestly:* "the arrow of time" is an interpretation; no theorem mentions entropy or time, and
the files say so. *(paper_f/F4_1b · EmergenceLineage · SpineSharpenings)*

**L6 · Why the fourth level — PARTIAL.** Minimality of 4 under the stated criterion is proved
with no upper bound assumed, and the first rung of the Chamseddine–Connes–Marcolli
classification is climbed: a finite-dimensional ⋆-algebra with a faithful ⋆-representation is
a product of matrix algebras. On rung 2, the ⋆-structures are classified and the order-one
condition is solved on every model bimodule the estate has. *Not proved:* the classification's
second half on CCM's actual bimodule — the named failing step of gap **W9** — and the Standard
Model algebra ℂ ⊕ ℍ ⊕ M₃(ℂ) has no Lean declaration anywhere. *(CascadeMinimality ·
StarRepSemisimple · units 168–243)*

**L7 · Three lineages — POSTULATE.** That End, Aut and the inner product are *the only*
canonical operations — the claim that makes the three branches exhaustive — has no formal
statement; a fourth natural construction is already in use elsewhere in mathematics. Stated
as the modelling choice it is. The lineages' individual contents are credited to their own
links.

**L8 · Spacetime dimension 4 — GENUINE.** The complex Clifford algebra in four dimensions is
M₄(ℂ), for every nondegenerate form — and the converse: a complex Clifford algebra is M₄(ℂ)
*only* in dimension four. The cascade's fourth level and the algebra of spacetime are the same
object, and dimension four is the only dimension at which that coincidence can occur.
*Stated:* reading spacetime at cascade level D₂ is a recorded modelling choice.
*(paper_f/CliffordIso · CliffordEvenLadder · SpineSharpenings)*

**L9 · Lorentzian signature — PARTIAL.** The real Clifford algebra of signature (1,3) is
M₂(ℍ) on a form of proven signature; (2,2) is excluded structurally; the restricted Lorentz
group and its double cover by SL₂(ℂ) are proved. *Machine-refuted:* the July claim that the
Riemannian signatures (4,0) and (0,4) are excluded *structurally* — three signatures share one
algebra, so Lorentzian-over-Riemannian is a postulate, now recorded as one.
*(CliffordRealMinkowski · LorentzianChosen · SL2Connected)*

**L10 · The gauge algebra — PARTIAL.** Each Standard-Model factor embeds as a Lie algebra
where the estate says it does, and the full Standard Model algebra embeds injectively in the
Pati–Salam algebra. *Machine-refuted:* the July sentence "the SM algebra embeds in su(4)" for
the estate's own maps — the honest statement is the two-step one, and ~30 files' prose is
re-pointed accordingly (§7). The group level is a recorded postulate. *(SMLieHom ·
SMEmbeddingHonest · SMInPatiSalam)*

**L11 · Pati–Salam at M₁₆ — PARTIAL.** The isomorphism M₄ ⊗ M₄ ≅ M₁₆ is genuine;
Skolem–Noether and the automorphism structure are proved; the ⋆-structures on M₁₆ are counted.
*Not proved:* "(4,2,2) with no alternatives" — every factorisation a·b·c = 16 decomposes M₁₆
and nothing in the mathematics prefers one; the choice is carried by a recorded constraint
system. *(F1_6_PatiSalamForced · CascadeEnd · SkolemNoether)*

**L12 · Chirality — POSTULATE.** The asymmetry that makes the weak force left-handed is, in
the estate, a definitional convention: the mirror statement compiles with the same one-line
proof. This paper says so plainly — parity violation is *modelled*, not derived, and the row
that once said otherwise is corrected in §7. *(supporting structure: TransposeSplit ·
Su2ModuleSixteen)*

**L13 · Colour 4 → 3 ⊕ 1 — GENUINE.** On the cascade's own carrier: the block embedding of
gl₃, the invariant quark and lepton submodules, the singlet, B−L, and the triplet ℂ³ ≅ the
quark subspace intertwining the actions — irreducible inside the 4. *Stated:* identifying the
carrier with the SU(4) fundamental is a recorded assumption; no group-level statement.
*(ColourEquivariance · ColourTriplet · ColourCascadeSubmodule)*

**L14 · Three generations — POSTULATE.** Frobenius's theorem (the real division algebras are
ℝ, ℂ, ℍ) is proved; the pure quaternions form a 3-dimensional space; the complexification
identities hold at every size. The *identification* — those three directions ARE the three
generations — is a physical postulate, recorded, and the mathematics itself proves the
complexification cannot decide the real form, so the postulate is genuinely load-bearing.
*(RealDivisionQuaternionCase and siblings)*

**L15 · The Higgs sector — PARTIAL.** The coupling window g²/N ≤ λ̃ ≤ g² with both endpoints
sharp, the mass-squared window, and — new in this campaign — the Pati–Salam → Standard-Model
breaking *classified*: unbroken groups, broken-generator counts, topology, for pairs of vacua
at every rank-one first vacuum. *Not proved:* any scalar potential; the vacua are chosen, not
derived; N = 96 is a recorded choice; no 125 GeV claim is made anywhere. *(HiggsBridge ·
units 199–227)*

**L16 · Anomaly cancellation — PARTIAL.** The full perturbative anomaly table vanishes on the
chiral 16, evaluated on the actual representation in one theorem. *Cited, not proved:* that
the cubic trace IS the triangle anomaly (ABJ), and Witten's global anomaly (Mathlib has no
homotopy groups). The fermion content is an input. *(AnomalyTraces ·
PatiSalamOnSixteen)*

**L17 · The Weinberg angle — PARTIAL.** In exact rational arithmetic on the chiral 16:
Tr(T₃L²)/Tr(Q²) = 3/8, and Tr(T₃L²)/Tr(Y²) = 3/5 — with a control theorem showing the
same construction on dimension-counting gives 3/7, which *refutes* the programme's old
"3/8 from the dimensions" mechanism (§7). *Assumed:* the coupling matching that turns the
trace ratio into the physical angle at unification. *(WeinbergIndex)*

**L18 · The spectral triple — PARTIAL.** A complete finite real spectral triple of
KO-dimension 6 exists for Mₙ(ℂ) on a four-block space, and the estate's own triple on the
regular bimodule of M₂(ℂ) is understood completely. *Not proved:* that it is the *cascade's*
triple — nothing connects it to the cascade's Hilbert space; which real structure the cascade
carries was an open author decision, ruled on 27 September 2026 (the Chamseddine–Connes KO-6
convention; §6). *(KOSixSpectralTriple · KOSixRealStructure · units 164–172)*

**L19 · The spectral action: the exponential forced — PARTIAL.** The genuinely striking half
is proved: a factorising cutoff must be exponential (the Cauchy functional equation, in
Mathlib, no shortcuts), and on a tensor-sum operator the cutoff trace factorises. *Not
proved:* the premise. No theorem says the cascade's Dirac operator IS a tensor sum — the
estate has no cascade Dirac operator at all — and the campaign's final units settled exactly
when the order-one condition supplies that shape: for one full matrix algebra at one
generation, and *not* for products or generations. The "zero free parameters" headline of the
May register does not survive this row (§7). *(F4_1h · SpectralCutoffFactorises ·
KronSumCriterion · ProductKronSum)*

**L20 · The Boltzmann measure — PARTIAL.** A genuine 16-dimensional Gaussian probability
measure exists on the Hermitian slice, every polynomial moment finite. *Ruled (27 Sep 2026):*
the Gaussian is the programme's *stated approximation*; the true weight e^(−S) exists in no
Lean declaration, and the row says so. *(GaussianProductMeasure · Herm4Gaussian)*

**L21 · Quantum outputs — PARTIAL.** GNS on the trace state of the cascade algebra —
positivity derived, cyclic vacuum, state recovery, faithfulness; Stone's theorem in both
directions for bounded generators in any C⋆-algebra, instantiated on the cascade's carriers;
the Schrödinger equation at every finite level. *Cited, not derived:* the Born rule, Gleason,
Wigner — physics inputs, recorded. *Bounded generators only:* the unbounded case is gap W2's
named step. *(CascadeGNS · FiniteStone · StoneConverseLocal)*

**L22 · ◇ OPEN — the Einstein equations.** The predicted element at gap W5. What exists: the
algebraic Lovelock classification (every additive, homogeneous, equivariant map on curvature
tensors is α·Ric + β·S·δ — proved), and the geometric chain to rung 3. What is missing, named
exactly: the heat-kernel expansion of the spectral action — which requires unbounded
self-adjoint operator theory that exists nowhere in Lean's ecosystem. §8 states the
prediction.

**L23 · ◇ OPEN — Yang–Mills and the mass gap.** The predicted element at gaps W1–W4. What
exists: reflection positivity for the massive lattice field (measure level, every dimension),
OS1 in finite volume, transfer-matrix gaps computed exactly for stand-in models — and a
*measured refutation* showing the old uniform-bound target is false above the critical point,
which is why the target was re-stated by ruling this September. What is missing, named
exactly: the infinite-volume limit (no projective system exists to take it along), and an
estimate that sees the transfer matrix's structure below threshold. §8 states the prediction.

**L24 · The numbers — PARTIAL.** Exactly two physical numbers have been computed on actual
objects: sin²θ_W = 3/8 as a trace ratio, and the Higgs coupling window. Everything else —
Newton's constant, the cosmological constant, fermion masses, proton lifetime — is
uncomputed, and this paper says so in one sentence rather than seventeen tables. What the
May register claimed here is superseded (§7).
