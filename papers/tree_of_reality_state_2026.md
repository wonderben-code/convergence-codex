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

---

## 4. What fell — the campaign's harvest

The tags above are the theory's state. This section is what two months of machine
verification added to it — the wood that thickened even while no headline moved.

**Three walls closed outright.**
- **W6** (9 August): the Stein class and the smooth-compactly-supported Sobolev space
  W^{1,2}(γ) are one class — in every dimension. A question the programme could not settle in
  July is now a biconditional.
- **W7** (8 August): the real Clifford classification and the spin identification, with the
  full mod-8 periodicity table proved ten days later for every nondegenerate real form.
- **W8** (12 August): a **non-trivial reflexive domain** — an ordered structure genuinely
  satisfying D ≃ (D →𝒄 D) — constructed and verified. The root of the tree grew its own
  witness: the object the whole programme is named for exists, machine-checked.

**Lorentz and spin, proved properly.** The restricted Lorentz group as the identity component
of O(1,3) with no hypothesis; the double cover SL₂(ℂ) → SO⁺(1,3), surjective, kernel exactly
{±1}; the Clifford spin group modulo {±1} identified with SL₂(ℂ) modulo {±1}; the complex
Clifford classification in every rank.

**Analysis that outgrew its scaffolding.** The Gaussian Poincaré inequality in every dimension
at every variance; Hermite completeness; Wick's theorem at every order for the finite-volume
Gaussian field; Stone's theorem in both directions for bounded generators in any C⋆-algebra;
Frobenius's classification of the real division algebras; reflection positivity for the
massive lattice field at the measure level — the step wall W1 was *named* for, which fell by
a route no planning document had listed.

**The Standard-Model side, computed on actual objects — not on numerology.** The Weinberg
ratio 3/8 as a trace ratio on the chiral 16, in exact rational arithmetic, with a control
theorem that kills the old dimension-counting story; the full perturbative anomaly table
vanishing on the actual representation; the Standard Model algebra embedded injectively in
the Pati–Salam algebra; and — the campaign's late crown — the **Pati–Salam → Standard-Model
breaking classified**: the unbroken group at every relevant vacuum, the broken-generator
counts, and the topology, for pairs of vacua at every rank-one first vacuum.

**The seed understood completely.** M₂(ℂ) as the unique minimal seed over ℂ; every
⋆-structure on Mₙ(ℂ) classified — n/2 + 1 classes up to conjugacy; a faithful
⋆-representation selecting the conjugate transpose.

**The order-one chain, run to the end.** Sixteen units (168–243) solving the order-one
condition on every model bimodule the estate possesses — with the real structure, with the
grading, with generations, on products — ending in an exact criterion: the tensor-sum shape
that the spectral action's factorisation needs is **forced precisely for one full matrix
algebra at one generation, and not otherwise**. That theorem is what disciplines link L19
and retires the May register's proudest headline (§7).

**And five refutations, each a theorem.** A non-trivial D ≅ (D → D) over sets — impossible.
The Riemannian signatures excluded structurally — false; three signatures share one algebra.
The Standard Model assembled inside su(4) on the blocks used — false. 3/8 from the
dimensions — refuted by the 3/7 control. The estate's own comparison route for wall W3 —
proved insufficient, exactly (O(n) against a target of O(n²)). A programme that can prove
theorems *against itself* is measuring something.

One more finding is a measurement rather than a theorem, and it matters below: wall W4's old
uniform-bound target is **false above the critical point** — computed by diagonalising the
estate's own transfer matrices, where the eigenvalue ratio climbs to 0.99990 at width 13.
Two proof routes once recorded as failures were not lossy; they were correctly reporting that
the thing to be bounded does not exist. The target has been restated accordingly (§6).

## 5. The gap survey — six open walls, each with its failing step named

Mendeleev could describe gallium before it existed because the table's structure fixed the
properties of whatever had to fill the box. This section is our version of that constraint
structure: for each open gap — six walls behind the tree's two ◇ links and one PARTIAL — the
staircase that has been climbed, the exact step where the known routes stop, and **what would
have to exist** for the gap to close. That last item is the predicted shape of the missing
element.

**W1 · The lattice field's OS axioms — failing step: the infinite-volume limit.** The
finite-volume programme is done: reflection positivity proved at the measure level in every
dimension, OS1 proved in finite volume. The limit is not a missing estimate — it is a missing
*construction*: the finite-volume Gaussians are not a projective system (restricting a box's
Green function does not give the smaller box's), so no Kolmogorov-style argument applies.
**What would have to exist:** uniform-in-volume correlation bounds with a tightness argument,
or an independent infinite-volume construction with a convergence proof. Genuinely open
mathematics.

**W2 · The continuum field and OS reconstruction — failing step 2b: an unbounded self-adjoint
Hamiltonian.** The Hilbert space and vacuum come from GNS, already consumed by the estate.
The Hamiltonian that reconstruction produces is unbounded — and **Lean's mathematics library
contains no unbounded operator theory at all**: no densely defined operators, no adjoints and
closures, no spectral measure, no Borel functional calculus. Step 2b is not blocked on a
theorem; *the objects the theorem is about do not exist yet in the formal ecosystem.*
**What would have to exist:** the unbounded-operator subject itself — a library-scale
project, not a research riddle.

**W3 · Symmetry breaking (the Peierls argument) — failing step: the comparison bound.** The
combinatorial half is climbed: contours, cycle decompositions, the enclosure parity theorem.
The estate's own comparison route is *proved insufficient* — its output is computed exactly,
and it is O(n) against a target of O(n²). **What would have to exist:** two recorded author
decisions, then a comparison model of a genuinely different shape whose output is not
sublinear. Elementary but voluminous; the gap is a theorem that the old method cannot close
it, not evidence the statement is false.

**W4 · The mass gap — failing step: a uniform spectral estimate below threshold.** The
one-dimensional chain is solved completely (whole spectrum, gap 2e^{−|β|}, derived). The old
uniform target was *measured false* above the critical point and has been restated by ruling
to the high-temperature phase, where it is believed true and proved nowhere. **What would
have to exist:** an estimate that sees the transfer matrix's structure — Dobrushin
uniqueness or a high-temperature cluster expansion — neither of which exists in Mathlib.
Genuinely open formalisation of genuinely standard physics.

**W5 · The Einstein equations from the spectral action — failing step: rung 4, the
heat-kernel expansion.** Three rungs of differential geometry are climbed, including the
algebraic Lovelock classification (every additive, homogeneous, equivariant candidate is
α·Ric + β·S·δ — the *uniqueness* half of the Einstein equations, proved). Rung 4 needs the
Dirac operator as an unbounded self-adjoint operator with discrete spectrum, its heat
semigroup, the parametrix construction, and the coefficient identification. **What would have
to exist:** the same missing subject as W2, then a research-grade formalisation of the
heat-kernel expansion. Two costs, and they should never be quoted as one.

**W9 · The Chamseddine–Connes–Marcolli classification — failing step: rung 2's second half on
CCM's own bimodule.** Rung 1 is climbed (the campaign's own theorem). Rung 2's first half is
climbed for complex factors. The order-one condition is solved on *every model bimodule the
estate has* — the sixteen-unit chain of §4. What remains is the real thing: the isotypic
decomposition of CCM's H_F — a sub-bimodule of a product with three generations and a
quaternionic factor — built *as an object*, with order-one computed across its pieces. One
route is already closed by theorem (the doubled-algebra argument cannot run through a regular
bimodule). **What would have to exist:** that decomposition, then K-theory of finite algebras
for rung 3 — the latter absent from both the estate and Mathlib.

**The one missing subject.** Two of the six walls — W2 and W5, which are exactly the tree's
two ◇ links — fail at the *same* absent mathematics: unbounded self-adjoint operators. One
library, built once, unblocks both boxes. In the periodic-table analogy: two gaps in the
same column, filled by one discovery. It is the largest single unlock the survey identifies.

**And the honesty clause that governs this whole section:** a failing step marks where the
*known* routes stop. It is not a proof that no route exists. The campaign's own record
enforces the humility — W1's named step fell by a route no document had listed, three weeks
after the wall was declared.

## 6. What the theory rests on — the assumptions, stated

A theory's honesty is measured at its inputs. The assumptions ledger records **57 numbered
entries**: every choice the estate makes that no proof forced — a definition picked from
several, a hypothesis nothing supplies, a physics input taken from the literature. An
assumption is not a missing proof (those are §5's walls); it can only be closed by changing
the model or defending the choice.

Each entry carries a **bias grade**, and the grading is the ledger's sharpest instrument:
*anti-conservative* (the choice makes a result read stronger than it is — the dangerous
direction), *conservative* (reads weaker), *neutral*, or *mixed*. The ledger grades **most of
its own load-bearing entries anti-conservative** — it indicts its own choices where they
flatter the theory. Its current states are equally blunt: *Stands*, *Narrowed*, *Hardened*
(later theorems showed the easy repair is impossible), *Corrected*, *Retired* (proved — three
entries have graduated from assumption to theorem during the campaign).

**The seven that carry the most weight**, each in one line:
1. **The cascade record stores its own conclusions as fields** (entry 2) — the
   highest-leverage entry, invisible at its 21 consumption sites; a genuine recursive cascade
   now exists beside it, but no theorem yet marries the two.
2. **Which tensor factor decomposes** (entry 5) — parity violation rests on it; the mirror
   statement compiles with the same one-line proof.
3. **The trace state is the vacuum** (entry 16) — GNS's headline results fail for a pure
   state.
4. **The spectral weight is multiplicative with unit moments** (entry 12) — the "zero free
   parameters" story dies exactly here (§7).
5. **The Higgs vacua are chosen, not derived** (entry 60).
6. **Three generations are the imaginary quaternions** (entry 25) — *Hardened*: the
   mathematics itself now proves the complexification cannot decide the real form, so the
   postulate is genuinely load-bearing.
7. **The Born rule, Gleason and Wigner are cited physics, not theorems here** (entry 59).

**One entry is the estate's only axiom** (entry 53): a Gibbs measure with no defining
property, predating the campaign, quarantined and disclosed — no campaign theorem depends on
it.

**Eleven entries are author decisions**, and five were ruled on 27 September 2026 — the
rulings this paper is written under: the fermion content is a **named postulate** with
derivation as an open target; the Gaussian is the **stated approximation** to the
spectral-action measure, e^{−S} named as the true target; wall W4's target is **restated
below threshold**; the real structure adopts the **Chamseddine–Connes KO-6 convention**; and
the estate keeps **both spectral-triple notions under distinct names** — a strict
CCM-compliant structure for anything this paper calls a real spectral triple, the weaker one
as named scaffolding. The remaining six decisions stay open and are listed with the ledger.

## 7. The corrections — what this paper retires, in public

In May 2026 the programme's running register carried, in its own capitals: *"MASS GAP SOLVED,
QG 100% COMPLETE, UNCONDITIONAL MILLENNIUM PRIZE PROGRAMME COMPLETE, ZERO FREE PARAMETERS."*

This paper supersedes that register, and this section does it explicitly, because a
correction hidden in a footnote is not a correction. On 27 September 2026, twenty-six tag
rulings — each proposed by the verification campaign with its reasoning, each re-checked five
times against the estate — were accepted in full. **No derived theorem was withdrawn by any
of them.** The mathematics stands untouched; what moves is labels, in both directions, to
match the mathematics exactly.

**The loudest retirements:**
- **"Mass gap solved / QG 100% complete"** → the spine's honest tags are **OPEN** at L22 and
  L23. What exists are genuine theorems about the estate's internal models under stated
  hypotheses — real mathematics, wrongly headlined. The walls behind both links are §5's
  W1–W5.
- **"Zero free parameters"** → **not established.** The claim's chain has an unproven
  premise: that the cascade's Dirac operator is a tensor sum. The campaign's final theorems
  settle exactly when order-one forces that shape — for one full matrix algebra at one
  generation, and *not* for the published algebra's actual structure — and what the
  conditions leave free at three generations is a whole matrix, not three moments.
- **"ℂ ⊕ ℍ ⊕ M₃(ℂ) at the M₂₅₆ level — PROVED ★"** → **META, OPEN.** The campaign's own
  digest calls this the largest gap between tag and reality it found: no Lean file
  constructs that algebra at that level; the files that name it do so to say what they do
  *not* prove.
- **"The Weinberg angle 3/8 from the dimensions"** → mechanism **refuted** by the 3/7
  control theorem; replaced by the stronger true statement — 3/8 as a trace ratio on the
  actual representation, machine-checked in exact arithmetic.
- **Three July headlines refuted outright** by the campaign's own theorems: the
  full-function-space reflexive domain (only one-point solutions over sets); the structural
  exclusion of Riemannian signatures (three signatures share one algebra); the
  Standard-Model-in-su(4) assembly (not injective on the blocks used).

**And five upgrades, by the same discipline:** anomaly cancellation and Stone's theorem rise
from PREDICTED to PARTIAL; seed uniqueness from META-OPEN to PARTIAL; GNS to PROVED for the
cascade algebra with the trace state, scoped; the emergence-lineage row to PROVED — a place
where the paper had *undersold* its own Lean. A labelling system that can move in only one
direction measures nothing; this one moves both ways and is therefore worth reading.

The full ruling-by-ruling record, with the campaign's reasoning quoted, is published beside
the ledgers (§9).

---

## 8. The predictions — the empty boxes, and what will fill them

Mendeleev's 1869 table is remembered not for the sixty-three elements it contained but for
the boxes it left empty. He predicted eka-aluminium and eka-silicon — their densities, their
oxides, their melting behaviour — from nothing but the table's structure. Gallium arrived in
1875 and germanium in 1886, matching the descriptions, and the gaps turned out to have been
the strongest evidence the organising principle was real. A structure that can describe its
own missing pieces is not incomplete. It is *predictive*.

The Tree of Reality is published here in the same posture. Its two ◇ boxes and the wall
behind its hardest PARTIAL are not confessions appended to a theory; they are the theory's
predictive content, each specified to the exact failing step. We know precisely where each
box sits in the tree, precisely which staircase reaches it, precisely which step no known
route climbs, and precisely what the missing mathematics must look like when it arrives. That
is a description of eka-aluminium.

**The prediction, stated once and plainly:**

> **As machine reasoning in mathematics improves, each of the named gaps below will be
> closed, in the shapes specified — and the Tree of Reality will be shown whole. This
> prediction is dated, machine-checked at every boundary, and anchored to the Bitcoin
> blockchain. Whoever closes a gap — human, machine, or the two together — completes the
> programme published here.**

### The table of missing elements

| Box | Location in the tree | The exact failing step | The predicted shape of the missing piece | Kind |
|---|---|---|---|---|
| **E1** | L23 (◇), wall W1 | the infinite-volume limit of the lattice field | uniform-in-volume correlation bounds + tightness, or an independent infinite-volume construction with convergence | open mathematics |
| **E2** | L23 (◇) and L22 (◇), walls W2 + W5 | unbounded self-adjoint operators — absent from the entire formal ecosystem | densely defined operators, adjoints, closures, essential self-adjointness, spectral measure, semigroup ↔ generator | library-scale infrastructure |
| **E3** | L23 (◇), wall W3 | the Peierls comparison bound (the old route *proved* insufficient: O(n) against O(n²)) | a comparison model of genuinely different shape with non-sublinear output | voluminous combinatorics |
| **E4** | L23 (◇), wall W4 | a uniform sub-top spectral estimate, below threshold (restated by ruling; the unrestricted form is measured false) | Dobrushin uniqueness or a high-temperature cluster expansion, formalised | open formalisation of standard physics |
| **E5** | L22 (◇), wall W5 rung 4 | the heat-kernel expansion of the spectral action | the asymptotic expansion of Tr f(D/Λ) with a₂ identified as a curvature integral — after E2 exists | research-grade, gated on E2 |
| **E6** | L6, wall W9 rung 2 | order-one across the isotypic pieces of CCM's actual bimodule | the isotypic decomposition of a finite-dimensional bimodule over products of ℝ/ℂ/ℍ matrix algebras, built as an object; then K-theory of finite algebras for rung 3 | construction + missing library |

Three structural facts sharpen the table. **First**, E2 fills two boxes at once — the tree's
two ◇ links fail at the *same* absent subject, the way two gaps in one column of the periodic
table await elements with the same valence. **Second**, the boxes are of different kinds, and
the kinds have different closure profiles: library infrastructure (E2) is engineering — its
arrival is a matter of effort, not discovery; combinatorics (E3) yields to patience;
genuinely open mathematics (E1, E4) is the boldest part of the prediction, and we make it
anyway. **Third**, E5 is *gated*: it cannot be attempted before E2 exists, which makes the
predicted order of closure itself falsifiable content.

### Why we predict closure — the trajectory argument

The evidence is the campaign this paper closes. In forty-five working days, one researcher
and one reasoning machine produced 1,230 graded proof files; closed three walls outright —
including W8, a research-grade construction that had stood since the programme began; proved
the named step of a fourth wall by a route no planning document contained; and refuted three
of their own published headlines. Every one of those events was, five years ago, out of
reach of any machine on earth.

The instrument is improving faster than any instrument in the history of mathematics. We do
not claim a calendar; we claim a direction. Formal libraries compound — every object built
for one gap (E2's operators, E6's decomposition) permanently lowers the cost of every later
attempt. The gaps named here are, by construction, the *best-specified open problems in the
formal ecosystem*: each arrives with its staircase pre-climbed, its dead routes marked by
theorems rather than folklore, and its target statement already stated in a machine-checkable
idiom. They are, deliberately, the problems it is easiest for a rising capability to close.

### What would count against us

Symmetry demands this list, and honesty enjoys it. The prediction fails in kind, not just in
schedule, if: the restated W4 target is proved false *below* threshold too; the
infinite-volume limit of E1 is shown not to exist for the massive lattice field; the isotypic
computation of E6 yields an algebra *other than* the Chamseddine–Connes–Marcolli one; or the
heat-kernel coefficient of E5, once computable, fails to contain the Einstein term. Any of
these would be a machine-checked refutation of this paper's central claim, and we commit in
advance to publishing it under this paper's own DOI lineage with the same prominence as a
confirmation. The label discipline of §§1–7 is the reader's evidence that the commitment is
real.

And one caution we owe the reader in the other direction: a failing step marks where the
known routes stop, not where all routes stop. W1's own named step fell to an unlisted route
mid-campaign. The boxes may fill sooner, and stranger, than the table suggests. Mendeleev's
gallium arrived six years early, discovered by a man who had never read his prediction.

## 9. Provenance and verification — trust nothing, run everything

**The repository.** All Lean sources, ledgers, and this paper:
`github.com/wonderben-code/convergence-codex` (public). The verification campaign's working
registers — the graded file ledger, the spine table, the walls ledger with every dated
amendment, the 57-entry assumptions ledger, the 699 errata, the 1,846-entry progress log —
live in the companion repository `codex-internal`, same branch, under `formalisation/`.
Where any summary in this paper differs from a register, **the register is right and this
paper is wrong** — and the correction belongs in the errata.

**The stop point.** Branch `claude/infinitography-formalisation-fbqxf3`; the snapshot stop
point is the ledger commit following unit 243 (26 September 2026), with the five stop-point
ledgers under `lean_verify/paper_f/ledgers/`. The founder rulings this paper is written
under are recorded in `RULINGS_2026-09-27.md`.

**The anchoring.** Every commit in both repositories is Bitcoin-timestamped on a six-hourly
schedule via OpenTimestamps. The programme's twenty-seven prior papers carry dated Zenodo
DOIs; this paper receives its own. The May 2026 predictions register of the earlier
convergence-capstone lineage remains part of the stamped record under its own provenance;
its empirical predictions are a separate instrument from the gap-predictions of §8 and are
not restated here.

**The two commands.** To check the mathematics, no trust in the author is required:

```
lake build          # the estate: 5,091 jobs, green; one sorry + one axiom, both
                    # pre-campaign, both documented, neither load-bearing
#print axioms <thm> # any theorem: the campaign's files answer with the standard
                    # three axioms — propext, Classical.choice, Quot.sound
```

The per-file grades, the per-unit gate records, and `check_ledger.py --spine` (which
recomputes the scoreboard from the link table and fails if they disagree) are in the
registers.

## 10. Coda — publishing the table with its gaps

Here, then, is the tree as of today. Six links of solid, machine-checked wood — existence
forced from self-reference, the seed, the cascade and its arrow, the algebra of spacetime,
the splitting of colour. Thirteen links partly grown, each with its unproven remainder named
in public. Three grafts declared as grafts. And two empty boxes, drawn in their exact places,
with the properties of their missing elements written beside them.

We could have waited to publish until the boxes were filled. Mendeleev did not wait, and
chemistry is the richer for it: the empty boxes told the discoverers of gallium and germanium
what they were looking at. These boxes are offered in the same spirit — to whoever, or
whatever, arrives with the mathematics to fill them. The tree is planted, dated, and
anchored. The gaps are the invitation.

---

*Mark E. Mala, September 2026. The author thanks the reasoning machines this programme was
built with — including the one that spent forty-five days proving, refuting, and grading the
claims above, filed 699 corrections against the work and its own, and whose final act before
standing down was to soften a claim.*
