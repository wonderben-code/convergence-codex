# The Refined Gaps

### What the Tree of Reality's open boxes become if Chain Theory's candidates hold — a validation of the posture, and a sharper set of predictions

**Version:** v1, 25 October 2026. **DOI:** 10.5281/zenodo.23637019 · https://zenodo.org/record/23637019 (concept DOI 10.5281/zenodo.23637018). The sections describing Chain
Theory are open to correction by its author; corrections received will be incorporated in v2 under the
same concept DOI, and recorded in `docs/chain-theory/07_reading_log.md`.
**Author:** Mark E. Mala (pen name of Ekram Alam), with Claude
**Series:** the first successor to *The Staked Gaps* (DOI 10.5281/zenodo.23338726, 13 October 2026),
recording the first independent test of its predictions; companion to *The Tree of Reality*
(DOI 10.5281/zenodo.23011897, 28 September 2026)
**Verification:** this paper proves nothing new and changes no grade. Every claim about the Tree
cites a link code (L1–L24), a gap code (G1–G6) or a Lean file in `wonderben-code/convergence-codex`.
Every claim about Chain Theory cites a box or theorem number in its public documents of
23 October 2026 and carries Chain Theory's own grade. The one new computation (§4.6) is in
`scripts/chain_theory/q3_alpha_count_in_M16.py`, public and dated.

---

## Abstract

A theory of everything was built by one person and an AI and published, machine-verified, on
28 September 2026: a single minimal algebra, forced by self-reference, growing by one repeated
operation into the structures of physics. It was published *with its gaps* — twenty-four links,
each graded, each unproven residue named — and on 13 October 2026 those gaps were published a
second time as pre-registered predictions: where each sits, what shape its filler must take, who
would fill it (*"advancing AI, human–machine teams, or the authors"*), roughly when, and what would
refute the theory at each site. Ten days later, on 23 October 2026, A. D. Wissner-Gross released
*Chain Theory*: an independent, Lean-checked, graded programme deriving Standard-Model structure
from finitely many entangled finite-dimensional systems, developed as a human–AI collaboration.
Its objects are built from exactly the three dimensions the Tree forces — 2, 4 and 3 — and its
results land on exactly the residues the Tree named: three generations, confinement, the Born
rule, Lorentzian signature, the three lineages, chirality. The Tree's pre-registered trichotomy
for any newly found structure — *extends the walked branch, realises a sibling, or fits nowhere*
— returned its first verdict: *extends the walked branch*. This paper does three things, in the
posture the series committed to. **First**, it states precisely what that fit validates — the
method: the forced objects are the natural ones, the residues were correctly located, the
meta-prediction's agent and timetable were right in kind — and precisely what it does not: no
physical identification on either side, none of the six headline gaps G1–G6, no grade, and not
the fine-structure constant. **Second**, it takes each candidate *as if correct* and shows that
the corresponding gap does not vanish but *sharpens*: a part the candidate would cover, and a
residual that is smaller, better specified, and more falsifiable than before. **Third**, it
pre-registers those residuals as the next predictions — attribute lists, kill-conditions, and the
computation or proof that tests each — so that running the test *is* testing the prediction, in
either direction. The result is a theory whose gaps are more precisely known than they were ten
days ago, because an independent programme put candidates in them, and whose next edition is
earned, not asserted.

---

## 1. The theory, stated

The Tree of Reality proposes that the structures of physics are not axioms but descendants. Where
the unification tradition seeks one framework to *contain* the known structures, the Tree derives
them from one *ancestor* — a theory of everything in the sense that evolutionary biology is a
theory of every species: unification by common descent.

The root is Lawvere's fixed-point theorem: a structure that can refer to itself cannot be empty of
fixed points, so self-reference forces existence (L1). The seed is M₂(ℂ), the observable algebra
of one qubit — the unique minimal non-commutative algebra over ℂ (L3). The operation is *take the
algebra of endomorphisms*: End(M_b) ≅ M_{b²}, so the seed grows M₂ → M₄ → M₁₆ → M₂₅₆ → … (L4),
irreversibly (L5). Three lineages run up the tree — what things *are* (End), how they *transform*
(Aut), how they are *known* (the inner product) (L7). On the branches: spacetime dimension four,
because Cl₄(ℂ) ≅ M₄(ℂ) and no other Clifford algebra is a level of the cascade (L8); Lorentzian
signature (L9); the gauge algebra and Pati–Salam structure on M₁₆ = M₄ ⊗ M₄ (L10, L11), with colour
as the split 4 → 3⊕1 (L13); chirality, three generations, the Higgs sector, anomaly cancellation,
the Weinberg ratio 3/8 (L12, L14–L17); the spectral triple and spectral action (L18–L20); the
quantum apparatus by GNS, Stone and Schrödinger (L21); and at the frontier, the Einstein
equations from the spectral action (L22) and Yang–Mills with its mass gap (L23). Every link is
graded against machine-checked Lean 4 proofs in Mathlib.

## 2. The shape we mapped, and the gaps we left

### 2.1 The scoreboard, 28 September 2026

| Link | Grade | Headline | The named residue (what is *not* proved) |
|---|---|---|---|
| L1 | GENUINE | existence from self-reference (Lawvere) | — |
| L2 | PARTIAL | the reflexive domain D ≃ (D → D) | existence as a non-trivial ordered structure beyond the finite levels |
| L3 | GENUINE | the seed M₂(ℂ) | — |
| L4 | GENUINE | the cascade M₂ → M₄ → M₁₆ → … | — |
| L5 | GENUINE | irreversibility | — |
| L6 | PARTIAL | why the fourth level (the CCM algebra) | minimality of 4 proved under a stated criterion; the criterion not forced |
| L7 | **POSTULATE** | three lineages: End · Aut · ⟨·,·⟩ | that these are *the only* lineages |
| L8 | GENUINE | spacetime dimension 4: Cl₄(ℂ) ≅ M₄(ℂ) | — |
| L9 | PARTIAL | Lorentzian signature (1,3) | the step excluding the Euclidean alternative (a fork) |
| L10 | PARTIAL | the gauge algebra, embedded | — |
| L11 | PARTIAL | Pati–Salam at M₁₆ | the factorisation 4·4 chosen among a·b·c = 16 |
| L12 | **POSTULATE** | chirality — which factor is "left" | the choice of factor |
| L13 | GENUINE | colour: the 4 splits as 3⊕1 | — |
| L14 | **POSTULATE** | three generations — the imaginary quaternions | the count itself |
| L15 | PARTIAL | the Higgs sector and coupling window | any scalar potential; the vacua |
| L16 | PARTIAL | anomaly cancellation | — |
| L17 | PARTIAL | the Weinberg angle 3/8 as a trace ratio | the coupling matching at unification |
| L18 | PARTIAL | the spectral triple | — |
| L19 | PARTIAL | the spectral action: the exponential forced | forced for one algebra at one generation only |
| L20 | PARTIAL | the Boltzmann measure of the action | — |
| L21 | PARTIAL | Hilbert space, GNS, Stone, Schrödinger | *the Born rule, Gleason and Wigner are cited physics, not theorems* |
| L22 | **◇ OPEN** | the Einstein equations from the spectral action | gap G5, gated on G2 |
| L23 | **◇ OPEN** | Yang–Mills and the mass gap | walls W1–W4; gaps G1, G3, G4 |
| L24 | PARTIAL | the numbers | no coupling constant computed |

**6 GENUINE · 13 PARTIAL · 3 POSTULATE · 2 OPEN.**

### 2.2 Three kinds of gap, three kinds of prediction

*The Staked Gaps* (13 October) distinguished them:

- **The six headline gaps G1–G6** — analytic and representation-theoretic obstacles in the proof
  chain (the infinite-volume limit; the unbounded-operator library; a comparison bound of new
  shape; a uniform sub-top spectral estimate; the heat-kernel expansion of the spectral action;
  the isotypic bimodule and its K-theory). Each was staked with an *attribute list*, a *kind*
  (pinned / bounded / open-directional), and a *kill-condition*.
- **The residues** — "Every PARTIAL link of the capstone's §4 carries a named, machine-checkable
  remainder, and the prediction covers them too: as the boxes fill and the residues close, the
  wood of the tree hardens."
- **The sibling branches** — alternative descendants of the seed, proved to exist as mathematics
  at four forks, predicted to be "candidates for physics not yet found."

### 2.3 Who, and when — the meta-prediction

> "As automated mathematical reasoning continues its current trajectory, the gaps named here will
> be closed — in the shapes predicted — soon (on the order of years, not decades) … **The agent of
> closure will be advancing AI, human–machine teams, or the authors.**" (*The Staked Gaps* §7)

And the protocol for a fill:

> "Anyone — human, machine, or the two together — who closes a gap in the shape predicted …
> confirms a pre-registered prediction; the dated, Bitcoin-anchored record of *this* paper
> establishes the priority of the prediction, **not a claim on the solver's work**." (§8)

### 2.4 Where anything new must land — the trichotomy

> "Physics not yet known will, when found, do one of three things. **Either it extends the walked
> branch** — a new structure of our own lineage, joining the tree where the tree already has a
> place for it, strengthening it; **or it realises a sibling** … ; **or it fits nowhere on the
> tree at all** … The first two confirm the theory, and are predicted. The third refutes the
> generative claim itself." (*The Tree of Reality* §9)

With the boundary that keeps it honest: "the tree is refutable on the branch it walks, and never
excused by the branches it merely permits."

That is the shape we mapped. The posture was stated as a posture — "the analogy claims a
*posture*, not a *stature*" — and what follows is the first occasion on which the posture was
tested by something we did not build.

## 3. What arrived, ten days later

On 23 October 2026 A. D. Wissner-Gross released *Chain Theory*: a 24-page preprint (*A
Parameter-Free Candidate for the Fine-Structure Constant from Entangled Qudits*), a 754-page
working-draft compendium (release 0.1; 100 theorems, 64 tied to Lean declarations; 109 conditional
theorems; 198 open results), an introductory slide deck, and a self-contained Core Lean 4 file
checking the preprint's central count. The announcement followed on 24 October.

Its axiom: *"Nothing exists but finitely many maximally entangled pairs of qudits, some qudits
shared, known only by distilling them."* From this and six definitions it obtains a *read cap*
(a read fixes both ends of a pair only when d₁d₂ ≤ 6, by Størmer–Woronowicz–Choi), six *genres*
of link labelled by end dimensions drawn from {2, 3, 4} (Conjecture 0, box 1.7), the group
S(U(3)×U(2)) ≅ (SU(3)×SU(2)×U(1))/ℤ₆ as the symmetry of the qutrit–qubit pair (theorems 64.2,
65.1), and — as conditional theorems — the Born rule, the Lorentz group and signature, three
generations as a bound, confinement, curvature and a cosmological term. Its headline is an exact
number, (79 + 48√2 + 42√3 + 3√6)/31104, a theorem of the definitions, *conjectured* to be the
fine-structure constant at zero momentum transfer (0.60σ from CODATA 2022). Its acknowledgments
state that the work "was developed as part of a long-term human-superintelligence collaboration
supervised by the human author."

Neither programme cites the other before this paper. Chain Theory names "the spectral action on
a finite noncommutative geometry" as a sibling tradition; the Tree grows from it.

## 4. The fit

We now hold Chain Theory against the shape of §2, object by object, and record where it fits,
where it does not, and which fits are generic.

### 4.1 The objects: built from exactly what the Tree forces

Chain Theory's Conjecture 0 is that link ends have dimension 2, 3 or 4 — found from its move
table, graded a conditional theorem, with no generative reason given for the set. The Tree's
cascade produces levels of dimension 2, 4, 16, … (L4, GENUINE); colour splits the 4 as 3⊕1 (L13,
GENUINE). So **the Tree generates exactly {2, 4} as levels and {3} as a split of a level, and
nothing of dimension 5, 6, 7 or 8 below 16.** An independent programme, with no generative
principle, found by exhaustion the same three dimensions the Tree forces by construction. Chain
Theory's ququart is End(M₂); its qubit is the seed; its qutrit is the colour triplet.

### 4.2 The residues: candidates land where the residues were named

| Tree residue (28 Sep) | Chain Theory candidate (23 Oct) | Its grade |
|---|---|---|
| L14 · "three generations … a physical postulate; the mathematics proves what follows from it" — *the count itself* | the generation bound at the hub dimension: a ququart hub assembly admits at most the third generation (197.3); three at the core triangle (83.1); three *as* the count held open (197.5) | 197.3 theorem; 83.1 theorem on the roster; 197.5 open |
| L23 · a wall, no mechanism | confinement as dark-genre readability: the (3,3) link has d₁d₂ = 9 > 6, so no single read fixes both ends (171.1) | conditional |
| L21 · "the Born rule, Gleason and Wigner are cited physics, not theorems here" | the Born readout from the wash (35.1, 40.1), premises named: the Hilbert space of a qudit and the pair as a ray | conditional |
| L9 · the fork: Euclidean not excluded | the Lorentz group as isometries of the Hermitian split (54.1); one against three at every step (55.1); the Pell-lattice argument that only the indefinite form has infinitely many integer isometries | 54.1 conditional; 55.1 theorem |
| L7 · "that End, Aut and ⟨·,·⟩ are *the only* lineages" | Definition 1.6, "known": what all reads fix jointly under every matching and exchange — pairs / matchings / reads as the three primitives | definition |
| L12 · which factor is "left" | parity as the improper element (59.1); three involutions with CPT their product (61.1) | 59.1 conditional; 61.1 theorem |

Six of the Tree's nine non-GENUINE-non-headline openings received a candidate aimed at the
named residue. None of the candidates was aimed at the Tree; each is a result of Chain Theory
about its own networks. That they land where they do is the content.

### 4.3 The trichotomy: *extends the walked branch*

The capstone's first outcome reads: "a new structure of our own lineage, joining the tree where
the tree already has a place for it, strengthening it." Chain Theory's objects — qubit, pair of
qubits, ququart, qutrit, S(U(3)×U(2)), SU(4) = Spin(6) — each have a place on the walked branch
(L3, L8, L4, L13, L10–L11, L11). None realises an unwalked sibling (no quaternionic seed, no
Riemannian signature, no alternative cut of M₁₆). None fits nowhere. **The first independent
test of the trichotomy returned the first confirming outcome.** The boundary of §2.4 is
respected: nothing here is a failure on the walked branch reclassified as a sibling.

### 4.4 The meta-prediction: agent and timetable, right in kind

The staked agent of closure was "advancing AI, human–machine teams, or the authors." Chain
Theory describes itself as a human–superintelligence collaboration and checks its computations
in Lean. The staked timetable was "soon (on the order of years, not decades)." Candidates for
six residues arrived ten days after the predictions were staked and twenty-five days after the
tree was published. We record this as the meta-prediction materialising *in kind* — the kind of
agent, the kind of method, the direction of the timetable — and we are explicit that it
materialised on *residues*, not on the six headline gaps, whose timetable is unaffected (§4.5).

### 4.5 What did not fit

**The six headline gaps G1–G6 received no candidates.** Chain Theory's confinement mechanism is
of a different kind from the continuum-limit and spectral-gap estimates G1, G3 and G4 ask for.
Its gravity (depth metric, graph-Laplacian curvature, cosmological term at the depth exponent) is
a route disjoint from the heat-kernel expansion G5 predicts. It uses neither unbounded operators
(G2) nor the spectral triple (G6). The headline predictions stand exactly as staked.

**The number did not transfer** (§4.6). **No physical identification was confirmed** on either
side (§5).

**Generic and non-generic fits.** The Standard-Model group as S(U(3)×U(2)) is a generic
consequence of having a 3 and a 2 — the stabiliser of a 3+2 split in SU(5) (Baez–Huerta 2010,
which Chain Theory cites) — and any finite programme with a qutrit and a qubit reaches it. That
fit is weak evidence. Three fits are not generic: (i) the pair of qubits as *four*-dimensional
spacetime — the Tree's theorem about Clifford algebras, Chain Theory's spin-c group of the pair,
with nothing in "two qubits" forcing "four dimensions" in general; (ii) the register set
*exactly* {2, 3, 4} — found by exhaustion on one side, generated on the other, with neither
having a reason to stop at 4 except that it does; (iii) the threshold 6 marking the visible world
on both sides — Chain Theory's read cap from positive-map decomposability, the Tree's 3 ⊗ 2 block
from the colour split, with no shared premise. A fourth non-generic fit emerged from the
computation in §4.6.

### 4.6 One computation: the α object inside the Tree

We rebuilt Chain Theory's 172-record count from its own rules — letters at four slots (8, 3, 8,
3), 169 products and 3 commutators, exchanges X and Y as 172 × 172 commuting involutions — and
reproduced it exactly: sectors 79, 48, 42, 3; 1/α = 137.035 999 189 566 155…. We then realised
the object inside the Tree's M₁₆ = (3⊕1) ⊗ 2 ⊗ 2 by explicit matrices. Three facts:

1. The qutrit and both read qubits are present with the right letter algebras and commutation
   structure, so **the numerator transfers unchanged** — it depends on the end dimensions alone.
2. The denominator's unread third link needs a third qubit entangled with the qutrit. **M₁₆ has
   two; the third first appears at M₂₅₆ — the Tree's fourth level, the level at which L6
   independently places the Chamseddine–Connes–Marcolli finite algebra.** Neither programme had
   reason to expect the other's object to complete there. This is the fourth non-generic fit.
3. The 169 products, realised as matrices, span only 66 dimensions: Chain Theory's two *copies*
   of the one shared qutrit — "one copy per link" (Definition 1.3) — collapse to a single M₃
   factor. **The number lives in Chain Theory's record space, defined by "shared" (1.3) and
   "known" (1.6), not in the operator algebra of the shared system.** The Tree supplies the
   object; it does not supply the number. For Chain Theory this localises exactly which clauses
   a derivation of α rests on. For the Tree it sharpens L24 (§6.4).

## 5. What this validates, and what it does not

We owe the reader the boundary before the claims.

**Not validated.** No physical identification, on either side: that M₄ is spacetime, that the 3
is colour, that the (3,2) link is the photon, that the number is α — all remain conjectures,
graded as such by both programmes. Not one of G1–G6. Not one grade on the Tree: the scoreboard is
6 · 13 · 3 · 2 today as it was on 28 September. Not the fine-structure constant: the Tree does not
derive it, and §4.6 shows why it cannot from the algebra alone.

**Validated — three claims about the method, each bounded.**

1. **The forced objects are the natural ones.** The Tree's distinctive claim is generative: that
   2, 4 and 3 are not chosen but produced. An independent programme with no generative principle,
   searching its own move table, found exactly those three dimensions and no others. If the Tree
   had forced {2, 4, 16} with colour as 16 → 15⊕1, or if Chain Theory had needed a register of 5,
   the two would have missed. They did not. This is the kind of evidence a generative claim can
   receive short of proof: the things it says must exist are the things someone else found.

2. **The residues were correctly located.** Six named residues received candidates aimed at
   exactly what the residue said was missing — the count of generations, a mechanism for
   confinement, a derivation of the probability rule, an exclusion of the Euclidean signature, a
   reason for three lineages, a reason for "left". The Tree did not say "something is missing
   here"; it said *what* was missing, and candidates for *that* arrived. This validates the
   grading discipline: a PARTIAL row that names its residue precisely is a row someone else can
   fill.

3. **The meta-prediction was right in kind.** Agent (human–AI collaboration with formal
   checking), method (Lean), direction (candidates within weeks of staking). It was not tested on
   G1–G6, where the timetable remains open, and we do not claim it was.

The validation is of the *posture*, not the *stature* — exactly the distinction *The Staked Gaps*
drew. A theory that specifies its own missing pieces precisely enough that an independent
programme's results can be matched to them, attribute by attribute, is a theory whose gaps are
doing work. That is now demonstrated once. Whether the pieces *fit* — whether the candidates hold
and the residuals close — is what §6 and §7 put at risk.

## 6. The refined gaps

The Mendeleev move is not "a candidate arrived, box filled." It is: *a candidate of this shape
lets us predict the box's finer properties.* Conditional on each candidate being correct, the
corresponding gap decomposes into the part the candidate would cover and a residual — smaller,
sharper, and killable. We state each residual in the format of *The Staked Gaps*: prediction
kind, attributes, kill-condition, and the test (from `docs/chain-theory/06_questions_to_work_on_together.md`)
whose outcome decides it.

### 6.1 L14 · three generations

**As staked:** POSTULATE — the count is not derived; the candidate reason is that ℍ ⊂ M₂(ℂ) has
three imaginary units.
**If the candidate holds (197.3):** the count is bounded above by three, from the hub dimension
four — i.e. from M₄ = M₂ ⊗ M₂, the Tree's first cascade step.
**The gap becomes two:**
- **(a) the bound, transferred.** *Pinned.* Attributes: a Mathlib theorem on tensor
  factorisations of M₄ = M₂ ⊗ M₂ stating that at most three independent "attachments" of the kind
  Chain Theory's hub assembly makes are admitted. Kill-condition: the bound depends essentially on
  Chain Theory's network moves and has no statement about M₄ alone. Test: Q4.
- **(b) exactly three.** *Pinned.* Attributes: the three attach sites of Chain Theory's closed
  core triangle (83.1, 197.4), realised as operators, satisfy the quaternion relations
  i² = j² = k² = ijk = −1 up to the twirl — so that Chain Theory's open result 197.5 and the
  Tree's postulate are one statement. Kill-condition: the three attach-site operators commute, or
  generate something other than ℍ. Test: Q5.
**What moves if both hold:** L14 → GENUINE. If (a) holds and (b) fails: L14 → "bounded above by
theorem; selection open" — a real grade change, and the postulate is replaced by a smaller one.

### 6.2 L23 · Yang–Mills and the mass gap

**As staked:** ◇ OPEN — a wall (W1–W4) with gaps G1, G3, G4 behind it; no mechanism.
**If the candidate holds (171.1):** confinement has a *reason* — on the colour block M₃ ⊗ M₃
(the Tree's qutrit twice), d₁d₂ = 9 exceeds the read cap, so no single act of knowing fixes both
colour ends.
**The gap becomes two:**
- **(a) the mechanism.** *Bounded.* Attributes: a statement about the spectral triple (A, H, D)
  restricted to the colour block — our ranked candidates: (i) no conditional expectation onto a
  mutually-unbiased-basis sub-algebra of M₃ ⊗ M₃ commutes with D on that block; (ii) the
  positive-map decomposability threshold reappears as a property of the bimodule structure (L18).
  Kill-condition: the read cap has no statement in the algebraic picture — it is a feature of the
  network of copies that the operator algebra does not see. Test: Q6.
- **(b) the continuum.** *Unchanged.* G1, G3, G4 exactly as staked. The candidate speaks to *why*
  there is a gap, not to *how large* it is or whether the infinite-volume limit exists. We predict
  that a successful (a) does not shorten (b)'s timetable.
**What moves if (a) holds:** L23 → "mechanism stated, continuum limit open" — from a wall to a
staircase with its first step built.

### 6.3 L21 · the Born rule

**As staked:** PARTIAL — Hilbert space by GNS from the inner product; the Born rule, Gleason and
Wigner *cited*.
**If the candidate holds (35.1, 40.1):** the probability rule is an output of the wash, given the
Hilbert space of a qudit and the pair as a ray.
**The gap becomes one, and small:** *Pinned.* Attributes: the chain *GNS (Tree) → Hilbert space
of a qudit → wash (Chain Theory) → Born readout* closes with nothing used twice and nothing
cited — the Tree supplies exactly the import Chain Theory names, and Chain Theory supplies exactly
the rule the Tree cites. Kill-condition: a second import in Chain Theory's premises ("the pair as
a ray," or the twirl's invariance) that the Tree's inner-product lineage does not already
provide. Test: Q8.
**What moves if it holds:** L21 → GENUINE for the probability rule; the assumptions ledger loses
entry 59.

### 6.4 L24 · the numbers

**As staked:** PARTIAL — two numbers computed (the Weinberg ratio, a Higgs window); no coupling
constant.
**What §4.6 established:** the α object's ingredients are forced by the cascade (qutrit, two
qubits at M₁₆, the third at M₂₅₆), but the number lives in Chain Theory's record space, not in the
algebra.
**The gap becomes precise:** *Open-directional.* Attributes: a construction, over M₂₅₆, of a
record space in which the one shared qutrit appears as *one copy per link* — the content of
Chain Theory's Definition 1.3 — from the Tree's third lineage (the inner product) and nothing
else. If it exists, the Tree derives the 172-record space and with it the numerator and
denominator; if it does not, the Tree has identified "one copy per link" as the one
extra-algebraic clause in the derivation of α. Kill-condition for the *Tree's* side: the inner
product lineage provably yields only the operator algebra of the shared system (rank 66 of the
169 products) and no copy structure. Test: a follow-on to Q3, stated in
`docs/chain-theory/08_results_first_pass.md`.
**What moves:** nothing until the construction exists. But the gap has changed character: from
"no coupling constant" to "one named clause stands between the Tree and a coupling constant."

### 6.5 L9 · Lorentzian signature

**As staked:** PARTIAL — the fork; Euclidean not excluded.
**If the candidate holds (54.1, ch. 54):** the indefinite form on the lattice of counts admits
infinitely many integer isometries (a Pell family) while the definite form admits finitely many,
so the signature "reads Lorentzian by existence."
**The gap becomes one:** *Pinned.* Attributes: the Tree's Clifford lattice in M₄ (the integer
structure of γ₁…γ₄ in `F4_1e_CliffordMatrix.lean`) carries an indefinite integer form with an
infinite isometry group and a definite one with a finite group. Kill-condition: both forms on
that lattice have infinite isometry groups, or both finite. Test: a lattice computation on the γ
basis — straightforward.
**What moves if it holds:** L9 → GENUINE, by a route the Tree had not tried.

### 6.6 L7 · the three lineages

**As staked:** POSTULATE — that End, Aut and ⟨·,·⟩ are *the only* lineages.
**If the candidate holds (Definition 1.6):** a structure is a thing (pairs), acted on
(matchings), and known only through what the action leaves fixed (reads/"known") — three
primitives, no fourth.
**The gap becomes one:** *Pinned.* Attributes: a theorem that an object equipped with an action
and a knowledge clause of Chain Theory's form has exactly three aspects — carrier, symmetry,
invariant pairing — and that any fourth is a function of these. Kill-condition: a fourth
primitive that is not derived. Test: Q9.
**What moves if it holds:** L7 → GENUINE; the Tree's only *structural* postulate becomes a
theorem with a knowledge clause as its premise.

### 6.7 L12 · chirality

**As staked:** POSTULATE — which factor of M₄ ⊗ M₄ is "left" is chosen.
**If the candidate holds (59.1, 61.1):** parity is the improper element of the Hermitian split's
isometry group; CPT is the product of three involutions.
**The gap becomes one:** *Bounded.* Attributes: the improper element, realised on M₄ ⊗ M₄,
either (i) exchanges the two factors — in which case "left" is a convention, as *The Forced and
the Chosen* already argues — or (ii) acts non-trivially within one factor, singling it out.
Kill-condition: the improper element has no action on the factorisation at all. Test: a
computation on the γ basis.

### 6.8 The fourth level — a new prediction from §4.6

**Not previously staked.** The Tree's L6 places the Chamseddine–Connes–Marcolli finite algebra —
the full Standard-Model fermion content as a bimodule — at the fourth level M₂₅₆, under a stated
minimality criterion. §4.6 found that Chain Theory's α object, complete with its third qubit,
first fits at the same level.
**Prediction:** *Pinned.* Attributes: Chain Theory's sixteen particle webs (17 particles), each a
network of links with ends in {2, 3, 4}, embed in M₂₅₆ = M₁₆ ⊗ M₁₆ with the hub assemblies as
M₄ factors and the core triangles in the colour blocks — and the embedding respects the CCM
bimodule's isotypic decomposition (G6). Kill-condition: a particle web of Chain Theory requires
more tensor factors than M₂₅₆ provides, or fits only at M₆₅₅₃₆. Test: a dimension count per web,
then the embedding. This is the first prediction the two programmes generate *jointly*: neither
could have stated it alone.

### 6.9 In the other direction: what the Tree predicts for Chain Theory's open items

The refinement runs both ways. Taking the Tree's theorems as correct:

- **Conjecture 0 (1.7).** *Prediction:* no web of Chain Theory will ever require an end of
  dimension 5, 6, 7 or 8; the next admissible register after 4 is 16. *Kill-condition:* a web
  that needs a 5-dimensional end. Test: Q10, a census of the move table.
- **Conjecture 2 (1.9).** *Prediction:* the four generators of the (2,2) register (ch. 3-5) are
  Clifford generators of Cl₄(ℂ) on M₂ ⊗ M₂, and no (d,d) register other than (2,2) carries a
  Clifford structure that is a cascade level. Already checked in part: the compendium's β is the
  Tree's γ₁ entry for entry (Q2). *Kill-condition:* a Clifford structure at (3,3) or (4,4) that
  is a cascade level.
- **The Weinberg angle (not derived in the compendium).** *Prediction:* if Chain Theory's W and Z
  "offices" (164.5: ratio exactly ½) are the traces Tr(T₃L²) and Tr(Q²) on its particle webs,
  their ratio at the unification reading is 3/8 and at the hypercharge reading 3/5. *Kill-condition:*
  a different ratio from the same offices.
- **The step below the axiom.** *Prediction:* Chain Theory's Definition 1.6 is satisfiable only on
  a carrier admitting a reflexive structure D ≃ (D → D), so that Lawvere's theorem applies and the
  existence of at least one qudit is forced rather than posited. *Kill-condition:* a model of the
  six definitions on a carrier with no fixed-point property.

## 7. The predictions, pre-registered

| # | Residual | Kind | Test | Confirms | Refutes (at that site) |
|---|---|---|---|---|---|
| R1 | L14(a) the ≤3 bound on M₄ | pinned | Q4 | bound is a theorem of M₂ ⊗ M₂ | bound needs the network |
| R2 | L14(b) attach sites = i, j, k | pinned | Q5 | quaternion relations hold up to twirl | sites commute / not ℍ |
| R3 | L23(a) read cap on the spectral triple | bounded (2 shapes) | Q6 | a statement about (A, H, D) on the colour block | no algebraic statement |
| R4 | L23(b) continuum unchanged | — | — | G1/G3/G4 timetable unaffected | (a) shortens (b) — would be a surprise, not a refutation |
| R5 | L21 the Born circle | pinned | Q8 | GNS → wash closes with no import | a second hidden import |
| R6 | L24 record space over M₂₅₆ | open-directional | Q3′ | "one copy per link" from the inner product | only the operator algebra (rank 66) |
| R7 | L9 Pell family on the γ lattice | pinned | lattice computation | indefinite infinite, definite finite | both infinite or both finite |
| R8 | L7 three aspects from a knowledge clause | pinned | Q9 | carrier / symmetry / pairing, no fourth | a fourth primitive |
| R9 | L12 the improper element on the factorisation | bounded (2 shapes) | γ computation | exchanges factors, or singles one out | no action |
| R10 | Fourth level: particle webs in M₂₅₆ | pinned | dimension count + embedding | all 16 webs fit, respecting G6's decomposition | a web needs M₆₅₅₃₆ |
| R11 | Chain Theory: no register 5–8 | pinned | Q10 | census confirms | a 5-dim end |
| R12 | Chain Theory: Weinberg 3/8 from the offices | pinned | trace identification | 3/8 and 3/5 | other ratios |

**The gated order, as before.** R7, R9 and R10's dimension count are computations and come first.
R1, R3, R5, R8 are Mathlib proofs. R2, R6, R10's embedding, R11, R12 need both programmes'
objects side by side and are the joint work.

### 7.1 First results, 25 October 2026

Two residuals were pure computations and were run on the day of writing
(`scripts/chain_theory/r7_r9_lattice_and_parity.py`, public). Both came back as *refinements* — the
outcome §6 said a correct candidate should produce.

**R7 — holds as stated, and sharpens.** On the Tree's Clifford lattice, the Euclidean form (4,0)
has exactly 384 integer isometries (finite, by enumeration); the Lorentzian form (1,3) and the
split form (2,2) each admit an integer isometry of infinite order (spectral radii 5.83 and 5.16,
explicit matrices in the script). So Chain Theory's existence argument *excludes the Euclidean
branch* at the fork L9 — a theorem-grade exclusion the Tree did not have — and does *not* choose
between the indefinite signatures (1,3) and (2,2), which share Cl₄(ℂ). L9's residue narrows to
"select among the indefinite three"; it does not close.

**R9 — answered, and re-posed.** With the Tree's γ-basis, the improper element P = γ₁ = σ₃ ⊗ I₂
acts within the first tensor factor of M₄ = M₂ ⊗ M₂ (shape ii) and anticommutes with
γ₅ = γ₁γ₂γ₃γ₄ = σ₂ ⊗ σ₂. But γ₅ is not aligned with the factorisation — the Weyl split is not a
tensor-factor split — and which factor P lives in is a property of the basis. So "which factor is
left" is not a question M₄ can answer, and R9 was posed on the wrong object. It is re-posed at
M₁₆ = M₄ ⊗ M₄, where L12's choice actually lives, as **R9′**: *does the improper element of Cl₄,
lifted to M₁₆, exchange the two M₄ factors or single one out?* We record this as a correction to
this paper found by its own test, on the day of writing, and leave the original R9 in the table
above so the correction is visible.

## 8. What kills this paper

Three layers, stated in advance.

**If the candidates fail on their own side** — if Chain Theory's 197.3, 171.1, 35.1 or 54.1 do
not survive its own further work — then §6's conditionals are vacuous for those rows and the
gaps revert to their 13 October statement. §4's validation of the *method* survives, because it
concerned where candidates were aimed, not whether they hold; §5's three claims survive for the
same reason. We would record the reversion under this paper's DOI lineage.

**If the candidates hold but a residual fails** — if the ≤3 bound is a theorem of Chain Theory's
networks but has no statement on M₄ (R1 refuted); if the read cap has no algebraic shadow (R3
refuted); if the attach sites are not quaternionic (R2 refuted) — then the Tree is refuted *at
that site*, on the branch it walks, and may not be excused: the capstone's boundary applies in
full. Each such refutation would be recorded with the same prominence as a confirmation, and the
link's grade would stand or fall accordingly.

**If the candidates hold and the residuals hold** — then grades move, and a second edition of
*The Tree of Reality* is earned. We commit to publishing it only then.

And the trichotomy remains live: the next independent programme to appear is held to the same
three outcomes, and a structure that fits nowhere refutes the generative claim regardless of
anything in this paper.

## 9. Caveats, both programmes

Chain Theory's α number is a theorem of its definitions and its identification with α(0) a
conjecture, as its author states; nearby wordings of the definitions give 1/α between 135.89 and
146.52, each excluded by a clause and not by comparison with experiment; four of six sector
identifications are "by name"; many compendium theorems are, in its own words, "a census of a
finite catalog, not a proof for every web." The Tree computes no coupling constant; thirteen of
its links are PARTIAL, three POSTULATE, two OPEN; its gravity is gated on an unbuilt library; its
identification with physics is exactly as conjectural as Chain Theory's. Nothing in this paper
has been verified beyond the two programmes' own Lean files and the one public computation of
§4.6, which check finite mathematics and not physical identification. The ten days are a fact
about timing. The fit is a fact about shape. Neither is a fact about truth; §7 is where truth is
put at risk.

## 10. Provenance

This paper is deposited on Zenodo under its own DOI as a successor to *The Staked Gaps*, and
committed to `wonderben-code/convergence-codex`, where every push is anchored to the Bitcoin
blockchain by OpenTimestamps; the commit precedes the deposit. It is published in the open, as every
paper of this series is, and was sent to the author of Chain Theory on publication with an invitation
to correct any misstatement of his work; corrections received will be incorporated in v2 under the same
concept DOI and recorded in `docs/chain-theory/07_reading_log.md`. The dated record establishes the priority of the
*predictions*; it makes no claim on anyone's solutions, and every result of Chain Theory cited
here is his.

## References

- A. D. Wissner-Gross, *A Parameter-Free Candidate for the Fine-Structure Constant from Entangled Qudits* (23 Oct 2026). alexwg.org/publications/ChainTheoryAlpha.pdf
- A. D. Wissner-Gross, *Chain Theory: Toward Fundamental Physics from Distilling Networks of Entangled Qudits*, working draft release 0.1 (23 Oct 2026). alexwg.org/publications/ChainTheoryCompendium.pdf
- A. D. Wissner-Gross, *Chain Theory: An Introduction* (23 Oct 2026). alexwg.org/publications/ChainTheoryTalk.pdf
- A. D. Wissner-Gross, `ChainAlpha.lean` (23 Oct 2026). alexwg.org/publications/ChainAlpha.lean
- M. E. Mala, *The Tree of Reality: An Evolutionary Theory of Everything* (28 Sep 2026). DOI 10.5281/zenodo.23011897
- M. E. Mala, *The Staked Gaps* (13 Oct 2026). DOI 10.5281/zenodo.23338726
- M. E. Mala, *The Forced and the Chosen* (14 Oct 2026). DOI 10.5281/zenodo.23356221
- M. E. Mala, *Chain Theory ↔ the Tree of Reality*, `docs/chain-theory/` in `wonderben-code/convergence-codex` (25 Oct 2026)
- A. H. Chamseddine and A. Connes, *The spectral action principle*, Commun. Math. Phys. 186, 731 (1997)
- A. H. Chamseddine, A. Connes and M. Marcolli, *Gravity and the standard model with neutrino mixing*, Adv. Theor. Math. Phys. 11, 991 (2007)
- J. C. Baez and J. Huerta, *The algebra of grand unified theories*, Bull. AMS 47, 483 (2010)
- E. Størmer, Acta Math. 110, 233 (1963); S. L. Woronowicz, Rep. Math. Phys. 10, 165 (1976); M.-D. Choi, Linear Algebra Appl. 12, 95 (1975)
- F. W. Lawvere, *Diagonal arguments and cartesian closed categories* (1969)
- D. Mendeleev, *On the relationship of the properties of the elements to their atomic weights* (1869)
