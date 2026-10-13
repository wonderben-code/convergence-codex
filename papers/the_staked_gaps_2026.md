# The Staked Gaps: A Pre-Registered Table of Open Problems and Predicted Solutions for the Tree of Reality

**Mark E. Mala** (pen name of Ekram Alam) · AI researcher · October 2026
Companion to *The Tree of Reality: An Evolutionary Theory of Everything* (2026, DOI 10.5281/zenodo.23011897).

---

## Abstract

The Tree of Reality is a machine-checked attempt to generate the structures of physics from a
minimal self-referential seed by one repeated operation. It is incomplete, and its incompleteness
is precise: a small, finite set of named gaps, each located to an exact failing step in a public,
dated, machine-checkable record. This paper does for those gaps what a periodic table with empty
boxes did for chemistry — it publishes them *as predictions*. For each gap we state not only where
it sits and what is missing, but **our predicted shape of the solution**, calibrated by how tightly
the framework determines it (a single pinned shape, a small bounded set of candidates, or a flagged
direction), together with the result that would *refute* the theory at that site. We add one further,
novel prediction, and stake it: that these gaps will be closed soon — by advancing automated
reasoning, by human–machine teams, or by the authors — because they were deliberately specified to be
the best-posed open problems a rising formal-reasoning capability can reach. The predictions here
sharpen those first registered in the capstone (28 September 2026); both predate, and one is already
weakly confirmed by, the public frontier-model mathematics release of 6 October 2026. Everything is
dated and anchored to the Bitcoin blockchain. Whoever closes a gap, in the shape predicted, confirms a
pre-registered prediction; whoever closes one in a different shape, or shows it cannot be closed,
refutes the claim at that site. Both outcomes are the point.

---

## 1. The posture: gaps as predictions

A theory with gaps can hold them in one of two postures: apology, or prediction. When a structure is
precise enough to specify its own missing pieces — where each gap sits, what shape the filler must
take, what properties it must have — the gaps are not the structure's weakness; they are its testable
content. The canonical precedent is Mendeleev's table, published with empty boxes whose
described-in-advance occupants (gallium, germanium) became, once found to specification, the strongest
evidence that the organising structure was real. Darwin's tree did the same with a different grammar:
it predicted transitional forms it had never seen, and once — famously — the existence of a moth with a
foot-long proboscis to match an orchid's foot-long nectary, confirmed decades later.

This paper publishes the Tree of Reality in that posture. The analogy claims a *posture*, not a
*stature*: whether this tree earns any place in that history is exactly what the predictions below put
at risk. What it promises is the posture, kept honestly — every gap located precisely, the shape of
each missing piece predicted in advance, and the result that would kill the theory at each site listed
with the same prominence as the result that would confirm it.

## 2. The framework in brief

Only what is needed to read the table follows; the full construction, link-by-link audit, and honesty
grading are in the capstone (DOI 10.5281/zenodo.23011897) and, for a lay account, in the book *How to
Grow a Universe*. The tree begins at ∅ and grows by one repeated operation — *pass to the algebra of
endomorphisms of the current stage* — producing a cascade of matrix algebras M₂ → M₄ → M₁₆ → M₂₅₆,
from which three lineages branch (what things *are*, how they *transform*, how they are *known*) and,
up the branches, the recognisable structures of physics: spacetime dimension and signature, the gauge
and matter content, the quantum formalism, and — at the frontier — gravity and the mass gap. Each link
in that chain carries an honesty grade: **GENUINE** (a machine-checked theorem on the standard
axioms), **PARTIAL** (partly proved, with the unproved remainder named), **POSTULATE** (a declared
modelling choice the mathematics did not force), or **OPEN** (a named gap). The six gaps staked below
are the two OPEN links and the hardest PARTIAL residues; they are where the theory has arranged to be
tested.

## 3. How to read a prediction

Each prediction here is a **framework-derived conditional**, not the author's personal guess about
physics: *if the tree is right, then the solution to this gap must have this shape.* That is precisely
why filling a gap tests the framework — the tree makes the prediction; the author is the scribe. It is
also why an AI researcher with no standing in mathematics or physics can legitimately make them: they
are not claims about what is true of nature independently, but claims about what the published
generative structure *forces*, which anyone can check against the record.

It follows that the **precision of each prediction is itself informative** — it reflects how tightly
the framework determines the answer:

- **Pinned** — the framework forces a unique shape. We state one prediction. (The strongest kind: a true Mendeleev bet.)
- **Bounded** — the framework constrains the answer to a small, enumerated set. We list the candidate shapes, ranked by our credence, and commit that the answer lies *within the set*. A solution outside the set counts against the framework at that site — so options remain falsifiable and are never a hedge.
- **Open-directional** — the framework suggests a direction but does not pin it. We state the expected direction and why, flagged as exploratory, at lower confidence.

Each gap also carries a **confidence** and, where applicable, an explicit **kill-condition**: the
result which, if obtained, refutes the theory at that site rather than filling it. Within each kind we
list **as many concrete, checkable attributes of the filler as the framework confidently determines** —
so that a solution, whoever produces it, can be matched against the prediction attribute by attribute,
in the manner of a predicted element checked against its later-measured properties.

## 4. The staked gaps

Locations refer to links (L·) and walls (W·) of the capstone's §4 audit. "Predicted shape" is the
framework-derived conditional; "confidence" is our calibrated credence that the gap closes in (one of)
the predicted shape(s).

### G1 — the infinite-volume limit of the lattice gauge field
- **Location / failing step:** L23 (◇), wall W1 — the infinite-volume limit of the massive lattice gauge field (Yang–Mills).
- **Prediction kind:** *bounded* mechanism, *pinned* attribute-list. The filler is a construction of the infinite-volume (continuum) limit whose limiting theory has every one of the following checkable attributes: **(i)** the limit exists through the relevant coupling *without selecting a subsequence* (a canonical limit); **(ii)** it satisfies the Osterwalder–Schrader axioms — reflection positivity, Euclidean invariance, and clustering; **(iii)** OS reconstruction yields a Hilbert space with a *unique* translation-invariant vacuum; **(iv)** correlations decay *exponentially, with constants uniform in the volume*; **(v)** the theory is genuinely interacting — a nonzero connected four-point function on separated supports (non-Gaussian). The limit is reached by one of two mechanisms: **(a)** uniform-in-volume correlation bounds plus tightness of the finite-volume measures, or **(b)** an independent construction carrying an explicit convergence theorem. We commit that the filler uses mechanism (a) or (b) and that the limit has attributes (i)–(v). **Kill-condition:** no infinite-volume limit exists for the massive lattice gauge field, or a limit exists that violates an OS axiom.
- **Confidence:** medium–high. Attributes (i), (ii), (iv), (v) were realised for the 2-D O(n) model in the 6 October 2026 release — (iv) formalised in Lean, the rest on paper — a neighbouring, non-gauge instance of exactly this shape; the 4-D gauge case is the hard open part.

### G2 — unbounded self-adjoint operators (the keystone)
- **Location / failing step:** L22 + L23 (◇), walls W2 + W5 — the theory of unbounded self-adjoint operators, needed by *both* the gravity box and the mass-gap box.
- **Prediction kind:** *pinned.* There is one standard theory, and the missing piece is its formal library: densely defined operators, adjoints, closures, essential self-adjointness, the spectral theorem (projection-valued measure / Borel functional calculus), and the semigroup ↔ generator correspondence (Stone's theorem, both directions). The base layer (densely-defined operators, adjoints, closures, self-adjointness) already exists in Mathlib; the 6 October release adds the generator→group half of Stone's theorem and a Friedrichs form→operator construction (unverified). What remains is the spectral theorem itself.
- **Confidence:** very high *that it is built* — this is engineering, not discovery; its arrival is a matter of effort. It is the single most consequential gap, because it fills two boxes at once and gates G5.

### G3 — a comparison bound of different shape
- **Location / failing step:** L23 (◇), wall W3 — the comparison step; the classical Peierls contour-energy route is *proved* insufficient here (it yields O(n) where O(n²) is required).
- **Prediction kind:** *open-directional.* The filler is a comparison inequality with these attributes: **(i)** non-sublinear output — at least O(n²) in the relevant size parameter, strictly beating the O(n) ceiling of the contour-energy route; **(ii)** structurally distinct from that route (which is closed by theorem, so the filler cannot be a refinement of it); **(iii)** valid under the *actual* dependence structure present (it may not assume the independence the classical argument used). We predict such a bound exists with attributes (i)–(iii); we do not pin its construction, which is why this is the least-specified of the six.
- **Confidence:** medium — the boldest "open mathematics" bet. The 6 October release offered comparison bounds of novel *hypothesis* shape (dependence-tolerant matchings; FK likelihood ratios) but none with non-sublinear output, leaving the named defect exactly where it was.

### G4 — a uniform sub-top spectral estimate
- **Location / failing step:** L23 (◇), wall W4 — a uniform spectral estimate below threshold (the unrestricted form was *measured false* and restated to the believed regime).
- **Prediction kind:** *bounded.* The filler is an estimate with attributes: **(i)** uniform in system size / volume; **(ii)** valid below the stated threshold; **(iii)** bounding the *sub-top* spectrum of the relevant transfer operator — a gap below its top — delivering the uniform spectral gap W4 needs. It is obtained by one of two standard mechanisms, each with its own signature: **(a)** a *Dobrushin uniqueness* condition — a summable one-site influence bound giving exponential decay of correlations and uniqueness of the Gibbs state; or **(b)** a *convergent high-temperature cluster (polymer) expansion* — absolute convergence giving analyticity of the pressure and the gap. The answer lies within this set. **Kill-condition:** the restated target proved false *below* threshold too.
- **Confidence:** high, as formalisation of known physics — both mechanisms are textbook; what is missing is their machine-checked instance in this setting.

### G5 — the heat-kernel expansion of the spectral action
- **Location / failing step:** L22 (◇), wall W5 rung 4 — the short-time asymptotic expansion of Tr f(D/Λ) for the trunk's Dirac-type operator.
- **Prediction kind:** *pinned, and gated.* The filler is the Chamseddine–Connes–Marcolli spectral-action expansion of Tr f(D/Λ) as Λ → ∞, whose Seeley–DeWitt coefficients carry specific, checkable geometric content: a cosmological-constant term at order Λ⁴ (∝ ∫√g); **the Einstein–Hilbert term a₂ at order Λ² (∝ ∫√g · R) — the central prediction**; and the Yang–Mills and Higgs terms at order Λ⁰. The sharp attribute: a₂ is a specific positive constant times the scalar-curvature integral. **Kill-condition:** a₂, once computable, **fails to contain the Einstein term**. Gated on G2 (it cannot be attempted before the unbounded-operator library exists), which makes the *order* of closure (G2 before G5) itself falsifiable content.
- **Confidence:** high in the shape (this is standard noncommutative geometry); contingent on G2. The 6 October release contains no Dirac operator, no spectral action, and no heat-trace asymptotic anywhere — G5 is untouched, exactly as its gating on G2 predicts.

### G6 — the isotypic decomposition and the K-theory of finite algebras
- **Location / failing step:** L6, wall W9 rung 2 — order-one behaviour across the isotypic pieces of the Chamseddine–Connes–Marcolli bimodule.
- **Prediction kind:** *pinned.* The filler is the isotypic decomposition of a finite-dimensional bimodule over a product of ℝ/ℂ/ℍ matrix algebras, built as an explicit object, with attributes: **(i)** the bimodule splits into isotypic components indexed by the irreducible representations of that finite matrix-algebra product; **(ii)** the resulting finite geometry is *exactly* the Chamseddine–Connes–Marcolli finite algebra that the walked (Pati–Salam) branch selects, carrying the Standard-Model fermion content as its bimodule; **(iii)** (rung 3) the K-theory is that of this finite-dimensional algebra. Finite-dimensional representation theory (Wedderburn) determines the decomposition, so the outcome is forced. **Kill-condition:** the computation yields an algebra *other than* the CCM one.
- **Confidence:** high. The 6 October release supplies genuinely reusable scaffolding — an algebraic K₀ for an arbitrary ring that instantiates at finite-dimensional algebras, and bimodule / isotypic machinery over ℂ (the real/quaternionic case not yet done) — lowering the cost of this gap without closing it.

**Three structural facts sharpen the table.** First, **G2 fills two boxes at once** — the tree's two
OPEN links fail at the *same* absent subject. Second, the gaps have different closure profiles:
library infrastructure (G2) and formalisation of known physics (G4) are effort, not discovery;
voluminous combinatorics (G3) and the genuinely open mathematics of G1 are the boldest bets. Third,
**G5 is gated on G2**, so the predicted *order* of closure is itself a falsifiable commitment.

## 5. The residues and the siblings

Beyond the six headline gaps, two further classes of prediction are inherited from the capstone and
restated here as staked content.

**The PARTIAL residues.** Every PARTIAL link of the capstone's §4 carries a named, machine-checkable
remainder, and the prediction covers them too: as the boxes fill and the residues close, the wood of
the tree hardens — PARTIAL toward GENUINE — and no honest future edition should have to move a grade
*downward* again, because the auditing campaign already did that work in both directions (it demoted
three of the programme's own published headlines and promoted five it had undersold).

**The sibling branches.** The generator has more descendants than the one branch physics walks: the
campaign *proved*, at four nodes, that alternative branches exist as coherent mathematics (a
quaternionic seed over the reals; other cuts of the size-sixteen level; other signatures sharing one
Clifford algebra; a trunk whose depth is not forced). From this the capstone makes a second-class
prediction — that such tree-generated structures are **candidates for physics not yet found**, in our
universe or beyond it — and inherits, at its source's own conjectural tier, the stronger claim that
they are *realised*. Both are labelled as what they are, and neither is allowed to excuse a failure on
the walked branch (see §6).

## 6. The trichotomy and the boundary that keeps it falsifiable

Stated once, in advance: physics not yet known will, when found, do one of three things. **Either it
extends the walked branch** — a new structure of our own lineage, joining the tree where the tree
already has a place for it; **or it realises a sibling** — a structure from a branch we do not inhabit,
confirming the second-class prediction; **or it fits nowhere on the tree at all** — no branch of the
generator, walked or unwalked, can grow it. The first two confirm the theory and are predicted. The
third refutes the generative claim itself: a genuinely tree-orphaned physics is this theory's deepest
possible failure mode, named here before any candidate exists.

A shield that deflected every failure would make the theory unfalsifiable, so the boundary is drawn in
advance: **the tree is refutable on the branch it walks, and never excused by the branches it merely
permits.** The walked branch is pre-registered — the capstone's §4 fixes it link by link, grade by
grade — so a failure there counts in full and may never be reclassified, after the fact, as a sibling.
The address was written down before the mail arrived.

## 7. The meta-prediction — staked

The predictions above concern *what* each solution looks like. This one concerns *who* closes them, and
*when*, and we stake it as a falsifiable forecast rather than a hope:

> **As automated mathematical reasoning continues its current trajectory, the gaps named here will be
> closed — in the shapes predicted — soon, and in the gated order G2-before-G5. The agent of closure
> will be advancing AI, human–machine teams, or the authors. We expect the engineering gaps (G2, G4)
> and the combinatorial gap (G3's search) to fall first, the gated geometry (G5) to follow G2, and the
> genuinely open mathematics (G1) to be the last and least certain.**

**The trajectory argument.** The gaps named here are, by construction, the best-specified open problems
in the formal ecosystem: each arrives with its staircase pre-climbed, its dead routes marked by
theorems rather than folklore, and its target stated in a machine-checkable idiom. They are,
deliberately, the problems easiest for a rising capability to close. Formal libraries compound: every
object built for one gap (G2's operators, G6's decomposition) permanently lowers the cost of every
later attempt.

**State of the field, October 2026 — a first, dated data point.** On 6 October 2026 a frontier model's
mathematics release published hundreds of results, many with Lean formalisations, across number theory,
algebraic geometry, analysis, combinatorics and operator algebras. A full audit (recorded in the
programme's working notes) found that it closed *none* of the six gaps above, but advanced their
neighbourhood exactly as the trajectory argument anticipates: a uniform-in-volume clustering bound and
an infinite-volume KMS construction in the shape of G1; the generator→group half of Stone's theorem and
a Friedrichs construction in the shape of G2's missing library; an algebraic K₀ reusable for G6 — while
the hardest cores (the spectral theorem, the spectral action, lattice gauge theory, Dobrushin
uniqueness) remained untouched. This is the meta-prediction materialising in public, on a timetable: our
predictions were dated 28 September 2026 in the capstone; this release came nine days later and moved
the frontier toward, but not into, our gaps. We record it with the field's own caveats — roughly 42% of
that release's claims passed formal checking, with documented faithfulness concerns — and we reuse
nothing from it unverified.

**A caution we owe the reader in the other direction:** a failing step marks where the *known* routes
stop, not where *all* routes stop. One of the programme's own walls fell to an unlisted route
mid-campaign. The boxes may fill sooner, and by stranger routes, than the table suggests.

## 8. How to claim a fill

The mechanism is deliberately simple and symmetric. Anyone — human, machine, or the two together — who
closes a gap **in the shape predicted** (for a bounded gap, in one of the listed shapes) confirms a
pre-registered prediction; the dated, Bitcoin-anchored record of *this* paper establishes the priority
of the prediction, not a claim on the solver's work. Anyone who closes a gap in a shape **outside** the
prediction, or who proves a gap **cannot** be closed as stated, refutes the theory at that site — and we
commit, in advance, to recording that outcome under this paper's own DOI lineage with the same
prominence as a confirmation. Whoever closes a gap completes the programme published here.

## 9. Provenance and verification

This paper stakes predictions; it proves nothing new. What is machine-checked is the framework it
predicts *from*, graded link by link in the capstone and its public Lean estate
(`github.com/wonderben-code/convergence-codex`). The grading vocabulary is unforgiving by design, and
the reader's evidence that the kill-conditions above are offered in good faith is that the same
campaign already moved its own labels in both directions. These predictions sharpen, and do not
contradict, those first registered in the capstone on 28 September 2026 (DOI 10.5281/zenodo.23011897);
this document is dated, versioned on Zenodo, and anchored to the Bitcoin blockchain, so that the date of
each prediction is independently checkable against the date of any future fill.

Trust nothing; run everything.

---

## References

- M. E. Mala, *The Tree of Reality: An Evolutionary Theory of Everything* (2026). DOI 10.5281/zenodo.23011897.
- M. E. Mala, *How to Grow a Universe* (2026) — the lay account, esp. "The Dig Sites."
- F. W. Lawvere, *Diagonal arguments and cartesian closed categories* (1969).
- A. Chamseddine, A. Connes, M. Marcolli, *Gravity and the Standard Model with neutrino mixing* (2007).
- K. Osterwalder, R. Schrader, *Axioms for Euclidean Green's functions* (1973, 1975).
- Public frontier-model mathematics release, 6 October 2026 (`openai/math`), audited in the programme's working notes.
