# Proposed tag changes — 26 rulings

*Snapshot of 26 September 2026, taken at the stand-down after hardening unit 243. The source register
is `formalisation/PROPOSED_TAG_CHANGES.md` in `wonderben-code/codex-internal`, branch
`claude/infinitography-formalisation-fbqxf3`, commit `2bc86f1`. It was last re-checked against the
estate at unit 243.*

## How to use this

Each ruling is a published tag, or a published sentence, that says more (or, in three cases, less)
than the Lean proves. For each one you get:
- where it is;
- what the tag is now and what is proposed;
- **my recommendation**;
- why, in a few sentences.

Rule each one **yes** or **no**.

**Nothing has been changed.** No published tag, paper, tree or website has been edited. Every item is
a proposal, and every ruling is yours.

The source register holds 32 items: rows 1–31, plus a prose entry that reuses the number 9 (*entry 9,
Root Equation*, `ERRATUM 669`). Those 32 become **26 rulings** here:
- rows 4 and 26 are one ruling, because they are the same claim in several places;
- rows 14 and 24 are one ruling;
- rows 20 and 25 are one ruling;
- rows 7, 8 and 11 need no ruling, and are listed at the end with the reason.

The recommendation vocabulary is the published one: **PROVED**, **PARTIAL**, **CLAIMED**,
**[PREDICTED]** and **META, OPEN**, with ★ marking a flagship claim. "Assumptions entry *n*" means
`ASSUMPTIONS_LEDGER.md` beside this file.

| # | ruling | recommendation |
|---|---|---|
| T1 | Chamseddine–Connes classification ★ PROVED → PARTIAL | yes |
| T2 | "Cl₄ = M₄ forces 4D" PROVED → PARTIAL | yes |
| T3 | "(4,2,2) unique": split, isomorphism PROVED, uniqueness PARTIAL | yes |
| T4 | Weinberg angle "from finrank" ★ → PARTIAL; add a PROVED trace-ratio row | yes |
| T5 | "Parameter count 19 → 3": split, Γ/exp PROVED, parameter claim CLAIMED | yes |
| T6 | `SpectralActionMeasure` ★: keep, with a scope note | yes |
| T7 | `EmergenceLineage` PARTIAL → PROVED (an upgrade) | yes |
| T8 | "only the dimension match is in Lean" (SL₂(ℂ) ≅ Spin(3,1)): reword | yes |
| T9 | ℂ ⊕ ℍ ⊕ M₃(ℂ) at the M₂₅₆ level ★ PROVED → META, OPEN | yes |
| T10 | Gaussian domination (Wick) ★ PROVED → PARTIAL | yes |
| T11 | Bakry–Émery gap = 2/Λ² ★ PROVED → CLAIMED; separate PROVED Poincaré row | yes |
| T12 | "Gaussian integral converges" ★: keep, with a scope note | yes |
| T13 | anomaly cancellation [PREDICTED] → PARTIAL (an upgrade) | yes |
| T14 | Stone's theorem [PREDICTED] → PARTIAL (an upgrade) | yes |
| T15 | GNS reconstruction [CLAIMED] → PROVED for the cascade algebra, scoped | yes, scoped |
| T16 | seed uniqueness [META, OPEN] → PARTIAL (an upgrade) | yes |
| T17 | Lorentzian signature: split, the form PROVED, "forced" unchanged | yes |
| T18 | OS2: keep [PREDICTED], add a footnote naming the theorem | yes |
| T19 | mass-gap chain: keep, add a footnote citing the Ising chain | yes |
| T20 | Higgs mass [CLAIMED] → PARTIAL, with five caveats | yes, with caveats |
| T21 | re-point ~30 files' "SM embeds in su(4)" and "Cl₄ ≅ M₄" prose | yes |
| T22 | "Incompleteness" under `Inexhaustibility`: drop or qualify | yes |
| T23 | "Cantor/Tarski applied to D": say "Cantor" | yes |
| T24 | "Fixed point theorem in cartesian closed categories": name the category | yes |
| T25 | §6.8 "determined by Goldstone counting": qualify | yes |
| T26 | Root Equation §14.6 *Proven* list: restrict the quantifier | yes |

Every recommendation is yes. That is not a rubber stamp. Each proposal has been re-checked against
the estate five times since 20 September, and none has weakened. The register records that no
proposal has been withdrawn, and I have found no reason to withdraw one. Where the honest answer is
narrower than the proposal, the recommendation says so (T15, T20).

---

## The rulings

### T1 · Chamseddine–Connes classification — ★ PROVED → PARTIAL *(row 1)*

**Where.** `papers/tree_of_reality.md` §4.3 evidence table, the `ConnesClassification.lean` row:
*"★ Chamseddine-Connes (2007) classification theorem"*.
**Recommend: YES.**
**Why.** The file assumes the answer's shape. The algebra is taken to be a single `Mₙ(ℂ)`, and
minimality is a hypothesis, after which `n = 4` is a three-case check (assumptions entry 7). The real
theorem classifies sums of matrix algebras over ℝ, ℂ and ℍ and lands on `ℂ ⊕ ℍ ⊕ M₃(ℂ)`, which is
not of that shape; none of that is formalised. A derived route sits beside it (`CCConstraints`,
`classification_min`), but the published row cites the structure with the assumed field. A ★ tag
should not claim a classification the Lean does not contain.

### T2 · "Cl₄ = M₄ forces 4D" — PROVED → PARTIAL *(row 2)*

**Where.** §6.1 evidence table, `F1_7_SpacetimeForced.lean`: *"`Cl₄ = M₄` forces 4D. `n = 2`
excluded"*.
**Recommend: YES.**
**Why.** Both halves of the mathematics are now proved:
- the isomorphism `Cl₄(ℂ) ≅ M₄(ℂ)` (`CliffordIso.cliffordMatrixEquiv`);
- a complex Clifford algebra is `M₄(ℂ)` exactly in dimension 4 (`clifford_iso_M4_iff_finrank_four`).

What is not proved is *forces*. That spacetime is read at the cascade level where `M₄` appears is a
choice (assumptions entry 22).
**Alternative, if you prefer:** keep PROVED and change the words to *"`Cl₄(ℂ) ≅ M₄(ℂ)`, and `M₄(ℂ)`
is a Clifford algebra exactly in dimension 4"*. That sentence is proved as it stands.

### T3 · "(4,2,2) unique; alternatives excluded" — split *(row 3)*

**Where.** §6.4 evidence table, `F1_6_PatiSalamForced.lean`: *"Azumaya iso `M₄ ⊗ M₄ ≅ M₁₆`. `(4,2,2)`
unique. Alternatives excluded"*.
**Proposed.** The isomorphism **PROVED**; the uniqueness **PARTIAL**.
**Recommend: YES.**
**Why.** The isomorphism is genuine. The uniqueness is of a hand-picked system of equations
(assumptions entry 10):
- the 16 fixes the cascade level;
- one constraint is justified by one line of prose;
- the constraint meant to carry left–right symmetry does no work.

The file's header also says the constraints are *"stated as axioms"*, and the file contains no axioms.

### T4 · Weinberg angle — "★ 3/8 from finrank" → PARTIAL, and add the trace-ratio row as PROVED *(rows 4 and 26)*

**Where.** §6.10 evidence table, `F4_1_Foundations.lean`: *"★ Weinberg angle `3/8` from `finrank`"*.
The same claim appears at `papers/tree_of_reality.md:311`, `docs/Tree_of_Reality.md:239` and
`paper_f/README.md:59`.
**Proposed.**
- *"3/8 from the dimensions"* → **PARTIAL**.
- A new row, *"3/8 as the trace ratio `Tr(T₃L²)/Tr(Q²)` on the chiral Pati–Salam 16"* → **PROVED**,
  citing `WeinbergIndex.lean`.
- The step from that ratio to the physical Weinberg angle stays prose.

**Recommend: YES.**
**Why.** The published mechanism is refuted by a theorem: the same construction, with the same
dimensions, gives 3/7 (`WeinbergIndex.weinberg_not_from_dimensions`), so the match with 3/8 is a
coincidence. What is proved is 3/8 as a trace ratio on an actual representation. Since unit 190, the
3/5 beside it is also read from one invariant form. That the ratio *is* the angle at unification
needs a coupling-matching input, which is an author decision (assumptions entry 57). Running to 0.231
is untouched.

### T5 · "Parameter count 19 → 3" — split *(row 5)*

**Where.** §10.1 evidence table, `F3_10a_HeatKernelCanonicity.lean`: *"`Γ(1) = 1`, `exp(0) = 1` from
Mathlib. Parameter count 19 → 3"*.
**Proposed.** The Γ/exp facts **PROVED**; the parameter claim **CLAIMED**.
**Recommend: YES.**
**Why.** The parameter content is the arithmetic `19 − 3 = 16` plus narrative. The estate's own
later theorems say which premises the chain lacks:
- *"All three moments are 1"* is exactly the normalisation `κ = 1` (`DecayingCutoff.moments_eq_one_iff`).
- The tensor-sum shape that makes the cutoff exponential is supplied by order-one only for one full
  matrix algebra at one generation (units 232–243). The published algebra is a product with three
  generations, where this is not settled.
- What the conditions on `D` leave free is a whole matrix on the generations — six real numbers at
  three generations, for self-adjoint `D` (`SelfAdjointDiracCount`) — not the cutoff's three moments.

### T6 · `SpectralActionMeasure` ★ — keep the tag, add a scope note *(row 6)*

**Where.** §10.2 evidence table: *"★ Genuine `Measure.withDensity` construction. Absolute
continuity"*.
**Recommend: YES.**
**Why.** The construction is genuine, but the measure lives on ℝ, with the action's *value* as the
coordinate, not on the 16-dimensional space of Dirac operators. It is also not a probability
measure; the file's own header says so (assumptions entry 26). A genuine Gaussian probability measure
on `Herm₄(ℂ)` now exists (`Herm4Gaussian`), but the density `e^{−S}` is in no declaration.
**Suggested note:** *"on ℝ, not normalised; the spectral-action density on `Herm₄(ℂ)` is not in Lean"*.

### T7 · `EmergenceLineage` — PARTIAL → PROVED *(row 9; an upgrade)*

**Where.** §5 evidence table: *"`EmergenceLineage.lean` | PARTIAL | Doubly-exponential dimension
sequence"*.
**Recommend: YES.**
**Why.** The row claims only the dimension sequence, and that is exactly what is proved: the
recurrence, the closed form `2^(2^n)`, `finrank (End V) = (finrank V)²`, and the values 4, 16 and 256.
The file's own note says *Standard Model*, *category* and *quantum* occur only in its prose, and the
row claims none of them. Here the paper undersells the Lean.

### T8 · "SL₂(ℂ) ≅ Spin(3,1): only the dimension match is in Lean" — reword *(row 10)*

**Where.** `papers/tree_of_reality.md` §16.2 item 7, line 772, tagged [PREDICTED].
**Recommend: YES.**
**Why.** Much more than the dimension match is in Lean:
- the double cover `SL₂(ℂ) → SO⁺(1,3)` — surjective, with kernel exactly `{±1}`
  (`LorentzSurjectivity.double_cover`);
- the Clifford spin group modulo `{±1}`, identified with `SL₂(ℂ)` modulo `{±1}`
  (`SpinSurjective.spinEquivSL2Quot`);
- `SO⁺(1,3)` as the identity component of O(1,3), with no hypothesis (`SL2Connected.identityComponent_eq`).

Two things are not in Lean. `SL₂(ℂ) ≅ Spin(3,1)` as groups is not proved; only the two quotients are
identified. And nothing topological is proved about Spin, which is Mathlib's algebraic spin group
(assumptions entry 42).
**Suggested words:** *"The double cover `SL₂(ℂ) → SO⁺(1,3)` and the identification of the quotients
by `{±1}` are in Lean; `SL₂(ℂ) ≅ Spin(3,1)` as groups, and the topology of Spin, are not."*

### T9 · ℂ ⊕ ℍ ⊕ M₃(ℂ) at the M₂₅₆ level — ★ PROVED → META, OPEN *(row 12)*

**Where.** `docs/TREE_OF_REALITY_STRUCTURE.md:255`: *"Our branch: C ⊕ ℍ ⊕ M₃(ℂ) at the M₂₅₆ level
[PROVED ★]"*.
**Recommend: YES.** The source calls this the largest gap between tag and reality that it found.
**Why.** The `M₂₅₆` level is in Lean, as the cascade's third step, and as an algebra. The Standard
Model's algebra is not placed there by anything:
- no Lean file constructs `ℂ ⊕ ℍ ⊕ M₃(ℂ)` at that level;
- the four files that name it do so to say what they do not prove, or to argue against a route;
- no selection principle picks a depth (assumptions entry 23; running decision list, item 1).

The paper's own §4.4 already says META, OPEN; this brings the spec document into line with it.

### T10 · Gaussian domination (Wick) — ★ PROVED → PARTIAL *(row 13)*

**Where.** `docs/TREE_OF_REALITY_STRUCTURE.md:493`.
**Recommend: YES.**
**Why.** Wick's theorem is proved at every order, for the Gaussian field on a finite box
(`IsserlisAll.isserlisGeneral_all`), and Gaussian moments are bounded. Domination of the physical
measure `e^{−S}` is not proved, because that measure is in no declaration.

### T11 · Bakry–Émery gap = 2/Λ² — ★ PROVED → CLAIMED, and a separate PROVED row for the Gaussian Poincaré inequality *(rows 14 and 24)*

**Where.** `docs/TREE_OF_REALITY_STRUCTURE.md:494`, and the paper's §11.4.
**Recommend: YES.**
**Why.** In `BakryEmeryGap.lean` the gap is a *definition*, and the criterion is discharged by
`le_refl`. A genuine Poincaré inequality with the constant `Λ²/2` is proved for a Gaussian — in every
dimension, at every variance, beyond polynomials — and deserves its own **PROVED** row. But the
`2/Λ²` claim is about the spectral-action measure, which does not exist in Lean (assumptions entries
8 and 27). Keep the two rows separate, so the true one does not lend its tag to the other.

### T12 · "Gaussian integral converges" ★ — keep, with a scope note *(row 15)*

**Where.** `docs/TREE_OF_REALITY_STRUCTURE.md:492`.
**Recommend: YES** — keep PROVED ★ with the note. Without the note, PARTIAL.
**Why.** The old worry, one dimension only, is gone. The Gaussian is in Lean in `n` dimensions and
on the 16-dimensional Hermitian slice, with its value computed. The note should now say *"the
Gaussian, not `e^{−S}`"*.

### T13 · Anomaly cancellation — [PREDICTED] → PARTIAL *(row 16; an upgrade)*

**Where.** `papers/tree_of_reality.md` §6.9.
**Recommend: YES.**
**Why.** The anomaly coefficients are computed from representation traces (`AnomalyTraces`). Since
14 September the cubic form is evaluated on the actual representation on the chiral 16
(`SU4OnSixteen`), so the equal-multiplicity input is no longer written into the statement. Two
things are still cited rather than proved: that the anomaly *is* the cubic trace (the ABJ result),
and Witten's global anomaly, since Mathlib has no homotopy groups. So PARTIAL, not PROVED.

### T14 · Stone's theorem — [PREDICTED] → PARTIAL *(row 17; an upgrade)*

**Where.** §8.1, and §16.2 item 9.
**Recommend: YES.**
**Why.** Both directions are proved for bounded generators. Generator to group, and the converse: a
unitary group continuous at a single point has a unique self-adjoint generator, in any C⋆-algebra
(`StoneConverseLocal`), instantiated on the cascade's own carriers. Not proved: unbounded generators
on infinite-dimensional spaces, which is what physics uses (assumptions entry 32). So PARTIAL, not
PROVED.

### T15 · GNS reconstruction — [CLAIMED] → PROVED for the cascade algebra, scoped *(row 18)*

**Where.** §16.2 item 5.
**Recommend: YES, but only with the scope written into the row.**
**Why.** `CascadeGNS` carries out the GNS construction for the cascade's algebra: positivity derived,
a unit vacuum vector, state recovery, cyclicity, faithfulness and definiteness. Two limits belong in
the row:
- the input state is the trace state, which is chosen, and the headline results fail for a pure state
  (assumptions entry 16);
- the non-unital case is not proved.

**Suggested words:** *"PROVED for the cascade algebra with the trace state"*.

### T16 · Seed uniqueness — [META, OPEN] → PARTIAL *(row 19; an upgrade)*

**Where.** §3.
**Recommend: YES.**
**Why.** `SeedUniqueness` proves that `M₂(ℂ)` is the unique minimal non-commutative seed, over ℂ and
for associative algebras. Those two restrictions are inputs, and over ℝ the uniqueness is false,
because ℍ also qualifies (assumptions entry 3). The C⋆ input has been narrowed to one named
hypothesis, a faithful ⋆-representation (assumptions entry 4).
**Suggested words:** *"PARTIAL — resolved over ℂ under stated modelling"*.

### T17 · Lorentzian signature — split the row *(rows 20 and 25)*

**Where.** §6.2 and §7.1 (*"signature (1,3)"*), and the stage-1 description in §16.2 item 7.
**Proposed.**
- (a) *"The determinant form on `Herm₂(ℂ)` has signature (1,3), basis-independently, and is not the
  Euclidean form"* → **PROVED**.
- (b) *"`Herm₂(ℂ)` with the determinant form is forced by the cascade"* → unchanged; not derived.

**Recommend: YES.**
**Why.** (a) is proved through Mathlib's basis-independent signature (`MinkowskiSignature`), and every
"remaining stair" the register once listed has since been climbed. (b) is a choice. Every route in
the estate selects (1,3) by a choice, and the route through the seed's ⋆-structure provably never
gives (1,3) (assumptions entry 6; running decision list, item 26).

### T18 · OS2 (reflection positivity) — keep [PREDICTED], add a footnote *(row 21)*

**Where.** §11.6.
**Recommend: YES.**
**Why.** Reflection positivity is proved at the level of measures, for a Gaussian field with the
product covariance, in every dimension (`OS2MeasureLevel.os2_measure_level`). A nonzero mass is shown
to be necessary. The paper's OS2 is about an interacting continuum theory, which is not in Lean
(walls W1 and W2). The footnote should name the theorem and say that this is what it covers.

### T19 · Mass-gap chain — keep the tags, add a footnote *(row 22)*

**Where.** §11.6.
**Recommend: YES.**
**Why.** `TransferGap` derives a gap from the computed spectrum of an operator written down by hand.
The estate also has a derived one: the one-dimensional Ising chain's transfer matrix, with its whole
spectrum and its gap computed (`IsingTransferMatrix`). Neither is the cascade's dynamics (wall W4).
The footnote should cite the Ising chain and say it is one-dimensional, in zero field.

### T20 · Higgs mass attachment — [CLAIMED] → PARTIAL, with its caveats *(row 23)*

**Where.** §6.8.
**Recommend: YES, with the caveats in the row.**
**Why.** The Chamseddine–Connes boundary coupling is bracketed on both sides, `g²/N ≤ λ̃ ≤ g²`, with
both constants sharp. Their own values, `g²/3` and `g²/4`, are theorems inside the window. The row
must carry five caveats:
1. `N = 96` is a modelling choice (assumptions entry 1).
2. Sharpness uses every complex texture, not physical ones (entry 14).
3. `λ = 4λ̃` and `m_H² = 2λv²` are cited, not derived (entry 13).
4. `g` is `g₃` at unification, and Chamseddine and Connes themselves say the couplings do not meet
   exactly (entry 13). **The register's row never carried this one**; the assumptions ledger's
   priority list flags the omission.
5. Running to 125 GeV is out of reach.

### T21 · Re-point the "SM embeds in su(4)" and "Cl₄ ≅ M₄" prose in about 30 files *(row 27)*

**Where.** Estate files, not the paper: `LieAlgebraEmbedding`'s closing docstring, `CascadeFoundation`,
`ConnesClassification.leptoquark_count`, `F1_6` Part 8, `F3_9g`, `F4_3a/b/e`, `F4_4g`,
`CascadeUniqueness`, and the `F1_7` citations.
**Recommend: YES.** This is prose, not a tag. It is also running decision list items 18 and 19.
**Why.** The assembly into `su(4)` is refuted (`SMEmbeddingHonest`). What does embed is colour ⊕ B−L,
and the Standard Model algebra embeds injectively in the Pati–Salam algebra (`SMInPatiSalam`).
*"`Cl₄(ℂ) ≅ M₄(ℂ)`"* should cite `CliffordIso.cliffordMatrixEquiv`, which `F1_7_SpacetimeForced`
still does not name. Every downstream theorem survives.

### T22 · "Incompleteness" under `Inexhaustibility` — drop or qualify *(row 28)*

**Where.** `docs/Tree_of_Reality.md:52`: *"`Inexhaustibility.lean` | PROVED | No surjection
D→(D→Prop). Incompleteness."*
**Recommend: YES** — keep PROVED for the first sentence, and drop or qualify *Incompleteness*.
**Why.** The first sentence is Cantor's theorem, and it is proved. No statement anywhere in the estate
contains a formal system, a provability predicate or a machine.

### T23 · "Cantor/Tarski applied to D" — say "Cantor applied to D" *(row 29)*

**Where.** `docs/TREE_OF_REALITY_STRUCTURE.md:245` [PROVED].
**Recommend: YES.**
**Why.** The Cantor half is proved. The "Tarski" half is the liar contradiction as one line of
propositional logic, with no language and no truth predicate for sentences. Either say *"Cantor
applied to D"*, or tag the Tarski half on its own.

### T24 · "Fixed point theorem in cartesian closed categories" — name the category *(row 30)*

**Where.** `papers/tree_of_reality.md:75` and `docs/Tree_of_Reality.md:31` (`LawvereFixedPoint.lean`,
PROVED).
**Recommend: YES.**
**Why.** It is proved in one cartesian closed category, `Type`. There, at the Root Equation's own `D`,
its hypothesis forces `D` to have one point. The non-degenerate case is proved in ω-CPOs
(`DInfForces.lawvere_domainReflexive`). The row should name the category and cite `DInfForces` for
the non-degenerate case.

### T25 · §6.8 "determined by Goldstone counting" — qualify *(row 31)*

**Where.** Untagged prose at `papers/tree_of_reality.md:280`, `docs/Tree_of_Reality.md:209` and
`docs/Tree_of_Reality.html:508`.
**Recommend: YES.**
**Why.** The counting is now a theorem. The number of broken generators decides the unbroken group,
at the first stage and for pairs of vacua at every rank-one first vacuum (units 213, 225 and 227).
The evidence row's *9 + 3 = 12* is a theorem at the chosen pair. Two qualifications:
- the count decides the group of a *given* vacuum; it does not choose the vacuum, which is a
  postulate (assumptions entry 60);
- *Goldstone* names a theorem about massless modes, which needs a potential the estate does not have.

**Suggested words:** *"…is determined, once the vacua are given, by counting broken generators"*.

### T26 · The Root Equation's *Proven* list — restrict the quantifier *(entry 9, Root Equation)*

**Where.** `The_Root_Equation.md` §14.1 and §14.6. That paper is not in these two repositories; the
register cites its sections.
**Recommend: YES.** This is also running decision list item 13.
**Why.** The listed claim says the construction *"in any symmetric monoidal closed category with
coproducts … produces a reflexive object `D∞ ≅ [D∞, D∞]`"*. Set is such a category, and in Set only
one-point objects satisfy `D ≅ [D, D]` (`ReflexiveDomainObstruction.isSetReflexive_iff`). The
construction is right where it applies: a non-trivial ω-CPO with `D ≃ (D →𝒄 D)` is built
(`CanonicalTower.dInfExists_holds`).
**Suggested fix:** restate it for O-categories, or for CPOs with embedding–projection pairs. That
version is true and provable from what the estate already has.

---

## Items that need no ruling

- **Row 7** (§6.5, `F2_3_ChiralityForced`). Discharged on 29 July.
- **Row 8** (the KO-dimension contradiction between `ConnesNCG` and `ConnesClassification`). This is
  not a tag. It is now a theorem that the two sign conventions cannot both hold, and choosing the real
  structure is assumptions entry 48, an author decision.
- **Row 11** (§3, `SeedForced`, PARTIAL). The tag is correct. It is listed for completeness only.

## Three tag questions with no proposal

These are on the author's running decision list. The register points at them, and none is a proposal.
I give my lean, clearly marked as mine.

- **Item 6 — does L2's tag change now that the reflexive domain is inhabited?** The hypothesis is
  inhabited (`CanonicalTower.dInfExists_holds`). The consequences are still derived *from* the
  hypothesis, not *through* the witness. *My lean:* do not move the tag until the chain is re-derived
  through the witness. A note that the hypothesis is inhabited is accurate now.
- **Item 7 — does anything move on general-order Isserlis (Wick's theorem at every order)?** *My
  lean:* nothing beyond T10, which already uses it as evidence. Isserlis covers a Gaussian, not the
  physical measure.
- **Item 24 — does wall W5's published tag move on the algebraic Lovelock classification?** *My
  lean:* no. The result is about equivariant maps on curvature tensors, not the differential-geometric
  theorem.

## Errata found while writing this digest

- **The register's 20 September re-check, row 10, says *"Still stands: `ASSUMPTIONS_LEDGER` 41
  (`SO⁺(1,3)` is defined algebraically, not as the identity component)"*. That is wrong.** The
  assumptions ledger records entry 41 as *retired by proof* on 15 August (`ERRATUM 189`), and the
  theorem exists and is unconditional: `SL2Connected.identityComponent_eq :
  Subgroup.connectedComponentOfOne O13 = LorentzIdentityComponent.Splus`, whose docstring reads *"No
  hypothesis"*. For row 10, only entry 42, the spin group's topology, still stands. T8 above is
  written from the corrected reading. Per the stand-down order, this is logged here and the source is
  not reopened.
