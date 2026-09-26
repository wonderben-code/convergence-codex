# Assumptions ledger — the stop-point digest

*Snapshot of 26 September 2026, taken at the stand-down after hardening unit 243. The source is
`formalisation/ASSUMPTIONS_LEDGER.md` in `wonderben-code/codex-internal`, branch
`claude/infinitography-formalisation-fbqxf3`, as of commit `2bc86f1` (unit 243).*

## How to read this

An **assumption** here is a choice the estate makes that no proof forced: a definition picked from
several, a hypothesis a theorem takes and nothing supplies, or a physics input taken from the
literature. It is **not** a missing proof — those are the walls, in `WALLS.md` beside this file — and
it is not a hollow file, whose verdicts are in the `TRUE_LEDGER` tier table. A missing proof can be
closed by proving something. An assumption can only be closed by changing the model or by defending
the choice.

The source ledger has **57 entries**, numbered **1–36 and 40–60**. **Numbers 37, 38 and 39 were never
issued.** On 1 August the first appended entry was numbered 40 by mistake. The numbers were not
closed up afterwards because other documents cite entries by number (`ERRATUM 207`). This digest
keeps the source's numbers.

Each entry below says four things in plain language:

- **Assumed** — what is taken rather than derived.
- **Bites** — the files and theorems that depend on it.
- **Cuts** — the source's *bias* grade. *Anti-conservative* means the choice makes a result read
  stronger than it is. *Conservative* means it reads weaker. *Neutral* means neither.
- **Today** — where it stands on 26 September, and what later work changed.

The **Today** line uses six words:

| word | meaning |
|---|---|
| **Stands** | still assumed, as filed |
| **Narrowed** | later proofs removed part of it; the rest is still assumed |
| **Hardened** | later theorems showed the choice cannot be repaired the easy way; it is still assumed |
| **Corrected** | the entry as filed understated the estate; the amendment says what is really still assumed |
| **Retired** | proved; kept on the list for the record |
| **DECISION** | a choice only the author can make (`DECISIONS NEEDED`) |

**Eleven entries are author decisions**: 47, 48, 49, 50, 51, 52, 54, 55, 56, 57 and 58. **One entry,
53, is the estate's only `axiom`.**

**Three numberings share the word *decision*** (`ERRATUM 683`), and this digest keeps them apart:
- *item n* is the running `DECISIONS NEEDED` list in `PROGRESS_LOG.md`, items 1–30;
- *DECISION 1* to *DECISION 6* are the early-August series, now items 16–21 of that list;
- *entry 47* to *entry 58* are this ledger's entries.

The source runs to 2,191 lines. It carries the evidence, the reasoning and every amendment, each
quoted in place rather than rewritten (`ERRATUM 94`). This digest is shorter and plainer. **Where it
disagrees with the source, the source is right and this digest is wrong.**

---

## At a glance

| # | assumption, in one line | cuts | today |
|---|---|---|---|
| 1 | 96 is the right count of Yukawa eigenvalues | conservative | Stands |
| 2 | the cascade is a record whose fields are its own conclusions | anti-conservative | Stands |
| 3 | the seed algebra is over ℂ and associative | anti-conservative | Hardened |
| 4 | the seed's ⋆-structure: the positive cone is pointed (a faithful ⋆-representation) | mixed | Narrowed |
| 5 | which tensor factor decomposes; chirality's asymmetry is a definition | anti-conservative | Stands |
| 6 | Lorentzian signature is picked by a choice of real slice and form | anti-conservative | Stands |
| 7 | `n = 4` comes from the constraint set, with `n ≤ 4` a hypothesis | anti-conservative | Narrowed |
| 8 | the mass gap is that of a Gaussian substituted for the spectral action | anti-conservative | Stands |
| 9 | the Standard Model algebra does not embed in `su(4)` on the blocks used | anti-conservative | Corrected |
| 10 | the Pati–Salam constraint system and the level it is read at | anti-conservative | Stands |
| 11 | the gauge group of a factor `Mₙ(ℂ)` is `SU(n)` | anti-conservative | Stands |
| 12 | the spectral weight is multiplicative; the cutoff moments are 1 | anti-conservative | Narrowed |
| 13 | the Higgs normalisation chain is Chamseddine–Connes's; `g = g₃` | unknown | Stands |
| 14 | the Yukawa matrix ranges over all complex `N × N` matrices | mixed | Stands |
| 15 | the reflexive domain is the full function space | anti-conservative | Corrected |
| 16 | the GNS state is the trace state, and its vector is called the vacuum | anti-conservative | Stands |
| 17 | one cascade level is given two different Hilbert spaces | unknown | Narrowed |
| 18 | KO-dimension is assigned three ways | anti-conservative | Corrected |
| 19 | the finite spectral triple is a toy | anti-conservative for physics | Stands |
| 20 | the three lineages branch from `ℂ²`, not from the seed `M₂(ℂ)` | anti-conservative | Stands |
| 21 | End, Aut and the inner product are the only canonical operations | anti-conservative | Stands |
| 22 | spacetime is read at cascade level `D₂` | anti-conservative | Stands |
| 23 | the Standard Model algebra is placed at the `M₂₅₆` level | anti-conservative | Stands |
| 24 | `sin²θ_W = dim su(2) / dim su(3)` | anti-conservative | Stands |
| 25 | the three generations are the three imaginary quaternions | anti-conservative | Hardened |
| 26 | the spectral-action measure is one-dimensional and infinite | anti-conservative | Narrowed |
| 27 | Poincaré inequality: polynomial tests, standard Gaussian, iterated integrals | conservative | Corrected |
| 28 | the transfer operator is chosen, not derived | anti-conservative | Narrowed |
| 29 | reflection positivity is proved only where a block is rank one | — | Corrected |
| 30 | cascade identifications are linear equivalences, not algebra maps | mixed | Corrected |
| 31 | anomaly coefficients are cubic traces, with the fermion content built in | anti-conservative | Narrowed |
| 32 | generators are bounded in the Stone/Schrödinger work | conservative | Hardened |
| 33 | three Standard-Model numbers are imported, not derived | anti-conservative | Stands |
| 34 | "at least three colours" is a physical input to chirality | anti-conservative | Stands |
| 35 | the seed-forcing argument runs in `Type` | neutral in file | Stands |
| 36 | conventions that carry no content | neutral | Stands |
| 40 | the `n`-dimensional Gaussian expectation is a moment functional | anti-conservative | Stands |
| 41 | `SO⁺(1,3)` is defined algebraically | neutral | Retired |
| 42 | `spinGroup` is algebraic, not the simply-connected double cover | neutral | Stands |
| 43 | the spectral action is for polynomial cutoffs and is not a measure | anti-conservative | Narrowed |
| 44 | `d = 4` on the lattice is four coordinates, in finite volume | conservative | Stands |
| 45 | `MatrixLoewner` fixes a norm Mathlib leaves open | none | Stands |
| 46 | the Peierls decomposition assumes a `+` boundary the model lacks | conservative | Stands |
| 47 | what *compatible* means for the torus covariances | — | DECISION |
| 48 | which real structure `J` is the estate's: `ε = +1` or `−1` | — | DECISION |
| 49 | the real Clifford classification as a table or as one theorem | — | DECISION |
| 50 | which of three OS-axiom numberings to use | — | DECISION |
| 51 | whether a watchlist item proved by an unforeseen route is closed | — | DECISION |
| 52 | whether to namespace the `F`-series | — | DECISION |
| 53 | the one `axiom`: a Gibbs measure with no defining property | — | Stands |
| 54 | in which frame a metric's curvature components are read | — | DECISION |
| 55 | whether finite-volume OS shadows finish the lattice-field item | — | DECISION |
| 56 | which contraction the contracted Bianchi identity means | — | DECISION |
| 57 | what turns the trace ratio `3/8` into the Weinberg angle | — | DECISION |
| 58 | `PROOF_STRATEGY` §3's worked example is out of date on `main` | — | DECISION |
| 59 | the Born rule, Gleason and Wigner are cited, not derived | anti-conservative | Stands |
| 60 | the two Higgs vacua are chosen, not derived | anti-conservative | Narrowed |

A dash in the *cuts* column means the source gives no single grade for the entry as it now stands.

---

## The entries

### 1. N = 96 is the right Yukawa multiplicity

**Assumed.** The Higgs-coupling bound is computed from two traces of the Yukawa matrix,
`a = Tr(Y†Y)` and `b = Tr((Y†Y)²)`, over 96 indices — the cascade's fermion count. Chamseddine and
Connes compute the same quantities over 24 eigenvalues. The ratio that matters, `b/a²`, changes when
the count changes, and nothing in the estate derives which count is right.
**Bites.** `HiggsBridge.lean`: `cascade_ccLambda_lower`, `cascade_ccLambda_window`,
`cascade_higgsMassSq_window`.
**Cuts.** Conservative, because `g²/96` is a weaker lower bound than `g²/24`. But it is nearly empty:
the window `[g²/96, g²]` spans a factor of 96.
**Today.** Stands.

### 2. The cascade is modelled as a record that carries its own conclusions

**Assumed.** `CascadeData` stores the numbers the estate says it derives as fields: the spectral gap
(`internal_gap = 2/Λ²`), the spacetime dimension (`d = 4`) and the Poincaré dimension (10).
`HasMassGap.mk_from_positive_gap` builds a whole mass-gap structure from any positive real. A theorem
that reads such a field back out is projecting an assumption, not deriving a result.
**Bites.** `CascadeFoundation.lean` and its consumers, among them `F1_7_SpacetimeForced` and
`BakryEmeryGap`. The source counts 21 consumption sites.
**Cuts.** Anti-conservative. The source calls this the highest-leverage entry, because it is
invisible wherever it is used.
**Today.** Stands. On 10 September `projection_scan.py` counted, across the estate:
- 134 projections of assumed fields;
- 1 assumption in disguise;
- 19 definitional verifications — for example, `d := 4` is set and then `hd : d = 4` is discharged by
  `rfl`;
- 1 vacuous field.

Since unit 152 (20 September) the estate also has a genuine recursive cascade, `CascadeTowerRecursive`,
built by `Dr (k+1) = End(Dr k)`. It comes with `Dr 1 ≃ₐ M₄(ℂ)`, `Dr 2 ≃ₐ M₁₆(ℂ)` and
`Dr 3 ≃ₐ M₂₅₆(ℂ)` proved. No theorem relates it to `CascadeData`, whose fields are unchanged.

### 3. The seed algebra is over ℂ, and is associative

**Assumed.** "`M₂(ℂ)` is the unique minimal non-commutative seed" is proved over the complex numbers,
for associative algebras. Over ℝ the uniqueness is false: ℍ and `M₂(ℝ)` both qualify. The `[Ring A]`
hypothesis excludes the octonions before the argument starts. The published constraint list does not
name the base field, and ℍ meets all four published constraints.
**Bites.** `SeedUniqueness.lean`: `seed_dim_lower_bound`, `seed_unique_dim_four`, `seed_forced`.
**Cuts.** Anti-conservative.
**Today.** Hardened on 15 September. `matrix1H_not_ringEquiv_matrix2R` proves ℍ and `M₂(ℝ)` are not
isomorphic. `realForm_not_determined_two` proves the two have the same complexification, so working
over ℂ instead erases exactly the distinction at issue. The Lean discloses the assumption; the
published paper does not.

### 4. The seed's ⋆-structure

**Assumed, as filed.** The seed is meant to be a C⋆-algebra, but `SeedUniqueness` had no star, no
involution and no norm. Its conclusion carried the multiplication across and not the adjoint.
**Bites.** `SeedUniqueness.lean` (`seed_unique_dim_four`, `seed_forced`), and every reading of "the seed
C⋆-algebra is `M₂(ℂ)`".
**Cuts.** Mixed. Dropping the star from the hypotheses is conservative, and the conclusion side is
the dangerous one.
**Today.** Narrowed to one named input by units 150, 151 and 164–166 (20 September):
- Any ⋆-structure on the seed is carried to `M₂(ℂ)`, where there are exactly two classes: the definite
  one and signature (2, 2) (`SeedStarStructure`).
- A pointed positive cone selects the definite class, at every size (`SeedStarPositivity`,
  `StarStructurePointed`).
- A faithful ⋆-representation on an inner-product space gives a pointed cone, and so does a faithful
  spectral triple (`StarStructureFromRep`, `TripleSelectsStar`).

**What is still assumed:** that the seed acts faithfully on the Hilbert space of a spectral triple —
or, more weakly, that its positive cone is pointed. Nothing in the estate supplies either for a seed
with its own star, and no norm exists anywhere in the estate. The *"ALL of them"* modelling-note
header in `SeedUniqueness.lean` is still unrepaired.

### 5. Which tensor factor decomposes — chirality's asymmetry is a definition

**Assumed.** The claim that the weak force is left-handed rests on an asymmetry in `M₄ ⊗ M₄`: the
right factor "remembers" its `M₂ ⊗ M₂` structure and the left does not. In Lean the right factor
decomposes because the definition decomposes it. The mirror statement has the same one-line proof;
this was compiled and checked.
**Bites.** `F1_6_PatiSalamForced.asymmetric_from_iteration`; `F2_3_ChiralityForced`
(`azumaya_sectors_inequivalent`, `internal_structure_distinguishes`);
`GaugeGroupSelection.asymmetric_decomposition`; `PreferredDecomposition.lean`.
**Cuts.** Anti-conservative, and the source calls it the sharpest case in the estate. Parity
violation, the most-emphasised derived fact in the published §6, rests on a definitional convention.
**Today.** Stands.

### 6. Lorentzian signature is selected by the choice of real slice and quadratic form

**Assumed.** Three routes in the estate reach signature (1, 3), and each selects it by a choice:
- **(a)** 2×2 Hermitian matrices with the determinant as the form. The slice `M₂(ℝ)` gives (2, 2)
  instead.
- **(b)** Of the two natural forms on ℍ, choosing `Re(q²)` rather than the norm.
- **(c)** Ruling out (4, 0) and (0, 4) as Riemannian, which is the very empirical input the file claims
  to eliminate.

**Bites.** `MinkowskiHerm2`, `MinkowskiSignature`, `F1_7b_SpacetimeUnconditional`,
`F1_7c_SpacetimeFinalClosure`, `F1_7_SpacetimeForced`, `GravityLineage`.
**Cuts.** Anti-conservative.
**Today.** Stands. Three later results sharpen it without moving it:
- Signature (2, 2) is excluded by an algebra invariant (`clifford13_not_ringEquiv_clifford22`), so one
  signature is decided structurally and two are not.
- A fourth route, a form taken from the seed's own ⋆-structure, is closed by theorem: such forms have
  even signature entries and are never (1, 3) (`HermitianSignatureEven`, units 150–153).
- `Aut(M₂(ℂ)) ≃* SO⁺(1,3)` (units 186–187) does not select the signature, because its target group is
  defined with the Minkowski metric written in.

### 7. n = 4 is selected by the constraint set, and minimality is a hypothesis

**Assumed.** "The classification forces `n = 4`" is proved from a structure whose fields say:
- the algebra is a single `Mₙ(ℂ)`;
- `n` is even;
- `n² − 1 ≥ 12`;
- `n ≤ 4`.

The caller supplies `n ≤ 4`, and after that the proof checks three cases. The real
Chamseddine–Connes classification ranges over sums of matrix algebras over ℝ, ℂ and ℍ, and lands on
`ℂ ⊕ ℍ ⊕ M₃(ℂ)`, which is not of the assumed form.
**Bites.** `ConnesClassification.lean` (`ChamseddineConnesAxioms`,
`chamseddine_connes_classification`), and `CascadeUniqueness`'s `n ≤ 4`.
**Cuts.** Anti-conservative, and it carries the estate's flagship star tag.
**Today.** Narrowed on 14 September. Semisimplicity, which Chamseddine and Connes assume, is now a
theorem from a faithful ⋆-representation (`StarRepSemisimple`). The inputs this entry is about are
still supplied: a single matrix algebra, `n` even (standing in for Poincaré duality), and
`n² − 1 ≥ 12` (standing in for Standard-Model containment), together with the minimality bound.

### 8. The mass gap is the gap of a Gaussian substituted for the spectral action

**Assumed.** The Bakry–Émery route replaces the spectral action `Tr f(D/Λ)` by the quadratic
`Tr(D²/Λ²)`. That makes the measure exactly Gaussian, with gap `2/Λ²`. The real spectral action has
Yang–Mills and Higgs-quartic terms and is not quadratic, and without log-concavity Bakry–Émery does
not apply.
**Bites.** `BakryEmeryGap.lean`, which proves no gap: `spectral_gap` is a `def`, and the criterion is
`le_refl _`.
**Cuts.** Anti-conservative, severely.
**Today.** Stands. The picture around it was corrected on 10 August:
- The spectral action exists in Lean for polynomial cutoffs (`SpectralAction.spectralAction`), and it
  is a function of `Λ²`.
- A genuine Poincaré inequality with the constant `Λ²/2` exists (`SpectralGaussianGap.poincare_lambda`).

So the obstacle is not the shape of the action. It is that a trace is a number, and nothing builds a
measure from it. That step is a modelling choice, sent to the author in early August as DECISION 5
(what fluctuates, and with what weight) and DECISION 6 (whether a polynomial cutoff is acceptable).
Those are items 20 and 21 of the running `DECISIONS NEEDED` list.

### 9. su(3) ⊕ su(2) ⊕ u(1) does not embed in su(4) on the blocks used

**Assumed, as filed.** The colour block uses indices {0, 1, 2} and the weak block {2, 3}. They share
index 2, so the three maps do not assemble into an embedding: their images do not commute. A compiled
counterexample checks this.
**Bites.** `LieAlgebraEmbedding.lean` (the `sm_embedding_theorem` docstring), propagating to
`F1_6_PatiSalamForced.pati_salam_constructive_embedding` and
`ConnesClassification.gauge_group_forced`.
**Cuts.** Anti-conservative.
**Today.** Corrected on 20 September:
- The non-embedding has been a theorem since 2 August (`SMEmbeddingHonest.assembly_not_injective`,
  `SMLieHom.no_lieHom_assembling`).
- The docstring has carried a warning since 4 August.
- The statement the headline should have made has been a theorem since 14 September: an injective Lie
  map of the Standard Model algebra into the Pati–Salam algebra `sl₄ × sl₂ × sl₂`
  (`SMInPatiSalam.smToPS`).

Still open: whether the Standard Model algebra embeds in `sl₄` alone by arbitrary maps.

### 10. The Pati–Salam constraint system, and the level at which it is read

**Assumed.** "Pati–Salam is forced, zero alternatives" means that `a·b·c = 16`, `a = b²`, `b = c`,
`b ≥ 2` has the unique solution (4, 2, 2). Three choices sit inside that:
- The 16 fixes the cascade level. At the next level the same constraints give (16, 4, 4).
- `a = b²` is justified in one line of prose, and dropping it admits other solutions.
- `b = c`, which is meant to carry left–right symmetry, does no work: the other constraints alone force
  (4, 2, 2). This was checked.

**Bites.** `F1_6_PatiSalamForced.lean`: `CascadeConstraints` and its uniqueness theorems.
**Cuts.** Anti-conservative.
**Today.** Stands.

### 11. From a matrix factor Mₙ(ℂ) to the gauge group SU(n)

**Assumed.** Nothing derives that the gauge group of a factor `Mₙ(ℂ)` is `SU(n)`. `U(n)`, `PU(n)` and
the algebra's unitary group are all defensible, and they give different ranks and generator counts.
**Bites.** `F1_6` (`three_factor_dimensions`, `pati_salam_to_sm_rank`), and every symmetry-breaking
file since unit 188.
**Cuts.** Anti-conservative for "the only possible group"; neutral for the dimension counts.
**Today.** Stands. The objects now exist:
- `SU(n)` with its exponential map (unit 188).
- `su(n)` is exactly `SU(n)`'s Lie algebra (unit 217).
- The group acts on the Higgs fields (unit 191).

Nothing tests another choice of group, so these statements inherit the choice; they do not support it.

### 12. The spectral weight is assumed multiplicative, and the cutoff moments are set to 1

**Assumed, as filed.** The chain to "zero free parameters" has four steps:
1. Tensoring makes eigenvalues add.
2. So the weight must be multiplicative.
3. So `f(x) = e^{−cx}`.
4. So with `c = 1` all three moments are 1.

Three choices are buried in that chain:
- Multiplicativity was asserted from a dimension identity, not from eigenvalues.
- `c = 1` is a normalisation, and the physical outputs depend on the individual moments.
- Multiplicativity excludes the smooth cutoffs Chamseddine and Connes actually use.

**Bites.** `F3_10a_HeatKernelCanonicity` (`zero_free_parameters` is `19 − 3 = 16 ∧ 3 − 3 = 0`) and
the cutoff files.
**Cuts.** Anti-conservative.
**Today.** Narrowed. This is the most-amended entry: nine amendments, six of them today.
- **14 September.** The trace of an exponential factorises across a tensor sum
  (`SpectralCutoffFactorises.trace_exp_kroneckerSum`), and factorisation forces
  `f(x + y) = f(x) f(y)`. Multiplicativity is now derived from the tensor-sum shape, not asserted from
  dimensions.
- **20 September.** On the regular bimodule of `Mₙ(ℂ)`, order-one is equivalent to the tensor-sum shape
  (unit 168), so there the factorisation follows from order-one (unit 172). The three moments equal 1
  exactly when `κ = 1` (unit 174), so "the moments are set to 1" is exactly a normalisation of `Λ`.
- **26 September, units 232–243.** Whether order-one gives the tensor-sum shape — the premise the
  factorisation needs — is decided on each of the estate's models:
  - It holds for every operator exactly for one full matrix algebra at multiplicity one.
  - It fails with generations, with or without `J` and the grading.
  - It fails on a product of two or more matrix algebras.
  - In the model with the grading, it holds exactly when the generation matrix is a multiple of the
    identity.

**Still assumed:** the tensor-sum shape for the cascade's own `D`, of which there is none in the
estate, and for `A_F` on `H_F`, which is none of these models and is not settled either way.

### 13. The Higgs normalisation chain is CCM's, and g is g₃ at unification

**Assumed.** Four links are taken from Chamseddine–Connes rather than derived:
- the boundary condition `λ̃(Λ) = g²·b/a²`;
- `λ = 4λ̃`;
- `m_H² = 2λv²`;
- a single coupling `g` at unification.

That `g` is their `g₃`, which is defensible only as far as the couplings meet, and their own figure
says they do not meet exactly. In Lean, `g` is an inert multiplier and `v` is unconstrained.
**Bites.** `HiggsBridge.lean`: `ccLambda`, `higgsMassSq`, `cascade_higgsMassSq_window`.
**Cuts.** Unknown and multiplicative. An error of 4 in `λ = 4λ̃` was actually made and caught (see
`ERRATA`).
**Today.** Stands.

### 14. The Yukawa texture space is all complex N×N matrices

**Assumed.** `Y` ranges over every complex 96×96 matrix: no sector blocks, no colour multiplicity, no
generation structure. That is what makes the sharpness witnesses work. The upper end is attained by a
single nonzero diagonal entry, which no physical texture can be.
**Bites.** `HiggsBridge`: `ccLambda_upper_sharp`, `ccLambda_lower_sharp`.
**Cuts.** Mixed. Conservative for the window. Anti-conservative for "the constants cannot be
improved", which is unproved over physical textures.
**Today.** Stands.

### 15. The reflexive domain is the full function space

**Assumed, as filed.** The root of the tree is `D = (D → D)`. Domain theory uses continuous functions
(Scott's `D∞`). With all functions, Cantor's argument forces `D` to be trivial.
**Today.** Corrected on 20 September:
- The full-function reading is refuted as a theorem: such a `D` is a subsingleton
  (`ReflexiveDomainObstruction`).
- The continuous reading is the estate's working one. A non-trivial `D ≃o (D →𝒄 D)` is built
  (`CanonicalTower.dInfExists_orderIso`), and the "forces" half is proved at it
  (`DInfForces.dInf_forces`).

**What stands:** four files still take `φ : D ≃ (D → D)`, so their theorems are true of trivial `D`
only. The published headline uses the full function space. Moving it to the continuous reading is
the author's restatement (item 6 of the running `DECISIONS NEEDED` list), and the L2 link stays
PARTIAL for that reason.

### 16. The GNS input state is the trace state, and its cyclic vector is called the vacuum

**Assumed.** The GNS construction takes `ω(a) = Tr(a)/4`, the maximally mixed state, and calls its
cyclic vector "the vacuum". A vacuum is normally a pure state. For a pure state, faithfulness fails,
the null space is 12-dimensional, and the GNS space collapses from ℂ¹⁶ to ℂ⁴.
**Bites.** `CascadeGNS`.
**Cuts.** Anti-conservative: both headline results are properties of the chosen state.
**Today.** Stands.

### 17. The same cascade level is given two different Hilbert spaces

**Assumed.** `FiniteStone` puts `M₄(ℂ)` on ℂ⁴, and `CascadeGNS` puts it on its 16-dimensional GNS
space. Neither file is wrong. Any argument that chains them is.
**Cuts.** Unknown, and the source calls it the dangerous kind of unknown.
**Today.** Narrowed on 15 September. Stone's converse holds on both spaces (`StoneConverseCarriers`),
so a unitary group's generator exists and is unique whichever space is meant. The two spaces are not
identified, and which one is the cascade's is still unresolved.

### 18. KO-dimension: three assignments across the estate

**Assumed, as filed.** The same triple is assigned KO-dimension 0 in one file, 2 in three and 6 in
two. At filing, no real structure `J` was an operator anywhere.
**Cuts.** Anti-conservative wherever a value is asserted with no operator behind it.
**Today.** Corrected in parts:
- Units 119–120 (18 September) re-counted the files. The repair owed was two files, not four, and both
  of them — `F3_8f_ConnesNCG` and `F4_3d_SpectralWightman` — now carry a disclosure.
- `J` has been an operator in the KO-6 file since 14 September (`KOSixSpectralTriple`).
- Since unit 155 both real structures are built on the toy's own operators: `Jzero` gives the KO-0
  signs, `Jtoy` the KO-6 signs.

Which `J` is the estate's is entry 48's decision.

### 19. The finite spectral triple is a toy

**Assumed.** The triple has `A = M₄(ℂ)`, `H = ℂ⁴`, and a Dirac operator with one parameter `m`, so
`D² = m²`. The physical finite `D` carries 3×3 Yukawa matrices and Majorana terms. What the published
§11 attributes to the heat-kernel expansion "on the cascade" is computed on this toy.
**Cuts.** Anti-conservative if any Yukawa or Higgs consequence is drawn from it; neutral as a witness
that the grading axioms can be met.
**Today.** Stands for the toy. Since 15 September the estate also has a genuine spectral triple on the
regular bimodule of `M₂(ℂ)` (`RealSpectralWitness.realWitness`), with every Chamseddine–Connes
condition a proved field. Units 164–172 show that there the axioms leave nothing to choose. Neither
object is the physical finite triple on `H_F`.

### 20. The three lineages branch from ℂ², not from the seed algebra M₂(ℂ)

**Assumed.** The published §5 branches three operations "from the seed `M₂(ℂ)`", but the evidence
branches from ℂ². The difference matters:
- The automorphisms of the algebra `M₂(ℂ)` form `PGL₂(ℂ)`, with trivial centre.
- The automorphisms of the vector space ℂ² form `GL₂(ℂ)`.

The gravity lineage — `SL₂(ℂ)`, its centre of order 2, the 2:1 cover of the Lorentz group — needs the
vector-space reading.
**Cuts.** Anti-conservative.
**Today.** Stands.

### 21. "End, Aut and ⟨·,·⟩ are the only canonical operations"

**Assumed.** This is what makes the cladogram a complete map rather than three chosen constructions.
"Canonical" is never defined. An inner product is extra structure, not a functor, and a canonical
inner product on ℂ² presupposes a preferred basis.
**Cuts.** Anti-conservative in the paper; neutral-to-unknown as mathematics.
**Today.** Stands.

### 22. Spacetime is read at cascade level D₂

**Assumed.** The cascade levels give Clifford dimensions 2, 4 and 8. The estate picks level 2 as "the
physically relevant" one, on the grounds that Pati–Salam needs `D₂`, while `F1_6` places Pati–Salam
at `D₃`, which would give dimension 8.
**Cuts.** Anti-conservative. "dim = 4 FORCED" really means "dim = 4 if spacetime is read at level 2".
**Today.** Stands. The source's priority list also notes that the Clifford model's signature-(2, 2)
quadratic form is recorded in no audit document.

### 23. The Standard Model's finite algebra is placed at the M₂₅₆ level

**Assumed.** That `ℂ ⊕ ℍ ⊕ M₃(ℂ)` appears at cascade level 4 carries a `PROVED ★` tag. No Lean file
constructs that algebra, and the one statement that mentions it compares its dimension (14) with 16,
which is the `M₄` level. No selection principle picks a depth.
**Bites.** `F3_8f_ConnesNCG.ncg_input_comparison`.
**Cuts.** Anti-conservative.
**Today.** Stands.

### 24. sin²θ_W = dim su(2) / dim su(3)

**Assumed.** The Weinberg angle is presented as a ratio of Lie-algebra dimensions, 3/8. The formula is
chosen, and the two numbers are never divided in any statement. The standard derivation is a trace
ratio over a complete multiplet. A second, incompatible derivation of the same number sits in the
same estate.
**Cuts.** Anti-conservative.
**Today.** Stands for the files that use the dimension ratio. The trace-ratio derivation is now
computed elsewhere, and what connects it to the physical angle is entry 57's decision.

### 25. Generations are indexed by the imaginary quaternions

**Assumed.** `dim Im ℍ = 3` is proved. That those three directions *are* the three fermion generations
is a physical postulate.
**Bites.** `F3_1_ThreeGenerations`, Step 5; `F3_1b_ModuleSpectral`, which is graded HOLLOW.
**Cuts.** Anti-conservative.
**Today.** Hardened:
- Frobenius's theorem is proved in the estate (1 September), though not in Mathlib. Hurwitz's theorem
  is only cited.
- `ℂ ⊗ M₂(ℍ) ≃ M₄(ℂ)` is proved (15 September). Theorems also show it cannot bear on this assumption:
  different real algebras share that complexification.
- Since unit 154 the imaginary quaternions exist as an object (`pureSubmodule`).

None of this touches the identification with generations.

### 26. The spectral-action measure is one-dimensional, and has infinite mass

**Assumed.** The `withDensity` measure lives on ℝ, with the action's value as the coordinate, not on
the space of Dirac operators. `exp(−S)` is unbounded where `S < 0`, so the measure is not finite, let
alone a probability measure.
**Cuts.** Anti-conservative.
**Today.** Narrowed around it. A genuine Gaussian probability measure exists on the Hermitian 4×4
matrices (`Herm4Gaussian`, 14 September), with its density, scaling and partition function computed
(unit 161). That any such Gaussian is the Boltzmann measure of the spectral action is not proved. It
is early-August DECISION 5, which is item 20 of the running `DECISIONS NEEDED` list.

### 27. Poincaré: polynomial test functions, the standard Gaussian, iterated integrals

**Assumed, as filed.** The Gaussian Poincaré inequality was proved only for polynomial test functions
and the standard Gaussian, with iterated integrals.
**Cuts.** Conservative for the inequality itself.
**Today.** Corrected on 10, 16 and 29 August. All four restrictions have fallen:
- the Sobolev-space version is proved (`TextbookSobolev.poincare_sobolevWeak`);
- it holds at every variance;
- Hermite completeness holds at every variance and in every dimension.

**The load-bearing caveat stands.** The estate's `gap = 2/Λ²` concerns a spectral-action measure that
does not exist in Lean, so no Bakry–Émery tag may move.

### 28. The transfer operator is chosen, not derived

**Assumed.** `TransferGap` computes a spectral gap from a spectrum, but the spectrum belongs to an
operator written down by hand, `T = diag(e^{−Δk})`, so the gap is put in by hand. `TransferMatrix` is
worse: there the gap is a field, and the bound is `le_refl`.
**Cuts.** Anti-conservative.
**Today.** Narrowed. The two files are unchanged. The amendment of 20 September (unit 146) records
that the estate also has a derived transfer operator: the one-dimensional Ising chain's
(`IsingTransferMatrix`), with spectrum `2 cosh β` and `2 sinh β` and gap `2e^{−|β|}`.

### 29. Reflection positivity is proven where the block is rank one

**Assumed, as filed.** OS2 was proved only for the one-dimensional exponential kernel, where the
cross-boundary block is rank one.
**Cuts.** Graded conservative when filed. The source's revised grade is that the entry itself
understated the estate and pointed readers at the wrong wall, twice.
**Today.** Corrected twice (10 and 16 August):
- OS2 is proved in every dimension, for both the product field and the graph Gaussian field, with
  complex test vectors. When counted on 10 August, 33 files carried an OS2 theorem.
- The estimates for OS0, OS3 and OS4 exist, and OS1 has been stated in finite volume since 28 August.

**What is still assumed:**
- the field is free (Gaussian), with no interacting measure anywhere in the estate;
- the volume is finite;
- the mass is nonzero;
- everything is on a lattice.

What is missing is the infinite-volume and continuum limits, not an estimate.

### 30. Cascade identifications are ℂ-linear equivalences, not algebra or representation isomorphisms

**Assumed, as filed.** `Dₙ ≅ M_{2^2^n}(ℂ)`, `ℂ¹⁶ ≅ ℂ⁴ ⊗ ℂ² ⊗ ℂ²` and the branching rule
`4 → 3 ⊕ 1` are proved as linear equivalences from equal dimensions. No algebra structure or group
action is carried, so any space of the same dimension satisfies them.
**Cuts.** Conservative where a file labels this; anti-conservative where it does not.
**Today.** Corrected in part. That no algebra structure is carried is false for the End step as of
14 September (`ERRATUM 563`): `CascadeEnd.endMatrixEquiv` is an algebra equivalence, and so is the
recursive tower in entry 2. The branching-rule point stands: no group, action or equivariance appears.

### 31. Anomaly coefficients are cubic traces, with the fermion content written into the statement

**Assumed, as filed.** Three things:
1. That the anomaly *is* the symmetrised cubic trace — the ABJ result, cited and not formalised.
2. That fundamental and antifundamental appear with equal multiplicity — the input that makes
   Pati–Salam anomaly-free — was written into the theorem's shape.
3. `SU(2)_L` and `SU(2)_R` were collapsed into one factor.

**Cuts.** Anti-conservative.
**Today.** Narrowed on 14 September. `SU4OnSixteen.su4Rep` acts on the chiral 16, and the cubic form
is evaluated on that representation. So equal multiplicity is no longer written into a statement,
and the two mixed anomalies are computed on different blocks. The ABJ identification is still cited.
Witten's global anomaly is not addressed.

### 32. Bounded generators in the Stone/Schrödinger work

**Assumed.** The Schrödinger equation is proved for bounded Hamiltonians. Physics uses unbounded
self-adjoint operators, for which Mathlib has no spectral theory.
**Cuts.** Conservative: a smaller class of Hamiltonians than physics needs.
**Today.** Hardened into a characterisation on 15 September:
- Stone's converse is proved for any C⋆-algebra (`exists_unique_global_generator`).
- The groups `exp(itH)` with `H` in the algebra are exactly the norm-continuous ones
  (`eq_unitaryGroup_iff`).
- The converse is instantiated on concrete matrix carriers.

Unbounded generators need a different theorem, and machinery Mathlib lacks.

### 33. Imported Standard-Model bookkeeping

**Assumed.** Three numbers presented as cascade outputs are transcriptions:
- **β₀ = 21** is the standard one-loop QCD coefficient, imported, with a scale-dependent flavour count
  as input.
- **52 bosonic degrees of freedom** counts every Pati–Salam boson as massless, which contradicts the
  estate's own symmetry breaking, and includes the graviton.
- **96 fermionic degrees of freedom** is entry 1's number, reached in two incompatible ways in one file.

**Cuts.** Neutral as arithmetic; anti-conservative as attribution.
**Today.** Stands.

### 34. "At least three colours" as a physical input to chirality

**Assumed.** The decomposition `(4,2,1) ⊕ (4̄,1,2)` is computed from `a·b = 8` with `a ≥ 3`, `b ≥ 2`.
The input `a ≥ 3` is the observed number of colours, and it very nearly determines the output.
**Bites.** `F2_3_ChiralityForced.chiral_decomposition_derived`.
**Cuts.** Anti-conservative for the word "forced". The file discloses the input precisely.
**Today.** Stands.

### 35. The seed-forcing argument runs in Type

**Assumed.** "Nothing is sterile and the seed is fertile" is run with ∅ = `Empty`, I = `Unit`,
I ⊕ I = `Bool`, and functions as the internal hom. The sterility step needs `[∅, ∅] ≅ I`. That holds
in `Type` but fails in finite-dimensional complex vector spaces, where `End(0)` is the zero space.
Nothing connects `Bool` to ℂ².
**Cuts.** Neutral within the file; anti-conservative for any estate-level use as "the seed is forced".
**Today.** Stands.

### 36. Conventions that carry no content

**Assumed.** These are recorded so nobody mistakes them for content:
- the `exp(+itH)` sign convention;
- `ℏ = 1`, which is silent;
- `det` rather than `−det` for the Minkowski form;
- the lattice kernel's dropped normalisation;
- Pauli coordinates labelled (t, x, y, z) by fiat.

**Cuts.** Neutral. Nothing numerical depends on them.
**Today.** Stands.

### 40. The n-dimensional Gaussian expectation is a moment functional, not an integral

**Assumed.** `GaussianPoincareProduct.EN n` is defined by peeling off one variable at a time and
weighting by one-dimensional moments. It agrees with the Gaussian expectation on everything checked,
and it is the integral at `n = 1` (`EN_one_eq_integral`). But no theorem identifies it with the
product-measure integral for `n > 1`.
**Bites.** `EN n`, `SpectralGaussianGap.ENs`, and the ℝ¹⁶ results.
**Cuts.** Anti-conservative wherever the word "measure" is used.
**Today.** Stands.

### 41. SO⁺(1,3) is defined algebraically, not as the identity component

**Assumed, as filed.** "Proper orthochronous" was defined as `det Λ = 1` together with `Λ⁰₀ > 0`, with
nothing proving that this is the identity component.
**Today.** Retired by proof on 15 August. `SL2Connected.identityComponent_eq` proves that the identity
component of O(1,3) is SO⁺(1,3), with no hypothesis.

### 42. `spinGroup Q₁₃` is Mathlib's algebraic spin group, not the simply-connected double cover

**Assumed.** Mathlib's `spinGroup` is defined algebraically. The physics object "Spin(1,3)" is the
simply-connected double cover of the Lorentz group's identity component, which is a topological
description.
**Cuts.** Neutral, but the name invites over-reading.
**Today.** Stands, and carries more weight since 8 August. The estate proves an isomorphism of
abstract groups, `Spin(1,3)/{±1} ≃* SO⁺(1,3)` (`spinDoubleCover`), and identifies it with the `SL₂(ℂ)`
chain. No topology, continuity or covering map appears anywhere in that chain. "Simply-connected
double cover" is not proved.

### 43. The spectral action is defined for polynomial cutoffs only, and it is not a measure

**Assumed.** `spectralAction f Λ M := Tr f(D/Λ)` takes `f` to be a polynomial. More importantly, it is
a number, not a measure.
**Cuts.** Anti-conservative.
**Today.** The first part is narrowed:
- The spectrum is symmetric, so only the even part of any cutoff contributes.
- Since 14 September the estate evaluates exponential cutoffs on matrices
  (`SpectralCutoffFactorises`, `OrderOneCutoffFactorises`, `DecayingCutoff`).

The second part stands. What fluctuates, and with what weight, is a modelling choice (early-August
DECISIONS 5 and 6, which are items 20 and 21 of the running `DECISIONS NEEDED` list).

### 44. d = 4 in the lattice files is four coordinates, and the field is finite-volume

**Assumed.** The lattice objects live on `Fin 4 → Fin n`. There is no lattice spacing, no continuum
limit, no physical volume and no distinguished time direction. `d = 4` is a number of indices.
**Cuts.** Conservative in the theorems; anti-conservative if cited loosely. "A four-dimensional
lattice Gaussian field" is true; "the four-dimensional Euclidean field" is false.
**Today.** Stands.

### 45. `MatrixLoewner` fixes a norm on complex matrices that Mathlib deliberately leaves open

**Assumed.** The file declares a C⋆-algebra instance with the L² operator norm. Mathlib provides the
ingredients but declines to bundle them.
**Cuts.** None on the conclusions, because the Loewner order is norm-free.
**Today.** Stands.

### 46. The Peierls circuit decomposition holds under a `+` boundary condition the model does not impose

**Assumed.** `PlusBoundary σ` — every boundary site up — is a hypothesis on the configuration, not a
property of the free-boundary model. The Gibbs measure gives weight to configurations that violate it
(`not_plusBoundary_cornerDown`).
**Cuts.** Conservative in the theorems; anti-conservative if cited loosely.
**Today.** Stands.

### 47. DECISION — what *compatible* means for the torus covariances

The watchlist says, in load-bearing places, that the torus covariances are "not compatible". It gives
that as the reason there is no projective system along the torus graphs. The claim is prose. To
state it you must first say what *compatible* means, and that needs a map between the site sets of
tori of different sizes. No such map is canonical: adjacent sites and antipodal sites give different
statements. **The author's choice:** which notion of compatibility the estate means.

### 48. DECISION — `ε = J²` is −1 in one file and +1 in another, and the real structure has to be chosen

`F4_1e.ko_dimension_signs` asserts KO-dimension 2, with `ε = −1`. `KOSixRealStructure` proves
`ε = +1`, which is KO-dimension 6. The two cannot be reconciled by a convention. Since 15 September
the estate's `Triple` makes `ε = +1` an axiom of the structure, and unit 155 built both real
structures on the toy. **The author's choice:** which `J` is the estate's.

### 49. DECISION — the real Clifford classification as a table or as a theorem

A script (`reach_closure.py`) reports 3,321 real Clifford algebras (`p + q ≤ 80`). Each is answered
by a chain of the estate's own theorems, and none disagrees with the classical eightfold table. There
are two ways to present this:
- **(a)** Eight theorems, one per residue class. The estate effectively has these, and they are what
  any consumer uses.
- **(b)** One theorem with a type-valued target and a strong induction. It is the only form that
  deserves the name "the classification theorem", and nothing downstream needs it.

**The author's choice:** which form the estate should contain. It is a presentation question, not a
mathematical one.

### 50. DECISION — the OS axioms are numbered three ways

Three numberings in the sources disagree about which axiom is OS0 through OS5. The textbook order
argues for retiring the third. Choosing between the other two — whether regularity is OS0 or OS5 —
has no mathematical content, but it touches a structure four `F` files consume. Nothing is blocked
on it. **The author's choice:** which numbering.

### 51. DECISION — a watchlist item proved by a route its own BLOCKED ON line did not anticipate

The item on the volume-uniform variance bound for `absCoordField` has its objective proved
(`WitnessVarianceUniform.absCoordField_var_le_boxGraph`), by a route its own `BLOCKED ON` line did
not foresee. **The author's choice:** whether "closed" means "the objective is met" or "the named
route was taken". The answer sets a convention for every watchlist item.

### 52. DECISION — six theorem names declared twice at top level in the `F`-series

Thirty-two declarations share both name and signature with another file's. Six names are declared
twice at top level in the `F`-series, because each phase file restates the foundation facts it uses,
by the series' own convention. **The author's choice:** whether to namespace the `F`-series. The
source sets out three options, each of which is a rule for a whole published series.

### 53. The estate declares exactly one `axiom`: a Gibbs measure asserted into existence

**Assumed.** `axiom GibbsMeasure` (`lean_verify/_proof_004_logos.lean:86`) takes a Hamiltonian, an
inverse temperature and a reference measure, and returns a measure. Nothing constrains that measure.
Its docstring says why it is opaque: constructing it needs a finite partition function, Ruelle's
theorem and the DLR equations. The `gibbs` measure that `FiniteGibbs` defines is a different object,
with no bridge to it.
**Today.** Stands. Any declaration that uses it shows it in `#print axioms`. The same file holds the
build's one `sorry` (line 180).

### 54. DECISION — in which frame a metric's curvature components are read

The curvature of a metric now satisfies every clause of `AlgebraicCurvature.IsAlgCurv`, the algebraic
setting of the Lovelock classification. Stating that needs a basis of the tangent space indexed by
`Fin n`, and the estate offers three bases, with different consequences. **The author's choice:**
which frame.

### 55. DECISION — whether finite-volume OS shadows finish the item "for the lattice field"

The watchlist item *the OS axioms other than OS2, for the lattice field* has every finite-volume
shadow in place. **The author's choice**, in one sentence: whether an item titled *for the lattice
field* is satisfied by finite-volume shadows. If it is, the item closes, and walls W1 and W2 carry
the rest unchanged. Nothing in Lean moves either way.

### 56. DECISION — which contraction the contracted Bianchi identity means

`∇R` is now a `C^k` field (`CurvatureCovOrder.contMDiffAt_covRiemann_hom`). The next step, the
contracted Bianchi identity (`div Ric = ½ d scal`, so the Einstein tensor is divergence-free), has
every ingredient in the estate except a statement of which of `∇R`'s slots are contracted. **The
author's choice:** which contraction.

### 57. DECISION — what turns the trace ratio 3/8 into the Weinberg angle

The mathematics is proved. On the chiral Pati–Salam 16, `Tr(T₃L²)/Tr(Q²) = 3/8` and
`Tr(T₃L²)/Tr(Y²) = 3/5` exactly, on the actual charge matrices (`WeinbergIndex`). Since unit 190 the
abelian generator sits inside the invariant form. The physics is not proved: that `sin²θ_W` equals
the ratio at unification needs a coupling-matching input. The bridge is stated over ℝ, with its
hypothesis shown to be satisfiable (`ERRATUM 557` found the version over ℚ unsatisfiable). **The
author's choice:** the matching.

### 58. DECISION — `PROOF_STRATEGY` §3's worked example names a gap that closed six weeks ago

`formalisation/PROOF_STRATEGY.md`, line 76 on `main`, uses the signature work as §3's only worked
example of "a partial C is a legitimate B". That gap has since closed. The file lives on `main`, which
only the author edits, and replacing the only worked example is a choice about how to teach the
method. **The author's choice:** whether and how to replace it.

### 59. The Born rule, Gleason's theorem and Wigner's theorem are cited, not derived

**Assumed.** SPINE link L21 says the cascade produces quantum mechanics. The Hilbert-space side is
machine-checked: GNS, unitary groups, the Schrödinger equation and Stone's converse. The step from
"there is an inner product" to "`|⟨ψ, φ⟩|²` is a probability" rests on three citations: the Born
rule, Gleason (1957) and Wigner (1931). None is proved, none is stated as a hypothesis, and none is in
Mathlib.
**Bites.** `QuantumLineage.lean` and `ThreeLineages.lean`. Eight files mention the three.
**Cuts.** Anti-conservative in `QuantumLineage`'s prose, and in one place false: `ERRATUM 561` records
a docstring that invokes Gleason's theorem.
**Today.** Stands.

### 60. The two Higgs vacua are chosen, not derived

**Assumed.** The Pati–Salam symmetry breaking is built as linear algebra around two specific vectors,
`vac` and `vacEW`. There is no potential on either Higgs field, so the vacua are inputs.
**Cuts.** Anti-conservative if read as physics: the breaking pattern is what these two vectors give,
not what the cascade forces.
**Today.** Narrowed by units 203–227:
- Every rank-one first vacuum is gauge-equivalent to the chosen one.
- For the question of `U(3)`, `vac` is a representative. A pair `(X, Φ)` leaves `U(3)` unbroken exactly
  when `X` has rank one, `Φ ≠ 0`, and `ΦᴴΦ` commutes with `(XᴴX)ᵀ`.
- The number of broken generators decides the joint group.

What remains a choice is a rank-one `X` and a compatible `Φ`. The count decides the group once the
pair is given; it does not choose the pair. The entry's own sentence *"a different vector has a
different stabiliser"* was false and is corrected in place (`ERRATUM 690`).

---

## What to repair first — the source's priority list

These are the assumptions no file disclosed, so a reader could not have found them. The source ranks
them by what would be repaired first. Its ranks are kept here even where the item has since moved.

1. **Entry 2** — `CascadeData`'s fields. The highest leverage in the ledger.
2. **Entry 9** — the overlapping `su(3)`/`su(2)` blocks, machine-refuted, in a file graded GENUINE.
   The refutation is now a theorem, and the correct embedding into Pati–Salam is proved.
3. **Entry 5** — which tensor factor decomposes; parity violation rests on it.
4. **Entry 4** — the seed's ⋆-structure. Narrowed on 20 September to the pointed-cone input and the
   unrepaired header.
5. **Entry 16** — the trace state as the vacuum.
6. **Entry 17** — two Hilbert spaces for one cascade level.
7. **Entry 18** — the KO-dimension-2 files. Both of the two that needed it now carry a disclosure.
8. **Entry 12** — multiplicativity and the moments. Much narrowed; the premise is decided on every
   model the estate has, and is open for `A_F` on `H_F`.
9. **Entry 24** — the Weinberg-angle formula.
10. **Entry 26** — infinite total mass on a measure called a probability measure.

The source adds two gaps that are in documents rather than in Lean:
- the `g = g₃` caveat (entry 13) is missing from `PROPOSED_TAG_CHANGES` row 23;
- the Clifford model's signature-(2, 2) form (entry 22) is recorded in no audit document.

## What this ledger deliberately leaves out

- **Missing proofs.** They are in `WALLS.md` and the unlock watchlist.
- **Discharged hypotheses.** A theorem that assumes exactly what it proves is needed is mathematics,
  not modelling.
- **Hollow files.** They prove nothing, rather than assume too much; they are in `TRUE_LEDGER`.
- **Two exceptions**, because the choice in them infects files that are not hollow: `CascadeData`'s
  fields (entry 2) and `CascadeUniqueness`'s `n ≤ 4` (entry 7).

## Errata found while writing this digest

None in the source. The digest does not re-verify every clause of the source against the Lean; it
restates the source's own amended text. Its counts — 57 entries, eleven decisions, one `axiom` — were
counted on the source at the commit named above.
