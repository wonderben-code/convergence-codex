# Closing report — the stand-down of 26 September 2026

*Written on the main terminal's stand-down order, which the author confirmed, after hardening unit
243. This is the last word of the cloud prover's run: 28 July to 26 September 2026, 45 working days.*

## The order, and what was done with it

The order had four parts: finish the current unit only; write five ledger files into
`lean_verify/paper_f/ledgers/`; push everything; stand down. Each was carried out:

1. **Unit 243 finished, and no unit started after it.** `paper_f/ProductKronSum.lean` was built and
   gated (zero unaccepted defects over 44 modes and 25 scanners), then committed and pushed to both
   repositories, with its dates fixed.
2. **The five files are written.** Their exact paths are at the end of this report.
3. **Everything is pushed** to branch `claude/infinitography-formalisation-fbqxf3` in both
   `wonderben-code/convergence-codex` and `wonderben-code/codex-internal`. The commit that adds these
   files is the snapshot stop point.
4. **Standing down.** The hourly routine that told this session *"Continue … Do not stop"*
   (`trig_0197oUiCitTsgLkhH6bLyEqZ`, *Infinitography formalisation — continuous work loop*) was
   **disabled, not deleted**, at 09:51 UTC. Otherwise it would have woken the session at 10:12 and
   contradicted the stand-down. To resume the loop, re-enable that routine; its prompt and schedule
   are unchanged.

Where writing the ledgers turned up an error in an earlier unit, it is logged as an erratum — in
the ledger concerned, or in this report — and not fixed in the source. There are three; see *Errata
found at the stop* below.

---

## 1. What shipped, end to end

**The estate builds.** `lake build PaperF` completes: **5,091 jobs**, green, at unit 243. The whole
build contains exactly **one `sorry`** and **one `axiom`**. Both are in the author's
`lean_verify/_proof_004_logos.lean`, both predate the campaign, and both are documented honestly:
- the `sorry` in `phase_transition_symmetry_breaking` (the token is at line 228; the build reports the
  declaration at line 180), whose clause-(2) shape is machine-refuted (`ERRATUM 34`);
- `axiom GibbsMeasure` (line 86), a measure with no defining property (assumptions entry 53).

What to do with both is running decision list items 16 and 17.

**Axioms in the campaign's own files.** The campaign's files use only the standard three axioms —
`propext`, `Classical.choice`, `Quot.sound` — with one disclosed exception. `PhaseTransitionStatement`
refutes the logos statement with the axiom in place, so its declarations that mention `GibbsMeasure`
carry that axiom by construction; its header says so. No campaign declaration depends on the
`sorry`. These claims rest on the per-file `#print axioms` records in `TRUE_LEDGER` and on each unit's
scoped `--axioms` audit. The full-estate axiom sweep (the gate's `--slow` mode) was not re-run at the
stop.

**The registers.** These are the working ledgers in `codex-internal/formalisation/`, counted at the
stop by `check_ledger.py --stats`:

| register | what it holds at the stop |
|---|---|
| `TRUE_LEDGER.md` | **1,230** Lean files graded, **312,334** lines: GENUINE 1,142 · HOLLOW 59 · MIXED 15 · PARTIAL 12 · NOT_BUILT 2. The campaign opened on 107 files. |
| `SPINE.md` | the 24-link chain from nothing to everything: **6 GENUINE · 13 PARTIAL · 3 POSTULATE · 2 OPEN** |
| `WALLS.md` | nine walls: **three closed** (W6, W7, W8) and **six open**, each with its staircase and failing step |
| `ASSUMPTIONS_LEDGER.md` | **57** assumptions, numbered 1–36 and 40–60; eleven are author decisions |
| `ERRATA.md` | **699** errata, numbered to 700, with 414 never issued. Each records something this campaign said, or the estate said, that was wrong, with the correction quoted beside it. |
| `PROPOSED_TAG_CHANGES.md` | 32 items, none withdrawn; **no published tag has been moved** |
| `UNLOCK_WATCHLIST.md` | the re-sweep register. `RE-SWEEP #86` (unit 240) read the 101 live items, and the live set stood at 102 after it |
| `PROGRESS_LOG.md` | **1,846** dated entries over 45 working days, and the running decision list, items 1–30 |

**What fell** — mathematics that is now machine-checked and was not on 28 July. These are
highlights; the registers hold the full account.

- **Three walls closed.**
  - W6 (9 August): the Stein class and the Sobolev space `W^{1,2}(γ)` are one class, in every
    dimension.
  - W7 (8 August): the real Clifford classification and the spin identification; the mod-8
    periodicity table followed on 18 August.
  - W8 (12 August): a non-trivial reflexive domain `D ≃ (D →𝒄 D)` in ω-CPOs.
- **W1's named step.** Reflection positivity for the massive lattice field (9 August), then lifted to
  measures, with OS1 stated and proved in finite volume.
- **Lorentz and spin.**
  - `SO⁺(1,3)` is the identity component of O(1,3), with no hypothesis.
  - The double cover `SL₂(ℂ) → SO⁺(1,3)`, surjective, with kernel `{±1}`.
  - The Clifford spin group modulo `{±1}`, identified with `SL₂(ℂ)` modulo `{±1}`.
  - The complex Clifford classification in every rank.
- **Analysis.**
  - The Gaussian Poincaré inequality in every dimension, at every variance, beyond polynomials.
  - Hermite completeness.
  - Wick's theorem at every order for the finite-volume Gaussian field (27 August).
  - Stone's theorem in both directions, for bounded generators, in any C⋆-algebra (15 September).
  - Frobenius's theorem on real division algebras.
- **The Standard-Model side, computed on actual objects.**
  - `sin²θ_W = 3/8` as a trace ratio on the chiral 16, with the dimension numerology refuted.
  - The perturbative anomaly table on the 16.
  - The Standard Model algebra embedded in the Pati–Salam algebra.
  - The Pati–Salam → Standard Model breaking classified: the unbroken group
    `U(3) ≅ (SU(3) × U(1))/ℤ₃` as a compact topological group, and the number of broken generators
    deciding the group, for pairs of vacua at every rank-one first vacuum (units 199–227).
- **The seed and its ⋆-structure.**
  - `M₂(ℂ)` as the unique minimal seed over ℂ.
  - Every ⋆-structure on `Mₙ(ℂ)` classified: `n/2 + 1` classes up to conjugacy.
  - A faithful ⋆-representation selects the conjugate transpose.
- **The order-one chain** (units 168–243), rung 2 of wall W9. On the estate's model bimodules the
  order-one condition is solved:
  - with the real structure `J` and the grading;
  - with generations and on products;
  - with the self-adjoint solutions counted and classified.

  The tensor-sum shape that the spectral-action factorisation needs is decided **exactly**: forced for
  every operator only for one full matrix algebra at one generation.
- **Refutations**, each a theorem, and each worth as much as a proof:
  - a non-trivial `D ≅ (D → D)` over sets;
  - the Standard Model algebra in `su(4)` on the blocks used;
  - *(4,0) and (0,4) excluded structurally*;
  - `3/8` from the dimensions;
  - the estate's own comparison route for W3, proved insufficient.

  One more finding is a measurement, not a theorem: W4's uniform target is false above the critical
  point, by diagonalising the estate's own transfer matrices.

**The five stop-point files** (§5 below) summarise the registers for a reader who has an evening,
not a week.

---

## 2. The honest state of the theory

**The spine is 6 GENUINE, 13 PARTIAL, 3 POSTULATE and 2 OPEN.** No rating moved in units 75–243.
Five recompute addenda re-read the table against the work, and every later unit that touched a link
recorded *rating unchanged*. The work sharpened what is known without changing a headline. That is
the honest result, and inflating it would be the one real failure available here.

**What is genuinely established.** Six links are theorems as their headlines state them:
- existence from self-reference (L1);
- the seed (L3), over ℂ;
- the cascade of algebras (L4);
- its irreversibility (L5);
- the spacetime Clifford algebra `Cl₄(ℂ) ≅ M₄(ℂ)` (L8);
- colour `4 → 3 ⊕ 1` (L13).

Each GENUINE link is a theorem about the estate's objects. Whether those objects are the physical
ones is the separate question the assumptions ledger answers, link by link.

**What the theory rests on that is not proved.** Among the 57 assumptions, these carry the most. The
assumptions ledger has all of them, with its own priority list of what to repair first.
- `CascadeData` stores its conclusions as fields (entry 2).
- Which tensor factor decomposes, which is what parity violation rests on (entry 5).
- The trace state as the vacuum (entry 16).
- The multiplicativity of the spectral weight, with its moments set to 1 (entry 12).
- The Higgs vacua are chosen, not derived (entry 60).
- Three generations as the imaginary quaternions is a postulate (entry 25).
- The Born rule, Gleason and Wigner are cited, not derived (entry 59).

**Where it stops, and why** — the six open walls:

| wall | what | where it stops |
|---|---|---|
| W1 | the lattice OS axioms | the infinite-volume limit; there is no projective system to take it along |
| W2 | the continuum field and OS reconstruction | an unbounded self-adjoint Hamiltonian. Mathlib has no unbounded operators at all |
| W3 | Peierls symmetry breaking | the estate's comparison is proved insufficient (`O(n)` against `O(n²)`) |
| W4 | the mass gap | a uniform sub-top eigenvalue bound, which measurement says is false above `β_c` |
| W5 | Einstein from `a₂` | the heat-kernel expansion — unbounded operators again |
| W9 | the CCM classification | rung 2 on CCM's own `H_F`: a sub-bimodule of a product with three generations and `ℍ` |

**The two OPEN spine links are the two real walls**: L22, general relativity (W5), and L23, the
mass gap (W1–W4). One missing subject — unbounded self-adjoint operators — sits behind W2 and W5
both.

**The spectral-action chain, stated exactly.** The chain *spectral action → exponential cutoff →
three moments → couplings* has a premise: that the Dirac operator is a tensor sum. The estate has
proved whether the conditions on a Dirac operator force that premise, on every model it has:
- order-one forces it for every operator only for one full matrix algebra at one generation;
- with generations, or on a product of two or more factors, it is not forced — with or without `J`
  and the grading, some operator meeting every condition is not a tensor sum.

The estate has no Dirac operator for the cascade itself, and CCM's `A_F` on `H_F` is none of its
models. There, the question is **not settled either way**. So the claim that the spectral action
leaves "zero free parameters" is not established. Tag ruling T5 and assumptions entry 12 carry this.

**What the estate does not contain.** It contains no gauge theory, no interacting measure, no
infinite-volume limit, no continuum field, no curved example, no heat-kernel coefficient, no
declaration of `ℂ ⊕ ℍ ⊕ M₃(ℂ)`, and no Dirac operator for the cascade. Every physical number except
`3/8` and the Higgs coupling window is uncomputed.

---

## 3. What to do next, with more time

In order of what each step unlocks.

1. **W9 rung 2 on CCM's actual `H_F`.** This is the direct continuation of units 228–243:
   - build the isotypic decomposition of a finite-dimensional bimodule over a product of real,
     complex and quaternionic matrix algebras, as an object;
   - compute order-one on it, with `J` and the grading;
   - decide the tensor-sum premise for `A_F` on `H_F`.

   Every tool it needs exists except the decomposition itself: `OrderOneCommutant` already handles
   sub-bimodules, and `ProductKronSum` handles products. It also extends rung 2's first half to real
   and quaternionic factors, which that half does not yet cover.
2. **A Dirac operator for the cascade** (`cascadeDirac`). This waits on the author's ruling on what
   counts as a derivation of the fermion content (running list item 8). With it, the order-one
   results apply to the cascade and not only to models.
3. **Unbounded self-adjoint operators.** This is a Mathlib-scale project: densely defined operators,
   adjoints, closures, essential self-adjointness, the semigroup-to-generator step. It is the one
   missing subject behind W2's step 2b and W5's rung 4, so it is the largest single unlock available.
4. **W4, after the author's threshold ruling** (item 10). Prove the restricted statement with a
   Dobrushin-type or high-temperature cluster estimate; Mathlib has neither.
5. **W3, after the logos rulings** (items 16–17). Build a comparison model whose output is not
   sublinear.
6. **`K`-theory of finite algebras**, for W9 rung 3. It is absent from the estate and from Mathlib.
7. **`RE-SWEEP #87`.** This was not run, because of the stand-down. `RE-SWEEP #86` (unit 240) read
   the live watchlist against units 233–239. Units 241–243 each added a status line to the items they
   bear on — *the cascade's `D` as a tensor sum*, and in unit 241 also the `Triple` item — but have
   not been swept against the whole list.
8. **Upstreaming to Mathlib**, which is the author's call (items 6, 7 and 25). The strongest
   candidates are the `D∞` construction, the Hermite material, the combinatorial half of Isserlis, and
   the `pderiv` bridges.

---

## 4. What needs a founder ruling

The **26 tag rulings** are in `PROPOSED_TAG_CHANGES.md`, and they are not repeated here. Everything
below is **not** a tag question. Three numberings share the word *decision* (`ERRATUM 683`):
- *item n* is the running list in `PROGRESS_LOG.md`;
- *entry n* is the assumptions ledger;
- early-August *DECISION 1–6* are items 16–21.

**The rulings that unblock the most work — if you rule on only five, rule on these.**

| ruling | what it unblocks |
|---|---|
| **Item 8** — what would count as a derivation of the cascade's fermion content? | the `N = 96` item; the KO-6 real structure item; a genuine finite spectral triple for the cascade, and with it next step 2 |
| **Item 20** (early-August DECISION 5) — what is the spectral action's fluctuation measure: what fluctuates, and with what weight? | every Bakry–Émery tag; spine L20 |
| **Item 10** — restate W4's uniform bound to hold below a threshold? | W4. Until then, a proof attempt at `β ≠ 0` attacks a statement the numbers say is false |
| **Entry 48, with item 27** — which real structure `J` is the estate's, and how the algebra acts on the antiparticle sector | the real spectral triple; spine L18 |
| **Item 12** — should `SpectralTripleBimodule.Triple` require CCM's two grading axioms? | what the estate's "real spectral triple" means. Option (a) costs the non-scalar witness at every size |

**The rest of the running list, one line each.**
- **Theory-building.** Item 1 (why the cascade stops at `M₂₅₆`), item 2 (the fermion mass
  hierarchy), item 3 (what "canonical operation" means), item 4 (generations as a named postulate or
  a derivation target), item 14 (the Born rule, Gleason and Wigner as inputs or as targets), item 26
  (Lorentzian signature: forced, or chosen and exhibited), item 28 (`SU(n)` or another group with the
  same Lie algebra), item 29 (which tensor factor decomposes), item 30 (whether the spectral weight is
  multiplicative).
- **The logos file.** Item 16: amend or freeze `phase_transition_symmetry_breaking`. Item 17: replace
  the `GibbsMeasure` axiom with `FiniteGibbs`'s definition.
- **Estate housekeeping.**
  - Item 5: the 28 duplicated declaration names, which stop the estate loading into one Lean
    environment.
  - Item 11: merge two copies of one argument.
  - Item 15: retire `smToPS` in favour of `smToPSY`.
  - Item 22: keep `TRUE_LEDGER`'s line-count column.
  - Item 23: the two definitions of reflection positivity.
  - Item 9: close watchlist items whose objective was proved by an unforeseen route. This is the same
    question as entry 51.
- **Published-claim questions without a proposal.** Item 6 (spine L2's tag, now that `D∞` exists),
  item 7 (anything stated from Wick's theorem), item 24 (the algebraic Lovelock classification).
  `PROPOSED_TAG_CHANGES.md` gives a lean on each; none is a proposal.
- **Already covered by tag rulings.** Item 13 is T26. Items 18 and 19 are T21. Item 21 (the polynomial
  cutoff) is now only whether to generalise `SpectralAction.lean`'s definition.
- **Upstreaming.** Item 25, the `pderiv` bridges.

**The assumptions ledger's decision entries not already named above.**
- Entry 47: what *compatible* means for the torus covariances. This blocks W2's step 1a.
- Entry 49: the real Clifford classification as a table or as one theorem.
- Entry 50: which of three OS-axiom numberings to use.
- Entry 52: whether to namespace the `F`-series.
- Entry 54: the frame for curvature components.
- Entry 55: whether finite-volume OS shadows finish the lattice-field item.
- Entry 56: which contraction the contracted Bianchi identity means. This blocks that identity, the
  next step on the curvature chain.
- Entry 57: the coupling matching behind the Weinberg angle.
- Entry 58: `PROOF_STRATEGY` §3's worked example on `main`, which only the author can edit.

---

## Errata found at the stop

Producing the ledgers turned up three errors. Each is logged here or in the ledger concerned, and
no source was reopened.

1. **The tag register's re-check of 20 September, row 10**, says assumptions entry 41 *"still
   stands"*. Entry 41 was retired by proof on 15 August: `SL2Connected.identityComponent_eq` is
   unconditional. This is logged in `PROPOSED_TAG_CHANGES.md` beside this file, and tag ruling T8 is
   written from the corrected reading.
2. **This campaign's own draft of `WALLS.md` beside this file** listed *whether the doubled algebra
   acts faithfully* as open for W9. That was settled on 14 September: the real regular bimodule of
   `M₂(ℂ)` is not faithful (`CentralBimoduleKernel.regAction_not_injective_M2C_over_R`), and §W9.4
   of the source closes that route. The draft was corrected before it was committed; it is recorded
   here because it happened.
3. **A stray probe file, committed on 6 September and never compiled.** `lean_verify/ProbeTwo.lean`
   is 8 lines: one `example` against `DualDegreeExact`. It was committed in `782031c`
   (*EvenDegreesReach*). It has no `TRUE_LEDGER` row, and no lakefile root reaches it, so `lake build`
   has never compiled it. `check_ledger.py --roster` reports it at the stop (*UNROSTERED*,
   *UNREACHABLE*); the gate prints that mode but does not count it. It proves nothing and nothing
   depends on it. It should be deleted, or rostered as NOT_BUILT; it is left untouched at the stop.

---

## 5. The five files — exact paths

In repository `wonderben-code/convergence-codex`, branch `claude/infinitography-formalisation-fbqxf3`:

1. `lean_verify/paper_f/ledgers/SPINE_SCOREBOARD.md` — every link tagged, the counted scoreboard,
   and the files behind each GENUINE link.
2. `lean_verify/paper_f/ledgers/WALLS.md` — every wall, its staircase and the exact failing step, as
   of unit 243.
3. `lean_verify/paper_f/ledgers/ASSUMPTIONS_LEDGER.md` — all 57 assumptions, stated plainly.
4. `lean_verify/paper_f/ledgers/PROPOSED_TAG_CHANGES.md` — 26 rulings, each with a recommendation.
5. `lean_verify/paper_f/ledgers/CLOSING_REPORT.md` — this file.

The working registers these summarise are in `wonderben-code/codex-internal`, same branch, under
`formalisation/`. Where a summary and its register differ, the register is right.
