# Chain Theory ↔ the Tree of Reality

**A working reading of A. D. Wissner-Gross's *Chain Theory*, kept alongside the Tree of Reality
so the two programmes can be studied together.**

Started 25 October 2026, on first reading of the Chain Theory release of 23 October 2026.
Maintained by Mark E. Mala (Ekram Alam) with Claude. Corrections from the Chain Theory side are
very welcome — the whole point of this folder is to get the correspondences *right*.

## Why this folder exists

Chain Theory and the Tree of Reality both start from finite-dimensional quantum systems and ask
how much of physics follows. Both check their finite computations in Lean 4. Both grade every
statement and refuse to let a correspondence with physics pass as a derivation. Chain Theory
names "the spectral action on a finite noncommutative geometry" among its sibling programmes;
that is the tradition the Tree of Reality grows from. The two were built independently, from
opposite ends — Chain Theory from the measurement side (what a distillation can fix), the Tree
from the algebraic side (what a self-referential seed generates) — and they land on the **same
objects**: the qubit, the pair of qubits as spacetime, the ququart, the qutrit, and the group
S(U(3)×U(2)).

When two constructions that share no premises meet at the same place, each is evidence for the
other, and each can lend the other what it has. These notes try to map that exchange precisely.

## Contents

| File | What it holds |
|---|---|
| [01_chain_theory_in_its_own_words.md](01_chain_theory_in_its_own_words.md) | The axiom, the six definitions, the read cap, the six genres, the α count, the grading system — stated as the Chain Theory documents state them, with box numbers |
| [02_dictionary.md](02_dictionary.md) | A two-way translation of vocabulary: link / genre / read / wash / hub / web ↔ seed / cascade / lineage / link grade / gap |
| [03_where_the_constructions_meet.md](03_where_the_constructions_meet.md) | Object-by-object correspondences, with each side's own grade, and what each coincidence validates |
| [04_what_chain_theory_offers_the_tree.md](04_what_chain_theory_offers_the_tree.md) | Open items in the Tree (by link and gap code) for which Chain Theory has a candidate mechanism |
| [05_what_the_tree_offers_chain_theory.md](05_what_the_tree_offers_chain_theory.md) | Open items in Chain Theory (by box number) for which the Tree has a candidate theorem |
| [06_questions_to_work_on_together.md](06_questions_to_work_on_together.md) | Concrete joint problems, each with a sketch of how it could be run |
| [07_reading_log.md](07_reading_log.md) | What was read in full, what only in part, and what is not yet understood — so the Chain Theory side can see exactly where these notes may be wrong |
| [08_results_first_pass.md](08_results_first_pass.md) | First results: Q3 (the 172-record count inside M₁₆ — numerator transfers, denominator needs a third qubit first available at M₂₅₆, the count lives in the record space not the algebra), Q2 (yes: his β is our γ₁), Q1 (inputs located). Script in `scripts/chain_theory/` |
| [09_results_second_pass.md](09_results_second_pass.md) | Second results: Q4 (the hub bound transfers as a theorem about frames of M₄ and M₃ — Lean file `lean_verify/chain_theory/Q4HubBound.lean` — and not as tensor factors), R9′ (factor exchange is carried by anti-automorphisms, chiral-half exchange by the improper element — two separate binaries), Q6 (the read cap locates on the Tree's gluon corner; no finite mechanism), Q1 (the quartic computed from the compendium and tested against the window; the window itself in tension with m_H under Standard-Model running), Q5 (two different threes sharing an oriented Z₃; Lean `Q5TwoThrees.lean`), Q10 (every register generated; L11 narrows 4 → 2) |
| [10_results_third_pass.md](10_results_third_pass.md) | Third results: R13 confirmed (σ is forced on the Tree's Pati–Salam 16 — no PS-invariant Majorana entry, the unique SM-singlet one lies in (10̄,1,3); with σ the window gives m_H = 125.20 GeV at a seesaw-consistent scale ~10¹⁴ GeV, vacuum metastable as in the SM), R10 refuted (the electron web fits only at M₆₅₅₃₆) |

## The Tree of Reality, for Chain Theory readers

The shortest statement: a single minimal non-commutative algebra, **M₂(ℂ)** — the observable
algebra of one qubit — is forced by the logic of self-reference (Lawvere's fixed-point theorem),
and grows by one repeated operation, *take the algebra of endomorphisms*, into
M₄(ℂ) → M₁₆(ℂ) → M₂₅₆(ℂ) → …. Three lineages run up the tree: what things *are* (End), how they
*transform* (Aut), and how they are *known* (the inner product). Spacetime dimension four
(Cl₄(ℂ) ≅ M₄(ℂ)), the Pati–Salam gauge structure on M₁₆ = M₄ ⊗ M₄ with colour as 4 → 3⊕1, and
the quantum apparatus (GNS, Stone, Schrödinger) appear as branches. Every link in the chain is
graded GENUINE / PARTIAL / POSTULATE / OPEN against machine-checked Lean proofs; the current
scoreboard is 6 · 13 · 3 · 2 over 24 links, with six named gaps G1–G6.

- *The Tree of Reality* (capstone, full grading): [10.5281/zenodo.23011897](https://doi.org/10.5281/zenodo.23011897)
- *The Staked Gaps* (the gaps and what we predict for them): [10.5281/zenodo.23338726](https://doi.org/10.5281/zenodo.23338726)
- *The Forced and the Chosen* (every modelling choice, declared): [10.5281/zenodo.23356221](https://doi.org/10.5281/zenodo.23356221)
- Lean estate: this repository, `lean_verify/`
- Prose: [infinitography.com](https://infinitography.com)

## Chain Theory, for Tree readers

- Announcement: https://theinnermostloop.substack.com/p/chain-theory
- *A Parameter-Free Candidate for the Fine-Structure Constant from Entangled Qudits* (the "alpha Letter"): https://alexwg.org/publications/ChainTheoryAlpha.pdf
- *Chain Theory: Toward Fundamental Physics from Distilling Networks of Entangled Qudits* (compendium, release 0.1, 754 pp): https://alexwg.org/publications/ChainTheoryCompendium.pdf
- *Chain Theory: An Introduction* (slides): https://alexwg.org/publications/ChainTheoryTalk.pdf
- Lean check of the α count: https://alexwg.org/publications/ChainAlpha.lean

## A note on working together

Neither programme is finished, and both say so in print: Chain Theory with its 198 open results
and its ungraded page, the Tree with its thirteen PARTIAL links, two OPEN ones, and six named
gaps. What is striking is not that either has arrived but that two people, starting from
different intuitions — one from what a measurement can certify, one from what a self-referential
seed must generate — have independently drawn the same objects at the same places: a qubit at the
bottom, a pair of qubits as spacetime, a ququart above it, a qutrit beside it, and
S(U(3)×U(2)) as the symmetry of the pair. That is the kind of coincidence that, in the history of
physics, has usually meant that something real is being described from two sides.

The questions in file 06 are written so that either answer is progress. If the α count runs
inside M₁₆ and gives the same number, both programmes gain a derivation they did not have. If it
gives a different number, both learn exactly which definition carries the weight. If the hub
bound transfers to M₄, a postulate becomes a theorem; if it does not, a dependency becomes
visible. The point of putting the two constructions side by side is not to decide between them
but to find out, together, how much of reality one sentence can hold — and which sentence.

## House rules for this folder

1. Every Chain Theory claim is cited to a box or theorem number and carries *Chain Theory's own
   grade* (theorem / conditional theorem / open result / conjecture / "by name").
2. Every Tree claim carries the Tree's own grade (GENUINE / PARTIAL / POSTULATE / OPEN) and link
   or gap code.
3. Where one side has a theorem and the other a conjecture at the same object, that is recorded
   as *support*, not as a verdict.
4. Nothing here is a review. It is a map for working together.
