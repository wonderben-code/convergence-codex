# Questions to work on together

Each is a concrete computation or proof that needs both programmes, ordered roughly by how
quickly it could be run. Each names what it would show either way.

## Q1 · Does the Higgs quartic land in the window?

> **Status 28 Oct 2026:** run from the compendium's own numbers — see `09_results_second_pass.md`.

**Needs.** Chain Theory's exact quartic (202.1): an element of ℚ(√2, √3), stated at the
Higgs-form sinks. The Tree's coupling window (L15), stated as rational bounds.

**Run.** Evaluate the quartic numerically; compare against the window; note the normalisation
conventions on both sides (λ vs λ/2 vs λ/4).

**If inside:** two independent constraints on the same number agree — support for both. **If
outside:** one normalisation or one derivation has a specific, findable issue. Either way a
half-day's work.

## Q2 · Read L8's Lean file against chapter 3-5

**Needs.** The Tree's `Cl4IsoM4` (the Clifford algebra of four-dimensional space is M₄(ℂ), and
only for n = 4 is Cl_n a cascade level). Chain Theory's chapter 3-5: "the Clifford relation at
four generators met … β = diag(1,1,−1,−1), the three alphas squaring to the identity and
anticommuting."

**Run.** Check that Chain Theory's four generators at the (2,2) link are the Tree's Clifford
generators under the identification M₂ ⊗ M₂ ≅ M₄. If so, the Tree's "only in dimension 4"
theorem applies to Chain Theory's (2,2) cell directly.

**Shows.** Whether Conjecture 2 can cite a theorem for the dimension. Essentially a reading
exercise; no new proof needed.

## Q3 · Run the 172-record count inside M₁₆

**Needs.** Chain Theory's object: a shared qutrit with three links to qubits, two read; letters
at slots (8, 3, 8, 3); exchanges X and Y; weight law √k_r; readout dimension 24·36·36. The Tree's
object: M₁₆ = M₄ ⊗ M₄ with 4 → 3⊕1 on one factor, which contains a qutrit (the colour triplet)
tensored with qubits (the M₂ factors of the other M₄).

**Run.** Construct the qutrit–qubit links inside M₁₆ using the Tree's explicit matrices; define
"read" as a conditional expectation in a MUB of the qutrit; count the records that survive the
Tree's automorphisms; weight by the exchange eigenvalues; divide by the readout dimension.

**Shows.** Three possibilities, all informative. (a) The same number, 1/137.036 — then the α
candidate has a second, algebraic derivation and the Tree has its first coupling constant.
(b) A different number — then the "end rule" or the weight law depends on something the Tree's
object does not have, and both sides learn exactly what. (c) No well-defined count — then
"read" does not translate to the Tree's third lineage as cleanly as 02 suggests, which is itself
worth knowing.

## Q4 · Does the hub bound transfer to M₄?

> **Status 28 Oct 2026:** answered — yes as a theorem about frames (additive); no as tensor factors. See `09_results_second_pass.md`.

**Needs.** Chain Theory's 197.3: "a hub assembly is a ququart carrying a qubit pair among its
qubit legs, the pair takes two of its four ends and every move applies at a site with spare
alone, so a hub assembly admits at most the third generation." The Tree's M₄ = M₂ ⊗ M₂ with its
Lean-checked tensor structure.

**Run.** State "legs", "pair", "spare", and "move" as operations on tensor factorisations of M₄;
attempt the bound as a Mathlib theorem about M₄.

**Shows.** If it goes through: the Tree gets a theorem-grade upper bound of three generations
(L14 upgraded), and Chain Theory's 197.3 gets a second proof in a different formalism. If it
does not: the bound depends on the network structure (webs, moves) and not on M₄ alone, which
tells Chain Theory which of its definitions carries the weight.

## Q5 · Do the three attach sites carry a quaternionic structure?

> **Status 28 Oct 2026:** answered — no at the operator level (Lean: no quaternion action in odd dimension); the two threes share an oriented cyclic Z₃. See `09_results_second_pass.md`.

**Needs.** Chain Theory's three core sites of the closed (3,3) triangle (83.1, 197.4). The
Tree's ℍ ⊂ M₂(ℂ) with imaginary units i, j, k.

**Run.** Check whether the three attach-site operators, or the three hub-assembly attachments at
the electron/muon/tau webs, satisfy i² = j² = k² = ijk = −1 up to the twirl.

**Shows.** If yes: Chain Theory's open result 197.5 ("three generations as attach sites") and
the Tree's postulate L14 ("three generations are the imaginary quaternions") are the same
statement, and each side's half-proof completes the other's. If no: the two threes are
different threes, and the coincidence of the number is a coincidence.

## Q6 · Does the read cap give L23 a mechanism in the spectral-triple language?

> **Status 28 Oct 2026:** location yes, mechanism no; the drafted statement is false for colour-blind D. See `09_results_second_pass.md`.

**Needs.** Chain Theory's read cap (d₁d₂ ≤ 6 from decomposable positive maps; Størmer,
Woronowicz, Choi). The Tree's colour block M₃ ⊗ M₃ inside M₁₆ and its Dirac operator D.

**Run.** Ask whether "no single read fixes both ends of a (3,3) link" has a statement about the
spectral triple (A, H, D) restricted to the colour block — e.g. that no conditional expectation
onto a MUB sub-algebra commutes with D on that block.

**Shows.** If a statement exists and is provable: L23 moves from "wall" to "mechanism stated,
continuum limit open" — a real change in the Tree's scoreboard, from a Chain Theory idea.
If none exists: the read cap is a feature of the network picture that the algebraic picture
does not see, which is a sharp fact about where the two pictures differ.

## Q7 · Does the graph Laplacian meet the heat kernel?

**Needs.** Chain Theory's curvature as the graph Laplacian washed over the ladder (90.2) and
the cosmological term at the depth exponent (115.1). The Tree's spectral action
Tr f(D/Λ) with the exponential cutoff forced (L19) and the target a₂ coefficient (gap G5).

**Run.** At a single finite level (M₄ or M₁₆), compute Chain Theory's Laplacian curvature on
the ladder induced by the cascade, and the Tree's Tr e^{−tD²} expansion for the finite D.
Compare the leading coefficients as functions of the level.

**Shows.** If they track: Chain Theory's open field equation has a continuum target (the
Einstein–Hilbert term of the spectral action), and the Tree's G5 has a finite stand-in that can
be computed before G2 is built. If they do not: the two gravities are different objects, and
Conjecture 2 and L22 are about different things despite both being at the (2,2) / M₄ cell.

## Q8 · Does the Born circle close?

**Needs.** Chain Theory's Born rule from the wash (35.1), whose premises import "the Hilbert
space of a qudit and the pair as a ray." The Tree's GNS construction (L21), which builds the
Hilbert space from the inner-product lineage but cites the Born rule.

**Run.** Chain the two: Tree GNS → Hilbert space of a qudit → Chain Theory wash → Born
readout. Check that nothing is used twice and nothing is circular.

**Shows.** If it closes: between the two programmes, the probability rule is derived from the
inner product with no cited physics — a result neither has alone. If it does not: one of the
two imports is doing hidden work, and the chain shows which.

## Q9 · Can Definition 1.6 derive the three lineages?

**Needs.** Chain Theory's "known": what all reads fix jointly under every matching and every
exchange. The Tree's L7 (POSTULATE): that End, Aut and ⟨·,·⟩ are *the* three lineages.

**Run.** Ask whether a structure that is (i) a thing, (ii) acted on by matchings, and (iii)
known only through what the matchings leave fixed, is forced to have exactly those three aspects
and no fourth.

**Shows.** If yes: the Tree's only structural postulate becomes a theorem, with a knowledge
clause from Chain Theory as the premise. If no: the fourth aspect, whatever it is, is something
both programmes have missed.

## Q10 · Can End-iteration reproduce the move table behind Conjecture 0?

> **Status 28 Oct 2026:** answered — every register (2, 3, 4) is a cascade level or L13's split; Conjecture 0 narrows L11 from 4 alternatives to 2. See `09_results_second_pass.md`.

**Needs.** Chain Theory's move table (the moves that admit registers 2, 3, 4 and no others).
The Tree's cascade and colour split.

**Run.** List the registers Chain Theory's networks ever require; check each is a cascade level
(2, 4, 16, …) or a split of one (3 = 4 − 1); check whether any move produces a register the
cascade cannot.

**Shows.** If every register is generated: Conjecture 0 has a derivation from a growth law.
If some register is not: either the Tree's cascade is missing a branch or Chain Theory's move
table admits something the Tree would call unforced — either way, a precise place to look.

---

## A note on how to run these

Both programmes keep their finite computations in Lean 4, with different libraries (Chain
Theory in Core Lean; the Tree in Mathlib). Q1, Q2, Q3 and Q5 can be done in either, or in a
Python notebook first. Q4, Q6, Q8, Q9 are proofs and belong in Mathlib, where the Tree's
estate already has the objects. Q7 and Q10 are investigations before they are proofs.

None of these needs either programme to be right about physics. They are questions about
whether two finite constructions agree, and if they do, where.
