# Results — sixth pass: L18 scoped, R8 (the three lineages), R6 (the copies), R5 (the Born circle)

**Date:** 29 October 2026. These are the remaining items of the v3 work list in *The Refined Gaps* v2
(DOI 10.5281/zenodo.23724193, §A8).
- Scripts in `scripts/chain_theory/`: `l18_cascade_to_pati_salam.py`, `r8_known_generates_pairing.py`,
  `r6_record_space_from_gns.py`, `r5_born_circle.py`.
- Lean: `lean_verify/chain_theory/R8KnownGivesPairing.lean` (the `ChainTheory` library; standard axioms
  only).
- Sources checked verbatim: Chamseddine–Connes, *Why the Standard Model*, J. Geom. Phys. 58 (2008) 38
  (arXiv:0706.3688), Props. 2.5, 2.8 and 3.2 and §§2.2–3.

## L18 · What connects the cascade to the σ-generating triple — scoped to four named items

**Chamseddine–Connes 2008, Prop. 2.8.** An irreducible finite geometry with centre ℂ ⊕ ℂ exists iff
dim H = 2k². It is M_k ⊕ M_k acting by left multiplication on M_k ⊕ M_k, with J(x, y) = (y\*, x\*). The
real form M₂(ℍ) ⊕ M₄(ℂ) (k = 4) is their *hypothesis* ("quaternion linearity … we choose the simplest
case"). Given it, the grading is unique (Prop. 3.2).

**Checked against the cascade.**
- k = 4 is the cascade's level 2, M₄ = End(M₂).
- Each half of H is the cascade's carrier M₄ (16 dimensions).
- On it, the left action of the first summand and the right action of the second (which, through J,
  reaches the carrier only as x ↦ xb\*) commute and generate all 256 dimensions: End(M₄) = M₁₆, the
  cascade's level 3. The left action is the Tree's covariant factor and the right its contravariant
  factor (R9′).
- M₂(ℍ) complexifies back to M₄(ℂ). This is the Tree's `RealDivisionQuaternionCase` at n = 2, and the
  Tree's own `realForm_not_determined` says the complexification cannot fix the real form.
- The grading's even part is ℍ_R ⊕ ℍ_L. On the carrier, ℍ_R ⊕ ℍ_L (left) and M₄ (right) generate
  (M₂ ⊕ M₂) ⊗ M₄ = 128 dimensions.
- The particle states ψ_{sc} (s ∈ 2_R ⊕ 2_L, c ∈ 4 = 3 ⊕ 1) are exactly the representation in which
  the fifth pass generated σ.

**The scope of L18.**

| Item | Status |
|---|---|
| k = 4, the carrier, M₁₆ as the generated algebra, left/right roles, 4 = 3 ⊕ 1 | supplied by the cascade |
| the real structure J(x, y) = (y\*, x\*), KO-dimension 6 | a ruling already made (27 Sep 2026) |
| the quaternionic real form M₂(ℍ) of the left summand | a choice the Tree shares with Chamseddine–Connes; L14's ground |
| the grading ℍ_R ⊕ ℍ_L | forced once the real form is chosen (CC Prop. 3.2) |
| the Dirac operator D (Yukawa and Majorana entries) | still to supply |

L18 stays **PARTIAL**, but its residue is no longer "nothing connects the triple to the cascade's
Hilbert space". It is one ruling already made, one shared choice, one forced consequence, and D. The
Higgs chain now reads:

> cascade (k = 4, M₁₆) + J (ruled) + ℍ real form (chosen) → Pati–Salam triple → σ generated
> (L13, L11) → m_H = 125.20 GeV.

## R8 · The three lineages from Chain Theory's "known" — confirmed

**Pre-registered (v1 §6.6).** A carrier, its symmetries, and a knowledge clause of Chain Theory's form
(Definition 1.6: "what all its reads, taken jointly, fix … whichever way basis directions are
matched") have exactly three aspects, carrier, symmetry and invariant pairing, and any fourth is a
function of these. *Kill-condition:* a fourth primitive that is not derived.

**The chain.**
1. The carrier Mₙ (End).
2. Its symmetries are the conjugations (Skolem–Noether, proved in the estate, L11).
3. What every symmetry fixes, for a single element, is the trace and nothing else. Lean,
   `eq_smul_trace_of_comm` (the infinitesimal form) and `eq_smul_trace_of_conj_invariant` (the
   finite form, using transvections, with no assumption on the characteristic), for every n.
4. The GNS construction on the trace state gives ⟨x, y⟩ = tr(x\*y), which is the Tree's L21.

So **the pairing is forced by the carrier and its symmetries under the knowledge clause.**

**No fourth.** Every invariant of several elements is a trace polynomial (the First Fundamental
Theorem for matrices, Procesi 1976 and Razmyslov 1974, cited). This was checked exactly by computing
the full invariant space against the trace monomials:

| n | k | invariants | trace monomials | span equal |
|---|---|---|---|---|
| 2 | 1 | 1 | 1 | yes |
| 3 | 1 | 1 | 1 | yes |
| 2 | 2 | 2 | 2 | yes |
| 3 | 2 | 2 | 2 | yes |
| 2 | 3 | 5 | 6 (one Cayley–Hamilton relation) | yes |
| 3 | 3 | 6 | 6 | yes |

Everything the matchings fix is built from the carrier's product and its trace pairing.

**Verdict: confirmed.** Chain Theory's three primitives (thing, matching, known) land on the Tree's
three lineages (End, Aut, ⟨·,·⟩), with the third *derived* from the first two. The kill-condition is
not met.

**A candidate grade move, for the founder's ruling.** v1 §6.6 said that if R8 holds, "L7 → GENUINE;
the Tree's only structural postulate becomes a theorem with a knowledge clause as its premise." The
strict reading is narrower:
- the k = 1 step is machine-checked;
- Skolem–Noether is machine-checked;
- the general "no fourth" (FFT) is cited and checked only at small n and k;
- the premise is Chain Theory's knowledge clause.

That is **POSTULATE → PARTIAL** (real theorems cover part, residue named: the FFT in general, and the
knowledge clause as a premise). It is proposed, not enacted. By the series' rule, a grade move earns
a capstone v2.

## R6 · The record space from the inner-product lineage — partly confirmed

**The test.** Q3 found that the α Letter's 169 two-letter products span only 66 dimensions when the
shared qutrit is one tensor factor. The inner-product lineage, applied to the qutrit's algebra, is the
GNS standard form L²(M₃). It carries exactly two commuting copies of M₃, left and right
multiplication (the Tree's End(A) = A ⊗ A^op), exchanged by the modular conjugation J x = x\*.

| Realisation of the two read-link copies | rank of the 169 products |
|---|---|
| the same (left) action | 66 (reproducing Q3) |
| the standard form's left and right actions | **169** (all independent) |

**Verdict: partly confirmed.**
- "One copy per link" is derived for **two** links (the α star's read pair) from the inner product
  alone. The refutation ("only the operator algebra, rank 66") is not met.
- Not derived: a third commuting copy for the held link, because a standard form has two, and the
  Letter's exchange of reads X. J exchanges the copies, but it acts as +swap on kept-edge records
  where X is −swap, and it moves mixed-edge records that X fixes.
- The full 172-record count, with its exchanges, is therefore not reconstructed from the Tree's
  lineages.

## R5 · The Born circle — closes

**Pre-registered (v1 §6.3).** GNS (Tree) → a qudit's Hilbert space → wash (Chain Theory) → Born
readout closes, with nothing used twice and nothing cited. *Kill-condition:* a second import ("the
pair as a ray", or the twirl's invariance) that the Tree does not provide. Chain Theory 35.1: "the
twirl of the whole identification group has exactly one pure fixed state, the maximally entangled
pair …, its amplitude the root of the Born readout."

**Checked for d = 2 and d = 3.**
1. R8 forces the trace state.
2. Its GNS vector Ω = 1 in L²(M_d) ≅ ℂ^d ⊗ ℂ^d is maximally entangled (flat reduced state). **Chain
   Theory's pair is the Tree's GNS vector.** Vectors enter only as rays.
3. The matchings (the Tree's Aut, conjugations x ↦ UxU\* = U ⊗ Ū) have commutant span{1, |Ω⟩⟨Ω|}
   (dimension 2), with unique pure fixed state Ω.
4. The twirl maps |x⟩⟨x| to p|Ω⟩⟨Ω| + (1 − p)·(flat), with **p = |⟨Ω, x⟩|²**: the Born square.

**Verdict: the circle closes.** No second import is needed: the Tree's GNS supplies the Hilbert space,
the rays and the pair, and its Aut lineage supplies the twirl. One step remains, and it is
interpretive: reading the weight as a probability. Gleason's route shares that step.

**For L21.** The Born row moves from "cited (Gleason)" to "derived, up to the interpretive step, by a
route through R8 and Chain Theory's wash". L21 stays PARTIAL. The assumptions-ledger entry (59) can be
narrowed to that one step, by founder ruling.

## The v3 tally after six passes

| Residual | Outcome |
|---|---|
| R1 | holds (re-posed: frames); R1′ formalised |
| R2 | **refuted** |
| R3 | half confirmed (bimodule shape), half refuted (Dirac shape) |
| R4 | consistent |
| R5 | **closes** (up to the interpretive step) |
| R6 | **partly confirmed** (two copies, rank 169; the third copy and X not supplied) |
| R7 | holds and sharpens (v1) |
| R8 | **confirmed**; candidate L7 move POSTULATE → PARTIAL |
| R9′ | answered; L12 re-posed |
| R10 | **refuted** |
| R11 | consistent; L11 narrowed from 4 to 2 |
| R12 | **refuted** |
| R13 | **confirmed**: σ forced, m_H = 125.20, σ generated |
| R14 | confirmed |
| R15 | confirmed (existence); the quaternion reading implies spontaneous CP violation |
| L18 | scoped to four named items |
| open | Q7 (gravity), the L11 choice, the third copy and X (R6), the general FFT in Lean |

The scoreboard is unchanged pending the founder's ruling on L7: 6 · 13 · 3 · 2.
