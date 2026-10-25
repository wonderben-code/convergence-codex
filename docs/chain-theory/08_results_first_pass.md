# Results — first pass on Q1, Q2, Q3

**Date:** 25 October 2026. Computations in `scripts/chain_theory/`. Everything below is a first
pass by one side; the Chain Theory side's corrections are invited and will be recorded in
`07_reading_log.md`.

## Q3 · The 172-record count inside M₁₆ — answered: outcome (b), with a surprise

**Script:** `scripts/chain_theory/q3_alpha_count_in_M16.py` (numpy + sympy; exact where a number
is claimed). Run with `python3 -I scripts/chain_theory/q3_alpha_count_in_M16.py`.

**Part A — the Letter's count, reproduced from its rules.** Letters at four slots (8, 3, 8, 3);
169 two-letter products plus 3 commutators = 172 records; the exchanges X (of reads) and Y (of
links) built as 172 × 172 involutions exactly as the Letter's backup table prescribes (kept
edges: X = −swap, Y = 1; swapped edges: X = 1, Y = −swap; commutators: X = Y = −1). The script
checks that X and Y are commuting involutions, then:

```
tr X = 82, tr Y = 70, tr XY = -8
sectors (X,Y): (+,+) 79  (+,-) 48  (-,+) 42  (-,-) 3
numerator  = 79 + 48√2 + 42√3 + 3√6
N          = 24 · 36 · 36 = 31104
1/α        = 137.0359991895661550291837…
```

The closed forms in a = 8, b = 3 — ½(a²−a+b²−b) + 2ab, 2ab, ½(a²+a+b²+b), ½b(b−1) — are
asserted equal to the census. **The Letter's arithmetic is reproduced exactly.** This checks the
rules' arithmetic; it does not test the rules, which is what the Letter itself says of its two
hand methods.

**Part B — what M₁₆ contains, by explicit 16 × 16 matrices.** The Tree's M₁₆ = M₄ ⊗ M₄ with the
colour split 4 → 3⊕1 on one factor (L13) and M₄ = M₂ ⊗ M₂ on the other (L4) was realised
explicitly, with Gell-Mann letters on the colour 3 and Pauli letters on each qubit.

| Check | Result |
|---|---|
| B1 — the 8 qutrit letters, 3 + 3 qubit letters are present and independent in M₁₆ | rank 8, 3, 3; all 14 together rank 14 ✓ |
| B2 — the qutrit commutes with both qubits (the Letter's shared qudit, one copy per link) | ✓ |
| B3 — Pauli letters anticommute at each qubit; the two qubits commute with each other | ✓ ✓ |
| B4 — rank of the 169 two-letter products realised as 16 × 16 matrices | **66**, not 169 |
| B5 — the 3 ⊗ 2 ⊗ 2 block (colour 3 with both qubits) | dimension 12; operator space 144 |

Three findings follow, and they answer Q3 at its outcome (b): *the definition that carries the
weight is identified.*

1. **The numerator transfers unchanged.** It depends on the end dimensions (3, 2) alone — the
   Letter's own lemma on sector sizes says so, and the script confirms it — so inside M₁₆ the
   numerator is identically 79 + 48√2 + 42√3 + 3√6. The Tree contributes the *object* (the
   qutrit is forced by 4 → 3⊕1, the two qubits by M₄ = M₂ ⊗ M₂) but adds nothing to, and
   subtracts nothing from, the number.

2. **The denominator needs a third qubit that M₁₆ does not have.** N = 24 · 36 · 36: the two
   read links' whole operator spaces (36 each) are present in M₁₆ as M₃ ⊗ M₂ twice; the 24 is the
   traceless part of the *unread* third link — a third qubit maximally entangled with the qutrit,
   carrying the state (the Letter's Theorem 1 configuration). M₁₆ = (3⊕1) ⊗ 2 ⊗ 2 has exactly two
   qubits beside the colour 3. **A third qubit is first available at M₂₅₆ = M₁₆ ⊗ M₁₆ — the
   Tree's fourth level, the same level at which L6 says the Chamseddine–Connes–Marcolli algebra
   fits.** So the α object, if it lives on the Tree, lives at level four. This is a new
   correspondence, not previously in 03.

3. **The record space is not the matrix algebra.** The 169 products, realised as matrices, span
   only 66 dimensions, because the Letter's two *copies* Q₁, Q₂ of the one shared qutrit — "one
   copy per link" — become the *same* M₃ factor when the qutrit is a single tensor factor, and
   the 64 kept-edge records collapse onto the 9-dimensional M₃. The count lives in the Letter's
   **record space** (Definition 1.6, "known"; the "shared" clause of 1.3), which is network
   structure, not in the operator algebra of the shared system. Any attempt to derive the number
   from the algebra alone must first reconstruct the record space from the "one copy per link"
   clause. That clause is where the weight sits.

**What this means for both programmes.** For the Tree: the α object's ingredients are all forced
(qutrit, two qubits, a third at level four), but the number is not a property of the algebra;
L24 does not gain a coupling constant from the algebra alone. For Chain Theory: the result
localises precisely which definitions a derivation of the number depends on — "shared" (1.3) and
"known" (1.6) — and shows that the Tree's cascade supplies the object those definitions act on at
exactly its fourth level. The next step, if both sides want it, is to state the record space as
a construction over M₂₅₆ and ask whether the Tree's third lineage (the inner product) reproduces
the "one copy per link" clause or something else.

## Q2 · Are the (2,2) Clifford generators the Tree's? — answered: yes

The compendium (ch. 3-5) gives at the qubit pair "β = 1,0,0,0; 0,1,0,0; 0,0,−1,0; 0,0,0,−1
traceless and squaring to the identity and the three alphas squaring to the identity and
anticommuting with beta and among themselves at three of three, the Clifford relation at four
generators met." The Tree's `lean_verify/paper_f/F4_1e_CliffordMatrix.lean` builds Cl₄(ℂ) on
M₂ ⊗ M₂ from γ₁ = σ₃ ⊗ I₂, γ₂ = σ₁ ⊗ I₂, γ₃ = (σ₃σ₁) ⊗ σ₃, γ₄ = (σ₃σ₁) ⊗ σ₁, with every
square and anticommutator a checked theorem, and `F1_7_SpacetimeForced.lean : D2_is_Cl4` records
dim Cl₄(ℂ) = dim M₄(ℂ) = 16 with the algebra map from `CliffordAlgebra.lift`.

- The compendium's β **is** the Tree's γ₁ = σ₃ ⊗ I₂, entry for entry.
- The compendium's four generators (one β, three α) and the Tree's four γ are both Clifford
  generators on the same M₂ ⊗ M₂; the real signatures differ (the compendium's all square to +1;
  the Tree's quadratic form Q₄ has signature (2,2)), which over ℂ is immaterial: both generate
  Cl₄(ℂ) ≅ M₄(ℂ).
- So the (2,2) register of Chain Theory *is* the algebra of L8, and L8's "only in dimension 4"
  — that Cl_n(ℂ) is a level of the cascade for n = 4 and no other n — applies to it directly.

**Outcome:** Conjecture 2 can cite a theorem for the dimension. It cannot yet cite one for the
*metric* (that is Part VI's open programme and the Tree's L22), and nothing here touches that.

## Q1 · Higgs quartic inside the window? — inputs located, comparison not yet possible

- Chain Theory, Theorem 202.1: the quartic is "a Higgs face over a vacuum face squared", an
  exact element of ℚ(√2, √3), with the vacuum office 6561 (= 3⁸) at the fourth column and the
  hub-face office over 6561² and leg-face office over 256² (= 2⁸·2) at the Higgs word. The
  explicit numerical value was not extractable from the compendium text in this pass; it is
  defined relationally through the office tables.
- The Tree, L15: the window g²/N ≤ λ̃ ≤ g² with both endpoints sharp, N = 96 a recorded choice,
  and no scalar potential derived.

A comparison needs (i) Chain Theory's quartic as a number, and (ii) a common normalisation of λ
and of g. Both are obtainable; neither was in this pass. **Status: open, inputs identified.**

## R7 · Pell family on the Tree's Clifford lattice — holds, and sharpens

**Script:** `scripts/chain_theory/r7_r9_lattice_and_parity.py`. For each real signature sharing
Cl₄(ℂ), the integer isometry group O(Q; ℤ) was decided — by exhaustive enumeration for the
definite form, by explicit construction of an infinite-order element for the indefinite ones:

| Signature | O(Q; ℤ) | Witness |
|---|---|---|
| Euclidean (4,0) | **finite**, exactly 384 (signed permutations) | enumeration |
| Lorentzian (1,3) | **infinite** | integer isometry with spectral radius 5.83 |
| split (2,2) — the real form of the Tree's Q₄ | **infinite** | integer isometry with spectral radius 5.16 |

The prediction as stated holds: definite finite, indefinite infinite. **The refinement:** both
indefinite signatures that share Cl₄(ℂ) have infinite integer isometry groups, so Chain Theory's
"signature by existence" argument *excludes the Euclidean branch* at the Tree's fork L9 and does
*not* select Lorentzian (1,3) over split (2,2). It is a theorem-grade exclusion of one branch of
the fork, not a selection of the walked one. L9's residue narrows from "exclude Euclidean; choose
among (1,3)/(2,2)/(3,1)" to "choose among the indefinite three" — a smaller residue with a new
argument closing the first half.

## R9 · The improper element on M₄ = M₂ ⊗ M₂ — answered, and re-posed

Same script. With the Tree's γ₁ = σ₃⊗I₂, γ₂ = σ₁⊗I₂, γ₃ = (σ₃σ₁)⊗σ₃, γ₄ = (σ₃σ₁)⊗σ₁
(squares +1, +1, −1, −1; pairwise anticommuting), the chirality element is
γ₅ = γ₁γ₂γ₃γ₄ = σ₂ ⊗ σ₂, and the improper element P = γ₁ sends (γ₁, γ₂, γ₃, γ₄) ↦
(+γ₁, −γ₂, −γ₃, −γ₄) and anticommutes with γ₅ (swaps the Weyl spinors).

- P = σ₃ ⊗ I₂ is of the form A ⊗ I: **outcome (ii)** — it acts within the first tensor factor
  and leaves the second untouched; it is not the factor swap.
- **Two qualifications that change the question.** (1) Which factor P lives in is a property of
  the chosen Clifford basis, not of M₄. (2) γ₅ = σ₂ ⊗ σ₂ is *not* aligned with the
  factorisation — the Weyl split is not a tensor-factor split — so "which factor is left" is not
  a question M₄ = M₂ ⊗ M₂ can answer at all.

**Verdict:** R9 as stated is answered (shape ii, basis-dependent) and shown to be *posed on the
wrong object*. The Tree's L12 choice lives at M₁₆ = M₄ ⊗ M₄ (the Pati–Salam SU(2)_L × SU(2)_R
factors), and R9 is re-posed there as R9′: *does the improper element of Cl₄, lifted to M₁₆,
exchange the two M₄ factors or single one out?* A refinement, found by our own test, not a
confirmation — and recorded as such.

## What changed in this folder as a result

- 03: a new correspondence — the α object's third qubit is first available at M₂₅₆, the Tree's
  fourth level, where L6 places the CCM algebra.
- 04 / L24: "the Tree has the object but has never asked it for a number" is now sharper: the
  Tree has the object's ingredients; the number lives in the record space defined by "shared" and
  "known", not in the algebra.
- 06 / Q3: outcome (b) reached; a follow-on question is posed (the record space over M₂₅₆).
- 06 / Q2: yes.
- 06 / Q1: inputs located.

Nothing in the Tree's scoreboard changes. 6 · 13 · 3 · 2.
