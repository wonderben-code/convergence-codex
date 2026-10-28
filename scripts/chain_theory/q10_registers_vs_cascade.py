#!/usr/bin/env python3
"""Q10 — Chain Theory's registers against the Tree's cascade, and what Conjecture 0 does to L11.

Chain Theory, Theorem 1.7 (Conjecture 0, a conditional theorem under its move table): link ends come
in exactly three registers, 2, 3, 4, and the six genres are their six pairings. Theorem 2.9 excludes a
one-dimensional end. Refined Gaps R11 pre-registered: "no register 5-8".

The Tree: the cascade M2 -> M4 -> M16 -> M256 (carriers 2, 4, 16, 256), and L13's split of the
level-2 carrier, 4 = 3 + 1. L11 (PARTIAL): M16 = M4 (x) M4 is genuine, but "(4,2,2) with no
alternatives" is not proved: every factorisation a.b.c = 16 decomposes M16.
Run: python3 -I scripts/chain_theory/q10_registers_vs_cascade.py
"""
from itertools import combinations_with_replacement

levels = [2 ** (2 ** n) for n in range(4)]          # 2, 4, 16, 256
splits_of_4 = {3, 1}                                   # L13: 4 = 3 + 1
registers = [2, 3, 4]

print("(1) EVERY CHAIN THEORY REGISTER IS A CASCADE LEVEL OR A SPLIT OF ONE")
for r in registers:
    where = f"cascade level {levels.index(r) + 1} (carrier of M_{r})" if r in levels else \
            ("L13 split of the level-2 carrier, 4 = 3 + 1" if r in splits_of_4 else "NOT GENERATED")
    print(f"  register {r}: {where}")
print("  The cascade's higher levels 16 and 256 are, in Chain Theory, composites rather than registers:")
print("  16 = the two ends of a (4,4) link; 256 holds the alpha object's third qubit (Q3).")

print("\n(2) THE WALKED BRANCH NEVER NEEDS A REGISTER ABOVE 4  (R11: no register 5-8)")
pieces = {"Pati-Salam factors of M16 (4,2,2)": [4, 2, 2],
          "after L13 (colour 3, lepton 1, isospin 2, 2)": [3, 1, 2, 2],
          "fundamentals of su(4), su(3), su(2)L, su(2)R": [4, 3, 2, 2]}
for name, dims in pieces.items():
    print(f"  {name:<48} {dims}  max = {max(dims)}")

print("\n(3) CONJECTURE 0 AS A CONSTRAINT ON L11'S ALTERNATIVES")
triples = sorted({tuple(sorted(t, reverse=True)) for t in combinations_with_replacement([1, 2, 4, 8, 16], 3)
                  if t[0] * t[1] * t[2] == 16}, reverse=True)
print("  three-factor decompositions a.b.c = 16 (L11):", triples)
admissible = [t for t in triples if all(f == 1 or f in registers for f in t)]
with_qutrit = [t for t in admissible if 4 in t]
print("  every nontrivial factor a register (2, 3 or 4):", admissible)
print("  ... and a 4 present, so that L13 can supply the qutrit register:", with_qutrit)
print(f"  L11's residue narrows from {len(triples)} alternatives to {len(with_qutrit)}, the walked (4,2,2) among them.")
print("  The two survivors differ only in reading the second 4 as one ququart or as a qubit pair;")
print("  Chain Theory's Theorem 65.2 makes that same identification (a hub pair read as one qudit of dimension four).")

print("\n(4) THE SIX GENRES AS END-PAIRS ON THE TREE'S OBJECTS")
genres = [
    ((2, 2), "M4 = M2 (x) M2, the Clifford algebra of L8", "spacetime, conjectured", "agree (Q2: his beta is our gamma1)"),
    ((3, 2), "colour 3 (x) isospin 2: the quark doublet", "electromagnetic, the photon (Conjecture 1)",
     "agree on the algebra: su(3)+su(2)+u(1), dim 12, acts on both"),
    ((4, 2), "the Pati-Salam (4,2,1) block, where SU(2)L acts", "the weak sector", "agree"),
    ((3, 3), "the gluon corner C3 (x) C3* of End(C4) (Q6)", "the strong sector", "agree"),
    ((4, 3), "the 4 (x) 3* corner of End(C4)", "the Higgs / Yukawa sector", "open: see note"),
    ((4, 4), "End(C4) = C4 (x) C4*, on which M16 acts", "the Higgs", "open: see note"),
]
for g, tree, ct, verdict in genres:
    print(f"  {str(g):<7} Tree: {tree:<50} Chain Theory: {ct:<44} -> {verdict}")
print("  Note: the Tree's Higgs is the (1,2,2) bidoublet, 2 (x) 2 = 4 dimensions; Chain Theory's Higgs is the")
print("  closed hub read (200.1), a qubit pair read as one ququart (65.2). The two may be one object, met through")
print("  65.2; that is a correspondence to test, not a result.")
