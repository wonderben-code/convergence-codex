#!/usr/bin/env python3
"""R10 — do Chain Theory's particle webs fit in the Tree's fourth level, M256? (The Refined Gaps v1, §6.8)

Pre-registered: "Chain Theory's sixteen particle webs ... embed in M256 = M16 (x) M16 with the hub assemblies
as M4 factors and the core triangles in the colour blocks ... Kill-condition: a particle web of Chain Theory
requires more tensor factors than M256 provides, or fits only at M65536."

A web is a network of maximally entangled pairs; a faithful realisation puts every site in its own tensor
factor (a pair needs both ends as factors). The Tree's levels are M_{2^(2^k)}: 2, 4, 16, 256, 65536, 2^32.
By Q4's Theorem D a qutrit is never a tensor factor of a level (3 does not divide 2^m); it sits only as the
corner of a 4 (L13: 4 = 3 + 1). So a qutrit costs a factor 4, a ququart 4, a qubit 2.
(Chain Theory's copy model, one copy per pair, only makes every count larger.)

Web anatomies, from the compendium (release 0.1):
  electron   9 sites / 10 links: core triangle (3 qutrits), one hub assembly (ququart + 3 leg qubits, a pair among
             them), 2 dock qubits                                                        (152.1, 197.5, ch. 113)
  muon       13 / 15: core triangle, two hub assemblies, 1 dock qubit, 1 leaf qubit      (152.1: measures 27+2*40+6+4)
  tau        17 / 20: core triangle, three hub assemblies, 2 leaf qubits                 (152.1: measures 27+3*40+0+8)
  up quark   3 / 2: a qutrit with its two dock qubits                                     (ch. 39 check; fig. 164 text)
  W word     5 / 4: (4,2),(2,3),(3,2),(2,4) chain: two ququarts, one qutrit, two qubits   (ch. 72, fig. 80)
  photon word 6 / 5: alternating (3,2) chain: three qutrits, three qubits                 (eq. 187)
  alpha star (the fine-structure object of Q3): one qutrit with three qubit links          (alpha Letter, Theorem 1)
Run: python3 -I scripts/chain_theory/r10_webs_in_the_cascade.py
"""
import math

webs = {  # name: (qutrits, ququarts, qubits, sites, links)
    "alpha star (Q3)": (1, 0, 3, 4, 3),
    "up quark": (1, 0, 2, 3, 2),
    "W word": (1, 2, 2, 5, 4),
    "photon word": (3, 0, 3, 6, 5),
    "electron": (3, 1, 5, 9, 10),
    "muon": (3, 2, 8, 13, 15),
    "tau": (3, 3, 11, 17, 20),
}
levels = [2 ** (2 ** k) for k in range(6)]  # 2, 4, 16, 256, 65536, 2^32
name_of = {2: "M2", 4: "M4", 16: "M16", 256: "M256", 65536: "M65536", 2 ** 32: "M_2^32"}

print(f"{'web':<18}{'sites/links':>12}{'site product':>14}{'faithful (qutrit -> corner of 4)':>34}   smallest level   fits M256?")
for name, (q3, q4, q2, s, l) in webs.items():
    assert q3 + q4 + q2 == s, name
    plain = 3 ** q3 * 4 ** q4 * 2 ** q2
    faithful = 4 ** (q3 + q4) * 2 ** q2
    lvl = next(L for L in levels if L >= faithful)
    print(f"{name:<18}{f'{s}/{l}':>12}{plain:>14}{f'2^{int(math.log2(faithful))} = {faithful}':>34}   "
          f"level {levels.index(lvl) + 1} ({name_of[lvl]}){'':>3}{'yes' if faithful <= 256 else 'NO'}")
print()
print("The electron's core triangle and hub fill M256 exactly (4^4 = 256), as R10 pictured; its five qubits do not fit.")
print("R10's kill-condition, 'fits only at M65536', is met by the electron and the photon word; the muon and tau need")
print("the level after that. The alpha star, the up quark and the W word fit at or below M256.")
