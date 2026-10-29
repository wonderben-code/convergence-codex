#!/usr/bin/env python3
"""R6 — can the Tree's third lineage (the inner product) supply Chain Theory's "one copy per link"?

Q3 (first pass) found that the alpha Letter's 169 two-letter products, realised with the shared qutrit as ONE tensor
factor, span only 66 dimensions: the Letter's two copies Q1, Q2 of the shared qutrit (one per read link) collapse.
R6 (The Refined Gaps v1, §6.4) asks for a construction of the copies from the inner-product lineage alone.

The inner-product lineage, applied to the qutrit's algebra M_3, is the GNS construction on the trace state: the
standard form L^2(M_3) = M_3 with <x, y> = tr(x* y). It carries two commuting copies of M_3, left multiplication and
right multiplication, the Tree's End(A) = A (x) A^op (L12, R9'), exchanged by the modular conjugation J x = x*.
Test: realise Q1 by left and Q2 by right multiplication on L^2(M_3), each read link's qubit by its own factor
(H = L^2(M_3) (x) C^2 (x) C^2, 36 dimensions), and count the rank of the 169 products. For comparison, realise both
copies by the same left multiplication in the same space.
Run: python3 -I scripts/chain_theory/r6_record_space_from_gns.py
"""
import itertools
import numpy as np


def gell_mann():
    E = lambda i, j: np.eye(3)[:, [i]] @ np.eye(3)[[j], :]
    return [E(0, 1) + E(1, 0), -1j * E(0, 1) + 1j * E(1, 0), E(0, 0) - E(1, 1), E(0, 2) + E(2, 0),
            -1j * E(0, 2) + 1j * E(2, 0), E(1, 2) + E(2, 1), -1j * E(1, 2) + 1j * E(2, 1),
            (E(0, 0) + E(1, 1) - 2 * E(2, 2)) / np.sqrt(3)]


GM = [g.astype(complex) for g in gell_mann()]
PA = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]), np.diag([1, -1]).astype(complex)]
I2, I3 = np.eye(2), np.eye(3)
Lm = lambda a: np.kron(a, I3)            # x -> a x on vec(x), x in M_3 (row-major)
Rm = lambda b: np.kron(I3, b.T)          # x -> x b


def letters(two_copies):
    Q1 = [np.kron(np.kron(Lm(g), I2), I2) for g in GM]
    Q2 = [np.kron(np.kron(Rm(g) if two_copies else Lm(g), I2), I2) for g in GM]
    q1 = [np.kron(np.kron(np.eye(9), p), I2) for p in PA]
    q2 = [np.kron(np.kron(np.eye(9), I2), p) for p in PA]
    return {0: Q1, 1: q1, 2: Q2, 3: q2}


def rank_169(two_copies):
    S = letters(two_copies)
    prods = []
    for a, b in itertools.combinations(range(4), 2):
        for x, y in itertools.product(S[a], S[b]):
            prods.append((x @ y).ravel())
    assert len(prods) == 169
    return np.linalg.matrix_rank(np.array(prods), tol=1e-9)


r1, r2 = rank_169(False), rank_169(True)
print("R6 — THE RECORD SPACE FROM THE INNER-PRODUCT LINEAGE")
print(f"  both qutrit copies as the same (left) action:           rank of the 169 products = {r1}")
print(f"  the GNS standard form's two copies (left and right):    rank of the 169 products = {r2}   (all independent)")

# the modular conjugation J (x -> x*) exchanges the copies: J L(a) J = R(a*)
x = np.random.default_rng(0).normal(size=(3, 3)) + 1j * np.random.default_rng(1).normal(size=(3, 3))
a = GM[3]
lhs = (a @ x.conj().T).conj().T          # J L(a) J x = (a x*)*
print(f"  J L(a) J = R(a*) on L^2(M_3): {np.allclose(lhs, x @ a.conj().T)}  (J exchanges the two copies)")

# does J (with the qubit swap) reproduce the Letter's exchange of reads X? On a kept-edge product L(a)R(b) with Hermitian
# letters, J gives R(a)L(b) = L(b)R(a): +swap. The Letter's X is -swap there and the identity on mixed edges, which
# J (x) SWAP instead exchanges in pairs.
a_, b_ = GM[0], GM[5]
kept = Lm(a_) @ Rm(b_); Jkept = Rm(a_.conj()) @ Lm(b_.conj())
print(f"  on a kept-edge record L(a)R(b): J gives L(b)R(a) (+swap): {np.allclose(Jkept, Lm(b_) @ Rm(a_))};"
      " the Letter's X gives -swap there and fixes the mixed edges, which J (x) SWAP exchanges:")
print("  the modular conjugation exchanges the copies but is not the Letter's X (sign and mixed-edge action differ).")
print()
print("VERDICT: the inner-product lineage supplies exactly two commuting copies of a shared qudit (left and right), and with")
print("them the 169 products become independent (169, against 66 with one copy). 'One copy per link' is derived for TWO")
print("links (the alpha star's two read links); a third commuting copy (the held link) is not in a standard form, and the")
print("Letter's exchange X is not the modular conjugation. Partial: the numerator's record space for the read pair, yes;")
print("the full 172-record count with its exchanges, no.")
