#!/usr/bin/env python3
"""R8 — Chain Theory's "known" generates exactly the pairing, and nothing else: an exact check of the
First Fundamental Theorem for matrices (Procesi 1976; Razmyslov 1974) at small size.

Lean (`R8KnownGivesPairing.lean`) proves the k = 1 case for every n: the only linear functional fixed by every
matching (conjugation) is c * trace, whose GNS inner product <x, y> = tr(x* y) is the Tree's third lineage (L21).
Here, for n <= 3 and k <= 3: compute the whole space of multilinear functionals f(X_1, ..., X_k) on M_n that are
invariant under every conjugation (infinitesimally: sum_s f(..., [A, X_s], ...) = 0 for all A in gl_n), and check
that the trace monomials tr_sigma (sigma in S_k: products of traces of products along the cycles of sigma) span it.
If they do, everything the matchings fix is built from the carrier's product and its trace pairing: no fourth primitive.
Run: python3 -I scripts/chain_theory/r8_known_generates_pairing.py
"""
import itertools
import numpy as np


def cycles(perm):
    seen, out = set(), []
    for s in range(len(perm)):
        if s in seen:
            continue
        c, t = [], s
        while t not in seen:
            seen.add(t); c.append(t); t = perm[t]
        out.append(c)
    return out


def check(n, k):
    basis = [(a, b) for a in range(n) for b in range(n)]
    Eab = {(a, b): np.eye(n)[:, [a]] @ np.eye(n)[[b], :] for (a, b) in basis}
    N = len(basis)
    # ad_A on vec(X), row-major: vec(AX - XA) = (A (x) I - I (x) A^T) vec X
    def ad(A):
        return np.kron(A, np.eye(n)) - np.kron(np.eye(n), A.T)
    blocks = []
    for (a, b) in basis:
        adA = ad(Eab[(a, b)])
        D = sum(np.kron(np.kron(np.eye(N ** s), adA), np.eye(N ** (k - 1 - s))) for s in range(k))
        blocks.append(D.T)                     # invariant F satisfies F @ D = 0  <=>  D^T F^T = 0
    Mstack = np.vstack(blocks)
    sv = np.linalg.svd(Mstack, compute_uv=False)
    inv_dim = int((sv < 1e-9).sum()) + max(0, N ** k - len(sv))
    # trace monomials as row vectors indexed by tuples of basis matrices
    mons = []
    for perm in itertools.permutations(range(k)):
        row = []
        for tup in itertools.product(basis, repeat=k):
            Xs = [Eab[t] for t in tup]
            val = 1.0
            for c in cycles(perm):
                P = np.eye(n)
                for s in c:
                    P = P @ Xs[s]
                val *= np.trace(P)
            row.append(val)
        mons.append(row)
    Mon = np.array(mons)
    r_mon = np.linalg.matrix_rank(Mon, tol=1e-9)
    # are the monomials invariant, and do they span the invariant space?
    inv_ok = np.allclose(Mon @ np.hstack([b.T for b in blocks]), 0)  # each monomial killed by every D
    return inv_dim, r_mon, inv_ok, len(mons)


print("R8 — invariant multilinear 'knowledge' on M_n versus trace monomials (FFT check)")
print("   n  k   invariant functionals   trace monomials (|S_k|)   their rank   monomials invariant   span equal")
for n, k in [(2, 1), (3, 1), (2, 2), (3, 2), (2, 3), (3, 3)]:
    d, r, ok, m = check(n, k)
    print(f"   {n}  {k}   {d:>20}   {m:>22}   {r:>10}   {str(ok):>19}   {str(d == r and ok):>10}")
print("k = 1: one invariant, the trace (Lean, every n). k = 2: two, tr(XY) and tr(X) tr(Y): the pairing.")
print("n = 2, k = 3: six monomials span five dimensions (one Cayley-Hamilton relation); n = 3, k = 3: all six independent.")
print("In every case the invariants are exactly the span of trace monomials: built from the product and the trace pairing alone.")
