#!/usr/bin/env python3
"""R6, the open half — (a) is there room for a third copy? (b) can the alpha Letter's exchanges X, Y be operations?

R6 (sixth pass) realised the alpha star's two read-link copies of the shared qutrit as the left and right actions of
the GNS standard form L^2(M_3), making the 169 two-letter products independent. Two things were left:
  (a) the held link's copy: a third copy of M_3 commuting with both;
  (b) the Letter's exchanges X (of reads) and Y (of links), as given in its backup table (q3_alpha_count_in_M16.py):
      X = -swap on kept edges, +1 on mixed edges; Y = +1 on kept edges, -swap (moving the qubit letters) on mixed edges.
Every automorphism of the full operator algebra B(H) on a finite-dimensional H is a conjugation r -> Psi r Psi^{-1}
(linear) or, for an antilinear symmetry, r -> Psi conj(r) Psi^{-1}. So X is an operation on the space iff some
invertible Psi satisfies Psi r = X(r) Psi on every record r: a linear system in Psi, solved exactly here.
Run: python3 -I scripts/chain_theory/r6b_third_copy_and_exchanges.py
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
Lm = lambda a: np.kron(a, I3)
Rm = lambda b: np.kron(I3, b.T)

# (a) the commutant of the two standard-form copies on L^2(M_3)
gens = [Lm(g) for g in GM] + [Rm(g) for g in GM]
A = np.vstack([np.kron(g, np.eye(9)) - np.kron(np.eye(9), g.T) for g in gens])
comm_dim = 81 - np.linalg.matrix_rank(A, tol=1e-9)
print("(a) THE THIRD COPY")
print(f"    commutant of the left and right copies of M_3 on L^2(M_3): dimension {comm_dim} (the scalars)")
print("    so no third copy commuting with both fits in the standard form; it needs a new tensor factor (a new qutrit,")
print("    identified with the first only by a matching): Chain Theory's copy model, not a consequence of the inner product.")

# (b) the records and the exchanges, exactly as the Letter's backup table builds them
slot_dim = {0: 8, 1: 3, 2: 8, 3: 3}
linkswap = {0: 0, 1: 3, 2: 2, 3: 1}
letters = {0: [np.kron(np.kron(Lm(g), I2), I2) for g in GM], 1: [np.kron(np.kron(np.eye(9), p), I2) for p in PA],
           2: [np.kron(np.kron(Rm(g), I2), I2) for g in GM], 3: [np.kron(np.kron(np.eye(9), I2), p) for p in PA]}
products = [((a, i), (b, j)) for a, b in itertools.combinations(range(4), 2)
            for i in range(slot_dim[a]) for j in range(slot_dim[b])]
idx = {r: k for k, r in enumerate(products)}
ops = [letters[a][i] @ letters[b][j] for (a, i), (b, j) in products]
kept = lambda r: {r[0][0], r[1][0]} in ({0, 2}, {1, 3})
Xm = np.zeros((169, 169)); Ym = np.zeros((169, 169))
for r in products:
    k = idx[r]; (a, i), (b, j) = r
    if kept(r):
        Xm[idx[((a, j), (b, i))], k] = -1; Ym[k, k] = 1
    else:
        Xm[k, k] = 1
        s = tuple(sorted([(linkswap[a], i), (linkswap[b], j)])); Ym[idx[s], k] = -1
image = lambda M, k: sum(M[m, k] * ops[m] for m in range(169) if M[m, k] != 0)


def implementers(M, antilinear):
    """Dimension of {Psi : Psi r = M(r) Psi for every record r} (r -> conj(r) if antilinear)."""
    N = 36
    rows = []
    for k in range(169):
        r = ops[k].conj() if antilinear else ops[k]
        Xr = image(M, k)
        # Psi r - Xr Psi = 0, as a linear map on vec(Psi) (row-major): (I (x) r^T) - (Xr (x) I)
        rows.append(np.kron(np.eye(N), r.T) - np.kron(Xr, np.eye(N)))
    Big = np.vstack(rows)
    return N * N - np.linalg.matrix_rank(Big, tol=1e-8)


print("(b) THE EXCHANGES AS OPERATIONS ON THE SPACE (H = L^2(M_3) (x) C^2 (x) C^2, 36 dims)")
for name, Mx in (("X (exchange of reads)", Xm), ("Y (exchange of links)", Ym)):
    lin, anti = implementers(Mx, False), implementers(Mx, True)
    print(f"    {name}: solutions Psi of Psi r = {name[0]}(r) Psi — linear: {lin}, antilinear: {anti}")
# controls: the method must find solutions where they exist
print(f"    control 1, the identity on records: linear solutions {implementers(np.eye(169), False)} (> 0 expected)")
# control 2: the exchange actually induced by J (x) SWAP (antilinear; J x = x*), with its conjugation signs computed
P = np.zeros((9, 9))
for r_ in range(3):
    for c_ in range(3):
        P[c_ * 3 + r_, r_ * 3 + c_] = 1                  # vec(x) -> vec(x^T)
SW = np.zeros((4, 4)); SW[0, 0] = SW[3, 3] = SW[1, 2] = SW[2, 1] = 1
U = np.kron(P, SW)
basis = np.array([o.ravel() for o in ops]).T
MJ = np.linalg.lstsq(basis, np.array([(U @ o.conj() @ U.T).ravel() for o in ops]).T, rcond=None)[0].real
assert np.allclose(basis @ MJ, np.array([(U @ o.conj() @ U.T).ravel() for o in ops]).T, atol=1e-8)
print(f"    control 2, the exchange J (x) SWAP induces (with its signs): antilinear solutions {implementers(MJ, True)} (> 0 expected);")
print(f"      it differs from the Letter's X on {int((np.abs(MJ - Xm) > 1e-9).any(axis=0).sum())} of 169 records")
print()
print("VERDICT: a zero-dimensional solution space means no conjugation, linear or antilinear, realises the exchange: X and")
print("Y are rules on the record labels, not operations on the Hilbert space the Tree's lineages build. With (a), R6 is settled:")
print("the inner-product lineage supplies the two read copies and nothing more; the third copy and the exchanges are Chain")
print("Theory's own structure.")
