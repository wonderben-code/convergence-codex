#!/usr/bin/env python3
"""
Q3 — first pass: Chain Theory's 172-record count, and where its object sits in the Tree.

Two things are done here, kept strictly apart:

  PART A  reproduces the count of the alpha Letter (Wissner-Gross, 23 Oct 2026) from its own
          rules: letters at four slots (8, 3, 8, 3), 169 products + 3 commutators = 172 records,
          two commuting exchanges X (of reads) and Y (of links) acting as the Letter's Table I /
          backup slide prescribe, sector sizes by trace, weights sqrt(k_r) with
          k_r = (2 - X_r)(3 - Y_r)/2, readout dimension 24 * 36 * 36.
          This checks the arithmetic of the rules. It does not test the rules.

  PART B  asks what of that object the Tree of Reality's M_16 = M_4 (x) M_4 actually contains,
          using the Tree's own structures: the colour split 4 -> 3 (+) 1 on one factor (link L13)
          and the two-qubit factorisation M_4 = M_2 (x) M_2 of the other (link L4). Letters are
          realised as explicit 16 x 16 matrices and the questions are answered by linear algebra,
          not by assertion.

Everything is exact (sympy) where a number is claimed. Output is printed; the companion note
docs/chain-theory/Q3_first_pass.md records the findings.
"""
import itertools
import numpy as np
import sympy as sp

# ----------------------------------------------------------------------------------------------
# Letters: Gell-Mann (qutrit, 8) and Pauli (qubit, 3), as numpy complex arrays
# ----------------------------------------------------------------------------------------------
def gell_mann():
    l = []
    E = lambda i, j: np.array([[1 if (r, c) == (i, j) else 0 for c in range(3)] for r in range(3)], dtype=complex)
    l.append(E(0, 1) + E(1, 0))
    l.append(-1j * E(0, 1) + 1j * E(1, 0))
    l.append(E(0, 0) - E(1, 1))
    l.append(E(0, 2) + E(2, 0))
    l.append(-1j * E(0, 2) + 1j * E(2, 0))
    l.append(E(1, 2) + E(2, 1))
    l.append(-1j * E(1, 2) + 1j * E(2, 1))
    l.append((E(0, 0) + E(1, 1) - 2 * E(2, 2)) / np.sqrt(3))
    return l

def pauli():
    return [np.array([[0, 1], [1, 0]], dtype=complex),
            np.array([[0, -1j], [1j, 0]], dtype=complex),
            np.array([[1, 0], [0, -1]], dtype=complex)]

GM, PA = gell_mann(), pauli()
I2, I3, I4 = np.eye(2), np.eye(3), np.eye(4)

# ----------------------------------------------------------------------------------------------
# PART A — the Letter's count from its own rules
# ----------------------------------------------------------------------------------------------
print("=" * 78)
print("PART A — the alpha Letter's 172-record count, reproduced from its rules")
print("=" * 78)

# Slots: 0 = Q1 (qutrit copy, read 1), 1 = q1 (qubit, read 1), 2 = Q2 (qutrit copy, read 2), 3 = q2
slot_dim = {0: 8, 1: 3, 2: 8, 3: 3}
mirror = {0: 2, 1: 3, 2: 0, 3: 1}          # X: exchange of reads swaps read 1 <-> read 2
linkswap = {0: 0, 1: 3, 2: 2, 3: 1}        # Y: exchange of links moves the qubits, qutrit copies are one qudit

# Products: two letters at two different slots. Edge = unordered pair of slots.
products = []
for a, b in itertools.combinations(range(4), 2):
    for i in range(slot_dim[a]):
        for j in range(slot_dim[b]):
            products.append(((a, i), (b, j)))
assert len(products) == 64 + 9 + 4 * 24 == 169
# Commutators: at a qubit, two reads in different bases anticommute; their commutator is a record.
# Three of them (Lambda^2 of the 3 Pauli letters). They carry X = -1, Y = -1 (Table I / backup).
commutators = [("comm", k) for k in range(3)]
records = products + commutators
N_REC = len(records)
assert N_REC == 172
idx = {r: n for n, r in enumerate(records)}

def kept(edge):          # kept edges: both slots of the same kind of end (Q1Q2 or q1q2)
    (a, _), (b, _) = edge
    return {a, b} in ({0, 2}, {1, 3})

# Build X and Y as 172 x 172 matrices following the Letter's backup table:
#   kept edges (73):    X = -swap,  Y = +1
#   swapped edges (96): X = +1,     Y = -swap
#   commutators (3):    X = -1,     Y = -1
X = np.zeros((N_REC, N_REC)); Y = np.zeros((N_REC, N_REC))
for r in products:
    n = idx[r]
    (a, i), (b, j) = r
    if kept(r):
        # swap = exchange the two letters between the two slots of the edge
        s = ((a, j), (b, i)); X[idx[s], n] = -1.0; Y[n, n] = 1.0
    else:
        X[n, n] = 1.0
        # Y moves the qubit letters between q1 and q2 (and so between edges of the pair)
        a2, b2 = linkswap[a], linkswap[b]
        s = tuple(sorted([(a2, i), (b2, j)]))
        Y[idx[s], n] = -1.0
for c in commutators:
    n = idx[c]; X[n, n] = -1.0; Y[n, n] = -1.0

assert np.allclose(X @ X, np.eye(N_REC)) and np.allclose(Y @ Y, np.eye(N_REC)), "exchanges must be involutions"
assert np.allclose(X @ Y, Y @ X), "exchanges must commute"
trX, trY, trXY = round(np.trace(X)), round(np.trace(Y)), round(np.trace(X @ Y))
print(f"tr X = {trX}, tr Y = {trY}, tr XY = {trXY}   (Letter: 82, 70, -8)")
sectors = {}
for x in (+1, -1):
    for y in (+1, -1):
        sectors[(x, y)] = round((N_REC + x * trX + y * trY + x * y * trXY) / 4)
print("sector sizes (X,Y):", sectors, "  (Letter: (+,+)=79, (+,-)=48, (-,+)=42, (-,-)=3)")
assert sectors == {(1, 1): 79, (1, -1): 48, (-1, 1): 42, (-1, -1): 3}

# Weights: k_r = (2 - X_r)(3 - Y_r)/2, entering as sqrt(k_r)
r2, r3, r6 = sp.sqrt(2), sp.sqrt(3), sp.sqrt(6)
numerator = (sectors[(1, 1)] * 1 + sectors[(1, -1)] * r2 + sectors[(-1, 1)] * r3 + sectors[(-1, -1)] * r6)
a, b = 8, 3
closed = {(1, 1): sp.Rational(1, 2) * (a*a - a + b*b - b) + 2*a*b,
          (1, -1): 2*a*b,
          (-1, 1): sp.Rational(1, 2) * (a*a + a + b*b + b),
          (-1, -1): sp.Rational(1, 2) * b * (b - 1)}
assert all(sp.Integer(sectors[k]) == closed[k] for k in sectors), "closed forms in a=8, b=3 must match the census"
N_readout = (a * b) * ((3 * 2) ** 2) * ((3 * 2) ** 2)     # 24 * 36 * 36
print(f"numerator = {numerator}")
print(f"readout dimension N = 24 * 36 * 36 = {N_readout}")
alpha = numerator / N_readout
inv = sp.N(1 / alpha, 25)
print(f"1/alpha = {inv}   (Letter: 137.035 999 189 566...)")
assert str(inv).startswith("137.0359991895")
print("PART A: the Letter's count is reproduced exactly from its stated rules.\n")

# ----------------------------------------------------------------------------------------------
# PART B — what of this object M_16 contains, by explicit matrices
# ----------------------------------------------------------------------------------------------
print("=" * 78)
print("PART B — the object inside the Tree's M_16 = M_4 (x) M_4")
print("=" * 78)

def kron(*ms):
    out = np.array([[1.0 + 0j]])
    for m in ms:
        out = np.kron(out, m)
    return out

# Factor 1: M_4 with the colour split 4 -> 3 (+) 1 (link L13). P3 projects onto the 3.
P3 = np.diag([1, 1, 1, 0]).astype(complex)
# Factor 2: M_4 = M_2 (x) M_2, two qubits (link L4).
# Embeddings of letters as 16 x 16 matrices:
def qutrit_letter(k):      # Gell-Mann on the colour 3, zero on the 1, identity on both qubits
    g4 = np.zeros((4, 4), dtype=complex); g4[:3, :3] = GM[k]
    return kron(g4, I2, I2)
def qubit1_letter(k):
    return kron(P3, PA[k], I2)
def qubit2_letter(k):
    return kron(P3, I2, PA[k])

def rank_of(mats):
    return np.linalg.matrix_rank(np.array([m.flatten() for m in mats]), tol=1e-9)

Q = [qutrit_letter(k) for k in range(8)]
q1 = [qubit1_letter(k) for k in range(3)]
q2 = [qubit2_letter(k) for k in range(3)]

# B1: the three letter algebras are present, independent, and have the right dimensions
print(f"B1  qutrit letters in M_16: rank {rank_of(Q)} (expect 8); qubit-1 letters: {rank_of(q1)} (3); qubit-2 letters: {rank_of(q2)} (3)")
print(f"    all 14 letters together: rank {rank_of(Q + q1 + q2)} (expect 14)")
# B2: the qutrit commutes with both qubits (shared qudit, one copy per link, as the Letter requires)
comm_ok = all(np.allclose(A @ B, B @ A) for A in Q for B in q1 + q2)
print(f"B2  qutrit letters commute with both qubits' letters: {comm_ok}")
# B3: the two qubits anticommute within themselves and commute with each other
anti_ok = all(np.allclose(q1[i] @ q1[j] + q1[j] @ q1[i], 0) for i in range(3) for j in range(3) if i != j)
cross_ok = all(np.allclose(A @ B, B @ A) for A in q1 for B in q2)
print(f"B3  Pauli letters anticommute at each qubit: {anti_ok}; the two qubits commute with each other: {cross_ok}")
# B4: the 169 two-letter products, realised as 16 x 16 matrices, are linearly independent
letter_at = {0: Q, 1: q1, 2: Q, 3: q2}   # Q1 and Q2 are two copies of ONE qutrit: same matrices
prods_mats = []
for ((a_, i), (b_, j)) in products:
    prods_mats.append(letter_at[a_][i] @ letter_at[b_][j])
r169 = rank_of(prods_mats)
print(f"B4  rank of the 169 two-letter products as 16x16 matrices: {r169}")
print(f"    (the Q1Q2 edge realises as products of two Gell-Mann matrices on ONE qutrit copy in M_16,")
print(f"     so the 64 'kept' qutrit records collapse onto the 9-dim M_3: the Letter's two COPIES of the")
print(f"     shared qutrit are a network notion — one copy per link — that a single M_3 factor does not carry.)")
# B5: the operator spaces behind the readout dimension
d_block = 3 * 2 * 2
print(f"B5  the 3 (x) 2 (x) 2 block of M_16 (colour 3 with both qubits) has dimension {d_block}; its operator space {d_block**2}")
print(f"    the Letter's N = 24 * 36 * 36 needs: two read links' whole operator spaces (36 each: present, as M_3 (x) M_2 twice)")
print(f"    and the UNREAD third link's traceless part 24 = 8 * 3 (a third qubit entangled with the qutrit).")
print(f"    M_16 = (3 (+) 1) (x) 2 (x) 2 has exactly TWO qubits beside the colour 3. A third is first available at M_256 = M_16 (x) M_16.")
print()
print("PART B summary:")
print("  - the qutrit, both read qubits, their letter algebras and commutation structure are present in M_16 (L13 + L4);")
print("  - the NUMERATOR depends on the end dimensions (3, 2) alone, so it is the same inside M_16 as in the Letter;")
print("  - the DENOMINATOR needs the Letter's three-link two-point configuration (Theorem 1), whose unread third link")
print("    requires a third qubit: not in M_16, first in M_256 — the Tree's fourth level (L6).")
print("  - the Letter's 'two copies of one shared qutrit' is network structure that a single M_3 factor does not reproduce;")
print("    the 64 kept-edge records collapse to 9 when realised as plain matrix products. The count needs the record space,")
print("    not the matrix algebra. This is the definition that carries the weight (outcome (b) of Q3).")
