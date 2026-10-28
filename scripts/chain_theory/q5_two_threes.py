#!/usr/bin/env python3
"""Q5 — the Tree's three (imaginary quaternions) against Chain Theory's three (attach sites).

Numerical companion to lean_verify/chain_theory/Q5TwoThrees.lean.

  Tree (L14):          i, j, k in M2(C): three anticommuting square roots of -1, the qubit's three
                       traceless directions.
  Chain Theory (197):  three attach sites, the qutrit corners of the closed core triangle, spanning
                       a generation space of dimension three, carried cyclically by the shift (197.2);
                       mixing = overlap of the site basis with the eigenbasis of the step, the order-3
                       Fourier matrix, every squared modulus 1/3, phases a third of a turn (166.1, eq. 250).

Checks: (1) the commutator phase of each structure; (2) the shared cyclic Z3 and its Fourier basis;
(3) orientation; (4) Chain Theory's polar unitary of the incidence matrix (197.4) read as a rotation.
Run: python3 -I scripts/chain_theory/q5_two_threes.py
"""
import numpy as np
import scipy.linalg as sl

np.set_printoptions(precision=4, suppress=True)
I2 = np.eye(2)
s = [np.array([[0, 1], [1, 0]], complex), np.array([[0, -1j], [1j, 0]]), np.array([[1, 0], [0, -1]], complex)]
qi, qj, qk = (-1j * m for m in s)  # i, j, k as 2x2 complex matrices
w = np.exp(2j * np.pi / 3)


def ok(a, b):
    return np.allclose(a, b, atol=1e-12)


print("(1) THE COMMUTATOR PHASE")
assert all(ok(q @ q, -I2) for q in (qi, qj, qk)) and ok(qi @ qj, qk)
c_quat = (qi @ qj @ np.linalg.inv(qj @ qi))[0, 0]
X3 = np.roll(np.eye(3), 1, axis=0)        # the shift on the three sites: s_a -> s_{a+1}
Z3 = np.diag([1, w, w * w])               # the clock
c_qutrit = (Z3 @ X3 @ np.linalg.inv(X3 @ Z3))[0, 0]
print(f"  Tree's triple (qubit):        i j = c j i with c = {c_quat.real:+.0f}        (order 2: a sign)")
print(f"  Chain Theory's sites (qutrit): Z X = c X Z with c = e^(2 pi i/3)  ({np.isclose(c_qutrit, w)}; order 3: a cube root)")
print("  Lean (Q5TwoThrees): c^n = 1 at any n-dimensional end; in odd n no pair anticommutes; no unital")
print("  R-algebra map H -> M_n(C) for odd n. So i, j, k cannot act on the 3-dimensional generation space.")

print("\n(2) THE SHARED CYCLIC Z3 AND ITS FOURIER BASIS")
u = (np.eye(2) + qi + qj + qk) / 2
ui = np.linalg.inv(u)
assert ok(u @ qi @ ui, qj) and ok(u @ qj @ ui, qk) and ok(u @ qk @ ui, qi)
print("  conjugation by u = (1+i+j+k)/2 cycles i -> j -> k -> i   (an inner automorphism of H)")
# the cycle as a 3x3 matrix on Im H in the basis (i, j, k), via the trace pairing <x,y> = -tr(xy)/2
basis = [qi, qj, qk]
coord = lambda x: np.array([(-np.trace(x @ b) / 2).real for b in basis])
sigma = np.array([coord(u @ b @ ui) for b in basis]).T
assert ok(sigma, X3)
print("  on Im H in the basis (i, j, k) the cycle IS the site shift X of Chain Theory's triangle:", ok(sigma, X3))
evals, evecs = np.linalg.eig(sigma)
order = np.argsort(np.angle(evals) % (2 * np.pi))
evecs = evecs[:, order]
evecs = evecs / evecs[0]                   # fix the phase of each eigenvector
overlap = evecs / np.sqrt(3)
print("  overlap of the (i, j, k) basis with the eigenbasis of the cycle (squared moduli):")
print(np.abs(overlap) ** 2)
phases = np.angle(overlap) / (2 * np.pi) % 1
print("  phases in turns:\n", phases)
print("  = the order-3 Fourier matrix: every squared modulus 1/3, every phase a multiple of 1/3 turn —")
print("    Chain Theory's eq. (250) for the mixing. Shared, but generic: any cyclically shifted triple gives it.")

print("\n(3) ORIENTATION")
print(f"  i j k = {np.round((qi @ qj @ qk)[0, 0].real):+.0f} * 1,   k j i = {np.round((qk @ qj @ qi)[0, 0].real):+.0f} * 1")
swap_ok = ok(qj @ qi, qk)
print(f"  swapping i <-> j while fixing k respects the product: {swap_ok}  (j i = -k): the triple's symmetry is Z3, not S3")
print("  Chain Theory: the triangle is carried by a directed shift (197.2); odd cycles carry a half turn")
print("  in the arrow transfer operator (Theorem 44.1). Both triples are oriented; whether the")
print("  two signs are the same sign needs a quaternionic transport around the core triangle, defined by neither side.")

print("\n(4) CHAIN THEORY'S POLAR UNITARY (197.4) AS AN AUTOMORPHISM OF THE TREE'S TRIPLE")
L = np.tril(np.ones((3, 3)))
U, _ = sl.polar(L)
ang = np.degrees(np.arccos((np.trace(U) - 1) / 2))
ev, vec = np.linalg.eig(U)
axis = np.real(vec[:, np.argmin(abs(ev - 1))])
axis = axis / np.linalg.norm(axis) * np.sign(axis[0])
print(f"  U is in SO(3): det = {np.linalg.det(U):+.6f}; a rotation by {ang:.4f} degrees about {axis}")
print(f"  (the cycle's axis is (1,1,1)/sqrt3 = {np.ones(3) / np.sqrt(3)}; U^4 = 1: {ok(np.linalg.matrix_power(U, 4), np.eye(3))})")
print("  Every rotation of Im H is an automorphism of H, so U lifts to a unit quaternion; this is true of any")
print("  rotation and carries no discriminating content.")

print("\nVERDICT: two different threes — a qubit's three traceless directions (phase -1) and a qutrit")
print("triangle's three sites (phase e^(2 pi i/3)) — which share one structure, the oriented cyclic Z3 and")
print("its Fourier basis. Chain Theory's 197.5 and the Tree's L14 are not the same statement.")
