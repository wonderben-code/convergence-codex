#!/usr/bin/env python3
"""R13, the open sub-step — is sigma GENERATED (an inner fluctuation of the Dirac operator), or added by hand?

In a spectral triple (A, H, D, J) the bosonic fields are the inner fluctuations
    D -> D_A = D + A + J A J^{-1},   A = sum_i pi(a_i) [D, pi(b_i)],   a_i, b_i in A.
A Majorana entry T of D fluctuates, giving a field sigma that rescales it, only if T fails to commute
with the algebra: the T-block of pi(a)[D, pi(b)] is pi(a)(T pi(b) - pi(b) T).

The Tree's estate has no cascade Dirac operator (capstone L18, L19), so this script builds the two
finite spectral triples that carry its walked branch, on the Tree's fermions: H = 16 + 16bar per
generation, in the Chamseddine-Connes-van Suijlekom (CCvS 2013) bimodule form.
  particles      index (s, c): s in {nu_R/u_R, e_R/d_R, nu_L/u_L, e_L/d_L} (2_R + 2_L), c in {1, 2, 3, lepton}
  antiparticles  the same index set;  J = swap (particle <-> antiparticle) composed with complex conjugation
  Pati-Salam algebra (L11)  a = (q_R, q_L, m) in H_R + H_L + M4(C): (q_R + q_L) (x) 1 on particles, 1 (x) m on
                 antiparticles; M4 treats the lepton as the fourth colour (L13: 4 = 3 + 1)
  Standard-Model algebra    (lambda, q, m3) in C + H + M3(C), embedded as q_R = diag(lambda, conj lambda),
                 q_L = q, m = m3 + lambda: the lepton is NOT a colour
  D = [[S, T^dagger], [T, conj S]]: S the Yukawa block (generic, colour-dependent), T = k_R |nu_R-bar><nu_R|.
Run: python3 -I scripts/chain_theory/r13c_sigma_from_fluctuations.py
"""
import itertools
import numpy as np

rng = np.random.default_rng(3)
n = 16
idx = [(s, c) for s in range(4) for c in range(4)]       # s: 0 nu_R/u_R, 1 e_R/d_R, 2 nu_L/u_L, 3 e_L/d_L; c: 0,1,2 quark, 3 lepton
NU_R = idx.index((0, 3))


def op_part(Q4):            # (q_R + q_L) acting on the s index, identity on colour
    return np.kron(Q4, np.eye(4))


def op_anti(M):             # m acting on the colour index of antiparticles
    return np.kron(np.eye(4), M)


def pi(a):
    qR, qL, m = a
    Q4 = np.zeros((4, 4), complex); Q4[:2, :2] = qR; Q4[2:, 2:] = qL
    return np.block([[op_part(Q4), np.zeros((n, n))], [np.zeros((n, n)), op_anti(m)]])


Jm = np.block([[np.zeros((n, n)), np.eye(n)], [np.eye(n), np.zeros((n, n))]])
def Jconj(X):               # J X J^{-1} for J = Jm o (complex conjugation)
    return Jm @ X.conj() @ Jm


# --- the Dirac operator: generic Yukawas (quark and lepton, up and down distinct) + the Majorana entry
S = np.zeros((n, n), complex)
M_quark = np.diag(rng.uniform(0.5, 2.0, 2))      # colour-blind: the same for the three quark colours
M_lepton = np.diag([0.7, 1.3])                   # distinct for the lepton (the fourth colour)
for c in range(4):
    Mc = M_quark if c < 3 else M_lepton
    for (i, si), (j, sj) in itertools.product(enumerate([0, 1]), enumerate([2, 3])):
        S[idx.index((sj, c)), idx.index((si, c))] = Mc[j, i]     # R -> L
        S[idx.index((si, c)), idx.index((sj, c))] = Mc[j, i]     # L -> R (Hermitian)
T = np.zeros((n, n), complex); T[NU_R, NU_R] = 1.0              # nu_R -> nu_R-bar, k_R = 1
D = np.block([[S, T.conj().T], [T, S.conj()]])
assert np.allclose(Jconj(D), D), "JD = DJ"

# --- real bases of the two algebras
quat = [np.eye(2), 1j * np.array([[0, 1], [1, 0]]), 1j * np.array([[0, -1j], [1j, 0]]), 1j * np.diag([1, -1])]
Z2, Z4 = np.zeros((2, 2)), np.zeros((4, 4))
def E(k, i, j):
    m = np.zeros((k, k), complex); m[i, j] = 1; return m
M4_basis = [E(4, i, j) for i in range(4) for j in range(4)] + [1j * E(4, i, j) for i in range(4) for j in range(4)]
PS = [(q, Z2, Z4) for q in quat] + [(Z2, q, Z4) for q in quat] + [(Z2, Z2, m) for m in M4_basis]
SM = []
for lam in (1.0, 1j):
    m = np.zeros((4, 4), complex); m[3, 3] = lam
    SM.append((np.diag([lam, np.conj(lam)]), Z2, m))
SM += [(Z2, q, Z4) for q in quat]
for i, j in itertools.product(range(3), repeat=2):
    for ph in (1.0, 1j):
        m = np.zeros((4, 4), complex); m[i, j] = ph
        SM.append((Z2, Z2, m))


def Tblock(X):
    return X[n:, :n]


def report(name, alg):
    P = [pi(a) for a in alg]
    comm = max(np.abs(Tblock(D @ p - p @ D)).max() for p in P)
    forms = []
    for pa, pb in itertools.product(P, P):
        X = pa @ (D @ pb - pb @ D)
        forms.append(Tblock(X + Jconj(X)))
    Mx = np.array([np.concatenate([f.real.ravel(), f.imag.ravel()]) for f in forms])
    rank = np.linalg.matrix_rank(Mx, tol=1e-9)
    tvec = np.concatenate([T.real.ravel(), T.imag.ravel()])
    if rank:
        coef, *_ = np.linalg.lstsq(Mx.T, tvec, rcond=None)
        has_sigma = np.allclose(Mx.T @ coef, tvec, atol=1e-8)
    else:
        has_sigma = False
    # first-order condition [[D, a], J b J^-1] = 0, its worst violation
    foc = max(np.abs((D @ pa - pa @ D) @ Jconj(pb) - Jconj(pb) @ (D @ pa - pa @ D)).max()
              for pa, pb in itertools.product(P[::3], P[::3]))
    print(f"  {name}:")
    print(f"    max |[T, pi(a)]| over the algebra: {comm:.3g}")
    print(f"    real dimension of the Majorana-block fluctuations (A + JAJ^-1): {rank}")
    print(f"    is the sigma direction (a rescaling of T) among them? {has_sigma}")
    print(f"    first-order condition, worst violation: {foc:.3g}")
    return P


print("R13, OPEN SUB-STEP — IS SIGMA GENERATED BY INNER FLUCTUATIONS ON THE TREE'S 16 + 16bar?")
report("Standard-Model algebra C + H + M3 (lepton not a colour)", SM)
P_PS = report("Pati-Salam algebra H_R + H_L + M4 (the Tree's walked branch: L11, with L13's lepton as fourth colour)", PS)

# which parts of the Pati-Salam algebra make T fluctuate?
# the structure of the Pati-Salam Majorana-block fluctuations (first-order part): which entries they occupy
P = [pi(a) for a in PS]
occ = np.zeros((n, n), bool)
for pa, pb in itertools.product(P, P):
    X = pa @ (D @ pb - pb @ D); occ |= np.abs(Tblock(X + Jconj(X))) > 1e-12
rows = sorted({idx[i] for i in range(n) if occ[i].any()}); cols = sorted({idx[j] for j in range(n) if occ[:, j].any()})
print(f"  the Pati-Salam Majorana-block fluctuations occupy {occ.sum()} complex entries: antiparticle states {rows}")
print(f"    <- particle states {cols};  (s = 0, 1 are nu_R/u_R, e_R/d_R; c = 3 is the lepton)")
print("    = (antiparticle s in 2_R, lepton colour) <- (particle s = 0, any colour)  and  (antiparticle s = 0, any colour)")
print("      <- (particle s in 2_R, lepton colour): two copies of a field in (2_R, 1, 4), sharing the nu_R nu_R entry, sigma;")
print("      CCvS's Delta in (2_R,1_L,4), whose composite Delta Delta sits in the (3_R,1_L,10) of Part A.")
print("  which Pati-Salam directions fail to commute with T:")
groups = {
    "M4: the leptoquark directions (lepton <-> quark colour)": [E(4, 3, c) for c in range(3)] + [E(4, c, 3) for c in range(3)],
    "M4: the B-L direction diag(1,1,1,-3)": [np.diag([1, 1, 1, -3]).astype(complex)],
    "M4: su(3) colour": [E(4, 0, 1), E(4, 1, 2), np.diag([1, -1, 0, 0]).astype(complex)],
    "H_R: off-diagonal (nu_R <-> e_R)": [quat[1], quat[2]],
    "H_R: diagonal i*sigma3 (T3R)": [quat[3]],
    "H_L (any)": quat,
}
for gname, mats in groups.items():
    if gname.startswith("H_R"):
        algs = [(m, Z2, Z4) for m in mats]
    elif gname.startswith("H_L"):
        algs = [(Z2, m, Z4) for m in mats]
    else:
        algs = [(Z2, Z2, m) for m in mats]
    c = max(np.abs(Tblock(D @ pi(a) - pi(a) @ D)).max() for a in algs)
    print(f"    {gname:<58} {'fails to commute' if c > 1e-12 else 'commutes'}  ({c:.3g})")
