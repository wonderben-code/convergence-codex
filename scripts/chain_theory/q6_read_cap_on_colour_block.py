#!/usr/bin/env python3
"""Q6 — does Chain Theory's read cap give the Tree's L23 a statement in spectral-triple language?

The read cap (Chain Theory, alpha Letter and compendium): a read fixes both ends of a (d1, d2) link
only when every positive map between them is decomposable, which holds exactly when d1 d2 <= 6
(Stormer 1963, Woronowicz 1976; Choi 1975 for the failure at 3 x 3). Equivalently (Horodecki
1996-97): for d1 d2 <= 6 every PPT state is separable; at 3 x 3 there are PPT entangled states,
which no distillation can sharpen ("the dark sector is undistillable").

The Tree's object. M16 = End(M4) = M4 (x) M4^op, acting on the 16-dimensional carrier M4 = C4 (x) C4*
(R9' identifies the cut between the factors as the left|right cut). L13 splits C4 = C3 + C1, so the
carrier splits into corners: colour-colour C3 (x) C3* (9 dims: the gluon corner, 3 (x) 3bar = 8 + 1),
colour-lepton 3 + 3, lepton-lepton 1.

Part A  An explicit bound-entangled state on the gluon corner of the Tree's carrier, checked:
        positive, trace one, PPT across the left|right cut, entangled (realignment criterion).
Part B  The partition of the Tree's tensor blocks by the read cap.
Part C  The drafted spectral statement: "no conditional expectation onto a MUB subalgebra of the
        colour factor commutes with D on that block." Tested for a colour-blind finite Dirac
        operator D = 1_3 (x) Y (the structure of every finite Standard-Model Dirac operator: the
        Yukawa couplings do not see colour).
Run: python3 -I scripts/chain_theory/q6_read_cap_on_colour_block.py
"""
import numpy as np

TOL = 1e-10


def ptranspose(rho, dA, dB):
    r = rho.reshape(dA, dB, dA, dB)
    return r.transpose(0, 3, 2, 1).reshape(dA * dB, dA * dB)


def realign(rho, dA, dB):
    r = rho.reshape(dA, dB, dA, dB)
    return r.transpose(0, 2, 1, 3).reshape(dA * dA, dB * dB)


def horodecki_3x3(a):
    """P. Horodecki, Phys. Lett. A 232 (1997) 333: PPT and entangled for 0 < a < 1."""
    b, c = (1 + a) / 2, np.sqrt(1 - a * a) / 2
    M = np.zeros((9, 9))
    for i in (0, 4, 8):
        for j in (0, 4, 8):
            M[i, j] = a
    for i in (1, 2, 3, 5, 7):
        M[i, i] = a
    M[6, 6], M[8, 8], M[6, 8], M[8, 6] = b, b, c, c
    return M / (8 * a + 1)


# ---------------- Part A ----------------
a = 0.3
rho3 = horodecki_3x3(a)
# embed into the Tree's carrier C4 (x) C4*, colour indices 0..2 on each side, lepton index 3
emb = np.zeros((16, 9))
for i in range(3):
    for j in range(3):
        emb[4 * i + j, 3 * i + j] = 1.0
rho = emb @ rho3 @ emb.T
evals = np.linalg.eigvalsh(rho)
pt = np.linalg.eigvalsh(ptranspose(rho, 4, 4))
ccnr = np.linalg.svd(realign(rho, 4, 4), compute_uv=False).sum()
print("Part A — a Horodecki state (a = 0.3) placed on the Tree's gluon corner C3 (x) C3* of the carrier C4 (x) C4*")
print(f"  positive: {evals.min() > -TOL}   trace: {np.trace(rho):.12f}")
print(f"  PPT across the left|right cut (min eigenvalue of the partial transpose): {pt.min():+.2e}  -> PPT: {pt.min() > -TOL}")
print(f"  realignment norm: {ccnr:.6f}  (> 1 certifies entanglement)  -> entangled: {ccnr > 1 + 1e-9}")
print("  So the Tree's gluon corner carries a state that is entangled across the left|right cut of M16")
print("  yet has a positive partial transpose: bound entangled, undistillable. The read cap's 'dark' object")
print("  exists on the Tree's own carrier, at the colour block.")

# ---------------- Part B ----------------
print("\nPart B — the Tree's tensor blocks against the read cap d1 d2 <= 6")
blocks = [
    ("isospin pair (2,2)  [M4 = M2 (x) M2, L4 / Pati-Salam SU(2)L x SU(2)R]", 2, 2),
    ("colour-isospin (3,2) [quark doublet: 4 -> 3 on one side, a qubit on the other]", 3, 2),
    ("colour-lepton (3,1) / (1,3)", 3, 1),
    ("gluon corner (3,3)  [C3 (x) C3* inside End(C4): 3 (x) 3bar = 8 + 1]", 3, 3),
    ("whole cut (4,4)     [M16 = End(M4) across left|right]", 4, 4),
]
for name, d1, d2 in blocks:
    tag = "readable (every PPT state separable)" if d1 * d2 <= 6 else "DARK (bound entanglement exists)"
    print(f"  {name:<80} d1 d2 = {d1 * d2:>2}: {tag}")
print("  The cap falls between the quark doublet (6, exactly at the cap) and the gluon corner (9).")

# ---------------- Part C ----------------
print("\nPart C — the drafted spectral statement, tested on a colour-blind finite Dirac operator")
rng = np.random.default_rng(1)
k = 4  # the non-colour part of the quark sector (flavour x isospin x chirality, any size)
Y = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
Y = Y + Y.conj().T
D = np.kron(np.eye(3), Y)
w = np.exp(2j * np.pi / 3)
F = np.array([[1, 1, 1], [1, w, w * w], [1, w * w, w]]) / np.sqrt(3)  # Fourier basis: unbiased to the standard one
mubs = {"computational": np.eye(3, dtype=complex), "Fourier": F}
for name, Bm in mubs.items():
    Ps = [np.kron(np.outer(Bm[:, i], Bm[:, i].conj()), np.eye(k)) for i in range(3)]
    commute = all(np.allclose(D @ P_, P_ @ D) for P_ in Ps)
    # E(X) = sum_i P_i X P_i, the conditional expectation onto the MUB-diagonal subalgebra (x) M_k
    X = rng.normal(size=(3 * k, 3 * k)) + 1j * rng.normal(size=(3 * k, 3 * k))
    E = lambda Z: sum(P_ @ Z @ P_ for P_ in Ps)
    ecomm = np.allclose(E(D @ X - X @ D), E(D) @ E(X) - E(X) @ E(D)) and np.allclose(E(D), D)
    print(f"  {name:>13} basis of the colour qutrit: projections commute with D: {commute};  E(D) = D and E is D-covariant: {ecomm}")
print("  So the statement as drafted is false for every colour-blind D: a finite Standard-Model Dirac operator")
print("  commutes with the whole colour factor, so every conditional expectation onto a colour subalgebra")
print("  commutes with it. The finite triple sees colour only through its unbroken symmetry.")
