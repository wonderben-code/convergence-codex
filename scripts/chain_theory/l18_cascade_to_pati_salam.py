#!/usr/bin/env python3
"""L18 scoped — what connects the Tree's cascade to the Pati-Salam spectral triple that generates sigma?

Capstone L18 (PARTIAL): a KO-6 finite real spectral triple exists for M_n(C), "but nothing connects it to the
cascade's Hilbert space". R13 (fifth pass) generated sigma from the Pati-Salam triple. This script places that
triple against the cascade, using Chamseddine-Connes, "Why the Standard Model" (J. Geom. Phys. 58 (2008) 38):
  Prop. 2.8: an irreducible finite geometry with centre C + C exists iff dim H = 2k^2; it is A_C = M_k + M_k
            acting by left multiplication on M_k + M_k, with J(x, y) = (y*, x*).
  Section 2.2-3: the real form M_2(H) + M_4(C) (k = 4) is a hypothesis ("quaternion linearity ... we choose the
            simplest case"); Prop. 3.2: the grading is then unique up to equivalence.
The cascade: M_2 -> M_4 = End(M_2) -> M_16 = End(M_4). Checks below, numerically exact to 1e-10:
  (1) k = 4 is the cascade's level 2, and each half of CC's H is the cascade's carrier M_4 (16 dims).
  (2) On that carrier, the left action of the first summand and the right action (through J) of the second
      commute and generate End(M_4) = M_16: the cascade's level 3 is the algebra the triple's actions generate.
  (3) The real form M_2(H) inside M_4(C) (a quaternionic structure j, j^2 = -1, on C^4) complexifies back to M_4(C),
      while the Tree's own theorem realForm_not_determined says the complexification cannot fix the real form.
  (4) The unique grading (Prop. 3.2) splits M_2(H) to H_R + H_L, and the resulting particle representation is the one
      R13's fifth pass used: particles psi_{s c}, s in 2_R + 2_L (left action), c in 4 = 3 + 1 (right action, L13).
Run: python3 -I scripts/chain_theory/l18_cascade_to_pati_salam.py
"""
import itertools
import numpy as np

rng = np.random.default_rng(11)
k = 4
def E(n, i, j):
    m = np.zeros((n, n), complex); m[i, j] = 1; return m
units = [E(k, i, j) for i in range(k) for j in range(k)]

# (1)-(2): the carrier M_4 (16 dims, row-major vec) with left and right multiplication
L = lambda a: np.kron(a, np.eye(k))          # x -> a x
R = lambda b: np.kron(np.eye(k), b.T)        # x -> x b
comm = max(np.abs(L(a) @ R(b) - R(b) @ L(a)).max() for a in units for b in units)
span = np.linalg.matrix_rank(np.array([(L(a) @ R(b)).ravel() for a in units for b in units]), tol=1e-10)
print("(1) k = 4 = the cascade's level 2 (M_4 = End(M_2)); CC's H at k = 4 is M_4 + M_4, 2k^2 = 32 = 16 + 16bar per generation")
print(f"(2) on one half, the carrier M_4: left and right actions commute (max |[L,R]| = {comm:.1e}) and generate "
      f"{span} of 256 dimensions -> End(M_4) = M_16, the cascade's level 3")

# J(x, y) = (y*, x*): J L(a) J^-1 acts on the first copy as right multiplication by a* of the second summand
x = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k)); y = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
a2 = rng.normal(size=(k, k)) + 1j * rng.normal(size=(k, k))
J = lambda X, Y: (Y.conj().T, X.conj().T)
# the second summand b acts by left multiplication on the second copy; transport it through J to the first copy:
Xj, Yj = J(x, y); Yj2 = a2 @ Yj; Xb, Yb = J(Xj, Yj2)          # J (0, b) J^-1 applied to (x, y)
print(f"    J (0 + b) J^-1 acts on the first copy as x -> x b*: {np.allclose(Xb, x @ a2.conj().T)}"
      "  (so the second summand reaches the carrier only as a right action: the Tree's contravariant factor, R9')")

# (3) the quaternionic real form M_2(H) in M_4(C): a in M_4(C) with j a = a j, j = antilinear, j^2 = -1
Om = np.kron(np.eye(2), np.array([[0, -1], [1, 0]]))          # j(v) = Om conj(v), j^2 = Om Om* = -1
assert np.allclose(Om @ Om.conj(), -np.eye(4))
def is_quat(a): return np.allclose(Om @ a.conj(), a @ Om)
# a real basis of M_2(H): solve the real-linear condition Om conj(a) = a Om
basis = []
for M in [E(4, i, j) for i in range(4) for j in range(4)] + [1j * E(4, i, j) for i in range(4) for j in range(4)]:
    P = 0.5 * (M + Om @ M.conj() @ np.linalg.inv(Om))      # projection onto the fixed algebra
    basis.append(P)
Bq = np.array([np.concatenate([b.real.ravel(), b.imag.ravel()]) for b in basis])
real_dim = np.linalg.matrix_rank(Bq, tol=1e-10)
cplx_span = np.linalg.matrix_rank(np.array([b.ravel() for b in basis] + [(1j * b).ravel() for b in basis]), tol=1e-10)
print(f"(3) M_2(H) in M_4(C): real dimension {real_dim} (= 2 x 2 quaternion entries x 4 = 16), all fixed by j: "
      f"{all(is_quat(b) for b in basis)}; its complex span has dimension {cplx_span} = M_4(C)")
print("    so C (x) M_2(H) = M_4(C) (the Tree's RealDivisionQuaternionCase, n = 2). The cascade supplies M_4(C); the real form")
print("    M_2(H) is CC's 'quaternion linearity' hypothesis and, by the Tree's realForm_not_determined, is not fixed by it.")

# (4) the grading: gamma = diag(1,1,-1,-1) on the isospin index splits M_2(H) to H_R + H_L (block-diagonal part)
g = np.diag([1, 1, -1, -1]).astype(complex)
even = [0.5 * (b + g @ b @ g) for b in basis]
ev_dim = np.linalg.matrix_rank(np.array([np.concatenate([e.real.ravel(), e.imag.ravel()]) for e in even]), tol=1e-10)
print(f"(4) the grading's even part of M_2(H): real dimension {ev_dim} = H_R + H_L (4 + 4)")
# the Pati-Salam particle representation on the carrier: H_R + H_L on the row (isospin s), M_4 on the column (colour c)
PS_alg = [L(e) @ R(np.eye(4)) for e in even] + [R(m) for m in units]
gen = np.linalg.matrix_rank(np.array([(p @ q).ravel() for p in PS_alg for q in PS_alg]), tol=1e-10)
print(f"    on the carrier, H_R + H_L (left) and M_4 (right) generate {gen} complex dimensions = (M_2 + M_2) (x) M_4 = 128,")
print("    the graded half of M_16; the particle states psi_{s c} with s in 2_R + 2_L and c in 4 = 3 + 1 are exactly the")
print("    representation R13's fifth pass used (r13c_sigma_from_fluctuations.py).")
print()
print("SCOPE OF L18 — between the cascade and the sigma-generating triple:")
print("  supplied by the cascade : k = 4 (level 2); the carrier M_4 as each half of H; M_16 = the algebra the two actions")
print("                            generate (level 3); left = covariant, right = contravariant (R9'); colour 4 = 3 + 1 (L13)")
print("  a ruling already made  : the real structure J(x, y) = (y*, x*), KO-dimension 6 (ruled 27 Sep 2026)")
print("  a choice, shared with CC: the quaternionic real form M_2(H) of the left summand (CC's hypothesis; the Tree's L14 ground)")
print("  forced once chosen      : the grading, H_R + H_L (CC Prop. 3.2)")
print("  still to supply         : the Dirac operator D (Yukawa and Majorana entries)")
