#!/usr/bin/env python3
"""R9' — the improper element of Cl4, lifted to M16 = End(M4) = M4 (x) M4^op.

R9 (Refined Gaps, 25 Oct 2026) asked whether the improper element on M4 = M2 (x) M2 exchanges the
tensor factors or singles one out; the first pass found it posed on the wrong object, because the
Tree's L12 ("which factor is left") lives one level up, at End(A) = A (x) A^op, where the LEFT
factor acts covariantly and the RIGHT factor (A^op) contravariantly (F2_3_ChiralityForced).

This script realises End(M4) as 16 x 16 matrices acting on vec(xi), xi in M4, and tests every
canonical lift of the improper element, and of the three Clifford involutions, on two things:
  (a) the two factors: the left algebra  L = {xi -> a xi}  and the right algebra  R = {xi -> xi b};
  (b) the 8 + 8 split of the carrier M4 = Cl4 into even and odd Clifford elements (the
      eigenspaces of the grading Ad(gamma5)), the only 8 + 8 split the carrier offers.

Gamma matrices are the Tree's (F4_1e_CliffordMatrix): g1 = s3 (x) 1, g2 = s1 (x) 1,
g3 = (s3 s1) (x) s3, g4 = (s3 s1) (x) s1; the improper element P = g1 (R9, first pass).
Run: python3 -I scripts/chain_theory/r9prime_parity_at_M16.py
"""
import itertools
import numpy as np

I2 = np.eye(2, dtype=complex)
s1 = np.array([[0, 1], [1, 0]], dtype=complex)
s3 = np.array([[1, 0], [0, -1]], dtype=complex)
k = np.kron
g = [k(s3, I2), k(s1, I2), k(s3 @ s1, s3), k(s3 @ s1, s1)]
I4 = np.eye(4, dtype=complex)
g5 = g[0] @ g[1] @ g[2] @ g[3]
P = g[0]
TOL = 1e-10


def close(a, b):
    return np.allclose(a, b, atol=TOL)


# --- the Clifford algebra and its 16 basis monomials, graded --------------------------------
for i, j in itertools.product(range(4), repeat=2):
    ac = g[i] @ g[j] + g[j] @ g[i]
    assert close(ac, 0 * I4) if i != j else close(ac, 2 * (g[i] @ g[i]))
squares = [int(round((gi @ gi)[0, 0].real)) for gi in g]
monos, grades = [], []
for r in range(5):
    for S in itertools.combinations(range(4), r):
        m = I4.copy()
        for s in S:
            m = m @ g[s]
        monos.append(m)
        grades.append(r)
B = np.array([m.reshape(-1) for m in monos]).T  # 16 x 16, columns = vec(monomial), row-major
assert np.linalg.matrix_rank(B) == 16
Binv = np.linalg.inv(B)

# --- End(M4) as 16x16 matrices on row-major vec(xi) -------------------------------------------
def Lmul(a):  # xi -> a xi
    return k(a, I4)


def Rmul(b):  # xi -> xi b
    return k(I4, b.T)


def as_map(f):  # any linear f: M4 -> M4, as a 16x16 matrix
    E = np.eye(16, dtype=complex)
    return np.array([f(E[:, c].reshape(4, 4)).reshape(-1) for c in range(16)]).T


units = [np.eye(4, dtype=complex)[:, [i]] @ np.eye(4, dtype=complex)[[j], :] for i in range(4) for j in range(4)]
Lbasis = np.array([Lmul(u).reshape(-1) for u in units]).T
Rbasis = np.array([Rmul(u).reshape(-1) for u in units]).T


def in_span(Basis, X):
    c = np.linalg.lstsq(Basis, X.reshape(-1), rcond=None)[0]
    return np.allclose(Basis @ c, X.reshape(-1), atol=1e-8)


def factor_action(U):
    """Conjugation by U on End(M4): does it map L to L, L to R, or neither?"""
    Ui = np.linalg.inv(U)
    LtoL = all(in_span(Lbasis, U @ Lmul(u) @ Ui) for u in units)
    LtoR = all(in_span(Rbasis, U @ Lmul(u) @ Ui) for u in units)
    RtoR = all(in_span(Rbasis, U @ Rmul(u) @ Ui) for u in units)
    RtoL = all(in_span(Lbasis, U @ Rmul(u) @ Ui) for u in units)
    if LtoL and RtoR:
        # does it act on L, on R, or on both?
        onL = not all(close(U @ Lmul(u) @ Ui, Lmul(u)) for u in units)
        onR = not all(close(U @ Rmul(u) @ Ui, Rmul(u)) for u in units)
        who = {(True, False): "acts on L alone (singles out L)", (False, True): "acts on R alone (singles out R)",
               (True, True): "acts on both, preserving each", (False, False): "acts on neither"}[(onL, onR)]
        return "preserves the factors; " + who
    if LtoR and RtoL:
        return "EXCHANGES the factors (L <-> R)"
    return "mixes the factors"


even = Binv  # coordinates in the monomial basis
Peven = np.diag([1.0 if gr % 2 == 0 else 0.0 for gr in grades]).astype(complex)
proj_even = B @ Peven @ Binv  # projector onto the 8 even elements, as a map on vec(xi)
proj_odd = np.eye(16) - proj_even


def halves_action(U):
    """On the carrier M4 = Cl4_even (8) + Cl4_odd (8): preserve or exchange the halves?"""
    if close(proj_odd @ U @ proj_even, 0) and close(proj_even @ U @ proj_odd, 0):
        return "preserves the 8 + 8 halves"
    if close(proj_even @ U @ proj_even, 0) and close(proj_odd @ U @ proj_odd, 0):
        return "EXCHANGES the 8 + 8 halves"
    return "mixes the halves"


# --- the Clifford involutions as maps on M4 (defined on monomials, extended linearly) -------------
def from_signs(signs):
    D = np.diag(np.array(signs, dtype=complex))
    return lambda xi: (B @ D @ Binv @ xi.reshape(-1)).reshape(4, 4)


def reversion(xi):  # anti-automorphism fixing vectors: g_{i1}...g_{ir} -> g_{ir}...g_{i1}
    return from_signs([(-1) ** (r * (r - 1) // 2) for r in grades])(xi)


def clifford_conj(xi):  # anti-automorphism, vectors -> minus vectors
    return from_signs([(-1) ** (r * (r + 1) // 2) for r in grades])(xi)


def grade_inv(xi):  # automorphism, vectors -> minus vectors
    return from_signs([(-1) ** r for r in grades])(xi)


# sanity: automorphism / anti-automorphism on monomials
for f, anti in [(reversion, True), (clifford_conj, True), (grade_inv, False)]:
    for a, b in itertools.product(monos, repeat=2):
        lhs = f(a @ b)
        rhs = f(b) @ f(a) if anti else f(a) @ f(b)
        assert close(lhs, rhs)
assert close(as_map(grade_inv), as_map(lambda xi: g5 @ xi @ np.linalg.inv(g5)))

Pinv = np.linalg.inv(P)
lifts = {
    "L(P): spinor action, xi -> P xi (Pin acting on a left module)": Lmul(P),
    "R(P): xi -> xi P": Rmul(P),
    "Ad(P): the automorphism lift, xi -> P xi P^-1": Lmul(P) @ Rmul(Pinv),
    "twisted Ad(P): the reflection, xi -> alpha(P) xi P^-1": as_map(lambda xi: grade_inv(P) @ xi @ Pinv),
    "grade involution alpha = Ad(gamma5)": as_map(grade_inv),
    "reversion beta (anti-automorphism)": as_map(reversion),
    "Clifford conjugation (anti-automorphism)": as_map(clifford_conj),
    "transpose xi -> xi^T (anti-automorphism)": as_map(lambda xi: xi.T),
}

print("Signature of the Tree's gammas (squares):", squares)
print("gamma5 = g1 g2 g3 g4;  gamma5^2 =", int(round((g5 @ g5)[0, 0].real)), "; P = g1 anticommutes with gamma5:",
      close(P @ g5, -g5 @ P))
print("Azumaya check: L and R commute:", all(close(Lmul(a) @ Rmul(b), Rmul(b) @ Lmul(a)) for a in units for b in units),
      "; L.R spans M16:", np.linalg.matrix_rank(np.array([(Lmul(a) @ Rmul(b)).reshape(-1) for a in units for b in units])) == 256)
print()
w = max(len(n) for n in lifts)
for name, U in lifts.items():
    print(f"{name:<{w}} | {factor_action(U):<48} | {halves_action(U)}")

# antilinear J: xi -> xi^dagger (the real structure of a spectral triple); J L(a) J^-1 = R(a^dagger)
rng = np.random.default_rng(0)
a = rng.normal(size=(4, 4)) + 1j * rng.normal(size=(4, 4))
xi = rng.normal(size=(4, 4)) + 1j * rng.normal(size=(4, 4))
J = lambda x: x.conj().T
lhs = J(a @ J(xi))  # J L(a) J^-1 applied to xi (J is its own inverse)
print(f"{'J: xi -> xi^dagger (antilinear real structure)':<{w}} | "
      f"{'EXCHANGES the factors (L <-> R)' if close(lhs, xi @ a.conj().T) else 'does not exchange':<48} | "
      f"{halves_action(as_map(lambda x: x.T)) + ' (as its linear part)'}")

# chirality pairing: which lifts anticommute with the same lift of gamma5?
print()
print("Does lifted P anticommute with lifted gamma5 (same lift)?")
print("  L-lift:", close(Lmul(P) @ Lmul(g5), -Lmul(g5) @ Lmul(P)),
      "| Ad-lift:", close((Lmul(P) @ Rmul(Pinv)) @ (Lmul(g5) @ Rmul(np.linalg.inv(g5))),
                          -(Lmul(g5) @ Rmul(np.linalg.inv(g5))) @ (Lmul(P) @ Rmul(Pinv))),
      "(Ad loses the sign: Ad(P) and Ad(gamma5) commute)")
