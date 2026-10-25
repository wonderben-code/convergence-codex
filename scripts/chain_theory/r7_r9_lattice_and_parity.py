#!/usr/bin/env python3
"""
R7 and R9 of 'The Refined Gaps' — the two residuals that are pure computations.

R7  (L9, signature). Chain Theory's argument (compendium ch. 54): on a lattice of counts, an
    indefinite integer quadratic form admits infinitely many integer isometries (a Pell family)
    while a definite form admits finitely many, so "the signature by existence reads Lorentzian".
    Prediction R7: the Tree's Clifford lattice in M_4 carries an indefinite integer form with an
    infinite isometry group and a definite one with a finite group.
    Test: for each real signature sharing Cl_4(C) — (4,0), (1,3), (2,2) — decide whether the
    integer isometry group O(Q; Z) is finite or infinite, by explicit construction of an
    infinite-order element (indefinite) or exhaustive enumeration (definite).

R9  (L12, chirality). Chain Theory reads parity as the improper element of the isometry group of
    its Hermitian split (59.1). Prediction R9 (bounded, two shapes): realised on the Tree's
    M_4 = M_2 (x) M_2, the improper element either (i) exchanges the two tensor factors, or
    (ii) acts within one factor and singles it out.
    Test: build the Tree's gamma matrices (F4_1e_CliffordMatrix.lean), the chirality element
    gamma_5, and the parity operator; see how each sits against the tensor factorisation.

Everything is exact integer / sympy arithmetic.
"""
import itertools
import numpy as np
import sympy as sp

# =================================================================================================
# R7 — integer isometry groups of the three signatures that share Cl_4(C)
# =================================================================================================
print("=" * 78)
print("R7 — Pell / lattice test on the three signatures sharing Cl_4(C)")
print("=" * 78)

def isometry_group_is_finite(diag):
    """diag: tuple of +-1. Decide finiteness of O(Q; Z) for Q = sum diag_i x_i^2.
    Definite: columns of an isometry are integer vectors of norm 1 => +-e_i => group finite (2^n n!).
    Indefinite: search for an integer isometry with an eigenvalue of modulus > 1 (infinite order)."""
    n = len(diag)
    G = np.diag(diag)
    if all(d == 1 for d in diag) or all(d == -1 for d in diag):
        # enumerate: signed permutation matrices are exactly the integer isometries
        count = 0
        for perm in itertools.permutations(range(n)):
            for signs in itertools.product((1, -1), repeat=n):
                M = np.zeros((n, n), dtype=int)
                for i, p in enumerate(perm):
                    M[p, i] = signs[i]
                if (M.T @ G @ M == G).all():
                    count += 1
        return True, f"finite: exactly {count} integer isometries (signed permutations)"
    # indefinite: find an element of infinite order by a bounded search on columns
    B = 3
    vecs = [np.array(v) for v in itertools.product(range(-B, B + 1), repeat=n)]
    byQ = {}
    for v in vecs:
        q = int(v @ G @ v)
        byQ.setdefault(q, []).append(v)
    # columns: column i must have Q = diag[i]; columns pairwise G-orthogonal
    cols_choices = [byQ.get(d, []) for d in diag]
    best = None
    def search(i, chosen):
        nonlocal best
        if best is not None:
            return
        if i == n:
            M = np.column_stack(chosen)
            if (M.T @ G @ M == G).all():
                ev = np.linalg.eigvals(M.astype(float))
                if max(abs(ev)) > 1 + 1e-9:
                    best = M
            return
        for v in cols_choices[i]:
            if all(int(v @ G @ c) == 0 for c in chosen):
                search(i + 1, chosen + [v])
    search(0, [])
    if best is None:
        return None, "no infinite-order element found within the search bound (inconclusive)"
    ev = np.linalg.eigvals(best.astype(float))
    return False, (f"infinite: integer isometry with spectral radius {max(abs(ev)):.4f} (infinite order)\n"
                   f"      M = {best.tolist()}")

for name, diag in (("Euclidean (4,0)", (1, 1, 1, 1)),
                   ("Lorentzian (1,3)", (1, -1, -1, -1)),
                   ("split (2,2) — the Tree's Q4 real form", (1, 1, -1, -1))):
    finite, msg = isometry_group_is_finite(diag)
    print(f"{name:42s} -> {msg}")

print()
print("R7 reading:")
print("  The prediction as stated holds: the definite form has a finite integer isometry group and the")
print("  indefinite forms have infinite ones. But BOTH indefinite signatures sharing Cl_4(C) — (1,3) and")
print("  (2,2) — are infinite. So the Pell/existence argument excludes the Euclidean alternative at the")
print("  Tree's fork L9, and does not choose between Lorentzian (1,3) and split (2,2). It is a theorem-")
print("  grade exclusion of one branch of the fork, not a selection of the walked one.")

# =================================================================================================
# R9 — the improper element against the tensor factorisation M_4 = M_2 (x) M_2
# =================================================================================================
print()
print("=" * 78)
print("R9 — parity (the improper element) against M_4 = M_2 (x) M_2")
print("=" * 78)
I2 = sp.eye(2)
s1 = sp.Matrix([[0, 1], [1, 0]]); s2 = sp.Matrix([[0, -sp.I], [sp.I, 0]]); s3 = sp.Matrix([[1, 0], [0, -1]])
kron = sp.kronecker_product
# The Tree's gamma matrices (F4_1e_CliffordMatrix.lean)
g1 = kron(s3, I2)
g2 = kron(s1, I2)
g3 = kron(s3 * s1, s3)
g4 = kron(s3 * s1, s1)
gam = [g1, g2, g3, g4]
sq = [sp.simplify(g * g) for g in gam]
print("gamma squares (diagonal entries):", [list(set(m.diagonal())) for m in sq])
anti = all(sp.simplify(gam[i] * gam[j] + gam[j] * gam[i]).is_zero_matrix for i in range(4) for j in range(4) if i < j)
print("pairwise anticommutation:", anti)
g5 = sp.simplify(g1 * g2 * g3 * g4)
print("gamma_5 = g1 g2 g3 g4 =", g5.tolist())
# Is gamma_5 a tensor-factor operator (I (x) P or P (x) I)? Check via partial-trace structure:
def is_of_form_I_x_B(M):
    # M = I2 (x) B  <=>  M[2a+i, 2b+j] = delta_ab B[i,j]
    B = M[0:2, 0:2]
    return sp.simplify(M - kron(I2, B)).is_zero_matrix
def is_of_form_A_x_I(M):
    A = sp.Matrix(2, 2, lambda a, b: M[2*a, 2*b])
    return sp.simplify(M - kron(A, I2)).is_zero_matrix
print("gamma_5 of the form I (x) B:", is_of_form_I_x_B(g5), "; of the form A (x) I:", is_of_form_A_x_I(g5))
print("  -> gamma_5 = sigma_2 (x) sigma_2: the chirality split (Weyl spinors) is NOT a tensor-factor split in this basis.")
# Parity: the improper element reverses the three 'spatial' generators and fixes the 'time' one.
# With g1 as the time-like generator (squares to +1), conjugation by g1 does exactly that:
P = g1
acts = [sp.simplify(P * g * P.inv()) for g in gam]
print("conjugation by P = gamma_1:", ["+g%d" % (k+1) if sp.simplify(acts[k] - gam[k]).is_zero_matrix else "-g%d" % (k+1) for k in range(4)])
print("P anticommutes with gamma_5 (swaps Weyl spinors):", sp.simplify(P * g5 + g5 * P).is_zero_matrix)
# How does conjugation by P act on the factorisation?
print("P = gamma_1 is of the form A (x) I:", is_of_form_A_x_I(P), " (A = sigma_3)")
# Does P exchange the factors? An operator exchanging factors is the swap S with S(A x B)S = B x A.
S = sp.zeros(4, 4)
for a in range(2):
    for b in range(2):
        S[2*a + b, 2*b + a] = 1
print("P equals the factor-swap (up to phase)?", any(sp.simplify(P - c * S).is_zero_matrix for c in (1, -1, sp.I, -sp.I)))
print()
print("R9 reading:")
print("  Outcome (ii): in the Tree's gamma basis the improper element is sigma_3 (x) I — it acts within the")
print("  FIRST tensor factor and leaves the second untouched; it does not exchange the factors. But two")
print("  honest qualifications. (1) Which factor it lives in is a property of the chosen Clifford basis,")
print("  not of M_4: a different gamma basis moves it. (2) Chirality itself (gamma_5 = sigma_2 (x) sigma_2)")
print("  is not aligned with the factorisation at all, so 'which factor is left' is not a question that")
print("  M_4 = M_2 (x) M_2 can answer. The Tree's L12 choice lives at M_16 = M_4 (x) M_4 (the Pati-Salam")
print("  SU(2)_L x SU(2)_R factors), and R9 must be restated there before it decides anything.")
print("  Verdict: R9 as stated is answered (shape ii, basis-dependent) and shown to be posed on the wrong")
print("  object; it is re-posed at M_16 in the next revision. That is a refinement, not a confirmation.")
