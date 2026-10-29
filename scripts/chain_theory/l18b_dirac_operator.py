#!/usr/bin/env python3
"""L18, the missing item — a finite Dirac operator on the cascade's carrier, with every axiom checked exactly.

L18 (sixth pass) was scoped to four items: J (ruled), the quaternionic real form (a choice), the grading (forced),
and D, still to supply. Here D is constructed on H = M_4 + M_4 (the cascade's carrier doubled, Chamseddine-Connes
Prop. 2.8 at k = 4), in the particle basis psi_{s c} (s in 2_R + 2_L, c in 3 + 1), for one generation with general
complex Yukawas y_u, y_d, y_nu, y_e and a Majorana mass k_R, and checked in exact symbolic arithmetic (sympy):
  (1) D self-adjoint;  (2) J D = D J, J^2 = 1, J gamma = -gamma J (KO-dimension 6);  (3) D gamma = -gamma D;
  (4) the order-zero condition [a, J b* J^-1] = 0 for the Pati-Salam algebra;
  (5) the first-order condition [[D, a], J b* J^-1] = 0 for the Standard-Model algebra C + H + M_3;
  (6) the first-order condition for the Pati-Salam algebra H_R + H_L + M_4: where, exactly, it fails.
Run: python3 -I scripts/chain_theory/l18b_dirac_operator.py
"""
import itertools
import sympy as sp

yu, yd, yn, ye = sp.symbols("y_u y_d y_nu y_e")
kR = sp.symbols("k_R", positive=True)
n = 16
idx = [(s, c) for s in range(4) for c in range(4)]   # s: 0 nu_R/u_R, 1 e_R/d_R, 2 nu_L/u_L, 3 e_L/d_L; c: 0,1,2 quark, 3 lepton
P = lambda s, c: idx.index((s, c))
Z = sp.zeros(n, n)


def block(A, B, C, Dm):
    return sp.Matrix(sp.BlockMatrix([[A, B], [C, Dm]]))


# the Dirac operator
S = sp.zeros(n, n)
for c in range(4):
    up, dn = (yu, yd) if c < 3 else (yn, ye)
    for (sR, sL, y) in ((0, 2, up), (1, 3, dn)):
        S[P(sL, c), P(sR, c)] = y
        S[P(sR, c), P(sL, c)] = sp.conjugate(y)
T = sp.zeros(n, n); T[P(0, 3), P(0, 3)] = kR
D = block(S, T.H, T, S.conjugate())
Jm = block(Z, sp.eye(n), sp.eye(n), Z)
Jc = lambda X: Jm * X.conjugate() * Jm            # J X J^-1, J = Jm o (complex conjugation)
g_part = sp.diag(*[(-1 if s < 2 else 1) for (s, c) in idx])
gamma = block(g_part, Z, Z, -g_part)

zero = lambda X: all(sp.simplify(e) == 0 for e in X)
print("L18 — THE FINITE DIRAC OPERATOR ON THE CASCADE'S CARRIER (one generation, general complex Yukawas)")
print(f"  (1) D self-adjoint: {zero(D - D.H)}")
print(f"  (2) J D J^-1 = D: {zero(Jc(D) - D)};  J^2 = 1: {zero(Jm * Jm - sp.eye(2 * n))};  J gamma = -gamma J: {zero(Jc(gamma) + gamma)}")
print(f"  (3) D gamma = -gamma D: {zero(D * gamma + gamma * D)}")


def E(k, i, j):
    m = sp.zeros(k, k); m[i, j] = 1; return m


def pi(qR, qL, m):
    Q4 = sp.zeros(4, 4); Q4[:2, :2] = qR; Q4[2:, 2:] = qL
    return block(sp.kronecker_product(Q4, sp.eye(4)), Z, Z, sp.kronecker_product(sp.eye(4), m))


I_ = sp.I
quat = [sp.eye(2), sp.Matrix([[0, I_], [I_, 0]]), sp.Matrix([[0, 1], [-1, 0]]), sp.Matrix([[I_, 0], [0, -I_]])]
Z2, Z4 = sp.zeros(2, 2), sp.zeros(4, 4)
PS = [pi(q, Z2, Z4) for q in quat] + [pi(Z2, q, Z4) for q in quat] + \
     [pi(Z2, Z2, ph * E(4, i, j)) for i in range(4) for j in range(4) for ph in (1, I_)]
SM = [pi(sp.diag(lam, sp.conjugate(lam)), Z2, sp.diag(0, 0, 0, lam)) for lam in (1, I_)] + \
     [pi(Z2, q, Z4) for q in quat] + [pi(Z2, Z2, ph * E(4, i, j)) for i in range(3) for j in range(3) for ph in (1, I_)]

order0 = all(zero(a * Jc(b.H) - Jc(b.H) * a) for a, b in itertools.product(PS, PS))
print(f"  (4) order zero, Pati-Salam algebra, all generator pairs: {order0}")
foc = lambda a, b: (D * a - a * D) * Jc(b.H) - Jc(b.H) * (D * a - a * D)
sm_ok = all(zero(foc(a, b)) for a, b in itertools.product(SM, SM))
print(f"  (5) first-order condition, Standard-Model algebra, all generator pairs: holds = {sm_ok}")

# (6) Pati-Salam: collect every violating entry and factor it
viol = set()
for a, b in itertools.product(PS, PS):
    F = foc(a, b)
    for e in F:
        e = sp.factor(sp.simplify(e))
        if e != 0:
            viol.add(e)
gens = sorted({str(sp.factor(v)) for v in viol})
print(f"  (6) first-order condition, Pati-Salam algebra: {len(viol)} distinct nonzero entries, e.g. {gens[:6]}")
at_relation = all(sp.simplify(v.subs({kR: 0, yn: yu, ye: yd})) == 0 for v in viol)
only_kR = all(sp.simplify(v.subs({yn: yu, ye: yd})) == 0 or v.has(kR) for v in viol)
print(f"      every violation vanishes when k_R = 0 and the Pati-Salam relation y_nu = y_u, y_e = y_d holds: {at_relation}")
print(f"      at that relation, what is left is carried by k_R alone: {only_kR}")
print()
print("RESULT: a finite Dirac operator with general Yukawa and Majorana entries exists on the cascade's carrier and")
print("satisfies every KO-dimension-6 axiom; the first-order condition holds for the Standard-Model algebra and, for the")
print("Pati-Salam algebra, fails exactly through the Majorana entry and through any quark-lepton Yukawa difference.")

# three generations, numerically: H = (16 + 16bar) (x) C^3, general complex 3 x 3 Yukawas and a symmetric Majorana matrix
import numpy as np
rng = np.random.default_rng(2)
cplx = lambda *sh: rng.normal(size=sh) + 1j * rng.normal(size=sh)
Yu, Yd, Yn, Ye = (cplx(3, 3) for _ in range(4))
MR = cplx(3, 3); MR = MR + MR.T
N = 16 * 3
Sg = np.zeros((N, N), complex)
for c in range(4):
    up, dn = (Yu, Yd) if c < 3 else (Yn, Ye)
    for (sR, sL, Y) in ((0, 2, up), (1, 3, dn)):
        for f, g in itertools.product(range(3), repeat=2):
            Sg[P(sL, c) * 3 + f, P(sR, c) * 3 + g] = Y[f, g]
            Sg[P(sR, c) * 3 + g, P(sL, c) * 3 + f] = np.conj(Y[f, g])
Tg = np.zeros((N, N), complex)
for f, g in itertools.product(range(3), repeat=2):
    Tg[P(0, 3) * 3 + f, P(0, 3) * 3 + g] = MR[f, g]
Dg = np.block([[Sg, Tg.conj().T], [Tg, Sg.conj()]])
Jg = np.block([[np.zeros((N, N)), np.eye(N)], [np.eye(N), np.zeros((N, N))]])
Jcg = lambda X: Jg @ X.conj() @ Jg
gp = np.kron(np.diag([(-1 if s < 2 else 1) for (s, c) in idx]), np.eye(3))
gg = np.block([[gp, np.zeros((N, N))], [np.zeros((N, N)), -gp]])
def pig(a):
    M_ = np.array(a.tolist(), dtype=complex)
    return np.kron(M_, np.eye(3))
SMg = [pig(a) for a in SM]; PSg = [pig(a) for a in PS]
ok = lambda X: np.allclose(X, 0, atol=1e-10)
fg = lambda a, b: (Dg @ a - a @ Dg) @ Jcg(b.conj().T) - Jcg(b.conj().T) @ (Dg @ a - a @ Dg)
print("  THREE GENERATIONS (numerical, general complex 3x3 Yukawas, symmetric complex Majorana matrix):")
print(f"    D self-adjoint {ok(Dg - Dg.conj().T)}; JD = DJ {ok(Jcg(Dg) - Dg)}; D gamma = -gamma D {ok(Dg @ gg + gg @ Dg)}; "
      f"first-order, SM algebra {all(ok(fg(a, b)) for a, b in itertools.product(SMg, SMg))}; "
      f"first-order, PS algebra {all(ok(fg(a, b)) for a, b in itertools.product(PSg, PSg))}")
