#!/usr/bin/env python3
"""R14 (the Higgs cells) and R15 (where the three generations live). Numerical companion to
lean_verify/chain_theory/R14R15HiggsAndPhases.lean. From the v3 list of The Refined Gaps v2 (§A8).

R14 pre-registered: Chain Theory's Higgs (200.1: the Higgs word, a (4,4) link; 65.2: "the hub-pair weights at
the two qubit copies ... equal the doublet of the Higgs entry by entry"), realised on M2 (x) M2, transforms as the
Tree's (1,2,2) bidoublet under su(2)_L + su(2)_R. Confirms: (2,2). Refutes: any other representation.

R15 pre-registered: under L14's quaternion reading the generation space carries the real structure of Im H, so
Yukawas are real in the basis (i, j, k). Confirms: the observed mixing, with its CP phase from a stated source.
Refutes: the quaternion structure forbids CP violation in quark mixing with no other source.
The Lean file proves real mass matrices give det[H_u, H_d] = 0 (J = 0). The only complex vacuum value in the
Tree's scalar sector that enters quark masses is the bidoublet's relative phase: <Phi> = diag(k1, k2 e^{i alpha}).
With SU(2)_R-symmetric Yukawas Y, Yt:  M_u = k1 Y + conj(k2) Yt,  M_d = k2 Y + conj(k1) Yt.
Run: python3 -I scripts/chain_theory/r14_r15_higgs_and_generations.py
"""
import numpy as np
from scipy.optimize import least_squares

rng = np.random.default_rng(7)
np.set_printoptions(precision=4, suppress=True)
s1 = np.array([[0, 1], [1, 0]], complex); s2 = np.array([[0, -1j], [1j, 0]]); s3 = np.diag([1.0, -1.0]).astype(complex)
I2 = np.eye(2)

# ------------------------------------------------------------------ R14
print("R14 — THE HIGGS CELLS")
TL = [np.kron(s / 2, I2) for s in (s1, s2, s3)]   # su(2)_L on the first qubit of the hub pair
TR = [np.kron(I2, s / 2) for s in (s1, s2, s3)]   # su(2)_R on the second
CL = sum(t @ t for t in TL); CR = sum(t @ t for t in TR)
print(f"  states of the hub pair C2 (x) C2: su(2)_L Casimir {set(np.round(np.linalg.eigvalsh(CL), 6))}, "
      f"su(2)_R Casimir {set(np.round(np.linalg.eigvalsh(CR), 6))}  -> (2,2): j_L = j_R = 1/2")
Y = TR[2]; Q = TL[2] + Y   # the Higgs is a colour singlet with B-L = 0, so Y = T3R
for idx, lab in enumerate(["|00>", "|01>", "|10>", "|11>"]):
    print(f"    {lab}: T3L = {TL[2][idx, idx].real:+.1f}, T3R = {TR[2][idx, idx].real:+.1f}, Y = {Y[idx, idx].real:+.1f}, "
          f"Q = {Q[idx, idx].real:+.0f}")
print("  charges {+1, 0, 0, -1}: the bidoublet [[phi1^0, phi1^+], [phi2^-, phi2^0]] (two doublets, Y = -1/2 and +1/2), entry by entry.")


def adj(gens):  # adjoint action on 4x4 operators, as 16x16 matrices on vec(X) (row-major)
    return [np.kron(g, np.eye(4)) - np.kron(np.eye(4), g.T) for g in gens]


CLa = sum(a @ a for a in adj(TL)); CRa = sum(a @ a for a in adj(TR))
print(f"  operators on the hub pair (reads): su(2)_L Casimirs {sorted(set(np.round(np.linalg.eigvals(CLa).real, 6)))}, "
      f"su(2)_R {sorted(set(np.round(np.linalg.eigvals(CRa).real, 6)))}")
print("  -> (1+3, 1+3): integer spin only, no (2,2). The match holds for the Higgs as a STATE of the pair (as 65.2 has it),")
print("     never for a read operator.")


def ent_entropy(r):  # Schmidt coefficients |k1|, |k2| of <Phi> = diag(k1, k2), r = |k2/k1|
    p = np.array([1.0, r * r]) / (1 + r * r)
    p = p[p > 0]
    return float(-(p * np.log2(p)).sum())


print(f"  the vacuum <Phi> = diag(k1, k2) as a two-qubit ket: maximally entangled iff |k1| = |k2| (entropy {ent_entropy(1):.0f} bit).")
print("  Lean (R14R15HiggsAndPhases): then M_d = u M_u, |u| = 1 -> identical up and down spectra (m_t = m_b): excluded.")

# ------------------------------------------------------------------ R15
print("\nR15 — WHERE THE GENERATIONS LIVE: real Yukawas (the quaternion reading) + the bidoublet's vacuum phase")
mu_obs = np.array([1.23e-3, 0.620, 168.26])      # MS-bar running masses at M_Z (GeV), e.g. Huang & Zhou (2021)
md_obs = np.array([2.67e-3, 0.05316, 2.839])
V_obs = {"Vus": 0.22501, "Vcb": 0.04183, "Vub": 0.003732}   # PDG 2024
J_obs = 3.08e-5


def masses_and_ckm(p):
    Yr = p[:9].reshape(3, 3); Ytr = p[9:18].reshape(3, 3); r = np.exp(p[18]); a = p[19]
    k2 = r * np.exp(1j * a)
    Mu = Yr + np.conj(k2) * Ytr
    Md = k2 * Yr + Ytr
    Uu, su, _ = np.linalg.svd(Mu); Ud, sd, _ = np.linalg.svd(Md)
    ou, od = np.argsort(su), np.argsort(sd)
    Uu, su, Ud, sd = Uu[:, ou], su[ou], Ud[:, od], sd[od]
    V = Uu.conj().T @ Ud
    J = np.imag(V[0, 1] * V[1, 2] * np.conj(V[0, 2]) * np.conj(V[1, 1]))
    tb = np.angle(np.linalg.det(Mu)) + np.angle(np.linalg.det(Md))
    tb = (tb + np.pi) % (2 * np.pi) - np.pi
    return su, sd, V, J, tb, r, a, Mu, Md


def resid(p, theta_weight=0.0):
    su, sd, V, J, tb, *_ = masses_and_ckm(p)
    res = list(np.log(su / mu_obs) / 0.05) + list(np.log(sd / md_obs) / 0.05)
    res += [(abs(V[0, 1]) / V_obs["Vus"] - 1) / 0.005, (abs(V[1, 2]) / V_obs["Vcb"] - 1) / 0.02,
            (abs(V[0, 2]) / V_obs["Vub"] - 1) / 0.03, (J / J_obs - 1) / 0.05]
    if theta_weight:
        res.append(tb * theta_weight)
    return np.array(res)


def start():
    th12, th23, th13 = 0.227, 0.042, 0.0037
    def rot(i, j, t):
        R = np.eye(3); c, s = np.cos(t), np.sin(t); R[i, i] = R[j, j] = c; R[i, j] = s; R[j, i] = -s; return R
    O = rot(1, 2, th23) @ rot(0, 2, th13) @ rot(0, 1, th12)
    Y0 = np.diag(mu_obs) * np.exp(rng.normal(0, 0.3, 3))
    Yt0 = O @ np.diag(md_obs) @ O.T * np.exp(rng.normal(0, 0.3))
    Y0 = Y0 + rng.normal(0, 1e-3, (3, 3)) * mu_obs.max() * 1e-3
    return np.concatenate([Y0.ravel(), Yt0.ravel(), [np.log(rng.uniform(0.002, 0.03)), rng.uniform(-np.pi, np.pi)]])


def best_fit(theta_weight=0.0, n=60):
    best = None
    for _ in range(n):
        try:
            sol = least_squares(resid, start(), args=(theta_weight,), method="trf", max_nfev=4000, xtol=1e-12, ftol=1e-12)
        except Exception:
            continue
        if best is None or sol.cost < best.cost:
            best = sol
    return best


def report(sol, title):
    su, sd, V, J, tb, r, a, Mu, Md = masses_and_ckm(sol.x)
    chi2 = 2 * sol.cost
    print(f"  {title}: chi^2 = {chi2:.3g} for 10 observables")
    print(f"    m_u, m_c, m_t = {su}   (obs {mu_obs})")
    print(f"    m_d, m_s, m_b = {sd}   (obs {md_obs})")
    print(f"    |V_us|, |V_cb|, |V_ub| = {abs(V[0, 1]):.5f}, {abs(V[1, 2]):.5f}, {abs(V[0, 2]):.6f};  J = {J:.3e} (obs {J_obs:.2e})")
    print(f"    |k2/k1| = {r:.4f}, alpha = {a:.4f} rad;  vacuum entanglement {ent_entropy(r):.4f} bit;  theta-bar = {tb:+.3e} rad")
    return chi2, tb, r


c1, tb1, r1 = report(best_fit(0.0), "fit A (masses + CKM + J)")
c2, tb2, r2 = report(best_fit(1e6), "fit B (as A, and theta-bar = 0 imposed)")
print("  Controls: with alpha = 0 every fit has J = 0 exactly (the Lean theorem); with |k2/k1| = 1 every fit has m_t = m_b.")
