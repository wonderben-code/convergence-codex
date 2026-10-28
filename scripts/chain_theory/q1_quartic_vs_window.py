#!/usr/bin/env python3
"""Q1 — Chain Theory's Higgs quartic against the Tree's coupling window (guess-and-test).

Chain Theory (compendium 0.1, eq. 124 and Theorem 202.1): the quartic is the hub-face office over
the vacuum office squared,
    lambda = (46656001681 / 182250000) / V^2,
with the vacuum office V at its six readings 6561, 81, 65536, 256, 16, 256 (6561 = 81^2 the first,
adopted reading). Its literature gloss uses m_H^2 = 2 lambda v^2. No scale is stated: "the quartic
is a ratio of two offices and needs no observed value and no unit."

The Tree (L15, HiggsBridge): at the cutoff Lambda, g^2/N <= lambda~ <= g^2 with N = 96, lambda = 4 lambda~,
m_H^2 = 2 lambda v^2 (same convention as Chain Theory), g = g3 at Lambda. So
    g^2/24 <= lambda(Lambda) <= 4 g^2.

Neither side fixes the scale of Chain Theory's number, so three readings are tested:
  T1  as a value at the Tree's cutoff: inside the window?
  T2  as a Standard-Model running coupling: at what scale mu does lambda_SM(mu) equal it?
  T3  the window itself, run down with Standard-Model RGEs: which Higgs masses does it allow?

RGEs: Standard Model, MS-bar, one loop in full plus the two-loop gauge terms and the dominant
two-loop top/QCD/Higgs terms of y_t and lambda (electroweak two-loop terms in y_t and lambda omitted).
Boundary values at mu = m_t from Buttazzo et al., JHEP 12 (2013) 089, with their linear
dependences on m_t, m_h, alpha_s. Validation targets from the same paper (NNLO): lambda turns
negative near 10^10 GeV; lambda(M_Pl) = -0.0143 at their central inputs.
Run: python3 -I scripts/chain_theory/q1_quartic_vs_window.py
"""
from fractions import Fraction as F
import math
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

# ---------------- Chain Theory's quartic, exactly ----------------
office = F(46656001681, 182250000)
readings = [6561, 81, 65536, 256, 16, 256]
lam_ct = [office / (V * V) for V in readings]
assert lam_ct[0] == F(46656001681, 7845264902250000)  # eq. (124), as printed
assert office / 81**2 == F(46656001681, 1195742250000)  # the "register beside eighty-one", as printed

# ---------------- Standard-Model running ----------------
K = 1 / (16 * math.pi**2)


def beta(t, y):
    gY, g2, g3, yt, lam = y
    gY2, g22, g32, yt2 = gY**2, g2**2, g3**2, yt**2
    b_gY = K * 41 / 6 * gY**3 + K**2 * gY**3 * (199 / 18 * gY2 + 9 / 2 * g22 + 44 / 3 * g32 - 17 / 6 * yt2)
    b_g2 = -K * 19 / 6 * g2**3 + K**2 * g2**3 * (3 / 2 * gY2 + 35 / 6 * g22 + 12 * g32 - 3 / 2 * yt2)
    b_g3 = -K * 7 * g3**3 + K**2 * g3**3 * (11 / 6 * gY2 + 9 / 2 * g22 - 26 * g32 - 2 * yt2)
    b_yt = (K * yt * (9 / 2 * yt2 - 8 * g32 - 9 / 4 * g22 - 17 / 12 * gY2)
            + K**2 * yt * (-12 * yt2**2 + 36 * g32 * yt2 - 108 * g32**2 + 6 * lam**2 - 12 * lam * yt2))
    b_lam = (K * (24 * lam**2 + 12 * lam * yt2 - 6 * yt2**2 - 3 * lam * (3 * g22 + gY2)
                  + 3 / 8 * (2 * g22**2 + (g22 + gY2) ** 2))
             + K**2 * (-312 * lam**3 - 144 * lam**2 * yt2 - 3 * lam * yt2**2 + 30 * yt2**3
                       + 80 * lam * g32 * yt2 - 32 * g32 * yt2**2))
    return [b_gY, b_g2, b_g3, b_yt, b_lam]


def boundary(mt=173.34, mh=125.15, a3=0.1184, mW=80.384):
    """Buttazzo et al. (2013), eqs. for the MS-bar couplings at mu = m_t."""
    lam = 0.12604 + 0.00206 * (mh - 125.15) - 0.00004 * (mt - 173.34)
    yt = 0.93690 + 0.00556 * (mt - 173.34) - 0.00042 * (a3 - 0.1184) / 0.0007
    g3 = 1.1666 + 0.00314 * (a3 - 0.1184) / 0.0007 - 0.00046 * (mt - 173.34)
    g2 = 0.64779 + 0.00004 * (mt - 173.34) + 0.00011 * (mW - 80.384) / 0.014
    gY = 0.35830 + 0.00011 * (mt - 173.34) - 0.00020 * (mW - 80.384) / 0.014
    return mt, [gY, g2, g3, yt, lam]


def run(mt, y0, mu_max=1.22e19, dense=True):
    return solve_ivp(beta, (math.log(mt), math.log(mu_max)), y0, rtol=1e-10, atol=1e-12, dense_output=dense)


MPL = 1.22e19

# validation at Buttazzo's central inputs
mt0, y0 = boundary()
sol0 = run(mt0, y0)
lam_pl = sol0.sol(math.log(MPL))[4]
cross = brentq(lambda t: sol0.sol(t)[4], math.log(1e6), math.log(MPL))
print("VALIDATION (Buttazzo et al. central inputs m_t = 173.34, m_h = 125.15, alpha_s = 0.1184)")
print(f"  lambda(M_Pl) = {lam_pl:+.4f}   [published NNLO: -0.0143]")
print(f"  lambda = 0 at mu = 10^{cross / math.log(10):.1f} GeV   [published: ~10^10 GeV]")
print(f"  at M_Pl: gY={sol0.sol(math.log(MPL))[0]:.3f} g2={sol0.sol(math.log(MPL))[1]:.3f} "
      f"g3={sol0.sol(math.log(MPL))[2]:.3f} yt={sol0.sol(math.log(MPL))[3]:.3f}")

# current inputs (PDG 2024): m_t = 172.57, m_h = 125.20, alpha_s = 0.1180, M_W = 80.369
mt, y = boundary(mt=172.57, mh=125.20, a3=0.1180, mW=80.369)
sol = run(mt, y)
print("\nCURRENT INPUTS (m_t = 172.57, m_h = 125.20, alpha_s = 0.1180)")
lam_t = y[4]
print(f"  lambda(m_t) = {lam_t:.5f};  lambda(M_Pl) = {sol.sol(math.log(MPL))[4]:+.4f}")

# ---------------- T1: at the Tree's cutoff ----------------
print("\nT1 — Chain Theory's quartic read at the Tree's cutoff: window g^2/24 <= lambda <= 4 g^2, g = g3(Lambda)")
cutoffs = [1e13, 1e16, 1e17, MPL]
print("  Lambda (GeV)   g3(Lambda)   window for lambda")
for L in cutoffs:
    g3 = sol.sol(math.log(L))[2]
    print(f"  {L:9.1e}      {g3:.4f}      [{g3**2 / 24:.4f}, {4 * g3**2:.3f}]")
print("  reading  V       lambda_CT (exact)                       value        inside at all four cutoffs?")
for V, lam in zip(readings, lam_ct):
    inside = [(sol.sol(math.log(L))[2] ** 2 / 24 <= lam <= 4 * sol.sol(math.log(L))[2] ** 2) for L in cutoffs]
    verdict = "yes" if all(inside) else ("no" if not any(inside) else "at some")
    print(f"  {V:>6}   {str(lam):<38}  {float(lam):.6e}   {verdict}")

# ---------------- T2: as a running coupling ----------------
print("\nT2 — Chain Theory's quartic read as the Standard-Model running coupling: where is lambda_SM(mu) equal to it?")
tgrid = np.linspace(math.log(mt), math.log(MPL), 4000)
lgrid = sol.sol(tgrid)[4]
for V, lam in zip(readings, lam_ct):
    x = float(lam)
    idx = np.where(np.diff(np.sign(lgrid - x)))[0]
    if len(idx) == 0:
        print(f"  V = {V:>6}: lambda = {x:.4e} — never reached between m_t and M_Pl "
              f"(lambda_SM spans [{lgrid.min():+.4f}, {lgrid.max():.4f}])")
    else:
        t_star = brentq(lambda t: sol.sol(t)[4] - x, tgrid[idx[0]], tgrid[idx[0] + 1])
        print(f"  V = {V:>6}: lambda = {x:.4e} at mu = 10^{t_star / math.log(10):.2f} GeV")

# ---------------- T3: the window, run down ----------------
print("\nT3 — the Tree's window as a boundary condition at Lambda, Standard-Model running only:")
print("     which lambda(m_t), hence which m_H, does each edge require? (gauge and y_t fixed by measurement)")


def lam_at(L, lam_mt):
    yy = list(y)
    yy[4] = lam_mt
    s = solve_ivp(beta, (math.log(mt), math.log(L)), yy, rtol=1e-10, atol=1e-12)
    return s.y[4, -1]


def mh_from_lam(lam_mt):
    # invert Buttazzo's matching near the physical point; tree-level beyond it (m_H^2 = 2 lambda v^2,
    # offset so that both agree at the physical point)
    lin = 125.15 + (lam_mt - 0.12604 + 0.00004 * (mt - 173.34)) / 0.00206
    v = 246.22
    tree = math.sqrt(2 * lam_mt) * v
    tree_ref = math.sqrt(2 * lam_t) * v
    return lin if abs(lam_mt - lam_t) < 0.03 else tree + (125.20 - tree_ref)


for L in [1e16, 1e17, MPL]:
    g3 = sol.sol(math.log(L))[2]
    lo, hi = g3**2 / 24, 4 * g3**2
    row = []
    for target in (lo, hi):
        try:
            lm = brentq(lambda l: lam_at(L, l) - target, 0.05, 0.9)
            row.append(f"lambda(m_t) = {lm:.4f} -> m_H ~ {mh_from_lam(lm):.0f} GeV")
        except ValueError:
            row.append("no perturbative solution in lambda(m_t) in [0.05, 0.9]")
    print(f"  Lambda = {L:.1e}: lower edge {lo:.4f}: {row[0]}")
    print(f"  {'':18}upper edge {hi:.3f}: {row[1]}")
print(f"  measured: m_H = 125.20 GeV, lambda(m_t) = {lam_t:.4f}, running to lambda(Lambda) < 0 above ~10^10 GeV")

# ---------------- robustness: which top mass would the window need? ----------------
print("\nROBUSTNESS — the window's lower edge is strictly positive for every N (lambda~ = g^2 b/a^2 > 0),")
print("so the question is whether lambda(Lambda) > 0 is compatible with m_H = 125.20. Top mass required:")
for L in [1e16, MPL]:
    def lam_L(mtop, L=L):
        m, yy = boundary(mt=mtop, mh=125.20, a3=0.1180, mW=80.369)
        s = solve_ivp(beta, (math.log(m), math.log(L)), yy, rtol=1e-10, atol=1e-12)
        return s.y[4, -1]
    mt_zero = brentq(lam_L, 168.0, 176.0)
    print(f"  Lambda = {L:.1e}: lambda(Lambda) > 0 needs m_t < {mt_zero:.2f} GeV   [measured 172.57 +- 0.29]")
