#!/usr/bin/env python3
"""R13 Part B — with sigma, does the Tree's window give m_H = 125.2 GeV?

Model: Chamseddine-Connes, "Resilience of the spectral standard model", JHEP 09 (2012) 104 (CC12), with the
singlet sigma that Part A shows is forced on the Tree's Pati-Salam 16.
  potential  V = (1/4)(lam_h h^4 + 2 lam_hs h^2 s^2 + lam_s s^4), H^dagger H = h^2/2   (CC12 eq. 12)
  boundary conditions at Lambda (CC12 eqs. 13-15), g = g3(Lambda) as in the Tree's HiggsBridge:
      lam_h = (n^2+3)/(n+3)^2 * 4g^2,  lam_hs = 2n/(n+3) * 4g^2,  lam_s = 8 g^2,   y_nu = sqrt(n) y_t   (eq. 2)
  so lam_h(Lambda) = 4 lam~ runs over [g^2, 4g^2] as n runs over [0, inf): inside the Tree's window [g^2/24, 4g^2].
  RGEs above the sigma threshold: CC12 eqs. 16-20 (one loop) for y_t, y_nu, lam_h, lam_hs, lam_s.
  Below the threshold: the Standard Model with our validated running (q1_quartic_vs_window.py).

Improvement over CC12, which runs every coupling down to M_Z: here sigma (and nu_R) are decoupled at
m_sigma with the tree-level threshold  lam_SM(m_sigma) = lam_h - lam_hs^2/lam_s  (the light eigenvalue, CC12
eq. 32), and the Standard Model runs below. Gauge couplings and y_t are fixed by measurement (bottom-up);
only the scalar sector is fixed at Lambda (top-down). y_nu is shot so that y_nu(Lambda) = sqrt(n) y_t(Lambda).

Tests: (1) for each (Lambda, m_sigma), the n that gives m_H = 125.20; stability (CC12 eq. 33,
lam_hs^2 < lam_h lam_s) at Lambda and at m_sigma; perturbativity.
(2) Seesaw consistency. In CC12's normalisation the Majorana mass and the sigma mass are tied:
M_R = 2 g(Lambda) * w, m_sigma^2 = 2 lam_s w^2 (CC12 eqs. 8, 11, 31), so M_R = 2 g m_sigma / sqrt(2 lam_s).
Independently the seesaw fixes M_R = (y_nu * 174.1 GeV)^2 / m_nu with m_nu = 0.05 eV (atmospheric scale).
The two must agree: a check with no free parameter left.
Run: python3 -I scripts/chain_theory/r13b_sigma_running.py
"""
import math
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

K = 1 / (16 * math.pi**2)
MT, MH_TARGET = 172.57, 125.20
VEW = 246.22 / math.sqrt(2)  # 174.1 GeV


def beta_sm(t, y):  # (gY, g2, g3, yt, lam): one loop + two-loop gauge + dominant two-loop yt, lam (as in Q1)
    gY, g2, g3, yt, lam = y
    gY2, g22, g32, yt2 = gY**2, g2**2, g3**2, yt**2
    return [K * 41 / 6 * gY**3 + K**2 * gY**3 * (199 / 18 * gY2 + 9 / 2 * g22 + 44 / 3 * g32 - 17 / 6 * yt2),
            -K * 19 / 6 * g2**3 + K**2 * g2**3 * (3 / 2 * gY2 + 35 / 6 * g22 + 12 * g32 - 3 / 2 * yt2),
            -K * 7 * g3**3 + K**2 * g3**3 * (11 / 6 * gY2 + 9 / 2 * g22 - 26 * g32 - 2 * yt2),
            K * yt * (9 / 2 * yt2 - 8 * g32 - 9 / 4 * g22 - 17 / 12 * gY2)
            + K**2 * yt * (-12 * yt2**2 + 36 * g32 * yt2 - 108 * g32**2 + 6 * lam**2 - 12 * lam * yt2),
            K * (24 * lam**2 + 12 * lam * yt2 - 6 * yt2**2 - 3 * lam * (3 * g22 + gY2) + 3 / 8 * (2 * g22**2 + (g22 + gY2) ** 2))
            + K**2 * (-312 * lam**3 - 144 * lam**2 * yt2 - 3 * lam * yt2**2 + 30 * yt2**3 + 80 * lam * g32 * yt2 - 32 * g32 * yt2**2)]


def beta_cc(t, y):  # (gY, g2, g3, yt, ynu, lh, lhs, ls): CC12 eqs. 16-20 + our gauge running
    gY, g2, g3, yt, yn, lh, lhs, ls = y
    gY2, g22, g32, yt2, yn2 = gY**2, g2**2, g3**2, yt**2, yn**2
    bg = beta_sm(t, [gY, g2, g3, yt, lh])[:3]
    dyt = yt / (32 * math.pi**2) * (-(17 / 6 * gY2 + 9 / 2 * g22 + 16 * g32) + 9 * yt2 + 2 * yn2)
    dyn = yn / (32 * math.pi**2) * (-(3 / 2 * gY2 + 9 / 2 * g22) + 6 * yt2 + 5 * yn2)
    dlh = K * ((12 * yt2 + 4 * yn2 - (3 * gY2 + 9 * g22)) * lh
               + 2 * (12 * lh**2 + lhs**2 + 3 / 16 * (gY2**2 + 2 * gY2 * g22 + 3 * g22**2) - 3 * yt2**2 - yn2**2))
    dlhs = K * lhs * (0.5 * (12 * yt2 + 4 * yn2 - 3 * gY2 - 9 * g22) + 4 * (3 * lh + 1.5 * ls + 2 * lhs))
    dls = K * (8 * lhs**2 + 18 * ls**2)
    return bg + [dyt, dyn, dlh, dlhs, dls]


def boundary(mt=172.57, mh=125.20, a3=0.1180, mW=80.369):  # Buttazzo et al. 2013 at mu = m_t
    return [0.35830 + 0.00011 * (mt - 173.34) - 0.00020 * (mW - 80.384) / 0.014,
            0.64779 + 0.00004 * (mt - 173.34) + 0.00011 * (mW - 80.384) / 0.014,
            1.1666 + 0.00314 * (a3 - 0.1184) / 0.0007 - 0.00046 * (mt - 173.34),
            0.93690 + 0.00556 * (mt - 173.34) - 0.00042 * (a3 - 0.1184) / 0.0007,
            0.12604 + 0.00206 * (mh - 125.15) - 0.00004 * (mt - 173.34)]


def mh_from_lam(lam_mt):
    return 125.15 + (lam_mt - 0.12604 + 0.00004 * (MT - 173.34)) / 0.00206


L = math.log
SM = solve_ivp(beta_sm, (L(MT), L(1.3e19)), boundary(), rtol=1e-10, atol=1e-12, dense_output=True)


def run_above(Lam, ms, n):
    """y_t(m_s) from measurement; shoot y_nu(m_s) so y_nu(Lam) = sqrt(n) y_t(Lam); return the state at Lam."""
    g_ms = SM.sol(L(ms))
    def mismatch(ynu_ms):
        y0 = [*g_ms[:4], ynu_ms, 0.0, 0.0, 0.0]
        s = solve_ivp(beta_cc, (L(ms), L(Lam)), y0, rtol=1e-9, atol=1e-12)
        return s.y[4, -1] - math.sqrt(n) * s.y[3, -1], s.y[:, -1]
    if n == 0:
        return mismatch(0.0)[1]
    ynu = brentq(lambda x: mismatch(x)[0], 1e-4, 3.0)
    return mismatch(ynu)[1]


def predict(Lam, ms, n, gsel=2):
    top = run_above(Lam, ms, n)
    g = top[gsel]
    lh, lhs, ls = (n * n + 3) / (n + 3) ** 2 * 4 * g * g, 2 * n / (n + 3) * 4 * g * g, 8 * g * g
    y0 = [*top[:5], lh, lhs, ls]
    s = solve_ivp(beta_cc, (L(Lam), L(ms)), y0, rtol=1e-9, atol=1e-12)
    at = s.y[:, -1]
    lam_sm = at[5] - at[6] ** 2 / at[7]
    s2 = solve_ivp(beta_sm, (L(ms), L(MT)), [*SM.sol(L(ms))[:4], lam_sm], rtol=1e-10, atol=1e-12)
    out = dict(mh=mh_from_lam(s2.y[4, -1]), lam_sm_ms=lam_sm, stab_Lam=lhs**2 < lh * ls,
               stab_ms=at[6] ** 2 < at[5] * at[7], ynu_ms=at[4], ls_ms=at[7], g=g, lh_Lam=lh,
               ynu_Lam=top[4], yt_Lam=top[3], yt_cc=math.sqrt(4 / (n + 3)) * g, maxc=max(abs(v) for v in s.y[5:].ravel()))
    return out


print("SM-only check (n = 0, no portal): m_H at Lambda = 1e16, m_sigma = 1e10:",
      f"{predict(1e16, 1e10, 0.0)['mh']:.1f} GeV  (Q1 found ~131-176 GeV for the window; n = 0 is lam~ = g^2/3)")
print()
print("(1) THE n THAT GIVES m_H = 125.20 GeV")
print("  Lambda    m_sigma    n*       y_nu/y_t   lam_h(Lam)/g^2  lam_SM(m_s)  stable@Lam  stable@m_s  y_t(Lam): measured vs CC12")
rows = []
for Lam in (1e13, 1e15, 1e16, 1e17):
    for ms in (1e8, 1e10, 1e11, 1e12, 1e13, 1e14):
        if ms >= Lam / 10:
            continue
        f = lambda n: predict(Lam, ms, n)["mh"] - MH_TARGET
        # m_H falls from its n = 0 value (CC12's ~170 GeV) as n grows, then turns back up at large n;
        # take the first crossing of 125.20 on a grid, then refine
        grid = np.arange(0.0, 4.01, 0.1)
        vals = [f(x) for x in grid]
        cross = next((i for i in range(len(grid) - 1) if vals[i] > 0 >= vals[i + 1]), None)
        if cross is None:
            print(f"  {Lam:7.0e}  {ms:7.0e}   no crossing for n in [0, 4] (min m_H {min(vals) + MH_TARGET:.1f})")
            continue
        nstar = brentq(f, grid[cross], grid[cross + 1], xtol=1e-6)
        r = predict(Lam, ms, nstar)
        rows.append((Lam, ms, nstar, r))
        print(f"  {Lam:7.0e}  {ms:7.0e}  {nstar:6.3f}   {math.sqrt(nstar):6.3f}     {r['lh_Lam'] / r['g']**2:6.3f}        "
              f"{r['lam_sm_ms']:+.4f}     {str(r['stab_Lam']):<5}       {str(r['stab_ms']):<5}       {r['yt_Lam']:.3f} vs {r['yt_cc']:.3f}")
print("  (stability = CC12 eq. 33, lam_hs^2 < lam_h lam_s, the condition for the vacuum with both vevs to be a minimum;")
print("   at Lambda it is equivalent to n < sqrt(3) = 1.732)")

print()
print("(2) SEESAW CONSISTENCY: does the sigma scale that gives 125.2 GeV agree with the scale the neutrino mass demands?")
print("  M_R from CC12's normalisation: 2 g(Lam) m_sigma / sqrt(2 lam_s(m_sigma));  M_R from the seesaw: (y_nu(m_s) * 174.1)^2 / m_nu")
for m_nu_eV in (0.05,):
    m_nu = m_nu_eV * 1e-9
    print(f"  m_nu = {m_nu_eV} eV:")
    for Lam in (1e13, 1e15, 1e16, 1e17):
        sub = [(ms, n, r) for (La, ms, n, r) in rows if La == Lam]
        cells = []
        for ms, n, r in sub:
            MR_cc = 2 * r["g"] * ms / math.sqrt(2 * r["ls_ms"])
            MR_ss = (r["ynu_ms"] * VEW) ** 2 / m_nu
            cells.append(f"m_s={ms:.0e}: CC {MR_cc:.1e} / seesaw {MR_ss:.1e}")
        print(f"    Lambda {Lam:.0e}:  " + " | ".join(cells))

print()
print("(3) THE SELF-CONSISTENT POINT: m_sigma such that CC12's M_R equals the seesaw's M_R, with n set by m_H = 125.20")


def nstar(Lam, ms):
    f = lambda n: predict(Lam, ms, n)["mh"] - MH_TARGET
    grid = np.arange(1.0, 2.51, 0.1)
    vals = [f(x) for x in grid]
    i = next(i for i in range(len(grid) - 1) if vals[i] > 0 >= vals[i + 1])
    return brentq(f, grid[i], grid[i + 1], xtol=1e-5)


for m_nu_eV in (0.05, 0.10):
    m_nu = m_nu_eV * 1e-9
    for Lam in (1e16, 1e17):
        def gap(lms):
            ms = math.exp(lms); n = nstar(Lam, ms); r = predict(Lam, ms, n)
            return math.log(2 * r["g"] * ms / math.sqrt(2 * r["ls_ms"])) - math.log((r["ynu_ms"] * VEW) ** 2 / m_nu)
        lms = brentq(gap, math.log(1e13), math.log(Lam / 10), xtol=1e-4)
        ms = math.exp(lms); n = nstar(Lam, ms); r = predict(Lam, ms, n)
        MR = 2 * r["g"] * ms / math.sqrt(2 * r["ls_ms"])
        print(f"  m_nu = {m_nu_eV:.2f} eV, Lambda = {Lam:.0e}: m_sigma = {ms:.2e} GeV, M_R = {MR:.2e} GeV, n = {n:.3f} "
              f"(y_nu/y_t = {math.sqrt(n):.3f}), m_H = {r['mh']:.2f}, lam_SM(m_sigma) = {r['lam_sm_ms']:+.4f}, "
              f"stable at Lambda: {r['stab_Lam']}, at m_sigma: {r['stab_ms']}")
print("  At the self-consistent point the threshold sits above the Standard Model's instability scale (~10^10.6 GeV),")
print("  so lam_SM(m_sigma) < 0: m_H = 125.20 is reproduced, but the electroweak vacuum stays metastable, as in the SM.")
