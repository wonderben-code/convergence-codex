#!/usr/bin/env python3
"""L15 hardened — three generations, an error budget, and the top-mass test.

Builds on r13b_sigma_running.py (Chamseddine-Connes 2012 boundary conditions with sigma; sigma decoupled at m_sigma;
Standard-Model running below). Three upgrades:
 (a) three generations: CC12's boundary conditions use traces of all Yukawa matrices,
     a = tr(Yn+Yn + Ye+Ye + 3(Yu+Yu + Yd+Yd)), b = tr((Yn+Yn)^2 + (Ye+Ye)^2 + 3((Yu+Yu)^2 + (Yd+Yd)^2)), lam_h = 4 g^2 b / a^2.
     How much do the lighter generations move lam_h(Lambda)?
 (b) an error budget for n* (the value giving m_H = 125.20) and the seesaw-consistent sigma scale: matching scale
     (m_sigma/2, m_sigma, 2 m_sigma), the dominant two-loop Standard-Model terms added above sigma, m_t +- 0.29 GeV,
     alpha_s +- 0.0009, and g = g3 or g2 at Lambda.
 (c) the top-mass test: CC12's spectral action also fixes y_t(Lambda) = sqrt(4/(n+3)) g (their eq. 22). With n fixed by
     m_H, that predicts the top mass with no free parameter. The Tree's L15 does not adopt this relation; the test says
     what adopting it would cost.
Run: python3 -I scripts/chain_theory/r13d_higgs_hardened.py
"""
import math
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

K = 1 / (16 * math.pi**2)
L = math.log
VEW = 246.22 / math.sqrt(2)


def beta_sm(t, y):
    gY, g2, g3, yt, lam = y
    gY2, g22, g32, yt2 = gY**2, g2**2, g3**2, yt**2
    return [K * 41 / 6 * gY**3 + K**2 * gY**3 * (199 / 18 * gY2 + 9 / 2 * g22 + 44 / 3 * g32 - 17 / 6 * yt2),
            -K * 19 / 6 * g2**3 + K**2 * g2**3 * (3 / 2 * gY2 + 35 / 6 * g22 + 12 * g32 - 3 / 2 * yt2),
            -K * 7 * g3**3 + K**2 * g3**3 * (11 / 6 * gY2 + 9 / 2 * g22 - 26 * g32 - 2 * yt2),
            K * yt * (9 / 2 * yt2 - 8 * g32 - 9 / 4 * g22 - 17 / 12 * gY2)
            + K**2 * yt * (-12 * yt2**2 + 36 * g32 * yt2 - 108 * g32**2 + 6 * lam**2 - 12 * lam * yt2),
            K * (24 * lam**2 + 12 * lam * yt2 - 6 * yt2**2 - 3 * lam * (3 * g22 + gY2) + 3 / 8 * (2 * g22**2 + (g22 + gY2) ** 2))
            + K**2 * (-312 * lam**3 - 144 * lam**2 * yt2 - 3 * lam * yt2**2 + 30 * yt2**3 + 80 * lam * g32 * yt2 - 32 * g32 * yt2**2)]


def make_beta_cc(two_loop):
    def beta_cc(t, y):
        gY, g2, g3, yt, yn, lh, lhs, ls = y
        gY2, g22, g32, yt2, yn2 = gY**2, g2**2, g3**2, yt**2, yn**2
        bg = beta_sm(t, [gY, g2, g3, yt, lh])[:3]
        dyt = yt / (32 * math.pi**2) * (-(17 / 6 * gY2 + 9 / 2 * g22 + 16 * g32) + 9 * yt2 + 2 * yn2)
        dyn = yn / (32 * math.pi**2) * (-(3 / 2 * gY2 + 9 / 2 * g22) + 6 * yt2 + 5 * yn2)
        dlh = K * ((12 * yt2 + 4 * yn2 - (3 * gY2 + 9 * g22)) * lh
                   + 2 * (12 * lh**2 + lhs**2 + 3 / 16 * (gY2**2 + 2 * gY2 * g22 + 3 * g22**2) - 3 * yt2**2 - yn2**2))
        dlhs = K * lhs * (0.5 * (12 * yt2 + 4 * yn2 - 3 * gY2 - 9 * g22) + 4 * (3 * lh + 1.5 * ls + 2 * lhs))
        dls = K * (8 * lhs**2 + 18 * ls**2)
        if two_loop:   # the dominant two-loop Standard-Model terms for y_t and lam_h
            dyt += K**2 * yt * (-12 * yt2**2 + 36 * g32 * yt2 - 108 * g32**2 + 6 * lh**2 - 12 * lh * yt2)
            dlh += K**2 * (-312 * lh**3 - 144 * lh**2 * yt2 - 3 * lh * yt2**2 + 30 * yt2**3 + 80 * lh * g32 * yt2 - 32 * g32 * yt2**2)
        return bg + [dyt, dyn, dlh, dlhs, dls]
    return beta_cc


def boundary(mt=172.57, mh=125.20, a3=0.1180, mW=80.369):
    return [0.35830 + 0.00011 * (mt - 173.34) - 0.00020 * (mW - 80.384) / 0.014,
            0.64779 + 0.00004 * (mt - 173.34) + 0.00011 * (mW - 80.384) / 0.014,
            1.1666 + 0.00314 * (a3 - 0.1184) / 0.0007 - 0.00046 * (mt - 173.34),
            0.93690 + 0.00556 * (mt - 173.34) - 0.00042 * (a3 - 0.1184) / 0.0007,
            0.12604 + 0.00206 * (mh - 125.15) - 0.00004 * (mt - 173.34)]


class Model:
    def __init__(self, mt=172.57, a3=0.1180, two_loop=False, gsel=2, match=1.0):
        self.mt, self.a3, self.gsel, self.match = mt, a3, gsel, match
        self.bcc = make_beta_cc(two_loop)
        self.SM = solve_ivp(beta_sm, (L(mt), L(1.3e19)), boundary(mt=mt, a3=a3), rtol=1e-10, atol=1e-12, dense_output=True)

    def mh_from_lam(self, lam_mt):
        return 125.15 + (lam_mt - 0.12604 + 0.00004 * (self.mt - 173.34)) / 0.00206

    def top_state(self, Lam, ms, n):
        g = self.SM.sol(L(ms))
        def mism(ynu):
            s = solve_ivp(self.bcc, (L(ms), L(Lam)), [*g[:4], ynu, 0, 0, 0], rtol=1e-9, atol=1e-12)
            return s.y[4, -1] - math.sqrt(n) * s.y[3, -1], s.y[:, -1]
        return mism(brentq(lambda x: mism(x)[0], 1e-4, 3.0))[1] if n > 0 else mism(0.0)[1]

    def predict(self, Lam, ms, n):
        top = self.top_state(Lam, ms, n); g = top[self.gsel]
        y0 = [*top[:5], (n * n + 3) / (n + 3) ** 2 * 4 * g * g, 2 * n / (n + 3) * 4 * g * g, 8 * g * g]
        mmatch = ms * self.match
        s = solve_ivp(self.bcc, (L(Lam), L(mmatch)), y0, rtol=1e-9, atol=1e-12)
        at = s.y[:, -1]
        lam_sm = at[5] - at[6] ** 2 / at[7]
        s2 = solve_ivp(beta_sm, (L(mmatch), L(self.mt)), [*self.SM.sol(L(mmatch))[:4], lam_sm], rtol=1e-10, atol=1e-12)
        return dict(mh=self.mh_from_lam(s2.y[4, -1]), g=g, ls=at[7], ynu=at[4])

    def nstar(self, Lam, ms):
        f = lambda n: self.predict(Lam, ms, n)["mh"] - 125.20
        grid = np.arange(1.0, 2.51, 0.1); vals = [f(x) for x in grid]
        i = next(i for i in range(len(grid) - 1) if vals[i] > 0 >= vals[i + 1])
        return brentq(f, grid[i], grid[i + 1], xtol=1e-5)

    def selfconsistent(self, Lam, m_nu=0.05e-9):
        def gap(lms):
            ms = math.exp(lms); n = self.nstar(Lam, ms); r = self.predict(Lam, ms, n)
            return L(2 * r["g"] * ms / math.sqrt(2 * r["ls"])) - L((r["ynu"] * VEW) ** 2 / m_nu)
        ms = math.exp(brentq(gap, L(3e13), L(Lam / 10), xtol=1e-3))
        return ms, self.nstar(Lam, ms)

    def top_prediction(self, Lam, ms, n):
        """Impose CC12's y_t(Lambda) = sqrt(4/(n+3)) g, run down, and read off m_t."""
        top = self.top_state(Lam, ms, n); g = top[self.gsel]
        yt_L = math.sqrt(4 / (n + 3)) * g
        yn_L = math.sqrt(n) * yt_L
        s = solve_ivp(self.bcc, (L(Lam), L(ms)), [*top[:3], yt_L, yn_L, 0, 0, 0], rtol=1e-9, atol=1e-12)
        gs = s.y[:, -1]
        s2 = solve_ivp(beta_sm, (L(ms), L(self.mt)), [*gs[:4], 0.126], rtol=1e-10, atol=1e-12)
        yt_mt = s2.y[3, -1]
        return 173.34 + (yt_mt - 0.93690 + 0.00042 * (self.a3 - 0.1184) / 0.0007) / 0.00556, yt_L, top[3]


# (a) three generations
print("(a) THREE GENERATIONS IN THE BOUNDARY CONDITION")
mod = Model()
Lam = 1e16
sm = mod.SM.sol(L(Lam)); yt_L = sm[3]
ratios = {"u": (1.27e-3 / 172.57, 0.62 / 172.57, 1.0), "d": (2.7e-3 / 172.57, 0.053 / 172.57, 2.84 / 172.57),
          "e": (0.511e-3 / 172.57, 0.1057 / 172.57, 1.777 / 172.57)}
for n_ in (1.65,):
    yn = math.sqrt(n_)
    Yu = np.diag(ratios["u"]) * yt_L; Yd = np.diag(ratios["d"]) * yt_L; Ye = np.diag(ratios["e"]) * yt_L
    def ab(Yn):
        H = lambda Y: Y.conj().T @ Y
        a = np.trace(H(Yn) + H(Ye) + 3 * (H(Yu) + H(Yd))).real
        b = np.trace(H(Yn) @ H(Yn) + H(Ye) @ H(Ye) + 3 * (H(Yu) @ H(Yu) + H(Yd) @ H(Yd))).real
        return b / a**2
    third_only = (n_ * n_ + 3) / (n_ + 3) ** 2
    full_hier = ab(np.diag([1e-6, 1e-3, yn]) * yt_L)
    full_flat = ab(np.diag([yn, yn, yn]) * yt_L / math.sqrt(3))
    print(f"  b/a^2, third generation only (CC12's approximation): {third_only:.6f}")
    print(f"  all three generations, hierarchical neutrino Yukawas:  {full_hier:.6f}  (shift {100*(full_hier/third_only-1):+.3f}%)")
    print(f"  all three, neutrino Yukawa spread over generations:     {full_flat:.6f}  (shift {100*(full_flat/third_only-1):+.1f}%)")
print("  the quark and charged-lepton generations change nothing visible; the neutrino Yukawa's flavour structure does,")
print("  and it is unmeasured: it is the one place three generations matter.")

# (b) error budget
print("\n(b) ERROR BUDGET (Lambda = 1e16; n* at m_sigma = 2e14, then the seesaw-consistent m_sigma)")
cases = {"central": Model(), "match m_sigma/2": Model(match=0.5), "match 2 m_sigma": Model(match=2.0),
         "two-loop SM terms above sigma": Model(two_loop=True), "m_t + 0.29": Model(mt=172.86), "m_t - 0.29": Model(mt=172.28),
         "alpha_s + 0.0009": Model(a3=0.1189), "alpha_s - 0.0009": Model(a3=0.1171), "g = g2 at Lambda": Model(gsel=1)}
res = {}
for name, m in cases.items():
    ns = m.nstar(1e16, 2e14)
    res[name] = ns
    print(f"  {name:<32} n* = {ns:.4f}")
vals = np.array(list(res.values()))
print(f"  n* range: {vals.min():.3f} to {vals.max():.3f} (central {res['central']:.3f})")
ms_c, n_c = cases["central"].selfconsistent(1e16)
ms_2, n_2 = cases["two-loop SM terms above sigma"].selfconsistent(1e16)
print(f"  seesaw-consistent sigma scale: central {ms_c:.2e} GeV (n = {n_c:.3f}); with two-loop terms {ms_2:.2e} GeV (n = {n_2:.3f})")

# (c) the top-mass test
print("\n(c) THE TOP-MASS TEST: impose CC12's y_t(Lambda) = sqrt(4/(n+3)) g with n = n*")
for Lam_ in (1e16, 1e17):
    for gname, m in (("g3", Model()), ("g2", Model(gsel=1))):
        ms_, n_ = m.selfconsistent(Lam_)
        mt_pred, ytL, yt_meas_L = m.top_prediction(Lam_, ms_, n_)
        print(f"  Lambda = {Lam_:.0e}, g = {gname}: y_t(Lambda) = {ytL:.3f} (measured-running value {yt_meas_L:.3f}) "
              f"-> predicted m_t = {mt_pred:.1f} GeV  (measured 172.57 +- 0.29)")
