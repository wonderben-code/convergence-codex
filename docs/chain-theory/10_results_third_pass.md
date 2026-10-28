# Results — third pass: R13 (the σ field) and R10 (the webs in M₂₅₆)

**Date:** 28 October 2026. These are the first two items of the v3 work list in *The Refined Gaps* v2
(DOI 10.5281/zenodo.23724193, §A8). Scripts are in `scripts/chain_theory/`. As before, this is one side's
reading; corrections are recorded in `07_reading_log.md`.

## R13 · The σ field — confirmed: σ is forced, and with it the window gives m_H = 125.20 GeV

**Pre-registered (v2 §A8).** The Tree's Pati–Salam finite geometry, with a Majorana entry in its
finite Dirac operator, yields a scalar singlet σ, and with σ the boundary condition reproduces
m_H ≈ 125 GeV.
- **Confirms:** σ arises and m_H lands at 125.2 within the running's error.
- **Refutes:** no Majorana entry or no singlet on the Tree's algebra. L15 is then refuted as
  physics.

### Part A — on the Tree's own 16, σ is not optional (`r13_sigma_field.py`, exact arithmetic)

**The setup.** This is the Tree's 16 as `PatiSalamOnSixteen` builds it:
- su(4) acts as X ⊗ 1 on the left block (4,2,1) and as −Xᵀ ⊗ 1 on the right block (4̄,1,2);
- su(2)_L and su(2)_R each act on their own block;
- Y = T₃R + (B−L)/2.

A Majorana entry is a symmetric bilinear ψᵀMψ.

| Question | Answer |
|---|---|
| Pati–Salam-invariant Majorana entries | **none** (dimension 0) |
| Standard-Model-invariant Majorana entries | **exactly one**: ν_R ν_R (lepton colour, T₃R = −½, Y = 0) |
| The Pati–Salam module that direction generates | **30-dimensional**, su(2)_R Casimir 2 (a triplet) and su(4) Casimir 9/2 (the 10): it is **(10̄, 1, 3)** |

**So a Pati–Salam-covariant Dirac operator cannot carry a constant Majorana mass.** Once neutrinos
get Majorana masses (the seesaw), that term must be a **field** in (10̄,1,3), and its unique
Standard-Model-singlet component is **σ**. Chamseddine, Connes and van Suijlekom reach the same field
content by relaxing the first-order condition (JHEP 11 (2013) 132: "(3_R,1_L,10)"). Here it follows
from covariance alone, on the Tree's own representation.

What this does not show: that the Tree's cascade *generates* the field as an inner fluctuation of
its own Dirac operator. The Tree does not yet have a finite Dirac operator with Yukawa and Majorana
entries. That step stays open.

### Part B — with σ, the window reproduces the Higgs mass (`r13b_sigma_running.py`)

**The model** is Chamseddine–Connes, *Resilience of the spectral standard model* (JHEP 09 (2012) 104):
- the potential V = ¼(λ_h h⁴ + 2λ_hσ h²σ² + λ_σ σ⁴), with H†H = h²/2;
- boundary conditions at Λ: λ_h = (n²+3)/(n+3)²·4g², λ_hσ = 2n/(n+3)·4g², λ_σ = 8g², and
  y_ν = √n·y_t. Here g = g₃(Λ), as in the Tree's `HiggsBridge`.

As n runs over [0, ∞), λ_h(Λ) runs over [g², 4g²], inside the Tree's window [g²/24, 4g²]. Their
one-loop RGEs apply above the σ mass.

**One improvement on the 2012 paper.** It ran every coupling down to M_Z. Here σ and ν_R are
decoupled at m_σ with the tree-level threshold λ_SM(m_σ) = λ_h − λ_hσ²/λ_σ (their eq. 32), and the
Standard Model runs below with our validated running (Q1). The gauge couplings and y_t are fixed by
measurement.

**Result 1: the n that gives m_H = 125.20 GeV.**
- **n\* ≈ 1.59–1.74 (y_ν/y_t ≈ 1.26–1.32 at Λ)**, for every Λ from 10¹³ to 10¹⁷ GeV and every m_σ
  from 10⁸ to 10¹⁴ GeV. The answer barely moves.
- At that solution λ_h(Λ) ≈ 1.05–1.07 g², so λ̃ ≈ 0.26 g², close to the window's Chamseddine–Connes
  point g²/4.
- The potential is stable at Λ (n < √3) in every case except one corner (Λ = 10¹⁷, m_σ = 10⁸).

**Result 2: the seesaw fixes the σ scale, and the solution is self-consistent.** In the 2012 paper's
normalisation the Majorana mass and the σ mass are tied: M_R = 2g·m_σ/√(2λ_σ(m_σ)), which is about
m_σ/1.2 to m_σ/1.4. Independently, the seesaw with the observed neutrino mass demands
M_R = (y_ν·174 GeV)²/m_ν. Requiring both, with n set by m_H:

| m_ν | Λ (GeV) | m_σ (GeV) | M_R (GeV) | n | m_H (GeV) |
|---|---|---|---|---|---|
| 0.05 eV | 10¹⁶ | 2.5 × 10¹⁴ | 1.8 × 10¹⁴ | 1.66 | 125.20 |
| 0.05 eV | 10¹⁷ | 2.0 × 10¹⁴ | 1.6 × 10¹⁴ | 1.65 | 125.20 |
| 0.10 eV | 10¹⁶ | 1.2 × 10¹⁴ | 8.7 × 10¹³ | 1.65 | 125.20 |
| 0.10 eV | 10¹⁷ | 9.6 × 10¹³ | 8.1 × 10¹³ | 1.64 | 125.20 |

Once the cutoff is chosen, no free parameter is left: the seesaw sets the scale and the Higgs mass
sets n.

**Result 3: the price is stated plainly.** The self-consistent σ scale, about 10¹⁴ GeV, lies above the
Standard Model's instability scale (about 10^10.6 GeV). So λ_SM(m_σ) < 0 there.
- m_H = 125.20 is reproduced.
- The electroweak vacuum stays **metastable**, exactly as in the measured Standard Model. The
  threshold's well-known bonus, curing the instability, would need m_σ ≲ 10^10.5 GeV, and that
  conflicts with the seesaw by four orders of magnitude in m_ν.

**Two diagnostics, not imposed.**
- The 2012 paper's top boundary condition y_t(Λ) = √(4/(n+3))·g would give 0.47–0.54 at Λ, against
  the measured running value 0.41–0.49. The Tree does not claim that relation.
- The model keeps only the dominant third-generation Yukawas (the 2012 approximation), and the
  running above m_σ is one-loop.

**Verdict on R13: confirmed.**
- σ is forced on the Tree's Pati–Salam branch (Part A).
- With σ, the Tree's window gives m_H = 125.20 GeV at a seesaw-consistent scale, with nothing left to
  tune once Λ is chosen (Part B).

**What this does for L15.** The tension recorded in v2 §A7 has a computed resolution. The
resolution sits inside the Tree's own window and uses a field the Tree's own representation forces.
L15 stays **PARTIAL**: the boundary conditions are cited rather than derived, and the generation of
σ by the cascade's own Dirac operator is still open. What moves is the reading. "In tension with the
measured Higgs mass" becomes "consistent with it, given σ and the seesaw, with the vacuum metastable
as in the Standard Model".

## R10 · The particle webs in M₂₅₆ — refuted

**Pre-registered (v1 §6.8).** Chain Theory's particle webs embed in M₂₅₆ = M₁₆ ⊗ M₁₆, with the hub
assemblies as M₄ factors and the core triangles in the colour blocks. *Kill-condition:* a web needs
more tensor factors than M₂₅₆ provides, or fits only at M₆₅₅₃₆.

**Counting** (`r10_webs_in_the_cascade.py`). A web is a network of maximally entangled pairs, so a
faithful realisation gives every site its own tensor factor. By Q4's Theorem D, a qutrit is never a
tensor factor of a cascade level, because 3 never divides 2ᵐ. It sits only as the corner of a 4
(L13). So each qutrit and each ququart costs 4, and each qubit costs 2. Chain Theory's copy model only
makes every count larger.

| Web | Sites / links | Site product | Faithful size | Smallest level | Fits M₂₅₆? |
|---|---|---|---|---|---|
| α star (Q3) | 4 / 3 | 24 | 2⁵ | M₂₅₆ | yes |
| up quark | 3 / 2 | 12 | 2⁴ | M₁₆ | yes |
| W word | 5 / 4 | 192 | 2⁸ | M₂₅₆ (exactly) | yes |
| photon word | 6 / 5 | 216 | 2⁹ | M₆₅₅₃₆ | **no** |
| electron | 9 / 10 | 3456 | 2¹³ | M₆₅₅₃₆ | **no** |
| muon | 13 / 15 | 110,592 | 2¹⁸ | M_{2³²} | **no** |
| tau | 17 / 20 | 3,538,944 | 2²³ | M_{2³²} | **no** |

**Verdict: refuted, at exactly the pre-registered kill-condition.** The electron's core triangle and
hub fill M₂₅₆ exactly (4⁴ = 256), as v1 pictured. Its five qubits do not fit, and the web fits only
at M₆₅₅₃₆. The size alone already rules out M₂₅₆: 3456 > 256.

**What it means.** §4.6's coincidence holds: the α object first fits at the fourth level, where L6
places the Chamseddine–Connes–Marcolli algebra. But it does **not** extend to Chain Theory's particles.
Those are networks of many pairs, and they live two or three levels higher. The two programmes encode
particles differently: as representation labels on a small space (the Tree, L6) and as webs of pairs
(Chain Theory). Their particles do not meet as a sub-embedding at one level.
- L6 itself is unaffected, since it concerns the Chamseddine–Connes–Marcolli algebra, not Chain
  Theory's webs.
- No grade moves.
- This is the second jointly generated prediction of the series to fail, after R2. It is recorded
  with the same prominence as R13's success.

*An observation, not a claim:* in this count the electron sits at level five and the muon and tau at
level six.

## What changed as a result

- **R13: confirmed.** The L15 reading moves from "in tension" to "consistent given σ and the seesaw;
  vacuum metastable", and the public descriptions are updated to say so. The grade is unchanged.
- **R10: refuted.** It is recorded here and will be scored in v3.
- **Next on the v3 list:** R15 (where the generations live), then R14 (the Higgs cells). R14 now has
  extra point. The Tree's Higgs bidoublet and σ both come from the Pati–Salam scalar sector, so the
  question of whether Chain Theory's closed hub read is the (1,2,2) bears on both.

## Where the three passes leave the Tree (an assessment, 28 October 2026)

**Stronger.**
- **L15, the Higgs.** Two days ago it conflicted with a measured number; now it is consistent
  with it. The repair is a field the Tree's own Pati–Salam structure forces.
- **One independent cross-check passed.** The neutrino mass and the Higgs mass, two separate
  measurements, ask for the same σ scale. That check could have failed.
- **More machine-checked mathematics.** About twenty new Lean theorems
  (`lean_verify/chain_theory/`), each depending only on the standard axioms.
- **The method.** Predictions were made in advance, tested in public, and failures (R2, R10) were
  recorded as prominently as successes.

**Unchanged.**
- **No grade has moved.** The scoreboard is still 6 · 13 · 3 · 2.
- **The two walls are untouched:** gravity (L22) and the mass gap (L23).
- **The Higgs repair is partly borrowed and partly fitted.** It uses Chamseddine–Connes's boundary
  conditions, and one parameter (n ≈ 1.65) is fitted to 125 GeV. Fitting one number with one dial
  is accommodation, not prediction. The seesaw cross-check is what lifts it above a pure fit.
- **Two hoped-for links with Chain Theory failed.** Its generations are not the quaternions (R2),
  and its particle webs do not sit at the Tree's fourth level (R10).

**So:** the Tree is more solid, because it survived contact with data and its weakest physics link
now has a working repair, and it is better tested. It is not more proven. Validation in the strong
sense would be a grade moving, or a prediction made before a measurement. The nearest candidates are
the σ sector (if the cascade's own Dirac operator can be shown to generate σ) and R15 (which can
promote or sink L14).

Nothing in the Tree's scoreboard changes. 6 · 13 · 3 · 2.
