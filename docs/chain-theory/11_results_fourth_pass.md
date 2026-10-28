# Results — fourth pass: R15 (where the generations live) and R14 (the Higgs cells)

**Date:** 28 October 2026. These are items 2 and 3 of the v3 work list in *The Refined Gaps* v2
(DOI 10.5281/zenodo.23724193, §A8).
- Lean: `lean_verify/chain_theory/R14R15HiggsAndPhases.lean`, built in the `ChainTheory` library;
  every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
- Script: `scripts/chain_theory/r14_r15_higgs_and_generations.py`.

## R15 · Where the three generations live — confirmed, and the quaternion reading acquires a definite character

**Pre-registered (v2 §A8).** State L14 on the three-dimensional generation space, and decide which
structure that space carries: the quaternion reading (real; SO(3); no intrinsic phase) or a qutrit
reading (complex; Z₃ with ω).
- **Confirms:** the quaternion reading admits the observed mixing, with its phase from a stated
  source.
- **Refutes:** the quaternion structure forbids CP violation in quark mixing, with no other source.

**L14, stated on the generation space.** The quaternion reading makes the generation space
Im ℍ ⊗ ℂ, carrying the real structure of Im ℍ: a basis (i, j, k) with no intrinsic phase. The
Yukawa matrices are therefore real in that basis.

**The theorem** (`R15.no_cp_phase_from_real_masses`, with the general `det_commutator_of_symm`). For
real 3 × 3 mass matrices, with H = M Mᵀ, det [H_u, H_d] = 0. By Jarlskog's identity
(det [H_u, H_d] = 2i·J·Π(mass-squared differences), cited), J = 0. The measured
J = 3.08 × 10⁻⁵ is not zero.

**So under the quaternion reading, CP violation must come from a vacuum value, not from the
couplings.** In the Tree's scalar sector, the one complex vacuum value that enters quark masses is
the Pati–Salam bidoublet's relative phase: ⟨Φ⟩ = diag(κ₁, κ₂e^{iα}). σ is real. With SU(2)_R-symmetric
Yukawas Y and Ỹ:
- M_u = κ₁Y + κ̄₂Ỹ
- M_d = κ₂Y + κ̄₁Ỹ

**The fit.** Real Y and Ỹ, plus |κ₂/κ₁| and α, were fitted to the six quark masses at M_Z, |V_us|,
|V_cb|, |V_ub| (PDG 2024) and J.

| Fit | χ² | \|κ₂/κ₁\| | α (rad) | θ̄ |
|---|---|---|---|---|
| A: masses + CKM + J | ≈ 10⁻²³ (exact) | 0.0122 | 1.35 | −2.36 rad |
| B: as A, with θ̄ = 0 imposed | ≈ 10⁻²³ (exact) | 0.0115 | −1.11 | 0 |

The controls behave as they must. With α = 0, J = 0 exactly (the theorem). With |κ₂/κ₁| = 1,
m_t = m_b (R14 below).

**Verdict: confirmed as registered.** The quaternion reading admits the observed masses, mixing and
CP violation, with the phase from a stated source in the Tree: the bidoublet's vacuum phase. It is
not refuted.

**What this is, and what it is not.**
- **It is an existence result.** With 20 parameters against 10 observables, an exact fit is
  expected, so the fit alone is not evidence for the reading.
- **The evidence-bearing content is the theorem.** Under the quaternion reading, **CP is an exact
  symmetry of the Tree's Lagrangian, and all observed CP violation in quark mixing is
  spontaneous**, coming from the bidoublet's vacuum phase. This is the reading's definite,
  falsifiable character. A qutrit reading (complex, with ω) admits explicit CP violation and has no
  such character.

**Costs, stated now so they can be tested.**
1. **Strong CP is converted, not solved.** CP exactness sets θ_QCD = 0 at tree level, but
   θ̄ = arg det(M_u M_d) must still vanish. A generic fit gives θ̄ of order one (fit A: −2.36 rad).
   Zero is reachable (fit B), but only by tuning one condition. A Nelson–Barr-type structure would
   be needed to make it automatic.
2. **Spontaneous CP breaking near the electroweak scale threatens domain walls** in cosmology. The
   reading must say where CP breaks relative to inflation.
3. **A second Higgs doublet couples to quarks through Ỹ.** Its flavour-changing effects, and the
   right-handed sector (W_R and V_R), are not tested here.

**L14 stays POSTULATE.** What moves is the reading's content. "Three generations are the imaginary
quaternions" now implies "CP is spontaneously broken". That consequence can be checked against
cosmology, strong CP and the second doublet, and it is new to the record.

## R14 · The Higgs cells — confirmed; and the physical vacuum is almost a product state

**Pre-registered (v2 §A8).** Chain Theory's Higgs is "the closed hub read" (200.1); per 65.2, "the
hub-pair weights at the two qubit copies … equal the doublet of the Higgs entry by entry". Realised on
M₂ ⊗ M₂ (the Tree's own factorisation, with su(2)_L and su(2)_R on the two factors), does it transform
as the Tree's (1,2,2) bidoublet?
- **Confirms:** (2,2).
- **Refutes:** any other representation.

**The computation.**
- The states of the hub pair ℂ² ⊗ ℂ² carry su(2)_L Casimir 3/4 and su(2)_R Casimir 3/4, so they
  form (2,2).
- With Y = T₃R (a colour singlet, B−L = 0), the four states carry charges +1, 0, 0, −1. That is
  the bidoublet [[φ₁⁰, φ₁⁺], [φ₂⁻, φ₂⁰]], two doublets with Y = −½ and +½, entry by entry.
- The *operators* on the pair (reads) decompose as (1⊕3, 1⊕3), which has only integer spin and no
  (2,2).

**Verdict: confirmed.** Chain Theory's hub-pair Higgs is the Tree's bidoublet. The match holds for
the Higgs as a **state** of the pair, which is how 65.2 states it, and never for a read operator.

**A sharpened consequence.** Read as a two-qubit ket, the vacuum ⟨Φ⟩ = diag(κ₁, κ₂) is maximally
entangled exactly when |κ₁| = |κ₂|. The Lean theorems (`R14.equal_vevs_tie_down_to_up`,
`equal_vevs_equal_spectra`) show what that would do. With SU(2)_R-symmetric Yukawas, M_d = u·M_u
with |u| = 1, so the up-type and down-type masses would be identical: m_t = m_b. The measured
masses require |κ₂/κ₁| ≈ 0.012 (R15's fit), and the vacuum ket's entanglement is then about
**0.002 bits**, almost a product state.

This poses a question to Chain Theory, recorded as a question and not a claim. In Chain Theory every
link is a maximally entangled pair (Definition 1.1). If the Higgs vacuum is its hub-pair ket, the
up–down split must come from somewhere other than the vacuum. Chain Theory does assign quark masses
through offices of separate webs, which may be that other route.

## What changed as a result

- **R15: confirmed**, as an existence result. The quaternion reading now implies spontaneous CP
  violation (proved in Lean), with three costs named: strong CP tuning, domain walls, and the
  second doublet.
- **R14: confirmed.** Chain Theory's Higgs is the Tree's bidoublet as a state of the hub pair, and
  the physical vacuum is nearly a product state.
- **For v3:** R13, R14 and R15 are confirmed; R10 is refuted. Still to run: R1′, the L11 choice, R6,
  R5, R8, R12, Q7, and the σ sub-step (the cascade's own Dirac operator generating σ).

Nothing in the Tree's scoreboard changes. 6 · 13 · 3 · 2.
