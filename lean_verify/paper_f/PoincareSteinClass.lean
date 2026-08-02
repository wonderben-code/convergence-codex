/-
  PoincareSteinClass: the Gaussian Poincaré Inequality on the STEIN CLASS
  =======================================================================

  The W^{1,2}(γ) item's staircase, climbed by the non-circular route the
  watchlist maps (ledgers in the companion repository codex-internal). The
  class is defined by an INTEGRAL pairing — Gaussian integration by parts
  against every polynomial — not by Hermite coefficients, so the
  circularity trap the watchlist warns about ("defining the class BY the
  coefficients and then proving Poincaré for it") does not arise: the
  coefficient recursion is a THEOREM about the class, not its definition.

  WHAT THIS FILE PROVES (exactly this, nothing more):

  1. `SteinPair f g` — the class: f, g ∈ L²(γ) with
     ∫ g·q dγ = ∫ f·(X·q − q′) dγ for EVERY polynomial q ("g is the
     derivative of f in the Gaussian-IBP sense against polynomials").
  2. `coeff_steinPair` — the coefficient recursion cₙ(g) = (n+1)·cₙ₊₁(f),
     now a consequence of the pairing at q = Hₙ plus the Hermite
     recurrence — the same two lines as before, with the analytic
     hypothesis replaced by the defining pairing.
  3. **`poincare_stein`** — THE POINCARÉ INEQUALITY ON THE CLASS:
     Var_γ(f) ≤ ∫ g² dγ for every Stein pair. Pure Parseval bookkeeping:
     both series, the recursion, and n! ≤ (n+1)·n! termwise. No
     smoothness, no growth bound, no pointwise derivative anywhere in the
     hypotheses — only square-integrability and the pairing.
  4. `steinPair_of_polyGrowth` — every everywhere-differentiable f of
     polynomial growth (with derivative of polynomial growth) forms a
     Stein pair with its derivative: `stein_general` IS the pairing. So
     the class CONTAINS the whole class of `poincare_beyond_polynomials`,
     and `poincare_beyond_subsumed` re-derives that theorem as a
     two-line corollary — a strict generalisation (witnessed: item 6).
  5. `steinPair_id_one` — non-vacuity witness: (X, 1) is a Stein pair.
     (At this pair both sides of the inequality equal 1 — sharpness of
     the constant is already proven at measure level in the estate,
     `GaussianPoincare.no_better_constant`; not re-proven here.)
  6. `stein_strict` — the STRICTNESS WITNESS for item 4's claim: `fJump`
     (equal to X everywhere except a jump at 0) forms a Stein pair with
     the constant function 1, provably has NO everywhere-pointwise
     derivative (it is discontinuous at 0), and satisfies the Poincaré
     conclusion. The hypotheses of `poincare_beyond_polynomials` FAIL
     for it while the Stein hypotheses HOLD: the extension of the
     theorem's reach is strict. (fJump agrees with X off a γ-null set,
     so as an L² ELEMENT it is nothing new — the strictness certified
     is at the level of which FUNCTIONS the hypotheses admit, exactly
     what "strict generalisation" means for a theorem.)

  WHAT THE CLASS IS AND IS NOT (the honesty box the staircase demands):

  * The pairing is against POLYNOMIALS. The textbook W^{1,2}(γ) uses
    Cc^∞ test functions. The two test families are INCOMPARABLE — no
    nonzero polynomial is compactly supported, and no nonzero Cc^∞
    function is a polynomial — so NO inclusion between the Stein class
    and the Cc^∞-defined Sobolev space follows a priori in EITHER
    direction, and none is claimed; the relation is recorded as open on
    the watchlist. What IS proven: the Stein class contains every
    everywhere-differentiable function of polynomial growth (item 4)
    and strictly more (item 6), and Poincaré holds on all of it
    (item 3) — which strictly extends every Poincaré statement
    previously in the estate.
  * One dimension, the standard Gaussian, and nothing about the spectral
    action — all exactly as disclaimed upstream.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import PoincareBeyondPolynomials

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open scoped NNReal ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace PoincareSteinClass

open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
  PoincareBeyondPolynomials

/-- **The Stein class**: pairs (f, g) of square-integrable functions with
    the Gaussian integration-by-parts pairing against every polynomial —
    "g is the derivative of f in the Gaussian-IBP sense". An integral
    condition, NOT a coefficient condition. -/
def SteinPair (f g : ℝ → ℝ) : Prop :=
  MemLp f 2 gauss ∧ MemLp g 2 gauss ∧
    ∀ q : ℝ[X], ∫ x, g x * q.eval x ∂gauss
      = ∫ x, f x * (X * q - derivative q).eval x ∂gauss

/-- The coefficient recursion, now a THEOREM about the class: the pairing
    at q = Hₙ plus the Hermite recurrence Hₙ₊₁ = X·Hₙ − Hₙ′. -/
theorem coeff_steinPair {f g : ℝ → ℝ} (h : SteinPair f g) (n : ℕ) :
    coeff n g = (n + 1 : ℝ) * coeff (n + 1) f := by
  have hstein := h.2.2 (H n)
  have hH : X * H n - derivative (H n) = H (n + 1) := (H_succ n).symm
  rw [hH] at hstein
  simp only [HermiteBessel.coeff]
  rw [hstein]
  have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfac]
  have hne : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-- **THE GAUSSIAN POINCARÉ INEQUALITY ON THE STEIN CLASS**:
    Var_γ(f) ≤ ∫ g² dγ for every Stein pair — no smoothness, no growth
    bound, no pointwise derivative in the hypotheses. -/
theorem poincare_stein {f g : ℝ → ℝ} (h : SteinPair f g) :
    (∫ x, f x ^ 2 ∂gauss) - (∫ x, f x ∂gauss) ^ 2
      ≤ ∫ x, g x ^ 2 ∂gauss := by
  have PA := parseval f h.1
  have PB := parseval g h.2.1
  have hrec : (fun n => (n.factorial : ℝ) * coeff n g ^ 2)
      = fun (n : ℕ) => ((n : ℝ) + 1) * (((n + 1 : ℕ)).factorial : ℝ)
          * coeff (n + 1) f ^ 2 := by
    funext n
    rw [coeff_steinPair h n]
    have hfac : (((n + 1 : ℕ)).factorial : ℝ)
        = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    ring
  rw [hrec] at PB
  have hc0 : coeff 0 f = ∫ x, f x ∂gauss := by
    simp only [HermiteBessel.coeff]
    have hH0 : (H 0) = 1 := by
      unfold GaussianPoincare.H
      rw [Polynomial.hermite_zero]
      simp
    rw [hH0]
    simp
  have PA' : HasSum (fun k => ((k + 1).factorial : ℝ) * coeff (k + 1) f ^ 2)
      ((∫ x, f x ^ 2 ∂gauss) - (∫ x, f x ∂gauss) ^ 2) := by
    refine (hasSum_nat_add_iff (f := fun n =>
      (n.factorial : ℝ) * coeff n f ^ 2) 1).mpr ?_
    have hval : ((∫ x, f x ^ 2 ∂gauss) - (∫ x, f x ∂gauss) ^ 2)
        + ∑ i ∈ Finset.range 1, (i.factorial : ℝ) * coeff i f ^ 2
        = ∫ x, f x ^ 2 ∂gauss := by
      rw [Finset.sum_range_one, hc0]
      simp [Nat.factorial]
    rw [hval]
    exact PA
  have hle : ∀ k : ℕ, (((k + 1 : ℕ)).factorial : ℝ) * coeff (k + 1) f ^ 2
      ≤ ((k : ℝ) + 1) * (((k + 1 : ℕ)).factorial : ℝ) * coeff (k + 1) f ^ 2 := by
    intro k
    have h1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    nlinarith [mul_nonneg
      (Nat.cast_nonneg ((k + 1 : ℕ).factorial) : (0 : ℝ) ≤ _)
      (sq_nonneg (coeff (k + 1) f))]
  exact hasSum_le hle PA' PB

/-- **The old class embeds**: every everywhere-differentiable function of
    polynomial growth forms a Stein pair with its derivative —
    `stein_general` IS the pairing. -/
theorem steinPair_of_polyGrowth {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    SteinPair f f' := by
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have hfcont : Continuous f := hdiff.continuous
  have hf'meas : AEStronglyMeasurable f' gauss := by
    have hfd : f' = deriv f := funext fun x => ((hderiv x).deriv).symm
    rw [hfd]
    exact (measurable_deriv f).aestronglyMeasurable
  exact ⟨memLp_of_polyGrowth hfcont.aestronglyMeasurable hb,
    memLp_of_polyGrowth hf'meas hb',
    fun q => stein_general hderiv hb hb' q⟩

/-- The beyond-polynomials Poincaré theorem, re-derived as a corollary of
    the Stein-class inequality: the extension is strict — witnessed by
    `stein_strict` below — and the old theorem is an instance. -/
theorem poincare_beyond_subsumed {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    {C : ℝ} {m : ℕ}
    (hb : ∀ x, |f x| ≤ C * (1 + x ^ 2) ^ m)
    (hb' : ∀ x, |f' x| ≤ C * (1 + x ^ 2) ^ m) :
    (∫ x, f x ^ 2 ∂gauss) - (∫ x, f x ∂gauss) ^ 2
      ≤ ∫ x, f' x ^ 2 ∂gauss :=
  poincare_stein (steinPair_of_polyGrowth hderiv hb hb')

/-- Non-vacuity: (X, 1) is a Stein pair. (Both sides of the inequality
    equal 1 there; sharpness of the constant is
    `GaussianPoincare.no_better_constant`, proven upstream.) -/
theorem steinPair_id_one : SteinPair (fun x => x) (fun _ => 1) := by
  refine steinPair_of_polyGrowth (C := 1) (m := 1)
    (fun x => hasDerivAt_id x) (fun x => ?_) (fun x => ?_)
  · have h1 : |x| ≤ 1 + x ^ 2 := by
      nlinarith [sq_nonneg (|x| - 1), sq_abs x, abs_nonneg x]
    simpa using h1
  · have h0 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
    rw [abs_one]
    nlinarith

/-! ## The strictness witness

The review demanded evidence for "strict": a member of the Stein class
that NO pointwise-derivative hypothesis can reach. `fJump` is X with a
jump planted at 0 — a γ-null modification, so the PAIRING survives; but
the function is discontinuous at 0, so it is not differentiable there,
and `poincare_beyond_polynomials` cannot apply to it. -/

/-- X with a jump at the origin: not continuous, hence nowhere near the
    everywhere-differentiable class — yet a Stein-pair member. -/
def fJump : ℝ → ℝ := fun x => if x = 0 then 5 else x

theorem fJump_ae_eq : fJump =ᵐ[gauss] fun x => x := by
  have hna : NoAtoms (gauss : Measure ℝ) := noAtoms_gaussianReal one_ne_zero
  have h0 : (gauss : Measure ℝ) {0} = 0 := measure_singleton 0
  have hmem : {(0 : ℝ)}ᶜ ∈ ae gauss := by
    rw [mem_ae_iff, compl_compl]
    exact h0
  filter_upwards [hmem] with x hx
  simp only [fJump, if_neg (Set.mem_compl_singleton_iff.mp hx)]

/-- **(fJump, 1) is a Stein pair**: the pairing is an integral identity,
    so it survives the null modification. -/
theorem steinPair_jump : SteinPair fJump (fun _ => 1) := by
  obtain ⟨hid, hone, hpair⟩ := steinPair_id_one
  refine ⟨hid.ae_eq fJump_ae_eq.symm, hone, fun q => ?_⟩
  have hcongr : ∫ x, fJump x * (X * q - derivative q).eval x ∂gauss
      = ∫ x, x * (X * q - derivative q).eval x ∂gauss := by
    refine integral_congr_ae ?_
    filter_upwards [fJump_ae_eq] with x hx
    rw [hx]
  rw [hcongr]
  exact hpair q

/-- **fJump has no everywhere-pointwise derivative**: it is discontinuous
    at 0 (value 5, limit 0), and everywhere-differentiable functions are
    continuous. So no theorem hypothesising `∀ x, HasDerivAt f (g x) x`
    can reach it. -/
theorem jump_not_pointwise_differentiable :
    ¬ ∃ g : ℝ → ℝ, ∀ x, HasDerivAt fJump (g x) x := by
  rintro ⟨g, hg⟩
  have hc : ContinuousAt fJump 0 := (hg 0).continuousAt
  have h5 : fJump 0 = 5 := by simp [fJump]
  have hlim5 : Filter.Tendsto fJump (nhdsWithin 0 {0}ᶜ) (nhds (5 : ℝ)) := by
    have h := hc.tendsto
    rw [h5] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim0 : Filter.Tendsto fJump (nhdsWithin 0 {0}ᶜ) (nhds (0 : ℝ)) := by
    have hid : Filter.Tendsto (fun x : ℝ => x) (nhdsWithin 0 {0}ᶜ)
        (nhds (0 : ℝ)) :=
      (continuous_id.tendsto 0).mono_left nhdsWithin_le_nhds
    refine hid.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [fJump, if_neg (Set.mem_compl_singleton_iff.mp hx)]
  have h50 := tendsto_nhds_unique hlim5 hlim0
  norm_num at h50

/-- **The strictness certificate, in one statement**: (fJump, 1) is in the
    class, no pointwise-derivative hypothesis covers fJump, and the
    Poincaré conclusion holds for it anyway. -/
theorem stein_strict :
    SteinPair fJump (fun _ => 1)
      ∧ (¬ ∃ g : ℝ → ℝ, ∀ x, HasDerivAt fJump (g x) x)
      ∧ ((∫ x, fJump x ^ 2 ∂gauss) - (∫ x, fJump x ∂gauss) ^ 2
          ≤ ∫ x, (fun _ => (1 : ℝ)) x ^ 2 ∂gauss) :=
  ⟨steinPair_jump, jump_not_pointwise_differentiable,
    poincare_stein steinPair_jump⟩

end PoincareSteinClass
