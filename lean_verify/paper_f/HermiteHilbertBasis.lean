/-
  HermiteHilbertBasis.lean — the Hermite system bundled as a Hilbert basis
  of L²(γ), and with it the Sobolev characterisation closed to an iff.

  WHY. `SteinCoefficients` §6 states one missing ingredient, exactly, and
  names its route: *"Riesz–Fischer for a PRESCRIBED coefficient sequence …
  A cleaner route that would give this and much else: bundle `Hₙ/√(n!)` as
  a Mathlib `HilbertBasis` of `L²(γ)` — the estate has completeness
  (`HermiteCompleteness`) and orthogonality already, so the missing piece
  is the packaging."* This file is that packaging, and then the two
  theorems it unlocks.

  WHAT THIS FILE PROVES:
  1. **`hermiteBasis`** — `Hₙ/√(n!)` is a `HilbertBasis ℕ ℝ (Lp ℝ 2 gauss)`.
     Orthonormality is the estate's `hermite_orthogonal_gauss` divided by
     `n!`; the density hypothesis is discharged through
     `Submodule.topologicalClosure_eq_top_iff` from the estate's
     `hermite_complete`, so no partial-sum decomposition is needed. The
     bundling is the content: everything below is a consequence.
  2. **`exists_of_summable`** — the Riesz–Fischer §6 asked for. Given ANY
     sequence `a` with `Σ n!·aₙ² < ∞` there is an `f ∈ L²(γ)` whose
     Hermite coefficients are exactly `a`.
  3. **`steinPair_iff_sobolev`** — and therefore the characterisation
     `SteinCoefficients` could only prove in one direction is now a
     biconditional: **`f` has a Stein partner if and only if
     `Σ (n+1)·n!·cₙ(f)² < ∞`.** `SobolevGauss` names the coefficient side
     and `sobolevGauss_iff_steinDomain` states the equality of the two
     classes. The Gaussian Sobolev space of the watchlist item is now a
     theorem about a class defined by an integral pairing, in both
     directions.
  4. **`exists_memLp_not_steinPair`** — and the characterisation has
     teeth: there is an `f ∈ L²(γ)` with NO Stein partner at all, so the
     summability is a genuine restriction and the Stein class is a PROPER
     subset of `L²(γ)` (`sobolevGauss_proper`). The witness is built BY
     the new Riesz–Fischer, from the coefficient sequence
     `aₙ = 1/(√(n!)·(n+1))` — `Σ n!aₙ² = Σ (n+1)⁻²` converges,
     `Σ (n+1)n!aₙ² = Σ (n+1)⁻¹` does not.
     **The properness is about the class this file defines**, which is the
     Stein class; it is NOT a statement about the `Cc^∞`-defined
     `W^{1,2}(γ)`, whose relation to this one is WALLS W6 and open. The
     estate uses the symbol `W^{1,2}(γ)` for both and that is exactly the
     conflation to avoid, so it is not used as a name below.

  WHAT THIS DOES NOT DO. **Nothing here touches W6.** Whether this class
  coincides with the `Cc^∞`-defined `W^{1,2}(γ)` is a different question,
  still open, still unclaimed. What has closed is the watchlist item's
  PLUMBING residue, which was named as plumbing.

  ABSENT FROM MATHLIB v4.29.1, probed by SHAPE and not by name (ERRATA
  40/42): there is no orthonormal basis or `HilbertBasis` of an
  L²-of-Gaussian anywhere upstream. `Mathlib/RingTheory/Polynomial/
  Hermite/{Basic,Gaussian}.lean` contain polynomial identities and the
  Rodrigues-type derivative formula, and the strings `Orthonormal`,
  `HilbertBasis` and `Lp` do not occur in either; the only concrete
  `HilbertBasis` definitions upstream are `fourierBasis` and
  `mFourierBasis` on the circle. What Mathlib DOES supply, and what this
  file uses, is the constructor `HilbertBasis.mkOfOrthogonalEqBot`, whose
  hypothesis is the orthogonal complement being trivial — i.e. exactly the
  estate's completeness theorem.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SteinCoefficients
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries

namespace HermiteHilbertBasis

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness HermiteBessel HermiteParseval
open PoincareSteinClass SteinCoefficients
open scoped ENNReal

noncomputable section

/-! ## 1. The Hermite vectors of L²(γ)

Two small facts about `√(n!)` first, because every normalisation below
divides by it and `n! > 0` is the only reason that is legal.
-/

theorem sqrt_factorial_pos (n : ℕ) : 0 < Real.sqrt (n.factorial : ℝ) :=
  Real.sqrt_pos.mpr (by exact_mod_cast n.factorial_pos)

theorem sqrt_factorial_ne_zero (n : ℕ) : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
  ne_of_gt (sqrt_factorial_pos n)

theorem sqrt_factorial_mul_self (n : ℕ) :
    Real.sqrt (n.factorial : ℝ) * Real.sqrt (n.factorial : ℝ) = (n.factorial : ℝ) :=
  Real.mul_self_sqrt (Nat.cast_nonneg _)

/-- `Hₙ` as an element of `L²(γ)`. -/
def HL (n : ℕ) : Lp ℝ 2 gauss :=
  (GaussianPoincare.memLp_polynomial_gaussianReal (H n) 0 1).toLp fun x => (H n).eval x

theorem coeFn_HL (n : ℕ) : (HL n : ℝ → ℝ) =ᵐ[gauss] fun x => (H n).eval x :=
  MemLp.coeFn_toLp _

/-- **The pairing of `Hₙ` with an arbitrary L² vector is its coefficient.**
    This is the bridge that makes every statement below a statement about
    `HermiteBessel.coeff` rather than about abstract inner products. -/
theorem inner_HL (n : ℕ) (F : Lp ℝ 2 gauss) :
    inner ℝ (HL n) F = (n.factorial : ℝ) * coeff n (F : ℝ → ℝ) := by
  have hF : (Lp.memLp F).toLp (F : ℝ → ℝ) = F := Lp.toLp_coeFn F (Lp.memLp F)
  have h1 : inner ℝ (HL n) F = ∫ x, (H n).eval x * (F : ℝ → ℝ) x ∂gauss := by
    conv_lhs => rw [← hF]
    simp only [HL]
    rw [inner_toLp]
  rw [h1, ← integral_mul_H (F : ℝ → ℝ) n]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem inner_HL_HL (m n : ℕ) :
    inner ℝ (HL m) (HL n) = if m = n then (m.factorial : ℝ) else 0 := by
  simp only [HL]
  rw [inner_toLp]
  exact hermite_orthogonal_gauss m n

/-- The NORMALISED Hermite system `Hₙ/√(n!)`. -/
def eH (n : ℕ) : Lp ℝ 2 gauss := (Real.sqrt (n.factorial : ℝ))⁻¹ • HL n

theorem orthonormal_eH : Orthonormal ℝ eH := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [eH, eH, real_inner_smul_left, real_inner_smul_right, inner_HL_HL]
  split_ifs with h
  · subst h
    have hne := sqrt_factorial_ne_zero m
    field_simp
    exact (Real.sq_sqrt (Nat.cast_nonneg (m.factorial))).symm
  · ring

/-! ## 2. Density, from completeness rather than from partial sums

The obvious route to the `HilbertBasis.mk` hypothesis is to exhibit each
`f` as the limit of its Hermite partial sums, which the estate has
(`tendsto_SN_L2`) — but that needs the partial sum identified as an
element of the span, which is `Lp` bookkeeping. The orthogonal-complement
route is shorter and uses the estate's completeness theorem verbatim.
-/

theorem orthogonal_eq_bot : (Submodule.span ℝ (Set.range eH))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  have hmem : ∀ n : ℕ, eH n ∈ Submodule.span ℝ (Set.range eH) := fun n =>
    Submodule.subset_span ⟨n, rfl⟩
  have hz : ∀ n : ℕ, inner ℝ (HL n) F = 0 := by
    intro n
    have h1 : inner ℝ (eH n) F = 0 := (Submodule.mem_orthogonal _ _).mp hF _ (hmem n)
    rw [eH, real_inner_smul_left] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (inv_eq_zero.mp h) (sqrt_factorial_ne_zero n)
    · exact h
  have hae : (F : ℝ → ℝ) =ᵐ[gauss] 0 := by
    refine hermite_complete _ (Lp.memLp F) fun n => ?_
    have h2 := hz n
    rw [inner_HL] at h2
    rw [integral_mul_H]
    exact h2
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae

/-- Density of the Hermite span in norm form — the classical statement,
    kept as an export. It is NOT on the critical path: Mathlib's
    `mkOfOrthogonalEqBot` consumes `orthogonal_eq_bot` directly. -/
theorem span_dense : ⊤ ≤ (Submodule.span ℝ (Set.range eH)).topologicalClosure :=
  le_of_eq (Submodule.topologicalClosure_eq_top_iff.mpr orthogonal_eq_bot).symm

/-- **THE HERMITE FUNCTIONS ARE A HILBERT BASIS OF L²(γ).** The estate has
    had orthogonality and completeness since 1 August (`HermiteCompleteness`,
    added in ba9d4c2); this is the bundling that turns them into a Mathlib
    object with an API. -/
def hermiteBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 gauss) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_eH orthogonal_eq_bot

theorem hermiteBasis_apply (n : ℕ) : hermiteBasis n = eH n :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot orthonormal_eH orthogonal_eq_bot) n

/-! ## 3. The representation is the coefficient sequence

`HilbertBasis.repr` is an isometric equivalence onto `ℓ²`. Composed with
the dictionary of §1 it says: the `ℓ²` sequence attached to `f` is
`√(n!)·cₙ(f)`. Everything the file delivers is read off this one line.
-/

theorem repr_apply (F : Lp ℝ 2 gauss) (n : ℕ) :
    (hermiteBasis.repr F : ℕ → ℝ) n
      = Real.sqrt (n.factorial : ℝ) * coeff n (F : ℝ → ℝ) := by
  have hne := sqrt_factorial_ne_zero n
  have key : (Real.sqrt (n.factorial : ℝ))⁻¹ * (n.factorial : ℝ)
      = Real.sqrt (n.factorial : ℝ) := by
    refine mul_left_cancel₀ hne ?_
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul, sqrt_factorial_mul_self]
  rw [HilbertBasis.repr_apply_apply, hermiteBasis_apply, eH, real_inner_smul_left,
    inner_HL, ← mul_assoc, key]

/-- Parseval, re-derived from the basis. The estate proved this by hand in
    `HermiteParseval`; that it drops out of the bundling is a consistency
    check on the bundling, not a new result. -/
theorem norm_sq_eq_tsum (F : Lp ℝ 2 gauss) :
    ‖F‖ ^ 2 = ∑' n : ℕ, (n.factorial : ℝ) * coeff n (F : ℝ → ℝ) ^ 2 := by
  have h0 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  have hnorm := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞))
    (by rw [h0]; norm_num) (hermiteBasis.repr F)
  rw [h0] at hnorm
  simp only [Real.rpow_natCast] at hnorm
  rw [← hermiteBasis.repr.norm_map F, hnorm]
  refine tsum_congr fun n => ?_
  rw [repr_apply, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-! ## 4. Riesz–Fischer for a PRESCRIBED coefficient sequence

This is the theorem `SteinCoefficients` §6 named as missing. The estate's
`HermiteParseval.tendsto_SN_L2` builds the L² limit of the partial sums of
a function's OWN expansion; nothing constructed a function from
coefficients given in advance, and the Stein converse needs exactly that.
-/

theorem memℓp_of_summable {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => (n.factorial : ℝ) * a n ^ 2) :
    Memℓp (fun n : ℕ => Real.sqrt (n.factorial : ℝ) * a n) 2 := by
  refine memℓp_gen ?_
  have hp : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [hp]
  refine ha.congr fun n => ?_
  rw [Real.rpow_natCast, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

/-- **RIESZ–FISCHER FOR A PRESCRIBED HERMITE SEQUENCE.** Any square-summable
    (in the `n!`-weighted sense) sequence is the coefficient sequence of an
    honest element of `L²(γ)`. -/
theorem exists_of_summable {a : ℕ → ℝ}
    (ha : Summable fun n : ℕ => (n.factorial : ℝ) * a n ^ 2) :
    ∃ f : ℝ → ℝ, MemLp f 2 gauss ∧ ∀ n, coeff n f = a n := by
  set b : lp (fun _ : ℕ => ℝ) 2 :=
    ⟨fun n => Real.sqrt (n.factorial : ℝ) * a n, memℓp_of_summable ha⟩ with hbdef
  refine ⟨((hermiteBasis.repr.symm b : Lp ℝ 2 gauss) : ℝ → ℝ), Lp.memLp _, fun n => ?_⟩
  have hrepr : hermiteBasis.repr (hermiteBasis.repr.symm b) = b :=
    LinearIsometryEquiv.apply_symm_apply _ _
  have h1 := repr_apply (hermiteBasis.repr.symm b) n
  rw [hrepr] at h1
  have h2 : (b : ℕ → ℝ) n = Real.sqrt (n.factorial : ℝ) * a n := rfl
  rw [h2] at h1
  exact (mul_left_cancel₀ (sqrt_factorial_ne_zero n) h1).symm

/-! ## 5. The Stein characterisation, closed

`SteinCoefficients.summable_sobolev_of_steinPair` proved the summability
NECESSARY. With §4 it is also sufficient, and the coefficient description
of the Gaussian Sobolev space is a biconditional about a class that was
defined by an integral pairing.
-/

/-- The coefficient-side definition: `f ∈ L²(γ)` with the Sobolev-type
    summability. This is the object the watchlist item calls
    `W^{1,2}(γ)`. -/
def SobolevGauss (f : ℝ → ℝ) : Prop :=
  MemLp f 2 gauss ∧ Summable fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * coeff n f ^ 2

/-- The summability is exactly what the candidate partner's coefficients
    need in order to be admissible. -/
theorem summable_partner_coeff {f : ℝ → ℝ}
    (h : Summable fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * coeff n f ^ 2) :
    Summable fun n : ℕ =>
      (n.factorial : ℝ) * ((n + 1 : ℝ) * coeff (n + 1) f) ^ 2 := by
  have hshift : Summable fun n : ℕ =>
      (((n : ℝ) + 1) + 1) * (((n + 1).factorial : ℝ)) * coeff (n + 1) f ^ 2 := by
    have := (summable_nat_add_iff 1).mpr h
    refine this.congr fun n => ?_
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hshift
  have hfs : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hfs]
  have hsq : (0 : ℝ) ≤ coeff (n + 1) f ^ 2 := sq_nonneg _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  nlinarith [hsq, hn]

/-- **THE CONVERSE OF `summable_sobolev_of_steinPair`.** The summability
    produces a partner, so it is sufficient and not merely necessary. -/
theorem steinPair_of_sobolev {f : ℝ → ℝ} (hf : MemLp f 2 gauss)
    (h : Summable fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * coeff n f ^ 2) :
    ∃ g : ℝ → ℝ, SteinPair f g := by
  obtain ⟨g, hg, hgc⟩ := exists_of_summable (summable_partner_coeff h)
  exact ⟨g, steinPair_of_coeff hf hg fun n => hgc n⟩

/-- **THE BICONDITIONAL.** For `f ∈ L²(γ)`: `f` has a Stein partner exactly
    when `Σ (n+1)·n!·cₙ(f)² < ∞`. The class is defined by Gaussian
    integration by parts against every polynomial; the coefficient
    condition is a theorem about it, now in both directions. -/
theorem steinPair_iff_sobolev {f : ℝ → ℝ} (hf : MemLp f 2 gauss) :
    (∃ g : ℝ → ℝ, SteinPair f g) ↔
      Summable fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * coeff n f ^ 2 :=
  ⟨fun ⟨_, hg⟩ => summable_sobolev_of_steinPair hg, steinPair_of_sobolev hf⟩

/-- The two classes, as classes: the coefficient-defined Gaussian Sobolev
    space IS the domain of the Stein pairing. -/
theorem sobolevGauss_iff_steinDomain (f : ℝ → ℝ) :
    SobolevGauss f ↔ MemLp f 2 gauss ∧ ∃ g : ℝ → ℝ, SteinPair f g := by
  constructor
  · rintro ⟨hf, h⟩
    exact ⟨hf, steinPair_of_sobolev hf h⟩
  · rintro ⟨hf, hg⟩
    exact ⟨hf, (steinPair_iff_sobolev hf).mp hg⟩

/-! ## 6. The characterisation has teeth

A biconditional between two conditions that happen to hold for everything
would be worth nothing. The new Riesz–Fischer settles this in the sharpest
form available: it BUILDS a square-integrable function with no Stein
partner, so the Sobolev condition is a genuine restriction on `L²(γ)`.
-/

/-- The witness sequence: `aₙ = 1/(√(n!)·(n+1))`. -/
def badSeq (n : ℕ) : ℝ := (Real.sqrt (n.factorial : ℝ))⁻¹ * ((n : ℝ) + 1)⁻¹

theorem badSeq_weight (n : ℕ) :
    (n.factorial : ℝ) * badSeq n ^ 2 = (((n : ℝ) + 1) ^ 2)⁻¹ := by
  have hne := sqrt_factorial_ne_zero n
  have hs := sqrt_factorial_mul_self n
  have hfac : ((n.factorial : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hinv : ((Real.sqrt (n.factorial : ℝ))⁻¹) ^ 2 = ((n.factorial : ℝ))⁻¹ := by
    rw [inv_pow, pow_two, hs]
  rw [badSeq, mul_pow, hinv, ← mul_assoc, mul_inv_cancel₀ hfac, one_mul, inv_pow]

theorem summable_badSeq :
    Summable fun n : ℕ => (n.factorial : ℝ) * badSeq n ^ 2 := by
  have hbase : Summable fun m : ℕ => 1 / (m : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hshift := (summable_nat_add_iff 1).mpr hbase
  refine hshift.congr fun n => ?_
  rw [badSeq_weight]
  push_cast
  rw [one_div]

theorem not_summable_badSeq :
    ¬ Summable fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * badSeq n ^ 2 := by
  intro hcon
  have hrew : (fun n : ℕ => ((n : ℝ) + 1) * (n.factorial : ℝ) * badSeq n ^ 2)
      = fun n : ℕ => 1 / (((n : ℕ) + 1 : ℕ) : ℝ) := by
    funext n
    have h := badSeq_weight n
    have hpos : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [mul_assoc, h]
    push_cast
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hpos, one_mul, one_div]
  rw [hrew] at hcon
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp hcon)

/-- **THE STEIN CLASS IS A PROPER SUBSET OF L²(γ).** Not an observation
    about the definition: a function is constructed, by §4, and the
    biconditional of §5 refutes every candidate partner at once. -/
theorem exists_memLp_not_steinPair :
    ∃ f : ℝ → ℝ, MemLp f 2 gauss ∧ ¬ ∃ g : ℝ → ℝ, SteinPair f g := by
  obtain ⟨f, hf, hfc⟩ := exists_of_summable summable_badSeq
  refine ⟨f, hf, fun hex => not_summable_badSeq ?_⟩
  have h := (steinPair_iff_sobolev hf).mp hex
  refine h.congr fun n => ?_
  rw [hfc]

/-- The same statement in the language of §5: the Sobolev class is proper.
    Both halves of `⊊`, so that "proper subset" is a theorem and not a
    reading of one. -/
theorem sobolevGauss_proper :
    (∀ f : ℝ → ℝ, SobolevGauss f → MemLp f 2 gauss)
      ∧ ∃ f : ℝ → ℝ, MemLp f 2 gauss ∧ ¬ SobolevGauss f := by
  refine ⟨fun f hf => hf.1, ?_⟩
  obtain ⟨f, hf, hns⟩ := exists_memLp_not_steinPair
  exact ⟨f, hf, fun hs => hns ((sobolevGauss_iff_steinDomain f).mp hs).2⟩

/-! ## 7. What this does and does not settle

**Settled.** The watchlist's `W^{1,2}(γ)` item carried two residues after
`SteinCoefficients`. The first was named as PLUMBING — Riesz–Fischer for a
prescribed coefficient sequence — and §4 is it, by the route that entry
named. With it, §5 upgrades the necessary condition to a characterisation
and §6 shows the characterisation is not vacuous.

**Not settled, and not touched.** Whether this class coincides with the
`Cc^∞`-defined `W^{1,2}(γ)` (WALLS W6). Nothing in this file mentions
`Cc^∞`, and the two test families remain incomparable (no nonzero
polynomial has compact support, no nonzero `Cc^∞` function is a
polynomial — `ERRATA 35`). What §5 does change is the SHAPE an attempt
could take: one of the two classes now has a coefficient description, so
the comparison can be posed as a question about which sequences the
`Cc^∞` definition admits. Whether that is easier is unknown and is not
claimed here.

**One honesty note about §3.** `norm_sq_eq_tsum` is Parseval, which the
estate already had from `HermiteParseval.parseval`. It is included as a
CHECK on the bundling — if the `HilbertBasis` had been assembled with a
wrong normalisation, this is where it would show — and not as a new
theorem. **How independent it is was measured, not asserted**: a walk of
the transitive constant-dependency closure of `norm_sq_eq_tsum` (51636
constants) contains neither `HermiteParseval.parseval` nor
`HermiteParseval.tendsto_SN_L2`, so the partial-sum route is genuinely
not reused. It DOES contain `HermiteCompleteness.hermite_complete`, which
both routes need and which this file does not reprove — so the check is
independent of the Parseval proof, not of the completeness theorem. The
same walk over `steinPair_iff_sobolev` gives the same three answers.
-/

/-! ## 8. Review round 38 — the attacks this file invites

Three, and all three are answered above rather than left for a reviewer.

**"The basis could be mis-normalised and everything would still typecheck."**
`orthonormal_eH` is the guard, and it is not vacuous: `Orthonormal`
demands norm exactly 1, so a wrong power of `n!` fails there. §3's
independent Parseval is the second guard.

**"Riesz–Fischer might produce the zero function every time."** It cannot:
§4 returns an `f` with `coeff n f = a n` for the GIVEN `a`, and §6 feeds
it a sequence that is nowhere zero. The witness of
`exists_memLp_not_steinPair` therefore has nonzero coefficients at every
index.

**"The biconditional might be between two conditions that always hold."**
§6 is exactly the refutation, and it is constructive.
-/

theorem badSeq_ne_zero (n : ℕ) : badSeq n ≠ 0 := by
  rw [badSeq]
  have h1 : (Real.sqrt (n.factorial : ℝ))⁻¹ ≠ 0 :=
    inv_ne_zero (sqrt_factorial_ne_zero n)
  have h2 : (((n : ℝ) + 1))⁻¹ ≠ 0 := by
    refine inv_ne_zero ?_
    positivity
  exact mul_ne_zero h1 h2

/-- The witness of §6 is not the zero function: every one of its Hermite
    coefficients is nonzero. -/
theorem exists_not_steinPair_nonzero :
    ∃ f : ℝ → ℝ, MemLp f 2 gauss ∧ (∀ n, coeff n f ≠ 0) ∧ ¬ ∃ g : ℝ → ℝ, SteinPair f g := by
  obtain ⟨f, hf, hfc⟩ := exists_of_summable summable_badSeq
  refine ⟨f, hf, fun n => by rw [hfc]; exact badSeq_ne_zero n, fun hex => ?_⟩
  refine not_summable_badSeq ?_
  have h := (steinPair_iff_sobolev hf).mp hex
  refine h.congr fun n => ?_
  rw [hfc]

/-- The identity function is in the Sobolev class — the positive half of
    §6, so that the class is neither everything nor nothing. -/
theorem sobolevGauss_id : SobolevGauss (fun x : ℝ => x) :=
  ⟨steinPair_id_one.1, sobolev_summable_id⟩

end

end HermiteHilbertBasis
