/-
  HermitePiCoeff.lean — membership of the n-dimensional Gaussian Sobolev
  space, characterised by Hermite coefficients alone.

  WHY. Every file in this chain has defined the class by a PAIRING: against
  the Hermite products, against `Cc^∞`, or against Lebesgue weak
  derivatives. `SteinSmoothPi` proved those three the same class. None of
  them lets a reader decide membership by looking at `f` — each asks for a
  partner to be produced, or for an integral identity to be checked at every
  test function. In one dimension the estate has the answer
  (`HermiteHilbertBasis.steinPair_iff_sobolev`): membership is a single
  summability condition on the coefficients. This file is its n-dimensional
  twin.

  **HOW THIS UNIT WAS FOUND IS THE POINT OF ERRATUM 53.** That erratum was
  written an hour before this file, after three units in a row declared the
  reverse containment out of reach and the third supplied its key. Its
  standing rule is: after every unit, re-read the PREVIOUS unit's `WHAT THIS
  DOES NOT DO`. `SteinSmoothPi`'s said "certifying membership from
  coefficients alone is still open". Re-read one paragraph later, against
  the extraction of `summable_weighted_coeffPi` that happened the same day,
  it was not open at all.

  WHAT THIS FILE PROVES:
  1. **`summable_total_of_steinPairPi`** — the forward direction, and it is
     `HermitePiPoincare.summable_weighted_coeffPi` summed over the finitely
     many coordinates. A member's coefficients satisfy
     `Σ_k |k|·(∏ⱼkⱼ!)·c_k(f)² < ∞`, where `|k| = Σⱼ kⱼ`.
  2. **`exists_partner_of_summable`** — the converse, by CONSTRUCTION. The
     partner's coefficients are forced by `coeffPi_recursion`; their
     weighted sum is the forward direction's series reindexed along
     `succAt · i`; `HermitePiRiesz.exists_of_summable_pi` realises them.
     **The pairing is then an identity between coefficients, not an
     analytic step** — both sides are the same number by construction.
  3. **`steinPairPi_iff_summable`** — the characterisation, and through
     `SteinSmoothPi` the same condition decides membership of the `Cc^∞`
     class and the textbook Lebesgue class too
     (`sobolevWeakPi_iff_summable`).
  4. **`exists_memLp_not_steinPairPi_of_char`** — and properness becomes a
     COROLLARY rather than a construction, which is how the 1-dimensional
     estate is organised. `HermitePiProper`'s witness is reused; what
     changes is that refuting membership no longer needs its own argument.

  WHAT THIS DOES NOT DO — and per ERRATUM 53 this section is a dated claim,
  to be re-read after the next unit rather than trusted. The σ-scaled
  n-dimensional statement is still absent: the 1-d chain has
  `TextbookSobolevScaled` and `n` has no analogue, so every theorem here is
  at variance `1`. Nothing in this file bears on that, because the scaling
  transport acts on the measure and the whole coefficient apparatus is built
  against `gaussPi n` specifically.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SteinSmoothPi
import HermitePiProper

namespace HermitePiCoeff

open MeasureTheory ProbabilityTheory Filter Topology
open GaussianPoincare GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiBasis HermitePiRiesz
open HermitePiStein HermitePiPoincare TextbookSobolevPi
open W6ConversePi SteinSmoothPi

noncomputable section

variable {n : ℕ}

/-! ## 1. The coefficient weight

`|k| = Σⱼ kⱼ`, the total degree of a multi-index. It is what the
one-dimensional `n+1` becomes: there the weight on `cₙ(f)²` is `n+1` because
there is one coordinate to differentiate in, here it is the number of ways
to lower the index by one.
-/

/-- Total degree of a multi-index, as a real number. -/
def deg (n : ℕ) (k : Fin n → ℕ) : ℝ := ∑ j, (k j : ℝ)

theorem deg_nonneg (k : Fin n → ℕ) : 0 ≤ deg n k :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem coord_le_deg (k : Fin n → ℕ) (i : Fin n) : (k i : ℝ) ≤ deg n k :=
  Finset.single_le_sum (f := fun j => (k j : ℝ)) (fun _ _ => Nat.cast_nonneg _)
    (Finset.mem_univ i)

/-- The summand, named once because it appears in every statement below. -/
def wt (n : ℕ) (f : (Fin n → ℝ) → ℝ) (k : Fin n → ℕ) : ℝ :=
  deg n k * (facPi n k * coeffPi n k f ^ 2)

theorem wt_nonneg (f : (Fin n → ℝ) → ℝ) (k : Fin n → ℕ) : 0 ≤ wt n f k :=
  mul_nonneg (deg_nonneg k)
    (mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _))

/-! ## 2. Forward: a member's coefficients are summable against `|k|`

Entirely `HermitePiPoincare.summable_weighted_coeffPi`, which was extracted
from inside `poincare_steinPi` earlier today for a different purpose. A
finite sum over the coordinates turns the per-coordinate statement into the
total one.
-/

theorem summable_total_of_steinPairPi {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SteinPairPi n f g) :
    Summable (wt n f) := by
  classical
  have hs : Summable fun k : Fin n → ℕ =>
      ∑ i : Fin n, (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) :=
    summable_sum fun i _ => summable_weighted_coeffPi n h i
  refine hs.congr fun k => ?_
  rw [wt, deg, Finset.sum_mul]

/-! ## 3. Converse: the partner is constructed from the coefficients

`coeffPi_recursion` says a partner's `i`-th component must have coefficients
`(mᵢ+1)·c_{m+eᵢ}(f)`. That leaves nothing to choose, so the only questions
are whether such a function EXISTS in `L²(γⁿ)` — a summability question,
answered by the same reindex `poincare_steinPi` uses — and whether it then
satisfies the pairing, which turns out to be an identity.
-/

/-- The coefficients the partner is forced to have. -/
def partnerCoeff (n : ℕ) (f : (Fin n → ℝ) → ℝ) (i : Fin n) (m : Fin n → ℕ) : ℝ :=
  ((m i : ℝ) + 1) * coeffPi n (succAt m i) f

/-- Their weighted sum is the forward direction's series, reindexed. -/
theorem summable_partnerCoeff {f : (Fin n → ℝ) → ℝ} (hsum : Summable (wt n f))
    (i : Fin n) :
    Summable fun m : Fin n → ℕ => facPi n m * partnerCoeff n f i m ^ 2 := by
  classical
  set F : (Fin n → ℕ) → ℝ :=
    fun k => (k i : ℝ) * (facPi n k * coeffPi n k f ^ 2) with hFdef
  -- `F` is dominated by the total-degree series, hence summable
  have hF : Summable F := by
    refine hsum.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    · exact mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _))
    · rw [hFdef, wt]
      exact mul_le_mul_of_nonneg_right (coord_le_deg k i)
        (mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _))
  -- and the target series is `F` composed with the injection
  refine (hF.comp_injective (succAt_injective n i)).congr fun m => ?_
  simp only [Function.comp_apply, hFdef, partnerCoeff]
  rw [succAt_self, facPi_succAt]
  push_cast
  ring

/-- **THE PARTNER EXISTS.** Nothing is chosen: the coefficients are forced,
    and `exists_of_summable_pi` realises them. -/
theorem exists_partner_of_summable {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (gaussPi n)) (hsum : Summable (wt n f)) :
    ∃ g : Fin n → ((Fin n → ℝ) → ℝ), SteinPairPi n f g := by
  classical
  choose g hgmem hgcoeff using fun i : Fin n =>
    exists_of_summable_pi n (summable_partnerCoeff hsum i)
  refine ⟨g, hf, hgmem, fun i m => ?_⟩
  -- the pairing, in coefficients: both sides are `facPi (m+eᵢ) · c_{m+eᵢ}(f)`
  have hL : (∫ x, f x * (x i * Hpi n m x
        - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ))) ∂gaussPi n)
      = ∫ x, f x * Hpi n (succAt m i) x ∂gaussPi n :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [Hpi_succ])
  rw [hL, integral_mul_Hpi n (succAt m i) f, integral_mul_Hpi n m (g i),
    hgcoeff i m, partnerCoeff, facPi_succAt]
  ring

/-! ## 4. The characterisation, and what it decides -/

/-- **MEMBERSHIP IS A SUMMABILITY CONDITION ON THE COEFFICIENTS.** The
    n-dimensional twin of `HermiteHilbertBasis.steinPair_iff_sobolev`: an
    `f ∈ L²(γⁿ)` has a gradient partner if and only if
    `Σ_k |k|·(∏ⱼkⱼ!)·c_k(f)² < ∞`. -/
theorem steinPairPi_iff_summable {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (gaussPi n)) :
    (∃ g : Fin n → ((Fin n → ℝ) → ℝ), SteinPairPi n f g) ↔ Summable (wt n f) :=
  ⟨fun ⟨_, hg⟩ => summable_total_of_steinPairPi hg,
    fun hsum => exists_partner_of_summable hf hsum⟩

/-- And therefore the same condition decides membership of the textbook
    Lebesgue-weak-derivative class, through `SteinSmoothPi`. -/
theorem sobolevWeakPi_iff_summable {f : (Fin n → ℝ) → ℝ} (hf : MemLp f 2 (gaussPi n)) :
    (∃ g : Fin n → ((Fin n → ℝ) → ℝ), SobolevWeakPi n f g) ↔ Summable (wt n f) := by
  rw [← steinPairPi_iff_summable hf]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, (steinPairPi_iff_sobolevWeakPi n f g).mpr hg⟩,
    fun ⟨g, hg⟩ => ⟨g, (steinPairPi_iff_sobolevWeakPi n f g).mp hg⟩⟩

/-- And of the `Cc^∞`-tested class. -/
theorem smoothSteinPairPi_iff_summable {f : (Fin n → ℝ) → ℝ}
    (hf : MemLp f 2 (gaussPi n)) :
    (∃ g : Fin n → ((Fin n → ℝ) → ℝ), SmoothSteinPairPi n f g) ↔ Summable (wt n f) := by
  rw [← steinPairPi_iff_summable hf]
  exact ⟨fun ⟨g, hg⟩ => ⟨g, (steinPairPi_iff_smoothSteinPairPi n f g).mpr hg⟩,
    fun ⟨g, hg⟩ => ⟨g, (steinPairPi_iff_smoothSteinPairPi n f g).mp hg⟩⟩

/-! ## 5. Properness, now as a corollary

`HermitePiProper` proved this by construction on the morning of the same
day, using only the forward direction — which is all a REFUTATION needs. With
the biconditional the argument becomes "the series diverges, so by §4 there
is no partner", which is how `HermiteHilbertBasis` organises the
1-dimensional case.

**The dependency direction here is worth stating, because the first draft of
this section had it backwards.** It would be easy — and worthless — to take
`HermitePiProper`'s finished properness theorem and deduce that its witness's
series diverges. That deduces the hypothesis from the conclusion. What is
below instead rebuilds the witness from the same coefficient sequence, proves
the divergence directly out of `HermitePiProper`'s two SERIES lemmas (which
are the reusable half of that file), and lets §4 do the refuting. The
finished properness theorem is not cited.
-/

/-- The witness's total-degree series diverges. `HermitePiProper` proved the
    `kᵢ`-weighted version; `kᵢ ≤ |k|` upgrades it. -/
theorem not_summable_wt_of_coeff (i : Fin n) {f : (Fin n → ℝ) → ℝ}
    (hfc : ∀ k, coeffPi n k f = HermitePiProper.aPi n i k) :
    ¬ Summable (wt n f) := by
  classical
  intro hsum
  refine HermitePiProper.not_summable_weighted_aPi i ?_
  refine hsum.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
  · exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _))
  · rw [wt, hfc k]
    exact mul_le_mul_of_nonneg_right (coord_le_deg k i)
      (mul_nonneg (le_of_lt (facPi_pos n k)) (sq_nonneg _))

/-- **PROPERNESS, GENUINELY AS A COROLLARY.** The witness is built here from
    the same coefficient sequence, its series is shown to diverge, and §4
    refutes membership. `HermitePiProper.exists_memLp_not_steinPairPi` is
    NOT used — only its two series lemmas, which are the reusable half. -/
theorem exists_memLp_not_steinPairPi_of_char (i : Fin n) :
    ∃ f : (Fin n → ℝ) → ℝ, MemLp f 2 (gaussPi n) ∧ ¬ Summable (wt n f)
      ∧ ¬ ∃ g : Fin n → ((Fin n → ℝ) → ℝ), SteinPairPi n f g := by
  classical
  obtain ⟨f, hf, hfc⟩ :=
    exists_of_summable_pi n (HermitePiProper.summable_facPi_aPi i)
  have hns : ¬ Summable (wt n f) := not_summable_wt_of_coeff i hfc
  exact ⟨f, hf, hns, fun hex => hns ((steinPairPi_iff_summable hf).mp hex)⟩

/-! ## 6. Review round 62 — the ways this could be hollow

**"The biconditional could be vacuous in one direction."** It is not:
`HermitePiPoincare.Hpi_mem` and `SteinGeneralPi.sin_coord_mem` are members,
so the left side is inhabited, and §5 exhibits an `f` for which the right
side FAILS, so the condition is not automatic. Both halves of the
biconditional therefore have content.

**"The converse could be circular — using a partner to build a partner."**
It does not. `exists_partner_of_summable` takes only `MemLp f 2` and a
summability statement about numbers, and produces `g` from
`exists_of_summable_pi`, which builds a function out of a coefficient
sequence via the `HilbertBasis`. Nothing about `f` beyond its coefficients
is used, and no candidate partner is assumed.

**"The pairing at the end could be hiding an analytic step."** It is a
`ring` after three rewrites. `Hpi_succ` turns the Stein integrand into
`f·Hpi(m+eᵢ)`, `integral_mul_Hpi` turns both integrals into
`facPi·coeffPi`, and the two sides are then the same product of numbers.
The analysis lives in `exists_of_summable_pi` and, behind it, in stair N2's
completeness — cited, not repeated.

**"§5 could be circular, deducing properness from properness."** The first
draft was: it obtained `HermitePiProper.exists_memLp_not_steinPairPi` and
derived the divergence from it, which is the conclusion implying the
hypothesis. It now builds the witness from the coefficient sequence, proves
divergence from the two series lemmas, and refutes membership through §4;
the finished properness theorem is not cited. `HermitePiProper` remains
independently valid — it needed the forward direction ONLY, which is why it
landed before the characterisation existed.
-/

end

end HermitePiCoeff
