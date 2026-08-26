/-
  FiniteGibbsSum.lean — an integral against a finite-volume Gibbs measure IS the ratio of Boltzmann
  sums, and that is the bridge the magnetisation chain was missing.

  WHY. `IsingIndependentSpins` and everything under it is stated about `num S J A / part S J`, a
  ratio of sums over configurations. `IsingBoundaryField.MagnetisationBound` — the thing the whole
  chain is aimed at — is stated about `∫ σ, magnetisation n σ ∂(isingMeasure n h β)`, an integral
  against a MEASURE. Those are the same number and this estate had never said so; the watchlist
  trigger left by the previous unit was *"when anything in this estate identifies an integral
  against `FiniteGibbs.gibbs` with the corresponding ratio of Boltzmann sums."* **This file is
  that.**

  WHAT IT COMES TO. On a finite space with counting measure, `FiniteGibbs.gibbs β H count` is
  `Z⁻¹ • count.withDensity (ofReal ∘ exp ∘ (−β·H))`, so an integral against it unfolds in three
  moves — `integral_smul_measure`, `integral_withDensity_eq_integral_toReal_smul`, and
  `MeasureTheory.integral_count` — into `(∑ ω, e^{−βH ω}·f ω) / (∑ ω, e^{−βH ω})`. **Every step is a
  Mathlib lemma**; nothing here is new mathematics and the file says so rather than dressing it up.

  THE ONE THING WORTH NOTICING. The denominator is a sum of exponentials over a NONEMPTY finite
  type, hence strictly positive, so the division is honest and `partition_pos` records it. `Ω` must
  be nonempty for that, and every model this is applied to has at least one configuration.

  WHAT IS PROVED.

  * `partition`, `partition_pos` — the real partition function and its positivity;
  * **`integral_gibbs_count`** — `∫ f d(gibbs β H count) = (∑ e^{−βH}·f) / (∑ e^{−βH})`;
  * `integral_gibbs_count_le` and `le_integral_gibbs_count` — the two comparison forms, so that a
    bound proved on the ratio transfers to the integral and back without unfolding anything.

  WHAT THIS IS NOT. It is a change of notation, not a theorem about any model. It says nothing about
  Ising, nothing about boundaries and nothing about magnetisation; it makes those statements
  comparable, which is all a bridge should do.

  ADDENDUM 23 AUGUST 2026 — THE SENTENCE ABOVE BEGINNING "Those are the same number and this estate
  had never said so" IS FALSE, AND IT IS KEPT ABOVE SO THE CORRECTION IS LEGIBLE (`ERRATUM 94`).

  WHAT WAS ALREADY THERE. `BoundaryFieldRatio.integral_isingMeasure`, added **10 August 2026**
  (`4101026`), states
  `∫ σ, f σ ∂(isingMeasure n h β) = (∑_σ f σ·e^{−β·isingHB}) / (∑_σ e^{−β·isingHB})`.
  `isingMeasure n h β` is *definitionally* `FiniteGibbs.gibbs β (isingHB n h) Measure.count`, so
  that
  theorem identifies an integral against `FiniteGibbs.gibbs` with the corresponding ratio of
  Boltzmann
  sums — the exact words of the trigger quoted above. **The trigger was already satisfied on the day
  it was written.** `BoundaryFieldRatio`'s own header says so in as many words: *"It is now an
  identity with a proof rather than a gap."*

  WHAT IS STILL TRUE, AND IT IS NOT NOTHING. `integral_isingMeasure` is about ONE Hamiltonian on ONE
  configuration space. `integral_gibbs_count` is about an arbitrary `H : Ω → ℝ` on an arbitrary
  nonempty finite `Ω`, and that generality is load-bearing exactly once: `IsingBulkFieldBound`
  uses it
  for `isingHBulk`, a DIFFERENT Hamiltonian, which the 10 August theorem does not cover and
  cannot be
  made to cover. `partition_pos`, `Z_toReal` and the two comparison forms are also new. So this file
  is a genuine generalisation whose novelty claim was overstated — not a duplicate, and not the
  first
  of its kind either.

  AND ONE OF THE TWO CALL SITES DID NOT NEED IT. `IsingBoxInteraction` applies the general bridge at
  `isingHB`, where the special case would have served. That is recorded rather than tidied away,
  because it is the measure of how much of this file's motivation survives: half of it.

  HOW IT WAS MISSED. The search was conducted inside `FiniteGibbs.lean`, by shape, looking for a
  general lemma; it was never a grep of the whole estate for the specific instance. `ERRATUM 252`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import FiniteGibbs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace FiniteGibbsSum

open Finset Real MeasureTheory

noncomputable section

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-! ## 1. The partition function as a real sum -/

/-- The partition function, as a real number rather than an `ℝ≥0∞`. -/
def partition (β : ℝ) (H : Ω → ℝ) : ℝ := ∑ ω : Ω, exp (-β * H ω)

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem partition_pos [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) : 0 < partition β H :=
  Finset.sum_pos (fun _ _ => exp_pos _) ⟨Classical.arbitrary Ω, Finset.mem_univ _⟩

omit [MeasurableSpace Ω] [MeasurableSingletonClass Ω] in
theorem partition_ne_zero [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) : partition β H ≠ 0 :=
  ne_of_gt (partition_pos β H)

/-- `FiniteGibbs.Z` against counting measure is that sum, transported through `ENNReal`. -/
theorem Z_eq_ofReal (β : ℝ) (H : Ω → ℝ) :
    FiniteGibbs.Z β H Measure.count = ENNReal.ofReal (partition β H) := by
  rw [FiniteGibbs.Z, lintegral_count, partition, ENNReal.ofReal_sum_of_nonneg
    (fun ω _ => (exp_pos _).le), tsum_fintype]

theorem Z_toReal (β : ℝ) (H : Ω → ℝ) :
    (FiniteGibbs.Z β H Measure.count).toReal = partition β H := by
  rw [Z_eq_ofReal, ENNReal.toReal_ofReal]
  exact Finset.sum_nonneg fun ω _ => (exp_pos _).le

/-! ## 2. The bridge -/

/-- **AN INTEGRAL AGAINST A FINITE-VOLUME GIBBS MEASURE IS A RATIO OF BOLTZMANN SUMS.** Three
Mathlib rewrites and nothing else. -/
theorem integral_gibbs_count [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) (f : Ω → ℝ) :
    ∫ ω, f ω ∂(FiniteGibbs.gibbs β H Measure.count)
      = (∑ ω : Ω, exp (-β * H ω) * f ω) / partition β H := by
  have hmeas : Measurable fun ω : Ω => ENNReal.ofReal (exp (-β * H ω)) :=
    measurable_of_countable _
  have hlt : ∀ᵐ ω ∂(Measure.count : Measure Ω), ENNReal.ofReal (exp (-β * H ω)) < ⊤ :=
    Filter.Eventually.of_forall fun ω => ENNReal.ofReal_lt_top
  rw [FiniteGibbs.gibbs, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hmeas hlt, integral_count,
    ENNReal.toReal_inv, Z_toReal, smul_eq_mul, div_eq_inv_mul]
  refine congrArg _ (Finset.sum_congr rfl fun ω _ => ?_)
  rw [smul_eq_mul, ENNReal.toReal_ofReal (exp_pos _).le]

/-! ## 3. The two comparison forms -/

/-- A lower bound proved on the ratio transfers to the integral. -/
theorem le_integral_gibbs_count [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) (f : Ω → ℝ) {m : ℝ}
    (hm : m ≤ (∑ ω : Ω, exp (-β * H ω) * f ω) / partition β H) :
    m ≤ ∫ ω, f ω ∂(FiniteGibbs.gibbs β H Measure.count) := by
  rwa [integral_gibbs_count]

/-- And an upper bound likewise. -/
theorem integral_gibbs_count_le [Nonempty Ω] (β : ℝ) (H : Ω → ℝ) (f : Ω → ℝ) {m : ℝ}
    (hm : (∑ ω : Ω, exp (-β * H ω) * f ω) / partition β H ≤ m) :
    ∫ ω, f ω ∂(FiniteGibbs.gibbs β H Measure.count) ≤ m := by
  rwa [integral_gibbs_count]

end

end FiniteGibbsSum
