/-
  LatticeFieldTight.lean — the hypothesis discharged: the placed lattice Gaussian fields are tight.

  WHY. `ConfigSpread.isTightMeasureSet_map_spread` takes uniform per-site tail bounds and returns
  tightness, and its own header says what it does not do: *"this file transfers bounds it does not
  supply."* The bounds are in `FieldTightness`, one theorem away — `meas_abs_ge_le`, Chebyshev on a
  variance the estate bounded by `m⁻²` **at every finite simple graph at once**. Composing them is
  the difference between a conditional and a theorem.

  WHAT IS PROVED. **`isTightMeasureSet_gaussianField`** — for any family of finite simple graphs,
  any masses bounded away from zero by a single `m₀`, any placements of their sites into a
  countable ambient site set, and any positive summable weight of total mass at most one, **the
  placed Gaussian fields are a tight family** in Mathlib's sense. No hypothesis remains about the
  measures: the tail bounds are supplied, not assumed.

  THE RADIUS IS THE WHOLE ARITHMETIC. `siteRadius m s = √((m² s)⁻¹)` is chosen so that Chebyshev's
  bound at that radius is exactly `s`; `siteRadius_antitone_mass` then says a smaller mass needs a
  larger radius, which is why one `m₀` below all the masses gives one radius that works for all of
  them. Everything else is bookkeeping between `ℝ` and `ℝ≥0∞`.

  WHAT THIS IS AND IS NOT.

  * It **is** the clause `UNLOCK_WATCHLIST` has carried since 16 August: *"a tightness argument to
    sit on top of the uniform bound"*. There is no analysis left in it;
  * it is **not** a choice of placement. The theorem quantifies over placements, so extension by
    zero and periodic repetition are two of its instances and `ASSUMPTIONS 47` is untouched — the
    author still decides which the estate's narrative uses, and the tightness statement is the same
    either way;
  * it is **not** the infinite-volume limit. Tightness gives *a* limit measure along a subnet;
    identifying that limit as the `ℤ^d` free field needs `G_n(x,y) → G(x,y)`, which nothing here
    touches and which `FieldTightness` named as where the analysis actually lives. **W2's leg does
    not move.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import ConfigSpread
import FieldTightness

namespace LatticeFieldTight

open MeasureTheory GraphLaplacian ConfigSpace ConfigSpread

noncomputable section

variable {ι : Type*}

/-! ## 1. Evaluation is measurable

`gaussianField` lives on `EuclideanSpace ℝ V`, so the site evaluations `ConfigSpread.spread` takes
as a parameter are the `PiLp` coordinate maps, and they are continuous linear.

**This is written inline in §4 rather than as a named lemma, and the reason is a small finding.**
As a standalone theorem its statement elaborates with **no** `Fintype V` — the measurable space on
`PiLp 2 fun _ : V => ℝ` is available without it — and the unused-hypothesis linter says so; but the
*proof* needs `OpensMeasurableSpace`, which arrives only with the finite-dimensional normed
structure and so needs `Fintype V` after all. A hypothesis the statement does not mention and the
proof cannot do without is exactly the shape that makes a lemma awkward to state honestly, so there
is no lemma. -/

/-! ## 2. The radius that makes Chebyshev give exactly what is asked -/

/-- The radius at which `FieldTightness`'s bound at mass `m` reads `s`. -/
def siteRadius (m s : ℝ) : ℝ := Real.sqrt ((m ^ 2 * s)⁻¹)

theorem siteRadius_nonneg (m s : ℝ) : 0 ≤ siteRadius m s := Real.sqrt_nonneg _

theorem siteRadius_pos {m s : ℝ} (hm : m ≠ 0) (hs : 0 < s) : 0 < siteRadius m s := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  exact Real.sqrt_pos.mpr (by positivity)

theorem siteRadius_sq {m s : ℝ} (hm : m ≠ 0) (hs : 0 < s) :
    siteRadius m s ^ 2 = (m ^ 2 * s)⁻¹ := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  exact Real.sq_sqrt (by positivity)

/-- **THE DEFINING PROPERTY**: Chebyshev's bound at this radius is `s` on the nose. -/
theorem inv_mul_siteRadius_sq {m s : ℝ} (hm : m ≠ 0) (hs : 0 < s) :
    (m ^ 2 * siteRadius m s ^ 2)⁻¹ = s := by
  have hm2 : (m : ℝ) ^ 2 ≠ 0 := by positivity
  have hsne : s ≠ 0 := hs.ne'
  rw [siteRadius_sq hm hs]
  field_simp

/-- **A SMALLER MASS NEEDS A LARGER RADIUS.** This is why one `m₀` below every mass in a family
gives one radius that works for the whole family. -/
theorem siteRadius_antitone_mass {m₀ m s : ℝ} (hm₀ : 0 < m₀) (hmm : m₀ ≤ |m|) (hs : 0 < s) :
    siteRadius m s ≤ siteRadius m₀ s := by
  refine Real.sqrt_le_sqrt ?_
  have h1 : m₀ ^ 2 ≤ m ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
  have h2 : (0 : ℝ) < m₀ ^ 2 * s := by positivity
  exact inv_anti₀ h2 (by nlinarith)

/-! ## 3. One site of one graph -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE TAIL AT ONE SITE, AT A RADIUS CHOSEN FROM A LOWER BOUND ON THE MASS.** This is
`FieldTightness.meas_abs_ge_le` with the radius substituted and the mass loosened. -/
theorem gaussian_site_tail_le {m₀ m s : ℝ} (hm₀ : 0 < m₀) (hmm : m₀ ≤ |m|) (hs : 0 < s) (v : V) :
    gaussianField G m {ω : EuclideanSpace ℝ V | siteRadius m₀ s < |ω v|} ≤ ENNReal.ofReal s := by
  have hm : m ≠ 0 := by
    intro h
    rw [h] at hmm
    simp at hmm
    linarith
  have hsub : {ω : EuclideanSpace ℝ V | siteRadius m₀ s < |ω v|}
      ⊆ {ω : EuclideanSpace ℝ V | siteRadius m s ≤ |ω v|} := fun ω hω =>
    le_of_lt (lt_of_le_of_lt (siteRadius_antitone_mass hm₀ hmm hs) hω)
  refine (measure_mono hsub).trans ?_
  have := FieldTightness.meas_abs_ge_le G m hm v (siteRadius_pos hm hs)
  rwa [inv_mul_siteRadius_sq hm hs] at this

/-! ## 4. The family -/

/-- **THE PLACED LATTICE GAUSSIAN FIELDS ARE TIGHT.** No hypothesis about the measures survives:
the per-site bounds are supplied by `FieldTightness`, the radius by §2, the placement is arbitrary,
and the conclusion is Mathlib's `IsTightMeasureSet`. -/
theorem isTightMeasureSet_gaussianField [Countable ι]
    {Λ : Type*} {W : Λ → Type*} [∀ l, Fintype (W l)] [∀ l, DecidableEq (W l)]
    (H : ∀ l, SimpleGraph (W l)) [∀ l, DecidableRel (H l).Adj]
    (m : Λ → ℝ) {m₀ : ℝ} (hm₀ : 0 < m₀) (hmm : ∀ l, m₀ ≤ |m l|)
    (π : ∀ l, ι → Option (W l))
    {w : ι → ℝ} (hwpos : ∀ x, 0 < w x) (hws : Summable w) (hw1 : ∑' x, w x ≤ 1) :
    IsTightMeasureSet (Set.range fun l =>
      (gaussianField (H l) (m l)).map
        (spread (π l) (fun v (ω : EuclideanSpace ℝ (W l)) => ω v))) := by
  refine isTightMeasureSet_map_spread (V := W) (Ω := fun l => EuclideanSpace ℝ (W l))
    (fun l => gaussianField (H l) (m l)) π (fun l v ω => ω v)
    (fun l v => (PiLp.continuous_apply 2 (fun _ : W l => ℝ) v).measurable)
    (fun ε x => siteRadius m₀ (w x * ε.toReal))
    (fun ε x => siteRadius_nonneg _ _)
    (fun x => ENNReal.ofReal (w x)) ?_ ?_
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => (hwpos x).le) hws]
    exact (ENNReal.ofReal_le_ofReal hw1).trans (by simp)
  · intro ε hε l x v _
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · have : ENNReal.ofReal (w x) ≠ 0 := by
        simpa using (hwpos x)
      rw [ENNReal.mul_top this]
      exact le_top
    · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
      have hs : 0 < w x * ε.toReal := mul_pos (hwpos x) hεr
      refine (gaussian_site_tail_le (H l) hm₀ (hmm l) hs v).trans ?_
      rw [ENNReal.ofReal_mul (hwpos x).le, ENNReal.ofReal_toReal hεtop]

/-! ## 5. The hypotheses are simultaneously satisfiable

`ERRATUM 48`: a hypothesis nothing satisfies makes an empty class. The graph family, the masses and
the placements are unconstrained, so the only thing worth checking is the weight — and one exists on
the natural numbers, which is also a countable ambient site set. -/

/-- A positive summable weight of total mass exactly `1` on `ℕ`. -/
theorem exists_weight :
    ∃ w : ℕ → ℝ, (∀ x, 0 < w x) ∧ Summable w ∧ ∑' x, w x ≤ 1 := by
  refine ⟨fun n => 1 / 2 / 2 ^ n, fun n => by positivity, ?_, ?_⟩
  · exact summable_geometric_two' 1
  · rw [tsum_geometric_two' 1]

end

end LatticeFieldTight
