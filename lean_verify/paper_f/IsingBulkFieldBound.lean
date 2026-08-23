/-
  IsingBulkFieldBound.lean — `MagnetisationBound`'s own inequality, PROVED, for the box in a BULK
  field, with the explicit constant `tanh (β·h)`.

  WHY THIS AND WHY NOW. `IsingBoundaryRouteCeiling` showed that the bond-free comparison cannot
  reach `MagnetisationBound` for the estate's boundary-field box, because the field lives on `O(n)`
  sites and the target grows like `O(n²)`. That is a statement about a deficit, and a deficit is
  best displayed against the case where it does not occur. **Put the same field on EVERY site and
  the same machinery proves the same inequality outright**, with a constant that does not depend on
  the box. So the pair of files says precisely where the difficulty lives: **not in the model, not
  in the inequality, and not in the constant — in the fact that a boundary is smaller than an
  area.**

  **THIS IS NOT `IsingBoundaryField.MagnetisationBound` AND MUST NOT BE RECORDED AS IT.** That `def`
  is stated against `isingHB`, whose field term is `−h·∑_{p ∈ ∂} σ_p`. `MagnetisationBoundBulk`
  below is stated against `isingHBulk`, whose field term is `−h·∑_{p} σ_p`. They are different
  models and the second is the easy one: a field acting everywhere magnetises everywhere, which is
  physically unsurprising and is exactly why the Peierls problem is posed with a boundary field.
  Recorded in capitals, following `FieldAutInvariance`'s precedent for the OS axioms — a
  finite-volume statement that resembles a named axiom is labelled as not that axiom.

  WHAT IS PROVED.

  * `isingHBulk`, `bulkCoup`, `energy_eq_bulk` — the same interaction presentation as
    `IsingBoxInteraction`, with the site term unconditional instead of boundary-only;
  * `tanh_le_integral_bulk` — `tanh (β·h) ≤ ⟨σ_p⟩` at **every** site, boundary or interior;
  * **`magnetisationBound_bulk`** — hence `tanh (β·h) · n² ≤ ∫ magnetisation`, which is
    `MagnetisationBound`'s inequality with `m = tanh (β·h)`, at every box, uniformly.

  WHAT IT DOES NOT DO. It does not touch the boundary-field problem, it takes no limit, and it says
  nothing about symmetry breaking: the constant `tanh (β·h)` collapses to `0` as `h → 0`, which is
  the whole reason a bulk field is not a proof of spontaneous magnetisation.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingBoxInteraction

namespace IsingBulkFieldBound

open Finset Real MeasureTheory
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction
open IsingGriffiths IsingGriffithsMono IsingIndependentSpins

noncomputable section

variable {n : ℕ}

/-! ## 1. The bulk-field Hamiltonian -/

/-- The Ising Hamiltonian of `IsingFiniteVolume` plus a field on EVERY site. `isingHB` puts the
same field on the boundary only; that one word is the entire difference between the two files. -/
def isingHBulk (n : ℕ) (h : ℝ) (σ : Config n) : ℝ :=
  isingH n σ - h * ∑ p : Site n, IsingFiniteVolume.spin (σ p)

/-- The bulk-field Gibbs measure. -/
def bulkMeasure (n : ℕ) (h β : ℝ) : Measure (Config n) :=
  FiniteGibbs.gibbs β (isingHBulk n h) Measure.count

/-! ## 2. The interaction presentation -/

/-- The couplings: `β` on a bond, `β·h` on **every** site. -/
def bulkCoup (n : ℕ) (β h : ℝ) : BoxIdx n → ℝ
  | Sum.inl (p, q) => if adj p q then β else 0
  | Sum.inr _ => β * h

theorem bulkCoup_nonneg {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    ∀ i : BoxIdx n, 0 ≤ bulkCoup n β h i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hpq : adj p q <;> simp [bulkCoup, hpq, hβ]
  · exact mul_nonneg hβ hh

/-- **`−β · isingHBulk` IS A SUM OF INTERACTION TERMS**, by the same route
`IsingBoxInteraction.energy_eq` takes, with the site term unconditional. -/
theorem energy_eq_bulk (n : ℕ) (β h : ℝ) (σ : Config n) :
    ∑ i : BoxIdx n, bulkCoup n β h i * ∏ v ∈ boxSet n i, IsingTransfer2D.spin (σ v)
      = -β * isingHBulk n h σ := by
  rw [Fintype.sum_sum_type, isingHBulk, isingH]
  have hpair : ∑ i : Site n × Site n,
      bulkCoup n β h (Sum.inl i) * ∏ v ∈ boxSet n (Sum.inl i), IsingTransfer2D.spin (σ v)
      = β * ∑ p : Site n, ∑ q : Site n,
          if adj p q then IsingTransfer2D.spin (σ p) * IsingTransfer2D.spin (σ q) else 0 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hpq : adj p q
    · rw [if_pos hpq, prod_boxSet_inl p q hpq σ]
      simp [bulkCoup, hpq]
    · rw [if_neg hpq]
      simp [bulkCoup, hpq]
  have hsite : ∑ p : Site n,
      bulkCoup n β h (Sum.inr p) * ∏ v ∈ boxSet n (Sum.inr p), IsingTransfer2D.spin (σ v)
      = β * h * ∑ p : Site n, IsingTransfer2D.spin (σ p) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxSet, Finset.prod_singleton, bulkCoup]
  rw [hpair, hsite, ← spin_eq]
  ring

/-! ## 3. The comparison field, uniform this time -/

/-- The couplings with every bond switched off — and now the field really is uniform. -/
def bulkFieldCoup (n : ℕ) (β h : ℝ) : BoxIdx n → ℝ
  | Sum.inl _ => 0
  | Sum.inr _ => β * h

theorem bulkFieldCoup_nonneg {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    ∀ i : BoxIdx n, 0 ≤ bulkFieldCoup n β h i := by
  rintro (⟨p, q⟩ | p)
  · exact le_refl 0
  · exact mul_nonneg hβ hh

theorem bulkFieldCoup_le_bulkCoup {β h : ℝ} (hβ : 0 ≤ β) :
    ∀ i : BoxIdx n, bulkFieldCoup n β h i ≤ bulkCoup n β h i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hpq : adj p q <;> simp [bulkFieldCoup, bulkCoup, hpq, hβ]
  · exact le_refl _

theorem isUniformField_bulk (n : ℕ) (β h : ℝ) :
    IsUniformField (boxSet n) (bulkFieldCoup n β h) (β * h) := by
  intro σ
  rw [Fintype.sum_sum_type]
  have hpair : ∑ i : Site n × Site n,
      bulkFieldCoup n β h (Sum.inl i)
        * ∏ v ∈ boxSet n (Sum.inl i), IsingTransfer2D.spin (σ v) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨p, q⟩ := i
    rw [bulkFieldCoup, zero_mul]
  rw [hpair, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [boxSet, Finset.prod_singleton, bulkFieldCoup]

/-! ## 4. The bound at every site -/

theorem part_eq_partition_bulk (n : ℕ) (β h : ℝ) :
    part (boxSet n) (bulkCoup n β h) = FiniteGibbsSum.partition β (isingHBulk n h) := by
  rw [part, FiniteGibbsSum.partition]
  exact Finset.sum_congr rfl fun σ _ => by rw [energy_eq_bulk n β h σ]

theorem num_eq_sum_bulk (n : ℕ) (β h : ℝ) (p₀ : Site n) :
    num (boxSet n) (bulkCoup n β h) {p₀}
      = ∑ σ : Config n, exp (-β * isingHBulk n h σ) * IsingTransfer2D.spin (σ p₀) := by
  rw [num]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_singleton, energy_eq_bulk n β h σ, mul_comm]

/-- **AT EVERY SITE — BOUNDARY OR INTERIOR — THE MAGNETISATION IS AT LEAST `tanh (β·h)`.** This is
the clause the boundary-field model cannot have: there, the interior bound is `tanh 0 = 0`. -/
theorem tanh_le_integral_bulk (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (p₀ : Site n) :
    tanh (β * h) ≤ ∫ σ, IsingTransfer2D.spin (σ p₀) ∂(bulkMeasure n h β) := by
  have hb := tanh_le_expect (boxSet n) (bulkCoup n β h) (bulkFieldCoup n β h)
    (isUniformField_bulk n β h) (bulkFieldCoup_nonneg hβ hh) (bulkFieldCoup_le_bulkCoup hβ) p₀
  rw [num_eq_sum_bulk n β h p₀, part_eq_partition_bulk n β h] at hb
  rw [bulkMeasure]
  exact FiniteGibbsSum.le_integral_gibbs_count β (isingHBulk n h) _ hb

/-! ## 5. `MagnetisationBound`'s inequality, for this model -/

/-- The bulk-field twin of `IsingBoundaryField.MagnetisationBound`, stated in the same shape so the
two can be compared, and named so they cannot be confused. -/
def MagnetisationBoundBulk (β h m : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → m * ((n : ℝ) * n) ≤ ∫ σ, magnetisation n σ ∂(bulkMeasure n h β)

theorem isProbability_bulk (n : ℕ) (h β : ℝ) :
    IsProbabilityMeasure (bulkMeasure n h β) := by
  have hC : ∀ σ : Config n,
      |isingHBulk n h σ| ≤ ((n : ℝ) * n) ^ 2 + |h| * ((n : ℝ) * n) := by
    intro σ
    rw [isingHBulk]
    refine le_trans (abs_sub _ _) ?_
    have h1 := isingH_bound n σ
    have h2 : |h * ∑ p : Site n, IsingFiniteVolume.spin (σ p)| ≤ |h| * ((n : ℝ) * n) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [Finset.sum_congr rfl fun p _ => abs_spin (σ p), Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast
      exact le_refl _
    linarith
  exact FiniteGibbs.isProbabilityMeasure_gibbs β hC Measure.count Measure.count_ne_zero''

/-- **`MagnetisationBound`'S INEQUALITY, PROVED, FOR THE BULK-FIELD BOX**, with the explicit
constant `tanh (β·h)` — the same at every box. -/
theorem magnetisationBound_bulk {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    MagnetisationBoundBulk β h (tanh (β * h)) := by
  intro n _
  haveI : IsProbabilityMeasure (bulkMeasure n h β) := isProbability_bulk n h β
  have hsplit : ∫ σ, magnetisation n σ ∂(bulkMeasure n h β)
      = ∑ p : Site n, ∫ σ, IsingTransfer2D.spin (σ p) ∂(bulkMeasure n h β) := by
    rw [show (fun σ : Config n => magnetisation n σ)
        = fun σ => ∑ p : Site n, IsingTransfer2D.spin (σ p) from rfl]
    exact integral_finset_sum _ fun p _ => Integrable.of_finite
  rw [hsplit]
  refine le_trans ?_ (Finset.sum_le_sum fun p _ => tanh_le_integral_bulk β h hβ hh p)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_comm]

end

end IsingBulkFieldBound
