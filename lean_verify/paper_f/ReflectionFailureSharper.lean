import ReflectionFailureCriterion
import GreenLargeMass

/-!
# The same criterion `GreenLargeMass` §8 already had, with a weaker hypothesis — and the erratum

**READ THIS FIRST.** `paper_f/ReflectionRemainderGeneral.lean` and
`paper_f/ReflectionFailureCriterion.lean` were written believing they were new.
**`GreenLargeMass.lean` §General had done the same job**: `green_mirror_general`,
`Dinv_adj_Dinv_apply`, the exact split of the reflected form at an arbitrary graph, and
**`not_reflectionPositive_of_crossForm_pos_general`** — a cross form beating
`(m²)⁻³ · Δ² · (∑_{p ∈ H} |u p · (deg p + m²)|)²` refutes reflection positivity, on any graph with a
degree bound. That is `ERRATUM 427`, and the two headers carry it.

**THIS FILE IS THE FOLD-BACK, AND IT FOLDS BACK BY PROVING MORE.** The two thresholds differ in one
place and the difference is decidable: writing `c p = u p · (deg p + m²)` for the reweighted
witness, §8 asks that `Δ²/(m²)³ · (∑_{p ∈ H} |c p|)²` be beaten, and
`ReflectionFailureCriterion.reflectedForm_neg_of_crossForm_gt` asks that `Δ²/(m²)³ · (c ⬝ᵥ c)` be.
**`dotProduct_le_sq_sum_abs`: `c ⬝ᵥ c ≤ (∑_{p ∈ H} |c p|)²` always**, since a square of a sum of
non-negatives dominates the sum of their squares. **So the `ℓ²` hypothesis is the weaker one and the
`ℓ²` criterion is the sharper**, and `greenLargeMass_general_of_sq` derives §8's theorem from it
rather than the reverse.

**HOW MUCH SHARPER, STATED HONESTLY.** The gap is `2 ∑_{p < q} |c p| |c q|`, so the two coincide
exactly when at most one entry of the witness is nonzero and separate as soon as two are. **No claim
is made that this reaches a graph §8 cannot**: no witness is exhibited here, and whether the extra
room is ever the difference between firing and not is **not attempted, not costed**
(`ERRATUM 246`) and **not estimated** (`ERRATUM 183`).

**AND THE COMPARISON IS NOT ONE-SIDED, WHICH THE WORD *sharper* WOULD HIDE.** §3's derivation
carries `[Nonempty V]`, which §8 does not: the `ℓ²` route runs through
`PosSemidefNormBound.l2_opNorm_le`, false on an empty vertex type (`ERRATUM 426`), and §8's
entrywise route needs no such thing. **So the `ℓ²` criterion has the weaker threshold and the
stronger instance hypothesis**, and neither theorem dominates the other outright. On any graph with
a vertex — every graph this estate is about — the threshold is what decides, and there the `ℓ²` one
is weaker.

**AND §8 IS NOT SUPERSEDED.** It is stated in the `ℓ¹` mass, which is the quantity
`GreenLargeMass`'s own §9 witnesses are computed in (`us_weighted_sum`, `wpos_weighted_sum`), so a
caller holding one of those numbers should use §8 and not convert. `ERRATUM 94`, `ERRATUM 176`:
kept, cited, not deleted.

**W1 DOES NOT MOVE**, for the reason its fifth amendment already gives: this is a sufficient
condition for reflection positivity to FAIL, and the wall wants the opposite implication.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ReflectionFailureSharper

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection GreenExpansion
open ReflectionRemainderGeneral ReflectionFailureCriterion

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The `ℓ²` mass is below the squared `ℓ¹` mass -/

omit [DecidableEq V] in
/-- **`c ⬝ᵥ c ≤ (∑_{p ∈ H} |c p|)²` FOR A WITNESS SUPPORTED ON THE HALF.** The sum of squares is
below the square of the sum, for non-negatives; the support hypothesis moves the left side onto `H`.
The gap is `2 ∑_{p < q} |c p| |c q|`, so the two agree exactly when at most one entry is nonzero. -/
theorem dotProduct_le_sq_sum_abs {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    c ⬝ᵥ c ≤ (∑ p ∈ H, |c p|) ^ 2 := by
  classical
  have hsq : c ⬝ᵥ c = ∑ p ∈ H, |c p| ^ 2 := by
    rw [dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ H) fun p _ hp => by rw [hc p hp]; ring]
    exact Finset.sum_congr rfl fun p _ => by rw [sq_abs]; ring
  rw [hsq]
  exact Finset.sum_sq_le_sq_sum_of_nonneg fun p _ => abs_nonneg _

/-! ## 2. The `ℓ²` criterion as a failure of the estate's predicate -/

/-- **`ReflectionFailureCriterion.reflectedForm_neg_of_crossForm_gt` AS A REFUTATION**, in the shape
`GreenLargeMass` §8 states its conclusion. -/
theorem not_reflectionPositive_of_crossForm_gt [Nonempty V] (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0)
    (hgt : Δ ^ 2 / (m ^ 2) ^ 3 * (c ⬝ᵥ c) < crossForm G m θ H (fun v => c v * invDeg G m v)) :
    ¬ ReflectionPositive G m θ H := by
  intro hRP
  exact absurd (hRP c hc) (not_le.mpr (reflectedForm_neg_of_crossForm_gt hM h hΔ hm hc hgt))

/-! ## 3. It subsumes `GreenLargeMass` §8, proved and not asserted -/

/-- **§8's THEOREM, DERIVED FROM THE `ℓ²` ONE.** Its hypothesis is the stronger of the two by §1, so
the implication runs this way and not the other. The reweighting `c p = u p · (deg p + m²)` is §8's
own, and `c v * invDeg G m v = u v` because the weight is nonzero. -/
theorem greenLargeMass_general_of_sq [Nonempty V] (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {u : V → ℝ}
    (hus : ∀ p, p ∉ H → u p = 0)
    (hbig : ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2
              * (∑ p ∈ H, |u p * ((G.degree p : ℝ) + m ^ 2)|) ^ 2 < crossForm G m θ H u) :
    ¬ ReflectionPositive G m θ H := by
  classical
  set c : V → ℝ := fun p => u p * ((G.degree p : ℝ) + m ^ 2) with hcdef
  have hc : ∀ p, p ∉ H → c p = 0 := fun p hp => by rw [hcdef]; simp [hus p hp]
  have hΔR : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by exact_mod_cast hΔ p
  have hcw : (fun v => c v * invDeg G m v) = u := by
    funext v
    rw [hcdef, invDeg, mul_assoc, mul_inv_cancel₀ (ne_of_gt (weight_pos hm v)), mul_one]
  have hcoef : Δ ^ 2 / (m ^ 2) ^ 3 = ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 := by
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  have hnn : (0 : ℝ) ≤ ((m ^ 2)⁻¹) ^ 3 * (Δ : ℝ) ^ 2 := by positivity
  refine not_reflectionPositive_of_crossForm_gt hM h hΔR hm hc ?_
  rw [hcw, hcoef]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (dotProduct_le_sq_sum_abs (H := H) hc) hnn) hbig

end ReflectionFailureSharper
