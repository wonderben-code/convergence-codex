import NeumannTailBound

/-!
# The remainder of `GreenExpansion.reflectionPositive_iff_remainder`, bounded in the form it is used

`WALLS.md`'s W1 states its failing step as a theorem rather than a remark:
`GreenExpansion.reflectionPositive_iff_remainder` says reflection positivity at `c` holds
**exactly** when

  `crossForm G m θ H c ≤ ∑ p ∈ H, ∑ q ∈ H, c p * c q * (green G m * A * A) (θ p) q`,

so the wall's *"a bound making the remainder smaller than the cross form's negative direction"* is
about that double sum. `NeumannTailBound` bounded the remainder **as a matrix**. A matrix norm is
not yet a bound on a quadratic form indexed through a reflection `θ` and restricted to a half `H`.
This file is that conversion.

**WHAT IS PROVED.** `abs_remainder_le`: for any real matrix `M`, any `θ : V ≃ V` and any `c`,

  `|∑ p, ∑ q, c p * c q * M (θ p) q| ≤ ‖M‖ * (c ⬝ᵥ c)`,

by Cauchy–Schwarz on the inner sum, the reflection being a bijection so that it does not move the
squared length, and `dotProduct_mulVec_sq_le` for the matrix step. `abs_remainder_green_adj_adj_le`
is it at `M = green G m * A * A` with `‖M‖ ≤ Δ² / m²`, and `abs_remainder_le_of_mem_half` restricts
the sums to `H` for a `c` vanishing off `H`, **which is the exact shape the `iff` consumes.**

**WHAT IT IS NOT — AND W1 STILL DOES NOT MOVE, FOR THE SAME REASON AS THIS MORNING.** The wall needs
the remainder to be smaller than **the cross form's negative direction**. This file bounds the
remainder above by `(Δ² / m²) · ‖c‖²`; it says **nothing whatever about the cross form**, whose
magnitude nothing in this estate estimates. **An upper bound on one side of a comparison is not the
comparison**, and what is now missing is a LOWER bound on the other side — a different object, not
attempted here, not costed (`ERRATUM 246`) and not estimated (`ERRATUM 183`).

**And the direction of the inequality matters more than its size.**
`reflectionPositive_iff_remainder` needs the remainder to DOMINATE the cross form; a bound on
`|remainder|` bounds how much help the remainder can give, so it is the ingredient of a
**negative** argument — showing the remainder cannot rescue a violated `hcross` — rather than of
the positive one. **That asymmetry is stated here
because a bound in hand invites reading it the useful way round, and it does not go that way.**

**Nothing here is sharp.** Cauchy–Schwarz is tight only at proportional vectors, `‖A‖ ≤ Δ` is the
standard degree bound, and the restriction to `H` throws away that `c` is supported there.
**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace RemainderFormBound

open Matrix GraphLaplacian
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The operator norm as a bound on `‖M x‖²` in `dotProduct` form -/

/-- **`‖M c‖² ≤ ‖M‖² ‖c‖²`, WRITTEN IN `dotProduct`**, which is the form the double sums below are
in. `Matrix.l2_opNorm_toEuclideanCLM` and `ContinuousLinearMap.le_opNorm` do the work;
`PosSemidefNormBound.norm_sq_eq_dotProduct` moves both sides out of `EuclideanSpace`. -/
theorem dotProduct_mulVec_sq_le (M : Matrix V V ℝ) (c : V → ℝ) :
    (M *ᵥ c) ⬝ᵥ (M *ᵥ c) ≤ ‖M‖ ^ 2 * (c ⬝ᵥ c) := by
  set x : EuclideanSpace ℝ V := WithLp.toLp 2 c with hx
  have hofLp : x.ofLp = c := rfl
  have hle : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) x‖ ≤ ‖M‖ * ‖x‖ := by
    have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) M).le_opNorm x
    rwa [Matrix.l2_opNorm_toEuclideanCLM] at h
  have h1 : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M) x‖ ^ 2 = (M *ᵥ c) ⬝ᵥ (M *ᵥ c) := by
    rw [PosSemidefNormBound.norm_sq_eq_dotProduct, Matrix.ofLp_toEuclideanCLM, hofLp]
  have h2 : ‖x‖ ^ 2 = c ⬝ᵥ c := by
    rw [PosSemidefNormBound.norm_sq_eq_dotProduct, hofLp]
  nlinarith [hle, h1, h2, norm_nonneg ((Matrix.toEuclideanCLM (𝕜 := ℝ) M) x), norm_nonneg x,
    norm_nonneg M]

/-! ## 2. The double sum -/

/-- **THE REMAINDER'S QUADRATIC FORM, BOUNDED BY THE MATRIX NORM.** The reflection `θ` is a
bijection, so re-indexing by it does not change a sum of squares; Cauchy–Schwarz then reduces the
double sum to §1. **No hypothesis on `M` and none on `θ` beyond being an equivalence.** -/
theorem abs_remainder_le (M : Matrix V V ℝ) (θ : V ≃ V) (c : V → ℝ) :
    |∑ p, ∑ q, c p * c q * M (θ p) q| ≤ ‖M‖ * (c ⬝ᵥ c) := by
  have hsum : ∑ p, ∑ q, c p * c q * M (θ p) q = ∑ p, c p * ((M *ᵥ c) (θ p)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun p => (M *ᵥ c) (θ p))
  have hre : ∑ p, ((M *ᵥ c) (θ p)) ^ 2 = (M *ᵥ c) ⬝ᵥ (M *ᵥ c) := by
    rw [Equiv.sum_comp θ (fun v => ((M *ᵥ c) v) ^ 2), dotProduct]
    exact Finset.sum_congr rfl fun v _ => (pow_two _)
  have hcc : ∑ p, (c p) ^ 2 = c ⬝ᵥ c := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun v _ => (pow_two _)
  have hMc := dotProduct_mulVec_sq_le M c
  have hccnn : 0 ≤ c ⬝ᵥ c := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
  have hsq : (∑ p, c p * ((M *ᵥ c) (θ p))) ^ 2 ≤ (‖M‖ * (c ⬝ᵥ c)) ^ 2 := by
    rw [hcc, hre] at hcs
    nlinarith [hcs, hMc, hccnn, norm_nonneg M]
  rw [hsum]
  have hnn : 0 ≤ ‖M‖ * (c ⬝ᵥ c) := mul_nonneg (norm_nonneg M) hccnn
  exact abs_le.mpr (abs_le_of_sq_le_sq' hsq hnn)

/-! ## 3. At the estate's remainder, and on a half -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `‖green G m * A * A‖ ≤ Δ² / m²`, by submultiplicativity over
`LaplacianOpNorm.norm_green_le` and `SymmetricOpNorm.norm_adjMatrix_le`. -/
theorem norm_green_adj_adj_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ}
    (hm : m ≠ 0) : ‖green G m * G.adjMatrix ℝ * G.adjMatrix ℝ‖ ≤ Δ ^ 2 / m ^ 2 := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hΔ0 : 0 ≤ Δ := le_trans (Nat.cast_nonneg _) (hΔ (Classical.arbitrary V))
  have hG := LaplacianOpNorm.norm_green_le G hm
  have hA := SymmetricOpNorm.norm_adjMatrix_le G hΔ
  have hstep : ‖green G m * G.adjMatrix ℝ * G.adjMatrix ℝ‖ ≤ ((m ^ 2)⁻¹ * Δ) * Δ := by
    refine le_trans (Matrix.l2_opNorm_mul _ _) ?_
    refine mul_le_mul ?_ hA (norm_nonneg _) (by positivity)
    exact le_trans (Matrix.l2_opNorm_mul _ _) (mul_le_mul hG hA (norm_nonneg _) (by positivity))
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-- **THE BOUND IN THE SHAPE `reflectionPositive_iff_remainder` CONSUMES.** For a `c` vanishing off
the half `H`, the double sum over `H × H` that the `iff` compares against `crossForm` is at most
`(Δ² / m²) · (c ⬝ᵥ c)` in absolute value. **It bounds one side of that comparison and says nothing
about the other.** -/
theorem abs_remainder_le_of_mem_half [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ)
    {m : ℝ} (hm : m ≠ 0) (θ : V ≃ V) {H : Finset V} {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0) :
    |∑ p ∈ H, ∑ q ∈ H,
        c p * c q * (green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q|
      ≤ Δ ^ 2 / m ^ 2 * (c ⬝ᵥ c) := by
  set M := green G m * G.adjMatrix ℝ * G.adjMatrix ℝ with hM
  have hinner : ∀ p, ∑ q ∈ H, c p * c q * M (θ p) q = ∑ q, c p * c q * M (θ p) q := by
    intro p
    refine Finset.sum_subset (Finset.subset_univ H) fun q _ hq => ?_
    rw [hc q hq]
    ring
  have houter : ∑ p ∈ H, ∑ q ∈ H, c p * c q * M (θ p) q = ∑ p, ∑ q, c p * c q * M (θ p) q := by
    rw [Finset.sum_congr rfl fun p _ => hinner p]
    refine Finset.sum_subset (Finset.subset_univ H) fun p _ hp => ?_
    rw [Finset.sum_eq_zero]
    intro q _
    rw [hc p hp]
    ring
  rw [houter]
  refine le_trans (abs_remainder_le M θ c) ?_
  have hccnn : 0 ≤ c ⬝ᵥ c := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
  exact mul_le_mul_of_nonneg_right (norm_green_adj_adj_le G hΔ hm) hccnn

end RemainderFormBound
