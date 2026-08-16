import LatticeIsserlisSmeared
import GreenClustering

/-!
# The connected four-point function clusters, in the test-function vocabulary

`GreenClustering` proved exponential clustering of the **generating functional** and said in its
own summary, quoted by the `UNLOCK_WATCHLIST` item:

> *"no individual higher correlation is written down. Extracting one means differentiating under
> the integral `k` times, and the identity that would come out **IS** Wick's formula. So the
> generating functional clusters; **extraction does not follow**."*

The extraction now exists — `LatticeIsserlisSmeared.connected_smeared` — and it is in the same
vocabulary `GreenClustering` uses, test functions rather than sites. **So the two compose**, and
what comes out is exponential clustering of an individual higher correlation rather than of a
generating functional.

## What is proved

* **`connected_smeared_le`** — for test functions whose supports are `N` steps apart (or in
  different components), the connected four-point function is at most
  `2·(‖f‖₁‖g‖₁·r^N/m²)²` with `r = decayRate Δ m < 1`. **Geometric in `N`, at twice the exponent**,
  since it is the square of a quantity `GreenClustering.cross_abs_le` already bounds;
* **`connected_smeared_eq_zero_of_not_reachable`** — and across components it is **exactly zero**,
  not small. `GreenClustering.cross_eq_zero_of_not_reachable` gives that with no estimate in the
  way, and `connected_smeared_eq_zero_iff` turns it into an equality rather than a bound;
* **`exists_four_point_clustering_uniform`** — clustering with a tolerance instead of a rate: `N`
  is produced from the degree bound, the mass, an `ℓ¹` bound on the test functions and `ε`,
  **before the vertex type, the graph or the test functions are mentioned**. This is
  `GreenClustering.exists_clustering_uniform`'s shape, kept so the two can be read side by side.

## What this is NOT

**It is not OS4**, for the reason the watchlist has recorded throughout: OS4's two remaining pieces
are the infinite-volume limit and the continuum, and every statement here is at a fixed finite
graph. What the uniform version supplies is that the rate does not degrade as the graph grows —
the hypothesis such an argument needs, not the argument.

**And it is the pattern `(f,f,g,g)`.** The four field factors come from two test functions; four
arbitrary ones are not covered by anything in this file. **No published tag moves.**

*AMENDED 16 AUGUST 2026 (`ERRATUM 181`). This paragraph used to end: "~~Four arbitrary ones need
the fifteen-term polarisation the watchlist sub-trigger names, which is still untouched~~."
**Both halves are withdrawn** — the count was wrong (two steps of two terms, one slot at a time)
and it is no longer untouched (`LatticeIsserlisFour.isserlis_four`, `4d35d08`). **What is NOT
withdrawn is the restriction on THIS file**, whose every statement is still `(f,f,g,g)`; the
clustering estimate here has not been re-derived at four arbitrary arguments.*
-/

namespace LatticeFourPointClustering

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian GreenDecay
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **THE ESTIMATE.** `GreenClustering.cross_abs_le` bounds `|fᵀGg|`; the connected four-point
function is twice its square, so the bound squares and the exponent doubles. -/
theorem connected_smeared_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (f g : EuclideanSpace ℝ V)
    (hsep : ∀ p q, f p ≠ 0 → g q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
      ≤ 2 * ((∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2 := by
  rw [connected_smeared hm f g]
  have hcb : |dotG G m f g|
      ≤ (∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) :=
    GreenClustering.cross_abs_le hm hΔ (WithLp.ofLp f) (WithLp.ofLp g) hsep
  have hsq : (dotG G m f g) ^ 2
      ≤ ((∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) ^ 2 :=
    calc (dotG G m f g) ^ 2 = |dotG G m f g| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hcb 2
  linarith

/-- **ACROSS COMPONENTS IT IS EXACTLY ZERO**, not small. Everything above degrades with `N`; here
there is nothing to estimate, because the propagator between the two supports vanishes identically
and `connected_smeared_eq_zero_iff` converts that into an equality. -/
theorem connected_smeared_eq_zero_of_not_reachable (hm : m ≠ 0) (f g : EuclideanSpace ℝ V)
    (hsep : ∀ p q, f p ≠ 0 → g q ≠ 0 → ¬ G.Reachable p q) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m)) = 0 :=
  (connected_smeared_eq_zero_iff hm f g).mpr
    (GreenClustering.cross_eq_zero_of_not_reachable hm (WithLp.ofLp f) (WithLp.ofLp g) hsep)

/-- **CLUSTERING WITH A TOLERANCE INSTEAD OF A RATE.** `N` comes from `Δ`, `m`, the `ℓ¹` bound `C`
and `ε`, before the vertex type, the graph or the test functions are named —
`GreenClustering.exists_clustering_uniform`'s shape, kept so the two read side by side.

The `√` is where the doubled exponent shows up: to make a SQUARE smaller than `ε` one asks the
thing being squared to be smaller than `√(ε/2)`, and `GreenDecay.exists_pow_lt` supplies that. -/
theorem exists_four_point_clustering_uniform (hm : m ≠ 0) (Δ : ℕ) (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ f g : EuclideanSpace ℝ W,
        (∑ p, |f p|) ≤ C → (∑ q, |g q|) ≤ C →
        (∀ p q, f p ≠ 0 → g q ≠ 0 → ¬ H.Reachable p q ∨ N ≤ H.dist p q) →
          (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField H m))
              - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField H m))
                * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField H m))
            ≤ ε := by
  -- the tolerance the SQUARE demands, kept positive at `C = 0` by the `+ 1`
  set δ : ℝ := Real.sqrt (ε / 2) / (C ^ 2 + 1) with hδdef
  have hεhalf : 0 < Real.sqrt (ε / 2) := Real.sqrt_pos.mpr (by linarith)
  have hδ : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := GreenDecay.exists_pow_lt hm Δ hδ
  refine ⟨N, fun W _ _ H _ hdeg f g hfC hgC hsep => ?_⟩
  have hC0 : 0 ≤ C := le_trans (Finset.sum_nonneg fun p _ => abs_nonneg _) hfC
  have hfn : (0 : ℝ) ≤ ∑ p, |f p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  have hgn : (0 : ℝ) ≤ ∑ q, |g q| := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hcb : |dotG H m f g| ≤ (∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) :=
    GreenClustering.cross_abs_le hm hdeg (WithLp.ofLp f) (WithLp.ofLp g) hsep
  have hrate : decayRate Δ m ^ N * (m ^ 2)⁻¹ < δ := hN N le_rfl
  have hrate0 : 0 ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by
    have := decayRate_nonneg Δ (m := m) hm
    positivity
  -- ‖f‖₁‖g‖₁ ≤ C² ≤ C² + 1, so the product is below √(ε/2)
  have hprod : (∑ p, |f p|) * (∑ q, |g q|) ≤ C ^ 2 + 1 := by nlinarith
  have hbound : |dotG H m f g| ≤ Real.sqrt (ε / 2) := by
    refine hcb.trans ?_
    calc (∑ p, |f p|) * (∑ q, |g q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹)
        ≤ (C ^ 2 + 1) * δ := by
          refine mul_le_mul hprod hrate.le hrate0 (by positivity)
      _ = Real.sqrt (ε / 2) := by
          have hne : (C ^ 2 + 1) ≠ 0 := by positivity
          rw [hδdef]
          field_simp
  have hsq : (dotG H m f g) ^ 2 ≤ ε / 2 := by
    have h1 : |dotG H m f g| ^ 2 ≤ Real.sqrt (ε / 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hbound 2
    rwa [Real.sq_sqrt (by linarith : (0:ℝ) ≤ ε / 2), sq_abs] at h1
  rw [connected_smeared hm f g]
  linarith

end LatticeFourPointClustering
