import LatticeWickTwo
import GreenClustering

/-!
# Individual higher correlations, at every order, and they cluster

`GreenDecay` and `GreenClustering` have carried the same admission since they were written, and
the `UNLOCK_WATCHLIST` quotes it against the OS4 item:

> *"no individual higher correlation is written down. Extracting one means differentiating under
> the integral `k` times, and the identity that would come out **IS** Wick's formula. So the
> generating functional clusters; **extraction does not follow**."*

`LatticeFourPointClustering` answered that at **order four**, in the pattern `(f,f,g,g)`, by
composing `GreenClustering.cross_abs_le` with the smeared Isserlis identity. The two units of
16 August supply the identity at **every** order, so the same composition now runs at every order.

## What is proved, and why the first statement is stronger than a clustering estimate

* `moment_nonneg`, `linVar_nonneg`, `wickCoeff_nonneg` — the moments of a smeared field are
  nonnegative, which is what lets the bounds below be stated against `∫⟪f,ω⟫^n` itself rather than
  against its absolute value;
* **`odd_pattern_abs_le`** — for `a` supported `N` steps from `f`,

  ```
  |∫ ⟪a,ω⟫·⟪f,ω⟫^(n+1)| ≤ (n+1)·‖a‖₁‖f‖₁·r^N/m² · ∫ ⟪f,ω⟫^n
  ```

  **This is the whole correlation, not its connected part.** At order four
  `LatticeFourPointClustering` had to subtract a product of two-point functions before anything
  decayed, because `∫⟪f,ω⟫²⟪g,ω⟫²` tends to `∫⟪f,ω⟫²·∫⟪g,ω⟫²` rather than to zero. In this
  pattern there is nothing to subtract: `wick_recursion` says the correlation **is** a propagator
  times a moment, and the propagator is the thing `cross_abs_le` bounds;
* **`odd_pattern_eq_zero_of_not_reachable`** — and across components it is **exactly zero** at
  every order, with no estimate in the way;
* `exists_odd_pattern_clustering_uniform` — the same with a tolerance instead of a rate, `N`
  produced from the degree bound, the mass, an `ℓ¹` bound and `ε` **before the vertex type, the
  graph or the test functions are mentioned**, which is the shape of
  `GreenClustering.exists_clustering_uniform`, kept so the two read side by side;
* **`connected_two_abs_le`** — the even pattern needs its disconnected part removed, and what is
  left decays at **twice** the exponent:

  ```
  |∫ ⟪a,ω⟫⟪b,ω⟫⟪f,ω⟫^(n+2) − ⟨b,Ga⟩·∫⟪f,ω⟫^(n+2)|
      ≤ (n+2)(n+1)·(‖a‖₁‖f‖₁ r^N/m²)·(‖b‖₁‖f‖₁ r^N/m²)·∫⟪f,ω⟫^n
  ```

  because `wick_two`'s second term carries **two** propagators from `f`, one to `a` and one to `b`.
  `LatticeFourPointClustering.connected_smeared_le`'s doubled exponent is the same phenomenon at
  `n = 0`;
* `connected_two_eq_zero_of_not_reachable` — exactly zero across components, again with no estimate.

## What this is NOT

**It is not OS4.** OS4's two remaining pieces are the infinite-volume limit and the continuum, and
every statement here is at a fixed finite graph. What the uniform version supplies is that the rate
does not degrade as the graph grows — the hypothesis such an argument needs, not the argument.

**And the patterns are still `(a, f^(n+1))` and `(a, b, f^(n+2))`**, not `2n` arbitrary test
functions, for the reason `LatticeWickTwo` records: the obstruction is the number of **distinct**
test functions, which stands at three. **No published tag moves.**

**⚠ SUPERSEDED IN ITS REASON, 2026-08-27, and kept as written (`ERRATUM 94`).** *"The obstruction
is the number of **distinct** test functions, which stands at three"* is false:
`IsserlisAll.isserlisGeneral_all` proves `WickPairings.IsserlisGeneral G m k` at every `k`, so the
identity is available at any number of distinct test functions. **What is NOT superseded is the
first clause**: the patterns proved *in this file* are still `(a, f^(n+1))` and `(a, b, f^(n+2))`,
because lifting them needs the pairing sum split along the near/far boundary, and only the first
half of that split exists — `PairingSplit.sum_prod_eq_sum_respects` collapses the sum onto the
matchings that do not cross when the crossing propagator vanishes. **The factorisation and the
estimate are not written**, and no number is offered for them (`ERRATUM 194`).
-/

namespace LatticeHigherClustering

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian GreenDecay
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared
open LatticeMomentsGeneral LatticeWickRecursion LatticeWickTwo

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The moments are nonnegative -/

theorem wickCoeff_nonneg (k : ℕ) : 0 ≤ wickCoeff k := by
  rw [wickCoeff]
  split
  · positivity
  · exact le_rfl

/-- `fᵀGf` is a second moment, hence nonnegative. `moment_two_of_general` is the identification and
`integral_nonneg` is the rest. -/
theorem linVar_nonneg (hm : m ≠ 0) (f : EuclideanSpace ℝ V) : 0 ≤ linVar G m f := by
  rw [← moment_two_of_general (G := G) hm f]
  exact integral_nonneg fun ω => sq_nonneg _

/-- Hence **every** moment is nonnegative — the odd ones because they vanish. -/
theorem moment_nonneg (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (k : ℕ) :
    0 ≤ ∫ ω, (inner ℝ f ω : ℝ) ^ k ∂(gaussianField G m) := by
  rw [moment_eq_wickCoeff hm f k]
  exact mul_nonneg (wickCoeff_nonneg k) (pow_nonneg (linVar_nonneg hm f) _)

/-! ## 2. The odd pattern, where the whole correlation decays -/

/-- **THE WHOLE CORRELATION DECAYS, AT EVERY ORDER.** `wick_recursion` says
`∫⟪a,ω⟫⟪f,ω⟫^(n+1)` **is** `(n+1)` times a propagator times a moment; `GreenClustering.cross_abs_le`
bounds the propagator. There is no disconnected part to subtract, because there is nothing for the
correlation to tend to but zero. -/
theorem odd_pattern_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (a f : EuclideanSpace ℝ V) (n : ℕ)
    (hsep : ∀ p q, f p ≠ 0 → a q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂(gaussianField G m)|
      ≤ ((n : ℝ) + 1) * ((∑ p, |f p|) * (∑ q, |a q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
        * ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField G m) := by
  rw [wick_recursion hm f a n]
  have hcb : |dotG G m f a|
      ≤ (∑ p, |f p|) * (∑ q, |a q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) :=
    GreenClustering.cross_abs_le hm hΔ (WithLp.ofLp f) (WithLp.ofLp a) hsep
  have hmom := moment_nonneg (G := G) hm f n
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hn1, abs_of_nonneg hmom]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcb hn1) hmom

/-- **AND ACROSS COMPONENTS IT IS EXACTLY ZERO**, at every order. Nothing is estimated: the
propagator between the two supports vanishes identically and `wick_recursion` multiplies by it. -/
theorem odd_pattern_eq_zero_of_not_reachable (hm : m ≠ 0) (a f : EuclideanSpace ℝ V) (n : ℕ)
    (hsep : ∀ p q, f p ≠ 0 → a q ≠ 0 → ¬ G.Reachable p q) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂(gaussianField G m) = 0 := by
  have hz : dotG G m f a = 0 :=
    GreenClustering.cross_eq_zero_of_not_reachable hm (WithLp.ofLp f) (WithLp.ofLp a) hsep
  rw [wick_recursion hm f a n, hz]
  ring

/-- **CLUSTERING WITH A TOLERANCE INSTEAD OF A RATE**, at every order at once. `N` comes from `Δ`,
`m`, the `ℓ¹` bound `C`, the order `n` and `ε`, before the vertex type, the graph or the test
functions are named. The bound on the surviving moment has to be supplied — it is a number about
`f` alone, not about the separation — and `D` is where it enters. -/
theorem exists_odd_pattern_clustering_uniform (hm : m ≠ 0) (Δ : ℕ) (C D : ℝ) (n : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ a f : EuclideanSpace ℝ W,
        (∑ p, |f p|) ≤ C → (∑ q, |a q|) ≤ C →
        (∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField H m)) ≤ D →
        (∀ p q, f p ≠ 0 → a q ≠ 0 → ¬ H.Reachable p q ∨ N ≤ H.dist p q) →
          |∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ (n + 1) ∂(gaussianField H m)| ≤ ε := by
  -- the tolerance the three constants leave for the propagator, kept positive by the `+ 1`s
  set δ : ℝ := ε / (((n : ℝ) + 1) * (C ^ 2 + 1) * (|D| + 1)) with hδdef
  have hden : (0 : ℝ) < ((n : ℝ) + 1) * (C ^ 2 + 1) * (|D| + 1) := by positivity
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨N, hN⟩ := GreenDecay.exists_pow_lt hm Δ hδ
  refine ⟨N, fun W _ _ H _ hdeg a f hfC haC hD hsep => ?_⟩
  have hfn : (0 : ℝ) ≤ ∑ p, |f p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  have han : (0 : ℝ) ≤ ∑ q, |a q| := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hC0 : 0 ≤ C := le_trans hfn hfC
  have hmom := moment_nonneg (G := H) hm f n
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hrate : decayRate Δ m ^ N * (m ^ 2)⁻¹ < δ := hN N le_rfl
  have hrate0 : 0 ≤ decayRate Δ m ^ N * (m ^ 2)⁻¹ := by
    have := decayRate_nonneg Δ (m := m) hm
    positivity
  have hprod : (∑ p, |f p|) * (∑ q, |a q|) ≤ C ^ 2 + 1 := by nlinarith
  have hDD : (∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField H m)) ≤ |D| + 1 :=
    le_trans hD (by linarith [le_abs_self D])
  refine le_trans (odd_pattern_abs_le hm hdeg a f n hsep) ?_
  have hstep : ((n : ℝ) + 1) * ((∑ p, |f p|) * (∑ q, |a q|)
        * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
      * ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField H m)
      ≤ ((n : ℝ) + 1) * ((C ^ 2 + 1) * δ) * (|D| + 1) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left ?_ hn1) hDD hmom (by positivity)
    exact mul_le_mul hprod hrate.le hrate0 (by positivity)
  refine hstep.trans ?_
  rw [hδdef]
  field_simp
  exact le_rfl

/-! ## 3. The even pattern, where the disconnected part has to go first -/

/-- **TWO PROPAGATORS, HENCE TWICE THE EXPONENT.** `wick_two` splits the correlation into a
disconnected term `⟨b,Ga⟩·∫⟪f,ω⟫^(n+2)`, which does not decay when `a` and `b` sit together, and a
term carrying propagators from `f` to **both** `a` and `b`. Subtract the first and the second is
bounded by a product of two separately-decaying factors. -/
theorem connected_two_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (a b f : EuclideanSpace ℝ V) (n : ℕ)
    (hsa : ∀ p q, f p ≠ 0 → a q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q)
    (hsb : ∀ p q, f p ≠ 0 → b q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |(∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
          * (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m))
        - dotG G m b a * ∫ ω, (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m)|
      ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1)
          * (((∑ p, |f p|) * (∑ q, |a q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
            * ((∑ p, |f p|) * (∑ q, |b q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹)))
        * ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField G m) := by
  have hsplit : (∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m))
      - dotG G m b a * ∫ ω, (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m)
      = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (dotG G m f a * dotG G m f b)
          * ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField G m) := by
    rw [wick_two hm a b f n]; ring
  rw [hsplit]
  have hca : |dotG G m f a|
      ≤ (∑ p, |f p|) * (∑ q, |a q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) :=
    GreenClustering.cross_abs_le hm hΔ (WithLp.ofLp f) (WithLp.ofLp a) hsa
  have hcb : |dotG G m f b|
      ≤ (∑ p, |f p|) * (∑ q, |b q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹) :=
    GreenClustering.cross_abs_le hm hΔ (WithLp.ofLp f) (WithLp.ofLp b) hsb
  have hmom := moment_nonneg (G := G) hm f n
  have hn2 : (0 : ℝ) ≤ ((n : ℝ) + 2) * ((n : ℝ) + 1) := by positivity
  have hpair : |dotG G m f a * dotG G m f b|
      ≤ ((∑ p, |f p|) * (∑ q, |a q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
        * ((∑ p, |f p|) * (∑ q, |b q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹)) := by
    rw [abs_mul]
    exact mul_le_mul hca hcb (abs_nonneg _) (le_trans (abs_nonneg _) hca)
  rw [abs_mul, abs_mul, abs_of_nonneg hn2, abs_of_nonneg hmom]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpair hn2) hmom

/-- **AND EXACTLY ZERO ACROSS COMPONENTS**, once the disconnected term is removed. -/
theorem connected_two_eq_zero_of_not_reachable (hm : m ≠ 0) (a b f : EuclideanSpace ℝ V) (n : ℕ)
    (hsa : ∀ p q, f p ≠ 0 → a q ≠ 0 → ¬ G.Reachable p q) :
    (∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m))
      - dotG G m b a * ∫ ω, (inner ℝ f ω : ℝ) ^ (n + 2) ∂(gaussianField G m) = 0 := by
  have hz : dotG G m f a = 0 :=
    GreenClustering.cross_eq_zero_of_not_reachable hm (WithLp.ofLp f) (WithLp.ofLp a) hsa
  rw [wick_two hm a b f n, hz]
  ring

/-- Order six, spelled out: with `a` far from `f`, the six-point function in the pattern
`(a, f, f, f, f, f)` is bounded by `5·‖a‖₁‖f‖₁·r^N/m²·3(fᵀGf)²`. This is the case the
`GreenClustering` item asked for and could not have. -/
theorem six_point_abs_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) {N : ℕ}
    (a f : EuclideanSpace ℝ V)
    (hsep : ∀ p q, f p ≠ 0 → a q ≠ 0 → ¬ G.Reachable p q ∨ N ≤ G.dist p q) :
    |∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ f ω : ℝ) ^ 5 ∂(gaussianField G m)|
      ≤ 5 * ((∑ p, |f p|) * (∑ q, |a q|) * (decayRate Δ m ^ N * (m ^ 2)⁻¹))
        * (3 * (linVar G m f) ^ 2) := by
  have h := odd_pattern_abs_le (G := G) hm hΔ a f 4 hsep
  rw [moment_four_of_recursion hm f] at h
  norm_num at h
  exact h

end LatticeHigherClustering
