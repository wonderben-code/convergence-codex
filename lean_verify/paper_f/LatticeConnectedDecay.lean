import LatticeIsserlis
import GreenDecay
import TorusDecay

/-!
# The connected four-point function clusters, at twice the rate

`LatticeIsserlis` (`32e9766`) proved `∫(ω p)²(ω q)² − (∫(ω p)²)(∫(ω q)²) = 2·G(p,q)²` and then said
of the obvious next step:

> *"Composing it with `GreenDecay.covariance_abs_le` would give exponential decay of the connected
> four-point function — that composition is **not written here** … it is one import and one `calc`
> away, and being one step away is not the same as being done."*

**This writes it.** One import and, as advertised, very little else.

## What is proved

* **`connected_eq_two_mul_sq_twoPoint`** — the connected four-point function is **twice the square
  of the two-point function**, with no Green function anywhere in the statement:
  `∫(ω p)²(ω q)² − (∫(ω p)²)(∫(ω q)²) = 2·(∫ ω p · ω q)²`. This is the basis-free form of
  `LatticeIsserlis.connected_four_point` and it is the one a clustering argument reads;
* **`connected_le`** — hence it is at most `2·(r^{d(p,q)}/m²)²` where `r = decayRate Δ m < 1`. So it
  decays in the graph distance at **twice the exponent** the two-point function does, which is what
  a squared propagator must do and is worth having as a theorem rather than as an expectation;
* **`exists_dist_uniform_connected`** — and the uniform form: for every `ε > 0` there is an `N`
  depending on the degree bound, the mass and `ε` **and on nothing else** — not on the graph, the
  vertex type or the two sites — beyond which the connected four-point function is below `ε`. This
  is `GreenDecay.exists_dist_uniform`'s shape, kept deliberately, so that the box and torus
  instances below are instances rather than separate theorems;
* `boxGraph_connected_le`, `torusGraph_connected_le` — on the `n^d` box and torus, where the degree
  bound is `2d` at every side length, **the rate does not depend on `n`.**

## What this is NOT

**It is not OS4.** OS4's two remaining pieces, recorded on the watchlist, are the infinite-volume
limit and the continuum. Every statement here is at a fixed finite graph. What the uniformity gives
is that the *rate* does not degrade as the box grows — which is the hypothesis an infinite-volume
argument would need, not the argument.

**And it is one index pattern.** `LatticeIsserlis` proves Isserlis at `(p,p,q,q)` only; the
connected function of four *distinct* sites is not available, so "the connected four-point function"
here means the one built from `(ω p)²(ω q)²`. The general case still needs the polarisation nobody
has done.

**No published tag moves.**
-/

namespace LatticeConnectedDecay

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian LatticeMoments LatticeIsserlis

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **THE CONNECTED FOUR-POINT FUNCTION IS TWICE THE SQUARE OF THE TWO-POINT FUNCTION.**

No Green function appears. `LatticeIsserlis.connected_four_point` says the same thing with `G(p,q)`
on the right; this says it with the estate's other vocabulary for the same object, and it is the
form a clustering argument consumes: the thing being squared is what has a decay estimate. -/
theorem connected_eq_two_mul_sq_twoPoint (hm : m ≠ 0) (p q : V) :
    (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (ω p) ^ 2 ∂(gaussianField G m)) * (∫ ω, (ω q) ^ 2 ∂(gaussianField G m))
      = 2 * (∫ ω, ω p * ω q ∂(gaussianField G m)) ^ 2 := by
  rw [connected_four_point hm p q, GraphLaplacian.twoPoint G hm p q]

/-- **AND IT DECAYS AT TWICE THE EXPONENT.** `GreenDecay.green_abs_le_pow_dist` bounds `|G(p,q)|`
by `r^{d(p,q)}/m²` with `r < 1`; squaring doubles the exponent, which is exactly what the connected
function of a free field should do. -/
theorem connected_le (hm : m ≠ 0) {Δ : ℕ} (hΔ : ∀ v : V, G.degree v ≤ Δ) (p q : V) :
    (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (ω p) ^ 2 ∂(gaussianField G m)) * (∫ ω, (ω q) ^ 2 ∂(gaussianField G m))
      ≤ 2 * (GreenDecay.decayRate Δ m ^ (G.dist p q) * (m ^ 2)⁻¹) ^ 2 := by
  rw [connected_four_point hm p q]
  have habs := GreenDecay.green_abs_le_pow_dist (G := G) hm hΔ p q
  have hsq : (green G m p q) ^ 2
      ≤ (GreenDecay.decayRate Δ m ^ (G.dist p q) * (m ^ 2)⁻¹) ^ 2 :=
    calc (green G m p q) ^ 2 = |green G m p q| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) habs 2
  linarith

/-- **UNIFORM IN EVERYTHING BUT THE DEGREE BOUND, THE MASS AND `ε`.** `N` is produced before the
graph, the vertex type or the two sites are mentioned — `GreenDecay.exists_dist_uniform`'s shape,
kept so that the families below are instances.

The separation hypothesis is `¬ Reachable ∨ N ≤ dist` for the reason `GreenDecay` records:
`SimpleGraph.dist` is `0` across components, so the second disjunct alone would exclude exactly the
pairs where the conclusion is sharpest. -/
theorem exists_dist_uniform_connected (hm : m ≠ 0) (Δ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      (∀ v : W, H.degree v ≤ Δ) → ∀ p q : W,
        (¬ H.Reachable p q ∨ N ≤ H.dist p q) →
          (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField H m))
              - (∫ ω, (ω p) ^ 2 ∂(gaussianField H m)) * (∫ ω, (ω q) ^ 2 ∂(gaussianField H m))
            < ε := by
  have hhalf : 0 < Real.sqrt (ε / 2) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨N, hN⟩ := GreenDecay.exists_dist_uniform (m := m) hm Δ hhalf
  refine ⟨N, fun W _ _ H _ hdeg p q hsep => ?_⟩
  have hg := hN W H hdeg p q hsep
  rw [LatticeIsserlis.connected_four_point (G := H) hm p q]
  have hsq : (green H m p q) ^ 2 < ε / 2 := by
    have h1 : |green H m p q| ^ 2 < Real.sqrt (ε / 2) ^ 2 :=
      pow_lt_pow_left₀ hg (abs_nonneg _) (by norm_num)
    rw [Real.sq_sqrt (by linarith : (0:ℝ) ≤ ε / 2)] at h1
    rwa [sq_abs] at h1
  linarith

/-! ## The two families, as instances -/

open BoxGraph in
/-- **ON THE `n^d` BOX THE RATE DOES NOT DEPEND ON `n`.** -/
theorem boxGraph_connected_le (d n : ℕ) (hm : m ≠ 0) (p q : Site d n) :
    (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField (boxGraph d n) m))
        - (∫ ω, (ω p) ^ 2 ∂(gaussianField (boxGraph d n) m))
          * (∫ ω, (ω q) ^ 2 ∂(gaussianField (boxGraph d n) m))
      ≤ 2 * (GreenDecay.decayRate (2 * d) m ^ ((boxGraph d n).dist p q) * (m ^ 2)⁻¹) ^ 2 :=
  connected_le hm (fun v => BoxDegree.boxGraph_degree_le v) p q

open TorusReflection BoxGraph in
/-- **AND ON THE TORUS**, which is the family an infinite-volume limit would run along. -/
theorem torusGraph_connected_le (d n : ℕ) (hm : m ≠ 0) (p q : Site d n) :
    (∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField (torusGraph d n) m))
        - (∫ ω, (ω p) ^ 2 ∂(gaussianField (torusGraph d n) m))
          * (∫ ω, (ω q) ^ 2 ∂(gaussianField (torusGraph d n) m))
      ≤ 2 * (GreenDecay.decayRate (2 * d) m ^ ((torusGraph d n).dist p q) * (m ^ 2)⁻¹) ^ 2 :=
  connected_le hm (fun v => TorusDecay.torusGraph_degree_le v) p q

end LatticeConnectedDecay
