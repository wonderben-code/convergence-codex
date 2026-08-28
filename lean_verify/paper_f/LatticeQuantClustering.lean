import GreenDecay
import LatticeClustering

/-!
# Quantitative clustering with no hypothesis, and the price of removing the hypothesis

`LatticeClustering` narrowed the OS item's trigger to one clause: *"an unconditional quantitative
clustering statement on a connected graph — that is, `covariance_abs_le` without the degree bound."*
The probe ran first this time, and it changes the shape of the answer.

**Half of it already exists, at the Green-function level.** `GreenDecay.green_abs_le_maxDegree` is
the decay estimate with the graph's own `SimpleGraph.maxDegree` in place of a hypothesised bound,
and its own docstring says
it *"needs no hypothesis"* — every finite graph has a maximum degree. **What does not exist is the
field-level statement**: `GreenDecay` §4 states `covariance_abs_le` and `twoPoint_abs_le` **with**
the `hΔ` hypothesis and offers no `maxDegree` form of either. That is one line, and it is written
below.

## And the hypothesis is not free to remove — this is the content

`decayRate Δ m = Δ / (Δ + m²)`. Replacing a hypothesised `Δ` by `SimpleGraph.maxDegree` buys an
unconditional
statement **at the cost of a rate that depends on the graph**, and

> **`decayRate_tendsto_one`** — `decayRate Δ m → 1` as `Δ → ∞`, at every nonzero mass.

So across a family of graphs whose degrees grow, the unconditional bound degenerates to `|cov| ≤
m⁻²`, which is `GreenLargeMass.green_diag_le` and says nothing about distance. **A bound per graph
is worth nothing to an infinite-volume argument; a bound whose rate is the same at every volume is
what `W2` would consume** — which is `GreenDecay` §5's own sentence, and `boxGraph_green_abs_le`
fixing the rate at `decayRate (2d) m` for every side length is what that section is for.

**So the trigger's clause is answered and the answer is a distinction, not a strengthening.** The
hypothesis can be dropped; the uniformity cannot, and dropping the first is exactly what loses the
second in general. On a *fixed* graph the two are the same statement; on a *family* they are not,
and it is the family that matters.

## What is proved

> **`covariance_abs_le_maxDegree`**, **`twoPoint_abs_le_maxDegree`** — the decay estimate for the
> field, in both of the estate's vocabularies, **with no hypothesis on the degrees**.
>
> **`QuantClusteringFinVol G m`** — the property, named in the style of `RegularFinVol` and
> `ClusteringFinVol`, and `gaussianField_quantClusteringFinVol` its instance.
>
> **`decayRate_tendsto_one`** — the price, as a limit rather than as a remark.

## What this is NOT

**It is not OS4**, which is a continuum, infinite-volume statement about translates. Nothing here
has an infinite volume, a translation or a limit of measures.

**It does not give uniformity**, and `decayRate_tendsto_one` is the proof that it cannot in general.
`GreenDecay.boxGraph_green_abs_le` remains the uniform statement, and it is on the box, where the
degree bound `2d` is a fact about the graph rather than an assumption.

**It says nothing about a rate being attained or sharp.** `decayRate` is an upper bound coming from
a Neumann-series count; no lower bound on correlations appears anywhere here.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeQuantClustering

open MeasureTheory ProbabilityTheory GraphLaplacian GreenDecay

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The field-level estimate, with no hypothesis -/

/-- **THE TWO-POINT FUNCTION CLUSTERS EXPONENTIALLY, WITH NOTHING ASSUMED ABOUT THE DEGREES.**
`GreenDecay.green_abs_le_maxDegree` is the same statement about the propagator; §4 of that file
states the field version only under a hypothesised bound. -/
theorem covariance_abs_le_maxDegree (hm : m ≠ 0) (p q : V) :
    |cov[fun ω : EuclideanSpace ℝ V => ω p, fun ω : EuclideanSpace ℝ V => ω q;
        gaussianField G m]|
      ≤ decayRate G.maxDegree m ^ (G.dist p q) * (m ^ 2)⁻¹ :=
  covariance_abs_le hm (fun v => G.degree_le_maxDegree v) p q

/-- The same in the integral vocabulary. -/
theorem twoPoint_abs_le_maxDegree (hm : m ≠ 0) (p q : V) :
    |∫ ω, ω p * ω q ∂(gaussianField G m)|
      ≤ decayRate G.maxDegree m ^ (G.dist p q) * (m ^ 2)⁻¹ :=
  twoPoint_abs_le hm (fun v => G.degree_le_maxDegree v) p q

/-- **QUANTITATIVE CLUSTERING IN FINITE VOLUME**, as a property with no side condition: the
correlation of two sites is at most a fixed ratio to the power of their graph distance. -/
def QuantClusteringFinVol (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) : Prop :=
  ∀ p q : V,
    |cov[fun ω : EuclideanSpace ℝ V => ω p, fun ω : EuclideanSpace ℝ V => ω q;
        gaussianField G m]|
      ≤ decayRate G.maxDegree m ^ (G.dist p q) * (m ^ 2)⁻¹

theorem gaussianField_quantClusteringFinVol (hm : m ≠ 0) : QuantClusteringFinVol G m :=
  fun p q => covariance_abs_le_maxDegree hm p q

/-! ## 2. The price -/

/-- **THE RATE DEGENERATES AS THE DEGREE GROWS.** `Δ/(Δ + m²) → 1`, so across a family of graphs
whose degrees are unbounded the estimate above collapses to `|cov| ≤ m⁻²` — true, and silent about
distance. **This is why the hypothesised bound in `GreenDecay` §4 cannot simply be deleted**: it is
what makes the rate a constant of the family rather than of the graph. -/
theorem decayRate_tendsto_one (hm : m ≠ 0) :
    Filter.Tendsto (fun Δ : ℕ => decayRate Δ m) Filter.atTop (nhds 1) := by
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have h : ∀ Δ : ℕ, decayRate Δ m = 1 - m ^ 2 / ((Δ : ℝ) + m ^ 2) := by
    intro Δ
    have hd : ((Δ : ℝ) + m ^ 2) ≠ 0 := by positivity
    rw [decayRate]
    field_simp
    ring
  simp only [h]
  have hz : Filter.Tendsto (fun Δ : ℕ => m ^ 2 / ((Δ : ℝ) + m ^ 2)) Filter.atTop (nhds 0) := by
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds)
    exact Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hz

end LatticeQuantClustering
