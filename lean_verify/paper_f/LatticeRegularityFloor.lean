import LatticeRegularity
import GreenLoewnerFloorSharp
import LaplacianNormLowerBound
import MassiveSpectrumRange

/-!
# The generating functional has a Gaussian FLOOR as well as a Gaussian ceiling

`LatticeRegularity.generatingFunctional_le` bounds `∫ exp ⟪f, ω⟫` above by `exp(‖f‖²/(2m²))`, and
`LatticeRegularitySharp` proves that constant optimal. **Below, the estate had only
`one_le_generatingFunctional`** — the constant `1`, which is what positive semidefiniteness gives
and says nothing about how the functional grows. Counted before this file was written: of the
`Real.exp … ≤ ∫ …` shapes in `paper_f/`, there were **0**.

`PROOF_STRATEGY` §7 rule 3, and the hypothesis removed is the one that made the floor trivial.

## What is proved

**`smul_one_le_green_norm`** — `‖massive G m‖⁻¹ · 1 ≼ green G m` at **every** finite nonempty graph
and every `m ≠ 0`, **with no degree hypothesis at all**. It is
`GreenLoewnerFloorSharp.smul_one_le_green_iff` read at `c = ‖massive G m‖⁻¹`, where the
biconditional's right-hand side becomes `‖massive‖ ≤ ‖massive‖`. That file proved the equivalence
and instantiated it at the box; **the self-referential instance is the one it did not take**, and
it is the only one that needs nothing about the graph.

**`quadForm_green_ge`** — hence `‖f‖² / ‖massive G m‖ ≤ f ⬝ᵥ green G m *ᵥ f`, through
`PosSemidefNormBound.dotProduct_mono`.

**`le_generatingFunctional`** — hence `exp(‖f‖² / (2‖massive G m‖)) ≤ ∫ exp ⟪f, ω⟫`.

**`generatingFunctional_sandwich`** — the two together:

```
exp( ‖f‖² / (2‖massive G m‖) )  ≤  ∫ exp ⟪f, ω⟫  ≤  exp( ‖f‖² / (2m²) )
```

**`greatest_smul_one_le_green`** — and `‖massive G m‖⁻¹` is the **largest** constant for which a
Loewner floor holds, which is the same biconditional read the other way. So the floor above is the
best of its shape.

**`le_generatingFunctional_of_degree_le`** — the concrete form, `exp(‖f‖²/(2(2Δ + m²)))` on a graph
of degree at most `Δ`, which names a degree ceiling and a mass and **not the vertex count**. It is
**derived from the norm floor rather than reproved**, through `LaplacianOpNorm.norm_massive_le`
(`‖massive G m‖ ≤ 2Δ + m²`) — which is also the statement that **the norm floor is always at least
as good as the degree floor**, at every graph.

**`sandwich_collapse_iff`** — **the two ends meet exactly on the edgeless graph.** One edge forces
`2 + m² ≤ ‖massive G m‖` through `LaplacianNormLowerBound.le_norm_massive_of_adj`, and on `⊥` the
operator is `m²·1`. So the floor equals the ceiling iff there is nothing to propagate along, and
**this one needs no hypothesis on `m` at all** — at `m = 0` it says `‖lapMatrix‖ = 0` iff edgeless.

## What is NOT here

**No new axiom and no new bound on the estate's side.** The ceiling, the optimality of its constant,
the Loewner biconditional, the edge bound and `m² • 1 ≼ massive` are all quoted.

**Not an attaining test function for the FUNCTIONAL floor.** `greatest_smul_one_le_green` settles
optimality at the level of the Loewner order, where the biconditional does the work. Exhibiting an
`f` at which `exp(‖f‖²/(2‖massive G m‖))` is an *equality* would need the top eigenvector of
`massive G m`, which this estate produces only on named families (`LaplacianBoundSharp`,
`TorusRegular`), not in general. **Not attempted and no cost claimed.**

> ⚠ **THE PARAGRAPH ABOVE CONFLATES TWO QUESTIONS AND IS KEPT AS WRITTEN** (`ERRATUM 94`,
> **`ERRATUM 452`**, 2026-09-04, the very next unit). *Optimality of the constant* and *attainment
> at a test function* are different claims, and **only the second needs an eigenvector**.
> `LatticeFloorOptimal.le_of_le_generatingFunctional` proves the first with none: a floor holding at
> every test function **is** a Loewner floor, because a symmetric matrix whose quadratic form
> dominates `c‖x‖²` everywhere is `≽ c · 1` by definition, and `greatest_smul_one_le_green` already
> caps every Loewner floor. **The tool was in this file.** What the paragraph asked for — an `f`
> where the bound is met — is still open, and is still not attempted.

**Not a lower bound with a graph-free constant.** `‖massive G m‖` is a property of the graph, and it
must be: on a graph with an edge the functional genuinely is larger than the edgeless one at the
same `‖f‖`, so no floor naming only `m` can be sharp. **That is the asymmetry between the two ends
of the sandwich**, and it is why the ceiling is uniform and the floor is not.

**`OS0` in the continuum sense is untouched**, as is `OS4`. **No wall moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeRegularityFloor

open Matrix GraphLaplacian MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The propagator's Loewner floor, with no hypothesis on the graph -/

/-- `m² ≤ ‖massive G m‖`, so the norm is positive — `MassiveSpectrumRange.smul_one_le_massive`
through `OpNormLowerBound.le_opNorm_of_smul_one_le`. -/
theorem massSq_le_norm_massive [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    m ^ 2 ≤ ‖massive G m‖ :=
  OpNormLowerBound.le_opNorm_of_smul_one_le (MassiveSpectrumRange.smul_one_le_massive G m)

theorem norm_massive_pos [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : m ≠ 0) :
    0 < ‖massive G m‖ :=
  lt_of_lt_of_le (by positivity) (massSq_le_norm_massive G m)

/-- **THE PROPAGATOR'S FLOOR AT EVERY GRAPH**, with no degree bound and no other hypothesis:
`‖massive G m‖⁻¹ · 1 ≼ green G m`. `GreenLoewnerFloorSharp.smul_one_le_green_iff` at
`c = ‖massive G m‖⁻¹`, where its right-hand side is `‖massive‖ ≤ ‖massive‖`. -/
theorem smul_one_le_green_norm [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : m ≠ 0) :
    ‖massive G m‖⁻¹ • (1 : Matrix V V ℝ) ≤ green G m := by
  have hpos := norm_massive_pos G hm
  refine (GreenLoewnerFloorSharp.smul_one_le_green_iff G hm (by positivity)).mpr ?_
  rw [inv_inv]

/-- **AND `‖massive G m‖⁻¹` IS THE LARGEST CONSTANT THAT WORKS**, the same biconditional read the
other way, so the floor above is the best of its shape. -/
theorem greatest_smul_one_le_green [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : m ≠ 0) {c : ℝ} (hc : 0 < c) (h : c • (1 : Matrix V V ℝ) ≤ green G m) :
    c ≤ ‖massive G m‖⁻¹ := by
  have hnorm := (GreenLoewnerFloorSharp.smul_one_le_green_iff G hm hc).mp h
  rwa [le_inv_comm₀ (norm_massive_pos G hm) hc] at hnorm

/-! ## 2. And so the quadratic form, and the generating functional -/

/-- **THE QUADRATIC FORM FROM BELOW.** -/
theorem quadForm_green_ge [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : m ≠ 0)
    (f : EuclideanSpace ℝ V) : ‖f‖ ^ 2 / ‖massive G m‖ ≤ f ⬝ᵥ green G m *ᵥ f := by
  have h := PosSemidefNormBound.dotProduct_mono (smul_one_le_green_norm G hm) (WithLp.ofLp f)
  rw [PosSemidefNormBound.norm_sq_eq_dotProduct f, div_eq_inv_mul]
  simpa [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] using h

/-- **THE GENERATING FUNCTIONAL HAS A GAUSSIAN FLOOR.** Before this the estate's only lower bound
was the constant `1` (`LatticeRegularity.one_le_generatingFunctional`). -/
theorem le_generatingFunctional [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (hm : m ≠ 0)
    (f : EuclideanSpace ℝ V) :
    Real.exp (‖f‖ ^ 2 / (2 * ‖massive G m‖)) ≤ ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) := by
  rw [LatticeGeneratingFunctional.generatingFunctional (G := G) (m := m) hm f]
  refine Real.exp_le_exp.2 ?_
  have hq := quadForm_green_ge G hm f
  have hpos := norm_massive_pos G hm
  have hsplit : ‖f‖ ^ 2 / ‖massive G m‖ / 2 = ‖f‖ ^ 2 / (2 * ‖massive G m‖) := by
    rw [div_div, mul_comm]
  linarith [hq, hsplit]

/-- **THE SANDWICH.** The ceiling's constant names only the mass; the floor's names the graph. -/
theorem generatingFunctional_sandwich [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    Real.exp (‖f‖ ^ 2 / (2 * ‖massive G m‖)) ≤ ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) ∧
      ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) ≤ Real.exp (‖f‖ ^ 2 / (2 * m ^ 2)) :=
  ⟨le_generatingFunctional G hm f, LatticeRegularity.generatingFunctional_le hm f⟩

/-- **AND THE CONCRETE FORM**, on a graph of degree at most `Δ`: the constant names a degree
ceiling and a mass and **not the vertex count**. -/
theorem le_generatingFunctional_of_degree_le [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    Real.exp (‖f‖ ^ 2 / (2 * (2 * Δ + m ^ 2))) ≤ ∫ ω, Real.exp ⟪f, ω⟫ ∂(gaussianField G m) := by
  have hpos := norm_massive_pos G hm
  have hle : ‖massive G m‖ ≤ 2 * Δ + m ^ 2 := LaplacianOpNorm.norm_massive_le G hΔ hm
  refine le_trans (Real.exp_le_exp.2 ?_) (le_generatingFunctional G hm f)
  have h2 : (0 : ℝ) < 2 * ‖massive G m‖ := by positivity
  refine div_le_div_of_nonneg_left (sq_nonneg _) h2 ?_
  linarith

/-! ## 3. When the two ends meet -/

/-- **THE SANDWICH COLLAPSES EXACTLY ON THE EDGELESS GRAPH.** One edge forces `2 + m²` below the
norm, by `LaplacianNormLowerBound.le_norm_massive_of_adj` and the fact that an edge's endpoints have
degree at least one; and `⊥`'s operator is `m² · 1`. **No hypothesis on `m`**: at `m = 0` the
statement reads `‖lapMatrix‖ = 0` iff the graph is edgeless, which is true and is the same proof. -/
theorem sandwich_collapse_iff [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    ‖massive G m‖ = m ^ 2 ↔ ∀ u v : V, ¬ G.Adj u v := by
  constructor
  · intro heq u v huv
    have hu : (1 : ℝ) ≤ (G.degree u : ℝ) := by
      have : 0 < G.degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨v, by simpa using huv⟩
      exact_mod_cast this
    have hv : (1 : ℝ) ≤ (G.degree v : ℝ) := by
      have : 0 < G.degree v := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨u, by simpa using huv.symm⟩
      exact_mod_cast this
    have hb := LaplacianNormLowerBound.le_norm_massive_of_adj G huv m
    rw [heq] at hb
    linarith
  · intro hnone
    have hbot : G = ⊥ := by
      ext u v
      exact ⟨fun h => absurd h (hnone u v), fun h => absurd h (by simp)⟩
    subst hbot
    have hdeg : ∀ x : V, ((⊥ : SimpleGraph V).degree x : ℝ) = 0 := by
      intro x
      have : (⊥ : SimpleGraph V).neighborFinset x = ∅ := by
        ext y; simp
      rw [← SimpleGraph.card_neighborFinset_eq_degree, this]
      simp
    have hlap : (⊥ : SimpleGraph V).lapMatrix ℝ = 0 := by
      ext p q
      simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix_apply, hdeg]
    have hmas : massive (⊥ : SimpleGraph V) m = Matrix.diagonal (fun _ : V => m ^ 2) := by
      rw [GraphLaplacian.massive, hlap, zero_add]
    rw [hmas, Matrix.l2_opNorm_diagonal]
    simp [Real.norm_eq_abs]

end LatticeRegularityFloor
