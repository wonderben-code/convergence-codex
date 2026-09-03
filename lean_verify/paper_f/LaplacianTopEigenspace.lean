import LaplacianSignlessKernel
import RayleighAttainment

/-!
# The top eigenspace of a regular graph's Laplacian, and its dimension

`RayleighAttainment` §4 identified *a vector attains the degree bound* with *`2Δ` is an eigenvalue*
on any regular graph, as an **existence** statement. This file makes it pointwise and then counts.

**THE ESTATE ALREADY HAD THE HARD HALF, IN ANOTHER CURRENCY, AND THE GREP FOUND IT BEFORE ANYTHING
WAS WRITTEN** (`ERRATUM 436`'s rule, working). `LaplacianSignless.signlessLap` is `Q = D + A`;
`LaplacianSignlessDefinite.signlessLap_mulVec_eq_zero_iff` says `Q x = 0` **iff `x` flips sign
across every edge**, at every finite graph; and
`LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` says **`dim ker Q` is the number
of two-colourable components**, also with no hypothesis. On a
`Δ`-regular graph `D = Δ • 1`, so `Q = 2Δ • 1 − L` and those are statements about `L`'s **top
eigenspace**. Nothing here re-proves any of them.

> **`signlessLap_eq_of_regular`** — `Q = 2Δ • 1 − L` on a `Δ`-regular graph, which is the whole
> join.
>
> **`mulVec_eq_top_smul_iff_neg_adj`** — `L x = 2Δ • x` **iff** `x` flips sign across every edge.
> Pointwise, and with **no connectivity**.
>
> **`card_bipartiteComponent_eq_finrank_top_eigenspace`** — **the multiplicity of `2Δ` as an
> eigenvalue of `L` is the number of two-colourable connected components.**

## What that adds and what it does not

**It is a currency change and it says so.** Every mathematical step is `LaplacianSignless*`'s; what
is new is that those statements are read on `L` rather than on `Q`, which is where the rest of this
estate's Laplacian work lives — `LaplacianDegreeBound`, `LaplacianSharpEquality`,
`LaplacianLoewnerConverse`, `LaplacianNormSharp` and `RayleighAttainment` all speak about `L` and
none of them mentions `Q`.

**IT MAKES THE DAY'S EXISTENCE RESULTS QUANTITATIVE.**
`RayleighAttainment.exists_eigenvector_top_iff_exists_quadForm_eq` and
`LaplacianNormSharp.norm_lapMatrix_eq_iff_exists_component_colorable` both say *there is such a
vector iff some component is two-colourable*; this says **how many** independent ones there are, and
the two are consistent by construction — the count is positive exactly when the index type is
non-empty.

**It computes no other multiplicity.** `2Δ` is the only eigenvalue this reaches, because `Q`'s
kernel is the only fibre `LaplacianSignlessKernel` counts. The open item about eigenvalue fibres of
the massive torus Laplacian asks about **every** fibre and is untouched.

**No wall moves**, and nothing consumes this.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianTopEigenspace

open Matrix SimpleGraph LaplacianSignless

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. On a regular graph the signless Laplacian is the degree bound minus the Laplacian -/

/-- **`D = Δ • 1` ON A `Δ`-REGULAR GRAPH.** -/
theorem degMatrix_eq_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    G.degMatrix ℝ = (Δ : ℝ) • (1 : Matrix V V ℝ) := by
  ext u v
  rw [SimpleGraph.degMatrix, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply]
  by_cases h : u = v <;> simp [h, hreg u]

/-- **`Q = 2Δ • 1 − L`**, which is the whole join: everything `LaplacianSignless*` proves about
`Q`'s kernel is a statement about `L`'s top eigenspace. -/
theorem signlessLap_eq_of_regular {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    signlessLap G = (2 * (Δ : ℝ)) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ := by
  rw [signlessLap, SimpleGraph.lapMatrix, degMatrix_eq_of_regular G hreg]
  ext u v
  simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> ring

/-! ## 2. The eigenspace, pointwise -/

/-- **`L x = 2Δ • x` IFF `x` FLIPS SIGN ACROSS EVERY EDGE**, on a `Δ`-regular graph, **pointwise and
with no connectivity**. `LaplacianSignlessDefinite.signlessLap_mulVec_eq_zero_iff` read on `L`. -/
theorem mulVec_eq_top_smul_iff_neg_adj {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (x : V → ℝ) :
    G.lapMatrix ℝ *ᵥ x = (2 * (Δ : ℝ)) • x ↔ ∀ u v : V, G.Adj u v → x v = - x u := by
  rw [← LaplacianSignlessDefinite.signlessLap_mulVec_eq_zero_iff G x,
    signlessLap_eq_of_regular G hreg, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero]
  exact eq_comm

/-! ## 3. And its dimension -/

/-- **THE MULTIPLICITY OF `2Δ` AS AN EIGENVALUE OF `L` IS THE NUMBER OF TWO-COLOURABLE CONNECTED
COMPONENTS**, on a `Δ`-regular graph.
`LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` read on `L`. -/
theorem card_bipartiteComponent_eq_finrank_top_eigenspace {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) :
    Fintype.card (LaplacianSignlessKernel.BipComp G)
      = Module.finrank ℝ
          (LinearMap.ker (Matrix.toLin' ((2 * (Δ : ℝ)) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ))) := by
  rw [← signlessLap_eq_of_regular G hreg]
  exact LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker G

end LaplacianTopEigenspace
