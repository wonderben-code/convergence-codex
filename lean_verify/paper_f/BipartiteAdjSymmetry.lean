import AdjSpectrumBracket
import RegularBipartiteSharp

/-!
# On a two-colourable graph the adjacency spectrum is symmetric, so yesterday's bracket is attained

`AdjSpectrumBracket` puts every adjacency eigenvalue in `[−Δ, Δ]` and keeps the top at or above
`√(deg v)`. It fences its own bottom end: *"`−Δ ≤ λ` is proved; that equality at the bottom happens
exactly for bipartite graphs is classical and is **not attempted**"*. `OpNormTopEigenvalue` fences
the same thing more sharply: *"**Not the least eigenvalue.** `‖A‖` is a ceiling and says nothing
about the bottom of the spectrum."*

**The easy direction of that is this file**, and it costs almost nothing because the construction
already existed. `RegularBipartiteSharp.IsSignColouring` is a `±1` labelling that flips across every
edge, and `exists_signColouring_of_colorable` builds one from `G.Colorable 2`. That file spends it
on `massive`; **nobody had spent it on the adjacency matrix** — checked in both vocabularies before
this file was written (`ERRATUM 446`): `adjMatrix` beside `signColouring` returns nothing, and no
least-eigenvalue statement about `adjMatrix` exists anywhere.

## What is proved

**`adjMatrix_mulVec_signMul`** — for a sign colouring `σ` and any `x`,

```
A *ᵥ (fun v => σ v * x v)  =  fun v => -(σ v * (A *ᵥ x) v)
```

because every neighbour's sign is the opposite of `v`'s, so the whole neighbour sum changes sign at
once. **No regularity, no connectivity, no eigenvector.**

**`mulVec_smul_neg_of_signColouring`** — hence `A *ᵥ x = μ • x` gives `A *ᵥ (σ·x) = (−μ) • (σ·x)`,
and `signMul_ne_zero` keeps the new vector nonzero because `σ` never vanishes. **So the adjacency
spectrum of a two-colourable graph is closed under negation.**

**`neg_topEigen_isEigenvalue_of_colorable`** — applied to the top eigenvector,
`−topEigen` is an eigenvalue. With `AdjSpectrumBracket` that says the bracket is **attained at both
ends**, and with `NonnegPerronNorm.topEigen_eq_of_regular` a `Δ`-regular two-colourable graph has
`Δ` and `−Δ` both in its spectrum: **`[−Δ, Δ]` is exactly right there, not merely a containment.**

## What is NOT here

**Not the converse**, which is the classical content: that symmetry of the spectrum, or `−λ_max`
being an eigenvalue, forces a bipartite component. That needs Perron–Frobenius for irreducible
nonnegative matrices — `PerronGap` and `PerronVector` work at **strictly** positive matrices and do
not apply — and it is **not attempted and not costed** (`ERRATUM 246`).

**Not a claim about `λ_min` in general.** Off the two-colourable class this file says nothing; the
bottom of the spectrum of an arbitrary graph is exactly where `OpNormTopEigenvalue`'s fence leaves
it.

**Not new machinery.** The sign colouring is `RegularBipartiteSharp`'s, cited and not restated, and
that is deliberate: the previous unit's erratum was a construction rebuilt because its other
vocabulary was not searched.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BipartiteAdjSymmetry

open Matrix Finset SimpleGraph RayleighVariational RegularBipartiteSharp
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The sign colouring flips the adjacency matrix -/

omit [DecidableEq V] in
/-- **`A *ᵥ (σ·x) = −(σ·(A *ᵥ x))`.** Every neighbour of `v` carries the opposite sign to `v`, so
the whole neighbour sum changes sign at once. No regularity and no eigenvector. -/
theorem adjMatrix_mulVec_signMul {σ : V → ℝ} (hσ : IsSignColouring G σ) (x : V → ℝ) (v : V) :
    ((G.adjMatrix ℝ) *ᵥ (fun u => σ u * x u)) v = -(σ v * ((G.adjMatrix ℝ) *ᵥ x) v) := by
  classical
  rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.adjMatrix_mulVec_apply]
  have hterm : ∀ u ∈ G.neighborFinset v, σ u * x u = -(σ v * x u) := by
    intro u hu
    have hadj : G.Adj u v := ((SimpleGraph.mem_neighborFinset _ _ _).mp hu).symm
    rw [hσ.2 u v hadj]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A sign colouring never vanishes, so multiplying by it preserves nonzeroness. -/
theorem signMul_ne_zero {σ : V → ℝ} (hσ : IsSignColouring G σ) {x : V → ℝ} (hx : x ≠ 0) :
    (fun u => σ u * x u) ≠ 0 := by
  intro h0
  refine hx (funext fun v => ?_)
  have hv := congrFun h0 v
  simp only [Pi.zero_apply] at hv
  rcases hσ.1 v with hs | hs <;> rw [hs] at hv <;> simp at hv <;> simp [hv]

/-! ## 2. So the spectrum is closed under negation -/

omit [DecidableEq V] in
/-- **EVERY EIGENVALUE'S NEGATIVE IS AN EIGENVALUE, ON A TWO-COLOURABLE GRAPH.** -/
theorem mulVec_smul_neg_of_signColouring {σ : V → ℝ} (hσ : IsSignColouring G σ) {μ : ℝ}
    {x : V → ℝ} (hx : (G.adjMatrix ℝ) *ᵥ x = μ • x) :
    (G.adjMatrix ℝ) *ᵥ (fun u => σ u * x u) = (-μ) • (fun u => σ u * x u) := by
  funext v
  rw [adjMatrix_mulVec_signMul G hσ x v, hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

omit [DecidableEq V] in
/-- **THE ADJACENCY SPECTRUM OF A TWO-COLOURABLE GRAPH IS CLOSED UNDER NEGATION.** -/
theorem neg_mem_spectrum_of_colorable (hcol : G.Colorable 2) {μ : ℝ}
    (hμ : ∃ x : V → ℝ, x ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ x = μ • x) :
    ∃ y : V → ℝ, y ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ y = (-μ) • y := by
  obtain ⟨σ, hσ⟩ := exists_signColouring_of_colorable hcol
  obtain ⟨x, hx0, hx⟩ := hμ
  exact ⟨fun u => σ u * x u, signMul_ne_zero G hσ hx0,
    mulVec_smul_neg_of_signColouring G hσ hx⟩

/-! ## 3. The bracket is attained at both ends -/

variable [Nonempty V]

/-- **`−topEigen` IS AN EIGENVALUE ON A TWO-COLOURABLE GRAPH**, so `AdjSpectrumBracket`'s
containment `[−Δ, Δ]` is attained at the bottom as well as the top. -/
theorem neg_topEigen_isEigenvalue_of_colorable (hcol : G.Colorable 2) :
    ∃ y : V → ℝ, y ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ y
      = (-(topEigen (NonnegPerronNorm.isHermitian_adjMatrix G))) • y := by
  refine neg_mem_spectrum_of_colorable G hcol ?_
  obtain ⟨x, hx0, hx⟩ :=
    OpNormTopEigenvalue.exists_eigenvector_sup' (NonnegPerronNorm.isHermitian_adjMatrix G)
  exact ⟨x, hx0, hx⟩

omit [DecidableEq V] in
/-- **AND ON A `Δ`-REGULAR TWO-COLOURABLE GRAPH THE SPECTRUM REACHES `−Δ`.** With
`NonnegPerronNorm.topEigen_eq_of_regular` giving `Δ` at the top, `[−Δ, Δ]` is exactly the range and
not merely a containment. -/
theorem neg_degree_isEigenvalue_of_regular_colorable {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hcol : G.Colorable 2) :
    ∃ y : V → ℝ, y ≠ 0 ∧ (G.adjMatrix ℝ) *ᵥ y = (-(Δ : ℝ)) • y := by
  classical
  have h := neg_topEigen_isEigenvalue_of_colorable G hcol
  rwa [NonnegPerronNorm.topEigen_eq_of_regular G hreg] at h

end BipartiteAdjSymmetry
