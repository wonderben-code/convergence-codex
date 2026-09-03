import GreenNormExact
import LaplacianLoewnerDisconnected

/-!
# `‖L‖ = 2Δ` exactly when the graph is two-colourable

`LaplacianOpNorm.norm_lapMatrix_le` proved `‖G.lapMatrix ℝ‖ ≤ 2Δ` from a degree bound and said
nothing about when it is attained. `GreenNormExact` settled the same question for the propagator and
the answer was *always*. **Here the answer is a graph property**, and the estate already knew it in
two other currencies.

## The currency conversion, and it is the whole file

`LaplacianSharpEquality.exists_quadForm_eq_iff_colorable` (29 Aug) has the QUADRATIC FORM version —
some `x ≠ 0` attains `xᵀLx = 2Δ(x ⬝ᵥ x)` iff the graph is two-colourable — and
`LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable` has the LOEWNER version: the constant
`2Δ + m²` cannot be lowered iff the graph is two-colourable. **Neither is a statement about a
norm**, and the estate had no norm equality for the Laplacian at all — probed by shape before this
file was written: every occurrence of `‖…lapMatrix…‖` in `paper_f` is an inequality.

`OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one` is the bridge, and §1 is the general step:

> **`opNorm_eq_iff_min_smul_one`** — for `0 ≼ A` with `A ≼ r • 1`, `‖A‖ = r` **iff** `r` is the
> least such `r`. An operator norm IS the minimum of the Loewner ceilings.

That is a statement about positive semidefinite matrices with no graph in it, and it turns any
"this constant cannot be lowered" theorem into a norm equality, for free.

## What comes out

* **`norm_massive_eq_iff_colorable`** — for a connected `Δ`-regular graph and `m ≠ 0`,
  `‖massive G m‖ = 2Δ + m²` **iff** `G.Colorable 2`.
* **`norm_lapMatrix_eq_iff_colorable`** — the same at `m = 0`: `‖G.lapMatrix ℝ‖ = 2Δ` **iff**
  `G.Colorable 2`.
* **`norm_lapMatrix_lt_of_not_colorable`** — and so the bound is **strict** on a connected regular
  graph that is not two-colourable, which is the form a consumer of `norm_lapMatrix_le` would want.

## What it is not

**No new mathematics.** Every ingredient predates this file; what is new is that the three
statements are now the same statement, and that the operator-norm chain of 2026-09-02 can quote a
sharpness result rather than an inequality. `PROOF_STRATEGY` §7 rule 1 — *re-sweep against
everything now proven* — rather than rule 3.

**CONNECTIVITY AND REGULARITY ARE BOTH LOAD-BEARING AND NEITHER IS MINE TO REMOVE.**
`ConnectivityNecessary.connectivity_necessary` (30 Aug) refutes the underlying characterisation on a
seven-vertex witness with connectivity deleted, and `LaplacianSharpEquality`'s own header records
that the Loewner statements cannot lose regularity as they stand — *"without the collapse there is
no single constant to compare against"*. So the hypotheses here are inherited, and known necessary
rather than believed necessary.

**⚠ HALF OF THAT PARAGRAPH IS FALSE AND IT IS KEPT AS WRITTEN** (`ERRATUM 94`, **`ERRATUM 435`**,
the same day). **Regularity is necessary** — `LoewnerRegularityNecessary.regularity_necessary`
refutes weakening it to a degree bound, and does so against the GENERAL statement, so that half
stands. **Connectivity is not**, and the estate had already removed it:
`LaplacianLoewnerDisconnected.massive_le_smul_one_iff_exists_component_colorable` is the same
Loewner characterisation **with no connectivity hypothesis at all**, in a file that IMPORTS the one
this file used. What `connectivity_necessary` refutes is `exists_quadForm_eq_iff_colorable` with
connectivity deleted **and the conclusion left as `G.Colorable 2`** — it says the CONCLUSION has to
change, not that the hypothesis has to stay, and the changed conclusion is *some connected component
is two-colourable*. §3 below is that statement in the norm currency, and §2 is instantiated from it
(`ERRATUM 201`) rather than merely asserted to be its special case.

**FIRST CONSUMER, 2026-09-03, THE SAME DAY**: `TorusNormSharp` instantiates §3 at the periodic
lattice and gets `‖massive (torusGraph d n) m‖ = 4d + m² ↔ Even n` in every dimension, with the
component quantifier collapsed by `TorusDecay.torusGraph_connected`. **The sentence below was exact
when written and is kept** (`ERRATUM 94`): what it says is that nothing wanted the *attainment*, and
that is still true of `NeumannTailBound` and `LaplacianOpNorm`'s consumers.

**Nothing consumes it**, stated here rather than left to be discovered (`ERRATUM 434`'s week):
`NeumannTailBound` and `LaplacianOpNorm`'s consumers want an upper bound and are unaffected by its
being attained or not. **No wall moves**: `W1` asks for a lower bound on the cross form
(`WALLS.md` §W1.5), which is a different object on a different operator.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianNormSharp

open Matrix GraphLaplacian
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. An operator norm is the least Loewner ceiling -/

/-- **`‖A‖ = r` IFF `r` IS THE LEAST `c` WITH `A ≼ c • 1`**, for a positive semidefinite real
matrix already known to sit below `r • 1`. Both directions are
`OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one`, once forward and once at `c = ‖A‖`. -/
theorem opNorm_eq_iff_min_smul_one [Nonempty V] {A : Matrix V V ℝ} (hA : 0 ≤ A) {r : ℝ}
    (hr : A ≤ r • (1 : Matrix V V ℝ)) :
    ‖A‖ = r ↔ ∀ c : ℝ, A ≤ c • (1 : Matrix V V ℝ) → r ≤ c := by
  constructor
  · intro heq c hc
    rw [← heq]
    exact (OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one hA).mpr hc
  · intro hmin
    refine le_antisymm ((OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one hA).mpr hr) ?_
    exact hmin _ ((OpNormLoewnerConverse.l2_opNorm_le_iff_le_smul_one hA).mp le_rfl)

/-! ## 2. The graph statements -/

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`‖massive G m‖ = 2Δ + m²` IFF THE GRAPH IS TWO-COLOURABLE**, on a connected `Δ`-regular
graph. -/
theorem norm_massive_eq_iff_colorable [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) {m : ℝ} (hm : m ≠ 0) :
    ‖massive G m‖ = 2 * (Δ : ℝ) + m ^ 2 ↔ G.Colorable 2 := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  rw [opNorm_eq_iff_min_smul_one (massive_posDef G hm).posSemidef.nonneg
    (LaplacianDegreeBound.massive_le_smul_one G hdeg m)]
  exact LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable G hreg hG m

/-- **`‖G.lapMatrix ℝ‖ = 2Δ` IFF THE GRAPH IS TWO-COLOURABLE**, the `m = 0` case, and the norm
statement `LaplacianOpNorm.norm_lapMatrix_le` left open. -/
theorem norm_lapMatrix_eq_iff_colorable [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) :
    ‖G.lapMatrix ℝ‖ = 2 * (Δ : ℝ) ↔ G.Colorable 2 := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  have h0 : massive G 0 = G.lapMatrix ℝ := by simp [GraphLaplacian.massive]
  have hiff := LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable G hreg hG 0
  rw [h0] at hiff
  rw [opNorm_eq_iff_min_smul_one (SimpleGraph.posSemidef_lapMatrix ℝ G).nonneg
    (LaplacianDegreeBound.lapMatrix_le_smul_one G hdeg)]
  simpa using hiff

/-- **AND SO THE DEGREE BOUND IS STRICT OFF THE TWO-COLOURABLE GRAPHS**, which is the shape a
consumer of `LaplacianOpNorm.norm_lapMatrix_le` would want. -/
theorem norm_lapMatrix_lt_of_not_colorable [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (hcol : ¬ G.Colorable 2) : ‖G.lapMatrix ℝ‖ < 2 * (Δ : ℝ) := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  have hle := LaplacianOpNorm.norm_lapMatrix_le G hdeg
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd ((norm_lapMatrix_eq_iff_colorable G hreg hG).mp h) hcol

/-! ## 3. And connectivity comes off, because the estate had already taken it off -/

/-- **`‖massive G m‖ = 2Δ + m²` IFF SOME CONNECTED COMPONENT IS TWO-COLOURABLE**, on a `Δ`-regular
graph with **no connectivity hypothesis**. Same conversion, applied to
`LaplacianLoewnerDisconnected`'s characterisation instead of `LaplacianLoewnerConverse`'s
(`ERRATUM 435`). -/
theorem norm_massive_eq_iff_exists_component_colorable [Nonempty V] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) {m : ℝ} (hm : m ≠ 0) :
    ‖massive G m‖ = 2 * (Δ : ℝ) + m ^ 2
      ↔ ∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2 := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  rw [opNorm_eq_iff_min_smul_one (massive_posDef G hm).posSemidef.nonneg
    (LaplacianDegreeBound.massive_le_smul_one G hdeg m)]
  exact LaplacianLoewnerDisconnected.massive_le_smul_one_iff_exists_component_colorable G hreg m

/-- **`‖G.lapMatrix ℝ‖ = 2Δ` IFF SOME CONNECTED COMPONENT IS TWO-COLOURABLE**, the `m = 0` case with
no connectivity hypothesis. -/
theorem norm_lapMatrix_eq_iff_exists_component_colorable [Nonempty V] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ) :
    ‖G.lapMatrix ℝ‖ = 2 * (Δ : ℝ)
      ↔ ∃ C : G.ConnectedComponent, (G.induce C.supp).Colorable 2 := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  have h0 : massive G 0 = G.lapMatrix ℝ := by simp [GraphLaplacian.massive]
  have hiff :=
    LaplacianLoewnerDisconnected.massive_le_smul_one_iff_exists_component_colorable G hreg 0
  rw [h0] at hiff
  rw [opNorm_eq_iff_min_smul_one (SimpleGraph.posSemidef_lapMatrix ℝ G).nonneg
    (LaplacianDegreeBound.lapMatrix_le_smul_one G hdeg)]
  simpa using hiff

/-- **AND SO THE DEGREE BOUND IS STRICT ON A REGULAR GRAPH NO COMPONENT OF WHICH IS
TWO-COLOURABLE**, with no connectivity hypothesis. -/
theorem norm_lapMatrix_lt_of_no_component_colorable [Nonempty V] {Δ : ℕ}
    (hreg : G.IsRegularOfDegree Δ)
    (hcol : ∀ C : G.ConnectedComponent, ¬ (G.induce C.supp).Colorable 2) :
    ‖G.lapMatrix ℝ‖ < 2 * (Δ : ℝ) := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  rcases lt_or_eq_of_le (LaplacianOpNorm.norm_lapMatrix_le G hdeg) with h | h
  · exact h
  · obtain ⟨C, hC⟩ := (norm_lapMatrix_eq_iff_exists_component_colorable G hreg).mp h
    exact absurd hC (hcol C)

/-- **§2 IS INSTANTIATED FROM §3 RATHER THAN ASSERTED TO BE ITS SPECIAL CASE** (`ERRATUM 201`), and
the bridge is one line because both characterisations describe the SAME least-ceiling condition. -/
example [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) (hG : G.Connected) {m : ℝ}
    (hm : m ≠ 0) : ‖massive G m‖ = 2 * (Δ : ℝ) + m ^ 2 ↔ G.Colorable 2 := by
  rw [norm_massive_eq_iff_exists_component_colorable G hreg hm]
  have hgen :=
    LaplacianLoewnerDisconnected.massive_le_smul_one_iff_exists_component_colorable G hreg m
  exact hgen.symm.trans (LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable G hreg hG m)

end LaplacianNormSharp
