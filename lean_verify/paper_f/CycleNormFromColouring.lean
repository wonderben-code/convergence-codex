import LaplacianLoewnerConverse
import LaplacianNormSharp

/-!
# The odd cycle's strict bound in the NORM currency — and the finding is that I had it backwards

**READ THE ERRATUM FIRST** (`ERRATUM 436`). This file was written to make a point that this estate
had already made, a week earlier, in the file whose main theorem the whole 2026-09-03 chain is built
on.

`CycleSpectralBound`'s header names the obstacle it cleared: *"ruling attainment out needs every
eigenvalue below one, **which needs the eigenvalue list to be complete**. That was the blocker this
item was opened with."* **That claim about necessity is false**, and the estate knew it: on
2026-08-29 `LaplacianLoewnerConverse` §4 — a section titled **"The two families, with no spectrum
computed"** — proved **`odd_cycle_exists_lt`**, `∃ c < 4 + m², massive (cycleGraph (2M+3)) m ≼ c·1`,
from the colouring characterisation, **with no `m ≠ 0` and at `2M + 3` rather than `2M + 5`**, and
its docstring makes the comparison to `CycleSpectralBound` explicitly.

**MY VERSION OF THAT THEOREM WAS A STRICTLY WEAKER DUPLICATE AND IS WITHDRAWN** (`ERRATUM 337`'s
remedy: withdraw and cite). `odd_cycle_exists_lt` below is now a one-line reference to
`LaplacianLoewnerConverse.odd_cycle_exists_lt`, kept only so that a reader arriving here is sent to
the original rather than finding nothing.

## What is actually new here, measured rather than claimed

`LaplacianLoewnerConverse` states its results in the **Loewner order** and contains two `‖` in the
whole file. These are the **norm** statements, which that file does not have:

* **`norm_massive_lt_of_no_component_colorable`** — `‖massive G m‖ < 2Δ + m²` on a `Δ`-regular graph
  no connected component of which is two-colourable. **No connectivity hypothesis**, where
  `LaplacianLoewnerConverse`'s route through `massive_le_smul_one_iff_colorable` carries one.
* **`odd_cycle_norm_massive_lt`** — `‖massive (cycleGraph (2M+3)) m‖ < 4 + m²`.

`odd_cycle_not_colorable` is the chromatic-number step, which both routes need and which
`LaplacianLoewnerConverse` inlines rather than exporting.

## What is NOT new, stated because I claimed it was

**Not the conclusion**, **not the four-line route**, **not the reach to the triangle**, and **not
the observation that the eigenvalue list is unnecessary** — all four were in the estate on
2026-08-29.
`CycleSpectralBound` is not superseded by either route: it computes the cycle's entire spectrum, and
`apply_eq_of_mulVec_chi` is a general tool with other consumers.

**No wall moves**, and nothing consumes any of this.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleNormFromColouring

open Matrix GraphLaplacian SimpleGraph
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The general strict form at `massive` -/

/-- **`‖massive G m‖ < 2Δ + m²` WHEN NO COMPONENT IS TWO-COLOURABLE**, on a `Δ`-regular graph.
`LaplacianNormSharp.norm_lapMatrix_lt_of_no_component_colorable` is the same at `lapMatrix`; this is
the version the propagator's chain is stated in. -/
theorem norm_massive_lt_of_no_component_colorable [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) {m : ℝ} (hm : m ≠ 0)
    (hcol : ∀ C : G.ConnectedComponent, ¬ (G.induce C.supp).Colorable 2) :
    ‖massive G m‖ < 2 * (Δ : ℝ) + m ^ 2 := by
  have hdeg : ∀ p : V, (G.degree p : ℝ) ≤ (Δ : ℝ) := fun p => by rw [hreg p]
  rcases lt_or_eq_of_le (LaplacianOpNorm.norm_massive_le G hdeg hm) with h | h
  · exact h
  · obtain ⟨C, hC⟩ :=
      (LaplacianNormSharp.norm_massive_eq_iff_exists_component_colorable G hreg hm).mp h
    exact absurd hC (hcol C)

/-! ## 2. The odd cycle -/

/-- **AN ODD CYCLE IS NOT TWO-COLOURABLE**, off its chromatic number. -/
theorem odd_cycle_not_colorable (M : ℕ) : ¬ (cycleGraph (2 * M + 3)).Colorable 2 := by
  intro hcol
  have hchi : (cycleGraph (2 * M + 3)).chromaticNumber = 3 :=
    chromaticNumber_cycleGraph_of_odd (2 * M + 3) (by omega) ⟨M + 1, by ring⟩
  have hle := hcol.chromaticNumber_le
  rw [hchi] at hle
  norm_num at hle

/-- **`‖massive (cycleGraph (2M+3)) m‖ < 4 + m²` AT EVERY ODD LENGTH FROM THREE.**
The Loewner form of this is
`LaplacianLoewnerConverse.odd_cycle_exists_lt` (2026-08-29); what is new is only the currency. -/
theorem odd_cycle_norm_massive_lt (M : ℕ) {m : ℝ} (hm : m ≠ 0) :
    ‖massive (cycleGraph (2 * M + 3)) m‖ < 4 + m ^ 2 := by
  have hreg : (cycleGraph (2 * M + 3)).IsRegularOfDegree 2 := fun v =>
    cycleGraph_degree_three_le (n := 2 * M) (v := v)
  have hconn : (cycleGraph (2 * M + 3)).Connected := by
    have := SimpleGraph.cycleGraph_connected (n := 2 * M + 2)
    simpa using this
  have hlt := norm_massive_lt_of_no_component_colorable (cycleGraph (2 * M + 3)) hreg hm
    (fun C hC => odd_cycle_not_colorable M (by
      have hsupp : C.supp = Set.univ := by
        obtain ⟨v₀, hv₀⟩ := C.exists_rep
        subst hv₀
        ext v
        simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, Set.mem_univ, iff_true]
        exact SimpleGraph.ConnectedComponent.sound (hconn.preconnected v v₀)
      rw [hsupp] at hC
      exact SimpleGraph.Colorable.of_hom
        (SimpleGraph.induceUnivIso (cycleGraph (2 * M + 3))).symm.toHom hC))
  norm_num at hlt
  exact hlt

/-- **WITHDRAWN AND CITED** (`ERRATUM 337`'s remedy, `ERRATUM 436`). This was written as a new
theorem and is `LaplacianLoewnerConverse.odd_cycle_exists_lt`, proved 2026-08-29 **without**
`m ≠ 0`, so the original is strictly stronger. Kept as a one-line reference so a reader arriving
here is sent to it. -/
theorem odd_cycle_exists_lt (M : ℕ) (m : ℝ) :
    ∃ c : ℝ, c < 4 + m ^ 2 ∧ massive (cycleGraph (2 * M + 3)) m
      ≤ c • (1 : Matrix (Fin (2 * M + 3)) (Fin (2 * M + 3)) ℝ) :=
  LaplacianLoewnerConverse.odd_cycle_exists_lt M m

end CycleNormFromColouring
