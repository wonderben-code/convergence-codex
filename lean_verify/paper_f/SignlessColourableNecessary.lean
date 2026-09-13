import SignlessConjugateMultiplicity
import LaplacianSignlessKernel
import CycleNormFromColouring

/-!
# The two-colouring is not a convenience: it is exactly the condition, and it fails at zero

**THE QUESTION THE PREVIOUS UNIT'S `§6` ASKED, ANSWERED.** `SignlessConjugateMultiplicity` proved
that `Q` and `L` have the same multiplicity at every real `μ` **on a graph with a two-colouring**,
and fenced itself in these words: *the two-colouring hypothesis is not shown necessary — no graph
is exhibited where the two multiplicities differ.* This file removes the fence, and does better
than exhibiting a graph: the hypothesis is **exactly** the condition, on every finite graph, and
when it fails the failure is already visible at `μ = 0`.

**WHAT THE ESTATE ALREADY HAD, AND WHY THIS IS NOT IT.** `SignlessBipartite.
charpoly_signlessLap_ne_of_posDef` shows the two **characteristic polynomials** differ whenever `Q`
is positive definite, and `charpoly_signlessLap_ne_odd_cycle` spends it on the odd cycles. Those
are a *sufficient condition for failure* on a *family*, about the polynomial. What is here is a
**biconditional, about eigenspace dimensions, on every finite graph, with no hypothesis at all**.

**THE PROOF IS TWO COUNTS THAT WERE ALREADY IN THE ESTATE, PUT BESIDE EACH OTHER.**
Mathlib's `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` says `L`'s kernel has dimension
the number of **components**; `LaplacianSignlessKernel.card_bipartiteComponent_eq_finrank_ker` says
`Q`'s has dimension the number of **two-colourable** components. One index set is a subtype of the
other, so the dimensions are equal exactly when the predicate holds everywhere — and by Mathlib's
`colorable_iff_forall_connectedComponents`, that is `G.Colorable 2`. Neither count is new and the
comparison had not been made.

## What is proved

**`finrank_ker_signlessLap_le_lap`** — **`Q`'s kernel is never bigger than `L`'s**, on any finite
graph, with no hypothesis. A subtype is no bigger than its type.

**`finrank_ker_eq_iff_colorable`** — and **they are equal exactly when `G` is two-colourable**.

**`colorable_two_iff_forall_finrank_eq`** — **THE FILE'S THEOREM.** `G.Colorable 2` iff `Q` and `L`
have the same multiplicity at every real `μ`. Sufficiency is the previous unit; necessity is the
line above, so **the single value `μ = 0` decides it** — a graph whose multiplicities agree
anywhere they can disagree agrees everywhere.

**`not_forall_finrank_eq_odd_cycle`** — the estate's own witness, made concrete: on an odd cycle
the two operators disagree. **`finrank_ker_signlessLap_odd_cycle`** and
**`finrank_ker_lapMatrix_odd_cycle`** say where and by how much: `Q`'s kernel is `0` because no
component is two-colourable, `L`'s is a **line** because the cycle is connected, and `μ = 0` is
the separating value.

## What is NOT here

* **NO STATEMENT ABOUT WHICH `μ` OTHER THAN `0` CAN SEPARATE THEM.** The theorem says that if the
  multiplicities agree at every `μ` the graph is two-colourable, and the proof reads only `μ = 0`.
  **It does not say `0` is the only separating value**, and no example is computed where some other
  `μ` separates. That would need a graph's full signless spectrum off the two-colourable case, and
  the estate has exactly one — the paw.
* **NOTHING ABOUT THE CHARACTERISTIC POLYNOMIAL.** `SignlessBipartite`'s two necessity theorems are
  about the polynomial and are neither restated nor generalised here (`ERRATUM 176`); this file's
  biconditional does not imply them, algebraic and geometric multiplicity being different things
  on a matrix nobody has shown to be diagonalisable.
* **NO COUNT OF THE DEFICIENCY.** `finrank ker L − finrank ker Q` is the number of components that
  are **not** two-colourable, which both cited counts make immediate; it is not stated, because
  nothing in this chain has asked for it.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a finite vertex type with decidable
equality and decidable adjacency. **No connectivity, no regularity, no parity, and no
`Nonempty`** — the empty graph satisfies the biconditional vacuously on both sides.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessColourableNecessary

open Matrix SimpleGraph LaplacianSignless LaplacianSignlessKernel

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The two kernels, compared -/

/-- **`Q`'s KERNEL IS NEVER BIGGER THAN `L`'s**: its index set is a subtype of the other's. -/
theorem finrank_ker_signlessLap_le_lap :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G)))
      ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ))) := by
  classical
  rw [← card_bipartiteComponent_eq_finrank_ker G,
    ← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  exact Fintype.card_subtype_le _

/-- **AND THEY ARE EQUAL EXACTLY WHEN `G` IS TWO-COLOURABLE.** -/
theorem finrank_ker_eq_iff_colorable :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G)))
        = Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ)))
      ↔ G.Colorable 2 := by
  classical
  rw [← card_bipartiteComponent_eq_finrank_ker G,
    ← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix,
    SimpleGraph.colorable_iff_forall_connectedComponents]
  constructor
  · intro hcard C
    by_contra hC
    exact absurd hcard (Fintype.card_subtype_lt (x := C) hC).ne
  · intro hall
    exact Fintype.card_congr (Equiv.subtypeUnivEquiv hall)

/-! ## 2. So the hypothesis of the transfer is exactly right -/

/-- **THE TWO OPERATORS HAVE THE SAME MULTIPLICITY EVERYWHERE EXACTLY WHEN `G` IS TWO-COLOURABLE**,
and `μ = 0` already decides it. -/
theorem colorable_two_iff_forall_finrank_eq :
    G.Colorable 2 ↔ ∀ μ : ℝ,
      Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
        = Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) := by
  constructor
  · intro hcol μ
    exact SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable hcol μ
  · intro h
    refine (finrank_ker_eq_iff_colorable G).1 ?_
    have e1 : (Matrix.toLin' (signlessLap G) - (0 : ℝ) • LinearMap.id)
        = Matrix.toLin' (signlessLap G) := by simp
    have e2 : (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id)
        = Matrix.toLin' (G.lapMatrix ℝ) := by simp
    have h0 := h 0
    rwa [e1, e2] at h0

/-! ## 3. The witness, and where it fails -/

/-- On an odd cycle `Q`'s kernel is trivial: the graph is connected and not two-colourable, so it
has no two-colourable component at all. -/
theorem finrank_ker_signlessLap_odd_cycle (M : ℕ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        (signlessLap (SimpleGraph.cycleGraph (2 * M + 3))))) = 0 :=
  (finrank_ker_eq_zero_iff_posDef _).2
    (LaplacianSignlessDefinite.odd_cycle_signlessLap_posDef M)

/-- **AND `L`'s IS A LINE**, the cycle being connected — so the two dimensions are `1` and `0`, and
the separation is as wide as it can be at a single value. -/
theorem finrank_ker_lapMatrix_odd_cycle (M : ℕ) :
    Module.finrank ℝ (LinearMap.ker (Matrix.toLin'
        ((SimpleGraph.cycleGraph (2 * M + 3)).lapMatrix ℝ))) = 1 := by
  classical
  rw [← SimpleGraph.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix]
  have hsub : Subsingleton (SimpleGraph.cycleGraph (2 * M + 3)).ConnectedComponent :=
    SimpleGraph.cycleGraph_preconnected.subsingleton_connectedComponent
  have hne : Nonempty (SimpleGraph.cycleGraph (2 * M + 3)).ConnectedComponent :=
    ⟨(SimpleGraph.cycleGraph (2 * M + 3)).connectedComponentMk ⟨0, by omega⟩⟩
  have : Unique (SimpleGraph.cycleGraph (2 * M + 3)).ConnectedComponent :=
    uniqueOfSubsingleton (Classical.arbitrary _)
  exact Fintype.card_unique

/-- **THE HYPOTHESIS IS NOT DECORATION**: on an odd cycle the multiplicities differ. -/
theorem not_forall_finrank_eq_odd_cycle (M : ℕ) :
    ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap (SimpleGraph.cycleGraph (2 * M + 3)))
          - μ • LinearMap.id))
      = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' ((SimpleGraph.cycleGraph (2 * M + 3)).lapMatrix ℝ)
            - μ • LinearMap.id)) :=
  fun h => CycleNormFromColouring.odd_cycle_not_colorable M
    ((colorable_two_iff_forall_finrank_eq _).2 h)

end SignlessColourableNecessary
