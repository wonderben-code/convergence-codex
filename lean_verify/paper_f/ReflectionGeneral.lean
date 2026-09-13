/-
  ReflectionGeneral.lean — the previous unit's witness was one instance of a
  theorem the estate already had, and this is the general statement.

  WHY THIS FILE EXISTS, AND IT IS A CORRECTION. `ReflectionNotColorable` proved
  that `SpectrumReflection`'s symmetry fails on the odd cycle, and its header said:

    > **WHAT IS NOT CLAIMED.** The general statement just described is not proved
    > here … turning *"`2Δ + m²` is not attained"* into *"the eigenspace at `2Δ`
    > is trivial"* needs a step this file does not take for general graphs.

  The first sentence is true of that file. **The clause after it is misleading,
  because the step IS taken, elsewhere and before either file existed**:
  `LaplacianTopEigenspace.finrank_top_eigenspace_eq_zero` says exactly that a
  connected regular graph that is not two-colourable has a trivial eigenspace at
  `2Δ`. Written up as `ERRATUM 542`, and the sentence is annotated in place.

  **The discipline that caught it is worth more than the theorem.** That unit's §6
  named this successor and said it *"should be checked before it is promised"*, and
  refused to predict whether the step would be cheap — `ERRATUM 541`'s rule, kept.
  The check took one grep. The step is not cheap; it is free.

  WHAT THIS FILE PROVES.

  1. `finrank_lap_top_eq_zero` — the sign bridge: `LaplacianTopEigenspace` states
     the vanishing at `ker(2Δ·1 − L)` and the reflection statements want
     `ker(L − 2Δ·id)`. Two applications of
     `SignlessRegularSimple.ker_signless_eq_ker_lap_of_regular` at `μ = 0` and
     `LaplacianTopEigenspace.signlessLap_eq_of_regular` join them.
  2. **`reflection_fails_of_not_colorable`** — the reflection `μ ↦ 2Δ − μ` fails on
     **every** connected regular non-two-colourable graph, not only the odd cycle:
     `mult_L(0) = 1` and `mult_L(2Δ) = 0`.
  3. **`colorable_not_removable_general`** — so two-colourability is necessary in
     `SpectrumReflection.finrank_lap_reflect_of_regular_colorable` for the whole
     class, and `ReflectionNotColorable.colorable_not_removable` is its instance at
     the odd cycle.
  4. `top_eigenspace_dichotomy` — and on a connected regular graph the eigenspace at
     `2Δ` is a line or is trivial according to two-colourability, with nothing in
     between. Both halves are `LaplacianTopEigenspace`'s; this states them together
     in the `ker(L − 2Δ·id)` spelling the reflection work uses.

  WHAT THIS DOES NOT DO. It does not supersede `ReflectionNotColorable`. That file's
  odd-cycle route goes through the fibre count and is independent of
  `LaplacianTopEigenspace`'s component argument; two independent proofs of one
  instance is not a defect, and the instance is cited in §3 rather than deleted.
  **What was wrong was a sentence, not a theorem**, and the repair is this file plus
  a dated annotation, not a retraction.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import ReflectionNotColorable
import LaplacianTopEigenspace

namespace ReflectionGeneral

open Matrix SimpleGraph GraphLaplacian LaplacianSignless

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## 1. The sign bridge -/

/-- `LaplacianTopEigenspace` works at `2Δ·1 − L`; the reflection statements work at
`L − 2Δ·id`. The two kernels agree, through the signless Laplacian at `μ = 0`. -/
theorem ker_lap_top_eq {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ) :
    LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ)) • LinearMap.id)
      = LinearMap.ker (Matrix.toLin' ((2 * (Δ : ℝ)) • (1 : Matrix V V ℝ) - G.lapMatrix ℝ)) := by
  have h0 := SignlessRegularSimple.ker_signless_eq_ker_lap_of_regular (G := G) hreg 0
  rw [zero_smul, sub_zero, sub_zero] at h0
  rw [← h0, LaplacianTopEigenspace.signlessLap_eq_of_regular G hreg]

/-- **THE TOP OF THE RANGE IS NOT AN EIGENVALUE OF A NON-BIPARTITE REGULAR GRAPH.**
`LaplacianTopEigenspace.finrank_top_eigenspace_eq_zero` in the spelling the
reflection work uses. -/
theorem finrank_lap_top_eq_zero {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (hcol : ¬ G.Colorable 2) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ)) • LinearMap.id)) = 0 := by
  rw [ker_lap_top_eq hreg]
  exact LaplacianTopEigenspace.finrank_top_eigenspace_eq_zero G hreg hG hcol

/-- And it IS an eigenvalue, simply, when the graph is two-colourable. -/
theorem finrank_lap_top_eq_one [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (hcol : G.Colorable 2) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ)) • LinearMap.id)) = 1 := by
  rw [ker_lap_top_eq hreg]
  exact LaplacianTopEigenspace.finrank_top_eigenspace_eq_one G hreg hG hcol

/-- **THE DICHOTOMY.** On a connected regular graph the eigenspace at `2Δ` is a line
or is trivial, according to two-colourability, with nothing in between. Both halves
are `LaplacianTopEigenspace`'s; the value of stating them together is that the
reflection in §2 needs exactly this and nothing more. -/
theorem top_eigenspace_dichotomy [Nonempty V] {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) :
    (G.Colorable 2 → Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ)) • LinearMap.id)) = 1)
      ∧ (¬ G.Colorable 2 → Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ)) • LinearMap.id)) = 0) :=
  ⟨finrank_lap_top_eq_one hreg hG, finrank_lap_top_eq_zero hreg hG⟩

/-! ## 2. So the reflection fails on the whole class -/

/-- **THE REFLECTION FAILS ON EVERY CONNECTED REGULAR NON-BIPARTITE GRAPH.**
`mult_L(0) = 1` because the graph is connected; `mult_L(2Δ − 0) = 0` by §1. The odd
cycle was one instance of this and `ReflectionNotColorable` proved it by a different
route. -/
theorem reflection_fails_of_not_colorable {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (hcol : ¬ G.Colorable 2) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      ≠ Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ) - 0) • LinearMap.id)) := by
  -- `finrank_ker_lapMatrix_zero_connected` already carries `- (0 : ℝ) • LinearMap.id`.
  -- Normalising it away with `zero_smul` first makes the `exact` unify the two spellings,
  -- and THAT is what loops -- not any decidability instance. See `ERRATUM 543`.
  have h0 : Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (0 : ℝ) • LinearMap.id)) = 1 :=
    FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected hG
  have h1 : Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ) - 0) • LinearMap.id)) = 0 := by
    rw [sub_zero]
    exact finrank_lap_top_eq_zero hreg hG hcol
  rw [h0, h1]
  exact one_ne_zero

/-- **SO TWO-COLOURABILITY IS NECESSARY IN
`SpectrumReflection.finrank_lap_reflect_of_regular_colorable` FOR THE WHOLE CLASS**,
not only at the odd cycle. -/
theorem colorable_not_removable_general {Δ : ℕ} (hreg : G.IsRegularOfDegree Δ)
    (hG : G.Connected) (hcol : ¬ G.Colorable 2) :
    ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id))
        = Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.lapMatrix ℝ) - (2 * (Δ : ℝ) - μ) • LinearMap.id)) :=
  fun h => reflection_fails_of_not_colorable hreg hG hcol (h 0)

/-! ## 3. Review round 66 — the ways this could be hollow

**"This could be `LaplacianTopEigenspace` restated."** §1 is, and says so: the only
work there is the sign bridge, and it is three lines. §2 is not — the reflection
statement is about a symmetry of one spectrum and does not appear in that file, and
the point of proving it is that `SpectrumReflection` asserted a pairing of
hypotheses that was justified on only one side.

**"It could supersede `ReflectionNotColorable` and quietly not say so."** It does
not supersede it and §3's docstrings say why: that file's odd-cycle route runs
through the fibre count and is independent of the component argument used here. Two
independent proofs of one instance is not a defect. What that file got wrong was a
SENTENCE — *"needs a step this file does not take for general graphs"*, which reads
as though no file takes it — and that sentence is annotated in place, not deleted
(`ERRATUM 542`, `ERRATUM 94`).

**"The dichotomy might be vacuous on one side."** Neither side: the even cycle is
connected, regular and two-colourable, and the odd cycle is connected, regular and
not. Both are in the estate with their regularity proved
(`SignlessRegularSimple.torusGraph_one_isRegular`).

**"§2 might need more than connectivity at `μ = 0`."** It does not —
`FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected` is exactly the
component count at one component. **AND THE FIRST DRAFT OF THIS PARAGRAPH WAS
WRONG, WHICH IS HOW `ERRATUM 543` WAS FOUND.** It said the previous unit's timeout
*"does not recur here because the graph is a variable rather than a named
construction"*. It recurred immediately, on a variable graph, at two million
heartbeats — refuting both the sentence and the open `DecidableRel timeout` item
it cited. **The real cause is a shape mismatch and has nothing to do with
decidability**: `finrank_ker_lapMatrix_zero_connected`'s statement already carries
`- (0 : ℝ) • LinearMap.id`, and normalising the goal with `rw [zero_smul,
sub_zero]` before applying it makes the unifier prove `toLin' L - 0 • id` defeq
`toLin' L`, which does not terminate. Deleting the rewrite is the whole fix, in
this file and in the two units that blamed decidability. Both were re-tested and
both close in one line.
-/

end

end ReflectionGeneral
