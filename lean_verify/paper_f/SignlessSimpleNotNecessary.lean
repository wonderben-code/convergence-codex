import PawSignlessSpectrum
import SignlessColourableNecessary
import SignlessSimpleFamilies

/-!
# Two-colourability is necessary for one transfer and not for the other, and the paw says so

Two files of this chain fence the same hypothesis as *not shown necessary*, in almost the same
words, and **the two sentences are about different theorems and have different answers**. This file
separates them, and every ingredient was already in the estate.

## The two transfers, and why they are not the same statement

`SignlessConjugateMultiplicity.finrank_eigenspace_signlessLap_eq_lap_of_colorable` says a
two-colourable graph has `Q` and `L` with the **same multiplicity at every real `μ`**.
`SignlessSimpleFamilies.finrank_signless_le_one_iff_lap_of_colorable` says a two-colourable graph
has `Q` simple **iff** `L` is. The first is an equality of two functions of `μ`; the second is an
equivalence of two *properties*, and a graph can satisfy the second without coming near the first —
`1 ≤ 1` on both sides says nothing about the two numbers being equal.

**FOR THE FIRST, THE HYPOTHESIS IS EXACTLY RIGHT AND THE ESTATE ALREADY KNEW IT.**
`SignlessColourableNecessary.colorable_two_iff_forall_finrank_eq` is a biconditional: the
multiplicities agree everywhere **exactly when** `G` is two-colourable.

**FOR THE SECOND, THE HYPOTHESIS IS STRICTLY SUFFICIENT, AND THIS FILE PROVES IT.**

## What is proved

**`simple_transfer_paw`** — on the paw, `Q` simple ↔ `L` simple, with no colouring hypothesis:
both sides are unconditionally true (`PawSignlessSpectrum.finrank_signless_le_one_paw`,
`PawSimpleSpectrum.finrank_lapMatrix_le_one_paw`), so the equivalence holds for the dullest of
reasons — and the dullest of reasons is enough, because what is at issue is the hypothesis.

**`simple_transfer_hypothesis_not_necessary`** — **THE FILE'S THEOREM.** There is a graph that is
**not** two-colourable on which the simplicity transfer holds. So that theorem's colouring
hypothesis cannot be dropped-and-recovered: it is a genuine sufficient condition and not a
disguised characterisation.

**`the_two_hypotheses_come_apart`** — the pair, as one statement: two-colourability is
**equivalent** to multiplicity-transfer and **strictly stronger** than simplicity-transfer.

## What is NOT here

* **NO CHARACTERISATION OF SIMPLICITY-TRANSFER.** Which graphs have `Q` simple iff `L` simple is
  **not** determined, and one non-two-colourable witness is not a class (`ERRATUM 246`). What is
  settled is only that two-colourability is not the answer.
* **NO GRAPH WHERE SIMPLICITY-TRANSFER FAILS.** Both files' fences ask for one — a graph with `Q`
  simple and `L` not, or the reverse — and **the paw is not it**, being simple on both sides. That
  question is untouched here and stays open exactly where those files leave it.
* **NOTHING COMPUTED.** Every ingredient is a citation: the paw's two spectra, its
  non-two-colourability, and the biconditional of `SignlessColourableNecessary`. This file is four
  compositions and a contrast.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): none beyond the paw's own type. The
contrast theorem quantifies over a graph with the estate's usual finiteness and decidability.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessSimpleNotNecessary

open Matrix SimpleGraph LaplacianSignless PawSimpleSpectrum PawSignlessSpectrum

/-! ## 1. The paw transfers simplicity, and is not two-colourable -/

/-- On the paw both operators are simple, so the transfer holds with nothing assumed. -/
theorem simple_transfer_paw :
    (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (signlessLap pawGraph) - μ • LinearMap.id)) ≤ 1)
      ↔ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (pawGraph.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1) :=
  ⟨fun _ => finrank_lapMatrix_le_one_paw, fun _ => finrank_signless_le_one_paw⟩

/-- **THE FILE'S THEOREM.** The simplicity transfer's colouring hypothesis is **not necessary**. -/
theorem simple_transfer_hypothesis_not_necessary :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      ¬ G.Colorable 2 ∧
      ((∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (signlessLap G) - μ • LinearMap.id)) ≤ 1)
        ↔ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
          (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1)) :=
  ⟨Fin 4, inferInstance, inferInstance, pawGraph, inferInstance,
    not_colorable_two_paw, simple_transfer_paw⟩

/-! ## 2. So the two hypotheses come apart -/

section Contrast
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **THE CONTRAST, AS ONE STATEMENT.** Two-colourability is **equivalent** to the multiplicities
agreeing at every `μ`, and **strictly stronger** than the two simplicities agreeing — the paw
being two-colourable's counterexample and simplicity-transfer's witness at once. -/
theorem the_two_hypotheses_come_apart :
    (G.Colorable 2 ↔ ∀ μ : ℝ,
        Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (signlessLap G) - μ • LinearMap.id))
          = Module.finrank ℝ (LinearMap.ker
              (Matrix.toLin' (G.lapMatrix ℝ) - μ • LinearMap.id)))
      ∧ ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (H : SimpleGraph W)
          (_ : DecidableRel H.Adj),
          ¬ H.Colorable 2 ∧
          ((∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
              (Matrix.toLin' (signlessLap H) - μ • LinearMap.id)) ≤ 1)
            ↔ (∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
              (Matrix.toLin' (H.lapMatrix ℝ) - μ • LinearMap.id)) ≤ 1)) :=
  ⟨SignlessColourableNecessary.colorable_two_iff_forall_finrank_eq G,
    simple_transfer_hypothesis_not_necessary⟩

end Contrast

end SignlessSimpleNotNecessary
