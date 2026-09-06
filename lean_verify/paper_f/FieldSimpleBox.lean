import FieldSimpleConnected
import FieldBoxRotation

/-!
# The box in dimension two or more fails it too, so the line is the only lattice left

`FieldSimpleConnected` showed the symmetry chain's hypothesis fails on every **periodic** lattice
of dimension at least one, and left the corresponding claim about **boxes** where the watchlist had
it: as prose. *"A box in `d ≥ 2` does not [have a simple spectrum], by `FieldRotationCount`"* was an
assertion in an `UNLOCK_WATCHLIST` block, checked by nobody. It is a theorem here.

## What is proved

**`twoFreq`, `twoFreq_ne`** — the frequency whose first coordinate is `0` and whose others are `1`,
and that its first two coordinates differ. This needs **dimension at least two** and **side at
least two**, which is why every statement below is stated at `d + 2` and `m + 2`.

**`not_finrank_massive_le_one_box`** — so the box fails the hypothesis, by
`FieldBoxRotation.two_le_finrank_eigenspace_box`: a frequency with two different coordinates shares
its eigenvalue with its swap, so that eigenspace has dimension at least two. At **every** mass.

**`not_finrank_lapMatrix_le_one_box`** — and in the graph-only form, at no mass at all
(`FieldLaplacianSimple.ker_massive_eq` at `m = 0`, the same one-line step as in
`FieldLaplacianInstance` and `FieldSimpleConnected`).

**`box_connected`, `not_eigenvalues_injective_box`** — **so the box in dimension two or more is a
connected graph whose propagator spectrum is degenerate**, at every non-zero mass: the second such
family, beside the periodic lattices.

**WHAT THE THREE FILES TOGETHER SAY, AND IT IS WORTH SAYING ONCE.** The chain's hypothesis holds on
`boxGraph 1 (m+1)` — the path — and fails on every periodic lattice in every dimension and on every
box in dimension two or more. **The line is the only lattice this estate has left on the satisfying
side.**

## What is NOT here

**THE DICHOTOMY FOR BOXES IS NOT STATED AS ONE.** The failing side is proved for `d ≥ 2` and side
`≥ 2`; the satisfying side at `d = 1` is `FieldSimpleCriterion.finrank_le_one_line` and at side `1`
is a one-vertex graph, and **neither is restated here, nor are the three assembled into a
biconditional**. Doing so is bookkeeping and is not done in this file, which is a choice and not
an oversight.

**ONLY A LOWER BOUND IS USED, AND THE ESTATE HAS MORE THAN THAT.**
`two_le_finrank_eigenspace_box` gives two, and this file uses nothing else. That is a choice, not a
limit: `BoxEigenspaceDimension.finrank_eigenspace_massive_box` computes the multiplicity
**exactly**, as `Nat.card` of the fibre of the frequency map over the eigenvalue — checked before
this sentence was written (`ERRATUM 450`), because the sentence first drafted here said no exact
multiplicity existed and that was false. What the estate does **not** have is that cardinality as a
closed-form number, which is the same remainder `NullSpaceCodimension` records.

**NOTHING NEW ABOUT THE EIGENSPACE.** The whole content is `FieldBoxRotation`'s, from 2026-09-05.
What is new is the **direction** — turning a two-dimensional eigenspace into *the propagator's
spectrum is degenerate* is the contrapositive of
`FieldSimpleConverse.finrank_massive_le_one_of_eigenvalues_injective`, which is hours old. This is
the third time that step has been taken and the third family it has been taken on.

**NO CHARACTERISATION.** Ruling out lattices is not describing what remains. Every graph that is
neither a lattice nor edgeless nor disconnected is untouched, and **no claim is made that the
failing families found so far have anything in common** — `FieldInvolutionConverse` already showed
the obvious candidate for a common cause, *an automorphism of order three or more*, is not one.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): **one of the six** takes a non-zero mass,
`not_eigenvalues_injective_box`, and only because `green` is defined as an inverse.
`not_finrank_massive_le_one_box` takes the mass as a **free variable it never constrains**, which is
what lets `ker_massive_eq` be applied at `m = 0`; `twoFreq`, `twoFreq_ne`,
`not_finrank_lapMatrix_le_one_box` and `box_connected` take no mass at all. `d ≥ 2` and side `≥ 2`
are carried structurally, as `d + 2` and `m + 2`, by everything except `box_connected`, which holds
at every dimension.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSimpleBox

open Matrix GraphLaplacian BoxGraph BoxLapSpectrum FieldBoxRotation

/-! ## 1. A frequency with two different coordinates -/

def twoFreq (d m : ℕ) : Site (d + 2) (m + 2) := fun a => ⟨min a.val 1, by omega⟩

theorem twoFreq_ne (d m : ℕ) : twoFreq d m 0 ≠ twoFreq d m 1 := by
  simp [twoFreq]

/-! ## 2. So the box in dimension at least two fails the hypothesis -/

theorem not_finrank_massive_le_one_box (d m : ℕ) (mass : ℝ) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (massive (boxGraph (d + 2) (m + 2)) mass) - ν • LinearMap.id)) ≤ 1) := by
  intro hdim
  have h2 : 2 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' (massive (boxGraph (d + 2) (m + 2)) mass)
        - (boxLapEig (d + 2) (m + 2) (fun a => (twoFreq d m a).val) + mass ^ 2)
            • LinearMap.id)) :=
    two_le_finrank_eigenspace_box (d + 2) (m + 1) mass (twoFreq d m) (twoFreq_ne d m)
  have h1 := hdim (boxLapEig (d + 2) (m + 2) (fun a => (twoFreq d m a).val) + mass ^ 2)
  omega

theorem not_finrank_lapMatrix_le_one_box (d m : ℕ) :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph (d + 2) (m + 2)).lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) := by
  intro hdim
  refine not_finrank_massive_le_one_box d m 0 fun ν => ?_
  rw [FieldLaplacianSimple.ker_massive_eq]
  exact hdim _

theorem box_connected (d m : ℕ) : (boxGraph (d + 2) (m + 2)).Connected :=
  boxGraph_connected (n := m + 2) (d + 2) (by omega)

/-- **SO THE BOX IN DIMENSION AT LEAST TWO IS A CONNECTED GRAPH WHOSE PROPAGATOR SPECTRUM IS
DEGENERATE**, at every non-zero mass — the second family of that kind, beside the periodic
lattices of `FieldSimpleConnected`. -/
theorem not_eigenvalues_injective_box (d m : ℕ) {mass : ℝ} (hmass : mass ≠ 0)
    (hH : (green (boxGraph (d + 2) (m + 2)) mass).IsHermitian) :
    ¬ Function.Injective hH.eigenvalues :=
  fun hsimple => not_finrank_massive_le_one_box d m mass
    (FieldSimpleConverse.finrank_massive_le_one_of_eigenvalues_injective hmass hH hsimple)

end FieldSimpleBox
