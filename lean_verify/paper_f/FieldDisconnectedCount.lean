import FieldRotationCount
import FieldRotationInstance
import FieldSimpleConnected

/-!
# Counting the symmetries of a disconnected graph, and the graph that OS2 already refuted

`FieldRotationInstance` proved that **every disconnected graph carries a genuine rotation** of its
Gaussian field, and fenced the obvious next question under **"No count of the rotations."** That
fence carries a supersession annotation, added 2026-09-05, saying `rotMatrix_inj` compares the
rotations "and `infinite_symmetryMatrices_of_orthogonal_eigenpair` counts them as infinite."

**The composition it describes was never performed.** As of 2026-09-06 this estate has six
`infinite_symmetryMatrices` theorems and they split cleanly. **Three name a graph** — `_box`,
`_torus`, `_twinGraph` — and **all three name a connected one**. **Three are general**, taking
any graph at all: `_of_orthogonal_eigenpair`, `_of_independent_eigenpair`, `_of_twin_pairs`.
**So no disconnected graph had ever been shown to supply the input of the general three, and the
named three do not include one.** The general counting theorem existed and the general eigenpair
existed; nothing joined them. The annotation named a target it did not hit (`ERRATUM 470`), and
**it is discharged here by proving it, not by rewording it.**

## What is proved

**`not_smul_of_orthogonal`** — two orthogonal vectors of non-zero square length are independent.
Three lines, and it is the missing joint: `exists_orthogonal_eigenpair_of_not_reachable` delivers
orthogonality, `infinite_symmetryMatrices_of_independent_eigenpair` wants independence, and no
lemma in this estate turned one into the other.

**`infinite_symmetryMatrices_of_not_reachable`** — **EVERY DISCONNECTED GRAPH HAS INFINITELY
MANY FIELD SYMMETRIES**, at `m ≠ 0`, and they are symmetries of the *measure* and not merely of
matrices, by `FieldRotationCount.gaussianField_map_of_mem`. **It does not supersede
`exists_rotation_symmetry_of_not_reachable` and is not claimed to**: that theorem produces an
explicit measure-preserving isometry with `R ≠ 1`, one per `(c, s)`, and compares none of them;
this counts the set and exhibits nothing. **Neither is stated as following from the other
here**, and no such implication is proved (`ERRATUM 246`).

**`infinite_symmetryMatrices_of_not_reachable_via_rescaling`** — **the same count by the route the
annotation itself named**, and the machine check on `ERRATUM 470`. It composes three existing
theorems and needs nothing that did not exist on 2026-09-05. **It is kept precisely so the erratum's
claim is checked rather than asserted**: the two routes prove the same statement, and the second one
was available for a day and was not written.

**`stepGraph_not_preconnected`, `stepGraph_infinite_symmetryMatrices`,
`stepGraph_exists_rotation_symmetry`, `stepGraph_exists_new_symmetry`,
`stepGraph_not_eigenvalues_injective`, `stepGraph_not_finrank_le_one`** — **and the whole tower is
instantiated on a named graph for the first time.** As of 2026-09-06 the three symmetry-side
consumers of `¬ Reachable` — `FieldComponentEigen.exists_orthogonal_eigenpair_of_not_reachable`,
`FieldRotationInstance.exists_rotation_symmetry_of_not_reachable` and
`FieldSignFlip.exists_new_symmetry_of_not_reachable` — had **never been applied to any concrete
graph**: every mention of each in this estate is its own statement, a header cross-reference, or a
relay from one general theorem to another. The Green-function consumers were instantiated
(`GreenDisconnected.stepGraph_green_three_zero`); the symmetry ones were not.

**`stepGraph_os2_degenerate_and_symmetry_infinite`** — and the graph they are instantiated on is
**the estate's own OS2 counterexample**. `GreenDisconnected.stepGraph_os2_not_strict` shows OS2's
inequality on `stepGraph` is exactly `0 ≤ 0`; the same graph has an infinite symmetry set. Stated as
one theorem so the two facts are visibly about one object.

## What is NOT here

**NO IMPLICATION BETWEEN THE TWO HALVES IS PROVED.**
`stepGraph_os2_degenerate_and_symmetry_infinite` is a conjunction, and **nothing here says a
degenerate OS2 forces an infinite symmetry set, or the reverse.** Both halves are consequences
of disconnection, which is a common cause and not a proof of either direction. **The conjunction
is an exhibition, not a theorem about the relationship.** Not attempted, no cost claimed
(`ERRATUM 246`).

**NO CARDINALITY.** `Set.Infinite` is not `Nat.card` and not a description of the group. What the
symmetry set of a disconnected graph *is* remains open, exactly as `FieldRotationInstance` says.

**NOTHING ON A CONNECTED GRAPH**, which is the case the OS programme is about. The eigenvalue this
construction uses is `(m²)⁻¹`, whose eigenspace on a connected graph is a line. Untouched.

**NO WALL MOVES.** This does not repair OS2 and does not bear on `W1`'s open part, which is `OS0`
and `OS4`, and `OS1` in its continuum sense. It is a statement about a graph the estate keeps as a
*counterexample*, and closing off a counterexample's properties is not progress on the axiom.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `not_smul_of_orthogonal` takes **no mass,
no graph and no eigenvalue** — it is linear algebra and holds for any two vectors. Every other
theorem here takes `m ≠ 0`, and that is part of the claim rather than boilerplate: at `m = 0` the
Gaussian field is a point mass and every isometry preserves it, on every graph
(`FieldMassNecessity`). `stepGraph_not_preconnected` and `stepGraph_not_finrank_le_one` take **no
mass either** — they are statements about the graph and its Laplacian.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldDisconnectedCount

open Matrix GraphLaplacian FieldRotationCount

/-! ## 1. The missing joint: orthogonal and non-null implies independent -/

/-- **TWO ORTHOGONAL VECTORS OF NON-ZERO SQUARE LENGTH ARE INDEPENDENT.** If `v = c • u` then
orthogonality forces `c * (u ⬝ᵥ u) = 0`, hence `c = 0`, hence `v = 0`. -/
theorem not_smul_of_orthogonal {V : Type*} [Fintype V] {u v : V → ℝ} (huu : u ⬝ᵥ u ≠ 0)
    (hvv : v ⬝ᵥ v ≠ 0) (huv : u ⬝ᵥ v = 0) : ∀ c : ℝ, v ≠ c • u := by
  intro c hc
  have hcu : c * (u ⬝ᵥ u) = 0 := by
    rw [hc, dotProduct_smul, smul_eq_mul] at huv
    exact huv
  have hc0 : c = 0 := (mul_eq_zero.mp hcu).resolve_right huu
  exact hvv (by simp [hc, hc0])

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 2. So every disconnected graph has infinitely many field symmetries -/

/-- **EVERY DISCONNECTED GRAPH HAS INFINITELY MANY FIELD SYMMETRIES.** The count that
`FieldRotationInstance`'s fence said was had and that nothing performed. -/
theorem infinite_symmetryMatrices_of_not_reachable (hm : m ≠ 0) {p q : V}
    (hpq : ¬ G.Reachable p q) : (symmetryMatrices G m).Infinite := by
  obtain ⟨u, v, hu0, hv0, huv, hu, hv⟩ :=
    FieldComponentEigen.exists_orthogonal_eigenpair_of_not_reachable (G := G) hm hpq
  exact infinite_symmetryMatrices_of_independent_eigenpair hm hu0
    (not_smul_of_orthogonal hu0 hv0 huv) hu hv

/-- **THE SAME COUNT BY THE ROUTE THE ANNOTATION ITSELF NAMED**, and the machine check on
`ERRATUM 470`'s factual claim. `FieldRotationInstance.exists_equal_length_eigenpair` takes exactly
what `exists_orthogonal_eigenpair_of_not_reachable` returns and returns exactly what
`infinite_symmetryMatrices_of_orthogonal_eigenpair` wants, so **this composition was available on
2026-09-05, needs no lemma that did not exist then, and was never written.** -/
theorem infinite_symmetryMatrices_of_not_reachable_via_rescaling (hm : m ≠ 0) {p q : V}
    (hpq : ¬ G.Reachable p q) : (symmetryMatrices G m).Infinite := by
  obtain ⟨u, v, hu0, hv0, huv, hu, hv⟩ :=
    FieldComponentEigen.exists_orthogonal_eigenpair_of_not_reachable (G := G) hm hpq
  obtain ⟨u', v', n, hn, hu'u', hv'v', hu'v', hu', hv'⟩ :=
    FieldRotationInstance.exists_equal_length_eigenpair (G := G) hu0 hv0 huv hu hv
  exact infinite_symmetryMatrices_of_orthogonal_eigenpair hm hn hu'u' hv'v' hu'v' hu' hv'

/-! ## 3. And the tower lands on a named graph: the estate's own OS2 counterexample -/

/-- `stepGraph` is two three-vertex paths, so it is not preconnected. -/
theorem stepGraph_not_preconnected : ¬ GreenLargeMass.stepGraph.Preconnected :=
  fun h => GreenDisconnected.stepGraph_not_reachable_three_zero (h 3 0)

/-- **THE FIELD ON `stepGraph` HAS INFINITELY MANY SYMMETRIES.** -/
theorem stepGraph_infinite_symmetryMatrices {mass : ℝ} (hmass : mass ≠ 0) :
    (symmetryMatrices GreenLargeMass.stepGraph mass).Infinite :=
  infinite_symmetryMatrices_of_not_reachable hmass
    GreenDisconnected.stepGraph_not_reachable_three_zero

/-- **AND A GENUINE ROTATION**, one for each point of the unit circle off the axis. -/
theorem stepGraph_exists_rotation_symmetry {mass : ℝ} (hmass : mass ≠ 0) {c s : ℝ}
    (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    ∃ (R : Matrix (Fin 6) (Fin 6) ℝ) (h : Rᵀ * R = 1), R ≠ 1 ∧
      MeasureTheory.Measure.map (FieldOrthIsometry.orthIsometry h)
          (gaussianField GreenLargeMass.stepGraph mass)
        = gaussianField GreenLargeMass.stepGraph mass :=
  FieldRotationInstance.exists_rotation_symmetry_of_not_reachable hmass
    GreenDisconnected.stepGraph_not_reachable_three_zero hcs hs

/-- **AND A SIGN FLIP ON A PROPER NON-EMPTY SET**, which a connected graph does not have. -/
theorem stepGraph_exists_new_symmetry {mass : ℝ} (hmass : mass ≠ 0) :
    ∃ s : Finset (Fin 6), FieldSignFlip.IsComponentClosed GreenLargeMass.stepGraph s ∧
      s.Nonempty ∧ s ≠ Finset.univ ∧
      (gaussianField GreenLargeMass.stepGraph mass).map (FieldSignFlip.signFlip s)
        = gaussianField GreenLargeMass.stepGraph mass :=
  FieldSignFlip.exists_new_symmetry_of_not_reachable hmass
    GreenDisconnected.stepGraph_not_reachable_three_zero

/-- **AND ITS PROPAGATOR SPECTRUM IS DEGENERATE**, by the connectivity criterion. -/
theorem stepGraph_not_eigenvalues_injective {mass : ℝ} (hmass : mass ≠ 0)
    (hH : (green GreenLargeMass.stepGraph mass).IsHermitian) :
    ¬ Function.Injective hH.eigenvalues :=
  FieldSimpleConnected.not_eigenvalues_injective_of_not_preconnected hmass hH
    stepGraph_not_preconnected

/-- **AND ITS LAPLACIAN HAS AN EIGENSPACE THAT IS NOT A LINE**, with no mass anywhere. -/
theorem stepGraph_not_finrank_le_one :
    ¬ (∀ ν : ℝ, Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((GreenLargeMass.stepGraph).lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :=
  fun hdim => stepGraph_not_preconnected
    (FieldSimpleConnected.preconnected_of_finrank_le_one hdim)

/-! ## 4. The two facts about one graph -/

/-- **THE GRAPH ON WHICH OS2 DEGENERATES HAS AN INFINITE SYMMETRY SET.** Stated as a conjunction
because that is what is proved: **no implication between the halves is claimed in either
direction**, and both follow from disconnection. -/
theorem stepGraph_os2_degenerate_and_symmetry_infinite {mass : ℝ} (hmass : mass ≠ 0) :
    (¬ (0 < ∫ ω, (∑ r, (if r = (0 : Fin 6) then (1 : ℝ) else 0) * ω (GreenLargeMass.sigma6 r))
              * (∑ q, (if q = (0 : Fin 6) then (1 : ℝ) else 0) * ω q)
          ∂(gaussianField GreenLargeMass.stepGraph mass)))
      ∧ (symmetryMatrices GreenLargeMass.stepGraph mass).Infinite :=
  ⟨GreenDisconnected.stepGraph_os2_not_strict hmass, stepGraph_infinite_symmetryMatrices hmass⟩

end FieldDisconnectedCount
