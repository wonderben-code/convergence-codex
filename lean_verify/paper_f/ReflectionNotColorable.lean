/-
  ReflectionNotColorable.lean — the odd cycle, and the other half of
  `SpectrumReflection`'s justification.

  WHY THIS FILE EXISTS. `SpectrumReflection.finrank_lap_reflect_of_regular_colorable`
  needs a graph to be **regular** and **two-colourable**, and that file justified
  only the first hypothesis: the star is two-colourable, not regular, and the
  symmetry fails on it. Its own §6 recorded the gap rather than letting the pairing
  look complete — *"two-colourability is NOT shown necessary; a witness for the
  other direction has to be regular, non-bipartite, and spectrally asymmetric"* —
  and predicted the witness might be expensive, since the last such search cost an
  exhaustive pass over every connected graph on six vertices.

  **It is not expensive: the odd cycle is already built and already regular.** The
  file that would have been needed, `CycleSpectralBound.cos_ne_neg_one_of_odd`,
  exists too — found by the per-unit name check before a line was written, which is
  the check `ERRATUM 536` exists for and the discipline `ERRATUM 541` is about. This
  unit is small and is recorded as small.

  WHAT THIS FILE PROVES.

  1. `nuR_ne_four_odd` — on an odd cycle the Laplacian eigenvalue function never
     reaches `4 = 2Δ`, because that needs a cosine equal to `−1` and the parity
     argument forbids it.
  2. `finrank_lap_odd_cycle_four_eq_zero` — so the eigenspace there is `0`, through
     `TorusRealMultiplicity.finrank_eigenspace_massive_real`'s fibre count and
     `FieldMassNecessity.massive_zero`.
  3. `finrank_lap_odd_cycle_zero_eq_one` — and at `0` it is a line, the cycle being
     connected.
  4. **`reflection_fails_odd_cycle`**, **`colorable_not_removable`** — so the
     reflection `μ ↦ 2Δ − μ` fails on a REGULAR graph, and regularity alone does not
     give `SpectrumReflection`'s symmetry.
  5. **`both_hypotheses_needed`** — with `SpectrumReflection.regularity_not_removable`,
     neither hypothesis can be dropped. The pairing is now justified in both
     directions, which is what §6 of that file said it was not.

  **WHY THE ODD CYCLE AND NOT SOMETHING FOUND BY SEARCH.** The prediction that this
  would be hard came from thinking of the witness as a coincidence to be hunted. It
  is not a coincidence: `2Δ` is the top of the Laplacian's range and a non-bipartite
  graph never attains it — `LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable`
  says exactly that in Loewner form, for every connected regular graph. So EVERY
  connected regular non-bipartite graph is a witness and the odd cycle is merely the
  cheapest. **The estimate was wrong because it mistook a theorem for an accident**,
  and that is worth more than the theorem below.

  WHAT IS NOT CLAIMED. The general statement just described is not proved here.
  `massive_le_smul_one_iff_colorable` is a Loewner bound, not a multiplicity, and
  turning *"`2Δ + m²` is not attained"* into *"the eigenspace at `2Δ` is trivial"*
  needs a step this file does not take for general graphs — it takes it for the odd
  cycle, where the eigenvalue list is explicit. Not attempted, no cost claimed
  (`ERRATUM 246`).

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SpectrumReflection
import CycleSpectralBound
import TorusRealMultiplicity
import FieldMassNecessity
import LaplacianSharpEquality

namespace ReflectionNotColorable

open Matrix SimpleGraph GraphLaplacian BoxGraph TorusReflection
open MassiveTorusSpectrum TorusRealMultiplicity

noncomputable section

/-! ## 1. The top of the range is not reached -/

/-- On an odd cycle `νR` never equals `4`. Reaching it needs `cos(2πk/n) = −1`, and
`CycleSpectralBound.cos_ne_neg_one_of_odd` is the parity argument that forbids it —
already in the estate, found by the name check before this file was drafted. -/
theorem nuR_ne_four_odd (M : ℕ) (k : Site 1 (2 * M + 3)) :
    nuR (2 * M) (0 : ℝ) k ≠ 4 := by
  intro h
  rw [nuR, Fin.sum_univ_one] at h
  have hcast : ((2 * M : ℕ) : ℝ) + 3 = ((2 * M + 3 : ℕ) : ℝ) := by push_cast; ring
  have hcos : Real.cos (2 * Real.pi * ((k 0).val : ℝ) / ((2 * M + 3 : ℕ) : ℝ)) = -1 := by
    rw [← hcast]
    push_cast at h ⊢
    linarith
  exact CycleSpectralBound.cos_ne_neg_one_of_odd (N := 2 * M + 3) (k := (k 0).val)
    ⟨M + 1, by ring⟩ hcos

/-- **SO THE EIGENSPACE AT `2Δ = 4` IS TRIVIAL ON AN ODD CYCLE.** -/
theorem finrank_lap_odd_cycle_four_eq_zero (M : ℕ) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ)
        - (4 : ℝ) • LinearMap.id)) = 0 := by
  rw [← FieldMassNecessity.massive_zero (G := torusGraph 1 (2 * M + 3)),
    finrank_eigenspace_massive_real (2 * M) (0 : ℝ) (4 : ℝ)]
  haveI : IsEmpty {k : Site 1 (2 * M + 3) // nuR (2 * M) (0 : ℝ) k = 4} :=
    ⟨fun x => nuR_ne_four_odd M x.1 x.2⟩
  exact Nat.card_of_isEmpty

/-- And at `0` the eigenspace is a line — the ground state, at zero mass.
**NOT by connectivity**, though the cycle is connected and
`FieldSimpleConnected.finrank_ker_lapMatrix_zero_connected` says so: that route
timed out at `whnf` past a million heartbeats on the `torusGraph` decidability
instance. `TorusRealMultiplicity.ground_state_simple_real` is the same fact for
this family, already proved through the fibre count, and it costs nothing. -/
theorem finrank_lap_odd_cycle_zero_eq_one (M : ℕ) :
    Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ)
        - (0 : ℝ) • LinearMap.id)) = 1 := by
  rw [← FieldMassNecessity.massive_zero (G := torusGraph 1 (2 * M + 3))]
  have h := ground_state_simple_real (d := 1) (2 * M) (0 : ℝ)
  rwa [show ((0 : ℝ) ^ 2) = (0 : ℝ) from by norm_num] at h

/-! ## 2. So regularity alone does not give the symmetry -/

/-- **THE REFLECTION FAILS ON THE ODD CYCLE**, which is regular of degree `2`:
`mult_L(0) = 1` and `mult_L(2·2 − 0) = mult_L(4) = 0`. -/
theorem reflection_fails_odd_cycle (M : ℕ) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ) - (0 : ℝ) • LinearMap.id))
      ≠ Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ)
          - (2 * (2 : ℝ) - 0) • LinearMap.id)) := by
  rw [finrank_lap_odd_cycle_zero_eq_one M,
    show (2 * (2 : ℝ) - 0) = 4 from by norm_num, finrank_lap_odd_cycle_four_eq_zero M]
  exact one_ne_zero

/-- **SO TWO-COLOURABILITY IS NOT REMOVABLE FROM `SpectrumReflection`'s SYMMETRY.**
The odd cycle is regular of degree `2` and not two-colourable, and the reflection
fails on it. -/
theorem colorable_not_removable (M : ℕ) :
    (torusGraph 1 (2 * M + 3)).IsRegularOfDegree 2
      ∧ ¬ (torusGraph 1 (2 * M + 3)).Colorable 2
      ∧ ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ) - μ • LinearMap.id))
          = Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ)
              - (2 * (2 : ℝ) - μ) • LinearMap.id)) := by
  refine ⟨SignlessRegularSimple.torusGraph_one_isRegular (2 * M), ?_, fun h => ?_⟩
  · have := LaplacianSharpEquality.torus_not_colorable_two_of_odd (d := 0) (n := 2 * M + 2)
      ⟨M + 1, by ring⟩ (by omega)
    simpa using this
  · exact reflection_fails_odd_cycle M (h 0)

/-! ## 3. Both hypotheses, both necessary -/

/-- **NEITHER HYPOTHESIS OF `finrank_lap_reflect_of_regular_colorable` CAN BE
DROPPED.** The star is two-colourable and not regular; the odd cycle is regular and
not two-colourable; the symmetry fails on both. `SpectrumReflection`'s §6 recorded
that only half of this was proved, and this is the other half. -/
theorem both_hypotheses_needed (M : ℕ) (c : Fin (M + 3)) :
    ((torusGraph 1 (2 * M + 3)).IsRegularOfDegree 2
        ∧ ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ) - μ • LinearMap.id))
          = Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((torusGraph 1 (2 * M + 3)).lapMatrix ℝ)
              - (2 * (2 : ℝ) - μ) • LinearMap.id)))
      ∧ ((StarAdjNormExact.starGraph c).Colorable 2
        ∧ ¬ ∀ μ : ℝ, Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((StarAdjNormExact.starGraph c).lapMatrix ℝ) - μ • LinearMap.id))
          = Module.finrank ℝ (LinearMap.ker
            (Matrix.toLin' ((StarAdjNormExact.starGraph c).lapMatrix ℝ)
              - (2 * ((Fintype.card (Fin (M + 3)) : ℝ) - 1) - μ) • LinearMap.id))) := by
  obtain ⟨hreg, -, hfail⟩ := colorable_not_removable M
  exact ⟨⟨hreg, hfail⟩, SpectrumReflection.regularity_not_removable c (by simp)⟩

/-! ## 4. Review round 65 — the ways this could be hollow

**"§1 could be new work."** It is not: the parity argument is
`CycleSpectralBound.cos_ne_neg_one_of_odd`, which has been in the estate since that
file was written, and the name check found it before this file was drafted. What is
new is the MULTIPLICITY statement — `CycleSpectralBound.odd_cycle_lt` says the
degree bound is not attained in the LOEWNER order, which is a different statement
and does not give `finrank = 0`.

**"§2 might not need the odd cycle specifically."** It does not, and the header says
so plainly: every connected regular non-bipartite graph works, because `2Δ` is the
top of the Laplacian's range and
`LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable` says a connected regular
graph attains it exactly when two-colourable. The odd cycle is the cheapest instance,
not the only one. **That general statement is NOT proved here** — it is a Loewner
bound and the step to a multiplicity is not taken for general graphs.

**"§3 could be two theorems stapled together."** It is, and that is its job: the
value is in the conjunction, because `SpectrumReflection`'s §6 named the missing half
and this is the sentence that says the pairing is now complete. It proves nothing
its two halves do not.

**"The prediction that this would be expensive was wrong and might be hidden."** It
is in the header, in the words *"the estimate was wrong because it mistook a theorem
for an accident"*. That is the reusable part of this unit and it is worth more than
the theorem.
-/

end

end ReflectionNotColorable
