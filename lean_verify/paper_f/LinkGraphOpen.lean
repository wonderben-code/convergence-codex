import GreenDisconnected
import AdjSqForcesRegular

/-!
# A concrete instance for the wall's remaining question, since closing the last one left none

`WALLS` §W1.2 named `GreenLargeMass.stepGraph` as the smallest instance of this wall's open
question. `StepGraphSmallMass` then closed it at every mass, and `GreenDisconnected` explained why:
that graph falls into two pieces and the reflection swaps them, so the reflected form's diagonal
vanishes and positivity fails for a reason **no connected graph can reproduce**.

The wall's account records the consequence honestly — *"the remaining question now has no concrete
instance on the books at all, which is a worse position to be in than an hour ago"*. This file
supplies one.

## What the instance has to avoid

Three mechanisms now decide reflection positivity, and a useful instance must escape all three:

* **Disconnection** (`GreenDisconnected.not_reflectionPositive_of_zero_diag`) — so the graph must be
  connected, and in particular each half-site must reach its own mirror.
* **The strongly regular class** (`AdjSqForcesRegular.reflectionPositive_iff_hcross_of_adjSq_clean`)
  — which settles the question at *every* mass, so the graph must not be strongly regular. Failing
  to be regular at all is enough (`AdjSqForcesRegular.not_in_class_of_degrees_differ`).
* **Satisfying `hcross`** — which would make it reflection positive at every mass by
  `GraphMirrorReflection.reflectionPositive_mirror`, so the coupling must be positive somewhere.

`linkGraph` is `stepGraph` with one edge added, `2–5`, together with its mirror — which is itself,
since `σ 2 = 5`. One edge is the whole difference: it joins the two paths, and it is the only new
cut edge.

## What is known about it, and what is not

**Known:** it is connected; it is irregular, so outside the class; it fails `hcross`, at the same
vector `us = (1, −1, 0, …)`; and therefore it is **not reflection positive for `m² > 100`**, by the
large-mass converse.

**Not known, and this is the point of the file:** whether it is reflection positive at small mass.
Neither exclusion applies, no estimate in the estate reaches it, and the question is a finite
computation on six vertices that nothing here performs. **It is stated, not attempted.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LinkGraphOpen

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection GreenLargeMass

/-! ## 1. The graph: `stepGraph` plus the one edge that joins its two paths -/

/-- **`stepGraph` WITH ONE EDGE ADDED.** `2–5` is fixed as a set by `σ : p ↦ p + 3`, so adding it
keeps the reflection an automorphism, and it is the only edge that joins the two paths. -/
def linkGraph : SimpleGraph (Fin 6) where
  Adj p q := stepGraph.Adj p q ∨ ((p = 2 ∧ q = 5) ∨ (p = 5 ∧ q = 2))
  symm := by
    rintro p q (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h2, h1⟩)
    · exact Or.inr (Or.inl ⟨h2, h1⟩)
  loopless := ⟨by
    rintro p (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact stepGraph.irrefl h
    · exact absurd (h1.symm.trans h2) (by decide)
    · exact absurd (h1.symm.trans h2) (by decide)⟩

instance : DecidableRel linkGraph.Adj := fun p q =>
  inferInstanceAs (Decidable (stepGraph.Adj p q ∨ ((p = 2 ∧ q = 5) ∨ (p = 5 ∧ q = 2))))

theorem isRefl_sigma6_link : GraphReflection.IsRefl linkGraph sigma6 where
  invol := by intro p; revert p; decide
  adj := by intro p q; revert p q; decide

/-! ## 2. It is connected, so the disconnection mechanism cannot apply -/

theorem reachable_zero (v : Fin 6) : linkGraph.Reachable v 0 := by
  have h20 : linkGraph.Reachable 2 0 := (show linkGraph.Adj 2 0 by decide).reachable
  have h52 : linkGraph.Reachable 5 2 := (show linkGraph.Adj 5 2 by decide).reachable
  have h35 : linkGraph.Reachable 3 5 := (show linkGraph.Adj 3 5 by decide).reachable
  have h13 : linkGraph.Reachable 1 3 := (show linkGraph.Adj 1 3 by decide).reachable
  have h40 : linkGraph.Reachable 4 0 := (show linkGraph.Adj 4 0 by decide).reachable
  fin_cases v
  · exact SimpleGraph.Reachable.refl 0
  · exact h13.trans (h35.trans (h52.trans h20))
  · exact h20
  · exact h35.trans (h52.trans h20)
  · exact h40
  · exact h52.trans h20

theorem linkGraph_connected : linkGraph.Connected :=
  { preconnected := fun u v => (reachable_zero u).trans (reachable_zero v).symm }

/-- **SO EVERY HALF-SITE REACHES ITS OWN MIRROR**, and `GreenDisconnected`'s hypotheses are
unsatisfiable here: the reflected form's diagonal is strictly positive at every half-site. -/
theorem green_diag_pos_at_half (hm : m ≠ 0) (p : Fin 6) :
    0 < GraphLaplacian.green linkGraph m (sigma6 p) p :=
  (GreenDisconnected.green_pos_iff_reachable linkGraph hm _ _).mpr
    ((reachable_zero (sigma6 p)).trans (reachable_zero p).symm)

/-! ## 3. It is irregular, so the strongly regular class cannot apply -/

theorem degree_one : linkGraph.degree 1 = 1 := by decide

theorem degree_zero : linkGraph.degree 0 = 2 := by decide

/-- **OUTSIDE `GreenExpansion` §9's CLASS FOR ANY COEFFICIENTS**, since membership forces
regularity. -/
theorem not_in_adjSq_class :
    ¬ ∃ α β γ : ℝ, linkGraph.adjMatrix ℝ * linkGraph.adjMatrix ℝ
      = α • (1 : Matrix (Fin 6) (Fin 6) ℝ) + β • linkGraph.adjMatrix ℝ
        + γ • GreenExpansion.allOnes (Fin 6) :=
  AdjSqForcesRegular.not_in_class_of_degrees_differ linkGraph (u := 1) (v := 0)
    (by rw [degree_one, degree_zero]; decide)

theorem degree_le_two (v : Fin 6) : linkGraph.degree v ≤ 2 := by revert v; decide

/-! ## 4. And it fails the coupling hypothesis, so it is not positive for free -/

theorem not_isCrossBlock_linkGraph :
    ¬ CrossBlockStructure.IsCrossBlock linkGraph sigma6 Hs := by decide

/-- **THE COUPLING IS `+2` HERE TOO.** The new edge `2–5` adds a diagonal entry to the cut matrix
at site `2`, where `us` vanishes, so the refuting vector is unchanged. -/
theorem crossForm_link_pos (m : ℝ) : crossForm linkGraph m sigma6 Hs us = 2 := by
  have h := GreenLargeMass.sum_crossAdj_eq (G := linkGraph) (θ := sigma6) (H := Hs)
    (Mir := (∅ : Finset (Fin 6))) isMirrorHalf_Hs m us
  have hs : ∑ p ∈ Hs, ∑ q ∈ Hs, us p * us q * CrossFormMatrix.crossAdj linkGraph sigma6 p q
      = -2 := by
    simp only [GreenLargeMass.sum_Hs, CrossFormMatrix.crossAdj, sigma6_apply]
    norm_num [us, show ((1 : Fin 6) + 3) = 4 from rfl, show ((2 : Fin 6) + 3) = 5 from rfl,
      show ((0 : Fin 6) + 3) = 3 from rfl,
      show ¬ linkGraph.Adj 0 3 by decide, show linkGraph.Adj 0 4 by decide,
      show ¬ linkGraph.Adj 0 5 by decide, show linkGraph.Adj 1 3 by decide,
      show ¬ linkGraph.Adj 1 4 by decide, show ¬ linkGraph.Adj 1 5 by decide,
      show ¬ linkGraph.Adj 2 3 by decide, show ¬ linkGraph.Adj 2 4 by decide,
      show linkGraph.Adj 2 5 by decide,
      show (![1, -1, 0, 0, 0, 0] : Fin 6 → ℝ) 2 = 0 from rfl]
  rw [hs] at h
  linarith

/-- The weighted `ℓ¹` mass of the refuting vector on `linkGraph`: the same `3 + 2m²` as on
`stepGraph`, because `us` is supported where the two graphs have the same degrees. -/
theorem us_weighted_sum_link (m : ℝ) :
    ∑ p ∈ Hs, |us p * ((linkGraph.degree p : ℝ) + m ^ 2)| = 3 + 2 * m ^ 2 := by
  have hm : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  have e0 : us 0 = 1 := by simp [us]
  have e1 : us 1 = -1 := by simp [us]
  have e2 : us 2 = 0 := by simp [us]
  rw [GreenLargeMass.sum_Hs (fun p => |us p * ((linkGraph.degree p : ℝ) + m ^ 2)|), e0, e1, e2,
    degree_zero, degree_one, show linkGraph.degree 2 = 2 by decide]
  push_cast
  rw [one_mul, zero_mul, abs_zero,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 + m ^ 2 by linarith),
    show (-1 : ℝ) * (1 + m ^ 2) = -(1 + m ^ 2) by ring, abs_neg,
    abs_of_nonneg (show (0 : ℝ) ≤ 1 + m ^ 2 by linarith)]
  ring

/-! ## 5. What is decided, and what is not -/

/-- **DECIDED ABOVE `m² = 100`**, by the large-mass converse — the same constant as `stepGraph`,
because the refuting vector and the degree ceiling are the same. -/
theorem not_reflectionPositive_of_large {m : ℝ} (hm : 100 < m ^ 2) :
    ¬ GraphReflection.ReflectionPositive linkGraph m sigma6 Hs := by
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hm; norm_num at hm
  refine GreenLargeMass.not_reflectionPositive_of_crossForm_pos_general (u := us) (Δ := 2)
    isMirrorHalf_Hs isRefl_sigma6_link hm0 degree_le_two us_supported ?_
  rw [crossForm_link_pos, us_weighted_sum_link]
  have ht : (0 : ℝ) < m ^ 2 := by linarith
  have hcube : (0 : ℝ) < (m ^ 2) ^ 3 := by positivity
  have hrw : (m ^ 2)⁻¹ ^ 3 * ((2 : ℕ) : ℝ) ^ 2 * (3 + 2 * m ^ 2) ^ 2
      = (4 * (3 + 2 * m ^ 2) ^ 2) / ((m ^ 2) ^ 3) := by
    push_cast
    rw [inv_pow]
    field_simp
    ring
  rw [hrw, div_lt_iff₀ hcube]
  nlinarith [hm, ht, mul_pos (show (0 : ℝ) < m ^ 2 - 100 by linarith) ht]

/-- **AND THE THREE EXCLUSIONS, TOGETHER**, so that what is open is visible as what is left after
them. Connected, irregular, and failing `hcross`: `GreenDisconnected` cannot apply,
`AdjSqForcesRegular` cannot apply, and `reflectionPositive_mirror` cannot apply. -/
theorem the_three_exclusions :
    linkGraph.Connected
      ∧ (¬ ∃ α β γ : ℝ, linkGraph.adjMatrix ℝ * linkGraph.adjMatrix ℝ
          = α • (1 : Matrix (Fin 6) (Fin 6) ℝ) + β • linkGraph.adjMatrix ℝ
            + γ • GreenExpansion.allOnes (Fin 6))
      ∧ ¬ CrossBlockStructure.IsCrossBlock linkGraph sigma6 Hs :=
  ⟨linkGraph_connected, not_in_adjSq_class, not_isCrossBlock_linkGraph⟩

end LinkGraphOpen
