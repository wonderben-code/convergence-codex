/-
  IsingBoundaryRouteCeiling.lean — the comparison against the BOND-FREE model cannot produce
  `MagnetisationBound`, and that is a theorem rather than an observation.

  WHY. `IsingBoxInteraction` ended by saying, in as many words, that at an interior site this route
  gives exactly `0`, so it can only pay for the boundary and never for the area — and that making
  the failure itself a theorem *"needs the boundary's cardinality, which is not here"*. **This is
  that**, and it is arithmetic rather than physics, exactly as that file predicted.

  WHAT IS PROVED, IN THREE STEPS.

  1. **`card_boundary_le`** — the boundary of the `n × n` box has at most `4·n` sites. Four pinned
     lines, each of at most `n` sites, by an injection onto the free coordinate. No case split on
     `n = 0` is needed: at `n = 0` the site type is empty and every count is `0`.
  2. **`sum_boxField_tanh`** and **`route_bound_le`** — the total this route delivers is
     `|∂| · tanh (β·h)`, hence at most `4·n·tanh (β·h)`: **linear in `n`**.
  3. **`route_insufficient`** — and no linear quantity dominates `m·n²` for `m > 0`. So for every
     positive `m`, every `β` and every `h`, it is FALSE that the route's own output satisfies
     `MagnetisationBound`'s inequality at every box.

  **AND THE INTEGRAL VERSION IS PROVED TOO, NOT LEFT AS A GAP.** `sum_le_integral_magnetisation`
  sums `IsingBoxInteraction.boxField_le_integral` over the sites — integrability is free on a finite
  space against a probability measure (`Integrable.of_finite`) — so the ceiling is a statement about
  `∫ magnetisation ∂(isingMeasure)` and not only about a sum of separate bounds.

  **WHAT THIS DOES NOT SAY, AND IT IS THE WHOLE OF THE CARE THIS FILE NEEDS.**

  * It says nothing about whether `MagnetisationBound` is TRUE. It rules out one METHOD — the same
    shape `StratumExhausted.no_uniform_field_from_stratum` established for a different method, and
    the same caution applies verbatim. A route shown incapable is information about the route.
  * **AND IT RULES OUT ONE COMPARISON, NOT ALL OF THEM.** What is bounded here is the output of
    comparing against the model with EVERY BOND SWITCHED OFF, which is the only comparison model
    whose magnetisation this estate can compute (`IsingIndependentSpins`, and it computes it
    because the sites are independent there). A comparison retaining some bonds is not ruled out by
    anything below — it is a different and harder route, because its comparison model's
    magnetisation would itself need computing. **A first draft of this header said "the
    Griffiths-comparison route", which is broader than what is proved**, and it is corrected here
    rather than left to be read charitably (`ERRATUM 247`).

  **AND THE REASON IS PHYSICAL, NOT TECHNICAL.** With every bond off, the only magnetisation left
  is the field's own, and the field lives on `O(n)` sites while the target is `O(n²)`. No choice of
  `β`, `h` or `m` recovers a factor of `n`, because none of them depends on `n` at all: the deficit
  is the whole point, and it is why a field acting on the boundary is a genuinely harder problem
  than a field acting everywhere — which `IsingSlabUniformBound` settled the same day.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingBoxInteraction

namespace IsingBoundaryRouteCeiling

open Finset Real MeasureTheory
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction
open IsingIndependentSpins

noncomputable section

/-! ## 1. The boundary is linear in the side -/

/-- A predicate pinning the FIRST coordinate to one value cuts out at most `n` sites. -/
theorem card_pinned_fst (n : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a b : Fin n, P a.val → P b.val → a = b) :
    (Finset.univ.filter fun p : Site n => P p.1.val).card ≤ n := by
  classical
  have hinj : Set.InjOn (fun p : Site n => p.2)
      (Finset.univ.filter fun p : Site n => P p.1.val) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
    exact Prod.ext (hP a.1 b.1 ha hb) hab
  refine le_trans (Finset.card_le_card_of_injOn (fun p : Site n => p.2)
    (fun _ _ => Finset.mem_univ _) hinj) ?_
  simp

/-- And the same for the second. -/
theorem card_pinned_snd (n : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ a b : Fin n, P a.val → P b.val → a = b) :
    (Finset.univ.filter fun p : Site n => P p.2.val).card ≤ n := by
  classical
  have hinj : Set.InjOn (fun p : Site n => p.1)
      (Finset.univ.filter fun p : Site n => P p.2.val) := by
    intro a ha b hb hab
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at ha hb
    exact Prod.ext hab (hP a.2 b.2 ha hb)
  refine le_trans (Finset.card_le_card_of_injOn (fun p : Site n => p.1)
    (fun _ _ => Finset.mem_univ _) hinj) ?_
  simp

theorem pin_zero (n : ℕ) : ∀ a b : Fin n, a.val = 0 → b.val = 0 → a = b :=
  fun _ _ ha hb => Fin.ext (ha.trans hb.symm)

theorem pin_last (n : ℕ) : ∀ a b : Fin n, a.val + 1 = n → b.val + 1 = n → a = b :=
  fun _ _ ha hb => Fin.ext (by omega)

/-- **THE BOUNDARY OF THE `n × n` BOX HAS AT MOST `4·n` SITES.** Four pinned lines. -/
theorem card_boundary_le (n : ℕ) :
    (Finset.univ.filter fun p : Site n => isBoundary p = true).card ≤ 4 * n := by
  classical
  set B₁ := Finset.univ.filter fun p : Site n => p.1.val = 0 with hB₁
  set B₂ := Finset.univ.filter fun p : Site n => p.1.val + 1 = n with hB₂
  set B₃ := Finset.univ.filter fun p : Site n => p.2.val = 0 with hB₃
  set B₄ := Finset.univ.filter fun p : Site n => p.2.val + 1 = n with hB₄
  have hsub : (Finset.univ.filter fun p : Site n => isBoundary p = true) ⊆ B₁ ∪ B₂ ∪ B₃ ∪ B₄ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, isBoundary,
      decide_eq_true_eq] at hp
    simp only [hB₁, hB₂, hB₃, hB₄, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  refine le_trans (Finset.card_le_card hsub) ?_
  have h1 : B₁.card ≤ n := by
    rw [hB₁]; exact card_pinned_fst n (fun k => k = 0) (pin_zero n)
  have h2 : B₂.card ≤ n := by
    rw [hB₂]; exact card_pinned_fst n (fun k => k + 1 = n) (pin_last n)
  have h3 : B₃.card ≤ n := by
    rw [hB₃]; exact card_pinned_snd n (fun k => k = 0) (pin_zero n)
  have h4 : B₄.card ≤ n := by
    rw [hB₄]; exact card_pinned_snd n (fun k => k + 1 = n) (pin_last n)
  calc (B₁ ∪ B₂ ∪ B₃ ∪ B₄).card
      ≤ (B₁ ∪ B₂ ∪ B₃).card + B₄.card := Finset.card_union_le _ _
    _ ≤ ((B₁ ∪ B₂).card + B₃.card) + B₄.card := by
        exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((B₁.card + B₂.card) + B₃.card) + B₄.card := by
        exact Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ ((n + n) + n) + n := by omega
    _ = 4 * n := by ring

/-! ## 2. What the route delivers -/

/-- The route's total is the boundary's size times `tanh (β·h)`: every interior site contributes
`tanh 0 = 0`. -/
theorem sum_boxField_tanh (n : ℕ) (β h : ℝ) :
    ∑ p : Site n, tanh (boxField n β h p)
      = ((Finset.univ.filter fun p : Site n => isBoundary p = true).card : ℝ) * tanh (β * h) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun p : Site n => isBoundary p = true)]
  have hin : ∀ p ∈ Finset.univ.filter fun p : Site n => isBoundary p = true,
      tanh (boxField n β h p) = tanh (β * h) := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [boxField, if_pos hp.2]
  have hout : ∀ p ∈ Finset.univ.filter fun p : Site n => ¬ (isBoundary p = true),
      tanh (boxField n β h p) = 0 := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    rw [boxField, if_neg hp.2, Real.tanh_zero]
  rw [Finset.sum_congr rfl hin, Finset.sum_congr rfl hout, Finset.sum_const, Finset.sum_const_zero,
    add_zero, nsmul_eq_mul]

/-- **AND IT IS LINEAR IN THE SIDE OF THE BOX.** -/
theorem route_bound_le (n : ℕ) {β h : ℝ} (hβh : 0 ≤ β * h) :
    ∑ p : Site n, tanh (boxField n β h p) ≤ 4 * (n : ℝ) * tanh (β * h) := by
  rw [sum_boxField_tanh n β h]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · exact_mod_cast card_boundary_le n
  · rcases eq_or_lt_of_le hβh with heq | hlt
    · rw [← heq, Real.tanh_zero]
    · exact (tanh_pos_of_pos hlt).le

/-! ## 3. And it is a statement about the measure -/

/-- The per-site bounds sum to a bound on the magnetisation, integrability being free on a finite
space against a probability measure. -/
theorem sum_le_integral_magnetisation (n : ℕ) {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    ∑ p : Site n, tanh (boxField n β h p)
      ≤ ∫ σ, magnetisation n σ ∂(isingMeasure n h β) := by
  haveI : IsProbabilityMeasure (isingMeasure n h β) := isingHB_isProbability n h β
  have hsplit : ∫ σ, magnetisation n σ ∂(isingMeasure n h β)
      = ∑ p : Site n, ∫ σ, IsingTransfer2D.spin (σ p) ∂(isingMeasure n h β) := by
    rw [show (fun σ : Config n => magnetisation n σ)
        = fun σ => ∑ p : Site n, IsingTransfer2D.spin (σ p) from rfl]
    exact integral_finset_sum _ fun p _ => Integrable.of_finite
  rw [hsplit]
  exact Finset.sum_le_sum fun p _ => boxField_le_integral β h hβ hh p

/-! ## 4. The ceiling -/

/-- **THE ROUTE CANNOT PRODUCE `MagnetisationBound`.** For every `m > 0` and every `β`, `h`, the
total this comparison delivers fails the inequality at all large boxes — because it grows like the
side and the target grows like the area. -/
theorem route_insufficient {β h m : ℝ} (hβh : 0 ≤ β * h) (hm : 0 < m) :
    ¬ ∀ n : ℕ, 0 < n → m * ((n : ℝ) * n) ≤ ∑ p : Site n, tanh (boxField n β h p) := by
  intro hall
  obtain ⟨N, hN⟩ := exists_nat_gt ((4 * tanh (β * h)) / m)
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h3 : m * (((N : ℝ) + 1) * ((N : ℝ) + 1)) ≤ 4 * ((N : ℝ) + 1) * tanh (β * h) := by
    have h1 := hall (N + 1) (Nat.succ_pos N)
    have h2 := route_bound_le (N + 1) hβh
    have hle := le_trans h1 h2
    push_cast at hle
    exact hle
  have h4 : m * ((N : ℝ) + 1) ≤ 4 * tanh (β * h) := by
    by_contra hcon
    have hcon' : 4 * tanh (β * h) < m * ((N : ℝ) + 1) := not_le.mp hcon
    nlinarith [h3, hpos, hcon']
  have h5 : (4 * tanh (β * h)) / m < (N : ℝ) + 1 := lt_trans hN (by linarith)
  rw [div_lt_iff₀ hm] at h5
  nlinarith [h4, h5]

end

end IsingBoundaryRouteCeiling
