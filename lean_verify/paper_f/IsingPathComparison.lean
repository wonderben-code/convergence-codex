/-
  IsingPathComparison.lean — any comparison model whose couplings sit below the box's, compared to
  the box by one theorem; and the coupling vector that keeps a CHOSEN SET OF BONDS.

  WHY. `WALLS §W3.6`'s last addendum names the remaining step on the Griffiths-comparison arm as
  *"for each site, a path to the boundary of its own depth, **presented in the Griffiths idiom with
  couplings below the box's**"*. `IsingBoxWalk.exists_boundary_walk` supplied the path. **This file
  is the second clause and nothing else.**

  WHAT IS PROVED.

  * `expect_le_integral` — for **any** `c : BoxIdx n → ℝ` with `0 ≤ c` and `c ≤ boxCoup n β h`, the
    comparison model's correlation is at most the box's, as an integral against `isingMeasure`
    itself. This is `griffiths_expect_mono` at the box's own interaction family, and it is the
    whole of "presented in the Griffiths idiom with couplings below the box's".
  * `pathCoup` — the couplings that keep the bonds of a chosen `B : Finset (Site n × Site n)` and
    the boundary field, and switch every other bond off. `pathCoup_le_integral` is the instance.

  **AND THE EXISTING ROUTE IS NOW THE `B = ∅` CASE, IN THE CODE AND NOT ONLY IN THE PROSE**
  (`ERRATUM 201` — a generalisation must be instantiated). `boxFieldCoup_eq_pathCoup_empty` proves
  `IsingBoxInteraction.boxFieldCoup n β h = pathCoup n β h ∅`, so the bond-free comparison that
  `zero_le_integral_interior` shows to be worth `0` inside the box is literally this file's family
  with no bonds kept, rather than a different construction that resembles it.

  WHAT IS **NOT** PROVED, AND IT IS NOW THE WHOLE RESIDUE OF THIS ARM. Nothing here computes
  `num (boxSet n) (pathCoup n β h B) A / part (boxSet n) (pathCoup n β h B)`. For `B = ∅` it is a
  product of `tanh`s (`IsingIndependentSpins.prod_tanh_le_expect`, via `IsSiteField`); for `B` a
  path it should be `(tanh β)^{|B|} · tanh (β·h)` by `IsingChainDecay.chain_expect`, but that
  theorem lives on `IsingChainDecay.chainSite` and this one on `Fin n × Fin n`, and **nothing
  carries one onto the other**. That transport is not attempted here and its cost is not claimed
  (`ERRATUM 246`). **No wall moves**, and this file proves no lower bound on anything.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingBoxInteraction
import IsingBoxWalk

namespace IsingPathComparison

open Finset Real MeasureTheory
open IsingFiniteVolume IsingBoundaryField
open IsingGriffiths IsingGriffithsMono IsingIndependentSpins IsingBoxInteraction
open IsingChainRouteCeiling

variable {n : ℕ}

/-! ## 1. The Griffiths idiom at the box, for an arbitrary dominated comparison -/

/-- **EVERY COMPARISON MODEL WITH COUPLINGS BELOW THE BOX'S IS BELOW THE BOX**, as an integral
against `isingMeasure` itself rather than against a sum of Boltzmann weights. The observable is an
arbitrary finite set of sites. This is the sentence `WALLS §W3.6` asks for; what it does NOT do is
evaluate the left-hand side for any particular `c`. -/
theorem expect_le_integral (β h : ℝ) (c : BoxIdx n → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    (hcle : ∀ i, c i ≤ boxCoup n β h i) (A : Finset (Site n)) :
    num (boxSet n) c A / part (boxSet n) c
      ≤ ∫ σ, ∏ p ∈ A, IsingTransfer2D.spin (σ p) ∂(isingMeasure n h β) := by
  have hb := griffiths_expect_mono (boxSet n) c (boxCoup n β h) hc0 hcle A
  rw [num_eq_sum n β h A, part_eq_partition n β h] at hb
  rw [isingMeasure]
  exact FiniteGibbsSum.le_integral_gibbs_count β (isingHB n h) _ hb

/-- The magnetisation case, which is the one the wall's inequality is about. -/
theorem expect_le_integral_site (β h : ℝ) (c : BoxIdx n → ℝ) (hc0 : ∀ i, 0 ≤ c i)
    (hcle : ∀ i, c i ≤ boxCoup n β h i) (p₀ : Site n) :
    num (boxSet n) c {p₀} / part (boxSet n) c
      ≤ ∫ σ, IsingTransfer2D.spin (σ p₀) ∂(isingMeasure n h β) := by
  have h₁ := expect_le_integral β h c hc0 hcle {p₀}
  simpa using h₁

/-! ## 2. Keeping a chosen set of bonds -/

/-- The couplings that keep the bonds of `B` and the boundary field, and switch every other bond
off. The `adj` guard is what makes domination automatic: a pair in `B` that is not a bond of the
box gets `0`, so no hypothesis relating `B` to the lattice is ever needed. -/
def pathCoup (n : ℕ) (β h : ℝ) (B : Finset (Site n × Site n)) : BoxIdx n → ℝ
  | Sum.inl (p, q) => if (p, q) ∈ B ∧ adj p q then β else 0
  | Sum.inr p => if isBoundary p then β * h else 0

theorem pathCoup_nonneg {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) (B : Finset (Site n × Site n)) :
    ∀ i : BoxIdx n, 0 ≤ pathCoup n β h B i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hpq : (p, q) ∈ B ∧ adj p q <;> simp [pathCoup, hpq, hβ]
  · by_cases hp : isBoundary p <;> simp [pathCoup, hp, mul_nonneg hβ hh]

theorem pathCoup_le_boxCoup {β h : ℝ} (hβ : 0 ≤ β) (B : Finset (Site n × Site n)) :
    ∀ i : BoxIdx n, pathCoup n β h B i ≤ boxCoup n β h i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hadj : adj p q
    · by_cases hmem : (p, q) ∈ B
      · simp [pathCoup, boxCoup, hadj, hmem]
      · simp [pathCoup, boxCoup, hadj, hmem, hβ]
    · simp [pathCoup, boxCoup, hadj]
  · by_cases hp : isBoundary p <;> simp [pathCoup, boxCoup, hp]

/-- The instance: a comparison keeping any chosen bonds is below the box. -/
theorem pathCoup_le_integral (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (B : Finset (Site n × Site n)) (A : Finset (Site n)) :
    num (boxSet n) (pathCoup n β h B) A / part (boxSet n) (pathCoup n β h B)
      ≤ ∫ σ, ∏ p ∈ A, IsingTransfer2D.spin (σ p) ∂(isingMeasure n h β) :=
  expect_le_integral β h _ (pathCoup_nonneg hβ hh B) (pathCoup_le_boxCoup hβ B) A

/-! ## 3. The walk's own bonds, and that keeping them is not vacuous -/

/-- The bonds a walk uses in its first `m` steps. -/
def walkBonds (γ : ℕ → Site n) (m : ℕ) : Finset (Site n × Site n) :=
  (Finset.range m).image (fun i => (γ i, γ (i + 1)))

theorem walkBonds_card_le (γ : ℕ → Site n) (m : ℕ) : (walkBonds γ m).card ≤ m := by
  refine le_trans (Finset.card_image_le) ?_
  simp

/-- **KEEPING A WALK'S BONDS IS NOT VACUOUS, AND THIS IS WHY THE LEMMA EXISTS.** `pathCoup`'s `adj`
guard makes domination automatic, but it also means a set of NON-adjacent pairs would leave every
bond coupling `0` — that is, a "path comparison" built from a bad set would silently be the
bond-free model of §3 and every statement about it would still be true. Along an actual walk the
coupling really is `β`. -/
theorem pathCoup_walk_eq (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
    (hadj : ∀ k, k < m → adj (γ k) (γ (k + 1))) (i : ℕ) (hi : i < m) :
    pathCoup n β h (walkBonds γ m) (Sum.inl (γ i, γ (i + 1))) = β := by
  have hmem : (γ i, γ (i + 1)) ∈ walkBonds γ m :=
    Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, rfl⟩
  simp [pathCoup, hmem, hadj i hi]

/-- **THE PATH'S INTERMEDIATE SITES CARRY NO FIELD**, which is the other half of what makes the
comparison model a chain in `IsingChainDecay`'s sense: a field at the base and bare sites hanging
off it. It is `IsingBoxWalk.exists_boundary_walk`'s fifth clause read through `pathCoup`. -/
theorem pathCoup_no_field_before (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
    (hoff : ∀ i, i < m → isBoundary (γ i) = false) (B : Finset (Site n × Site n))
    (i : ℕ) (hi : i < m) :
    pathCoup n β h B (Sum.inr (γ i)) = 0 := by
  simp [pathCoup, hoff i hi]

/-- **THE PRESENTATION CLAUSE, FOR EVERY SITE OF THE BOX.** For every `p` there is a set of at most
`depth n p` genuine bonds of the box such that the comparison model keeping exactly those bonds and
the boundary field is below the box at `p`, and whose last site is on the boundary. This is
`WALLS §W3.6`'s *"a path to the boundary of its own depth, presented in the Griffiths idiom with
couplings below the box's"* — **the presentation, not the evaluation.** The two coupling clauses
say the model along the path really is a chain in `IsingChainDecay`'s sense: `β` on each of its
bonds, and no field on any site before the last. The ratio on the left is **not computed here** and
no lower bound on the box follows from this theorem alone. -/
theorem exists_path_comparison (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (p : Site n) :
    ∃ (γ : ℕ → Site n) (B : Finset (Site n × Site n)),
      γ 0 = p ∧ isBoundary (γ (depth n p)) = true ∧ B = walkBonds γ (depth n p) ∧
      B.card ≤ depth n p ∧
      (∀ i, i < depth n p → pathCoup n β h B (Sum.inl (γ i, γ (i + 1))) = β) ∧
      (∀ i, i < depth n p → pathCoup n β h B (Sum.inr (γ i)) = 0) ∧
      num (boxSet n) (pathCoup n β h B) {p} / part (boxSet n) (pathCoup n β h B)
        ≤ ∫ σ, IsingTransfer2D.spin (σ p) ∂(isingMeasure n h β) := by
  obtain ⟨γ, h0, hbd, hadj, -, hoff⟩ := IsingBoxWalk.exists_boundary_walk n p
  refine ⟨γ, walkBonds γ (depth n p), h0, hbd, rfl, walkBonds_card_le γ _,
    fun i hi => pathCoup_walk_eq β h γ _ hadj i hi,
    fun i hi => pathCoup_no_field_before β h γ _ hoff _ i hi, ?_⟩
  have := pathCoup_le_integral β h hβ hh (walkBonds γ (depth n p)) {p}
  simpa using this

/-! ## 4. The bond-free route is the `B = ∅` case, in the code -/

/-- **THE EXISTING COMPARISON IS THIS ONE WITH NO BONDS KEPT.** Stated so that the relationship is
a theorem rather than a resemblance (`ERRATUM 201`). -/
theorem boxFieldCoup_eq_pathCoup_empty (n : ℕ) (β h : ℝ) :
    boxFieldCoup n β h = pathCoup n β h ∅ := by
  funext i
  rcases i with ⟨p, q⟩ | p
  · simp [boxFieldCoup, pathCoup]
  · rfl

/-- And so the route that pays `0` at an interior site is the empty-bond member of this family. -/
theorem boxField_le_integral_of_pathCoup (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (A : Finset (Site n)) :
    num (boxSet n) (boxFieldCoup n β h) A / part (boxSet n) (boxFieldCoup n β h)
      ≤ ∫ σ, ∏ p ∈ A, IsingTransfer2D.spin (σ p) ∂(isingMeasure n h β) := by
  rw [boxFieldCoup_eq_pathCoup_empty]
  exact pathCoup_le_integral β h hβ hh ∅ A

end IsingPathComparison
