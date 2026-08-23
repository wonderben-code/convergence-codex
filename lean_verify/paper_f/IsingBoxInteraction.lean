/-
  IsingBoxInteraction.lean — the boundary-field box Hamiltonian, written as a list of interaction
  terms, and the magnetisation bound that follows at every site.

  WHY. `FiniteGibbsSum` built the bridge between an integral and a ratio of sums and named the one
  remaining thing: *"`isingHB` presented as `∑ᵢ Jᵢ ∏_{Sᵢ} spin` with the boundary field as the
  `IsSiteField` part."* That is the same presentation `IsingSlabGriffiths.energy_eq` performs for
  the slab, done for the box. **This is that.**

  THE PRESENTATION. `−β · isingHB n h σ = β·∑_{p,q} [p ~ q] σ_p σ_q + β·h·∑_{p ∈ ∂} σ_p`, so the
  index family is `(Site n × Site n) ⊕ Site n`: an ordered pair carries the two-element set `{p, q}`
  with coupling `β` when the sites are adjacent and `0` otherwise, and a site carries the singleton
  `{p}` with coupling `β·h` when it is on the boundary and `0` otherwise. **`adj_irrefl` is what
  makes the pair term honest** — `∏_{v ∈ {p,q}} σ_v` is `σ_p·σ_q` only when `p ≠ q`, and adjacency
  gives exactly that.

  THE BOX'S DOUBLE-COUNT IS INHERITED AND NOT REPAIRED. `isingH` sums over ORDERED pairs, so each
  bond appears twice; that is `IsingFiniteVolume`'s stated convention and it is a rescaling of the
  coupling, harmless here because every hypothesis below is `0 ≤ β`.

  WHAT COMES OUT. **`tanh_le_expect_boundary`**: for `0 ≤ β` and `0 ≤ h`, the magnetisation at a
  BOUNDARY site of the box is at least `tanh (β·h)`. **`zero_le_expect_site`**: at any site it is at
  least `0`. Both are integrals against `isingMeasure n h β` itself, not against a ratio — the
  bridge is applied here rather than left for the reader.

  **AND THE INTERIOR BOUND IS `0`, WHICH IS THE POINT.** The comparison model has a field only on
  `∂`, so `IsingIndependentSpins.expect_eq_prod_tanh` returns `tanh 0 = 0` at every interior site.
  That is not a weakness of the proof: it is the honest output of this route, and it is why the
  route cannot reach a bound proportional to the AREA of the box. Making that failure a theorem
  needs the boundary's cardinality, which is not here.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingIndependentSpins
import FiniteGibbsSum
import IsingBoundaryField

namespace IsingBoxInteraction

open Finset Real MeasureTheory
open IsingFiniteVolume IsingBoundaryField
open IsingGriffiths IsingGriffithsMono IsingIndependentSpins

noncomputable section

variable {n : ℕ}

/-! ## 1. The two `spin`s are one -/

/-- This estate defines `spin` twice with identical bodies — `IsingFiniteVolume.spin` for the box
and `IsingTransfer2D.spin` for the transfer-matrix chain. The magnetisation machinery is stated
against the second and the box against the first, so the identification is needed here. It is
`rfl`, and recording that is cheaper than choosing a winner. -/
theorem spin_eq : (IsingFiniteVolume.spin) = (IsingTransfer2D.spin) := rfl

/-! ## 2. The interaction data -/

/-- One term per ordered pair of sites, one per site. -/
abbrev BoxIdx (n : ℕ) := (Site n × Site n) ⊕ Site n

/-- Their sites: a pair carries `{p, q}`, a site carries `{p}`. -/
def boxSet (n : ℕ) : BoxIdx n → Finset (Site n)
  | Sum.inl (p, q) => {p, q}
  | Sum.inr p => {p}

/-- Their couplings: `β` on a bond, `β·h` on a boundary site, `0` elsewhere. -/
def boxCoup (n : ℕ) (β h : ℝ) : BoxIdx n → ℝ
  | Sum.inl (p, q) => if adj p q then β else 0
  | Sum.inr p => if isBoundary p then β * h else 0

theorem boxCoup_nonneg {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    ∀ i : BoxIdx n, 0 ≤ boxCoup n β h i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hpq : adj p q <;> simp [boxCoup, hpq, hβ]
  · by_cases hp : isBoundary p <;> simp [boxCoup, hp, mul_nonneg hβ hh]

/-- The pair term is a genuine product of two distinct spins exactly when the sites are adjacent,
and `adj_irrefl` is what supplies that. -/
theorem prod_boxSet_inl (p q : Site n) (hpq : adj p q) (σ : Config n) :
    ∏ v ∈ boxSet n (Sum.inl (p, q)), IsingTransfer2D.spin (σ v)
      = IsingTransfer2D.spin (σ p) * IsingTransfer2D.spin (σ q) := by
  have hne : p ≠ q := by
    rintro rfl
    exact adj_irrefl p hpq
  rw [boxSet, Finset.prod_pair hne]

/-! ## 3. The presentation -/

/-- **`−β · isingHB` IS A SUM OF INTERACTION TERMS**, which is the statement the whole chain needed
about this model and did not have. -/
theorem energy_eq (n : ℕ) (β h : ℝ) (σ : Config n) :
    ∑ i : BoxIdx n, boxCoup n β h i * ∏ v ∈ boxSet n i, IsingTransfer2D.spin (σ v)
      = -β * isingHB n h σ := by
  rw [Fintype.sum_sum_type, isingHB, isingH, boundaryTerm]
  have hpair : ∑ i : Site n × Site n,
      boxCoup n β h (Sum.inl i) * ∏ v ∈ boxSet n (Sum.inl i), IsingTransfer2D.spin (σ v)
      = β * ∑ p : Site n, ∑ q : Site n,
          if adj p q then IsingTransfer2D.spin (σ p) * IsingTransfer2D.spin (σ q) else 0 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hpq : adj p q
    · rw [if_pos hpq, prod_boxSet_inl p q hpq σ]
      simp [boxCoup, hpq]
    · rw [if_neg hpq]
      simp [boxCoup, hpq]
  have hsite : ∑ p : Site n,
      boxCoup n β h (Sum.inr p) * ∏ v ∈ boxSet n (Sum.inr p), IsingTransfer2D.spin (σ v)
      = β * h * ∑ p : Site n, if isBoundary p then IsingTransfer2D.spin (σ p) else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : isBoundary p <;> simp [boxCoup, boxSet, hp]
  rw [hpair, hsite, ← spin_eq]
  ring

/-! ## 4. The comparison field: on the boundary and nowhere else -/

/-- The couplings with every bond switched off. -/
def boxFieldCoup (n : ℕ) (β h : ℝ) : BoxIdx n → ℝ
  | Sum.inl _ => 0
  | Sum.inr p => if isBoundary p then β * h else 0

/-- Its field strength, site by site: `β·h` on the boundary, `0` inside. -/
def boxField (n : ℕ) (β h : ℝ) (p : Site n) : ℝ := if isBoundary p then β * h else 0

theorem boxFieldCoup_nonneg {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    ∀ i : BoxIdx n, 0 ≤ boxFieldCoup n β h i := by
  rintro (⟨p, q⟩ | p)
  · exact le_refl 0
  · by_cases hp : isBoundary p <;> simp [boxFieldCoup, hp, mul_nonneg hβ hh]

theorem boxFieldCoup_le_boxCoup {β h : ℝ} (hβ : 0 ≤ β) :
    ∀ i : BoxIdx n, boxFieldCoup n β h i ≤ boxCoup n β h i := by
  rintro (⟨p, q⟩ | p)
  · by_cases hpq : adj p q <;> simp [boxFieldCoup, boxCoup, hpq, hβ]
  · by_cases hp : isBoundary p <;> simp [boxFieldCoup, boxCoup, hp]

/-- **AND IT IS A SITE-DEPENDENT FIELD**, which the uniform statement could not have expressed. -/
theorem isSiteField_boxField (n : ℕ) (β h : ℝ) :
    IsSiteField (boxSet n) (boxFieldCoup n β h) (boxField n β h) := by
  intro σ
  rw [Fintype.sum_sum_type]
  have hpair : ∑ i : Site n × Site n,
      boxFieldCoup n β h (Sum.inl i)
        * ∏ v ∈ boxSet n (Sum.inl i), IsingTransfer2D.spin (σ v) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨p, q⟩ := i
    rw [boxFieldCoup, zero_mul]
  rw [hpair, zero_add]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [boxSet, Finset.prod_singleton, boxFieldCoup, boxField]

/-! ## 5. The bound, at the measure -/

/-- The `num`/`part` pair of this model is the Boltzmann pair of `isingHB`. -/
theorem part_eq_partition (n : ℕ) (β h : ℝ) :
    part (boxSet n) (boxCoup n β h) = FiniteGibbsSum.partition β (isingHB n h) := by
  rw [part, FiniteGibbsSum.partition]
  exact Finset.sum_congr rfl fun σ _ => by rw [energy_eq n β h σ]

theorem num_eq_sum (n : ℕ) (β h : ℝ) (p₀ : Site n) :
    num (boxSet n) (boxCoup n β h) {p₀}
      = ∑ σ : Config n, exp (-β * isingHB n h σ) * IsingTransfer2D.spin (σ p₀) := by
  rw [num]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_singleton, energy_eq n β h σ, mul_comm]

/-- **THE MAGNETISATION AT A SITE OF THE BOUNDARY-FIELD BOX IS AT LEAST `tanh` OF THE LOCAL FIELD**,
as an integral against `isingMeasure` itself. -/
theorem boxField_le_integral [NeZero n] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (p₀ : Site n) :
    tanh (boxField n β h p₀)
      ≤ ∫ σ, IsingTransfer2D.spin (σ p₀) ∂(isingMeasure n h β) := by
  have hb := prod_tanh_le_expect (boxSet n) (boxCoup n β h) (boxField n β h) (boxFieldCoup n β h)
    (isSiteField_boxField n β h) (boxFieldCoup_nonneg hβ hh) (boxFieldCoup_le_boxCoup hβ) {p₀}
  rw [Finset.prod_singleton, num_eq_sum n β h p₀, part_eq_partition n β h] at hb
  rw [isingMeasure]
  exact FiniteGibbsSum.le_integral_gibbs_count β (isingHB n h) _ hb

/-- On the boundary the bound is `tanh (β·h)`. -/
theorem tanh_le_integral_boundary [NeZero n] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) {p₀ : Site n}
    (hp₀ : isBoundary p₀) :
    tanh (β * h) ≤ ∫ σ, IsingTransfer2D.spin (σ p₀) ∂(isingMeasure n h β) := by
  have h₁ := boxField_le_integral β h hβ hh p₀
  rwa [boxField, if_pos hp₀] at h₁

/-- **AND INSIDE, THIS ROUTE GIVES EXACTLY `0`** — `tanh 0`, because the comparison model has no
field there. Recorded as a theorem rather than as a remark, because it is the reason the route
cannot reach a bound proportional to the area of the box. -/
theorem zero_le_integral_interior [NeZero n] (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) {p₀ : Site n}
    (hp₀ : ¬ isBoundary p₀) :
    (0 : ℝ) ≤ ∫ σ, IsingTransfer2D.spin (σ p₀) ∂(isingMeasure n h β) := by
  have h₁ := boxField_le_integral β h hβ hh p₀
  rwa [boxField, if_neg hp₀, Real.tanh_zero] at h₁

end

end IsingBoxInteraction
