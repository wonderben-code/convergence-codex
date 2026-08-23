/-
  IsingSlabUniformBound.lean — leg (i), and with it a lower bound on this estate's own slab
  magnetisation that is UNIFORM IN THE VOLUME.

  WHY. `IsingGriffithsMono` named three legs; `IsingIndependentSpins` did (ii) and (iii) and said in
  its header that until leg (i) exists **it proves nothing about the slab**. Leg (i) is: exhibit the
  slab's couplings as a dominated pair — the field terms kept, the intra and length-bond terms
  zeroed — and check the zeroed model's energy really is a uniform field. **This is that check, and
  then the assembly.**

  WHAT COMES OUT. **`tanh_le_expectG_slab`**: for `0 ≤ β`, `0 ≤ h`, `0 ≤ Ja`, `0 ≤ Jb` and a slab of
  at least two slices,

      `tanh (β · h) ≤ ⟨σ_{v₀}⟩`

  **at every site, every cross-section and every length** — and `tanh (β·h)` does not depend on any
  of them. `expectG_slab_ge_of_pos` is the strict form. This is the first bound in this estate on a
  magnetisation that survives the volume growing; every earlier attempt failed because some factor
  grew with the boundary, and the reason none grows here is that the cardinality cancels in
  `IsingIndependentSpins.expect_eq_tanh` rather than being estimated.

  WHAT IT IS NOT, AND THIS MUST BE READ BEFORE THE ITEM IT LOOKS LIKE IT CLOSES. The field is FIXED
  and strictly positive; the bound degenerates to `0` as `h → 0`, since `tanh 0 = 0`. **So this is
  not spontaneous magnetisation and not symmetry breaking**, which need the field switched off after
  the volume grows. What it IS is a magnetisation bound at fixed finite `h`, uniform in the box —
  which is the shape `IsingBoundaryField.MagnetisationBound` asks for, for the BULK-field model.
  Whether it is that statement for the estate's own boundary-field model is a separate question and
  is not settled here.

  THE TWO TRANSPORTS ARE THE ONLY REAL WORK. `IsingIndependentSpins` speaks about `num`/`part` on a
  site set; `expectG` speaks about a path of cross-sections. `num_eq_slab` and `part_eq_slab` are
  the same `pathEquiv` re-indexing `IsingSlabGriffiths.expectG_nonneg` performs, run once each on
  the numerator and the denominator, and both go through `energy_eq`, which is where `1 ≤ M` enters
  and the only place it does.

  ADDENDUM 2026-08-23, SAME DAY — **THE BOUND IS NOT ONLY ABOUT THE MAGNETISATION.**
  `IsingIndependentSpins` was generalised from a one-site observable to an arbitrary set the same
  day, so `tanh_pow_le_expectG_slab` now gives `⟨∏_{v ∈ A} σ_v⟩ ≥ (tanh (β·h))^{|A|}` for any set
  `A` of sites in one cross-section — **a lower bound on the two-point function at `|A| = 2`, on the
  four-point function at `|A| = 4`, and so on, depending on `|A|` and the field and on nothing
  else**: not on the separation of the sites, and not on the size of the slab.
  `tanh_le_expectG_slab` is the `|A| = 1` instance. `prod_layerZero` and `card_layerZero` are the
  only new plumbing: the observable set inside the space-time site set is `{0} ×ˢ A`, whose product
  of spins is `A`'s product on layer `0` and whose cardinality is `A`'s.

  **THIS SAYS NOTHING ABOUT DECAY**, and the direction is worth stating because it is the opposite
  of what the estate's other two-point work is about. A LOWER bound that does not decrease with
  separation is not in tension with exponential decay of the CONNECTED function: at `h > 0` the
  connected two-point function is `⟨σ_uσ_v⟩ − ⟨σ_u⟩⟨σ_v⟩`, and the bound here is on the unconnected
  one, whose limit at large separation is the square of the magnetisation and not zero. Nothing here
  bounds a connected correlation in either direction.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingIndependentSpins
import IsingSlabFerro

namespace IsingSlabUniformBound

open Finset Real
open IsingTransfer2D IsingSlabTransfer IsingSlabConfig IsingSlabField IsingSlabAniso
open IsingGriffiths IsingGriffithsMono IsingIndependentSpins
open IsingSlabGriffiths IsingSlabFerro

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {K : Type*} [Fintype K]

/-! ## 1. The dominated pair -/

/-- The slab's couplings with everything but the field switched off. -/
def fieldCoup (M : ℕ) (V K : Type*) (β h : ℝ) : Idx M V K → ℝ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => β * h
  | Sum.inr (Sum.inr _) => 0

omit [Fintype V] [DecidableEq V] [Fintype K] in
theorem fieldCoup_nonneg {M : ℕ} {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h) :
    ∀ i : Idx M V K, 0 ≤ fieldCoup M V K β h i := by
  rintro (p | p | p) <;> simp [fieldCoup, mul_nonneg hβ hh]

omit [Fintype V] [DecidableEq V] [Fintype K] in
/-- **AND IT IS DOMINATED BY THE REAL ONE**, term by term, exactly when `β`, `h` and the intra
couplings are non-negative. -/
theorem fieldCoup_le_coup {M : ℕ} {β h : ℝ} (hβ : 0 ≤ β) {c : K → ℝ} (hc : ∀ k, 0 ≤ c k) :
    ∀ i : Idx M V K, fieldCoup M V K β h i ≤ coup M β h c i := by
  rintro (⟨j, k⟩ | ⟨j, v⟩ | ⟨j, v⟩)
  · exact mul_nonneg hβ (hc k)
  · exact le_refl _
  · exact hβ

/-- **AND THE ZEROED MODEL'S ENERGY IS A UNIFORM FIELD OF STRENGTH `β·h`** — the hypothesis
`IsingIndependentSpins` runs on. Two of the three interaction families vanish because their
couplings are `0`; the third is the singletons `{(j,v)}`, one per space-time site. -/
theorem isUniformField_fieldCoup (M : ℕ) (B : K → Finset V) (β h : ℝ) :
    IsUniformField (sset M B) (fieldCoup M V K β h) (β * h) := by
  intro τ
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [fieldCoup, zero_mul, Finset.sum_const_zero, zero_add, add_zero]
  rw [← Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun p _ => ?_)
  have hp : sset M B (Sum.inr (Sum.inl p)) = {p} := rfl
  rw [hp, Finset.prod_singleton]

/-! ## 2. The two transports -/

omit [Fintype V] [DecidableEq V] [Fintype K] in
/-- The observable set on layer `0`: `{0} ×ˢ A` inside the space-time site set, whose cardinality is
`A`'s and whose product of spins is `A`'s product on layer `0`. -/
theorem prod_layerZero (M : ℕ) (A : Finset V) (τ : (Fin (M + 1) × V) → Bool) :
    ∏ w ∈ ({(0 : Fin (M + 1))} : Finset (Fin (M + 1))) ×ˢ A, spin (τ w)
      = ∏ v ∈ A, spin (τ ((0 : Fin (M + 1)), v)) := by
  rw [Finset.prod_product, Finset.prod_singleton]

omit [Fintype V] [DecidableEq V] [Fintype K] in
theorem card_layerZero (M : ℕ) (A : Finset V) :
    ((({(0 : Fin (M + 1))} : Finset (Fin (M + 1))) ×ˢ A).card) = A.card := by
  rw [Finset.card_product, Finset.card_singleton, one_mul]

theorem num_eq_slab {M : ℕ} (hM : 1 ≤ M) (β h : ℝ) (c : K → ℝ) (B : K → Finset V)
    (A : Finset V) :
    num (sset M B) (coup M β h c) (({(0 : Fin (M + 1))} : Finset (Fin (M + 1))) ×ˢ A)
      = ∑ s : Fin (M + 1) → Cross V, (∏ v ∈ A, spin (s 0 v))
          * exp (β * energyG (fun σ => intraOf c B σ + fieldE h σ) M s) := by
  refine (Fintype.sum_equiv (pathEquiv M V)
    (fun s : Fin (M + 1) → Cross V => (∏ v ∈ A, spin (s 0 v))
      * exp (β * energyG (fun σ => intraOf c B σ + fieldE h σ) M s))
    (fun τ : (Fin (M + 1) × V) → Bool =>
      (∏ w ∈ ({(0 : Fin (M + 1))} : Finset (Fin (M + 1))) ×ˢ A, spin (τ w))
        * exp (∑ i : Idx M V K, coup M β h c i * ∏ w ∈ sset M B i, spin (τ w)))
    fun s => ?_).symm
  simp only [prod_layerZero, pathEquiv_apply]
  rw [energy_eq hM β h c B s]

theorem part_eq_slab {M : ℕ} (hM : 1 ≤ M) (β h : ℝ) (c : K → ℝ) (B : K → Finset V) :
    part (sset M B) (coup M β h c) = partitionG β (fun σ => intraOf c B σ + fieldE h σ) M := by
  rw [partitionG]
  refine (Fintype.sum_equiv (pathEquiv M V)
    (fun s : Fin (M + 1) → Cross V =>
      exp (β * energyG (fun σ => intraOf c B σ + fieldE h σ) M s))
    (fun τ : (Fin (M + 1) × V) → Bool =>
      exp (∑ i : Idx M V K, coup M β h c i * ∏ w ∈ sset M B i, spin (τ w)))
    fun s => ?_).symm
  dsimp only [pathEquiv_apply]
  rw [energy_eq hM β h c B s]

/-! ## 3. The bound, for an abstract slab -/

/-- **`tanh (β·h)` IS A LOWER BOUND ON THE SLAB MAGNETISATION, AND IT DOES NOT KNOW HOW BIG THE SLAB
IS.** Every hypothesis is `≤`: the bound is `0` at `β·h = 0`, which is exactly right, since the
magnetisation is `0` there. -/
theorem tanh_pow_le_expectG {M : ℕ} (hM : 1 ≤ M) {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {c : K → ℝ} (hc : ∀ k, 0 ≤ c k) (B : K → Finset V) (A : Finset V) :
    tanh (β * h) ^ A.card
      ≤ expectG β (fun σ => intraOf c B σ + fieldE h σ) M (fun σ => ∏ v ∈ A, spin (σ v)) := by
  have h₁ := tanh_pow_le_expect (sset M B) (coup M β h c) (β * h) (fieldCoup M V K β h)
    (isUniformField_fieldCoup M B β h) (fieldCoup_nonneg hβ hh) (fieldCoup_le_coup hβ hc)
    ((({(0 : Fin (M + 1))} : Finset (Fin (M + 1))) ×ˢ A))
  rw [num_eq_slab hM β h c B A, part_eq_slab hM β h c B, card_layerZero] at h₁
  rw [expectG]
  exact h₁

/-- The magnetisation case, `|A| = 1`. -/
theorem tanh_le_expectG {M : ℕ} (hM : 1 ≤ M) {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {c : K → ℝ} (hc : ∀ k, 0 ≤ c k) (B : K → Finset V) (v₀ : V) :
    tanh (β * h) ≤ expectG β (fun σ => intraOf c B σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  have h₁ := tanh_pow_le_expectG hM hβ hh hc B {v₀}
  rw [Finset.card_singleton, pow_one] at h₁
  simpa using h₁

/-! ## 4. The bound, for this estate's own slab -/

variable {a b : ℕ}

/-- **THE MAGNETISATION OF THIS ESTATE'S THREE-DIMENSIONAL ISING SLAB IN A FIELD IS AT LEAST
`tanh (β·h)`, AT EVERY SITE, EVERY CROSS-SECTION AND EVERY LENGTH.** -/
theorem tanh_le_expectG_slab {M : ℕ} (hM : 1 ≤ M) {β h Ja Jb : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hJa : 0 ≤ Ja) (hJb : 0 ≤ Jb) (v₀ : Fin (a + 1) × Fin (b + 1)) :
    tanh (β * h)
      ≤ expectG β (fun σ => slabIntraAniso Ja Jb σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  have hE : (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => slabIntraAniso Ja Jb σ + fieldE h σ)
      = fun σ => intraOf (bondCoup a b Ja Jb) (bondSet a b) σ + fieldE h σ := by
    funext σ
    rw [slabIntraAniso_eq_intraOf Ja Jb σ]
  rw [hE]
  exact tanh_le_expectG hM hβ hh (bondCoup_nonneg hJa hJb) (bondSet a b) v₀

/-- **AND THE SAME FOR EVERY CORRELATION FUNCTION OF THE SLAB, NOT ONLY THE MAGNETISATION.** For a
set `A` of sites in one cross-section, `⟨∏_{v ∈ A} σ_v⟩ ≥ (tanh (β·h))^{|A|}` — a lower bound on the
two-point function at `|A| = 2`, on the four-point function at `|A| = 4`, and so on. **The bound
depends on `|A|` and on the field, and on nothing else**: not on how far apart the sites are, and
not on how large the slab is. -/
theorem tanh_pow_le_expectG_slab {M : ℕ} (hM : 1 ≤ M) {β h Ja Jb : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hJa : 0 ≤ Ja) (hJb : 0 ≤ Jb) (A : Finset (Fin (a + 1) × Fin (b + 1))) :
    tanh (β * h) ^ A.card
      ≤ expectG β (fun σ => slabIntraAniso Ja Jb σ + fieldE h σ) M
          (fun σ => ∏ v ∈ A, spin (σ v)) := by
  have hE : (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => slabIntraAniso Ja Jb σ + fieldE h σ)
      = fun σ => intraOf (bondCoup a b Ja Jb) (bondSet a b) σ + fieldE h σ := by
    funext σ
    rw [slabIntraAniso_eq_intraOf Ja Jb σ]
  rw [hE]
  exact tanh_pow_le_expectG hM hβ hh (bondCoup_nonneg hJa hJb) (bondSet a b) A

/-- The isotropic case, the slab the rest of the estate uses. -/
theorem tanh_le_expectG_slab_iso {M : ℕ} (hM : 1 ≤ M) {β h : ℝ} (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (v₀ : Fin (a + 1) × Fin (b + 1)) :
    tanh (β * h) ≤ expectG β (fun σ => slabIntra σ + fieldE h σ) M (fun σ => spin (σ v₀)) := by
  have hE : (fun σ : Cross (Fin (a + 1) × Fin (b + 1)) => slabIntra σ + fieldE h σ)
      = fun σ => slabIntraAniso 1 1 σ + fieldE h σ := by
    funext σ
    rw [slabIntraAniso_one_one]
  rw [hE]
  exact tanh_le_expectG_slab hM hβ hh zero_le_one zero_le_one v₀

/-- And the bound is strictly positive as soon as the field is on at a finite temperature — which
is `IsingSlabStrict.expectG_slab_pos` again, but now with a NUMBER on the left instead of `0`. -/
theorem expectG_slab_ge_of_pos {M : ℕ} (hM : 1 ≤ M) {β h Ja Jb : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (hJa : 0 ≤ Ja) (hJb : 0 ≤ Jb) (v₀ : Fin (a + 1) × Fin (b + 1)) :
    0 < expectG β (fun σ => slabIntraAniso Ja Jb σ + fieldE h σ) M (fun σ => spin (σ v₀)) :=
  lt_of_lt_of_le (tanh_pos_of_pos (mul_pos hβ hh))
    (tanh_le_expectG_slab hM hβ.le hh.le hJa hJb v₀)

end

end IsingSlabUniformBound
