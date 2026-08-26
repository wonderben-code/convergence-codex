/-
  IsingSlabTopRatio.lean — the sub-top ratio at an arbitrary cross-section, and
  `WALLS` §W4 §6 item 3 stated in three dimensions.

  WHY. Six units carried the whole strip decay chain to an arbitrary finite
  cross-section, ending in `IsingSlabLimit.slab_corr2Sep_decay`. Every one of them
  left `IsingTopRatio` alone — and `IsingTopRatio` is where the WALL lives.
  `UniformSubTopRatio` is `WALLS` §W4 §6 item 3, it is a statement about a family
  of `Col n`s indexed by the WIDTH, and there was no way to say it about a family
  of cross-sections. **A wall that cannot be stated in the dimension one cares
  about is worse than one that can**, and this file fixes that and nothing else.

  WHAT IS PROVED. `topIndexG`, `subTopRatioG` and its four laws — the defining
  bound, non-negativity, `< 1` at every cross-section and every `β`, and that it
  is `IsingSlabDecay.exists_subTopRatioG`'s witness (`ERRATUM 201`); then
  `corr2SepInfG_abs_le_subTopRatioG`, the decay bound with the rate NAMED rather
  than existentially quantified; then `UniformSubTopRatioFam` for an arbitrary
  indexed family of cross-sections, `decay_uniform_of_uniformSubTopRatioFam`, and
  **`UniformSubTopRatioSlab`** — the wall, in three dimensions, for the first
  time.

  AND THE `β = 0` CASE, SO THE TARGET IS KNOWN TO BE SATISFIABLE. At `β = 0`
  every entry of `transferG 0 E` is `1` **for every `E`** — the energy is
  multiplied by `β` and disappears — so the matrix is all-ones, squares to
  `card (Cross V)` times itself, and `IsingTopRatioZero.eigenvalues_sq_eq_of_mul_self`
  gives an eigenvalue list of one positive value and zeros.
  `uniformSubTopRatioSlab_zero` follows with `δ = 1`.

  WHAT IS NOT PROVED, AND IT IS THE ITEM. Nothing here says anything about
  `β ≠ 0`, in any dimension. `β = 0` is the degenerate case where the matrix has
  rank one and non-interacting spins do not correlate; read the other way it is a
  filter on strategies — **an argument that would also work at `β = 0` is not yet
  doing the work.** That sentence is `IsingTopRatio`'s and is inherited verbatim,
  because generalising the statement changed nothing about its difficulty.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import IsingSlabLimit
import IsingTopRatioZero

namespace IsingSlabTopRatio

open Finset Matrix Real
open IsingTransfer2D IsingTransferSym IsingTopRatio IsingTopRatioZero
open IsingSlabTransfer IsingSlabFlip IsingSlabMagnetisation IsingSlabDecay

open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. The top index -/

/-- **THE INDEX OF THE LARGEST EIGENVALUE** of the symmetrised transfer matrix, at an arbitrary
cross-section. -/
noncomputable def topIndexG (β : ℝ) (E : Cross V → ℝ) : Cross V :=
  (Finite.exists_max (transferG_isHermitian β E).eigenvalues).choose

theorem topIndexG_max (β : ℝ) (E : Cross V → ℝ) (j : Cross V) :
    (transferG_isHermitian β E).eigenvalues j
      ≤ (transferG_isHermitian β E).eigenvalues (topIndexG β E) :=
  (Finite.exists_max (transferG_isHermitian β E).eigenvalues).choose_spec j

theorem topIndexG_pos (β : ℝ) (E : Cross V → ℝ) :
    0 < (transferG_isHermitian β E).eigenvalues (topIndexG β E) :=
  PerronGap.eigenvalue_max_pos _ (transferG_pos β E) (topIndexG_max β E)

omit [Fintype V] [DecidableEq V] in
/-- The flip of a configuration is never that configuration, provided the cross-section has a
site. This is what makes §2's maximum a maximum of something, and `[Nonempty V]` is exactly the
hypothesis it needs: an empty cross-section gives a ONE-element `Cross V` (`ERRATUM 48`). -/
theorem flipCross_ne [Nonempty V] (σ : Cross V) : flipCross σ ≠ σ := by
  obtain ⟨w⟩ := ‹Nonempty V›
  intro h
  have hw := congrFun h w
  cases hb : σ w <;> rw [flipCross, hb] at hw <;> simp at hw

theorem erase_topIndexG_nonempty [Nonempty V] (β : ℝ) (E : Cross V → ℝ) :
    (univ.erase (topIndexG β E)).Nonempty :=
  ⟨flipCross (topIndexG β E),
    Finset.mem_erase.mpr ⟨flipCross_ne (topIndexG β E), mem_univ _⟩⟩

/-! ## 2. The sub-top ratio

`IsingSlabDecay.exists_subTopRatioG` asserts this number to exist; here it is written down. A
`Finset.sup'` rather than an `iSup`, so that it is attained and no completeness argument enters. -/

/-- **THE LARGEST EIGENVALUE RATIO OFF THE TOP INDEX**, at an arbitrary cross-section. -/
noncomputable def subTopRatioG [Nonempty V] (β : ℝ) (E : Cross V → ℝ) : ℝ :=
  (univ.erase (topIndexG β E)).sup' (erase_topIndexG_nonempty β E) fun q =>
    |(transferG_isHermitian β E).eigenvalues q
      / (transferG_isHermitian β E).eigenvalues (topIndexG β E)|

theorem le_subTopRatioG [Nonempty V] (β : ℝ) (E : Cross V → ℝ) {q : Cross V}
    (hq : q ≠ topIndexG β E) :
    |(transferG_isHermitian β E).eigenvalues q
      / (transferG_isHermitian β E).eigenvalues (topIndexG β E)| ≤ subTopRatioG β E :=
  Finset.le_sup' (fun q => |(transferG_isHermitian β E).eigenvalues q
    / (transferG_isHermitian β E).eigenvalues (topIndexG β E)|)
    (Finset.mem_erase.mpr ⟨hq, mem_univ q⟩)

theorem subTopRatioG_nonneg [Nonempty V] (β : ℝ) (E : Cross V → ℝ) : 0 ≤ subTopRatioG β E := by
  obtain ⟨q, hq⟩ := erase_topIndexG_nonempty β E
  exact le_trans (abs_nonneg _) (le_subTopRatioG β E (Finset.mem_erase.mp hq).1)

/-- **THE PERRON GAP, AS A STATEMENT ABOUT A NAMED NUMBER**, at every cross-section and every `β`.
Read §4 before reading a limit into this: the quantifier order is the whole item. -/
theorem subTopRatioG_lt_one [Nonempty V] (β : ℝ) (E : Cross V → ℝ) : subTopRatioG β E < 1 := by
  have hpos : ∀ a b : Cross V, 0 < transferG β E a b := transferG_pos β E
  have hrfl : subTopRatioG β E
      = (univ.erase (topIndexG β E)).sup' (erase_topIndexG_nonempty β E) fun q =>
        |(transferG_isHermitian β E).eigenvalues q
          / (transferG_isHermitian β E).eigenvalues (topIndexG β E)| := rfl
  rw [hrfl, Finset.sup'_lt_iff]
  intro q hq
  have hqne : q ≠ topIndexG β E := (Finset.mem_erase.mp hq).1
  have hvne : (transferG_isHermitian β E).eigenvalues q
      ≠ (transferG_isHermitian β E).eigenvalues (topIndexG β E) := fun h =>
    hqne (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ hpos (topIndexG_max β E) h)
  rw [abs_div, abs_of_pos (topIndexG_pos β E), div_lt_one (topIndexG_pos β E)]
  exact PerronGap.abs_eigenvalues_lt_of_ne _ hpos (topIndexG_max β E) hvne

/-- **AND IT IS THE EXISTENTIAL'S WITNESS**, so the name and
`IsingSlabDecay.exists_subTopRatioG` are one fact and not two (`ERRATUM 201`). -/
theorem subTopRatioG_isWitness [Nonempty V] (β : ℝ) (E : Cross V → ℝ) :
    0 ≤ subTopRatioG β E ∧ subTopRatioG β E < 1 ∧ ∀ q ∈ univ.erase (topIndexG β E),
      |(transferG_isHermitian β E).eigenvalues q
        / (transferG_isHermitian β E).eigenvalues (topIndexG β E)| ≤ subTopRatioG β E :=
  ⟨subTopRatioG_nonneg β E, subTopRatioG_lt_one β E,
    fun _ hq => le_subTopRatioG β E (Finset.mem_erase.mp hq).1⟩

/-! ## 3. The decay bound with the rate named -/

/-- **EXPONENTIAL DECAY WITH NO EXISTENTIAL IN FRONT OF THE RATE**, at every cross-section, site
and separation. The vanishing of the diagonal term is `spinEigenG_top_eq_zero`, which is where
`hE` is spent; the sum over the rest is `corr2SepInfG_connected_le_of_ratio_le` at
`r = subTopRatioG β E`. -/
theorem corr2SepInfG_abs_le_subTopRatioG [Nonempty V] {E : Cross V → ℝ}
    (hE : ∀ σ, E (flipCross σ) = E σ) (β : ℝ) (v : V) (κ : ℕ) :
    |corr2SepInfG β E v (topIndexG β E) κ| ≤ subTopRatioG β E ^ κ := by
  have h := corr2SepInfG_connected_le_of_ratio_le β E v (topIndexG_pos β E)
    (subTopRatioG_nonneg β E) (fun q hq => le_subTopRatioG β E (Finset.mem_erase.mp hq).1) κ
  rwa [spinEigenG_top_eq_zero hE β v (topIndexG_max β E), norm_zero, zero_pow (by norm_num),
    sub_zero] at h

/-! ## 4. The wall, for a family of cross-sections

`IsingTopRatio.UniformSubTopRatio` quantifies over the WIDTH, which is the only family of
cross-sections that existed when it was written. The item is about a family, so this is stated for
an arbitrary one. -/

/-- **NOT PROVED HERE FOR ANY `β ≠ 0`, AND THIS IS `WALLS` §W4 §6 item 3.** That the sub-top ratio
stays below one UNIFORMLY along a family of cross-sections: one `δ > 0` serving every member at
once.

**What separates it from `subTopRatioG_lt_one`** is only the order of two quantifiers, and that is
the entire remaining content of the item. The estate proves `∀ i, subTopRatioG β (E i) < 1`; this
asks for `∃ δ > 0, ∀ i, subTopRatioG β (E i) ≤ 1 - δ`.

**"No route is recorded, in any dimension" — the sentence that used to end this docstring — was
true when written and is not now** (2026-08-26). `SpectralEntryRatio.subTop_ratio_le` is a route
and is stated for an arbitrary finite Hermitian matrix, so it applies here with nothing to adapt;
`SlabEntryRatio.uniformSubTopRatioFam_of_entries` discharges THIS `Prop` under the hypothesis that
one interval `[a, b]` with `b² < 2a²` contains every member's entries, producing the `δ` from `a`
and `b` before any member is named. **The item still does not move**: that hypothesis fails for the
Ising family at every `β > 0`, because `transferG_apply`'s entries are exponentials of sums over
the cross-section and their ratio therefore grows with it. What is retired is the claim that
nothing had been tried. -/
def UniformSubTopRatioFam {ι : Type*} {W : ι → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] [∀ i, Nonempty (W i)] (E : ∀ i, Cross (W i) → ℝ) (β : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ i : ι, subTopRatioG β (E i) ≤ 1 - δ

/-- **AND THIS IS WHAT IT WOULD BUY**: one exponential rate valid along the whole family at once. -/
theorem decay_uniform_of_uniformSubTopRatioFam {ι : Type*} {W : ι → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] [∀ i, Nonempty (W i)] {E : ∀ i, Cross (W i) → ℝ}
    (hE : ∀ (i : ι) (σ : Cross (W i)), E i (flipCross σ) = E i σ) {β : ℝ}
    (h : UniformSubTopRatioFam E β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (i : ι) (v : W i) (κ : ℕ),
      |corr2SepInfG β (E i) v (topIndexG β (E i)) κ| ≤ (1 - δ) ^ κ := by
  obtain ⟨δ, hδ, hle⟩ := h
  refine ⟨δ, hδ, fun i v κ => le_trans (corr2SepInfG_abs_le_subTopRatioG (hE i) β v κ) ?_⟩
  exact pow_le_pow_left₀ (subTopRatioG_nonneg β (E i)) (hle i) κ

/-! ## 5. The `β = 0` case, at every cross-section at once

`IsingTopRatioZero` proves this at `Col n`. What the general statement makes visible is that the
energy plays NO part: at `β = 0` the entries are `exp 0 = 1` whatever `E` is. -/

theorem transferG_zero_apply (E : Cross V → ℝ) (σ τ : Cross V) : transferG 0 E σ τ = 1 := by
  rw [transferG_apply]; simp

theorem transferG_zero_mul_self (E : Cross V → ℝ) :
    transferG 0 E * transferG 0 E = ((Fintype.card (Cross V) : ℕ) : ℝ) • transferG 0 E := by
  ext σ τ
  simp [Matrix.mul_apply, transferG_zero_apply]

theorem eigenvaluesG_zero_eq_or (E : Cross V → ℝ) (j : Cross V) :
    (transferG_isHermitian 0 E).eigenvalues j = 0
      ∨ (transferG_isHermitian 0 E).eigenvalues j = ((Fintype.card (Cross V) : ℕ) : ℝ) := by
  have h := eigenvalues_sq_eq_of_mul_self (transferG_isHermitian 0 E)
    (transferG_zero_mul_self E) j
  have hf : (transferG_isHermitian 0 E).eigenvalues j
      * ((transferG_isHermitian 0 E).eigenvalues j - ((Fintype.card (Cross V) : ℕ) : ℝ)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hf with h0 | h0
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h0)

theorem eigenvaluesG_zero_top (E : Cross V → ℝ) :
    (transferG_isHermitian 0 E).eigenvalues (topIndexG 0 E)
      = ((Fintype.card (Cross V) : ℕ) : ℝ) := by
  rcases eigenvaluesG_zero_eq_or E (topIndexG 0 E) with h | h
  · exact absurd h (topIndexG_pos 0 E).ne'
  · exact h

theorem eigenvaluesG_zero_eq_zero_of_ne (E : Cross V → ℝ) {q : Cross V} (hq : q ≠ topIndexG 0 E) :
    (transferG_isHermitian 0 E).eigenvalues q = 0 := by
  rcases eigenvaluesG_zero_eq_or E q with h | h
  · exact h
  · exact absurd (TransferPowerSum.index_eq_of_eigenvalues_eq_top _ (transferG_pos 0 E)
      (topIndexG_max 0 E) (h.trans (eigenvaluesG_zero_top E).symm)) hq

theorem subTopRatioG_zero [Nonempty V] (E : Cross V → ℝ) : subTopRatioG 0 E = 0 := by
  refine le_antisymm ?_ (subTopRatioG_nonneg 0 E)
  have hrfl : subTopRatioG 0 E
      = (univ.erase (topIndexG 0 E)).sup' (erase_topIndexG_nonempty 0 E) fun q =>
        |(transferG_isHermitian 0 E).eigenvalues q
          / (transferG_isHermitian 0 E).eigenvalues (topIndexG 0 E)| := rfl
  rw [hrfl]
  refine Finset.sup'_le _ _ fun q hq => ?_
  rw [eigenvaluesG_zero_eq_zero_of_ne E (Finset.mem_erase.mp hq).1, zero_div, abs_zero]

/-- **THE TARGET IS SATISFIABLE ALONG EVERY FAMILY AT ONCE**, at `β = 0`, with `δ = 1`. -/
theorem uniformSubTopRatioFam_zero {ι : Type*} {W : ι → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] [∀ i, Nonempty (W i)] (E : ∀ i, Cross (W i) → ℝ) :
    UniformSubTopRatioFam E 0 :=
  ⟨1, one_pos, fun i => by rw [subTopRatioG_zero (E i)]; norm_num⟩

/-! ## 6. Both instances, and the wall in three dimensions -/

/-- The strip's top index IS the general one at `E = intra`, by `rfl`. -/
theorem topIndex_eq_topIndexG (β : ℝ) (n : ℕ) :
    topIndex β n = topIndexG β (intra (n := n)) := rfl

/-- **INSTANCE ONE — the strip**, `IsingTopRatio.corr2SepInf_abs_le_subTopRatio` recovered. -/
theorem strip_corr2SepInf_abs_le (β : ℝ) (n : ℕ) (i : Fin (n + 1)) (κ : ℕ) :
    |corr2SepInfG β (intra (n := n)) i (topIndexG β (intra (n := n))) κ|
      ≤ subTopRatioG β (intra (n := n)) ^ κ :=
  corr2SepInfG_abs_le_subTopRatioG intra_flipCross β i κ

/-- **THE WALL, IN THREE DIMENSIONS, STATED FOR THE FIRST TIME.** That the slab's sub-top ratio
stays below one uniformly as the CROSS-SECTION grows — both of its dimensions at once, since the
index is `ℕ × ℕ`. This is `WALLS` §W4 §6 item 3 in the dimension the item is about, and it is
**not proved for any `β ≠ 0`**; `uniformSubTopRatioSlab_zero` below is the whole of what is
known. -/
def UniformSubTopRatioSlab (β : ℝ) : Prop :=
  UniformSubTopRatioFam (ι := ℕ × ℕ) (W := fun p => Fin (p.1 + 1) × Fin (p.2 + 1))
    (fun p => slabIntra (a := p.1) (b := p.2)) β

/-- **AND IT IS SATISFIABLE**, at `β = 0`, with `δ = 1` — so the three-dimensional statement is not
a name attached to nothing. Nothing here says anything about `β ≠ 0`. -/
theorem uniformSubTopRatioSlab_zero : UniformSubTopRatioSlab 0 :=
  uniformSubTopRatioFam_zero _

/-- **AND THIS IS WHAT IT WOULD BUY IN THREE DIMENSIONS**: one exponential rate for the whole
family of slabs at once, rather than one rate per cross-section. -/
theorem slab_decay_uniform_of_uniform {β : ℝ} (h : UniformSubTopRatioSlab β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : ℕ × ℕ) (v : Fin (p.1 + 1) × Fin (p.2 + 1)) (κ : ℕ),
      |corr2SepInfG β (slabIntra (a := p.1) (b := p.2)) v
          (topIndexG β (slabIntra (a := p.1) (b := p.2))) κ| ≤ (1 - δ) ^ κ :=
  decay_uniform_of_uniformSubTopRatioFam (fun _ _ => slabIntra_flipCross _) h

end IsingSlabTopRatio
