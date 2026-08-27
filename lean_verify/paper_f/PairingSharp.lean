import PairingParity

/-!
# Using the second crossing: the bound goes quadratic

`PairingParity.two_le_card_cross` says a pairing that crosses an even-sized group crosses
**twice**. Knowing two crossings exist is not the same as being able to use them: the two factors
have to be located **in the representative set**, which keeps one index out of each pair and not
the one the caller would choose. This file does that, and the bound becomes `ε²·M^(r−2)` —
recovering at order four the exponent `LatticeFourPointClustering.connected_smeared_le` has always
had, and giving it at every order.

## The one real step

`crossSet σ S R` is the set of representative indices whose factor crosses the split.
**`card_crossSet` is the content**: it has exactly as many elements as there are crossing pairs,
by a bijection that sends a representative to whichever end of its pair lies in `S` — `i` itself
when `i ∈ S`, and `σ i` when it is not. Its inverse sends a crossing pair's `S` end back to
whichever of the two the representative set kept. **Both directions have to consult `IsRepSet`**,
because neither map is "the obvious one" on both branches.

## What is proved

* `crossSet`, `mem_crossSet_iff` — the set and its membership;
* **`card_crossSet`** — it is equinumerous with the crossing pairs;
* `abs_le_of_mem_crossSet` — a representative in it has `|w i (σ i)| ≤ ε`, which needs the
  symmetry of `w` on the branch where the representative is the end OUTSIDE `S`. **It does not
  need `σ` to be a perfect matching**: a first draft asked for that and the build said the
  hypothesis was unused, so it was removed rather than silenced;
* **`abs_prod_le_sq_of_not_respects`** — the quadratic bound.

## What is NOT here

The measure. Carrying this up to `∫ ∏ᵢ⟪aᵢ,ω⟫` is `PairingCluster`'s and
`LatticeTruncatedDecay`'s route with `abs_prod_le_sq_of_not_respects` in place of
`PairingBound.abs_prod_le_of_not_respects`, and is **not done here**. **Not costed**
(`ERRATUM 194`).
-/

namespace PairingSharp

open Equiv Function Involutions PairWeightRep PairingSplit PairingBound PairingParity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The representatives whose factor crosses -/

/-- The representative indices whose pair straddles the split. -/
def crossSet (σ : Equiv.Perm ι) (S R : Finset ι) : Finset ι :=
  R.filter (fun i => ¬ (i ∈ S ↔ σ i ∈ S))

omit [Fintype ι] in
theorem mem_crossSet_iff {σ : Equiv.Perm ι} {S R : Finset ι} {i : ι} :
    i ∈ crossSet σ S R ↔ i ∈ R ∧ ¬ (i ∈ S ↔ σ i ∈ S) := by
  simp [crossSet, Finset.mem_filter]

omit [Fintype ι] in
/-- **AS MANY REPRESENTATIVES CROSS AS THERE ARE CROSSING PAIRS.** The bijection sends a
representative to whichever end of its pair lies in `S`, and its inverse sends that end back to
whichever end the representative set kept — neither map is the identity on both branches, and
both consult `IsRepSet`. -/
theorem card_crossSet {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι) {S R : Finset ι}
    (hR : IsRepSet σ R) :
    (crossSet σ S R).card = (S.filter (fun i => σ i ∉ S)).card := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  have hne : ∀ i, σ i ≠ i := hσ.2
  refine Finset.card_bij' (fun i _ => if i ∈ S then i else σ i)
    (fun s _ => if s ∈ R then s else σ s) ?_ ?_ ?_ ?_
  · intro i hi
    dsimp only
    rw [mem_crossSet_iff] at hi
    by_cases hiS : i ∈ S
    · have hσi : σ i ∉ S := fun h => hi.2 (iff_of_true hiS h)
      simp [hiS, Finset.mem_filter, hσi]
    · have hσi : σ i ∈ S := by
        by_contra h; exact hi.2 (iff_of_false hiS h)
      simp [hiS, Finset.mem_filter, hσi, hinv i]
  · intro s hs
    dsimp only
    simp only [Finset.mem_filter] at hs
    by_cases hsR : s ∈ R
    · rw [if_pos hsR, mem_crossSet_iff]
      exact ⟨hsR, fun h => hs.2 (h.mp hs.1)⟩
    · have hσs : σ s ∈ R := by
        by_contra h; exact hsR ((hR.2 s (hne s)).mpr h)
      rw [if_neg hsR, mem_crossSet_iff]
      refine ⟨hσs, fun h => hs.2 ?_⟩
      rw [hinv s] at h
      exact h.mpr hs.1
  · intro i hi
    dsimp only
    rw [mem_crossSet_iff] at hi
    by_cases hiS : i ∈ S
    · rw [if_pos hiS, if_pos hi.1]
    · have hσiR : σ i ∉ R := (hR.2 i (hne i)).mp hi.1
      rw [if_neg hiS, if_neg hσiR, hinv i]
  · intro s hs
    dsimp only
    simp only [Finset.mem_filter] at hs
    by_cases hsR : s ∈ R
    · rw [if_pos hsR, if_pos hs.1]
    · have hσs : σ s ∉ S := hs.2
      rw [if_neg hsR, if_neg hσs, hinv s]

/-! ## 2. A crossing representative's factor is small -/

omit [Fintype ι] in
/-- On the branch where the representative is the end OUTSIDE `S`, the hypothesis is about the
factor written the other way round, and the symmetry of `w` is what closes the gap. -/
theorem abs_le_of_mem_crossSet {σ : Equiv.Perm ι}
    {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i) {S R : Finset ι} {ε : ℝ}
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |w i j| ≤ ε) {i : ι} (hi : i ∈ crossSet σ S R) :
    |w i (σ i)| ≤ ε := by
  rw [mem_crossSet_iff] at hi
  by_cases hiS : i ∈ S
  · have hσi : σ i ∉ S := fun h => hi.2 (iff_of_true hiS h)
    exact hcross i hiS (σ i) hσi
  · have hσi : σ i ∈ S := by
      by_contra h; exact hi.2 (iff_of_false hiS h)
    rw [hw i (σ i)]
    exact hcross (σ i) hσi i hiS

/-! ## 3. The quadratic bound -/

omit [Fintype ι] [DecidableEq ι] in
/-- **THE BOUND GOES QUADRATIC.** Two representative factors cross, not one, so two are bounded by
`ε` and the remaining `r − 2` by `M`. At order four with `|S| = 2` this is the exponent
`LatticeFourPointClustering.connected_smeared_le` has always had; here it holds at every order. -/
theorem abs_prod_le_sq_of_not_respects {σ : Equiv.Perm ι} (hσ : σ ∈ perfectMatchings ι)
    {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i) {S R : Finset ι} (hR : IsRepSet σ R)
    {ε M : ℝ} (hM0 : 0 ≤ M)
    (hcross : ∀ i ∈ S, ∀ j ∉ S, |w i j| ≤ ε) (hall : ∀ i j, |w i j| ≤ M)
    (hS : Even S.card) (hns : ¬ RespectsSplit S σ) :
    |∏ i ∈ R, w i (σ i)| ≤ ε ^ 2 * M ^ (R.card - 2) := by
  classical
  have hinv : Function.Involutive σ := hσ.1
  -- the crossing pairs are nonempty, because the matching does not respect the split
  have hne : (S.filter (fun i => σ i ∉ S)).Nonempty := by
    rw [RespectsSplit, not_forall] at hns
    obtain ⟨i, hi⟩ := hns
    by_cases him : i ∈ S
    · exact ⟨i, Finset.mem_filter.mpr ⟨him, fun h => hi (iff_of_true h him)⟩⟩
    · have hσim : σ i ∈ S := by
        by_contra h; exact hi (iff_of_false h him)
      exact ⟨σ i, Finset.mem_filter.mpr ⟨hσim, by rw [hinv i]; exact him⟩⟩
  -- so there are two of them, and two representatives carry them
  have h2 : 2 ≤ (crossSet σ S R).card := by
    rw [card_crossSet hσ hR]
    exact two_le_card_cross hσ hS hne
  obtain ⟨i₀, hi₀, i₁, hi₁, hne01⟩ := Finset.one_lt_card.mp (by omega : 1 < (crossSet σ S R).card)
  have hi₀R : i₀ ∈ R := (mem_crossSet_iff.mp hi₀).1
  have hi₁R : i₁ ∈ R := (mem_crossSet_iff.mp hi₁).1
  have hi₀ε : |w i₀ (σ i₀)| ≤ ε := abs_le_of_mem_crossSet hw hcross hi₀
  have hi₁ε : |w i₁ (σ i₁)| ≤ ε := abs_le_of_mem_crossSet hw hcross hi₁
  have hε0 : 0 ≤ ε := le_trans (abs_nonneg _) hi₀ε
  have hi₁' : i₁ ∈ R.erase i₀ := Finset.mem_erase.mpr ⟨Ne.symm hne01, hi₁R⟩
  -- split the two crossing factors off and bound the rest
  have hrest : |∏ i ∈ (R.erase i₀).erase i₁, w i (σ i)| ≤ M ^ (R.card - 2) :=
    calc |∏ i ∈ (R.erase i₀).erase i₁, w i (σ i)|
        = ∏ i ∈ (R.erase i₀).erase i₁, |w i (σ i)| := Finset.abs_prod _ _
      _ ≤ ∏ _i ∈ (R.erase i₀).erase i₁, M :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hall i (σ i))
      _ = M ^ ((R.erase i₀).erase i₁).card := by rw [Finset.prod_const]
      _ = M ^ (R.card - 2) := by
          rw [Finset.card_erase_of_mem hi₁', Finset.card_erase_of_mem hi₀R]
          congr 1
  rw [← Finset.prod_erase_mul R _ hi₀R, ← Finset.prod_erase_mul (R.erase i₀) _ hi₁',
    abs_mul, abs_mul]
  calc |∏ i ∈ (R.erase i₀).erase i₁, w i (σ i)| * |w i₁ (σ i₁)| * |w i₀ (σ i₀)|
      ≤ M ^ (R.card - 2) * ε * ε := by
        refine mul_le_mul (mul_le_mul hrest hi₁ε (abs_nonneg _) (pow_nonneg hM0 _)) hi₀ε
          (abs_nonneg _) ?_
        exact mul_nonneg (pow_nonneg hM0 _) hε0
    _ = ε ^ 2 * M ^ (R.card - 2) := by ring

end PairingSharp
