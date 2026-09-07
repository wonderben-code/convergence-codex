import PlusClassVanishes
import EvenDegreesConverse

/-!
# The class the enclosure step reaches is asymptotically invisible too

`RayCircuitSurrounding` replaced `PlusBoundary` by `EvenDegrees (dualGraph σ)` in Peierls'
enclosure step, and `EvenDegreesConverse` proved that hypothesis is **exactly** *the boundary is
constant away from its four corners*. `PlusClassVanishes` is the file that closed the obvious
route to `IsingBoundaryField.MagnetisationBound`: it proves `P_h(+) → 0`, so conditioning on `+`
and paying for the complement cannot deliver a bound however good the conditional estimate is.

**The same argument applies to the new class, and this file runs it.**

> **`tendsto_classProb_zero`** — for every `β ≥ 0` and every `h`, the probability that the
> boundary is constant away from its corners tends to `0` as the box grows.

> **`evenDegrees_weight_eq_and_tendsto`** — and by `EvenDegreesConverse` that probability **is**
> the probability of `EvenDegrees (dualGraph σ)`, above `n = 2`.

So the hypothesis ten units of work put in place of `+` is asymptotically invisible in the same
limit `MagnetisationBound` is about. **Weakening `+` to the even-degree condition does not escape
`PlusClassVanishes`'s objection.**

## What is proved

**`boundaryTerm_flipAt`, `isingHB_flipAt_le_abs`** — one spin flip costs at most `16 + 2|h|`, **on
any configuration**. `PlusClassVanishes.isingHB_flipAt_le` is this with `PlusBoundary σ` assumed,
which buys the sharper `16 + 2h`; the hypothesis comes off and the field term is bounded by its
absolute value instead.

**`offCornerSites`, `three_le_card_offCornerSites`, `sub_two_le_card_offCornerSites`** — the
boundary sites that are not corners: at least three of them once `3 < n`, and at least `n - 2`.

**`not_class_flipAt`** — flipping one of them leaves the class, because another one keeps the old
value.

**`flipAt_injOn_class`** — and the flip map is injective on (site, configuration) pairs. **This is
where three sites are needed rather than two**: if `x ≠ y` gave the same image, the values at `x`
and at `y` are consistent on their own, and it takes a **third** off-corner boundary site to
produce the contradiction. `PlusClassVanishes`'s version needs no such site, because there the
image remembers `x` as its unique down boundary spin.

**`fullWeight_ge_class`, `classProb_le`, `classProb_eq_integral`, `tendsto_classProb_zero`** — the
counting argument, `PlusClassVanishes`'s §5–§6 with those four inputs swapped.

**`classWeight_eq_evenDegrees`, `evenDegrees_weight_eq_and_tendsto`** — read back onto the
even-degree condition.

## What is NOT here

**THIS DOES NOT REFUTE `MagnetisationBound`, AND IT DOES NOT REFUTE ANYTHING PROVED IN THE LAST
TEN UNITS.** Every theorem in that run is a pointwise statement about configurations satisfying a
hypothesis, and all of them stand. What is added is a fact about how much of the measure that
hypothesis carries. `PlusClassVanishes`'s own *What this does and does not say* applies here word
for word, including its labelled **guess** about the true size of the deficit, which this file does
not touch.

**THE INFERENCE "SO THE ROUTE IS CLOSED" IS `PlusClassVanishes`'S, NOT A NEW THEOREM.** That
file sets out the decomposition and reads the two terms; nothing here re-derives it for the new
class, and no theorem in this file mentions `MagnetisationBound` — a grep finds it only in this
header. **Not attempted, no cost claimed** (`ERRATUM 246`).

**NO OTHER CLASS IS EXAMINED.** Whether some hypothesis that is *not* a condition on the boundary
carries non-vanishing probability is untouched — and `RayBondsParity.no_spin_from_flip_invariant`
already says a large family of candidates cannot supply what the chain needs. The two facts point
the same way and **neither is a proof that no route exists.**

**NOTHING BELOW `n = 4`.** The counting needs three off-corner boundary sites, so every bound here
carries `3 < n`; the identification with the even-degree condition carries `2 < n`.

**W3 does not move. No wall moves. No published tag moves.**

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `boundaryTerm_flipAt` and
`isingHB_flipAt_le_abs` take **nothing at all** — no class, no `n`, no sign condition on `h`;
`classProb_le` and `fullWeight_ge_class` take **`0 ≤ β` and `3 < n`**; `tendsto_classProb_zero`
takes **`0 ≤ β`**; `classWeight_eq_evenDegrees` takes **`2 < n`**. No `PlusBoundary` anywhere.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace EvenDegreesClassVanishes

open IsingFiniteVolume IsingBoundaryField DualObstruction BoundaryFieldLimit
open PlusClassVanishes EvenDegreesBoundary EvenDegreesConverse
open MeasureTheory Filter

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. One spin flip moves the boundary term by at most two, on any configuration -/

theorem boundaryTerm_flipAt (σ : Config n) (x : Site n) :
    boundaryTerm n (flipAt σ x)
      = boundaryTerm n σ - 2 * (if isBoundary x then spin (σ x) else 0) := by
  rw [boundaryTerm, boundaryTerm, ← Finset.add_sum_erase _ _ (Finset.mem_univ x),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ x)]
  have hrest : ∑ p ∈ (Finset.univ : Finset (Site n)).erase x,
        (if isBoundary p then spin (flipAt σ x p) else 0)
      = ∑ p ∈ (Finset.univ : Finset (Site n)).erase x,
        (if isBoundary p then spin (σ p) else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [flipAt_of_ne (Finset.ne_of_mem_erase hp)]
  rw [hrest]
  by_cases hx : isBoundary x = true
  · simp only [if_pos hx]
    rw [flipAt_self, spin_not]
    ring
  · simp only [if_neg hx]
    ring

/-- **ONE SPIN FLIP COSTS AT MOST `16 + 2|h|`, ON ANY CONFIGURATION.**
`PlusClassVanishes.isingHB_flipAt_le` is this bound with `PlusBoundary σ` assumed, which buys
the sharper constant `16 + 2h`; the hypothesis is removed here and the field term is bounded by
its absolute value instead. -/
theorem isingHB_flipAt_le_abs (σ : Config n) (x : Site n) (h : ℝ) :
    isingHB n h (flipAt σ x) ≤ isingHB n h σ + (16 + 2 * |h|) := by
  set c : ℝ := (if isBoundary x = true then spin (σ x) else 0) with hcdef
  have hspin : |c| ≤ 1 := by
    rw [hcdef]
    by_cases hx : isBoundary x = true
    · rw [if_pos hx, abs_spin]
    · rw [if_neg hx, abs_zero]
      norm_num
  have hkey : h * c ≤ |h| :=
    calc h * c ≤ |h * c| := le_abs_self _
      _ = |h| * |c| := abs_mul h c
      _ ≤ |h| * 1 := mul_le_mul_of_nonneg_left hspin (abs_nonneg h)
      _ = |h| := mul_one _
  have hH := isingH_flipAt_le σ x
  rw [isingHB, isingHB, boundaryTerm_flipAt]
  have hring : h * (boundaryTerm n σ - 2 * c) = h * boundaryTerm n σ - 2 * (h * c) := by ring
  rw [← hcdef, hring]
  linarith [hH, hkey]

/-! ## 2. The boundary sites that are not corners -/

noncomputable def offCornerSites (n : ℕ) : Finset (Site n) :=
  (bdrySites n).filter (fun p => ¬ IsCorner p)

theorem mem_offCornerSites {p : Site n} :
    p ∈ offCornerSites n ↔ isBoundary p = true ∧ ¬ IsCorner p := by
  rw [offCornerSites, Finset.mem_filter, mem_bdrySites]

/-- Out of a set with more than two elements one can always avoid two named points. -/
theorem exists_ne_two {α : Type*} {s : Finset α} (h : 2 < s.card) (a b : α) :
    ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  by_contra hcon
  push Not at hcon
  have hsub : s ⊆ {a, b} := by
    intro c hc
    rcases eq_or_ne c a with rfl | hca
    · simp
    · simp [hcon c hc hca]
  have h1 := Finset.card_le_card hsub
  have h2 : ({a, b} : Finset α).card ≤ 2 := Finset.card_insert_le _ _
  omega

theorem three_le_card_offCornerSites (hn : 3 < n) : 3 ≤ (offCornerSites n).card := by
  have h0 : (0 : ℕ) < n := by omega
  have hsub : ({((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)),
      ((⟨0, by omega⟩ : Fin n), (⟨2, by omega⟩ : Fin n)),
      ((⟨1, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n))} : Finset (Site n))
      ⊆ offCornerSites n := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · refine mem_offCornerSites.mpr ⟨by simp [isBoundary], ?_⟩
      rintro ⟨-, h | h⟩
      · simp at h
      · simp at h
        omega
    · refine mem_offCornerSites.mpr ⟨by simp [isBoundary], ?_⟩
      rintro ⟨-, h | h⟩
      · simp at h
      · simp at h
        omega
    · refine mem_offCornerSites.mpr ⟨by simp [isBoundary], ?_⟩
      rintro ⟨h | h, -⟩
      · simp at h
      · simp at h
        omega
  have hcard : ({((⟨0, by omega⟩ : Fin n), (⟨1, by omega⟩ : Fin n)),
      ((⟨0, by omega⟩ : Fin n), (⟨2, by omega⟩ : Fin n)),
      ((⟨1, by omega⟩ : Fin n), (⟨0, by omega⟩ : Fin n))} : Finset (Site n)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff, Fin.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff, Fin.ext_iff]), Finset.card_singleton]
  calc 3 = _ := hcard.symm
    _ ≤ (offCornerSites n).card := Finset.card_le_card hsub

/-! ## 3. Flipping one off-corner boundary spin leaves the class, injectively -/

theorem not_class_flipAt (hn : 3 < n) {σ : Config n} (hσ : BoundaryConstOffCorner σ)
    {x : Site n} (hx : x ∈ offCornerSites n) :
    ¬ BoundaryConstOffCorner (flipAt σ x) := by
  intro hflip
  obtain ⟨y, hy, hyx, -⟩ := exists_ne_two (three_le_card_offCornerSites hn) x x
  obtain ⟨hxb, hxc⟩ := mem_offCornerSites.mp hx
  obtain ⟨hyb, hyc⟩ := mem_offCornerSites.mp hy
  have h1 : flipAt σ x x = flipAt σ x y := hflip x y hxb hxc hyb hyc
  rw [flipAt_self, flipAt_of_ne hyx, hσ x y hxb hxc hyb hyc] at h1
  exact (Bool.not_ne_self _) h1

theorem flipAt_injOn_class (hn : 3 < n) :
    ∀ z ∈ (offCornerSites n) ×ˢ
        ((Finset.univ : Finset (Config n)).filter fun σ => BoundaryConstOffCorner σ),
      ∀ w ∈ (offCornerSites n) ×ˢ
        ((Finset.univ : Finset (Config n)).filter fun σ => BoundaryConstOffCorner σ),
        flipAt z.2 z.1 = flipAt w.2 w.1 → z = w := by
  rintro ⟨x, σ⟩ hz ⟨y, ρ⟩ hw heq
  rw [Finset.mem_product] at hz hw
  obtain ⟨hxb, hxc⟩ := mem_offCornerSites.mp hz.1
  obtain ⟨hyb, hyc⟩ := mem_offCornerSites.mp hw.1
  have hσ : BoundaryConstOffCorner σ := (Finset.mem_filter.mp hz.2).2
  have hρ : BoundaryConstOffCorner ρ := (Finset.mem_filter.mp hw.2).2
  have hxy : x = y := by
    by_contra hne
    obtain ⟨z, hz3, hzx, hzy⟩ := exists_ne_two (three_le_card_offCornerSites hn) x y
    obtain ⟨hzb, hzc⟩ := mem_offCornerSites.mp hz3
    have hatx := congrFun heq x
    rw [flipAt_self, flipAt_of_ne hne] at hatx
    have hatz := congrFun heq z
    rw [flipAt_of_ne hzx, flipAt_of_ne hzy] at hatz
    dsimp only at hatx hatz
    have h1 : σ x = σ z := hσ x z hxb hxc hzb hzc
    have h2 : ρ x = ρ z := hρ x z hxb hxc hzb hzc
    have hcontra : (!σ x) = σ x := by rw [hatx, h2, ← hatz, ← h1]
    exact (Bool.not_ne_self _) hcontra
  subst hxy
  refine Prod.ext rfl ?_
  funext p
  by_cases hp : p = x
  · subst hp
    have := congrFun heq p
    rw [flipAt_self, flipAt_self] at this
    exact Bool.not_inj this
  · have := congrFun heq p
    rwa [flipAt_of_ne hp, flipAt_of_ne hp] at this

/-! ## 4. So the class is a vanishing fraction of the partition sum -/

noncomputable def classWeight (n : ℕ) (h β : ℝ) : ℝ :=
  ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => BoundaryConstOffCorner σ),
    Real.exp (-β * isingHB n h σ)

theorem classWeight_pos (n : ℕ) (h β : ℝ) : 0 < classWeight n h β := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ⟨fun _ => true, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ _ _ _ _ => rfl⟩

theorem fullWeight_ge_class (n : ℕ) (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hn : 3 < n) :
    (1 + ((offCornerSites n).card : ℝ) * Real.exp (-β * (16 + 2 * |h|))) * classWeight n h β
      ≤ fullWeight n h β := by
  set P := (Finset.univ : Finset (Config n)).filter (fun σ => BoundaryConstOffCorner σ) with hP
  set S := offCornerSites n with hS
  set T := (S ×ˢ P).image (fun z : Site n × Config n => flipAt z.2 z.1) with hT
  have hdisj : Disjoint P T := by
    refine Finset.disjoint_left.mpr fun τ hτP hτT => ?_
    obtain ⟨⟨x, σ⟩, hz, rfl⟩ := Finset.mem_image.mp hτT
    rw [Finset.mem_product] at hz
    exact not_class_flipAt hn (Finset.mem_filter.mp hz.2).2 hz.1 (Finset.mem_filter.mp hτP).2
  have hsub : P ∪ T ⊆ (Finset.univ : Finset (Config n)) := Finset.subset_univ _
  have hpw : classWeight n h β = ∑ σ ∈ P, Real.exp (-β * isingHB n h σ) := rfl
  have hstep1 : (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
      + ∑ τ ∈ T, Real.exp (-β * isingHB n h τ) ≤ fullWeight n h β := by
    rw [← Finset.sum_union hdisj, fullWeight]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => (Real.exp_pos _).le
  have hstep2 : ∑ τ ∈ T, Real.exp (-β * isingHB n h τ)
      = ∑ z ∈ S ×ˢ P, Real.exp (-β * isingHB n h (flipAt z.2 z.1)) :=
    Finset.sum_image (flipAt_injOn_class hn)
  have hstep3 : (S.card : ℝ) * Real.exp (-β * (16 + 2 * |h|))
        * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
      ≤ ∑ z ∈ S ×ˢ P, Real.exp (-β * isingHB n h (flipAt z.2 z.1)) := by
    rw [Finset.sum_product]
    have hterm : ∀ x ∈ S, Real.exp (-β * (16 + 2 * |h|))
          * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
        ≤ ∑ σ ∈ P, Real.exp (-β * isingHB n h (flipAt σ x)) := by
      intro x _
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun σ _ => ?_
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hle := isingHB_flipAt_le_abs σ x h
      nlinarith [hle, hβ]
    calc (S.card : ℝ) * Real.exp (-β * (16 + 2 * |h|))
          * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ))
        = ∑ _x ∈ S, Real.exp (-β * (16 + 2 * |h|))
            * (∑ σ ∈ P, Real.exp (-β * isingHB n h σ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ x ∈ S, ∑ σ ∈ P, Real.exp (-β * isingHB n h (flipAt σ x)) :=
          Finset.sum_le_sum hterm
  rw [add_mul, one_mul, hpw]
  rw [hstep2] at hstep1
  linarith [hstep1, hstep3]

/-- The probability, under the boundary-field measure, that the boundary is constant away from
its four corners. -/
noncomputable def classProb (n : ℕ) (h β : ℝ) : ℝ := classWeight n h β / fullWeight n h β

/-- It is a probability in the estate's own sense: the integral of the indicator against
`isingMeasure`. -/
theorem classProb_eq_integral (n : ℕ) (h β : ℝ) :
    ∫ σ, (if BoundaryConstOffCorner σ then (1 : ℝ) else 0) ∂(isingMeasure n h β)
      = classProb n h β := by
  rw [BoundaryFieldRatio.integral_isingMeasure, classProb, classWeight, fullWeight]
  congr 1
  have hterm : ∀ σ : Config n,
      (if BoundaryConstOffCorner σ then (1 : ℝ) else 0) * Real.exp (-β * isingHB n h σ)
        = if BoundaryConstOffCorner σ then Real.exp (-β * isingHB n h σ) else 0 := by
    intro σ; by_cases hc : BoundaryConstOffCorner σ <;> simp [hc]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_filter]

theorem classProb_le (n : ℕ) (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) (hn : 3 < n) :
    classProb n h β
      ≤ 1 / (1 + ((offCornerSites n).card : ℝ) * Real.exp (-β * (16 + 2 * |h|))) := by
  have hpos := classWeight_pos n h β
  have hfull := fullWeight_pos n h β
  have hden : 0 < 1 + ((offCornerSites n).card : ℝ) * Real.exp (-β * (16 + 2 * |h|)) := by
    have : (0 : ℝ) ≤ ((offCornerSites n).card : ℝ) * Real.exp (-β * (16 + 2 * |h|)) := by
      positivity
    linarith
  rw [classProb, div_le_div_iff₀ hfull hden]
  nlinarith [fullWeight_ge_class n h hβ hn]

/-! ## 5. And it tends to zero as the box grows -/

theorem sub_two_le_card_offCornerSites (hn : 3 < n) : n - 2 ≤ (offCornerSites n).card := by
  have h0 : (0 : ℕ) < n := by omega
  calc n - 2 = (Finset.Ico 1 (n - 1)).card := by rw [Nat.card_Ico]; omega
    _ ≤ (offCornerSites n).card := by
        refine Finset.card_le_card_of_injOn
          (fun j => ((⟨0, h0⟩ : Fin n), (⟨j % n, Nat.mod_lt _ h0⟩ : Fin n)))
          (fun j hj => ?_) (fun j hj k hk hjk => ?_)
        · simp only [Finset.coe_Ico, Set.mem_Ico] at hj
          refine mem_offCornerSites.mpr ⟨by simp [isBoundary], ?_⟩
          rintro ⟨-, hcor | hcor⟩ <;>
            · simp only [Nat.mod_eq_of_lt (show j < n by omega)] at hcor
              omega
        · simp only [Finset.coe_Ico, Set.mem_Ico] at hj hk
          have := (Prod.ext_iff.mp hjk).2
          rw [Fin.ext_iff] at this
          simp only [Nat.mod_eq_of_lt (show j < n by omega),
            Nat.mod_eq_of_lt (show k < n by omega)] at this
          exact this

/-- **THE CLASS IS ASYMPTOTICALLY INVISIBLE, AT EVERY TEMPERATURE AND EVERY FIELD.** -/
theorem tendsto_classProb_zero (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    Tendsto (fun n : ℕ => classProb n h β) atTop (nhds 0) := by
  set t : ℝ := Real.exp (-β * (16 + 2 * |h|)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have hnonneg : ∀ n : ℕ, 0 ≤ classProb n h β := fun n =>
    le_of_lt (div_pos (classWeight_pos n h β) (fullWeight_pos n h β))
  have hmaj : ∀ᶠ n : ℕ in atTop, classProb n h β ≤ 1 / (1 + ((n - 2 : ℕ) : ℝ) * t) := by
    filter_upwards [eventually_gt_atTop 3] with n hn
    refine le_trans (classProb_le n h hβ hn) ?_
    have hcard : ((n - 2 : ℕ) : ℝ) ≤ ((offCornerSites n).card : ℝ) := by
      exact_mod_cast sub_two_le_card_offCornerSites hn
    have hle : ((n - 2 : ℕ) : ℝ) * t ≤ ((offCornerSites n).card : ℝ) * t := by
      nlinarith [ht0]
    have h1 : (0 : ℝ) < 1 + ((n - 2 : ℕ) : ℝ) * t := by positivity
    exact one_div_le_one_div_of_le h1 (by linarith)
  refine squeeze_zero' (Eventually.of_forall hnonneg) hmaj ?_
  have hdiv : Tendsto (fun n : ℕ => 1 + ((n - 2 : ℕ) : ℝ) * t) atTop atTop := by
    have hcast : Tendsto (fun n : ℕ => ((n - 2 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (Filter.tendsto_sub_atTop_nat 2)
    exact Filter.tendsto_atTop_add_const_left _ 1 (hcast.atTop_mul_const ht0)
  simpa [one_div] using hdiv.inv_tendsto_atTop

/-! ## 6. Read back on the hypothesis the enclosure step actually carries -/

theorem classWeight_eq_evenDegrees (n : ℕ) (h β : ℝ) (hn : 2 < n) :
    classWeight n h β
      = ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
          (fun σ => SimpleGraph.EvenDegrees (DualGraph.dualGraph σ)),
        Real.exp (-β * isingHB n h σ) := by
  rw [classWeight]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  refine Finset.filter_congr fun σ _ => ?_
  exact (evenDegrees_iff_boundaryConstOffCorner σ hn).symm

/-- **SO THE HYPOTHESIS `RayCircuitSurrounding` USES IN PLACE OF `+` IS ALSO ASYMPTOTICALLY
INVISIBLE.** The weight of the even-degree class is `classWeight`, and its share of the partition
sum tends to zero exactly as the `+` class's does. -/
theorem evenDegrees_weight_eq_and_tendsto (h : ℝ) {β : ℝ} (hβ : 0 ≤ β) :
    (∀ n : ℕ, 2 < n → (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => SimpleGraph.EvenDegrees (DualGraph.dualGraph σ)),
        Real.exp (-β * isingHB n h σ)) / fullWeight n h β = classProb n h β)
      ∧ Tendsto (fun n : ℕ => classProb n h β) atTop (nhds 0) :=
  ⟨fun n hn => by rw [classProb, classWeight_eq_evenDegrees n h β hn],
   tendsto_classProb_zero h hβ⟩

end EvenDegreesClassVanishes
