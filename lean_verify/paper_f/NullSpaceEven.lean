import InnerLowerSupport
import NullSpace
import TorusReflection

/-!
# The null space of the EVEN box, exactly

`NullSpace.nullSpace_box_odd` says that on an **odd** box a family supported on the lower half is
null exactly when it is the massive image of something supported strictly below the midline.
`RE-SWEEP #27` batch 4 found that the even box has no such statement, and that this — not a stray
calculation — is what stands between it and the dimension count the odd box already has.

**This is that statement.**

> `nullSpace_box_even` — on a box of even side, a family supported on `lowerHalf i n` is null
> **exactly when** it is the massive image of something supported on `innerLower i n`.

## Why the odd proof does not just transfer

The odd case reaches the general theorem `NullSpace.reflectedForm_eq_zero_iff_massive` with the
cross-coupling **identically zero** (`crossForm_odd_eq_zero`), which makes that theorem's third
clause — `crossForm (anti θ v) = 0` — free. **On the even box the coupling is not zero.**
`BoxCrossCoupling.crossOp_eq` computes it as minus a diagonal indicator of the innermost layer,
so the clause is a real constraint, and identifying it is the work:

* `crossForm_box_eq` — on the even box the double sum collapses to
  `−∑ (w p)²` over the innermost layer of the half, because `BoxCrossCoupling.adj_revSite_iff`
  says a half-site is adjacent to the mirror of a half-site exactly when the two are equal and
  innermost.
* `crossForm_eq_zero_iff` — so the form vanishes exactly when `w` does, on that layer.
* `anti_eq_self_of_innermost` — and for `v` supported on the half, `anti θ v` agrees with `v`
  there, because the mirror of a half-site is not a half-site.

Together the clause reads *"`v` vanishes on the innermost layer"*, and a vector supported on the
half that vanishes there is supported on `innerLower` — the set `InnerLowerSupport` introduced
for exactly this reason. **The three pieces the two files needed turn out to be the same layer
seen three ways**: the support of the block difference (`BoxNotStrict.sub_apply`), the vanishing
locus of the coupling (here), and the gap that makes the support lemma work
(`InnerLowerSupport`).

## What this does and does not settle

It settles the *description* of the null space at even side, and `exists_null_massive` settles
the watch-list clause that asked for `BoxNotStrict`'s null direction to be shown to have the
massive shape — it does, by running the biconditional forwards. **It does not compute the
dimension**: that needs the injectivity-and-image argument `NullSpaceDimension` runs for the odd
box, and porting it is a separate step that is not taken here. The watch-list item stays open
with its remaining leg named, one rung shorter than it was.

Nothing here touches `GraphReflectionPositive.reflectionPositive_box`, which says the form is
`≥ 0` and is untouched and still sharp.
-/

namespace NullSpaceEven

open Finset BoxGraph GraphHalfSpace GraphMirrorReflection GraphReflection InnerLowerSupport
open scoped Matrix

variable {d n : ℕ} {m : ℝ}

/-- `BoxCrossCoupling`'s version of this is `private`, so it is restated here. -/
private theorem mem_lowerHalf (i : Fin d) (p : Site d n) :
    p ∈ lowerHalf i n ↔ 2 * (p i).val < n := by
  simp [lowerHalf]

/-! ## 1. The coupling on the even box is minus a sum of squares over one layer -/

/-- **THE CROSS FORM, EXACTLY.** On the even box it collapses to `−∑ (w p)²` over the innermost
layer of the half — one term per site, because a half-site is adjacent to the mirror of a
half-site only when the two coincide. -/
theorem crossForm_box_eq (i : Fin d) (hn : Even n) (m : ℝ) (w : Site d n → ℝ) :
    crossForm (boxGraph d n) m (revSite (n := n) i) (lowerHalf i n) w
      = - ∑ p ∈ (lowerHalf i n).filter (fun p => 2 * (p i).val + 2 = n), (w p) ^ 2 := by
  classical
  rw [crossForm_eq_neg_adj (isMirrorHalf_of_isHalf (isHalf_lowerHalf i hn)) m w]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · simp only [boxGraph_adj]
    by_cases hin : 2 * (p i).val + 2 = n
    · rw [if_pos hin, if_pos ((BoxCrossCoupling.adj_revSite_iff i hn hp hp).mpr ⟨rfl, hin⟩)]
      ring
    · rw [if_neg hin, if_neg fun hc =>
        hin ((BoxCrossCoupling.adj_revSite_iff i hn hp hp).mp hc).2]
      ring
  · intro q hq hqp
    simp only [boxGraph_adj]
    rw [if_neg fun hc => hqp ((BoxCrossCoupling.adj_revSite_iff i hn hp hq).mp hc).1.symm]
    ring
  · intro hpn
    exact absurd hp hpn

/-- **AND SO IT VANISHES EXACTLY ON THAT LAYER.** -/
theorem crossForm_eq_zero_iff (i : Fin d) (hn : Even n) (m : ℝ) (w : Site d n → ℝ) :
    crossForm (boxGraph d n) m (revSite (n := n) i) (lowerHalf i n) w = 0
      ↔ ∀ p ∈ lowerHalf i n, 2 * (p i).val + 2 = n → w p = 0 := by
  classical
  rw [crossForm_box_eq i hn m w, neg_eq_zero]
  constructor
  · intro h p hp hin
    have hmem : p ∈ (lowerHalf i n).filter (fun p => 2 * (p i).val + 2 = n) :=
      Finset.mem_filter.mpr ⟨hp, hin⟩
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => sq_nonneg (w q))).mp h p hmem
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    refine Finset.sum_eq_zero fun q hq => ?_
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    rw [h q hq1 hq2]
    ring

/-! ## 2. On the half, the antisymmetric part is the vector itself at the innermost layer -/

/-- The mirror of a half-site is not a half-site, so a vector supported on the half is unchanged
by antisymmetrisation there. -/
theorem anti_eq_self_of_mem (i : Fin d) (hn : Even n) {v : Site d n → ℝ}
    (hv : ∀ p, p ∉ lowerHalf i n → v p = 0) {p : Site d n} (hp : p ∈ lowerHalf i n) :
    anti (revSite (n := n) i) v p = v p := by
  have hsplit := (isMirrorHalf_of_isHalf (isHalf_lowerHalf i hn)).split p (by simp)
  rw [anti, hv _ (hsplit.mp hp), sub_zero]

/-! ## 3. The null space -/

/-- **THE NULL SPACE OF THE EVEN BOX, EXACTLY.** A family supported on the lower half is null if
and only if it is the massive operator applied to something supported on `innerLower` — the lower
half with its innermost layer removed.

The odd twin is `NullSpace.nullSpace_box_odd`, where the set is `strictLower` and the coupling
clause is free because the coupling vanishes. Here the clause is the whole content. -/
theorem nullSpace_box_even (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {c : Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    reflectedForm (boxGraph d n) m (revSite (n := n) i) c = 0
      ↔ ∃ v : Site d n → ℝ, (∀ p, p ∉ innerLower i n → v p = 0)
          ∧ GraphLaplacian.massive (boxGraph d n) m *ᵥ v = c := by
  classical
  have hM := isMirrorHalf_of_isHalf (isHalf_lowerHalf (n := n) i hn)
  have hcross : ∀ w : Site d n → ℝ,
      crossForm (boxGraph d n) m (revSite (n := n) i) (lowerHalf i n) w ≤ 0 := fun w =>
    crossForm_nonpos_of_cross_diag hM (TorusReflection.boxGraph_cross_diag i hn) w
  rw [NullSpace.reflectedForm_eq_zero_iff_massive hM (GraphReflection.boxGraph_revSite_aut i) hm
    hcross (fun p hp _ => hc p hp)]
  constructor
  · rintro ⟨v, hvsupp, hvc, hcr⟩
    refine ⟨v, ?_, hvc⟩
    intro p hp
    by_cases hph : p ∈ lowerHalf i n
    · have hin : 2 * (p i).val + 2 = n := by
        rw [mem_innerLower] at hp
        rw [mem_lowerHalf] at hph
        obtain ⟨t, ht⟩ := hn
        omega
      have := (crossForm_eq_zero_iff i hn m _).mp hcr p hph hin
      rwa [anti_eq_self_of_mem i hn hvsupp hph] at this
    · exact hvsupp p hph
  · rintro ⟨v, hvsupp, hvc⟩
    have hlow : ∀ p, p ∉ lowerHalf i n → v p = 0 := by
      intro p hp
      refine hvsupp p fun hc => hp ?_
      rw [mem_innerLower] at hc
      exact (mem_lowerHalf i p).mpr (by omega)
    refine ⟨v, hlow, hvc, ?_⟩
    refine (crossForm_eq_zero_iff i hn m _).mpr fun p hp hin => ?_
    rw [anti_eq_self_of_mem i hn hlow hp]
    refine hvsupp p fun hcon => ?_
    rw [mem_innerLower] at hcon
    omega

/-- **AND `BoxNotStrict`'S NULL DIRECTION HAS THE MASSIVE SHAPE.**

The watch-list clause this file was built for said, of the even box: *"the even-side construction
of `BoxNotStrict` is not shown to have the massive shape (it must, by the theorem, but the
calculation is not done)"*. It is done: run `nullSpace_box_even` forwards on the family
`BoxNotStrict.exists_null_direction` produces. **This also shows the biconditional is not vacuous
on either side** — there is a nonzero null family at every even side of at least four, and it is
a massive image of something supported on `innerLower`. -/
theorem exists_null_massive (i : Fin d) (hn : Even n) (h4 : 4 ≤ n) (hm : m ≠ 0) :
    ∃ c : Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → c p = 0)
      ∧ ∃ v : Site d n → ℝ, (∀ p, p ∉ innerLower i n → v p = 0)
          ∧ GraphLaplacian.massive (boxGraph d n) m *ᵥ v = c := by
  obtain ⟨c, hc0, hcsupp, hcnull⟩ := BoxNotStrict.exists_null_direction i hn h4 hm
  exact ⟨c, hc0, hcsupp, (nullSpace_box_even i hn hm hcsupp).mp hcnull⟩

end NullSpaceEven
