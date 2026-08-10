/-
  OddNotStrictInstances.lean — the odd-side sharpness identity, cashed at the
  torus and at the estate's own definition.

  WHY. `BoxOddNotStrict.reflectedForm_massive_eq_crossForm` is an EQUALITY
  over an arbitrary graph and an arbitrary mirror half, and the file that
  proved it used it once, on the box. Its own review section listed the torus
  and the estate's `def` as available and not attempted. **A general identity
  used at one instance is a special case wearing a general statement's
  clothes**, so this file cashes both, and the two turn out to need different
  amounts of care — which is the reason they are worth doing rather than
  asserting.

  **THE TORUS IS NOT A REPEAT, AND THE FIRST ATTEMPT WOULD HAVE BEEN WRONG.**
  On the box the identity reads `reflectedForm (massive *ᵥ v) = 0`, because
  the cross-coupling vanishes. **On the torus the cross-coupling does not
  vanish** — the wrap-around edge crosses the cut at every side length — so
  the identity gives a NEGATIVE number, and a negative reflected form does
  not contradict positivity only because **`massive *ᵥ v` is not supported in
  the half there**: the operator reaches from the bottom layer across the
  wrap-around into the upper half. Both facts have to be repaired at once,
  and one repair does it: **keep `v` off the bottom layer.** Then the
  operator's reach stays inside `lowerHalf`, and the cross-coupling term it
  would have contributed is exactly the term that vanishes.

  WHAT THIS FILE PROVES:
  1. **`crossForm_eq_zero_of_diag`** — a diagonal cross-coupling contributes
     nothing when the test vector vanishes at the sites that actually carry a
     cut-crossing edge. General; the sharpened form of
     `crossForm_nonpos_of_cross_diag`, giving equality where that gives an
     inequality.
  2. **`exists_null_direction_lattice_odd`** and **`not_strict_lattice_odd`**
     — the estate's own `LatticeReflection.ReflectionPositive` is not sharp at
     odd side three and up. By transport along `sitePair`, the same standard
     `LatticeNotStrict` applied to the even case.
  3. **`torus_massive_supported`** — on the torus, a coefficient family
     supported strictly between the bottom layer and the midline is pushed by
     the operator no further than `lowerHalf`. **This is the lemma that the
     box did not need**, and it is where the wrap-around is handled.
  4. **`exists_null_direction_torus_odd`** and **`not_strict_torus_odd`** —
     the torus is not sharp at odd side FIVE and up.

  WHAT THIS DOES NOT DO.
  * **Torus side three is not covered**, and the reason is structural rather
    than lazy: at side three the strict half is the single layer at
    coordinate zero, which is exactly the layer the wrap-around forbids, so
    the construction has nothing left to act on. Whether side three is sharp
    on the torus is open, and this file does not guess.
  * **Even sides on the torus are not covered either.** There the
    cross-coupling has two diagonal terms rather than one — the wrap-around
    AND the innermost layer — so the same construction needs `v` to avoid
    both, which needs side six and up. Stated because it is the obvious next
    instance, not attempted here.
  * **Still a subspace, not the null space.** Unchanged from
    `BoxOddNotStrict`.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import BoxOddNotStrict
import LatticeNotStrict

namespace OddNotStrictInstances

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection BoxOddReflection BoxOddNotStrict

/-! ## 1. When a diagonal cross-coupling contributes nothing -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-- **THE SHARPENED CRITERION.** `crossForm_nonpos_of_cross_diag` gives `≤ 0`
    from a diagonal coupling; this gives `= 0` when the test vector also
    vanishes wherever a cut-crossing edge actually lands. On the box at odd
    side there are no such edges and the second hypothesis is vacuous; on the
    torus there is exactly one layer of them and it is not. -/
theorem crossForm_eq_zero_of_diag (hM : IsMirrorHalf θ H Mir)
    (hcross : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q)
    (w : V → ℝ) (hw : ∀ p ∈ H, G.Adj p (θ p) → w p = 0) :
    crossForm G m θ H w = 0 := by
  classical
  refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
  have hne : p ≠ θ q := fun hc => hM.notMem_of_mem hq (hc ▸ hp)
  rw [GraphLaplacian.massive_apply, if_neg hne]
  by_cases hpq : p = q
  · subst hpq
    by_cases hadj : G.Adj p (θ p)
    · rw [hw p hp hadj]; ring
    · simp [hadj]
  · have : ¬ G.Adj p (θ q) := fun hc => hpq (hcross p hp q hq hc)
    simp [this]

/-! ## 2. The estate's own definition

The same standard `LatticeNotStrict` applied to the even case: a statement
about `boxGraph` does not close anything here until it is proved for the
`def` the estate itself wrote. `sum_green_congr` is an equality of forms, so
it carries the vanishing across as readily as it carried the sign.
-/

open IsingFiniteVolume LatticeReflectionPositive in
/-- **THE ESTATE'S OWN `def` IS NOT SHARP AT ODD SIDE EITHER.** -/
theorem exists_null_direction_lattice_odd {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n)
    {m : ℝ} (hm : m ≠ 0) :
    ∃ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 ∧
      (∀ p, p ∉ lowerHalfPair n → c p = 0) ∧
      GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph n) m
        (LatticeReflection.refl n) c = 0 := by
  classical
  obtain ⟨v, hv0, hvsupp, hvform⟩ :=
    BoxOddNotStrict.exists_null_direction_box_odd (d := 2) (0 : Fin 2) hn h3 hm
  refine ⟨fun q => v ((sitePair n).symm q), ?_, ?_, ?_⟩
  · intro hc
    refine hv0 (funext fun p => ?_)
    have := congrFun hc (sitePair n p)
    rwa [Equiv.symm_apply_apply] at this
  · intro q hq
    refine hvsupp _ fun hmem => hq ?_
    rw [← map_lowerHalf n]
    exact Finset.mem_map.mpr ⟨(sitePair n).symm q, hmem, by simp⟩
  · rw [LatticeNotStrict.reflectedForm_lattice_eq]
    simpa using hvform

open IsingFiniteVolume LatticeReflectionPositive in
/-- **SO `LatticeReflection.ReflectionPositive` IS SHARP AT NO SIDE OF THREE
    OR MORE**, the even cases being `LatticeNotStrict`. -/
theorem not_strict_lattice_odd {n : ℕ} (hn : Odd n) (h3 : 3 ≤ n) {m : ℝ} (hm : m ≠ 0) :
    ¬ (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 →
        (∀ p, p ∉ lowerHalfPair n → c p = 0) →
        0 < GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph n) m
              (LatticeReflection.refl n) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction_lattice_odd hn h3 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-! ## 3. The torus, where the wrap-around has to be dodged -/

section Torus

open TorusReflection TorusAnySide

variable {d n : ℕ}

/-- Sites strictly between the bottom layer and the midline. On the torus
    this is the region the construction can use: below the midline so the
    half applies, above the bottom so the wrap-around does not. -/
def innerLower (i : Fin d) (n : ℕ) : Finset (Site d n) :=
  Finset.univ.filter fun p => 1 ≤ (p i).val ∧ 2 * (p i).val + 1 < n

theorem mem_innerLower {i : Fin d} {p : Site d n} :
    p ∈ innerLower i n ↔ 1 ≤ (p i).val ∧ 2 * (p i).val + 1 < n := by
  simp [innerLower]

theorem innerLower_subset (i : Fin d) (n : ℕ) : innerLower i n ⊆ strictLower i n :=
  fun _ hp => mem_strictLower.mpr (mem_innerLower.mp hp).2

/-- **THE OPERATOR'S REACH STAYS INSIDE THE HALF.** A torus step from a site
    strictly between the bottom layer and the midline moves the reflected
    coordinate by one and cannot wrap, so it lands no higher than the
    midline. **This is the lemma the box did not need.** -/
theorem torus_massive_supported (i : Fin d) (hn : Odd n) (m : ℝ)
    {v : Site d n → ℝ} (hv : ∀ p, p ∉ innerLower i n → v p = 0) :
    ∀ p, p ∉ lowerHalf i n →
      (GraphLaplacian.massive (torusGraph d n) m *ᵥ v) p = 0 := by
  classical
  intro p hp
  have hpn : ¬ (2 * (p i).val < n) := by
    simpa [lowerHalf, Finset.mem_filter] using hp
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q ∈ innerLower i n
  · obtain ⟨hq1, hq2⟩ := mem_innerLower.mp hq
    obtain ⟨k, hk⟩ := hn
    have hqlt := (q i).isLt
    have hne : p ≠ q := fun hc => by rw [hc] at hpn; omega
    have hadj : ¬ (torusGraph d n).Adj p q := by
      rintro ⟨j, hsame, -, hstep⟩
      by_cases hj : j = i
      · subst hj
        omega
      · exact hne (funext fun l => by
          by_cases hl : l = j
          · subst hl
            exact absurd (congrArg Fin.val (hsame i (fun hc => hj hc.symm))) (by omega)
          · exact hsame l hl)
    rw [GraphLaplacian.massive_apply, if_neg hne, if_neg hadj]
    ring
  · rw [hv q hq, mul_zero]

/-- **THE TORUS IS NOT SHARP AT ODD SIDE FIVE AND UP.** Side five is where
    `innerLower` first has a site: below it the region the wrap-around leaves
    available is empty. -/
theorem exists_null_direction_torus_odd (i : Fin d) (hn : Odd n) (h5 : 5 ≤ n)
    {m : ℝ} (hm : m ≠ 0) :
    ∃ c : Site d n → ℝ, c ≠ 0 ∧
      (∀ p, p ∉ lowerHalf i n → c p = 0) ∧
      GraphReflection.reflectedForm (torusGraph d n) m
        (GraphReflection.revSite (n := n) i) c = 0 := by
  classical
  obtain ⟨k, hk⟩ := hn
  set p₀ : Site d n := fun j => if j = i then ⟨1, by omega⟩ else ⟨0, by omega⟩ with hp₀
  set v : Site d n → ℝ := fun p => if p = p₀ then 1 else 0 with hv
  have hp₀i : (p₀ i).val = 1 := by simp [hp₀]
  have hvsupp : ∀ p, p ∉ innerLower i n → v p = 0 := by
    intro p hp
    have hne : p ≠ p₀ := by
      rintro rfl
      exact hp (mem_innerLower.mpr ⟨by omega, by omega⟩)
    simp [hv, hne]
  have hvstrict : ∀ p, p ∉ strictLower i n → v p = 0 :=
    fun p hp => hvsupp p fun hc => hp (innerLower_subset i n hc)
  refine ⟨GraphLaplacian.massive (torusGraph d n) m *ᵥ v, ?_,
    torus_massive_supported i ⟨k, hk⟩ m hvsupp, ?_⟩
  · intro hc
    have hvne : v ≠ 0 := fun h0 => by
      have := congrFun h0 p₀; simp [hv] at this
    refine hvne ?_
    have hpd := GraphLaplacian.massive_posDef (torusGraph d n) hm
    have hunit : IsUnit (GraphLaplacian.massive (torusGraph d n) m).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
    have := congrArg (fun w => GraphLaplacian.green (torusGraph d n) m *ᵥ w) hc
    simpa [GraphLaplacian.green, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit] using this
  · rw [BoxOddNotStrict.reflectedForm_massive_eq_crossForm
      (isMirrorHalf_strictLower i n) (isRefl_torus i) hm hvstrict]
    -- the only cut-crossing edges sit on the bottom layer, where `v` vanishes
    refine crossForm_eq_zero_of_diag (isMirrorHalf_strictLower i n)
      (torus_cross_diag_any i n) _ fun p hp hadj => ?_
    have hbot : (p i).val = 0 := by
      rw [mem_strictLower] at hp
      obtain ⟨j, hsame, -, hstep⟩ := hadj
      have hplt := (p i).isLt
      have hrev : ((GraphReflection.revSite (n := n) i p) i).val = n - ((p i).val + 1) := by
        rw [GraphReflection.revSite_apply_self, Fin.val_rev]
      by_cases hj : j = i
      · subst hj
        omega
      · exact absurd (congrArg Fin.val (hsame i (fun hc => hj hc.symm))) (by omega)
    have hnp : p ≠ p₀ := fun hc => by rw [hc, hp₀i] at hbot; omega
    have hnθp : GraphReflection.revSite (n := n) i p ≠ p₀ := by
      intro hc
      have := congrArg (fun q => (q i).val) hc
      simp only [GraphReflection.revSite_apply_self, Fin.val_rev, hp₀i] at this
      have hplt := (p i).isLt
      omega
    simp [GraphReflection.anti, hv, hnp, hnθp]

/-- **SO REFLECTION POSITIVITY ON THE TORUS IS NOT SHARP FROM ODD SIDE
    FIVE.** -/
theorem not_strict_torus_odd (i : Fin d) (hn : Odd n) (h5 : 5 ≤ n) {m : ℝ} (hm : m ≠ 0) :
    ¬ (∀ c : Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (torusGraph d n) m
              (GraphReflection.revSite (n := n) i) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction_torus_odd i hn h5 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

end Torus

/-! ## 4. Review — the ways this could be hollow

**"Is the torus a copy of the box with names changed?"** No, and the place it
differs is the place a copy would have gone wrong. On the box the identity
gives zero because the cross-coupling vanishes; on the torus the coupling
does NOT vanish, so the same construction gives a strictly negative reflected
form — which would look like a contradiction with positivity and is not one,
because `massive *ᵥ v` is not supported in the half there. **Two things break
at once and one hypothesis fixes both**: keeping `v` off the bottom layer
stops the operator reaching across the wrap-around AND kills the only
cross-coupling term. A file that had assumed the box argument transferred
would have produced a false theorem or an unprovable one.

**"Why five on the torus and three on the box?"** Because `innerLower` is
empty below five: at side three the strict half is the single layer at
coordinate zero, which is exactly the layer the wrap-around forbids. That is
a real gap and it is stated as one — **torus side three is open**, not
"presumably fine".

**"Is `crossForm_eq_zero_of_diag` earning its place, or is it §1 of the
previous file again?"** It is the previous criterion with `≤` strengthened to
`=` under one extra hypothesis, and the extra hypothesis is what the torus
needs and the box does not. On the box it is vacuous, which is the honest way
to see that the box was the easy instance.

**"Does the lattice transport actually carry a NEGATIVE result?"** Yes, for
the reason `LatticeNotStrict` recorded when it did the same thing for the
even case: `sum_green_congr` is an EQUALITY of quadratic forms, not an
inequality between them, so it carries the vanishing and the attaining vector
and not merely the sign. That was luck the first time and is now a known
property being reused deliberately.

**"What is the state of sharpness across this wall?"** The box: not sharp at
any side of three or more. The estate's own `def`: the same, by transport.
The torus: not sharp at even side SIX and up (`TorusNotStrict`, which asks
`6 ≤ n`) and at odd side FIVE and up (here) — so **the odd-side result is the
stronger of the two on the torus**, reaching one side length lower, which was
not expected and is worth noting rather than smoothing over. Open on the
torus: every side of four or less. Open on the box: sides one and two. **None
of those gaps is accompanied by a prediction**, and the count above was
checked against the actual hypotheses of `TorusNotStrict` rather than
remembered — an earlier draft of this paragraph said "from three" and was
wrong.
-/

end OddNotStrictInstances
