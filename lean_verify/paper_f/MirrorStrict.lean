/-
  MirrorStrict.lean — the corrected strict criterion, and the last two open
  cases on this wall.

  WHY, AND A ROUTE THAT WAS MAPPED AND NOT NEEDED. ERRATUM 73 refuted the
  estate's prose criterion as an equivalence and gave the corrected version,
  measured over twenty cases: **the cross-coupling restricted to the STRICT
  half — excluding the mirror layer — is negative definite.** The watchlist
  item recorded it as blocked, and mapped a route: build the three-block form
  `S = [[2(A+B), 2C], [2Cᵀ, D]]`, minimise over the mirror coordinates, and
  recover the fixed-point-free answer by the Schur identity.

  **None of that is needed, and the reason is a line already in the estate.**
  `GraphMirrorReflection.reflectionPositive_mirror` proves positivity by
  completing the square, and its chain derives, before any hypothesis is
  used, that

      `reflectedForm ≥ − crossForm (G · anti θ c)`,

  the coupling being evaluated at the GREEN FUNCTION applied to the
  antisymmetrisation — the test vector the completing-the-square argument
  optimises at, not the antisymmetrisation itself. A first draft of this file
  stated it at `anti θ c` and did not compile, which is the cheapest possible
  way to be corrected.

  It then discards the right-hand side by assuming the cross-coupling
  nonpositive. **The discarded term is the entire strictness theorem.** §1
  keeps it. This is the fourth route this month refused on an unchecked claim
  about machinery the estate already owns, and the rule ERRATUM 71 states was
  written after the third — so the recurrence, not the instance, is what
  §4 records.

  **WHY "STRICT HALF" AND NOT "HALF" IS THE WHOLE CORRECTION.** The old prose
  quantified over `lowerHalf`, which contains the mirror layer, and a mirror
  site can never touch its own image — it IS its image, and graphs have no
  loops — so the condition failed on every reflection with a fixed layer and
  the criterion looked far narrower than it is. **The cross-coupling form
  never sees the mirror sites at all**: they are not in the index set. Once
  the condition is asked of `strictLower` instead, the torus at sides three
  and four satisfy it, and those were the last two open cases on this wall.

  WHAT THIS FILE PROVES:
  1. **`reflectedForm_ge_neg_crossForm`** — the sharpening. Over an arbitrary
     graph and an arbitrary mirror half, with NO hypothesis on the coupling.
     `reflectionPositive_mirror` is the corollary at `crossForm ≤ 0`.
  2. **`crossForm_eq_neg_sq`** — when the coupling is diagonal and every site
     of the STRICT half carries a cut-crossing edge, the form is exactly
     minus a sum of squares.
  3. **`reflectionPositive_mirror_strict`** — hence strictness, in both
     cases: a family charging the strict half is killed by §1, and a family
     living only on the mirror is killed by the energy, which is a different
     argument and is why the old condition could not cover it.
  4. **`torus_touching`**, **`reflectionPositive_torus_three_strict`**,
     **`reflectionPositive_torus_four_strict`** — the two cases ERRATUM 73's
     table said were strict and no proof reached.

  **SO THE TORUS IS SETTLED AT EVERY SIDE FROM TWO**: strict at two, three
  and four; not strict at five and up. With the box settled at every side,
  **this wall has no open sharpness case left**.

  WHAT THIS DOES NOT DO.
  * **Still not an "exactly when".** §3 is sufficiency. The converse — that a
    strict half whose coupling is degenerate always yields a null direction —
    is what the negative files do case by case and is still not unified.
    ERRATUM 73 exists because that gap was once papered over; it is not
    papered over here.
  * **Torus side one is not stated.** There the reflection is the identity
    and the argument is `StrictCriterion`'s side-one argument verbatim; it is
    omitted rather than copied, and this sentence is the record that it was a
    choice.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import StrictCriterion

namespace MirrorStrict

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection BoxOddReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The bound the positivity proof throws away

`reflectionPositive_mirror` runs: the antisymmetric energy is attained at
`ξ = G·anti`, the symmetric one is bounded below at the sign-flipped `ξ`, the
two linear terms agree, and the two quadratic terms differ by exactly four
times the cross-coupling. Chaining those gives the inequality below. The
positivity theorem then throws the right-hand side away.
-/

/-- **THE SHARP BOUND, with no hypothesis on the coupling.** -/
theorem reflectedForm_ge_neg_crossForm (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    -crossForm G m θ H (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c)
      ≤ GraphReflection.reflectedForm G m θ c := by
  classical
  set N := GraphLaplacian.massive G m with hN
  have hNpd : N.PosDef := GraphLaplacian.massive_posDef G hm
  set a := GraphReflection.anti θ c with ha
  set s := GraphReflection.sym θ c with hs
  set ξ : V → ℝ := N⁻¹ *ᵥ a with hξdef
  have hξodd : IsOddFun θ ξ := by
    intro p
    have hgreen : ∀ x y, GraphLaplacian.green G m (θ x) (θ y) = GraphLaplacian.green G m x y :=
      fun x y => GraphReflection.green_aut h m x y
    have haodd : ∀ q, a (θ q) = -a q := by
      intro q
      simp only [ha, GraphReflection.anti, h.invol q]
      ring
    have hNinv : N⁻¹ = GraphLaplacian.green G m := rfl
    simp only [hξdef, hNinv, Matrix.mulVec, dotProduct]
    rw [← Fintype.sum_equiv θ (fun q => GraphLaplacian.green G m (θ p) (θ q) * a (θ q))
      (fun q => GraphLaplacian.green G m (θ p) q * a q) (fun _ => rfl)]
    simp only [hgreen, haodd, mul_neg, Finset.sum_neg_distrib]
  have hAeq : GraphReflection.energy G m a = 2 * (ξ ⬝ᵥ a) - ξ ⬝ᵥ (N *ᵥ ξ) := by
    rw [energy_eq_dotProduct, hξdef]
    exact (dotProduct_inv_eq hNpd a).symm
  have hSle : 2 * (evenify H ξ ⬝ᵥ s) - evenify H ξ ⬝ᵥ (N *ᵥ evenify H ξ)
      ≤ GraphReflection.energy G m s := by
    rw [energy_eq_dotProduct]
    exact dotProduct_inv_le hNpd s (evenify H ξ)
  have hlin : evenify H ξ ⬝ᵥ s = ξ ⬝ᵥ a := by
    rw [hs, ha, dotProduct_sym (evenify_isEven hM hξodd) c,
      dotProduct_anti hξodd c, dotProduct_evenify_eq hM hξodd hc]
  have hq := quadDiff (G := G) (m := m) hM hξodd
  have h4 := GraphReflection.reflectedForm_eq (G := G) (m := m) h c
  rw [← hs, ← ha] at h4
  have hgx : GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c = ξ := rfl
  rw [hgx]
  linarith

/-! ## 2. The coupling as a sum of squares -/

/-- **DIAGONAL AND FULL ON THE STRICT HALF GIVES MINUS A SUM OF SQUARES.**
    Note what the index set is: `H`, the STRICT half. The mirror sites are
    not in it and never were, which is the whole of ERRATUM 73. -/
theorem crossForm_eq_neg_sq (hM : IsMirrorHalf θ H Mir)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q)
    (hfull : ∀ p ∈ H, G.Adj p (θ p)) (w : V → ℝ) :
    crossForm G m θ H w = -∑ p ∈ H, w p * w p := by
  classical
  rw [crossForm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hinner : ∑ q ∈ H, w p * w q * GraphLaplacian.massive G m p (θ q)
      = w p * w p * GraphLaplacian.massive G m p (θ p) :=
    Finset.sum_eq_single_of_mem p hp fun q hq hqp => by
      have hne : p ≠ θ q := fun hc => hM.notMem_of_mem hq (hc ▸ hp)
      have hnadj : ¬ G.Adj p (θ q) := fun hc => hqp (hdiag p hp q hq hc).symm
      rw [GraphLaplacian.massive_apply, if_neg hne, if_neg hnadj]
      ring
  rw [hinner]
  have hne : p ≠ θ p := fun hc => hM.notMem_of_mem hp (hc ▸ hp)
  rw [GraphLaplacian.massive_apply, if_neg hne, if_pos (hfull p hp)]
  ring

omit [Fintype V] [DecidableEq V] in
/-- An odd function vanishing on the strict half vanishes everywhere: the
    mirror kills itself and the far side is a sign flip of the near one.
    **Involutivity is not needed** — the splitting alone does it — which is
    why the hypothesis is absent. -/
theorem eq_zero_of_odd_of_zero_on_half (hM : IsMirrorHalf θ H Mir)
    {ξ : V → ℝ} (hodd : IsOddFun θ ξ)
    (hz : ∀ p ∈ H, ξ p = 0) : ξ = 0 := by
  funext p
  change ξ p = 0
  by_cases hp : p ∈ H
  · exact hz p hp
  · by_cases hpm : p ∈ Mir
    · have h1 := hodd p
      rw [(hM.fixed p).mp hpm] at h1
      linarith
    · have h1 := hodd p
      rw [hz _ (hM.mem_of_notMem hp hpm)] at h1
      linarith

/-! ## 3. Strictness, in two cases that need different arguments -/

/-- **THE CORRECTED CRITERION.** Diagonal coupling, every site of the STRICT
    half carrying a cut-crossing edge. Both cases are needed and they are not
    variants of each other: a family charging the strict half is killed by
    §1, and a family living only on the mirror is killed by the energy. -/
theorem reflectionPositive_mirror_strict (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q)
    (hfull : ∀ p ∈ H, G.Adj p (θ p))
    {c : V → ℝ} (hc0 : c ≠ 0) (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    0 < GraphReflection.reflectedForm G m θ c := by
  classical
  have hmirfix : ∀ p, θ p ∈ Mir → p ∈ Mir := by
    intro p hpm
    refine (hM.fixed p).mpr ?_
    have h1 := (hM.fixed (θ p)).mp hpm
    rw [h.invol p] at h1
    exact h1.symm
  by_cases hx : ∀ p ∈ H, c p = 0
  · -- the family lives on the mirror: antisymmetrisation dies, energy survives
    have hoff : ∀ p, p ∉ Mir → c p = 0 := fun p hp =>
      if hpH : p ∈ H then hx p hpH else hc p hpH hp
    have hazero : GraphReflection.anti θ c = 0 := by
      funext p
      by_cases hp : p ∈ Mir
      · simp [GraphReflection.anti, (hM.fixed p).mp hp]
      · simp [GraphReflection.anti, hoff p hp, hoff _ (fun hcm => hp (hmirfix p hcm))]
    have hszero : GraphReflection.sym θ c = fun p => 2 * c p := by
      funext p
      have h1 := congrFun hazero p
      simp only [GraphReflection.anti, Pi.zero_apply, sub_eq_zero] at h1
      simp only [GraphReflection.sym, ← h1]
      ring
    have h4 := GraphReflection.reflectedForm_eq (G := G) (m := m) h c
    rw [hazero, hszero] at h4
    have hz : GraphReflection.energy G m 0 = 0 := by
      simp [GraphReflection.energy, GraphReflection.bil]
    have hsc : GraphReflection.energy G m (fun p => 2 * c p)
        = 4 * GraphReflection.energy G m c := by
      simp only [GraphReflection.energy, GraphReflection.bil, Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
    rw [hz, hsc] at h4
    have hpos : 0 < GraphReflection.energy G m c := by
      rw [energy_eq_dotProduct]
      have := (Matrix.posDef_iff_dotProduct_mulVec.mp
        (GraphLaplacian.green_posDef G hm)).2 hc0
      simpa [dotProduct_comm] using this
    linarith
  · -- the family charges the strict half: §1 gives a strictly positive bound
    push Not at hx
    obtain ⟨p₀, hp₀H, hp₀⟩ := hx
    have haH : ∀ p ∈ H, GraphReflection.anti θ c p = c p := by
      intro p hp
      have : c (θ p) = 0 :=
        hc _ (hM.notMem_of_mem hp) fun hcm => hM.disj p hp (hmirfix p hcm)
      simp [GraphReflection.anti, this]
    have hane : GraphReflection.anti θ c ≠ 0 := fun h0 =>
      hp₀ ((haH p₀ hp₀H).symm.trans (congrFun h0 p₀))
    set ξ : V → ℝ := GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c with hξ
    have hξodd : IsOddFun θ ξ := by
      intro p
      have hgreen : ∀ x y, GraphLaplacian.green G m (θ x) (θ y) = GraphLaplacian.green G m x y :=
        fun x y => GraphReflection.green_aut h m x y
      have haodd : ∀ q, GraphReflection.anti θ c (θ q) = -GraphReflection.anti θ c q := by
        intro q
        simp only [GraphReflection.anti, h.invol q]
        ring
      simp only [hξ, Matrix.mulVec, dotProduct]
      rw [← Fintype.sum_equiv θ
        (fun q => GraphLaplacian.green G m (θ p) (θ q) * GraphReflection.anti θ c (θ q))
        (fun q => GraphLaplacian.green G m (θ p) q * GraphReflection.anti θ c q)
        (fun _ => rfl)]
      simp only [hgreen, haodd, mul_neg, Finset.sum_neg_distrib]
    have hξne : ξ ≠ 0 := by
      intro h0
      refine hane ?_
      have hunit : IsUnit (GraphLaplacian.massive G m).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp (GraphLaplacian.massive_posDef G hm).isUnit
      have hinv : GraphLaplacian.massive G m *ᵥ ξ = GraphReflection.anti θ c := by
        rw [hξ, show GraphLaplacian.green G m = (GraphLaplacian.massive G m)⁻¹ from rfl,
          Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at hinv
      exact hinv.symm
    obtain ⟨q₀, hq₀H, hq₀⟩ : ∃ p ∈ H, ξ p ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hξne (eq_zero_of_odd_of_zero_on_half hM hξodd hcon)
    have hsq : 0 < ∑ p ∈ H, ξ p * ξ p :=
      Finset.sum_pos' (fun p _ => mul_self_nonneg _) ⟨q₀, hq₀H, mul_self_pos.mpr hq₀⟩
    have hcf := crossForm_eq_neg_sq (G := G) (m := m) hM hdiag hfull ξ
    have hbound := reflectedForm_ge_neg_crossForm hM h hm hc
    rw [← hξ, hcf] at hbound
    linarith

/-! ## 4. The torus at sides three and four

ERRATUM 73's table says both are strict and no proof reached them. The
touching condition holds on the STRICT half at both — at side three the only
strict-half layer is the bottom one, which reaches its mirror through the
wrap-around; at side four the bottom layer does the same and the layer above
it reaches its mirror by an ordinary step.
-/

section Torus

open TorusReflection TorusAnySide

variable {d n : ℕ}

/-- **EVERY SITE OF THE STRICT HALF TOUCHES ITS MIRROR**, at torus sides three
    and four. Two different edges do the work and both are needed: the
    wrap-around for the bottom layer, an ordinary step for the layer above it
    when the side is four. -/
theorem torus_touching (i : Fin d) (hn : n = 3 ∨ n = 4) :
    ∀ p ∈ strictLower i n,
      (torusGraph d n).Adj p (GraphReflection.revSite (n := n) i p) := by
  intro p hp
  rw [mem_strictLower] at hp
  have hlt := (p i).isLt
  have hrev : ((GraphReflection.revSite (n := n) i p) i).val = n - ((p i).val + 1) := by
    rw [GraphReflection.revSite_apply_self]; exact Fin.val_rev (p i)
  refine ⟨i, fun j hj => (GraphReflection.revSite_apply_ne hj p).symm, ?_, ?_⟩
  · exact fun hc => by
      have := congrArg Fin.val hc
      rw [hrev] at this
      rcases hn with rfl | rfl <;> omega
  · rw [hrev]
    rcases hn with rfl | rfl <;> omega

/-- **THE TORUS AT SIDE THREE IS STRICT** — the case ERRATUM 73 used as its
    counterexample to the old criterion, now proved by the corrected one. -/
theorem reflectionPositive_torus_three_strict (i : Fin d) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d 3 → ℝ} (hc0 : c ≠ 0)
    (hcsupp : ∀ p, p ∉ lowerHalf i 3 → c p = 0) :
    0 < GraphReflection.reflectedForm (torusGraph d 3) m
          (GraphReflection.revSite (n := 3) i) c := by
  refine reflectionPositive_mirror_strict (isMirrorHalf_strictLower i 3) (isRefl_torus i) hm
    (torus_cross_diag_any i 3) (torus_touching i (Or.inl rfl)) hc0 ?_
  intro p hpH hpM
  refine hcsupp p ?_
  rw [lowerHalf_eq_union]
  simp only [Finset.mem_union]
  tauto

/-- **AND AT SIDE FOUR.** -/
theorem reflectionPositive_torus_four_strict (i : Fin d) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d 4 → ℝ} (hc0 : c ≠ 0)
    (hcsupp : ∀ p, p ∉ lowerHalf i 4 → c p = 0) :
    0 < GraphReflection.reflectedForm (torusGraph d 4) m
          (GraphReflection.revSite (n := 4) i) c := by
  refine reflectionPositive_mirror_strict (isMirrorHalf_strictLower i 4) (isRefl_torus i) hm
    (torus_cross_diag_any i 4) (torus_touching i (Or.inr rfl)) hc0 ?_
  intro p hpH hpM
  refine hcsupp p ?_
  rw [lowerHalf_eq_union]
  simp only [Finset.mem_union]
  tauto

end Torus

/-! ## 5. Review — the ways this could be hollow

**"Is §1 new, or is it `reflectionPositive_mirror` with a rearranged
`linarith`?"** The latter, and that is the finding rather than a criticism of
it. The chain in that proof establishes the bound and then discards it by
applying a hypothesis; keeping it costs one changed line and yields every
strictness result below. **The watchlist had this recorded as blocked behind
a three-block Schur argument that was never needed** — the fourth such
refusal this month, which §4 of the log treats as a pattern rather than an
incident.

**"Do the two cases in §3 really need different arguments?"** Yes, and it is
the substance of ERRATUM 73. A family charging the strict half is controlled
by the coupling, which is what §1 bounds. A family living entirely on the
mirror has zero antisymmetrisation, so the coupling says nothing at all about
it — its rigidity comes from the energy of the symmetrisation instead. **The
old prose criterion had no way to express the second case**, which is exactly
why it failed on the torus at side three.

**"Is `hfull` doing real work at side four, or is one edge type enough?"**
Both edge types are used and neither suffices alone: the bottom layer reaches
its mirror only through the wrap-around, and the layer above it only by an
ordinary step. At side three there is one layer and only the wrap-around. A
proof that handled one mechanism would fail at one of the two sides.

**"Does this close the wall?"** For sharpness, yes. Box: strict at sides one
and two, not strict from three. Torus: strict at two, three and four, not
strict from five. The estate's own `def`: not strict from three, and its
sides one and two are the box's by transport but are not stated. **No open
sharpness case remains on this wall**, and the one case that looked like a
counterexample to the whole picture is now a theorem.

**"What is still not proved?"** The converse direction, which would make the
criterion an equivalence. Every negative result on this wall exhibits a null
direction by an explicit construction, and no theorem says a degenerate
coupling forces one. **That is the honest remaining gap**, and after ERRATUM
73 it is stated rather than assumed away.
-/

end MirrorStrict
