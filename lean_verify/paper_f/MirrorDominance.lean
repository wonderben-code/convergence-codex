import MirrorConverseFails

/-!
# What replaces `hcross` when the reflection has a fixed layer

`ReflectionConverse` closed the wall's converse for fixed-point-free reflections and
`MirrorConverseFails` showed the hypothesis cannot be dropped. That left a new leg, written into
`UNLOCK_WATCHLIST` as the successor question:

> a criterion for reflection positivity on a **mirror** half at a fixed mass. `hcross` is
> sufficient and now known not necessary, and any replacement must be mass-dependent. The
> mechanism is named and unmeasured: on the even sector the operator couples the half to the
> fixed layer, the even energy acquires a Schur complement, and that correction can only help
> positivity. **Nothing in the estate measures it.**

This file measures it.

## The condition

`hcross` says the coupling form is `≤ 0`. The replacement says it is `≤` **what an energy over
the fixed layer can pay**:

    MirrorDominated : ∀ u, ∃ w supported on Mir,
        crossForm u ≤ 2 ⟪u, N w⟫ − ⟪w, N w⟫

Both terms on the right are ordinary sums against the massive operator — no inverse, no Schur
complement, nothing to invert. When `Mir = ∅` the only `w` is zero, both terms vanish, and the
condition **is** `hcross` (§4), so this is a genuine weakening rather than a different condition.

`§3` proves it sufficient, on every graph with a mirror reflection, at every mass. The route is
`GraphMirrorReflection.reflectionPositive_mirror`'s, with one change: that proof feeds the
lower-bound inequality the sign-flipped odd maximiser `evenify H ξ`, and this one feeds it
`evenify H ξ + w`. The extra cross term is §2, and it is where the fixed layer enters.

## Why the supremum is the right thing, and that this is tight

Off the formal development, and marked as such: maximising `2⟪u, Nw⟫ − ⟪w, Nw⟫` over `w` on the
mirror gives `⟪u, E D⁻¹ Eᵀ u⟫`, with `E` the half-to-mirror block and `D` the mirror block. So the
condition is the Löwner inequality `B ⪯ E D⁻¹ Eᵀ` on the cross block `B`, and the argument that
proves `ReflectionConverse` backwards shows it is **necessary** too. That converse is not
formalised here — it needs the solution of `D w = −2 Eᵀ u` exhibited, which the sufficiency
direction does not.

An exhaustive exact-rational check over 77184 (graph, mass) pairs — every `σ`-invariant graph for
`(|H|,|Mir|) = (2,3)` and `(3,1)` on seven vertices, `(2,1)` on five and `(3,0)` on six, at six
masses each — found the criterion and reflection positivity **never** disagreeing. That is
computation, not proof, and is recorded in `WALLS` as such.

## The witness explained

`MirrorConverseFails.mirGraph` is reflection positive exactly for `m² ≤ 1`, established there by
an explicit five-by-five solve. §5 recovers positivity at `m = 1/2` from this criterion instead,
with the mirror vector written down and no solve at all — and the reason the threshold sits at
`m² = 1` becomes visible: the mirror block is `(2 + m²)·1`, the half-to-mirror coupling
contributes `3`, and `1 ≤ 3/(2 + m²)` is `m² ≤ 1`.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace MirrorDominance

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The condition -/

/-- **THE COUPLING IS PAID FOR BY THE MIRROR.** `hcross` is the case where nothing has to be
paid. Written with `massive` on both sides so that no inverse appears and the condition is
checkable from the adjacency relation and the mass alone. -/
def MirrorDominated (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H Mir : Finset V) : Prop :=
  ∀ u : V → ℝ, ∃ w : V → ℝ, (∀ p, p ∉ Mir → w p = 0) ∧
    crossForm G m θ H u
      ≤ 2 * (∑ p ∈ H, ∑ r ∈ Mir, u p * w r * massive G m p r)
          - ∑ r ∈ Mir, ∑ s ∈ Mir, w r * w s * massive G m r s

/-! ## 2. What the operator does to a sign-flipped odd vector on the mirror

The one new computation. An odd vector pairs to zero against any row of the operator fixed by the
reflection, and the sign flip turns that cancellation into a doubling.
-/

/-- An odd vector is orthogonal to every row of the operator indexed on the mirror. -/
theorem row_dot_odd_eq_zero (h : IsRefl G θ) (hM : IsMirrorHalf θ H Mir) {ξ : V → ℝ}
    (hξ : IsOddFun θ ξ) {r : V} (hr : r ∈ Mir) :
    ∑ q, massive G m r q * ξ q = 0 := by
  have hfix : θ r = r := (hM.fixed r).mp hr
  have key : ∑ q, massive G m r q * ξ q = -∑ q, massive G m r q * ξ q := by
    calc ∑ q, massive G m r q * ξ q
        = ∑ q, massive G m r (θ q) * ξ (θ q) :=
          (Fintype.sum_equiv θ _ _ fun _ => rfl).symm
      _ = ∑ q, -(massive G m r q * ξ q) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          have hN : massive G m r (θ q) = massive G m r q := by
            conv_lhs => rw [← hfix]
            exact congrFun (congrFun (h.massive m) r) q
          rw [hN, hξ q]; ring
      _ = -∑ q, massive G m r q * ξ q := by rw [Finset.sum_neg_distrib]
  linarith

/-- **THE SIGN FLIP DOUBLES THE HALF'S CONTRIBUTION ON THE MIRROR.** -/
theorem mulVec_evenify_on_mir (h : IsRefl G θ) (hM : IsMirrorHalf θ H Mir) {ξ : V → ℝ}
    (hξ : IsOddFun θ ξ) {r : V} (hr : r ∈ Mir) :
    (massive G m *ᵥ evenify H ξ) r = 2 * ∑ q ∈ H, massive G m r q * ξ q := by
  classical
  have hsplit : ∑ q, massive G m r q * ξ q
      = (∑ q ∈ H, massive G m r q * ξ q) + ∑ q ∈ Hᶜ, massive G m r q * ξ q :=
    (Finset.sum_add_sum_compl H _).symm
  have hzero := row_dot_odd_eq_zero (m := m) h hM hξ hr
  have hcompl : ∑ q ∈ Hᶜ, massive G m r q * ξ q = -∑ q ∈ H, massive G m r q * ξ q := by
    rw [hsplit] at hzero; linarith
  have hev : (massive G m *ᵥ evenify H ξ) r
      = (∑ q ∈ H, massive G m r q * ξ q) - ∑ q ∈ Hᶜ, massive G m r q * ξ q := by
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_add_sum_compl H (fun q => massive G m r q * evenify H ξ q), ← sub_neg_eq_add]
    congr 1
    · exact Finset.sum_congr rfl fun q hq => by rw [evenify_of_mem hq]
    · rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun q hq =>
        by rw [evenify_of_notMem (Finset.mem_compl.mp hq)]; ring
  rw [hev, hcompl]; ring

/-! ## 3. The condition is sufficient, on every graph and at every mass

`reflectionPositive_mirror` maximises `2⟪ξ,a⟫ − ⟪ξ,Nξ⟫` over the odd sector, sign-flips the
maximiser and feeds it back. Feed it the maximiser **plus a mirror vector** and the same
bookkeeping goes through: the linear term is untouched, because the symmetrisation of a vector
supported on the half vanishes on the mirror; the quadratic term picks up exactly the two extra
sums the condition budgets for.
-/

theorem reflectionPositive_of_mirrorDominated (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hdom : MirrorDominated G m θ H Mir) :
    GraphReflection.ReflectionPositive G m θ H := by
  classical
  intro c hc
  set N := massive G m with hN
  have hNpd : N.PosDef := massive_posDef G hm
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hNpd.isUnit
  set a := GraphReflection.anti θ c with ha
  set s := GraphReflection.sym θ c with hs
  set ξ : V → ℝ := N⁻¹ *ᵥ a with hξdef
  -- the odd maximiser, exactly as in `reflectionPositive_mirror`
  have haodd : ∀ q, a (θ q) = -a q := by
    intro q; simp only [ha, GraphReflection.anti, h.invol q]; ring
  have hξodd : IsOddFun θ ξ := by
    intro p
    have hgreen : ∀ x y, GraphLaplacian.green G m (θ x) (θ y) = GraphLaplacian.green G m x y :=
      fun x y => GraphReflection.green_aut h m x y
    have hNinv : N⁻¹ = GraphLaplacian.green G m := rfl
    simp only [hξdef, hNinv, Matrix.mulVec, dotProduct]
    rw [← Fintype.sum_equiv θ (fun q => GraphLaplacian.green G m (θ p) (θ q) * a (θ q))
      (fun q => GraphLaplacian.green G m (θ p) q * a q) (fun _ => rfl)]
    simp only [hgreen, haodd, mul_neg, Finset.sum_neg_distrib]
  have hNξ : N *ᵥ ξ = a := by
    rw [hξdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  -- the antisymmetric energy, exactly
  have hAeq : GraphReflection.energy G m a = ξ ⬝ᵥ a := by
    rw [energy_eq_dotProduct, show GraphLaplacian.green G m = N⁻¹ from rfl, ← hξdef,
      dotProduct_comm]
  have hξNξ : ξ ⬝ᵥ (N *ᵥ ξ) = ξ ⬝ᵥ a := by rw [hNξ]
  -- the mirror vector the condition supplies, at the maximiser
  obtain ⟨w0, hw0supp, hw0bound⟩ := hdom ξ
  rw [← hN] at hw0bound
  set w : V → ℝ := fun p => -2 * w0 p with hwdef
  have hwsupp : ∀ p, p ∉ Mir → w p = 0 := fun p hp => by
    simp only [hwdef, hw0supp p hp]; ring
  set η : V → ℝ := evenify H ξ + w with hη
  have hηeven : IsEvenFun θ η := by
    intro p
    have h1 : evenify H ξ (θ p) = evenify H ξ p := evenify_isEven hM hξodd p
    have h2 : w (θ p) = w p := by
      by_cases hp : p ∈ Mir
      · rw [(hM.fixed p).mp hp]
      · have hθp : θ p ∉ Mir := by
          intro hc'
          have hfx : θ (θ p) = θ p := (hM.fixed _).mp hc'
          rw [h.invol p] at hfx
          exact hp ((hM.fixed p).mpr hfx.symm)
        rw [hwsupp p hp, hwsupp (θ p) hθp]
    simp only [hη, Pi.add_apply, h1, h2]
  -- the symmetric energy, bounded below at that test vector
  have hSge : 2 * (η ⬝ᵥ s) - η ⬝ᵥ (N *ᵥ η) ≤ GraphReflection.energy G m s := by
    rw [energy_eq_dotProduct, show GraphLaplacian.green G m = N⁻¹ from rfl]
    exact dotProduct_inv_le hNpd s η
  -- the linear term is untouched: `s` vanishes on the mirror
  have hsMir : ∀ r ∈ Mir, s r = 0 := by
    intro r hr
    have : θ r = r := (hM.fixed r).mp hr
    have hrH : r ∉ H := fun hc' => hM.disj r hc' hr
    simp only [hs, GraphReflection.sym, this, hc r hrH]; ring
  have hwS : w ⬝ᵥ s = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r ∈ Mir
    · rw [hsMir r hr, mul_zero]
    · rw [hwsupp r hr, zero_mul]
  have hlin : η ⬝ᵥ s = ξ ⬝ᵥ a := by
    have h1 : evenify H ξ ⬝ᵥ s = ξ ⬝ᵥ a := by
      rw [hs, dotProduct_sym (evenify_isEven hM hξodd) c,
        dotProduct_evenify_eq hM hξodd (fun p hp _ => hc p hp), ha,
        dotProduct_anti hξodd c]
    simpa [hη, add_dotProduct, hwS] using h1
  -- the quadratic term picks up exactly the two sums the condition budgets for
  have hcrossMir : ∀ r ∈ Mir, (N *ᵥ evenify H ξ) r = 2 * ∑ q ∈ H, N r q * ξ q :=
    fun r hr => mulVec_evenify_on_mir h hM hξodd hr
  have hquad : η ⬝ᵥ (N *ᵥ η)
      = ξ ⬝ᵥ (N *ᵥ ξ) + 4 * crossForm G m θ H ξ
        + 4 * (∑ p ∈ H, ∑ r ∈ Mir, ξ p * w r * N p r)
        + ∑ r ∈ Mir, ∑ s' ∈ Mir, w r * w s' * N r s' := by
    have hqd : evenify H ξ ⬝ᵥ (N *ᵥ evenify H ξ) - ξ ⬝ᵥ (N *ᵥ ξ) = 4 * crossForm G m θ H ξ :=
      quadDiff hM hξodd
    have hsymN : ∀ x y, N x y = N y x :=
      fun x y => congrFun (congrFun (GraphLaplacian.massive_isSymm G m) y) x
    have hcross2 : w ⬝ᵥ (N *ᵥ evenify H ξ) = 2 * ∑ p ∈ H, ∑ r ∈ Mir, ξ p * w r * N p r := by
      have hL : w ⬝ᵥ (N *ᵥ evenify H ξ) = ∑ r ∈ Mir, ∑ q ∈ H, 2 * (ξ q * w r * N q r) := by
        rw [dotProduct, ← Finset.sum_subset (Finset.subset_univ Mir)
          (fun r _ hr => by rw [hwsupp r hr, zero_mul])]
        refine Finset.sum_congr rfl fun r hr => ?_
        rw [hcrossMir r hr, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by rw [hsymN r q]; ring
      have hR : 2 * ∑ p ∈ H, ∑ r ∈ Mir, ξ p * w r * N p r
          = ∑ r ∈ Mir, ∑ q ∈ H, 2 * (ξ q * w r * N q r) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by rw [Finset.mul_sum]
      rw [hL, hR]
    have hwNw : w ⬝ᵥ (N *ᵥ w) = ∑ r ∈ Mir, ∑ s' ∈ Mir, w r * w s' * N r s' := by
      rw [dotProduct]
      rw [← Finset.sum_subset (Finset.subset_univ Mir)
        (fun r _ hr => by rw [hwsupp r hr, zero_mul])]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      rw [← Finset.sum_subset (Finset.subset_univ Mir)
        (fun s' _ hs' => by rw [hwsupp s' hs']; ring)]
      exact Finset.sum_congr rfl fun s' _ => by ring
    have hexp : η ⬝ᵥ (N *ᵥ η)
        = evenify H ξ ⬝ᵥ (N *ᵥ evenify H ξ) + 2 * (w ⬝ᵥ (N *ᵥ evenify H ξ)) + w ⬝ᵥ (N *ᵥ w) := by
      have hsym2 : evenify H ξ ⬝ᵥ (N *ᵥ w) = w ⬝ᵥ (N *ᵥ evenify H ξ) := by
        simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
          rw [hsymN y x]; ring
      simp only [hη, Matrix.mulVec_add, add_dotProduct, dotProduct_add, hsym2]
      ring
    rw [hexp, hcross2, hwNw]
    linarith [hqd]
  -- assemble
  have hfinal : 0 ≤ GraphReflection.reflectedForm G m θ c := by
    have hre := GraphReflection.reflectedForm_eq (m := m) h c
    rw [← hs, ← ha] at hre
    -- the test vector is `-2 w0`, which is what turns the condition's budget into the loss
    have hE : ∑ p ∈ H, ∑ r ∈ Mir, ξ p * w r * N p r
        = -2 * ∑ p ∈ H, ∑ r ∈ Mir, ξ p * w0 r * N p r := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by simp only [hwdef]; ring
    have hD : ∑ r ∈ Mir, ∑ s' ∈ Mir, w r * w s' * N r s'
        = 4 * ∑ r ∈ Mir, ∑ s' ∈ Mir, w0 r * w0 s' * N r s' := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s' _ => by simp only [hwdef]; ring
    rw [hlin] at hSge
    rw [hE, hD] at hquad
    linarith [hSge, hquad, hAeq, hre, hw0bound, hξNξ]
  exact hfinal

/-! ## 4. With no mirror it is exactly `hcross`, so this is a weakening and not a change -/

theorem mirrorDominated_iff_hcross_of_empty_mir :
    MirrorDominated G m θ H (∅ : Finset V) ↔ ∀ u : V → ℝ, crossForm G m θ H u ≤ 0 := by
  constructor
  · intro hdom u
    obtain ⟨w, _, hb⟩ := hdom u
    simpa using hb
  · intro hc u
    exact ⟨0, fun _ _ => rfl, by simpa using hc u⟩

/-- **AND `hcross` STILL IMPLIES IT, ON ANY MIRROR**, by taking `w = 0` — so §3 subsumes
`reflectionPositive_mirror` rather than competing with it. -/
theorem mirrorDominated_of_hcross (hc : ∀ u : V → ℝ, crossForm G m θ H u ≤ 0) :
    MirrorDominated G m θ H Mir :=
  fun u => ⟨0, fun _ _ => rfl, by simpa using hc u⟩

/-! ## 5. The witness, explained rather than computed

`MirrorConverseFails.reflectionPositive_half` established positivity at `m = 1/2` by exhibiting
the solution of a five-by-five system. Here the same conclusion comes from §3 with an explicit
mirror vector and no system at all, and the arithmetic shows where `m² = 1` comes from.
-/

open MirrorConverseFails

/-- The mirror vector that pays for the coupling on `mirGraph`: put `−u₀·(4/9)` on each of the
three fixed sites, `4/9` being `2/(2 + m²)` at `m = 1/2`. -/
noncomputable def payer (u : Fin 7 → ℝ) : Fin 7 → ℝ :=
  fun p => if p ∈ Mirm then -(4 / 9) * u 0 else 0

theorem payer_supported (u : Fin 7 → ℝ) : ∀ p, p ∉ Mirm → payer u p = 0 :=
  fun _ hp => if_neg hp

/-- **THE CRITERION HOLDS ON `mirGraph` AT `m = 1/2`.** -/
theorem mirrorDominated_mirGraph : MirrorDominated mirGraph (1 / 2) tau Hm Mirm := by
  intro u
  refine ⟨payer u, payer_supported u, ?_⟩
  have hsumM : ∀ f : Fin 7 → ℝ, ∑ r ∈ Mirm, f r = f 4 + f 5 + f 6 := by
    intro f
    rw [show Mirm = ({4, 5, 6} : Finset (Fin 7)) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  have hp4 : payer u 4 = -(4 / 9) * u 0 := if_pos (by decide)
  have hp5 : payer u 5 = -(4 / 9) * u 0 := if_pos (by decide)
  have hp6 : payer u 6 = -(4 / 9) * u 0 := if_pos (by decide)
  have hcf : crossForm mirGraph (1 / 2) tau Hm u
      = -(2 * (u 0 * u 1)) - u 1 * u 1 := by
    have t0 : tau 0 = 2 := rfl
    have t1 : tau 1 = 3 := rfl
    simp only [crossForm, sum_Hm, t0, t1, GraphLaplacian.massive_apply,
      if_neg (show ¬ ((0 : Fin 7) = 2) by decide), if_neg (show ¬ ((0 : Fin 7) = 3) by decide),
      if_neg (show ¬ ((1 : Fin 7) = 2) by decide), if_neg (show ¬ ((1 : Fin 7) = 3) by decide),
      if_neg (show ¬ mirGraph.Adj 0 2 by decide), if_pos (show mirGraph.Adj 0 3 by decide),
      if_pos (show mirGraph.Adj 1 2 by decide), if_pos (show mirGraph.Adj 1 3 by decide)]
    ring
  have hE : ∑ p ∈ Hm, ∑ r ∈ Mirm, u p * payer u r * massive mirGraph (1 / 2) p r
      = (4 / 3) * (u 0 * u 0) := by
    simp only [sum_Hm, hsumM, GraphLaplacian.massive_apply, hp4, hp5, hp6,
      if_neg (show ¬ ((0 : Fin 7) = 4) by decide), if_neg (show ¬ ((0 : Fin 7) = 5) by decide),
      if_neg (show ¬ ((0 : Fin 7) = 6) by decide), if_neg (show ¬ ((1 : Fin 7) = 4) by decide),
      if_neg (show ¬ ((1 : Fin 7) = 5) by decide), if_neg (show ¬ ((1 : Fin 7) = 6) by decide),
      if_pos (show mirGraph.Adj 0 4 by decide), if_pos (show mirGraph.Adj 0 5 by decide),
      if_pos (show mirGraph.Adj 0 6 by decide), if_neg (show ¬ mirGraph.Adj 1 4 by decide),
      if_neg (show ¬ mirGraph.Adj 1 5 by decide), if_neg (show ¬ mirGraph.Adj 1 6 by decide)]
    ring
  have hD : ∑ r ∈ Mirm, ∑ s ∈ Mirm, payer u r * payer u s * massive mirGraph (1 / 2) r s
      = (4 / 3) * (u 0 * u 0) := by
    simp only [hsumM, GraphLaplacian.massive_apply, hp4, hp5, hp6,
      show mirGraph.degree 4 = 2 by decide, show mirGraph.degree 5 = 2 by decide,
      show mirGraph.degree 6 = 2 by decide,
      if_neg (show ¬ ((4 : Fin 7) = 5) by decide), if_neg (show ¬ ((4 : Fin 7) = 6) by decide),
      if_neg (show ¬ ((5 : Fin 7) = 4) by decide), if_neg (show ¬ ((5 : Fin 7) = 6) by decide),
      if_neg (show ¬ ((6 : Fin 7) = 4) by decide), if_neg (show ¬ ((6 : Fin 7) = 5) by decide),
      if_neg (show ¬ mirGraph.Adj 4 5 by decide), if_neg (show ¬ mirGraph.Adj 4 6 by decide),
      if_neg (show ¬ mirGraph.Adj 5 4 by decide), if_neg (show ¬ mirGraph.Adj 5 6 by decide),
      if_neg (show ¬ mirGraph.Adj 6 4 by decide), if_neg (show ¬ mirGraph.Adj 6 5 by decide),
      if_neg (show ¬ mirGraph.Adj 4 4 by decide), if_neg (show ¬ mirGraph.Adj 5 5 by decide),
      if_neg (show ¬ mirGraph.Adj 6 6 by decide),
      if_true]
    ring
  rw [hcf, hE, hD]
  nlinarith [sq_nonneg (u 0 + u 1), sq_nonneg (u 0), sq_nonneg (u 1)]

/-- **A SECOND ROUTE TO `MirrorConverseFails.reflectionPositive_half`.** That theorem solved a
five-by-five system; this one supplies one vector and cites §3. The two share no lemma below
`crossForm`, so their agreement is a check on both. -/
theorem reflectionPositive_half_second_route :
    GraphReflection.ReflectionPositive mirGraph (1 / 2) tau Hm :=
  reflectionPositive_of_mirrorDominated isMirrorHalf_Hm isRefl_tau (by norm_num)
    mirrorDominated_mirGraph

/-- **AND THE CRITERION IS STRICTLY WEAKER THAN `hcross`**, witnessed on the same graph:
`mirGraph` satisfies it and fails `hcross`. Without a witness this would be a definition with no
content. -/
theorem strictly_weaker_than_hcross :
    MirrorDominated mirGraph (1 / 2) tau Hm Mirm
      ∧ ¬ ∀ u : Fin 7 → ℝ, crossForm mirGraph (1 / 2) tau Hm u ≤ 0 :=
  ⟨mirrorDominated_mirGraph, hcross_fails _⟩

end MirrorDominance
