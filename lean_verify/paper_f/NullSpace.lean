/-
  NullSpace.lean — the null space of the reflected form, exactly, and a
  discarded remainder that was sitting in a proof for a week.

  WHY. The negative results on this wall exhibit a SUBSPACE of the null space
  and say so. **Counted rather than recalled** (ERRATUM 74's rule, and see §8
  — the first draft of this sentence broke it): grepping `paper_f` for the
  claim returns THREE files — `BoxOddNotStrict` ("it exhibits a subspace of
  it. Whether that subspace is all of it is open"), `OddNotStrictInstances`
  ("still a subspace, not the null space") and `SmallSideStrict`, written
  earlier today. `BoxNotStrict`, `TorusNotStrict` and `ReachCriterion` do NOT
  carry it. The watchlist records the question in three places, all written
  2026-08-10. **It is not open, and the answer was already written down.**

  **WHERE IT WAS.** `GraphMirrorReflection.dotProduct_inv_le` proves
  completing-the-square by establishing, as a `have` inside its own proof, the
  EXACT identity

      `⟪ξ−z, N(ξ−z)⟫ = ⟪ξ,Nξ⟫ − 2⟪ξ,y⟫ + ⟪z,y⟫`   (`Nz = y`),

  and then throws the left-hand side away and keeps its sign. Beside it,
  `dotProduct_inv_eq` records that the bound is attained — the file's own
  header calls that "recorded because a one-sided estimate that is never sharp
  would make the argument lossy". **Both halves of the equality case were
  therefore already proved, and neither was ever used for anything but a
  sign.** This is the SECOND time this month that a term a proof discards was
  itself the theorem — `MirrorStrict` was the first, and kept one where this
  file keeps both — and the third instance of the wider pattern, an exact
  identity in the estate being consumed only for its sign, of which
  `BoxOddNotStrict`'s use of `quadDiff` was the first. The recurrence is
  recorded in §8 rather than in the commit message.

  **WHAT COMES OUT.** Not an estimate with an equality case bolted on, but a
  single exact identity with no hypothesis on the coupling at all:

      `4 · reflectedForm c = ⟪e−z, N(e−z)⟫ − 4 · crossForm ξ`,

  where `ξ = green · anti c` is the test vector the argument optimises at,
  `e = evenify H ξ` its sign-flip across the cut, and `z = green · sym c`.
  **The reflected form is a sum of two independently signed pieces**, and
  `reflectionPositive_mirror` is the corollary that drops the first and
  assumes the second nonpositive. Because `N` is positive definite the first
  piece vanishes only at `e = z`, so under the standing coupling hypothesis

      `reflectedForm c = 0  ⟺  evenify H ξ = z  and  crossForm ξ = 0`,

  and the first of those two conditions is what turns a subspace into the
  whole space: `N e = s` and `N ξ = a` force `N` applied to the part of `ξ`
  living on the half to be exactly `c`. **So every null direction is the
  massive operator applied to something supported on the half** — which is
  precisely the shape every negative file constructed by hand.

  WHAT THIS FILE PROVES:
  1. **`dotProduct_slack`** — the identity extracted from inside
     `dotProduct_inv_le`, stated with the inverse ELIMINATED: it asks only for
     some `z` with `Nz = y`, so it never mentions `N⁻¹` and applies wherever a
     solve is available. **`dotProduct_inv_le'`** and **`dotProduct_inv_eq'`**
     re-derive `GraphMirrorReflection`'s two originals from it verbatim, as the
     check that eliminating the inverse cost nothing (ERRATUM 48).
  2. **`dotProduct_slack_eq_iff`** — the equality case: the bound is attained
     at `ξ = z` and NOWHERE ELSE. Positive definiteness, used for the one
     thing only positive definiteness gives.
  3. **`reflectedForm_slack`** — **the exact identity above**, over an
     arbitrary graph and an arbitrary mirror half, with NO hypothesis on the
     coupling. The content of the file; §§4–5 instantiate it.
  4. **`reflectedForm_eq_zero_iff`** — hence, when the coupling is nonpositive,
     the null space is cut out by two equations rather than bounded below by a
     construction.
  5. **`exists_massive_of_eq_zero`** — **every null direction is
     `massive *ᵥ v` for some `v` supported on the half.** The converse of
     `BoxOddNotStrict.reflectedForm_massive_eq_crossForm`, which is the
     direction every negative file proved.
  6. **`reflectedForm_eq_zero_iff_massive`** — the two directions composed:
     the null space is EXACTLY the massive image of the coupling's isotropic
     cone on the half.
  7. **`nullSpace_box_odd`** — instantiated at the odd box, where the coupling
     vanishes identically, so the null space is exactly
     `{massive *ᵥ v : v supported strictly below the midline}`. **The subspace
     `BoxOddNotStrict` exhibited is the whole null space**, and the sentence
     three files carry is answered rather than repeated.

  WHAT THIS DOES NOT DO.
  * **It does not compute a dimension.** The null space is characterised as a
    massive image of an isotropic cone; how big that cone is depends on the
    graph, and at the odd box it is everything only because the coupling is
    identically zero there. No dimension is claimed anywhere.
    **AMENDED 2026-08-10, SAME DAY: computed at the odd box.**
    `NullSpaceDimension.finrank_nullSub_box_odd` — the null space is a genuine
    subspace there (the cone is everything, exactly for the reason this bullet
    gives) of dimension the number of sites STRICTLY below the midline, and
    `nullSub_lt_admissible_box_odd` measures the deficiency: one layer, the
    midline. **The bullet stays true everywhere else**, and for the reason
    stated — at even side and on the torus the cone is a proper quadric, the
    null set need not be a subspace, and a dimension is the wrong question
    rather than a hard one.
  * **It does not remove the coupling hypothesis from §§4–6.** §3 is
    unconditional, but "the form vanishes iff two things vanish" needs both
    pieces to have a sign, and only the first has one for free. Where the
    coupling is indefinite the identity still holds and the characterisation
    does not, and that is stated rather than skirted.
  * **Nothing for `BoxNotStrict`'s even-side construction.** That file's null
    direction comes from a vertex the cut cannot see, and §5 says every null
    direction has the massive shape — so the two must agree, but showing that
    its explicit witness IS of that shape is a separate calculation and is not
    done here.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SmallSideStrict

namespace NullSpace

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection BoxOddReflection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. Completing the square, with the remainder kept

`GraphMirrorReflection.dotProduct_inv_le` proves exactly the identity below
inside its own proof and then keeps only its sign. Stating it separately costs
nothing and is the whole of §3.

The inverse is eliminated on the way out: the hypothesis is that SOME `z`
solves `N z = y`, not that `N⁻¹` exists as a term. That makes the lemma usable
wherever a solve is available and removes every `Matrix.inv` side condition
from the callers.
-/

omit [DecidableEq V] in
/-- **THE REMAINDER.** For positive definite `N` and any `z` with `N z = y`,
    the gap between the linear-minus-quadratic expression at `ξ` and its value
    at `z` is a perfect square. No inverse appears. -/
theorem dotProduct_slack {N : Matrix V V ℝ} (hN : N.PosDef) {y z : V → ℝ}
    (hz : N *ᵥ z = y) (ξ : V → ℝ) :
    (ξ - z) ⬝ᵥ (N *ᵥ (ξ - z)) = ξ ⬝ᵥ (N *ᵥ ξ) - 2 * (ξ ⬝ᵥ y) + z ⬝ᵥ y := by
  classical
  have hsym : z ⬝ᵥ (N *ᵥ ξ) = ξ ⬝ᵥ y := by
    have h1 : z ⬝ᵥ (N *ᵥ ξ) = (N *ᵥ z) ⬝ᵥ ξ := by
      rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
        show Nᵀ = N from hN.isHermitian.eq]
    rw [h1, hz, dotProduct_comm]
  rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hz, hsym]
  ring

omit [DecidableEq V] in
/-- **THE BOUND, RE-DERIVED.** `GraphMirrorReflection.dotProduct_inv_le` in the
    inverse-free form, as the check that §1 lost nothing (ERRATUM 48). -/
theorem dotProduct_slack_le {N : Matrix V V ℝ} (hN : N.PosDef) {y z : V → ℝ}
    (hz : N *ᵥ z = y) (ξ : V → ℝ) :
    2 * (ξ ⬝ᵥ y) - ξ ⬝ᵥ (N *ᵥ ξ) ≤ z ⬝ᵥ y := by
  have hsq : 0 ≤ (ξ - z) ⬝ᵥ (N *ᵥ (ξ - z)) := by
    have := hN.posSemidef.dotProduct_mulVec_nonneg (ξ - z)
    simpa using this
  rw [dotProduct_slack hN hz ξ] at hsq
  linarith

omit [DecidableEq V] in
/-- **AND IT IS ATTAINED AT ONE POINT ONLY.** The equality case, which is the
    half of completing the square that positive definiteness is for and that
    the estate had recorded (`dotProduct_inv_eq`) without ever using. -/
theorem dotProduct_slack_eq_iff {N : Matrix V V ℝ} (hN : N.PosDef) {y z : V → ℝ}
    (hz : N *ᵥ z = y) (ξ : V → ℝ) :
    2 * (ξ ⬝ᵥ y) - ξ ⬝ᵥ (N *ᵥ ξ) = z ⬝ᵥ y ↔ ξ = z := by
  classical
  constructor
  · intro heq
    have hzero : (ξ - z) ⬝ᵥ (N *ᵥ (ξ - z)) = 0 := by
      rw [dotProduct_slack hN hz ξ]; linarith
    by_contra hne
    have hsub : ξ - z ≠ 0 := fun hc => hne (by
      have := congrFun hc
      funext p
      have := this p
      simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this)
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hN).2 hsub
    simp only [star_trivial] at hpos
    linarith
  · rintro rfl
    have := dotProduct_slack hN hz ξ
    simp only [sub_self, Matrix.mulVec_zero, dotProduct_zero] at this
    linarith

/-- **`GraphMirrorReflection.dotProduct_inv_le`, RE-DERIVED FROM §1.** The
    original statement, verbatim, from the inverse-free lemma — the check that
    eliminating `N⁻¹` cost nothing (ERRATUM 48). -/
theorem dotProduct_inv_le' {N : Matrix V V ℝ} (hN : N.PosDef) (y ξ : V → ℝ) :
    2 * (ξ ⬝ᵥ y) - ξ ⬝ᵥ (N *ᵥ ξ) ≤ y ⬝ᵥ (N⁻¹ *ᵥ y) := by
  classical
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  have hz : N *ᵥ (N⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  have := dotProduct_slack_le hN hz ξ
  rwa [dotProduct_comm (N⁻¹ *ᵥ y) y] at this

/-- **`GraphMirrorReflection.dotProduct_inv_eq`, RE-DERIVED FROM §1**, as the
    other half of the same check. -/
theorem dotProduct_inv_eq' {N : Matrix V V ℝ} (hN : N.PosDef) (y : V → ℝ) :
    2 * ((N⁻¹ *ᵥ y) ⬝ᵥ y) - (N⁻¹ *ᵥ y) ⬝ᵥ (N *ᵥ (N⁻¹ *ᵥ y))
      = y ⬝ᵥ (N⁻¹ *ᵥ y) := by
  classical
  have hdet : IsUnit N.det := (Matrix.isUnit_iff_isUnit_det N).mp hN.isUnit
  have hz : N *ᵥ (N⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hdet, Matrix.one_mulVec]
  rw [(dotProduct_slack_eq_iff hN hz (N⁻¹ *ᵥ y)).mpr rfl]
  exact dotProduct_comm _ _

/-! ## 2. Solving against the massive operator

`GraphLaplacian.green` IS the inverse, so this is `mul_nonsing_inv` with the
determinant side condition discharged once instead of at every call site.
-/

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

theorem massive_mulVec_green (hm : m ≠ 0) (v : V → ℝ) :
    GraphLaplacian.massive G m *ᵥ (GraphLaplacian.green G m *ᵥ v) = v := by
  classical
  have hdet : IsUnit (GraphLaplacian.massive G m).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (GraphLaplacian.massive_posDef G hm).isUnit
  rw [show GraphLaplacian.green G m = (GraphLaplacian.massive G m)⁻¹ from rfl,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The optimiser is odd, because the Green function commutes with the
    reflection. Extracted from `reflectionPositive_mirror`, which proves it
    inline. -/
theorem green_anti_isOddFun (h : IsRefl G θ) (m : ℝ) (c : V → ℝ) :
    IsOddFun θ (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c) := by
  intro p
  have hgreen : ∀ x y, GraphLaplacian.green G m (θ x) (θ y) = GraphLaplacian.green G m x y :=
    fun x y => GraphReflection.green_aut h m x y
  have haodd : ∀ q, GraphReflection.anti θ c (θ q) = -GraphReflection.anti θ c q := by
    intro q
    simp only [GraphReflection.anti, h.invol q]
    ring
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_equiv θ
    (fun q => GraphLaplacian.green G m (θ p) (θ q) * GraphReflection.anti θ c (θ q))
    (fun q => GraphLaplacian.green G m (θ p) q * GraphReflection.anti θ c q) (fun _ => rfl)]
  simp only [hgreen, haodd, mul_neg, Finset.sum_neg_distrib]

/-! ## 3. The exact identity

Everything `reflectionPositive_mirror` establishes, with nothing discarded.
Both remainders are kept: the completing-the-square square and the coupling.
-/

/-- **THE REFLECTED FORM, EXACTLY.** Over an arbitrary graph and an arbitrary
    mirror half, with **no hypothesis on the coupling**: four times the
    reflected form is a perfect square minus four times the coupling at the
    optimiser. `reflectionPositive_mirror` is this with the square dropped and
    the coupling assumed nonpositive. -/
theorem reflectedForm_slack (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    4 * GraphReflection.reflectedForm G m θ c
      = (evenify H (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c)
            - GraphLaplacian.green G m *ᵥ GraphReflection.sym θ c) ⬝ᵥ
          (GraphLaplacian.massive G m *ᵥ
            (evenify H (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c)
              - GraphLaplacian.green G m *ᵥ GraphReflection.sym θ c))
        - 4 * crossForm G m θ H
            (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c) := by
  classical
  have hNpd : (GraphLaplacian.massive G m).PosDef := GraphLaplacian.massive_posDef G hm
  set a := GraphReflection.anti θ c with ha
  set s := GraphReflection.sym θ c with hs
  set ξ : V → ℝ := GraphLaplacian.green G m *ᵥ a with hξdef
  have hξodd : IsOddFun θ ξ := green_anti_isOddFun h m c
  have hNξ : GraphLaplacian.massive G m *ᵥ ξ = a := massive_mulVec_green hm a
  have hNz : GraphLaplacian.massive G m *ᵥ (GraphLaplacian.green G m *ᵥ s) = s :=
    massive_mulVec_green hm s
  -- the antisymmetric energy, exactly, at the optimiser
  have hAeq : GraphReflection.energy G m a = ξ ⬝ᵥ a := by
    rw [GraphMirrorReflection.energy_eq_dotProduct, hξdef, dotProduct_comm]
  -- the symmetric energy, with the remainder kept
  have hSslack := dotProduct_slack hNpd hNz (evenify H ξ)
  have hSenergy : GraphReflection.energy G m s = (GraphLaplacian.green G m *ᵥ s) ⬝ᵥ s := by
    rw [GraphMirrorReflection.energy_eq_dotProduct, dotProduct_comm]
  -- the linear terms coincide
  have hlin : evenify H ξ ⬝ᵥ s = ξ ⬝ᵥ a := by
    rw [hs, ha, dotProduct_sym (evenify_isEven hM hξodd) c,
      dotProduct_anti hξodd c, dotProduct_evenify_eq hM hξodd hc]
  -- the quadratic terms differ by the coupling
  have hquad := quadDiff (G := G) (m := m) hM hξodd
  have h4 := GraphReflection.reflectedForm_eq (G := G) (m := m) h c
  rw [← hs, ← ha] at h4
  rw [hAeq, hSenergy] at h4
  -- the optimiser's own quadratic term IS its linear term, because `N ξ = a`
  have hxx : ξ ⬝ᵥ (GraphLaplacian.massive G m *ᵥ ξ) = ξ ⬝ᵥ a := by rw [hNξ]
  linarith [hSslack, hquad, hlin, h4, hxx]

/-! ## 4. The null space, cut out by two equations

The square has a sign for free. The coupling does not, so this section carries
the hypothesis the positivity theorem carries, and §3 above does not.
-/

/-- **WHEN THE REFLECTED FORM VANISHES.** Two independent conditions: the
    optimiser's sign-flip must solve the symmetric problem exactly, and the
    coupling must vanish at the optimiser. -/
theorem reflectedForm_eq_zero_iff (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    GraphReflection.reflectedForm G m θ c = 0
      ↔ evenify H (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c)
            = GraphLaplacian.green G m *ᵥ GraphReflection.sym θ c
        ∧ crossForm G m θ H (GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c) = 0 := by
  classical
  have hNpd : (GraphLaplacian.massive G m).PosDef := GraphLaplacian.massive_posDef G hm
  set ξ : V → ℝ := GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c with hξdef
  set z : V → ℝ := GraphLaplacian.green G m *ᵥ GraphReflection.sym θ c with hzdef
  have hslack := reflectedForm_slack hM h hm hc
  rw [← hξdef, ← hzdef] at hslack
  have hsq : 0 ≤ (evenify H ξ - z) ⬝ᵥ (GraphLaplacian.massive G m *ᵥ (evenify H ξ - z)) := by
    have := hNpd.posSemidef.dotProduct_mulVec_nonneg (evenify H ξ - z)
    simpa using this
  have hcr := hcross ξ
  constructor
  · intro hzero
    rw [hzero] at hslack
    have hsq0 : (evenify H ξ - z) ⬝ᵥ (GraphLaplacian.massive G m *ᵥ (evenify H ξ - z)) = 0 := by
      linarith
    refine ⟨?_, by linarith⟩
    by_contra hne
    have hsub : evenify H ξ - z ≠ 0 := fun hcz => hne (by
      funext p
      have := congrFun hcz p
      simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this)
    have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hNpd).2 hsub
    simp only [star_trivial] at hpos
    linarith
  · rintro ⟨heq, hcr0⟩
    rw [heq, sub_self, Matrix.mulVec_zero, dotProduct_zero, hcr0] at hslack
    linarith

/-! ## 5. Every null direction has the massive shape

This is the converse of the identity every negative file on this wall uses.
`N e = s` and `N ξ = a` between them force `N` applied to the part of `ξ`
living on the half to be exactly `c`, because `e + ξ` is twice that part and
`s + a` is twice `c`.
-/

/-- The part of the optimiser living on the half. -/
noncomputable def onHalf (H : Finset V) (ξ : V → ℝ) : V → ℝ :=
  fun p => if p ∈ H then ξ p else 0

omit [Fintype V] in
theorem onHalf_supported (H : Finset V) (ξ : V → ℝ) {p : V} (hp : p ∉ H) :
    onHalf H ξ p = 0 := if_neg hp

omit [Fintype V] in
theorem evenify_add_self (H : Finset V) (ξ : V → ℝ) (p : V) :
    evenify H ξ p + ξ p = 2 * onHalf H ξ p := by
  classical
  by_cases hp : p ∈ H
  · rw [evenify_of_mem hp, onHalf, if_pos hp]; ring
  · rw [evenify_of_notMem hp, onHalf, if_neg hp]; ring

omit [Fintype V] in
/-- The odd extension of the on-half part is the optimiser itself. Needed so
    that §6's two directions are talking about the same coupling. -/
theorem anti_onHalf (hM : IsMirrorHalf θ H Mir) {ξ : V → ℝ} (hξ : IsOddFun θ ξ) :
    GraphReflection.anti θ (onHalf H ξ) = ξ := by
  classical
  funext p
  simp only [GraphReflection.anti, onHalf]
  by_cases hp : p ∈ H
  · rw [if_pos hp, if_neg (hM.notMem_of_mem hp)]; ring
  · by_cases hMir : p ∈ Mir
    · have hfix : θ p = p := (hM.fixed p).mp hMir
      rw [if_neg hp, hfix, if_neg hp, hξ.eq_zero_on_fixed hM hMir]; ring
    · rw [if_neg hp, if_pos (hM.mem_of_notMem hp hMir), hξ p]; ring

/-- **EVERY NULL DIRECTION IS THE MASSIVE OPERATOR APPLIED TO SOMETHING ON THE
    HALF.** The converse of `BoxOddNotStrict.reflectedForm_massive_eq_crossForm`,
    which is the direction every negative file on this wall proves by
    construction. -/
theorem exists_massive_of_eq_zero (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0)
    (hzero : GraphReflection.reflectedForm G m θ c = 0) :
    ∃ v : V → ℝ, (∀ p, p ∉ H → v p = 0) ∧ GraphLaplacian.massive G m *ᵥ v = c
      ∧ GraphReflection.anti θ v
          = GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c := by
  classical
  obtain ⟨heq, -⟩ := (reflectedForm_eq_zero_iff hM h hm hcross hc).mp hzero
  set ξ : V → ℝ := GraphLaplacian.green G m *ᵥ GraphReflection.anti θ c with hξdef
  refine ⟨onHalf H ξ, fun p hp => onHalf_supported H ξ hp, ?_,
    anti_onHalf hM (hξdef ▸ green_anti_isOddFun h m c)⟩
  have hNξ : GraphLaplacian.massive G m *ᵥ ξ = GraphReflection.anti θ c :=
    massive_mulVec_green hm _
  have hNe : GraphLaplacian.massive G m *ᵥ evenify H ξ = GraphReflection.sym θ c := by
    rw [heq]; exact massive_mulVec_green hm _
  funext p
  have hsum : (GraphLaplacian.massive G m *ᵥ (fun q => evenify H ξ q + ξ q)) p
      = GraphReflection.sym θ c p + GraphReflection.anti θ c p := by
    have : (fun q => evenify H ξ q + ξ q) = evenify H ξ + ξ := rfl
    rw [this, Matrix.mulVec_add]
    simp only [Pi.add_apply]
    rw [hNe, hNξ]
  have hsc : GraphReflection.sym θ c p + GraphReflection.anti θ c p = 2 * c p := by
    simp only [GraphReflection.sym, GraphReflection.anti]; ring
  have hdouble : (GraphLaplacian.massive G m *ᵥ (fun q => 2 * onHalf H ξ q)) p
      = 2 * (GraphLaplacian.massive G m *ᵥ onHalf H ξ) p := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [funext (evenify_add_self H ξ)] at hsum
  rw [hdouble, hsc] at hsum
  linarith

/-! ## 6. The two directions composed, and the odd box -/

/-- **THE NULL SPACE, EXACTLY.** It is the massive image of the coupling's
    isotropic cone on the half — no larger, which is §5, and no smaller, which
    is the identity every negative file used. -/
theorem reflectedForm_eq_zero_iff_massive (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    GraphReflection.reflectedForm G m θ c = 0
      ↔ ∃ v : V → ℝ, (∀ p, p ∉ H → v p = 0) ∧ GraphLaplacian.massive G m *ᵥ v = c
          ∧ crossForm G m θ H (GraphReflection.anti θ v) = 0 := by
  classical
  constructor
  · intro hzero
    obtain ⟨-, hcr0⟩ := (reflectedForm_eq_zero_iff hM h hm hcross hc).mp hzero
    obtain ⟨v, hvsupp, hvc, hvanti⟩ := exists_massive_of_eq_zero hM h hm hcross hc hzero
    exact ⟨v, hvsupp, hvc, hvanti ▸ hcr0⟩
  · rintro ⟨v, hvsupp, rfl, hcr0⟩
    rw [BoxOddNotStrict.reflectedForm_massive_eq_crossForm hM h hm hvsupp]
    exact hcr0

/-! ## 7. The odd box: the exhibited subspace was the whole thing

`BoxOddReflection.crossForm_odd_eq_zero` says the coupling vanishes
identically at odd side, so the isotropic-cone condition in §6 is free and the
characterisation collapses to a single clause.
-/

section OddBox

variable {d n : ℕ}

/-- **THE NULL SPACE OF THE ODD BOX, EXACTLY.** A coefficient family supported
    on the lower half is null **if and only if** it is the massive operator
    applied to something supported STRICTLY below the midline. The `if` is
    `BoxOddNotStrict`'s construction; the `only if` is §5, and it is what
    three files on this wall recorded as open. -/
theorem nullSpace_box_odd (i : Fin d) (hn : Odd n) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d n → ℝ} (hc : ∀ p, p ∉ lowerHalf i n → c p = 0) :
    GraphReflection.reflectedForm (boxGraph d n) m
        (GraphReflection.revSite (n := n) i) c = 0
      ↔ ∃ v : BoxGraph.Site d n → ℝ, (∀ p, p ∉ strictLower i n → v p = 0)
          ∧ GraphLaplacian.massive (boxGraph d n) m *ᵥ v = c := by
  classical
  have hc' : ∀ p, p ∉ strictLower i n → p ∉ midLayer i n → c p = 0 := by
    intro p hp hmid
    refine hc p ?_
    rw [lowerHalf_eq_union]
    simp only [Finset.mem_union]
    tauto
  rw [reflectedForm_eq_zero_iff_massive (isMirrorHalf_strictLower i n)
    (GraphReflection.boxGraph_revSite_aut i) hm
    (fun w => le_of_eq (crossForm_odd_eq_zero i hn m w)) hc']
  constructor
  · rintro ⟨v, hvsupp, hvc, -⟩
    exact ⟨v, hvsupp, hvc⟩
  · rintro ⟨v, hvsupp, hvc⟩
    exact ⟨v, hvsupp, hvc, crossForm_odd_eq_zero i hn m _⟩

end OddBox

/-! ## 8. Review — the ways this could be hollow

**"Is §3 new, or is it `reflectionPositive_mirror` rearranged?"** New as a
statement and old as a calculation, and the distinction is the point.
`reflectionPositive_mirror` performs every step of §3's proof and then applies
`linarith` to a goal that has thrown two terms away. Recovering them needs no
new idea and no new lemma — it needs the theorem to be STATED with them. That
is the third time this month (`MirrorStrict` was the second, `BoxOddNotStrict`
the first), and the pattern is now specific enough to act on: **when a proof
completes a square or applies an inequality with a named equality case, the
remainder is a theorem, and the file should say what it is before discarding
it.**

**"Does §5 actually answer the open question, or restate it?"** It answers it.
The question the three files above record is whether the exhibited subspace is
the whole null space. §5 says every null direction is `massive *ᵥ v` with `v`
on the half; `BoxOddNotStrict` constructs null directions of exactly that
shape. §7 composes them at the odd box into a biconditional. **What is
answered is the general shape question, not a dimension count**, and the
header says so.

**"Is the coupling hypothesis in §§4–6 hiding the difficulty?"** It is doing
real work and the file does not pretend otherwise. §3 holds with no hypothesis
at all, and it is where the mathematics is. §4 needs the coupling to have a
sign because "a sum of two terms is zero iff both are" is false without one.
Where the coupling is indefinite the identity survives and the
characterisation does not.

**"Why is `dotProduct_slack` stated without `N⁻¹` when the original had it?"**
Because the original did not need it: its proof introduces `z := N⁻¹y`
immediately and then uses only `Nz = y`. Taking the solve as the hypothesis
removes the invertibility side condition from every call site, and §3 calls it
at `z = green · sym c`, where the solve is `massive_mulVec_green` and no
determinant argument appears. **A hypothesis that a proof never uses is a
hypothesis the statement should not have.**

**"Did this file obey the rule it was written under?"** No, on the first
draft, and the failure is worth more than the file. ERRATUM 74 was written
earlier today and says a coverage claim must be produced by listing, for each
element of the range, the declaration that covers it. **The first draft of
this header then asserted that five named files carry the "subspace, not the
null space" sentence.** Three do. `BoxNotStrict`, `TorusNotStrict` and
`ReachCriterion` do not, and the same draft dated the watchlist's version of
the question to "since the wall was started" when all three of its occurrences
were written today. Both were caught by running the grep the rule demands,
before the commit — which is the rule working, but only because it was run,
and it was nearly not. **Knowing the rule this morning was not enough to obey
it this afternoon.** That is the argument for mechanical enforcement rather
than intention, and it is recorded in ERRATUM 74's second addendum rather than
left as a private near-miss.

**"Does §7 depend on the odd box being special?"** Yes, and only in one way:
at odd side the coupling is identically zero, so the isotropic cone is
everything and the second clause of §6 disappears. At even side the same §6
applies and the cone is a proper subset, which is why §7 is stated for odd
side alone and no even-side corollary is claimed.
-/

end NullSpace
