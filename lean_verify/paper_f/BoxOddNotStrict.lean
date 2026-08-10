/-
  BoxOddNotStrict.lean — sharpness at odd side, and a blocker that was not
  one.

  WHY, AND THE THIRD INSTANCE OF ONE MISTAKE. The watchlist item written for
  this question said it was blocked, and named the blocker: the estate's
  null-direction machinery is indexed by the half through `plusOp`/`minusOp`,
  a mirror layer breaks that indexing, and — the operative clause —
  *"strictness cannot avoid the blocks the same way positivity did: it needs
  the attaining vector, not just the sign."*

  **That clause is false.** The positivity proof in `GraphMirrorReflection`
  is a completing-the-square argument, and a completing-the-square argument
  does not merely give a sign: **its equality case hands over the attaining
  vector.** `quadDiff` already says, as an exact identity, that the two
  quadratic forms differ by four times the cross-coupling. Where the
  cross-coupling vanishes they are EQUAL, and equal is exactly what a null
  direction is. Nothing had to be built. This is the third time today a route
  was refused on an unchecked claim about machinery the estate already owns
  (ERRATUM 71, addendum 2), and the recurrence is the finding.

  **THE CONSTRUCTION, in one line.** Take any `v` supported strictly below
  the midline and push it through the massive operator: `c = massive *ᵥ v`.
  Then the symmetrisation and antisymmetrisation of `c` are the massive
  operator applied to the symmetrisation and antisymmetrisation of `v`, so
  the two energies are the two quadratic forms of `quadDiff`, so their
  difference is four times the cross-coupling, so it is zero.

  **WHY THE RESULT LOOKS DIFFERENT FROM THE EVEN CASE.** `BoxNotStrict`
  produces ONE null direction, from a vertex the cut cannot see. This
  produces a whole subspace, one null direction per coefficient family below
  the midline, and every one of them charges the mirror layer — because
  `massive *ᵥ v` reaches one step further than `v` does, and one step above
  the top of the strict half is the midline. **That matches the measurement
  recorded on the watchlist** (at odd side three the form is nondegenerate on
  the strict half alone, so a null direction MUST charge the mirror), which
  is the check that this construction is producing the right objects rather
  than an artefact.

  WHAT THIS FILE PROVES:
  1. **`mulVec_comp_refl`** and **`anti_mulVec`** / **`sym_mulVec`** — the
     massive operator commutes with the reflection, so it carries symmetric
     to symmetric and antisymmetric to antisymmetric. Three lines from
     `IsRefl.massive`, stated because the rest of the file is bookkeeping on
     top of them.
  2. **`energy_mulVec`** — `energy (massive *ᵥ w) = ⟪w, massive *ᵥ w⟫`. The
     Green function is the inverse, so pushing a vector through the operator
     and then measuring it with the inverse gives the operator's own form.
  3. **`reflectedForm_massive_eq_crossForm`** — for `v` supported on the half,
     `reflectedForm (massive *ᵥ v) = crossForm (anti v)`. **An exact identity
     over an arbitrary graph and an arbitrary mirror half**, and the whole
     content of the file; everything else instantiates it.
  4. **`exists_null_direction_box_odd`** — hence on the box of ODD side a
     nonzero coefficient family supported on `lowerHalf` whose reflected form
     is exactly zero, for every side at least three and every dimension at
     least one.
  5. **`not_strict_box_odd`** — so reflection positivity on the odd box is
     **not** strict. Together with `BoxNotStrict` (even side, four and up)
     the box is now known non-strict at **every side length of three or
     more**: odd sides from three here, even sides from four there. Sides one
     and two are not covered by either, and no claim is made about them.

  WHAT THIS DOES NOT DO.
  * **It does not describe the null space.** It exhibits a subspace of it.
    Whether that subspace is all of it is open and is not claimed anywhere.
  * **Sides one and two are untouched**, and it is not an oversight: at both,
    the strict half is empty, so this construction produces nothing, and
    `BoxNotStrict` needs four. Whether either is strict is unknown here, and
    the honest phrasing is "not covered" rather than "the last case", since
    both fall BELOW the threshold rather than between the two results.
    **AMENDED 2026-08-10, SAME DAY: both are settled and they go the other
    way.** `StrictCriterion` proves the box STRICT at side two — every site of
    the half sits on the cut, so it touches its own mirror — and at side one,
    where the reflection is the identity and the reflected form is the energy.
    "Unknown here" was right about this file and is no longer right about the
    estate.
  * **Nothing for the torus or the estate's own `def` at odd side.** The
    identity in §3 is general and both should follow; neither is attempted,
    and this sentence is a statement about what was done, not a prediction
    about what will happen.
    **AMENDED 2026-08-10, SAME DAY: both are done.** `OddNotStrictInstances`
    instantiates §3 at the estate's own `def` (odd side three and up) and at
    the torus (odd side FIVE and up — at three the wrap-around leaves the
    construction nothing to act on, and the form is strict there anyway, by
    `MirrorStrict`). "Both should follow" held for the `def` and needed a
    side-length correction for the torus, which is why it was written as a
    statement about what was done.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import TorusAnySide

namespace BoxOddNotStrict

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection BoxOddReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The massive operator commutes with the reflection -/

theorem mulVec_comp_refl (h : IsRefl G θ) (m : ℝ) (v : V → ℝ) (p : V) :
    (GraphLaplacian.massive G m *ᵥ v) (θ p)
      = (GraphLaplacian.massive G m *ᵥ (fun q => v (θ q))) p := by
  classical
  have hM : ∀ x y, GraphLaplacian.massive G m (θ x) (θ y) = GraphLaplacian.massive G m x y :=
    fun x y => congrFun (congrFun (h.massive m) x) y
  simp only [Matrix.mulVec, dotProduct]
  rw [← Fintype.sum_equiv θ
    (fun q => GraphLaplacian.massive G m (θ p) (θ q) * v (θ q))
    (fun q => GraphLaplacian.massive G m (θ p) q * v q) (fun _ => rfl)]
  exact Finset.sum_congr rfl fun q _ => by rw [hM p q]

theorem anti_mulVec (h : IsRefl G θ) (m : ℝ) (v : V → ℝ) :
    GraphReflection.anti θ (GraphLaplacian.massive G m *ᵥ v)
      = GraphLaplacian.massive G m *ᵥ GraphReflection.anti θ v := by
  funext p
  simp only [GraphReflection.anti]
  rw [mulVec_comp_refl h m v p]
  simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by simp only [GraphReflection.anti]; ring

theorem sym_mulVec (h : IsRefl G θ) (m : ℝ) (v : V → ℝ) :
    GraphReflection.sym θ (GraphLaplacian.massive G m *ᵥ v)
      = GraphLaplacian.massive G m *ᵥ GraphReflection.sym θ v := by
  funext p
  simp only [GraphReflection.sym]
  rw [mulVec_comp_refl h m v p]
  simp only [Matrix.mulVec, dotProduct, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by simp only [GraphReflection.sym]; ring

/-! ## 2. Pushing through the operator turns the Green form into the operator form -/

theorem energy_mulVec (hm : m ≠ 0) (w : V → ℝ) :
    GraphReflection.energy G m (GraphLaplacian.massive G m *ᵥ w)
      = w ⬝ᵥ (GraphLaplacian.massive G m *ᵥ w) := by
  classical
  rw [GraphMirrorReflection.energy_eq_dotProduct]
  have hinv : GraphLaplacian.green G m *ᵥ (GraphLaplacian.massive G m *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, GraphLaplacian.green_mul_massive G hm, Matrix.one_mulVec]
  rw [hinv, dotProduct_comm]

/-! ## 3. The identity

An exact statement over an arbitrary graph and an arbitrary mirror half. The
even case is `Mir = ∅`, where the cross-coupling is generally nonzero and the
identity says the reflected form of a pushed-through vector is exactly that
coupling — which is worth knowing too, and is why this is stated as an
equality rather than as the corollary it is used for.
-/

/-- **THE PUSHED-THROUGH VECTOR'S REFLECTED FORM IS THE CROSS-COUPLING.** -/
theorem reflectedForm_massive_eq_crossForm (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) {v : V → ℝ} (hv : ∀ p, p ∉ H → v p = 0) :
    GraphReflection.reflectedForm G m θ (GraphLaplacian.massive G m *ᵥ v)
      = GraphMirrorReflection.crossForm G m θ H (GraphReflection.anti θ v) := by
  classical
  set ξ := GraphReflection.anti θ v with hξdef
  have hξodd : GraphMirrorReflection.IsOddFun θ ξ := by
    intro p
    simp only [hξdef, GraphReflection.anti, h.invol p]
    ring
  -- the sign flip of the antisymmetrisation is the symmetrisation, on the half
  have hev : GraphMirrorReflection.evenify H ξ = GraphReflection.sym θ v := by
    funext p
    by_cases hp : p ∈ H
    · have hθp : v (θ p) = 0 := hv _ (hM.notMem_of_mem hp)
      simp [GraphMirrorReflection.evenify_of_mem hp, hξdef, GraphReflection.anti,
        GraphReflection.sym, hθp]
    · have hvp : v p = 0 := hv p hp
      simp [GraphMirrorReflection.evenify_of_notMem hp, hξdef, GraphReflection.anti,
        GraphReflection.sym, hvp]
  have h4 := GraphReflection.reflectedForm_eq (G := G) (m := m) h
    (GraphLaplacian.massive G m *ᵥ v)
  rw [sym_mulVec h m v, anti_mulVec h m v, energy_mulVec hm, energy_mulVec hm,
    ← hξdef, ← hev] at h4
  have hq := GraphMirrorReflection.quadDiff (G := G) (m := m) hM hξodd
  linarith

/-! ## 4. The odd box -/

/-- On an ODD side, a step from strictly below the midline lands no higher
    than the midline. This is where the parity is spent, and it is the reason
    the null direction charges the mirror rather than escaping past it. -/
theorem massive_mulVec_supported {d n : ℕ} (i : Fin d) (hn : Odd n) (m : ℝ)
    {v : BoxGraph.Site d n → ℝ} (hv : ∀ p, p ∉ strictLower i n → v p = 0) :
    ∀ p, p ∉ lowerHalf i n → (GraphLaplacian.massive (boxGraph d n) m *ᵥ v) p = 0 := by
  classical
  intro p hp
  have hpn : ¬ (2 * (p i).val < n) := by
    simpa [lowerHalf, Finset.mem_filter] using hp
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hq : q ∈ strictLower i n
  · rw [mem_strictLower] at hq
    obtain ⟨k, hk⟩ := hn
    have hqlt := (q i).isLt
    -- `p` is at or above the midline, `q` strictly below: not equal, not adjacent
    have hne : p ≠ q := fun hc => by rw [hc] at hpn; omega
    have hadj : ¬ (boxGraph d n).Adj p q := by
      rintro ⟨j, hsame, hstep⟩
      by_cases hj : j = i
      · subst hj; omega
      · exact hne (funext fun l => by
          by_cases hl : l = j
          · subst hl
            exact absurd (congrArg Fin.val (hsame i (fun hc => hj hc.symm)))
              (by omega)
          · exact hsame l hl)
    rw [GraphLaplacian.massive_apply, if_neg hne, if_neg hadj]
    ring
  · rw [hv q hq, mul_zero]

/-- **THE ODD BOX IS NOT SHARP.** A nonzero coefficient family supported on
    `lowerHalf` whose reflected form is exactly zero, at every odd side at
    least three and every dimension at least one. -/
theorem exists_null_direction_box_odd {d n : ℕ} (i : Fin d) (hn : Odd n) (h3 : 3 ≤ n)
    {m : ℝ} (hm : m ≠ 0) :
    ∃ c : BoxGraph.Site d n → ℝ, c ≠ 0 ∧
      (∀ p, p ∉ lowerHalf i n → c p = 0) ∧
      GraphReflection.reflectedForm (boxGraph d n) m
        (GraphReflection.revSite (n := n) i) c = 0 := by
  classical
  obtain ⟨k, hk⟩ := hn
  -- a site on the bottom layer in direction `i`; it is strictly below the midline
  set p₀ : BoxGraph.Site d n := fun j => if j = i then ⟨0, by omega⟩ else ⟨0, by omega⟩ with hp₀
  set v : BoxGraph.Site d n → ℝ := fun p => if p = p₀ then 1 else 0 with hv
  have hvsupp : ∀ p, p ∉ strictLower i n → v p = 0 := by
    intro p hp
    have : p ≠ p₀ := by
      rintro rfl
      exact hp (mem_strictLower.mpr (by simp [hp₀]; omega))
    simp [hv, this]
  refine ⟨GraphLaplacian.massive (boxGraph d n) m *ᵥ v, ?_,
    massive_mulVec_supported i ⟨k, hk⟩ m hvsupp, ?_⟩
  · -- the massive operator is injective, and `v` is nonzero
    intro hc
    have hvne : v ≠ 0 := fun h0 => by
      have := congrFun h0 p₀
      simp [hv] at this
    exact hvne (by
      have hpd := GraphLaplacian.massive_posDef (boxGraph d n) hm
      have hunit : IsUnit (GraphLaplacian.massive (boxGraph d n) m).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
      have := congrArg (fun w => GraphLaplacian.green (boxGraph d n) m *ᵥ w) hc
      simpa [GraphLaplacian.green, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ hunit] using this)
  · rw [reflectedForm_massive_eq_crossForm (isMirrorHalf_strictLower i n)
      (GraphReflection.boxGraph_revSite_aut i) hm hvsupp]
    exact crossForm_odd_eq_zero i ⟨k, hk⟩ m _

/-- **SO REFLECTION POSITIVITY ON THE ODD BOX CANNOT BE STRENGTHENED.** -/
theorem not_strict_box_odd {d n : ℕ} (i : Fin d) (hn : Odd n) (h3 : 3 ≤ n)
    {m : ℝ} (hm : m ≠ 0) :
    ¬ (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph d n) m
              (GraphReflection.revSite (n := n) i) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction_box_odd i hn h3 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-! ## 5. Review — the ways this could be hollow

**"Is the witness real, or is it zero in disguise?"** Real, and the proof
that it is nonzero is the only place positive definiteness is used for
anything other than inverting: the massive operator is injective, so pushing
a nonzero `v` through it gives a nonzero `c`. The `v` chosen is a single
indicator at the corner of the bottom layer, which is in the strict half
whenever the side is at least three — that is where `3 ≤ n` is spent, and it
is spent nowhere else.

**"Does the null direction really charge the mirror, or is that decoration?"**
It does, and it is checkable against something independent: the watchlist
records a measurement, made before this file existed, that at odd side three
the reflected form is NONDEGENERATE on the strict half alone. A construction
producing null directions inside the strict half would therefore contradict
the measurement. This one produces `massive *ᵥ v`, which reaches exactly one
step beyond the support of `v`, and one step above the strict half is the
midline. **Construction and measurement agree, and neither was derived from
the other.**

**"Is §3 doing real work or restating `quadDiff`?"** Restating it, and the
restatement is the point. `quadDiff` is about a sign-flipped test vector, an
object that appears inside the positivity proof and nowhere else. §3 says the
same identity is a statement about the REFLECTED FORM of an explicit
coefficient family, which is the object the theorem is about. **The whole
difficulty was seeing that the equality case of a positivity proof is a
sharpness theorem**, and once seen the file is bookkeeping.

**"What is the state of sharpness on the box now?"** Non-strict at every even
side from four (`BoxNotStrict`) and every odd side from three (here) — so at
**every side of three or more**, with no gap between them. **Sides one and
two are not covered by either result**: at both, the strict half is empty, so
this construction yields nothing, and the even-side argument needs four.
Whether they are strict is left open and unguessed — this file's own
predecessor got burned predicting exactly this sort of thing (ERRATUM 72), so
the sentence stops at "not covered".

**"Does this generalise to the torus and to the estate's own `def`?"** §3 is
stated for an arbitrary graph and an arbitrary mirror half, so nothing in it
is box-specific; what is box-specific is §4's support lemma, which spends the
parity. Neither instance is attempted here, and no claim is made about how
they would go.
-/

end BoxOddNotStrict
