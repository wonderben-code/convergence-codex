/-
  BoxNotStrict.lean — strict reflection positivity is FALSE on the box.

  WHY. `CrossDegenerate` showed the criterion's inequality is attained on the
  box and was careful to say what that did NOT show: *"this does not prove
  that strict reflection positivity is FALSE on the box. It proves the
  criterion's inequality is attained, which blocks THIS route. A different
  argument could still give strictness, and nothing here rules one out."*

  **This rules one out.** The stronger negative is true, and the reason the
  previous file could not assert it is that it had only a null direction for
  the COUPLING, whereas what is needed is a null direction for the reflected
  form itself. The two are related by an invertible change of variable, and
  writing that change down is the whole of this file.

  WHAT THIS FILE PROVES:
  1. **`sub_apply`** — on the half, `(A − B) − (A + B) = −2·crossOp`, which by
     `BoxCrossCoupling.crossOp_eq` is `2` on the innermost layer's diagonal and
     `0` elsewhere. The difference of the two blocks is a diagonal indicator,
     scaled.
  2. **`sub_mulVec_eq_zero`** — hence it ANNIHILATES every vector supported
     away from the innermost layer.
  3. **`reflectedForm_eq_zero_of_off_innermost`** — and therefore, for such a
     `u`, the coefficient family `c = ext H (minusOp *ᵥ u)` has reflected form
     exactly ZERO. **The change of variable is `w = (A − B) u`**: it turns "the
     coupling does not see `u`" into "the reflected form does not see `w`",
     and it is invertible because `A − B` is positive definite.
  4. **`exists_null_direction`, `not_strict`** — **STRICT REFLECTION
     POSITIVITY FAILS ON THE BOX** of even side at least four: there is a
     nonzero coefficient family, supported on the half, whose reflected form
     vanishes. The corner site supplies the `u`.

  WHAT THIS DOES NOT DO.
  * **It does not weaken `GraphReflectionPositive.reflectionPositive_box`.**
    That theorem says the form is `≥ 0` and it is untouched and still sharp.
    What is now known is that `≥` cannot be improved to `>`.
  * **It says nothing about the torus**, whose null direction for the coupling
    `CrossDegenerate` supplies but whose block difference has TWO layers in it;
    the same construction should work and is not written.
  * **No measure-level statement.** `GraphOS2` and `GraphOS2Exponential`
    quantify over reflection positivity as a hypothesis, so nothing there
    changes: a non-strict hypothesis was all they ever used.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import CrossDegenerate

namespace BoxNotStrict

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace BoxGraph
open GraphReflectionPositive CrossDegenerate

variable {d n : ℕ} {m : ℝ}

/-! ## 1. The difference of the two blocks is a diagonal indicator -/

theorem sub_apply (i : Fin d) (hn : Even n) (p q : ↥(lowerHalf i n)) :
    (minusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)
      - plusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)) p q
      = if p = q ∧ 2 * ((p : BoxGraph.Site d n) i).val + 2 = n then 2 else 0 := by
  classical
  simp only [Matrix.sub_apply, minusOp, plusOp, Matrix.of_apply]
  rw [BoxCrossCoupling.crossOp_eq i hn p.2 q.2]
  by_cases h : (p : BoxGraph.Site d n) = (q : BoxGraph.Site d n)
      ∧ 2 * ((p : BoxGraph.Site d n) i).val + 2 = n
  · rw [if_pos h, if_pos ⟨Subtype.ext h.1, h.2⟩]; ring
  · rw [if_neg h, if_neg fun hc => h ⟨congrArg Subtype.val hc.1, hc.2⟩]; ring

/-- **The difference annihilates anything supported away from the innermost
    layer.** -/
theorem sub_mulVec_eq_zero (i : Fin d) (hn : Even n) {u : ↥(lowerHalf i n) → ℝ}
    (hu : ∀ p : ↥(lowerHalf i n), 2 * ((p : BoxGraph.Site d n) i).val + 2 = n → u p = 0) :
    (minusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)
      - plusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)) *ᵥ u
      = 0 := by
  classical
  funext p
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [sub_apply (m := m) i hn p q]
  by_cases h : p = q ∧ 2 * ((p : BoxGraph.Site d n) i).val + 2 = n
  · obtain ⟨rfl, hin⟩ := h
    rw [if_pos ⟨rfl, hin⟩, hu p hin, mul_zero]
  · rw [if_neg h, zero_mul]

/-! ## 2. The change of variable, and the null direction

`CrossDegenerate` had a `u` the coupling cannot see. What is needed is a `w`
the reflected form cannot see, and the two are related by `w = (A − B) u`.
That map is invertible because `A − B` is positive definite, which is why the
witness survives the change.
-/

theorem isRefl_box (i : Fin d) :
    IsRefl (boxGraph d n) (GraphReflection.revSite (n := n) i) where
  invol := GraphReflection.revSite_involutive i
  adj := fun p q => by simpa using GraphReflection.adj_revSite (n := n) i p q

/-- **THE REFLECTED FORM VANISHES** at the image of any `u` supported away
    from the innermost layer. -/
theorem reflectedForm_eq_zero_of_off_innermost (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {u : ↥(lowerHalf i n) → ℝ}
    (hu : ∀ p : ↥(lowerHalf i n), 2 * ((p : BoxGraph.Site d n) i).val + 2 = n → u p = 0) :
    GraphReflection.reflectedForm (boxGraph d n) m (GraphReflection.revSite (n := n) i)
      (ext (lowerHalf i n)
        (minusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n) *ᵥ u))
      = 0 := by
  classical
  have hH := isHalf_lowerHalf (n := n) i hn
  have hR := isRefl_box (n := n) (d := d) i
  set P := plusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n) with hPdef
  set M := minusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n) with hMdef
  have hPd : P.PosDef := plusOp_posDef hH hR hm
  have hMd : M.PosDef := minusOp_posDef hH hR hm
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPd.isUnit
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMd.isUnit
  set w : ↥(lowerHalf i n) → ℝ := M *ᵥ u with hwdef
  have hMinvw : M⁻¹ *ᵥ w = u := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hMu, Matrix.one_mulVec]
  have hkey : (P⁻¹ - M⁻¹) *ᵥ w = 0 := by
    rw [PrismStrict.inv_sub_inv hPu hMu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMinvw, sub_mulVec_eq_zero (m := m) i hn hu, Matrix.mulVec_zero]
  have heq : star w ⬝ᵥ (P⁻¹ *ᵥ w) = star w ⬝ᵥ (M⁻¹ *ᵥ w) := by
    have h0 : star w ⬝ᵥ ((P⁻¹ - M⁻¹) *ᵥ w) = 0 := by rw [hkey, dotProduct_zero]
    rw [Matrix.sub_mulVec, dotProduct_sub] at h0
    linarith
  have hsupp : ∀ p, p ∉ lowerHalf i n → ext (lowerHalf i n) w p = 0 :=
    fun _ hp => ext_notMem w hp
  have hform := GraphReflection.reflectedForm_eq (m := m) hR (ext (lowerHalf i n) w)
  rw [GraphHalfSpace.sym_eq_symExt hH hsupp, GraphHalfSpace.anti_eq_antiExt hH hsupp,
    energy_symExt_eq hH hR hm w, energy_antiExt_eq hH hR hm w] at hform
  linarith

/-- **STRICT REFLECTION POSITIVITY FAILS ON THE BOX.** -/
theorem exists_null_direction (i : Fin d) (hn : Even n) (h4 : 4 ≤ n) (hm : m ≠ 0) :
    ∃ c : BoxGraph.Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → c p = 0) ∧
      GraphReflection.reflectedForm (boxGraph d n) m
        (GraphReflection.revSite (n := n) i) c = 0 := by
  classical
  have hpos : 0 < n := by omega
  have hH := isHalf_lowerHalf (n := n) i hn
  have hR := isRefl_box (n := n) (d := d) i
  set M := minusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n) with hMdef
  have hMd : M.PosDef := minusOp_posDef hH hR hm
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hMd.isUnit
  set u : ↥(lowerHalf i n) → ℝ :=
    fun p => if (p : BoxGraph.Site d n) = corner d n hpos then 1 else 0 with hudef
  have hu : ∀ p : ↥(lowerHalf i n),
      2 * ((p : BoxGraph.Site d n) i).val + 2 = n → u p = 0 := by
    intro p hin
    refine if_neg fun hc => ?_
    exact corner_not_innermost (n := n) i hpos h4 (hc ▸ hin)
  have hcornerMem := corner_mem_lowerHalf (n := n) i hpos
  have hune : u ≠ 0 := by
    intro hc
    have := congrFun hc ⟨corner d n hpos, hcornerMem⟩
    simp [hudef] at this
  have hwne : (M *ᵥ u) ≠ 0 := by
    intro hc
    refine hune ?_
    have : M⁻¹ *ᵥ (M *ᵥ u) = M⁻¹ *ᵥ (0 : ↥(lowerHalf i n) → ℝ) := by rw [hc]
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hMu, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
  refine ⟨ext (lowerHalf i n) (M *ᵥ u), ?_, fun _ hp => ext_notMem _ hp, ?_⟩
  · intro hc
    refine hwne ?_
    funext p
    have := congrFun hc (p : BoxGraph.Site d n)
    rwa [ext_coe] at this
  · exact reflectedForm_eq_zero_of_off_innermost (m := m) i hn hm hu

/-- The same, phrased as the negation. -/
theorem not_strict (i : Fin d) (hn : Even n) (h4 : 4 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph d n) m
              (GraphReflection.revSite (n := n) i) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction (m := m) i hn h4 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-! ## 3. Review round 95 — the ways this could be hollow

**"The previous file said it could not assert this. What changed?"** The
mathematics did not; the construction did. `CrossDegenerate` produced a vector
the COUPLING cannot see, and was right that this is not the same as a vector
the reflected FORM cannot see. **The bridge is one invertible change of
variable, `w = (A − B) u`**, and once written it converts the first into the
second. The earlier file's caution was correct at the time and is now
discharged rather than contradicted — which is the difference between a
caveat and a mistake.

**"Does this weaken the reflection-positivity theorem?"** No.
`GraphReflectionPositive.reflectionPositive_box` says the form is `≥ 0`; that
is untouched, and **what is new is that it is SHARP** — the inequality cannot
be improved. A positivity theorem whose inequality is attained is a better
understood theorem, not a weaker one.

**"Is the change of variable doing real work or is it bookkeeping?"** It is
where the invertibility of `A − B` is spent, and that is not free: `A − B` is
positive definite by `minusOp_posDef`, which is one of the two genuinely
non-bookkeeping results in `GraphReflectionPositive`. **Without it `w` could be
zero and the witness would evaporate**, which is precisely the failure mode
`hwne` rules out.

**"Why does the corner work?"** Because it lies in the half and off the
innermost layer, both proved in `CrossDegenerate` and both needing `4 ≤ n`.
**At `n = 2` the statement of this file is false** — the half is a single
layer, every site is innermost, `A − B` is `2·1`, and the form is strictly
positive exactly as on the prism. The hypothesis is the boundary between the
two regimes and not a convenience.

**"What does this do to the measure-level results?"** Nothing, and that is
worth checking rather than assuming. `GraphOS2` and `GraphOS2Exponential`
take reflection positivity as a HYPOTHESIS and use only `0 ≤`. **They never
consumed strictness, so they neither gain nor lose.** The only thing that
changes is what a reader may hope to strengthen them to.
-/

end BoxNotStrict
