/-
  TorusNotStrict.lean — the strictness picture, closed.

  WHY. Three graphs, three answers, and until now only two of them were known:
  strictness HOLDS on the two-layer stack (`PrismStrict`), FAILS on the box
  (`BoxNotStrict`), and was open on the periodic box. `UNLOCK_WATCHLIST.md`
  seeded the gap with the route and named the single real difference: on the
  box the difference of the two blocks is supported on ONE layer, on the torus
  on TWO — the innermost and the seam. **This closes it, and the closed
  statement is clean: strictness holds exactly when every vertex touches the
  mirror.**

  WHAT THIS FILE PROVES:
  1. **`reflectedForm_eq_zero_of_annihilated` and
     `exists_null_direction_of_annihilated`** — the argument of `BoxNotStrict`
     with the box removed. **Given ANY graph, reflection and half, if the
     difference of the two blocks annihilates a nonzero `u`, then the
     reflected form has a null direction.** The change of variable
     `w = (A − B) u` and the invertibility of `A − B` are the whole content,
     and neither mentions a lattice.
  2. **`box_instance`** — `BoxNotStrict.reflectedForm_eq_zero_of_off_innermost`
     recovered from §1. **The check that §1 is the right generalisation**, and
     the reason this file is not duplication: the box proof is now an
     instance rather than a sibling.
  3. **`sub_apply_torus`, `sub_mulVec_eq_zero_torus`** — the torus's block
     difference, which is `2` on the diagonal of BOTH mirror layers. This is
     the one place the two lattices genuinely differ.
  4. **`exists_null_direction_torus`, `not_strict_torus`** — **STRICT
     REFLECTION POSITIVITY FAILS ON THE PERIODIC BOX** of even side at least
     six, with `CrossDegenerate.stepIn` as the witness.

  WHAT THIS DOES NOT DO.
  * **It does not weaken any positivity theorem.**
    `TorusReflection.reflectionPositive_torus` says the form is `≥ 0`; that
    stands, and what is now known is that the bound is SHARP on both lattices
    and not sharp on the stack.
  * **The clean statement is a summary, not a theorem.** "Strictness holds
    exactly when every vertex touches the mirror" is what the three results
    add up to; **there is no Lean theorem quantifying over graphs that says
    it**, and writing one would need a hypothesis capturing "every vertex
    touches the mirror" that nothing else in the estate uses.
  * **Nothing measure-level changes.** `GraphOS2` and `GraphOS2Exponential`
    consume `0 ≤` only — checked when `BoxNotStrict` landed and unchanged.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import BoxNotStrict

namespace TorusNotStrict

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace BoxGraph
open GraphReflectionPositive CrossDegenerate TorusReflection

/-! ## 1. The argument, with the box removed -/

section General

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H : Finset V}

/-- **The reflected form vanishes at the image of anything the block
    difference annihilates.** No graph, no coordinates: the change of variable
    `w = (A − B) u` and the invertibility of `A − B` are the whole content. -/
theorem reflectedForm_eq_zero_of_annihilated (hH : IsHalf θ H) (hR : IsRefl G θ) (hm : m ≠ 0)
    {u : ↥H → ℝ} (hu : (minusOp G m θ H - plusOp G m θ H) *ᵥ u = 0) :
    GraphReflection.reflectedForm G m θ (ext H (minusOp G m θ H *ᵥ u)) = 0 := by
  classical
  have hPd : (plusOp G m θ H).PosDef := plusOp_posDef hH hR hm
  have hMd : (minusOp G m θ H).PosDef := minusOp_posDef hH hR hm
  have hPu : IsUnit (plusOp G m θ H).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPd.isUnit
  have hMu : IsUnit (minusOp G m θ H).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hMd.isUnit
  set w : ↥H → ℝ := minusOp G m θ H *ᵥ u with hwdef
  have hMinvw : (minusOp G m θ H)⁻¹ *ᵥ w = u := by
    rw [hwdef, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, Matrix.one_mulVec]
  have hkey : ((plusOp G m θ H)⁻¹ - (minusOp G m θ H)⁻¹) *ᵥ w = 0 := by
    rw [PrismStrict.inv_sub_inv hPu hMu, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hMinvw, hu, Matrix.mulVec_zero]
  have heq : star w ⬝ᵥ ((plusOp G m θ H)⁻¹ *ᵥ w)
      = star w ⬝ᵥ ((minusOp G m θ H)⁻¹ *ᵥ w) := by
    have h0 : star w ⬝ᵥ (((plusOp G m θ H)⁻¹ - (minusOp G m θ H)⁻¹) *ᵥ w) = 0 := by
      rw [hkey, dotProduct_zero]
    rw [Matrix.sub_mulVec, dotProduct_sub] at h0
    linarith
  have hsupp : ∀ p, p ∉ H → ext H w p = 0 := fun _ hp => ext_notMem w hp
  have hform := GraphReflection.reflectedForm_eq (m := m) hR (ext H w)
  rw [GraphHalfSpace.sym_eq_symExt hH hsupp, GraphHalfSpace.anti_eq_antiExt hH hsupp,
    energy_symExt_eq hH hR hm w, energy_antiExt_eq hH hR hm w] at hform
  linarith

/-- And the witness survives, because `A − B` is invertible. -/
theorem exists_null_direction_of_annihilated (hH : IsHalf θ H) (hR : IsRefl G θ) (hm : m ≠ 0)
    {u : ↥H → ℝ} (hune : u ≠ 0) (hu : (minusOp G m θ H - plusOp G m θ H) *ᵥ u = 0) :
    ∃ c : V → ℝ, c ≠ 0 ∧ (∀ p, p ∉ H → c p = 0) ∧
      GraphReflection.reflectedForm G m θ c = 0 := by
  classical
  have hMd : (minusOp G m θ H).PosDef := minusOp_posDef hH hR hm
  have hMu : IsUnit (minusOp G m θ H).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hMd.isUnit
  have hwne : (minusOp G m θ H *ᵥ u) ≠ 0 := by
    intro hc
    refine hune ?_
    have h1 : (minusOp G m θ H)⁻¹ *ᵥ (minusOp G m θ H *ᵥ u)
        = (minusOp G m θ H)⁻¹ *ᵥ (0 : ↥H → ℝ) := by rw [hc]
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hMu, Matrix.one_mulVec,
      Matrix.mulVec_zero] at h1
  refine ⟨ext H (minusOp G m θ H *ᵥ u), ?_, fun _ hp => ext_notMem _ hp, ?_⟩
  · intro hc
    refine hwne ?_
    funext p
    have := congrFun hc (p : V)
    rwa [ext_coe] at this
  · exact reflectedForm_eq_zero_of_annihilated hH hR hm hu

end General

/-! ## 2. The box is an instance

`BoxNotStrict` proved its version directly. Recovering it from §1 is the check
that §1 is the right generalisation — without it this file would be a sibling
of that one rather than a roof over it.
-/

section BoxCheck

variable {d n : ℕ} {m : ℝ}

theorem box_instance (i : Fin d) (hn : Even n) (hm : m ≠ 0)
    {u : ↥(lowerHalf i n) → ℝ}
    (hu : ∀ p : ↥(lowerHalf i n), 2 * ((p : BoxGraph.Site d n) i).val + 2 = n → u p = 0) :
    GraphReflection.reflectedForm (boxGraph d n) m (GraphReflection.revSite (n := n) i)
      (ext (lowerHalf i n)
        (minusOp (boxGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n) *ᵥ u))
      = 0 :=
  reflectedForm_eq_zero_of_annihilated (isHalf_lowerHalf i hn) (BoxNotStrict.isRefl_box i) hm
    (BoxNotStrict.sub_mulVec_eq_zero (m := m) i hn hu)

end BoxCheck

/-! ## 3. The torus, where the difference is supported on two layers -/

section Torus

variable {d n : ℕ} {m : ℝ}

/-- **The torus's block difference.** `2` on the diagonal of BOTH mirror
    layers — the innermost and the seam — which is the one place the two
    lattices genuinely differ. -/
theorem sub_apply_torus (i : Fin d) (hn : Even n) (p q : ↥(lowerHalf i n)) :
    (minusOp (torusGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)
      - plusOp (torusGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)) p q
      = if p = q ∧ (2 * ((p : BoxGraph.Site d n) i).val + 2 = n
          ∨ ((p : BoxGraph.Site d n) i).val = 0) then 2 else 0 := by
  classical
  simp only [Matrix.sub_apply, minusOp, plusOp, Matrix.of_apply]
  rw [TorusReflection.crossOp_eq_neg_adj (isHalf_lowerHalf i hn) p.2 q.2]
  by_cases h : (p : BoxGraph.Site d n) = (q : BoxGraph.Site d n)
      ∧ (2 * ((p : BoxGraph.Site d n) i).val + 2 = n ∨ ((p : BoxGraph.Site d n) i).val = 0)
  · rw [if_pos ((adj_torus_revSite_iff i hn p.2 q.2).mpr h), if_pos ⟨Subtype.ext h.1, h.2⟩]
    ring
  · rw [if_neg fun hc => h ((adj_torus_revSite_iff i hn p.2 q.2).mp hc),
      if_neg fun hc => h ⟨congrArg Subtype.val hc.1, hc.2⟩]
    ring

theorem sub_mulVec_eq_zero_torus (i : Fin d) (hn : Even n) {u : ↥(lowerHalf i n) → ℝ}
    (hu : ∀ p : ↥(lowerHalf i n),
      (2 * ((p : BoxGraph.Site d n) i).val + 2 = n ∨ ((p : BoxGraph.Site d n) i).val = 0) →
        u p = 0) :
    (minusOp (torusGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)
      - plusOp (torusGraph d n) m (GraphReflection.revSite (n := n) i) (lowerHalf i n)) *ᵥ u
      = 0 := by
  classical
  funext p
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [sub_apply_torus (m := m) i hn p q]
  by_cases h : p = q ∧ (2 * ((p : BoxGraph.Site d n) i).val + 2 = n
      ∨ ((p : BoxGraph.Site d n) i).val = 0)
  · obtain ⟨rfl, hin⟩ := h
    rw [if_pos ⟨rfl, hin⟩, hu p hin, mul_zero]
  · rw [if_neg h, zero_mul]

/-- **STRICT REFLECTION POSITIVITY FAILS ON THE PERIODIC BOX** of even side at
    least six. The witness is `CrossDegenerate.stepIn`, already proved to lie
    off both mirror layers. -/
theorem exists_null_direction_torus (i : Fin d) (hn : Even n) (h6 : 6 ≤ n) (hm : m ≠ 0) :
    ∃ c : BoxGraph.Site d n → ℝ, c ≠ 0 ∧ (∀ p, p ∉ lowerHalf i n → c p = 0) ∧
      GraphReflection.reflectedForm (torusGraph d n) m
        (GraphReflection.revSite (n := n) i) c = 0 := by
  classical
  have h1 : 1 < n := by omega
  have hmem := stepIn_mem_lowerHalf (n := n) i h1 h6
  set u : ↥(lowerHalf i n) → ℝ :=
    fun p => if (p : BoxGraph.Site d n) = stepIn d n h1 then 1 else 0 with hudef
  have hu : ∀ p : ↥(lowerHalf i n),
      (2 * ((p : BoxGraph.Site d n) i).val + 2 = n ∨ ((p : BoxGraph.Site d n) i).val = 0) →
        u p = 0 := by
    intro p hin
    refine if_neg fun hc => ?_
    exact stepIn_off_both (n := n) i h1 h6 (hc ▸ hin)
  have hune : u ≠ 0 := by
    intro hc
    have := congrFun hc ⟨stepIn d n h1, hmem⟩
    simp [hudef] at this
  exact exists_null_direction_of_annihilated (isHalf_lowerHalf i hn) (isRefl_torus i) hm
    hune (sub_mulVec_eq_zero_torus (m := m) i hn hu)

/-- The same, phrased as the negation. -/
theorem not_strict_torus (i : Fin d) (hn : Even n) (h6 : 6 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (torusGraph d n) m
              (GraphReflection.revSite (n := n) i) c) := by
  intro hstrict
  obtain ⟨c, hc0, hcsupp, hcform⟩ := exists_null_direction_torus (m := m) i hn h6 hm
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

end Torus

/-! ## 4. Review round 96 — the ways this could be hollow

**"Is §1 a real generalisation or a rename?"** It is real and §2 is the
evidence: `BoxNotStrict`'s theorem is recovered from it in three lines, so the
box proof is now an INSTANCE rather than a sibling. **The test that matters
is that §1 mentions no graph, no coordinates and no layer** — the hypothesis
is "the block difference annihilates `u`" and everything else is the change of
variable and the invertibility of `A − B`. Had the box's geometry leaked into
it, §2 would not have typechecked.

**"Then is §3 just the box again with a disjunction?"** The proof shape is the
same and the CONTENT of the difference is not, which is the whole reason the
torus was open. `TorusReflection.adj_torus_revSite_iff` has two disjuncts
where the box's has one, so the block difference is supported on two layers
and the witness must avoid both. **The box's corner does not avoid both — it
sits on the seam** — which is exactly why `CrossDegenerate` had to prove a
second witness, and why the side bound moves from four to six.

**"Does this weaken `reflectionPositive_torus`?"** No. That says the form is
`≥ 0`, untouched. What is now known is that the bound is SHARP on both
lattices and NOT sharp on the stack, and a positivity theorem whose sharpness
is settled either way is better understood than one where it is not.

**"The clean statement — is it a theorem?"** No, and the header says so. *"
Strictness holds exactly when every vertex touches the mirror"* is what the
three results add up to when a reader lines them up; **there is no Lean
theorem quantifying over graphs that says it.** Writing one would need a
hypothesis expressing "every vertex touches the mirror", which nothing else in
the estate uses and which would exist only to make this sentence formal.
**Recording the summary as a summary is the honest option**, and the
alternative — a bespoke predicate with one use — is how definitions rot.
-/

end TorusNotStrict
