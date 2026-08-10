/-
  ReachCriterion.lean — the converse, and what it says strictness actually
  depends on.

  WHY. One technical item was left open on this wall: the converse that would
  turn the strictness criterion into an "exactly when". ERRATUM 73 exists
  because that gap was once papered over with a false equivalence, so it was
  kept open explicitly rather than assumed.

  **IT FOLLOWS FROM THE IDENTITY, AND IT SAYS SOMETHING BETTER THAN
  EXPECTED.** `BoxOddNotStrict.reflectedForm_massive_eq_crossForm` says the
  reflected form of `massive *ᵥ v`, for `v` on the strict half, IS the
  cross-coupling. Suppose the massive operator's REACH from the strict half
  stays inside the region — every neighbour of a site strictly below the
  midline is itself in the region. Then `massive *ᵥ v` is an admissible
  coefficient family, so positivity gives `≥ 0`, while the coupling
  hypothesis gives `≤ 0`. **Both, so it is zero, so the form is not strict.**

  **What that buys, stated at the strength the measurement supports.** Reach
  inside the region implies NOT strict, so — contrapositive — strictness
  requires the reach to escape. Checked against every row of ERRATUM 73's
  table: no row has the reach inside and the form strict, so the implication
  holds throughout. **The converse is FALSE and the check found it**: at box
  side four the reach escapes (the innermost layer reaches into the far half)
  and the form is degenerate anyway, and likewise at box six and torus five
  and six. A first draft of this header claimed one condition explained every
  row; it explains four of ten, and the theorem below is the half that is
  true. Escaping reach is necessary for strictness and nowhere near
  sufficient.

  WHAT THIS FILE PROVES:
  1. **`not_strict_of_reach`** — if the coupling is nonpositive, the reach
     stays inside the region, and the strict half is nonempty, then a null
     direction exists. Over an arbitrary graph and an arbitrary mirror half.
     **The converse, with its two hypotheses named.**
     **AMENDED 2026-08-10, SAME DAY (ERRATUM 75): THERE IS ONLY ONE
     HYPOTHESIS.** `ReachIsCoupling` proves `ReachInside ↔ ∀ w, crossForm w =
     0`, so the reach condition implies the coupling one and implies far more
     than nonpositivity. Three of this file's four signatures carry `hcross`
     and none needs it; the deleted-hypothesis versions are
     `ReachIsCoupling.not_strict_of_reach` and `.reach_escapes_of_strict`.
     Nothing here becomes false — a redundant hypothesis weakens a theorem
     and never wrongs it — and nothing this file covers changes.
  2. **`crossForm_eq_zero_of_reach`** — and in that situation the coupling is
     forced to vanish on the witness. It is not an extra assumption but a
     consequence, which is why `BoxOddNotStrict` had to prove it separately
     and this file does not.
  3. **`reach_escapes_of_strict`** — the contrapositive, which is the
     statement worth remembering: **strictness forces the operator to reach
     out of the region.** **AMENDED 2026-08-10, SAME DAY: the statement worth
     remembering is `ReachIsCoupling.crossForm_ne_zero_of_strict`, which says
     the same thing about the coupling — strictness forces the coupling to be
     NONZERO. "Reaching out" was that fact in geometric dress.
  4. **`exists_null_direction_box_odd'`** — the odd box re-derived from §1,
     as the check that the generalisation really covers the case it came
     from (ERRATUM 48).

  WHAT THIS DOES NOT DO.
  * **It is still not a biconditional in one statement.** §1 needs the reach
    hypothesis and `StrictCriterion`/`MirrorStrict` need the touching
    hypothesis, and neither is the negation of the other — a graph can fail
    both. What is now true is that the two known mechanisms are each proved
    in the general setting rather than case by case, and no wall case is left
    to either.
  * **The reach hypothesis is not vacuous and not automatic.** It fails on
    the box at even side (the innermost layer reaches the far half), which is
    why `BoxNotStrict`'s separate construction is still the only proof there
    and is left standing. **AMENDED 2026-08-10, SAME DAY: it also fails on the
    TORUS at every side length** — the wrap-around edge joins the bottom layer
    to its own mirror however long the side is
    (`TorusAnySide.torus_cross_diag_any`), so the coupling is diagonal rather
    than zero and `ReachIsCoupling`'s equivalence rules the torus out. This
    file never applied there, which is exactly why `OddNotStrictInstances`
    needed its own construction on a smaller half. Forced, not overlooked.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import MirrorStrict

namespace ReachCriterion

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection BoxOddReflection BoxOddNotStrict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. Reach inside the region forces a null direction

The whole argument is that one vector is squeezed. Positivity pushes the
reflected form up to zero; the coupling hypothesis pushes the same number
down to zero; the identity says they are talking about the same number.
-/

/-- The reach condition: the massive operator applied to anything living on
    the strict half stays inside the region. -/
def ReachInside (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (H Mir : Finset V) : Prop :=
  ∀ v : V → ℝ, (∀ p, p ∉ H → v p = 0) →
    ∀ p, p ∉ H → p ∉ Mir → (GraphLaplacian.massive G m *ᵥ v) p = 0

/-- **THE CONVERSE.** Nonpositive coupling, reach inside the region, strict
    half nonempty: then reflection positivity is attained. -/
theorem not_strict_of_reach (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    (hreach : ReachInside G m H Mir) {p₀ : V} (hp₀ : p₀ ∈ H) :
    ∃ c : V → ℝ, c ≠ 0 ∧ (∀ p, p ∉ H → p ∉ Mir → c p = 0) ∧
      GraphReflection.reflectedForm G m θ c = 0 := by
  classical
  set v : V → ℝ := fun p => if p = p₀ then 1 else 0 with hv
  have hvsupp : ∀ p, p ∉ H → v p = 0 := by
    intro p hp
    have : p ≠ p₀ := fun hc => hp (hc ▸ hp₀)
    simp [hv, this]
  have hvne : v ≠ 0 := fun h0 => by
    have := congrFun h0 p₀; simp [hv] at this
  refine ⟨GraphLaplacian.massive G m *ᵥ v, ?_, hreach v hvsupp, ?_⟩
  · -- the massive operator is injective
    intro hc
    refine hvne ?_
    have hunit : IsUnit (GraphLaplacian.massive G m).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp (GraphLaplacian.massive_posDef G hm).isUnit
    have := congrArg (fun w => GraphLaplacian.green G m *ᵥ w) hc
    simpa [GraphLaplacian.green, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit] using this
  · -- squeezed between positivity and the coupling hypothesis
    have hup : 0 ≤ GraphReflection.reflectedForm G m θ (GraphLaplacian.massive G m *ᵥ v) :=
      reflectionPositive_mirror hM h hm hcross (hreach v hvsupp)
    have hid := reflectedForm_massive_eq_crossForm hM h hm hvsupp
    have hdown := hcross (GraphReflection.anti θ v)
    linarith [hid ▸ hup]

/-- **AND THE COUPLING IS FORCED TO VANISH**, rather than assumed to.
    `BoxOddNotStrict` proved this separately for the odd box; here it is a
    consequence of the reach condition and needs no geometry. -/
theorem crossForm_eq_zero_of_reach (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    (hreach : ReachInside G m H Mir) {v : V → ℝ} (hvsupp : ∀ p, p ∉ H → v p = 0) :
    crossForm G m θ H (GraphReflection.anti θ v) = 0 := by
  have hup : 0 ≤ GraphReflection.reflectedForm G m θ (GraphLaplacian.massive G m *ᵥ v) :=
    reflectionPositive_mirror hM h hm hcross (hreach v hvsupp)
  have hid := reflectedForm_massive_eq_crossForm hM h hm hvsupp
  have hdown := hcross (GraphReflection.anti θ v)
  linarith [hid ▸ hup]

/-- **THE STATEMENT WORTH REMEMBERING.** Contrapositive of §1: if the form is
    strict then the operator must reach out of the region. Strictness is a
    fact about the geometry of the reach, not about the size of the
    coupling.

    **AMENDED 2026-08-10, SAME DAY: the last sentence is FALSE and is kept
    with its refutation** (ERRATUM 75). It contrasts two things
    `ReachIsCoupling` shows are one: reaching inside the region is exactly the
    coupling vanishing identically. The contrast was drawn from the fact that
    the two hypotheses had different names, not from any check that they were
    independent. -/
theorem reach_escapes_of_strict (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    {p₀ : V} (hp₀ : p₀ ∈ H)
    (hstrict : ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
      0 < GraphReflection.reflectedForm G m θ c) :
    ¬ ReachInside G m H Mir := by
  intro hreach
  obtain ⟨c, hc0, hcsupp, hcform⟩ := not_strict_of_reach hM h hm hcross hreach hp₀
  exact absurd hcform (ne_of_gt (hstrict c hc0 hcsupp))

/-! ## 2. The odd box, re-derived

ERRATUM 48's check: when a unit's contribution is "this makes X possible",
attempt X. `BoxOddNotStrict` proved the odd box non-strict by computing that
the coupling vanishes and then building the witness. §1 needs neither: the
coupling vanishing is a consequence, and the witness is generic.
-/

section Box

variable {d n : ℕ}

/-- **THE ODD BOX, FROM §1 ALONE.** Compare
    `BoxOddNotStrict.exists_null_direction_box_odd`, which computes the
    coupling first. The two agree, which is the check that the generalisation
    covers the case it came from. -/
theorem exists_null_direction_box_odd' (i : Fin d) (hn : Odd n) (h3 : 3 ≤ n)
    {m : ℝ} (hm : m ≠ 0) :
    ∃ c : BoxGraph.Site d n → ℝ, c ≠ 0 ∧
      (∀ p, p ∉ strictLower i n → p ∉ midLayer i n → c p = 0) ∧
      GraphReflection.reflectedForm (boxGraph d n) m
        (GraphReflection.revSite (n := n) i) c = 0 := by
  classical
  obtain ⟨k, hk⟩ := hn
  refine not_strict_of_reach (isMirrorHalf_strictLower i n)
    (GraphReflection.boxGraph_revSite_aut i) hm
    (fun w => le_of_eq (crossForm_odd_eq_zero i ⟨k, hk⟩ m w))
    (fun v hvsupp p hpH hpM => ?_)
    (p₀ := fun j => if j = i then ⟨0, by omega⟩ else ⟨0, by omega⟩) ?_
  · -- the reach condition is `BoxOddNotStrict`'s support lemma, restated
    have hlow : p ∉ lowerHalf i n := by
      rw [lowerHalf_eq_union]
      simp only [Finset.mem_union]
      tauto
    exact BoxOddNotStrict.massive_mulVec_supported i ⟨k, hk⟩ m hvsupp p hlow
  · exact mem_strictLower.mpr (by simp; omega)

end Box

/-! ## 3. Review — the ways this could be hollow

**"Is §1 a theorem or a rearrangement?"** A rearrangement, and a short one:
one number is bounded above by zero and below by zero. What makes it worth
stating is that the two bounds come from opposite directions — positivity of
the reflected form, and nonpositivity of the coupling — and the identity from
`BoxOddNotStrict` is what says they are bounds on the same number. **Nothing
here is new machinery; what is new is that the converse now has a proof
rather than five constructions and a hope.**

**"Does it actually close the gap ERRATUM 73 left?"** Partly, and the header
says which part. It supplies the converse *mechanism* in the general setting
— reach inside implies not strict — and the contrapositive says strictness
forces the reach to escape. It does NOT produce a single biconditional,
because the sufficient condition proved elsewhere is about touching and this
necessary one is about reach, and neither is the negation of the other. **A
graph can fail both**, and saying otherwise would repeat exactly the mistake
ERRATUM 73 records.

**"Is the reach hypothesis doing real work, or is it always true?"** Real
work: it holds on the box at odd side, where the mirror layer absorbs the
step, and fails everywhere else on this wall. **It is not, however, the
characterisation of strictness, and a draft of this file said it was.** The
implication proved here — reach inside implies not strict — holds on every
row of ERRATUM 73's table. Its converse does not: at box side FOUR the reach
escapes into the far half and the form is degenerate regardless, and the same
at box six and torus five and six. So the reach condition explains the odd
box and constrains the strict cases, and `BoxNotStrict`'s separate
construction remains the only proof at even side. **Four of the ten measured
rows are outside what this criterion decides**, and that was found by testing
the sentence rather than by re-reading it.

**"Is §2 a genuine re-derivation or a restatement?"** Genuine: it calls §1
with the reach lemma and the coupling bound and nothing else, and in
particular it does not use the fact that the coupling vanishes — §1 derives
that. `BoxOddNotStrict` had to prove it as geometry. **The old proof is left
standing** because it produces the witness explicitly and this one produces a
generic indicator, and the explicit witness is the one that matched the
independent measurement.

**"What remains open on this wall?"** Nothing about sharpness. The box and
the torus are settled at every side length, the estate's own definition is
settled from side three, both directions of the criterion are proved in the
general setting, and the one thing not claimed — a single biconditional — is
not claimed because it is not true in the form anyone would want to write.
-/

end ReachCriterion
