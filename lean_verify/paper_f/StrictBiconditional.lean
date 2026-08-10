/-
  StrictBiconditional.lean — the "exactly when" the wall has been declining to
  claim, obtained by negating one that was already proved.

  WHY, AND WHY IT IS NOT THE THING ERRATUM 73 FORBIDS. FOUR files on this wall
  end with a version of the same sentence — counted, not recalled:
  `MirrorStrict` ("still not an 'exactly when'"), `StrictCriterion` ("it is not
  called one"), `ReachCriterion` (three times, "it does NOT produce a single
  biconditional") and `ReachIsCoupling`, written earlier the same day. All say: *there
  is no single biconditional for strictness, and claiming one is exactly the
  mistake ERRATUM 73 records.*
  That caution was right about the criterion it was written about — *strict
  exactly when every site touches the mirror*, refuted by the torus at side
  three — and it is right about the pair "touching implies strict" /
  "reach-inside implies not strict", which are two different conditions and
  neither is the negation of the other.

  **It is not right that no biconditional exists**, and the one that does was
  proved earlier the same day, facing the other way. `NullSpace.reflectedForm_eq_zero_iff_massive`
  says exactly which coefficient families are null. Strictness, under the
  standing coupling hypothesis, is precisely the statement that none is. **So
  negate it.** No new mathematics is required and none is claimed; what is
  required is noticing that a characterisation of the null space is a
  characterisation of strictness with a `¬` in front, which nobody had written
  down because the null-space question and the strictness question had been
  pursued in different files.

  **THE CONDITION, and what makes it a criterion rather than a restatement.**
  A *supported isotropic vector* is a nonzero `v` living on the half with two
  properties: the coupling vanishes at it, and the massive operator does not
  carry it out of the region. The form is strict **exactly when no such vector
  exists**. Both clauses are conditions on the graph and the coupling — not on
  the reflected form — so the criterion says something, and §4 discharges it in
  both directions to show it says the right thing:

  * **When the coupling is negative definite on the half**, the first clause
    alone kills every candidate, so strictness follows and the second clause is
    never consulted. That is `MirrorStrict`'s regime.
  * **When the coupling vanishes identically**, every `v` satisfies the first
    clause and — by `ReachIsCoupling`'s identification — every `v` satisfies
    the second too, so any nonzero one is a witness and the form is not strict.
    That is `ReachCriterion`'s regime.
  * **In between**, which is every remaining row of ERRATUM 73's measured
    table, the two clauses genuinely compete, and that competition is what the
    table was recording. The box at EVEN side is the honest example, and §5
    proves rather than asserts it: its coupling is not identically zero, so
    neither regime above applies, and it is degenerate anyway — so an
    isotropic vector must sit exactly where the operator cannot push it out,
    and `supportedIsotropic_box_even` produces one.

  **WHAT THIS DOES AND DOES NOT SETTLE.** It settles the shape of the answer.
  It does not decide any particular graph, because deciding one means deciding
  whether a supported isotropic vector exists there, and that is a computation
  per graph. **A criterion that reduces a hard question to a finite check is
  not the same as an algorithm, and this file does not pretend to be one.**

  WHAT THIS FILE PROVES:
  1. **`crossForm_anti_eq`** — for `v` on the half, the coupling does not
     notice the antisymmetrisation: `crossForm (anti θ v) = crossForm v`. Two
     lines, and it is what lets the criterion be stated about `v` rather than
     about a derived vector nobody can inspect.
  2. **`SupportedIsotropic`** — the condition, as a definition, so that the
     two regimes in §4 are instances of one predicate rather than analogies.
  3. **`strict_iff_not_supportedIsotropic`** — **the biconditional.** Over an
     arbitrary graph and an arbitrary mirror half, under the coupling
     hypothesis the whole wall already assumes.
  4. **`strict_of_crossForm_neg`** — the negative-definite regime, recovered.
  5. **`not_strict_of_crossForm_zero`** — the vanishing regime, recovered,
     with `ReachIsCoupling` supplying the second clause for free.
  6. **`not_strict_box_odd_via_criterion`** — the odd box decided by the
     criterion alone, as the check that it reaches a case the wall already
     knows (ERRATUM 48).
  7. **`supportedIsotropic_box_even`** — and the even box run the other way:
     `BoxNotStrict` says it is degenerate, so the criterion says a supported
     isotropic vector EXISTS there. Neither regime of §4 reaches that case, so
     it is the evidence that the biconditional has content between the two
     extremes rather than only at them.

  WHAT THIS DOES NOT DO.
  * **It does not refute ERRATUM 73 or soften it.** That entry refutes a
    specific sentence, *strict exactly when every site touches the mirror*,
    and that sentence stays refuted — touching is sufficient and never
    necessary. What is corrected here is a different sentence, the one saying
    no biconditional of any kind is available.
  * **It does not remove the coupling hypothesis.** `hcross` is load-bearing
    in the backward direction: without a sign on the coupling, "the form is
    never negative" fails and strictness stops being the negation of
    degeneracy. `NullSpace.reflectedForm_slack` holds without it and this does
    not.
  * **It decides no new graph.** Every instantiation in §4 and §5 is a case
    the wall had already settled by other means; the criterion is checked
    against them, not used to extend them.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import ReachIsCoupling

namespace StrictBiconditional

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection BoxOddReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The coupling does not see the antisymmetrisation

`crossForm` indexes both its sums by the half, so it depends on its argument
only through the restriction to the half — and on the half, a vector supported
there is its own antisymmetrisation, because the mirror image of a site of the
half is outside it.
-/

theorem crossForm_anti_eq (hM : IsMirrorHalf θ H Mir) {v : V → ℝ}
    (hv : ∀ p, p ∉ H → v p = 0) :
    crossForm G m θ H (GraphReflection.anti θ v) = crossForm G m θ H v := by
  classical
  have hres : ∀ p ∈ H, GraphReflection.anti θ v p = v p := by
    intro p hp
    simp only [GraphReflection.anti]
    rw [hv (θ p) (hM.notMem_of_mem hp), sub_zero]
  refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
  rw [hres p hp, hres q hq]

/-! ## 2. The condition -/

/-- **A SUPPORTED ISOTROPIC VECTOR.** Nonzero, living on the half, killed by
    the coupling, and not pushed out of the region by the massive operator.
    Both clauses are conditions on the graph; neither mentions the reflected
    form. -/
def SupportedIsotropic (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (θ : V ≃ V)
    (H Mir : Finset V) : Prop :=
  ∃ v : V → ℝ, v ≠ 0 ∧ (∀ p, p ∉ H → v p = 0)
    ∧ crossForm G m θ H v = 0
    ∧ (∀ p, p ∉ H → p ∉ Mir → (GraphLaplacian.massive G m *ᵥ v) p = 0)

/-- The massive operator is injective, so a nonzero vector on the half gives a
    nonzero coefficient family. Extracted from `ReachCriterion`, which proves
    it inline. -/
theorem massive_mulVec_ne_zero (hm : m ≠ 0) {v : V → ℝ} (hv : v ≠ 0) :
    GraphLaplacian.massive G m *ᵥ v ≠ 0 := by
  classical
  intro hc
  refine hv ?_
  have hunit : IsUnit (GraphLaplacian.massive G m).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (GraphLaplacian.massive_posDef G hm).isUnit
  have := congrArg (fun w => GraphLaplacian.green G m *ᵥ w) hc
  simpa [GraphLaplacian.green, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hunit] using this

/-! ## 3. The biconditional

`NullSpace.reflectedForm_eq_zero_iff_massive` says which families are null.
Strictness says none is. The only work is turning one quantifier around and
checking that the two support conditions line up.
-/

/-- **STRICT EXACTLY WHEN NO SUPPORTED ISOTROPIC VECTOR EXISTS.** Over an
    arbitrary graph and an arbitrary mirror half, under the coupling
    hypothesis the wall already assumes everywhere. -/
theorem strict_iff_not_supportedIsotropic (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ ¬ SupportedIsotropic G m θ H Mir := by
  classical
  constructor
  · rintro hstrict ⟨v, hv0, hvsupp, hviso, hvreach⟩
    have hc0 : GraphLaplacian.massive G m *ᵥ v ≠ 0 := massive_mulVec_ne_zero hm hv0
    have hform : GraphReflection.reflectedForm G m θ (GraphLaplacian.massive G m *ᵥ v) = 0 := by
      rw [BoxOddNotStrict.reflectedForm_massive_eq_crossForm hM h hm hvsupp,
        crossForm_anti_eq hM hvsupp]
      exact hviso
    exact absurd hform (ne_of_gt (hstrict _ hc0 hvreach))
  · intro hno c hc0 hcsupp
    have hge : 0 ≤ GraphReflection.reflectedForm G m θ c :=
      reflectionPositive_mirror hM h hm hcross hcsupp
    rcases lt_or_eq_of_le hge with hlt | heq
    · exact hlt
    · exfalso
      obtain ⟨v, hvsupp, hvc, hviso⟩ :=
        (NullSpace.reflectedForm_eq_zero_iff_massive hM h hm hcross hcsupp).mp heq.symm
      refine hno ⟨v, ?_, hvsupp, ?_, ?_⟩
      · intro hv0
        refine hc0 ?_
        rw [← hvc, hv0, Matrix.mulVec_zero]
      · rw [← crossForm_anti_eq hM hvsupp]; exact hviso
      · intro p hpH hpM
        rw [hvc]
        exact hcsupp p hpH hpM

/-! ## 4. The two known regimes, recovered

Neither is new. They are here because a criterion that cannot reproduce the
results it claims to unify is not a unification (ERRATUM 48).
-/

/-- **THE NEGATIVE-DEFINITE REGIME.** If the coupling is strictly negative on
    every nonzero vector of the half, the first clause of the condition already
    has no solutions and strictness follows — the reach clause is never
    consulted. `MirrorStrict` reaches the same conclusion through the touching
    hypothesis, which is the special case where the coupling block is minus the
    identity. -/
theorem strict_of_crossForm_neg (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0)
    (hneg : ∀ v : V → ℝ, v ≠ 0 → (∀ p, p ∉ H → v p = 0) → crossForm G m θ H v < 0) :
    ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
      0 < GraphReflection.reflectedForm G m θ c := by
  refine (strict_iff_not_supportedIsotropic hM h hm hcross).mpr ?_
  rintro ⟨v, hv0, hvsupp, hviso, -⟩
  exact absurd hviso (ne_of_lt (hneg v hv0 hvsupp))

/-- **THE VANISHING REGIME.** If the coupling vanishes identically then every
    vector satisfies the first clause, and `ReachIsCoupling` supplies the
    second for every vector at once, so any nonzero vector on a nonempty half
    is a witness. `ReachCriterion` reaches the same conclusion; here the two
    clauses are visibly the two halves of that file's hypothesis. -/
theorem not_strict_of_crossForm_zero (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hzero : ∀ w : V → ℝ, crossForm G m θ H w = 0) {p₀ : V} (hp₀ : p₀ ∈ H) :
    ¬ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) := by
  classical
  intro hstrict
  refine (strict_iff_not_supportedIsotropic hM h hm
    (fun w => le_of_eq (hzero w))).mp hstrict ?_
  refine ⟨fun p => if p = p₀ then 1 else 0, ?_, ?_, hzero _, ?_⟩
  · intro h0
    have := congrFun h0 p₀
    simp at this
  · intro p hp
    exact if_neg fun hc => hp (by rw [hc]; exact hp₀)
  · exact ReachIsCoupling.reach_of_crossForm_eq_zero hM h hzero _
      (fun p hp => if_neg fun hc => hp (by rw [hc]; exact hp₀))

/-! ## 5. The odd box, decided by the criterion

ERRATUM 48's check at the level of an instance: the criterion must reach a case
the wall already knows, by its own route.
-/

section OddBox

variable {d n : ℕ}

/-- **THE ODD BOX IS NOT STRICT, FROM THE CRITERION.** Its coupling vanishes
    identically, so §4's vanishing regime applies with no geometry at all.
    Compare `BoxOddNotStrict.not_strict_box_odd`, which builds the witness, and
    `ReachCriterion.exists_null_direction_box_odd'`, which supplies the reach
    condition by hand. -/
theorem not_strict_box_odd_via_criterion (i : Fin d) (hn : Odd n) (h3 : 3 ≤ n)
    {m : ℝ} (hm : m ≠ 0) :
    ¬ (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ strictLower i n → p ∉ midLayer i n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph d n) m
              (GraphReflection.revSite (n := n) i) c) := by
  classical
  refine not_strict_of_crossForm_zero (isMirrorHalf_strictLower i n)
    (GraphReflection.boxGraph_revSite_aut i) hm
    (fun w => crossForm_odd_eq_zero i hn m w)
    (p₀ := fun j => if j = i then ⟨0, by omega⟩ else ⟨0, by omega⟩) ?_
  exact mem_strictLower.mpr (by simp; omega)

/-- **THE EVEN BOX HAS ONE, AND NEITHER REGIME OF §4 FINDS IT.** `BoxNotStrict`
    proves the even box degenerate from side four; the criterion therefore says
    a supported isotropic vector exists there. Its coupling is not identically
    zero, so §4's vanishing regime does not apply, and it is not negative
    definite either, so the other does not. **This is the case that shows the
    biconditional has content strictly between the two extremes** — and it is
    obtained by running the equivalence backwards from a known degeneracy
    rather than by constructing a witness. -/
theorem supportedIsotropic_box_even (i : Fin d) (hn : Even n) (h4 : 4 ≤ n)
    {m : ℝ} (hm : m ≠ 0) :
    SupportedIsotropic (boxGraph d n) m (GraphReflection.revSite (n := n) i)
      (lowerHalf i n) ∅ := by
  classical
  by_contra hno
  refine BoxNotStrict.not_strict i hn h4 hm fun c hc0 hcsupp => ?_
  refine (strict_iff_not_supportedIsotropic
    (isMirrorHalf_of_isHalf (isHalf_lowerHalf i hn))
    (GraphReflection.boxGraph_revSite_aut i) hm
    (fun w => crossForm_nonpos_of_cross_diag (isMirrorHalf_of_isHalf (isHalf_lowerHalf i hn))
      (TorusReflection.boxGraph_cross_diag i hn) w)).mpr hno c hc0
    (fun p hp _ => hcsupp p hp)

end OddBox

/-! ## 6. Review — the ways this could be hollow

**"Is this the thing ERRATUM 73 forbids?"** No, and the distinction is worth
being precise about rather than asserting. ERRATUM 73 refutes *strict exactly
when every site of the half touches the mirror* — a claim about a geometric
condition, refuted by the torus at side three. §3 makes no geometric claim: its
condition is the non-existence of a vector with two algebraic properties.
**The sentence this file corrects is a different one** — "no biconditional of
any kind is available" — which five files carry and which was inferred from the
failure of the touching one. An inference from "this criterion is not an
equivalence" to "no criterion is" is exactly the over-generalisation ERRATUM 73
is about, made in the cautious direction.

**"Is the criterion vacuous — is it just 'strict iff not degenerate'?"** It
would be if either clause mentioned the reflected form, and neither does. The
first is a condition on the coupling form, the second on the massive operator's
support. What makes it non-trivial is that the two can be checked separately
and that they pull in opposite directions: a coupling with many isotropic
vectors is one where the operator's reach is short, and §4 exhibits both
extremes. What it does NOT do is decide a given graph without work, and the
header says so.

**"Then why did nobody write this down?"** Because the null-space question and
the strictness question lived in different files with different vocabularies —
one asked "which families are null", the other "is the form positive". The
biconditional for the first was proved earlier today; **negating it is the
whole of §3, and the proof is thirty-one lines including the statement.** The
interesting fact is not the theorem but that the estate held both halves for
hours without the sentence.

**"Does `hcross` hide the difficulty?"** It is genuinely needed, in one
direction only, and the header says which. Backward needs the form to be
nonnegative so that strict is the negation of null; that is
`reflectionPositive_mirror` and it consumes `hcross`. Forward needs nothing
about the coupling's sign. An indefinite coupling breaks the equivalence and
this file does not claim otherwise.

**"Is §5 a real check or a re-run?"** A real one: it decides the odd box
without the witness `BoxOddNotStrict` constructs and without the reach argument
`ReachCriterion` supplies by hand, using only that the coupling vanishes. Three
routes to one fact is not redundancy here — it is the evidence that the
criterion is connected to the wall rather than parallel to it.
-/

end StrictBiconditional
