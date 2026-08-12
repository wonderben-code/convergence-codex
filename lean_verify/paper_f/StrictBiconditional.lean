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
  7. **`strict_iff_crossForm_neg_on_reachKernel`** — **the same criterion in
     closed form**: strict exactly when the coupling is NEGATIVE DEFINITE on
     the subspace of vectors the operator keeps inside the region. Two lines
     from §3, because the isotropy clause is the only quadratic one. **This is
     the same SHAPE as ERRATUM 73's measured criterion**, restricted to a
     different subspace — the measurement said "the strict half", and the two
     are not claimed to coincide. §7 says what is and is not settled by that.
  8. **`supportedIsotropic_box_even`** — and the even box run the other way:
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
    not. **AND THAT IS NOW A THEOREM RATHER THAN AN EXPLANATION**, 2026-08-12:
    `IndefiniteCoupling.backward_direction_fails` exhibits a four-vertex graph
    where the coupling is indefinite, no supported isotropic vector exists, and
    the form is strictly negative — premise true, conclusion false. So `hcross`
    is **necessary** in the backward direction, not merely used by this proof of
    it. §3b removes it from the FORWARD direction, where it was never needed.
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

/-! ## 3b. The forward half without the coupling hypothesis

§8 says of `hcross` that it is *"genuinely needed, in one direction only"*. That is true, and the
biconditional above carries it in both anyway, because a biconditional has one hypothesis list.
Stated separately, the forward half needs nothing about the coupling's sign — so it survives
exactly where §3 does not: **an indefinite coupling**, the case §8 names as breaking the
equivalence. -/

/-- **A SUPPORTED ISOTROPIC VECTOR IS A NULL DIRECTION, WHATEVER THE COUPLING DOES.** No
`hcross`. The two clauses do all the work: isotropy makes
`BoxOddNotStrict.reflectedForm_massive_eq_crossForm`'s right-hand side vanish, and the reach
clause is what puts `massive *ᵥ v` in the region where the reflected form is being asked about.
Nothing here inspects the sign of anything. -/
theorem reflectedForm_massive_eq_zero_of_isotropic (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) {v : V → ℝ} (hvsupp : ∀ p, p ∉ H → v p = 0)
    (hviso : crossForm G m θ H v = 0) :
    GraphReflection.reflectedForm G m θ (GraphLaplacian.massive G m *ᵥ v) = 0 := by
  rw [BoxOddNotStrict.reflectedForm_massive_eq_crossForm hM h hm hvsupp,
    crossForm_anti_eq hM hvsupp]
  exact hviso

/-- **AND SO IT REFUTES STRICTNESS, WITH NO HYPOTHESIS ON THE COUPLING.** This is §3's forward
direction with `hcross` **removed**, and it is the half that matters for a negative result: to
show a graph is not strict one exhibits a supported isotropic vector, and one should not have to
know the coupling is nonpositive first.

**Where the removal buys something rather than tidying.** With an indefinite coupling the
reflected form can be negative, `reflectionPositive_mirror` does not apply, and §3 is false as a
biconditional — §8 says so. This statement holds there unchanged. -/
theorem not_strict_of_supportedIsotropic (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hiso : SupportedIsotropic G m θ H Mir) :
    ¬ (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c) := by
  rintro hstrict
  obtain ⟨v, hv0, hvsupp, hviso, hvreach⟩ := hiso
  exact absurd (reflectedForm_massive_eq_zero_of_isotropic hM h hm hvsupp hviso)
    (ne_of_gt (hstrict _ (massive_mulVec_ne_zero hm hv0) hvreach))

/-! ## 3c. The biconditional, with its forward half now imported -/

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
  · -- §3b, which does not use `hcross`; imported rather than repeated, so that the
    -- hypothesis-free version is checked against this one rather than parallel to it.
    exact fun hstrict hiso => not_strict_of_supportedIsotropic hM h hm hiso hstrict
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

/-! ## 7. The criterion in closed form, and ERRATUM 73's table explained

The two clauses of `SupportedIsotropic` are of different kinds and the
difference is what lets them be separated. The support condition and the reach
condition are both LINEAR — they cut out a subspace of vectors on the half.
The isotropy condition is QUADRATIC. So the whole criterion says: the coupling
form, restricted to that subspace, has no nontrivial zero — and since the
coupling is nonpositive to begin with, no nontrivial zero means negative
definite.

**It is the same SHAPE as ERRATUM 73's measured criterion, and not the same
statement.** The measurement said *the coupling restricted to the strict half
is negative definite*, and matched the twenty cases it was tested on. **The two
restrictions are to different subspaces and this file does not claim they
coincide.** They plainly can differ: where the reach stays inside, the subspace
here is the whole half and the coupling is identically zero on it — never
negative definite, so never strict — while at the other extreme the subspace
can be trivial and the condition vacuous, giving strictness for a reason the
measured version states quite differently.

**AND THE SPECTRUM THE PARAGRAPH ABOVE DESCRIBES IS NOT A SPECTRUM, 2026-08-12
(`ERRATUM 150`).** It names two extremes — reach inside, where the coupling
vanishes on the whole half and strictness fails; and a trivial subspace, where
the condition is vacuous and strictness holds — and reads as though the cases
between them are the interesting ones. **There are no cases between them.**
`CrossBlockStructure.crossForm_eq_zero_of_inReachKernel`: a vector supported on
the half and in the reach kernel has `crossForm v = 0`, on EVERY graph with a
mirror reflection, with no coupling hypothesis. So the coupling is identically
zero on that subspace always, not only when the reach stays inside, and the
right-hand side of `strict_iff_crossForm_neg_on_reachKernel` is satisfiable only
vacuously: **strict exactly when the reach kernel is trivial**
(`CrossBlockStructure.strict_iff_reachKernel_trivial`). Nothing here is false —
the biconditional is a theorem and stays one — and the paragraph is kept because
what it got right is the harder half: that the two restrictions differ and that
this file does not claim they coincide.

  What the closed form settles is that a DEFINITENESS condition was the right
  shape to be measuring, and which restriction makes it a theorem. Whether the
  measured version agrees in verdict on every row of that table is a separate
  question, not checked here and not asserted — checking it means recomputing
  the table against this subspace, which nobody has done.
-/

/-- The vectors on the half that the massive operator keeps inside the region.
    A linear condition, though nothing here needs it to be. -/
def InReachKernel (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (H Mir : Finset V)
    (v : V → ℝ) : Prop :=
  (∀ p, p ∉ H → v p = 0)
    ∧ ∀ p, p ∉ H → p ∉ Mir → (GraphLaplacian.massive G m *ᵥ v) p = 0

/-- **THE CRITERION IN CLOSED FORM.** The reflected form is strict exactly when
    the coupling is NEGATIVE DEFINITE on the subspace of vectors the operator
    keeps inside the region. This is ERRATUM 73's measured criterion with the
    restriction corrected from "the strict half" to that subspace, and it is a
    two-line consequence of §3 — the isotropy clause is the only quadratic one,
    so it is the only one that survives into a definiteness statement.

    **THE DEFINITENESS IS VACUOUS, 2026-08-12 (`ERRATUM 150`).** The coupling is
    identically zero on this subspace — `CrossBlockStructure.crossForm_eq_zero_of_inReachKernel`,
    which needs neither `hcross` nor anything about the graph beyond the two
    hypotheses above — so the right-hand side holds exactly when the subspace is
    trivial. The theorem is unchanged; what it says is
    `CrossBlockStructure.strict_iff_reachKernel_trivial`. And the isotropy
    clause of `SupportedIsotropic` is implied by the other two at every site
    where that definition is used. -/
theorem strict_iff_crossForm_neg_on_reachKernel (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ ∀ v : V → ℝ, InReachKernel G m H Mir v → v ≠ 0 → crossForm G m θ H v < 0 := by
  rw [strict_iff_not_supportedIsotropic hM h hm hcross]
  constructor
  · rintro hno v ⟨hvs, hvr⟩ hv0
    rcases lt_or_eq_of_le (hcross v) with hlt | heq
    · exact hlt
    · exact absurd ⟨v, hv0, hvs, heq, hvr⟩ hno
  · rintro hneg ⟨v, hv0, hvs, hviso, hvr⟩
    exact absurd hviso (ne_of_lt (hneg v ⟨hvs, hvr⟩ hv0))

/-! ## 8. Review — the ways this could be hollow

**This section was `## 6` until `ERRATUM 140`, and there is no §6 now.** It was written when the
file ended at §5, and §7 was then appended ABOVE it — the defect `check_ledger.py --sections`
exists to catch, and the reason its number is the oldest in the file. Renumbering here was NOT
free: nine references had to move with it, three in this file, three in `IndefiniteCoupling` and
three in the ledgers. That is the cost of a section number escaping its file, and it is recorded
because it is the argument for fixing this class of defect early rather than late.


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
about the coupling's sign — **which §3b now states separately, with the
hypothesis gone.**

The last sentence of this paragraph used to read *"An indefinite coupling breaks
the equivalence and this file does not claim otherwise."* **It is now claimed,
and proved elsewhere, 2026-08-12.** `IndefiniteCoupling` builds the perfect
matching `0–3`, `1–2` on `Fin 4` with half `{0,1}` and reflection `p ↦ p + 2`;
there the coupling reaches `+2`, no supported isotropic vector exists (the reach
clause alone empties the condition), and the reflected form is strictly
negative. `backward_direction_fails` is the pair, and it upgrades this
paragraph's caution into a **necessity** result: `hcross` cannot be dropped from
§3's backward direction. Nothing above changes; what changes is that the reader
no longer has to take the caveat on trust.

**"Is §5 a real check or a re-run?"** A real one: it decides the odd box
without the witness `BoxOddNotStrict` constructs and without the reach argument
`ReachCriterion` supplies by hand, using only that the coupling vanishes. Three
routes to one fact is not redundancy here — it is the evidence that the
criterion is connected to the wall rather than parallel to it.
-/

end StrictBiconditional
