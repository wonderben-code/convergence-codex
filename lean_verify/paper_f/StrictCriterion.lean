/-
  StrictCriterion.lean — when reflection positivity IS strict, and the box
  picture closed.

  WHY. Five files on this wall have now proved reflection positivity NOT
  strict, each by exhibiting a null direction, and each has ended by naming
  the same informal reason it happens: **a coefficient family can hide from
  the cut.** The converse was written down as prose months ago — *strictness
  holds exactly when every site of the half touches the mirror* — and
  deliberately not formalised, on the stated grounds that it had one instance
  (the prism) and a bespoke single-use predicate is worse than a sentence.

  **That objection has expired.** Measuring the box at small sides (exact
  rational arithmetic, `d = 1, 2, 3`) says sides one and two are STRICT while
  three and up are not, and at side two every site of the half is adjacent to
  its own mirror. So the criterion now has two instances and closes a gap
  `BoxOddNotStrict` left open in writing. **The measurement came first; this
  file is not a guess being confirmed** (ERRATUM 72).

  **THE GENERALISATION THAT MADE IT CHEAP, and it was already flagged.**
  `PrismStrict`'s review section says of its strict antitonicity lemma: *"The
  general form — `M − P` positive definite — is true and this proof gives it
  ... It is not written because it was not needed."* It is needed now, and it
  turns out not to need that proof at all: **the variational inequality in
  `GraphMirrorReflection` gives the general form in six lines**, with no
  matrix products, no `PosDef.mul_self`, and no determinant. Feed the
  optimiser for `M` into the bound for `P` and the two linear terms cancel,
  leaving exactly `⟪M⁻¹x, (M − P) M⁻¹x⟫`.

  WHAT THIS FILE PROVES:
  1. **`inv_sub_inv_posDef_gen`** — for positive definite `P`, `M` with
     `M − P` positive definite, `P⁻¹ − M⁻¹` is positive definite. The general
     strict antitonicity of the matrix inverse, which `PrismStrict` recorded
     as available and unwritten.
  2. **`reflectionPositive_strict_of_gap`** — strict reflection positivity on
     any graph, from `A − B ≻ A + B` alone. The strict twin of
     `GraphReflectionPositive.reflectionPositive_of_crossOp_nonpos`.
  3. **`gap_posDef_of_touching`** — and that hypothesis holds whenever the
     cut-crossing edges are diagonal AND every site of the half has one.
     **This is the prose criterion, finally a theorem.**
  4. **`reflectionPositive_box_two_strict`** — the box of side TWO is strict,
     in every dimension.
  5. **`reflectionPositive_box_one_strict`** — and side ONE, where the
     reflection is the identity and the reflected form is the energy. Proved
     separately because no half exists there, so §2 cannot reach it.

  **SO THE BOX IS SETTLED AT EVERY SIDE LENGTH**: strict at one and two,
  not strict at three and up (`BoxNotStrict`, `BoxOddNotStrict`). No case is
  left open and no case is guessed.

  WHAT THIS DOES NOT DO.
  * **It is not an "exactly when", and the prose that said so is REFUTED.**
    §3 gives one direction: touching implies strict. **The converse is false,
    and there is now a counterexample** — the TORUS AT SIDE THREE, where the
    site on the midline touches nothing (it is its own mirror, and the graph
    is loopless) and the form is strict anyway. Measured after this file's
    theorems were proved, which is why the caution above was worth keeping
    (ERRATUM 73).
    **What the measurement says the right criterion is**, matching all twenty
    cases tried — box and torus, sides two to six, dimensions one and two —
    is: *the cross-coupling restricted to the STRICT half (strictly below the
    midline) is negative definite.* Touching is the special case where that
    block is minus the identity, and a site ON the mirror is rigid for a
    different reason the touching condition cannot express. Proving that
    version needs the three-block form with a middle layer, which this file
    does not build; it is on the watchlist with the data.
    **AMENDED 2026-08-10, SAME DAY: the three-block form was NOT needed.**
    `MirrorStrict` proves the corrected criterion by KEEPING a term that
    `reflectionPositive_mirror` already derives and then throws away — the
    completing-the-square chain gives `reflectedForm ≥ −crossForm (G · anti c)`
    before any hypothesis on the coupling is used. No Schur complement, no
    middle-layer block. Fourth route this month refused on an unchecked claim
    about machinery the estate already owned; ERRATUM 71's addenda record the
    pattern, and this sentence is one of its instances.
  * **Nothing new for the prism.** `PrismStrict` already had it by a longer
    route through two Green functions; that route is left standing because it
    proves a sharper statement (an equality of forms) than this one needs.
  * **The torus at four or less is untouched**, and the box result does not
    transfer — a torus site at the bottom layer touches its mirror through
    the wrap-around, but the innermost layer touches through the midline too,
    and whether every site touches depends on the side in a way this file
    does not analyse.
    **AMENDED 2026-08-10, SAME DAY: the torus is now settled at four or less,
    and every case is strict.** Sides three and four by `MirrorStrict`, whose
    `torus_touching` performs exactly the side-dependent analysis this bullet
    declined — both edge types are needed and neither suffices alone. Sides one
    and two by `SmallSideStrict`, side two transporting along
    `torus_two_eq_box` and side one by the identity reflection.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import OddNotStrictInstances

namespace StrictCriterion

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphReflectionPositive

/-! ## 1. Strict antitonicity of the inverse, in general

`PrismStrict.inv_sub_inv_posDef` does the case `M = P + 1 + 1` through matrix
products. The general case is shorter, because the variational inequality
already proved for the mirror-half positivity argument does all the work.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`M − P ≻ 0` IMPLIES `P⁻¹ − M⁻¹ ≻ 0`.** Recorded as available and
    unwritten in `PrismStrict`'s review; written here because §2 needs it,
    and by a different route than that review anticipated. -/
theorem inv_sub_inv_posDef_gen {P M : Matrix ι ι ℝ} (hP : P.PosDef) (hM : M.PosDef)
    (hgap : (M - P).PosDef) : (P⁻¹ - M⁻¹).PosDef := by
  classical
  have hMu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM.isUnit
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨Matrix.IsHermitian.sub (Matrix.PosDef.inv hP).1 (Matrix.PosDef.inv hM).1, ?_⟩
  intro x hx
  -- the optimiser for `M`, fed into the bound for `P`
  set z : ι → ℝ := M⁻¹ *ᵥ x with hz
  have hzne : z ≠ 0 := by
    intro h0
    refine hx ?_
    have : M *ᵥ z = x := by
      rw [hz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hMu, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at this
    exact this.symm
  have hPle := GraphMirrorReflection.dotProduct_inv_le hP x z
  have hMeq := GraphMirrorReflection.dotProduct_inv_eq hM x
  have hgapx := (Matrix.posDef_iff_dotProduct_mulVec.mp hgap).2 hzne
  rw [Matrix.sub_mulVec, dotProduct_sub] at hgapx
  simp only [star_trivial] at hgapx hPle hMeq ⊢
  rw [Matrix.sub_mulVec, dotProduct_sub, ← hz] at *
  linarith

/-! ## 2. Strict reflection positivity from a strict gap -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H : Finset V}

/-- **THE STRICT CRITERION.** The strict twin of
    `reflectionPositive_of_crossOp_nonpos`: where that asks the cross-coupling
    to be nonpositive and concludes `0 ≤`, this asks the gap `A − B` minus
    `A + B` to be positive DEFINITE and concludes `0 <`. -/
theorem reflectionPositive_strict_of_gap (hH : IsHalf θ H) (h : IsRefl G θ) (hm : m ≠ 0)
    (hgap : (minusOp G m θ H - plusOp G m θ H).PosDef)
    {c : V → ℝ} (hc0 : c ≠ 0) (hcsupp : ∀ p, p ∉ H → c p = 0) :
    0 < GraphReflection.reflectedForm G m θ c := by
  classical
  set w : H → ℝ := fun p => c ↑p with hw
  have hwne : w ≠ 0 := by
    intro h0
    refine hc0 (funext fun p => ?_)
    by_cases hp : p ∈ H
    · exact congrFun h0 ⟨p, hp⟩
    · exact hcsupp p hp
  have hstrict := (Matrix.posDef_iff_dotProduct_mulVec.mp
    (inv_sub_inv_posDef_gen (plusOp_posDef hH h hm) (minusOp_posDef hH h hm) hgap)).2 hwne
  rw [Matrix.sub_mulVec, dotProduct_sub] at hstrict
  rw [← ext_eq_self (H := H) hcsupp, ← hw]
  have h4 := GraphReflection.reflectedForm_eq (G := G) (m := m) h (ext H w)
  rw [GraphHalfSpace.sym_eq_symExt hH (fun p hp => ext_notMem w hp),
    GraphHalfSpace.anti_eq_antiExt hH (fun p hp => ext_notMem w hp),
    energy_symExt_eq hH h hm w, energy_antiExt_eq hH h hm w] at h4
  simp only [star_trivial] at hstrict h4
  linarith

/-- **AND THE GAP IS EXACTLY THE PROSE CRITERION.** If the only cut-crossing
    edges join a site to its own mirror, and EVERY site of the half has one,
    then the gap is positive definite — it is twice the identity. -/
theorem gap_posDef_of_touching (hH : IsHalf θ H)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q)
    (hfull : ∀ p ∈ H, G.Adj p (θ p)) :
    (minusOp G m θ H - plusOp G m θ H).PosDef := by
  classical
  have hentry : minusOp G m θ H - plusOp G m θ H = (2 : ℝ) • (1 : Matrix H H ℝ) := by
    ext p q
    simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    have hne : (p : V) ≠ θ (q : V) := fun hc => hH.notMem_of_mem q.2 (hc ▸ p.2)
    have hdiff : (minusOp G m θ H - plusOp G m θ H) p q
        = -2 * GraphLaplacian.massive G m (p : V) (θ (q : V)) := by
      simp only [Matrix.sub_apply, minusOp, plusOp, Matrix.of_apply,
        GraphHalfSpace.crossOp, Matrix.of_apply]
      ring
    rw [hdiff, GraphLaplacian.massive_apply, if_neg hne]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos (hfull (p : V) p.2)]
      simp
    · have hnadj : ¬ G.Adj (p : V) (θ (q : V)) := fun hc =>
        hpq (Subtype.ext (hdiag (p : V) p.2 (q : V) q.2 hc))
      rw [if_neg hnadj, if_neg hpq]
      ring
  rw [hentry]
  exact (Matrix.PosDef.one).smul (by norm_num)

/-! ## 3. The box at side two, and at side one -/

variable {d n : ℕ}

/-- At side two every site of the lower half sits on the cut, so it is
    adjacent to its own mirror: the reflected coordinate goes from `0` to
    `1` and the others are untouched. -/
theorem box_two_touching (i : Fin d) :
    ∀ p ∈ lowerHalf i 2, (boxGraph d 2).Adj p (GraphReflection.revSite (n := 2) i p) := by
  intro p hp
  have hp0 : (p i).val = 0 := by
    simp only [lowerHalf, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    omega
  refine ⟨i, fun j hj => (GraphReflection.revSite_apply_ne hj p).symm, Or.inl ?_⟩
  rw [GraphReflection.revSite_apply_self, Fin.val_rev]
  omega

/-- **THE BOX OF SIDE TWO IS STRICT**, in every dimension. This is the case
    `BoxNotStrict` (four and up) and `BoxOddNotStrict` (three and up) both
    leave out, and it comes out on the other side. -/
theorem reflectionPositive_box_two_strict (i : Fin d) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d 2 → ℝ} (hc0 : c ≠ 0) (hcsupp : ∀ p, p ∉ lowerHalf i 2 → c p = 0) :
    0 < GraphReflection.reflectedForm (boxGraph d 2) m
          (GraphReflection.revSite (n := 2) i) c :=
  reflectionPositive_strict_of_gap (isHalf_lowerHalf i (by decide))
    (GraphReflection.boxGraph_revSite_aut i) hm
    (gap_posDef_of_touching (isHalf_lowerHalf i (by decide))
      (TorusReflection.boxGraph_cross_diag i (by decide)) (box_two_touching i))
    hc0 hcsupp

/-- At side one the reflection is the identity: `Fin.rev` on `Fin 1` fixes
    its only element. -/
theorem revSite_one_eq_id (i : Fin d) (p : BoxGraph.Site d 1) :
    GraphReflection.revSite (n := 1) i p = p := by
  funext j
  by_cases hj : j = i
  · subst hj
    exact Fin.ext (by omega)
  · exact GraphReflection.revSite_apply_ne hj p

/-- **AND THE BOX OF SIDE ONE IS STRICT.** Proved directly rather than
    through §2, because at side one no half exists — `IsHalf` forces the
    reflection to be fixed-point free and here it is the identity — so the
    criterion cannot reach this case even though the result is easier. -/
theorem reflectionPositive_box_one_strict (i : Fin d) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d 1 → ℝ} (hc0 : c ≠ 0) :
    0 < GraphReflection.reflectedForm (boxGraph d 1) m
          (GraphReflection.revSite (n := 1) i) c := by
  classical
  have hform : GraphReflection.reflectedForm (boxGraph d 1) m
      (GraphReflection.revSite (n := 1) i) c
      = GraphReflection.energy (boxGraph d 1) m c := by
    simp only [GraphReflection.reflectedForm, GraphReflection.energy, GraphReflection.bil]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [revSite_one_eq_id i p]
  rw [hform, GraphMirrorReflection.energy_eq_dotProduct]
  have := (Matrix.posDef_iff_dotProduct_mulVec.mp
    (GraphLaplacian.green_posDef (boxGraph d 1) hm)).2 hc0
  simpa [dotProduct_comm] using this

/-! ## 4. Review — the ways this could be hollow

**"Is this the converse of the not-strict files, or something weaker?"**
Weaker, and the header says so rather than the review having to. §3 proves
*touching implies strict*. The prose that prompted the file said "exactly
when", and the other direction — a site that misses the mirror always yields
a null direction — is proved case by case in the NOT-strict files and is not
unified here. **Calling the pair an equivalence would be the overclaim this
project keeps catching**, so it is not called one. **AMENDED 2026-08-10, SAME DAY (ERRATUM 76): A BICONDITIONAL DOES EXIST**, and this sentence generalised from the failure of one candidate to the non-existence of any. `StrictBiconditional.strict_iff_not_supportedIsotropic`: the form is strict exactly when no nonzero vector on the half is both killed by the coupling and kept inside the region by the massive operator. It comes from negating `NullSpace.reflectedForm_eq_zero_iff_massive`, which was proved the same day facing the other way. **What stays true is the narrower claim** — touching and reach are two different conditions and neither is the negation of the other, so THAT pair is not an equivalence.

**"Two instances is barely more than one. Has the objection really
expired?"** The original objection was that a predicate used once is worse
than a sentence. It is now used at the prism and at the box of side two, and
— the part that matters more — **it closes a gap that was written down as
open**, which a sentence cannot do. `BoxOddNotStrict` stated in its own
review that sides one and two were uncovered; they are covered now, with the
answer going the other way from the rest of the wall.

**"Was the answer predicted or measured?"** Measured, before any Lean was
written: exact rational arithmetic on the box at sides one to four in
dimensions one to three. Sides one and two came back nondegenerate, three and
four degenerate. **The two entries immediately before this one are about
predicting instead of measuring** (ERRATA 71, 72), so the order was not
optional.

**"§1 claims to improve on `PrismStrict`. Does it?"** It generalises the
hypothesis from `M = P + 1 + 1` to `M − P` positive definite, which is what
that file's own review said was available and unwritten. It does NOT
generalise that file's route — it replaces it, using the variational
inequality instead of matrix products, and the replacement is shorter. Both
are kept: `PrismStrict` proves an equality of forms that this file does not
need and does not supply.

**"Why is side one proved separately?"** Because at side one the reflection
is the identity, so no half exists — `IsHalf` forces fixed-point-freeness,
and the estate proves that. **The criterion is unavailable exactly where the
result is easiest**, which is a fact about the machinery worth stating rather
than routing around silently.

**"What is the state of the box now?"** Settled at every side length: strict
at one and two, not strict at three and up. **No case open, no case guessed.**
The estate's own `def` inherits sides three and up by transport but its
side-one and side-two cases are not stated here; the torus at four or less
remains open and this file's argument does not reach it, because a torus site
touches its mirror through the wrap-around as well as the midline and whether
every site touches is side-dependent in a way not analysed.
**AMENDED 2026-08-10, SAME DAY: both gaps are closed.** `SmallSideStrict`
states the estate's own `def` at sides one and two; `MirrorStrict` and
`SmallSideStrict` between them settle the torus at every side of four or less.
The sentence is kept because "not stated here" is the phrasing that let the gap
be found — the same sweep caught a sibling file saying "settled" of a case with
no theorem (ERRATUM 74).
-/

end StrictCriterion
