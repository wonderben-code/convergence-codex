/-
  SmallSideStrict.lean — the four small-side cases the wall called easy and
  never stated.

  WHY. A re-sweep of this campaign's own headers, not a new question. Three
  separate files record the small sides as settled-by-transport and none of
  them states the theorem:

  * `MirrorStrict`'s summary says "**THE TORUS IS SETTLED AT EVERY SIDE FROM
    TWO**: strict at two, three and four", and its theorem list has three and
    four. Side two is not there. Its review section is the honest one — "sides
    one and two are the box's by transport but are not stated" — but its
    WHAT-THIS-DOES-NOT-DO bullet names side ONE only, so the register
    under-reports its own gap by exactly one case.
  * `StrictCriterion`'s review says the estate's own `def` "inherits sides
    three and up by transport but its side-one and side-two cases are not
    stated here", and no later file states them either.

  **Two of those three sentences are true as written and one is not.** The
  review sentences — `MirrorStrict`'s "not stated", `StrictCriterion`'s "not
  stated here" — are exact. **`MirrorStrict`'s summary line is an overclaim**:
  in this project's vocabulary "settled" means a theorem exists, and at torus
  side two none did. The mathematics was right (the side-two torus IS the box,
  and the box is strict), so nothing false was asserted about reflection
  positivity; what was asserted falsely was the state of the estate. ERRATUM
  74 records it.

  What all three share is that each parks a case behind the word *transport*
  and then nobody performs the transport. That is a different defect from the
  ones ERRATA 71–73 record — those were claims about the estate made from
  memory instead of from the estate — and it deserves the cheapest possible
  answer, which is to do the work rather than to write a fourth sentence about
  it. **Standing rule: fold review findings back by proving more, never by
  softening prose.**

  **WHAT THE TRANSPORT ACTUALLY COSTS.** Less than the sentences did. Side one
  needs the observation that a reflection which fixes every point turns the
  reflected form into the energy, and the energy is positive definite because
  the Green function is — an argument that has nothing to do with boxes, so §1
  states it for an arbitrary graph and an arbitrary reflection, and
  `StrictCriterion`'s box-side-one proof becomes its two-line corollary. Side
  two on the torus needs `torus_two_eq_box`, which the estate has had since
  the torus was built. The estate's own `def` needs
  `LatticeNotStrict.reflectedForm_lattice_eq`, which was written for the
  not-strict direction and is an equality of forms, so it carries strictness
  with no change at all.

  WHAT THIS FILE PROVES:
  1. **`reflectedForm_eq_energy_of_id`** and **`reflectionPositive_of_refl_id`**
     — over an ARBITRARY graph, if the reflection fixes every vertex then the
     reflected form is the energy, hence strictly positive on every nonzero
     coefficient family, with no half and no support hypothesis. The
     generalisation of `StrictCriterion`'s side-one argument, which was stated
     for the box only.
  2. **`reflectionPositive_box_one_strict'`** — the box of side one re-derived
     from §1 in two lines, as the check that the generalisation really covers
     the case it was extracted from (ERRATUM 48).
  3. **`reflectionPositive_torus_one_strict`** — the torus of side one, which
     `MirrorStrict` recorded as omitted-by-choice.
  4. **`reflectedForm_torus_two_eq_box`** and
     **`reflectionPositive_torus_two_strict`** — the torus of side two, the
     case `MirrorStrict`'s summary counted and its theorem list did not have.
  5. **`reflectionPositive_lattice_one_strict`** and
     **`reflectionPositive_lattice_two_strict`** — the estate's own
     `LatticeReflection.ReflectionPositive` at the two sides
     `StrictCriterion` left unstated.

  **SO THE TORUS IS NOW SETTLED AT EVERY SIDE, INCLUDING ONE**: strict at one,
  two, three and four; not strict at five and up (`OddNotStrictInstances` for
  odd, `TorusNotStrict` for even). And the estate's own `def` is settled at
  every side: strict at one and two, not strict at three and up
  (`OddNotStrictInstances`, `LatticeNotStrict`). Three graph families, every
  side length, no case open and no case behind the word *transport*.

  WHAT THIS DOES NOT DO.
  * **It introduces no mechanism.** §1 is a generalisation of an argument the
    estate already had and §§2–4 are transports along equalities the estate
    already had. The value is that four statements which existed only as
    promises are now theorems; nothing here was hard and the file does not
    pretend otherwise.
  * **It does not settle the second-coordinate cut for the estate's `def`.**
    That `def` hardcodes `LatticeReflection.refl n`, the first-coordinate
    reflection, and the obstruction is the same one `LatticeNotStrict` records:
    the second-direction statement lives only in the general graph vocabulary.
    Unchanged by this file.
  * **It does not describe the null space anywhere.** Unchanged from
    `BoxOddNotStrict`; strictness at the small sides says the null space is
    trivial there, which is the whole content, but at the large sides only a
    subspace of it is exhibited.

    **SUPERSEDED IN PART, 25 AUG 2026.** The trailing clause was a claim about
    the estate and is now false in three of its four cases. The null space is
    described EXACTLY at large sides by `NullSpace.nullSpace_box_odd`,
    `NullSpaceEven.nullSpace_box_even` and `NullSpaceTorus.nullSpace_torus_even`,
    each with the matching `mem_nullSub_iff_…` submodule identity and a
    dimension (`NullSpaceDimension`, `NullSpaceDimensionEven`,
    `NullSpaceTorus.finrank_nullSub_torus_even`). **The one case where the
    clause still holds as written is the ODD TORUS**: `OddNotStrictInstances`
    exhibits a null direction at odd side and nothing describes the space it
    lies in. That is now the only lattice-and-parity combination in this group
    without an exact description, and naming it is the point of amending this
    bullet rather than deleting it.

    **And the threshold this file's summary transports is now reached from the
    other end too.** `NullSpaceTorus.null_trivial_iff_side_le_four` proves the
    even torus nondegenerate on the half exactly for `n ≤ 4`, from the dimension
    of the null space rather than from strictness on the box. The two routes
    share no argument; they agree.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import ReachCriterion

namespace SmallSideStrict

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. A reflection that fixes everything

`StrictCriterion.reflectionPositive_box_one_strict` proves this for
`boxGraph d 1`, where the reflection is the identity because `Fin.rev` on
`Fin 1` has nowhere to send its only element. The graph plays no part in the
argument, so it should not appear in the hypotheses.
-/

/-- If the reflection fixes every vertex, the reflected form IS the energy.
    No half, no parity, no hypothesis on the graph. -/
theorem reflectedForm_eq_energy_of_id (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)
    {θ : V ≃ V} (hθ : ∀ p, θ p = p) (c : V → ℝ) :
    GraphReflection.reflectedForm G m θ c = GraphReflection.energy G m c := by
  simp only [GraphReflection.reflectedForm, GraphReflection.energy, GraphReflection.bil]
  exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by rw [hθ p]

/-- **A REFLECTION THAT FIXES EVERY VERTEX IS STRICT**, over an arbitrary
    graph and for every nonzero coefficient family — no support condition,
    because there is no cut to be on one side of. The Green function is
    positive definite and the reflected form is its quadratic form. -/
theorem reflectionPositive_of_refl_id (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℝ}
    (hm : m ≠ 0) {θ : V ≃ V} (hθ : ∀ p, θ p = p) {c : V → ℝ} (hc0 : c ≠ 0) :
    0 < GraphReflection.reflectedForm G m θ c := by
  classical
  rw [reflectedForm_eq_energy_of_id G m hθ, GraphMirrorReflection.energy_eq_dotProduct]
  have := (Matrix.posDef_iff_dotProduct_mulVec.mp (GraphLaplacian.green_posDef G hm)).2 hc0
  simpa [dotProduct_comm] using this

/-! ## 2. Side one, on both graph families

`StrictCriterion.revSite_one_eq_id` says the site reflection is the identity
at side one; it is a statement about `Fin 1`, not about the box, so it applies
to the torus unchanged.
-/

variable {d : ℕ}

/-- The box of side one, re-derived from §1. `StrictCriterion` proves this
    already; it is repeated here as the check that the generalisation covers
    the case it was extracted from, and the two-line proof is the evidence
    that §1 is the right statement (ERRATUM 48). -/
theorem reflectionPositive_box_one_strict' (i : Fin d) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d 1 → ℝ} (hc0 : c ≠ 0) :
    0 < GraphReflection.reflectedForm (boxGraph d 1) m
          (GraphReflection.revSite (n := 1) i) c :=
  reflectionPositive_of_refl_id _ hm (StrictCriterion.revSite_one_eq_id i) hc0

/-- **THE TORUS OF SIDE ONE IS STRICT.** `MirrorStrict` recorded this as
    omitted by choice rather than unknown; the choice is now unnecessary. -/
theorem reflectionPositive_torus_one_strict (i : Fin d) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d 1 → ℝ} (hc0 : c ≠ 0) :
    0 < GraphReflection.reflectedForm (TorusReflection.torusGraph d 1) m
          (GraphReflection.revSite (n := 1) i) c :=
  reflectionPositive_of_refl_id _ hm (StrictCriterion.revSite_one_eq_id i) hc0

/-! ## 3. Side two on the torus

`TorusReflection.torus_two_eq_box` says the two-site circle collapses: the two
bonds joining the same pair are one edge of a `SimpleGraph`. The equality is
between graphs, and the decidability instances on the two sides are not
syntactically the same, so the transport goes through `sum_green_congr` at the
identity equivalence rather than through `rw`.
-/

/-- The reflected form on the torus of side two is the box's. -/
theorem reflectedForm_torus_two_eq_box (i : Fin d) (m : ℝ) (c : BoxGraph.Site d 2 → ℝ) :
    GraphReflection.reflectedForm (TorusReflection.torusGraph d 2) m
        (GraphReflection.revSite (n := 2) i) c
      = GraphReflection.reflectedForm (boxGraph d 2) m
          (GraphReflection.revSite (n := 2) i) c :=
  LatticeReflectionPositive.sum_green_congr
    (G := boxGraph d 2) (G' := TorusReflection.torusGraph d 2)
    (Equiv.refl (BoxGraph.Site d 2))
    (fun p q => iff_of_eq (congrFun (congrFun
      (congrArg SimpleGraph.Adj (TorusReflection.torus_two_eq_box d)) p) q))
    (θ := GraphReflection.revSite (n := 2) i)
    (θ' := GraphReflection.revSite (n := 2) i) (fun _ => rfl) m c

/-- **THE TORUS OF SIDE TWO IS STRICT.** The case `MirrorStrict`'s summary
    counted among the settled ones and its theorem list did not contain. -/
theorem reflectionPositive_torus_two_strict (i : Fin d) {m : ℝ} (hm : m ≠ 0)
    {c : BoxGraph.Site d 2 → ℝ} (hc0 : c ≠ 0)
    (hcsupp : ∀ p, p ∉ lowerHalf i 2 → c p = 0) :
    0 < GraphReflection.reflectedForm (TorusReflection.torusGraph d 2) m
          (GraphReflection.revSite (n := 2) i) c := by
  rw [reflectedForm_torus_two_eq_box i m c]
  exact StrictCriterion.reflectionPositive_box_two_strict i hm hc0 hcsupp

/-! ## 4. The estate's own definition at the small sides

`LatticeNotStrict.reflectedForm_lattice_eq` was written to carry a vanishing
across. It is an equality of forms, so it carries a strict positivity across
with no change; the only work is turning the support condition around, and
`map_lowerHalf` does that.
-/

section Lattice

open IsingFiniteVolume LatticeReflectionPositive

variable {n : ℕ}

/-- Transport of the two side conditions: a family on the estate's box that is
    nonzero and supported on `lowerHalfPair` pulls back to a family on the
    general box that is nonzero and supported on `lowerHalf`. -/
theorem pullback_conditions {c : IsingFiniteVolume.Site n → ℝ} (hc0 : c ≠ 0)
    (hcsupp : ∀ p, p ∉ lowerHalfPair n → c p = 0) :
    (fun p => c (sitePair n p)) ≠ 0 ∧
      ∀ p, p ∉ lowerHalf (0 : Fin 2) n → c (sitePair n p) = 0 := by
  classical
  constructor
  · intro hzero
    refine hc0 (funext fun q => ?_)
    have := congrFun hzero ((sitePair n).symm q)
    rwa [Equiv.apply_symm_apply] at this
  · intro p hp
    refine hcsupp _ fun hmem => hp ?_
    rw [← map_lowerHalf n] at hmem
    obtain ⟨p', hp', hpp'⟩ := Finset.mem_map.mp hmem
    have : p' = p := (sitePair n).injective (by simpa using hpp')
    exact this ▸ hp'

/-- **THE ESTATE'S OWN `def` IS STRICT AT SIDE ONE.** No support hypothesis is
    needed: at side one the reflection fixes everything, so §1 applies through
    the transport and there is no cut. -/
theorem reflectionPositive_lattice_one_strict {m : ℝ} (hm : m ≠ 0)
    {c : IsingFiniteVolume.Site 1 → ℝ} (hc0 : c ≠ 0) :
    0 < GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph 1) m
          (LatticeReflection.refl 1) c := by
  classical
  rw [LatticeNotStrict.reflectedForm_lattice_eq (m := m) c]
  refine reflectionPositive_box_one_strict' (0 : Fin 2) hm ?_
  intro hzero
  refine hc0 (funext fun q => ?_)
  have := congrFun hzero ((sitePair 1).symm q)
  rwa [Equiv.apply_symm_apply] at this

/-- **AND AT SIDE TWO**, where the cut is real and the support hypothesis is
    the estate's own `lowerHalfPair`. -/
theorem reflectionPositive_lattice_two_strict {m : ℝ} (hm : m ≠ 0)
    {c : IsingFiniteVolume.Site 2 → ℝ} (hc0 : c ≠ 0)
    (hcsupp : ∀ p, p ∉ lowerHalfPair 2 → c p = 0) :
    0 < GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph 2) m
          (LatticeReflection.refl 2) c := by
  classical
  rw [LatticeNotStrict.reflectedForm_lattice_eq (m := m) c]
  obtain ⟨hne, hsupp⟩ := pullback_conditions hc0 hcsupp
  exact StrictCriterion.reflectionPositive_box_two_strict (0 : Fin 2) hm hne hsupp

end Lattice

/-! ## 5. Review — the ways this could be hollow

**"Is this padding? Four theorems, none of them hard."** The test is not
whether a unit was hard but whether the estate says something it did not say
before. Before this file, `MirrorStrict`'s summary asserted the torus was
settled from side two while its theorem list stopped at three, and a reader
checking that summary against the declarations would have found the gap.
After it, the summary is true. **A register that over-reports by one case is
the exact failure ERRATUM 55 is about**, and the response the standing rule
demands is to make the register true by proving, not by editing it down.

**"Was the gap real, or is `reflectedForm_torus_two_eq_box` a restatement of
`torus_two_eq_box`?"** Real, and the proof shows why: the equality of graphs
does not rewrite inside `reflectedForm`, because the decidability instance is
part of the term and the two instances are not syntactically equal. The
transport has to go through `sum_green_congr`. That is small, but it is not
nothing, and "by transport" was doing the work of hiding it.

**"Does §1 subsume `StrictCriterion`'s side-one theorem, and if so why is that
one still there?"** It subsumes the argument, not the statement — §2 re-proves
the box case from §1 in two lines precisely to check that (ERRATUM 48). The
original is left standing because a pushed theorem is a record, and because
deleting it would silently change what a file that has been reviewed says.

**"Is the torus really settled at every side now?"** Strict at one (§2), two
(§3), three and four (`MirrorStrict`); not strict at odd sides five and up
(`OddNotStrictInstances.not_strict_torus_odd`) and even sides six and up
(`TorusNotStrict.not_strict_torus`). Every natural number at least one is in
exactly one of those lists. Side zero is checked rather than waved past: every
statement on this wall needs a direction `i : Fin d`, so `d ≥ 1`, and then
`Site d 0 = (Fin d → Fin 0)` is empty, the only coefficient family is the zero
one, and `c ≠ 0` is unsatisfiable — the statements are vacuous there, which is
not the same thing as absent and is why the sentence names the reason.

**"And the estate's own `def`?"** Strict at one and two (§4); not strict at
three and up — odd by `OddNotStrictInstances.not_strict_lattice_odd`, even by
`LatticeNotStrict.not_strict_lattice`. Also complete.
-/

end SmallSideStrict
