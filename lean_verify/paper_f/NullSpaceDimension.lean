/-
  NullSpaceDimension.lean — how big the null space is, at the one side length
  where the question has a clean answer.

  WHY. `NullSpace` closed the shape question — every null direction is the
  massive operator applied to something on the half — and its own
  WHAT-THIS-DOES-NOT-DO section says: *"It does not compute a dimension. The
  null space is characterised as a massive image of an isotropic cone; how big
  that cone is depends on the graph."* The watchlist says the same thing in two
  places. **Scope of that claim, since it is an absence claim** (ERRATUM 76):
  `paper_f` was searched by shape for "not compute a dimension", "no
  dimension", "dimension is not" and "dimension of the null", and
  `NullSpace.lean:83` is the only hit. Nothing outside `paper_f` was searched.

  **At the odd box the cone is everything, and there the dimension is exactly
  computable.**

  **WHY ODD SIDE AND NOWHERE ELSE.** The characterisation makes the null set
  the image of `{v on the half : crossForm v = 0}`. An isotropic cone is not a
  subspace in general, so "the null space" is not even a vector space in
  general — a fact this file states rather than skirts, and the reason no
  general dimension statement is attempted. At odd side the coupling vanishes
  identically (`crossForm_odd_eq_zero`), so the cone is the whole half, the
  image is a genuine subspace, and its dimension is the half's.

  **THE ANSWER.** The null space is linearly isomorphic to the functions on
  `strictLower` — the sites STRICTLY below the midline, not the sites of the
  lower half. The midline layer contributes nothing, which is the same fact
  `BoxOddNotStrict` observed geometrically (a null direction must charge the
  mirror, and the mirror is where the operator's reach lands) now stated as a
  dimension count. The isomorphism is the massive operator itself, and it is
  injective because the operator is positive definite; nothing subtler is
  involved.

  WHAT THIS FILE PROVES:
  1. **`supportedOn`** and **`finrank_supportedOn`** — the functions vanishing
     off a `Finset`, as a submodule, with dimension its cardinality. General
     linear algebra with no reflection content; stated because the estate did
     not have it and the dimension count is otherwise unavailable.
  2. **`massive_mulVecLin_injective`** — the massive operator as an injective
     linear map. `StrictBiconditional.massive_mulVec_ne_zero` in the form the
     rank-nullity machinery consumes.
  3. **`nullSub`** — the massive image of the functions on a half, as a
     submodule of coefficient families.
  4. **`mem_nullSub_iff_box_odd`** — at odd side that submodule is EXACTLY the
     set of admissible families with vanishing reflected form. Both
     containments, so it is the null space and not merely inside it.
  5. **`finrank_nullSub_box_odd`** — **its dimension is the number of sites
     strictly below the midline.** The count `NullSpace` and the watchlist both
     say is not available. **It does not need the side to be odd**: the image
     of an injective map has the domain's dimension whatever the graph, and
     oddness enters only in §3, where the image is identified WITH the null
     space. The name records where it is used, not what it needs.
  6. **`nullSub_lt_admissible_box_odd`** — and that is strictly less than the
     dimension of the admissible families, so the form is degenerate without
     being trivial. Degeneracy with a measured deficiency rather than a
     one-line "not strict".

  WHAT THIS DOES NOT DO.
  * **No closed form for the cardinality.** `(strictLower i n).card` is left
    as it stands. A fibre decomposition over the cut coordinate would give one
    — the count has no mathematical content and nothing in the estate consumes
    it — and **no formula is asserted here, not even parenthetically.** An
    arithmetic expression written into a header is a claim like any other, and
    an unverified one would be exactly what ERRATA 63 and 74 are about.
  * **Nothing at even side, and not from laziness.** There the coupling does
    not vanish, the isotropic cone is a genuine quadric, and the null set need
    not be a subspace at all — so `finrank` is the wrong question and this file
    does not ask it. What replaces it is the criterion in
    `StrictBiconditional`, which does not need linearity.
  * **Nothing for the torus.** Same cause: its coupling is diagonal rather
    than zero at every side length (`ReachIsCoupling`), so the cone is a
    proper quadric there too.
  * Still one axiom, free field, finite graph.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import StrictBiconditional

namespace NullSpaceDimension

open Finset Matrix BoxGraph GraphHalfSpace GraphLaplacian GraphReflection
open GraphMirrorReflection BoxOddReflection

section Supported

variable {V : Type*}

/-! ## 1. Functions supported on a finite set

General linear algebra. The estate has the predicate everywhere as a bare
`∀ p, p ∉ H → v p = 0` and has never needed it bundled; a dimension count
needs it bundled.
-/

/-- The functions vanishing off `H`, as a submodule. -/
def supportedOn (H : Finset V) : Submodule ℝ (V → ℝ) where
  carrier := {v | ∀ p, p ∉ H → v p = 0}
  add_mem' := by intro u v hu hv p hp; simp [hu p hp, hv p hp]
  zero_mem' := by intro p _; rfl
  smul_mem' := by intro c v hv p hp; simp [hv p hp]

@[simp] theorem mem_supportedOn {H : Finset V} {v : V → ℝ} :
    v ∈ supportedOn H ↔ ∀ p, p ∉ H → v p = 0 := Iff.rfl

open scoped Classical in
/-- Restriction to `H` is a linear isomorphism onto the functions on `H`.
    Classical decidability is used for the extension by zero, so that neither
    `Fintype V` nor `DecidableEq V` appears in §1's statements — the section is
    general linear algebra and should not carry the wall's instances. -/
noncomputable def supportedOnEquiv (H : Finset V) : supportedOn H ≃ₗ[ℝ] (H → ℝ) where
  toFun v := fun p => (v : V → ℝ) ↑p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun w := ⟨fun p => if h : p ∈ H then w ⟨p, h⟩ else 0, by
    intro p hp; exact dif_neg hp⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext p
    dsimp only
    by_cases hp : p ∈ H
    · rw [dif_pos hp]
    · rw [dif_neg hp]
      exact ((v.2) p hp).symm
  right_inv := by
    intro w
    ext p
    exact dif_pos p.2

/-- **THE DIMENSION OF THE SUPPORTED FUNCTIONS IS THE SIZE OF THE SUPPORT.** -/
theorem finrank_supportedOn (H : Finset V) :
    Module.finrank ℝ (supportedOn H) = H.card := by
  rw [(supportedOnEquiv H).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe]

end Supported

/-! ## 2. The massive operator as an injective map -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

theorem massive_mulVecLin_injective (hm : m ≠ 0) :
    Function.Injective (Matrix.mulVecLin (GraphLaplacian.massive G m)) := by
  intro a b hab
  by_contra hne
  have hsub : a - b ≠ 0 := sub_ne_zero_of_ne hne
  refine StrictBiconditional.massive_mulVec_ne_zero (G := G) hm hsub ?_
  have : GraphLaplacian.massive G m *ᵥ a = GraphLaplacian.massive G m *ᵥ b := by
    simpa using hab
  rw [Matrix.mulVec_sub, this, sub_self]

/-- The massive image of the functions on a half. -/
noncomputable def nullSub (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (H : Finset V) :
    Submodule ℝ (V → ℝ) :=
  (supportedOn H).map (Matrix.mulVecLin (GraphLaplacian.massive G m))

theorem mem_nullSub {H : Finset V} {c : V → ℝ} :
    c ∈ nullSub G m H ↔ ∃ v : V → ℝ, (∀ p, p ∉ H → v p = 0)
      ∧ GraphLaplacian.massive G m *ᵥ v = c := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

/-! ## 3. At odd side it is exactly the null space

`NullSpace.nullSpace_box_odd` gives one containment; the support lemma from
`BoxOddNotStrict` gives the other, and without it the image could in principle
contain families the reflected form is not even defined on as admissible.
-/

section OddBox

variable {d n : ℕ}

/-- **THE MASSIVE IMAGE OF THE STRICT HALF IS THE NULL SPACE.** Both
    containments: everything in the image is admissible and null, and
    everything admissible and null is in the image. -/
theorem mem_nullSub_iff_box_odd (i : Fin d) (hn : Odd n) {m : ℝ} (hm : m ≠ 0)
    (c : BoxGraph.Site d n → ℝ) :
    c ∈ nullSub (boxGraph d n) m (strictLower i n)
      ↔ (∀ p, p ∉ lowerHalf i n → c p = 0)
        ∧ GraphReflection.reflectedForm (boxGraph d n) m
            (GraphReflection.revSite (n := n) i) c = 0 := by
  classical
  constructor
  · intro hc
    obtain ⟨v, hvsupp, rfl⟩ := mem_nullSub.mp hc
    have hsupp := BoxOddNotStrict.massive_mulVec_supported i hn m hvsupp
    refine ⟨hsupp, ?_⟩
    exact (NullSpace.nullSpace_box_odd i hn hm hsupp).mpr ⟨v, hvsupp, rfl⟩
  · rintro ⟨hcsupp, hcform⟩
    exact mem_nullSub.mpr ((NullSpace.nullSpace_box_odd i hn hm hcsupp).mp hcform)

/-- **THE DIMENSION.** The null space of the reflected form on the odd box has
    dimension exactly the number of sites STRICTLY below the midline. The
    midline layer contributes nothing — the same fact `BoxOddNotStrict`
    observed geometrically, as a count. -/
theorem finrank_nullSub_box_odd (i : Fin d) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (strictLower i n))
      = (strictLower i n).card := by
  have hinj := massive_mulVecLin_injective (G := boxGraph d n) (m := m) hm
  have hequiv := Submodule.equivMapOfInjective _ hinj (supportedOn (strictLower i n))
  rw [nullSub, ← hequiv.finrank_eq, finrank_supportedOn]

/-- **AND IT IS STRICTLY SMALLER THAN THE ADMISSIBLE FAMILIES.** The form is
    degenerate, and this says by how much: the deficiency is exactly the
    midline layer, which is nonempty at odd side. Degeneracy with a measured
    codimension rather than a bare "not strict". -/
theorem nullSub_lt_admissible_box_odd (i : Fin d) (hn : Odd n) {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (nullSub (boxGraph d n) m (strictLower i n))
      < Module.finrank ℝ (supportedOn (lowerHalf i n)) := by
  classical
  rw [finrank_nullSub_box_odd i hm, finrank_supportedOn]
  refine Finset.card_lt_card ?_
  constructor
  · intro p hp
    rw [lowerHalf_eq_union]
    exact Finset.mem_union_left _ hp
  · intro hsub
    obtain ⟨k, hk⟩ := hn
    set p₀ : BoxGraph.Site d n := fun _ => ⟨k, by omega⟩ with hp₀
    have hmid : p₀ ∈ midLayer i n := by
      rw [mem_midLayer]; simp [hp₀]; omega
    have hlow : p₀ ∈ lowerHalf i n := by
      rw [lowerHalf_eq_union]; exact Finset.mem_union_right _ hmid
    have := hsub hlow
    rw [mem_strictLower] at this
    simp [hp₀] at this
    omega

end OddBox

/-! ## 4. Review — the ways this could be hollow

**"Is `nullSub` the null space, or a submodule that happens to sit inside
it?"** The null space, and §3 proves both containments rather than one. The
easy direction is that everything in the image is null; the direction that
needed `NullSpace` is that everything null is in the image. **A file proving
only the first would have computed the dimension of something smaller and
called it the answer**, which is exactly the failure `NullSpace` was written to
fix, one level up.

**"Why is the answer `strictLower` and not `lowerHalf`?"** Because the operator
is applied to something on the strict half and lands one step further, on the
midline. So the null space is parametrised by the strict half while living on
the whole lower half — and the count is the parametrising set, not the
containing one. That is not an artefact of the proof; it is the same asymmetry
`BoxOddNotStrict` recorded as "every null direction charges the mirror", and
seeing the two agree is the check that neither is a slip.

**"Is the strict inequality in §3 doing work, or is it decoration?"** Work: it
is what distinguishes "the form is degenerate" from "the form is zero". A
reader who knew only that the form is not strict could not tell those apart,
and at odd side the deficiency is exactly one layer — the midline — which is
nonempty precisely because the side is odd. The witness is the constant site at
coordinate `k` where `n = 2k+1`.

**"Why no general dimension theorem?"** Because there is no general dimension.
`StrictBiconditional` says the null set is the massive image of the coupling's
isotropic cone, and a cone is not a subspace unless the form vanishes on it
identically. **At odd side that happens; at even side and on the torus it does
not**, and asking for a `finrank` there is asking the wrong question rather
than a hard one. The header says this and the file attempts nothing there.

**"Does the dimension theorem need odd side?"** No, and saying so is a
strengthening rather than a caveat. `finrank_nullSub_box_odd` computes the
dimension of the massive image of the supported functions, and an injective
linear map carries dimension whatever the graph or side length. **Oddness
enters only in §3**, where that image is shown to BE the null space. At even
side the image is still a subspace of the same dimension — it is simply no
longer all of the null set, so the number stops answering the question that was
asked.

**"Is `finrank_supportedOn` worth stating separately?"** It is pure linear
algebra with no reflection content, it was not in the estate, and Mathlib
states the corresponding fact for `Finsupp.supported` rather than for functions
on a `Fintype` vanishing off a `Finset`. Two routes were available — transport
through `Finsupp` or build the restriction equivalence directly — and the
direct one is shorter than the transport.
-/

end NullSpaceDimension
