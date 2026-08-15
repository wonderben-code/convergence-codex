import LorentzOrthochronousSign
import LorentzIsometryEquiv
import PinImage
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Connected.Clopen

/-!
# The last residue of the Lorentz-group watchlist item: one inclusion, and what the other needs

`UNLOCK_WATCHLIST`'s entry *"the O(1,3)/SO⁺(1,3) groups as MATHLIB-STYLE objects"* has been down
to a single residue since 1 Aug 2026, restated unchanged at every re-sweep since:

> **What is left is the identity-component identification** — the only topological statement in
> this neighbourhood, and it still has no consumer.

**This file does not close it.** What it does is split that one sentence into two inclusions,
prove one of them outright, and reduce the other to a statement that is not about the Lorentz
group at all.

## What is proved here

Write `Splus` for SO⁺(1,3) viewed as a subgroup of the *group* O(1,3) (rather than of GL₄(ℝ)),
and give O(1,3) the subspace topology it inherits from GL₄(ℝ).

1. **`isClopen_detPos` and `isClopen_chron` — each of the two defining conditions is
   *separately* open and closed in O(1,3).** Open because `det` and the entry `Λ⁰₀` are
   continuous and each condition reads `0 < ·`; closed because on O(1,3) neither quantity can
   vanish — `det Λ = ±1` (`PinImage.det_sq_of_isLorentz`) and `Λ⁰₀ ≠ 0`
   (`LorentzOrthochronousSign.zero_zero_ne_zero`) — so each complement is again a strict
   inequality and so again open.
2. **`isClopen_Splus` — hence SO⁺(1,3) is clopen in O(1,3)**, being their intersection, and
   **`connectedComponentOfOne_le` — the identity component of O(1,3) is contained in
   SO⁺(1,3)**, since a connected set meeting a clopen set lies inside it. That is one of the
   two inclusions the identification asserts.
3. **`four_components` — O(1,3) has at least four connected components**, exhibited: `1`, the
   Gram matrix (`LorentzIsometryEquiv.gramO13`, improper and orthochronous), `−I` (proper and
   antichronous) and their product (improper and antichronous) lie in six-fold pairwise
   distinct components. `not_preconnectedSpace_O13` follows. This is what makes the
   identification a statement with content rather than a triviality.
4. **`eq_of_isPreconnected` — the identification, conditional on the missing half.** If
   SO⁺(1,3) is preconnected then it *is* the identity component.

**A draft of item 1 said instead that "both discrete invariants are needed: dropping either one
leaves a set that is open but not closed". That is false**, and item 3 is the correction carried
out by proving rather than by rewording: each invariant is separately clopen, which is exactly
why their intersection is, and why the group falls into four pieces rather than two. The false
sentence was written from the intuition that an intersection is where clopen-ness comes from;
the file says the opposite.

## What is not proved, and where the remaining leg goes

**SUPERSEDED IN ITS CONCLUSION, 15 AUG 2026, AND KEPT RATHER THAN REWRITTEN.** The missing half
below was supplied the same afternoon: `LorentzConnectedReduction` reduced it to connectedness of
SL₂(ℂ), `SL2Connected` proved that, and `SL2Connected.identityComponent_eq` states the
identification **unconditionally**. `eq_of_isPreconnected` here keeps its hypothesis and stays as
the conditional form; nothing in this file changed. The paragraphs below are the state of play on
the morning of 15 August and are left standing as that.

**The missing half is that SO⁺(1,3) is connected**, and nothing here bears on it.

The honest reduction, and the only part of this that the last month of work changed: because
`LorentzSurjectivity.SOplus13_surjective` now proves SL₂(ℂ) → SO⁺(1,3) *onto*, SO⁺(1,3) is the
image of SL₂(ℂ), so its preconnectedness would follow from

* continuity of `LorentzGroup.lorentzMat` as a map of matrix entries — not attempted here, and
  a real if unexciting computation, the entries being real quadratic polynomials in the real
  and imaginary parts of `A`; and
* **connectedness of SL₂(ℂ)**, which is *not in this Mathlib*: probed 15 Aug 2026 by
  `grep -rn` over `.lake/packages/mathlib/Mathlib/ --include=*.lean` for the three patterns
  `ConnectedSpace.*SpecialLinearGroup`, `SpecialLinearGroup.*Connected` and
  `PathConnected.*SpecialLinear`, zero matches between them.

`LorentzGroup` §5 already recorded that second gap, from the other direction, when it proved
`det Λ(A) = 1` by an algebraic route: *"The usual proof that the image is proper is topological:
det Λ is continuous, valued in {±1}, and SL₂(ℂ) is connected. That argument is not available
here, and it is not needed."* It is the same missing fact, and here it *is* needed.

**Do not read item 2 as progress caused by the surjectivity closure.** The clopen argument uses
nothing beyond the Gram identity and was available on the day `O13` was defined; it went
unwritten because the watchlist item recorded — correctly — that nothing downstream wanted it.
What the surjectivity closure changed is only the *shape of the remaining half*: before it, the
missing statement was "SO⁺(1,3) is connected" with no route; after it, that statement reduces to
a fact about SL₂(ℂ) with the Lorentz group eliminated.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LorentzIdentityComponent

open Matrix LorentzGroup Set

/-! ## 1. O(1,3) as a topological group, and the matrix behind an element of it -/

/-- The underlying real matrix of an element of the subgroup `O13`. -/
def mat (M : O13) : Matrix (Fin 4) (Fin 4) ℝ :=
  ((M : Matrix.GeneralLinearGroup (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ)

theorem isLorentz_mat (M : O13) : IsLorentzMat (mat M) := M.2

theorem continuous_mat : Continuous (mat) :=
  (by fun_prop :
      Continuous fun M : Matrix.GeneralLinearGroup (Fin 4) ℝ =>
        (M : Matrix (Fin 4) (Fin 4) ℝ)).comp continuous_subtype_val

theorem continuous_det : Continuous fun M : O13 => (mat M).det :=
  continuous_mat.matrix_det

theorem continuous_entry (i j : Fin 4) : Continuous fun M : O13 => mat M i j :=
  continuous_mat.matrix_elem i j

/-! ## 2. SO⁺(1,3) inside O(1,3), and its two defining conditions as sign conditions

The subgroup is *defined* by `det = 1` and `0 < Λ⁰₀`. The first is an equality and so is not an
open condition on its face; the point of `mem_Splus` is that on O(1,3) it is equivalent to the
open condition `0 < det`, because `det` is confined to `{±1}` there.
-/

/-- SO⁺(1,3) as a subgroup of the group O(1,3), rather than of GL₄(ℝ). -/
def Splus : Subgroup O13 := SOplus13.subgroupOf O13

theorem mem_Splus_iff {M : O13} :
    M ∈ Splus ↔ (M : Matrix.GeneralLinearGroup (Fin 4) ℝ) ∈ SOplus13 :=
  Subgroup.mem_subgroupOf

/-- **Both defining conditions read as strict sign conditions.** -/
theorem mem_Splus {M : O13} : M ∈ Splus ↔ 0 < (mat M).det ∧ 0 < mat M 0 0 := by
  rw [mem_Splus_iff]
  constructor
  · rintro ⟨-, hd, h0⟩
    exact ⟨by rw [show (mat M).det = 1 from hd]; norm_num, h0⟩
  · rintro ⟨hd, h0⟩
    have hsq := PinImage.det_sq_of_isLorentz (isLorentz_mat M)
    have hfac : ((mat M).det - 1) * ((mat M).det + 1) = 0 := by nlinarith
    have hone : (mat M).det = 1 := by
      rcases mul_eq_zero.mp hfac with h | h <;> linarith
    exact ⟨isLorentz_mat M, hone, h0⟩

/-- The complement, also as strict sign conditions. This is the half that uses that **neither**
`det` nor `Λ⁰₀` can vanish on a Lorentz matrix. -/
theorem not_mem_Splus {M : O13} : M ∉ Splus ↔ (mat M).det < 0 ∨ mat M 0 0 < 0 := by
  have hd : (mat M).det ≠ 0 := by
    intro h0
    have hsq := PinImage.det_sq_of_isLorentz (isLorentz_mat M)
    rw [h0] at hsq; norm_num at hsq
  have h0 : mat M 0 0 ≠ 0 :=
    LorentzOrthochronousSign.zero_zero_ne_zero (isLorentz_mat M)
  rw [mem_Splus, not_and_or, not_lt, not_lt]
  constructor
  · rintro (h | h)
    · exact Or.inl (lt_of_le_of_ne h hd)
    · exact Or.inr (lt_of_le_of_ne h h0)
  · rintro (h | h)
    · exact Or.inl h.le
    · exact Or.inr h.le

/-! ## 3. Each sign condition is separately clopen

This is the load-bearing step, and it is stronger than the clopen-ness of the intersection: the
*two* invariants are independently locally constant, which is why O(1,3) has four pieces below
and not two.
-/

theorem det_ne_zero (M : O13) : (mat M).det ≠ 0 := by
  intro h0
  have hsq := PinImage.det_sq_of_isLorentz (isLorentz_mat M)
  rw [h0] at hsq; norm_num at hsq

/-- **PROPERNESS IS LOCALLY CONSTANT.** -/
theorem isClopen_detPos : IsClopen {M : O13 | 0 < (mat M).det} := by
  refine ⟨?_, isOpen_lt continuous_const continuous_det⟩
  rw [← isOpen_compl_iff]
  have hset : {M : O13 | 0 < (mat M).det}ᶜ = {M : O13 | (mat M).det < 0} := by
    ext M
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (det_ne_zero M), fun h => h.le⟩
  rw [hset]
  exact isOpen_lt continuous_det continuous_const

/-- **ORTHOCHRONICITY IS LOCALLY CONSTANT.** -/
theorem isClopen_chron : IsClopen {M : O13 | 0 < mat M 0 0} := by
  refine ⟨?_, isOpen_lt continuous_const (continuous_entry 0 0)⟩
  rw [← isOpen_compl_iff]
  have hset : {M : O13 | 0 < mat M 0 0}ᶜ = {M : O13 | mat M 0 0 < 0} := by
    ext M
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h
      (LorentzOrthochronousSign.zero_zero_ne_zero (isLorentz_mat M)), fun h => h.le⟩
  rw [hset]
  exact isOpen_lt (continuous_entry 0 0) continuous_const

/-- **SO⁺(1,3) IS CLOPEN IN O(1,3)** — the intersection of the two. -/
theorem isClopen_Splus : IsClopen (Splus : Set O13) := by
  have hset : (Splus : Set O13)
      = {M : O13 | 0 < (mat M).det} ∩ {M : O13 | 0 < mat M 0 0} := by
    ext M; simpa using mem_Splus
  rw [hset]
  exact isClopen_detPos.inter isClopen_chron

/-! ## 4. The inclusion that follows, and the one that does not -/

/-- **ONE HALF OF THE IDENTIFICATION.** Every Lorentz transformation connected to the identity
is proper and orthochronous. -/
theorem connectedComponentOfOne_le : Subgroup.connectedComponentOfOne O13 ≤ Splus :=
  fun _ hM => isClopen_Splus.connectedComponent_subset Splus.one_mem hM

/-- **THE OTHER HALF, STATED AS THE HYPOTHESIS IT IS.** Nothing in this file proves the
hypothesis; see the header for what it reduces to. -/
theorem eq_of_isPreconnected (h : IsPreconnected (Splus : Set O13)) :
    Subgroup.connectedComponentOfOne O13 = Splus :=
  le_antisymm connectedComponentOfOne_le
    fun _ hM => h.subset_connectedComponent Splus.one_mem hM

/-! ## 5. Four occupied sign classes, hence four components

`sgn det` and `sgn Λ⁰₀` are two *independently* locally constant invariants by §3, so two Lorentz
transformations differing in either sign lie in different components. All four sign patterns are
occupied: the identity, the Gram matrix, `−I`, and their product.
-/

/-- `−I` as an element of O(1,3): proper, because the dimension is even, and antichronous. -/
def negOne : O13 :=
  ⟨-1, by
    change IsLorentzMat ((-1 : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ)
    rw [Units.val_neg, Units.val_one]
    exact LorentzOrthochronousSign.isLorentzMat_neg IsLorentzMat.one⟩

theorem mat_mul (M N : O13) : mat (M * N) = mat M * mat N := rfl

theorem mat_one : mat (1 : O13) = 1 := rfl

theorem mat_gramO13 : mat LorentzIsometryEquiv.gramO13 = gram := rfl

theorem mat_negOne : mat negOne = -1 := by
  simp only [mat, negOne, Units.val_neg, Units.val_one]

theorem det_negOne_matrix : (-1 : Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
  norm_num [Matrix.det_neg]

/-! ### The sign table -/

theorem det_one_pos : 0 < (mat (1 : O13)).det := by
  rw [mat_one, Matrix.det_one]; norm_num

theorem chron_one : 0 < mat (1 : O13) 0 0 := by
  rw [mat_one, Matrix.one_apply_eq]; norm_num

theorem det_gram_neg : (mat LorentzIsometryEquiv.gramO13).det < 0 := by
  rw [mat_gramO13, det_gram]; norm_num

theorem chron_gram : 0 < mat LorentzIsometryEquiv.gramO13 0 0 := by
  rw [mat_gramO13]; exact LorentzOrthochronousSign.gram_chron.2

theorem det_negOne_pos : 0 < (mat negOne).det := by
  rw [mat_negOne, det_negOne_matrix]; norm_num

theorem antichron_negOne : mat negOne 0 0 < 0 := by
  rw [mat_negOne]
  simp

theorem det_negGram_neg : (mat (negOne * LorentzIsometryEquiv.gramO13)).det < 0 := by
  rw [mat_mul, Matrix.det_mul, mat_negOne, mat_gramO13, det_negOne_matrix, det_gram]
  norm_num

theorem antichron_negGram : mat (negOne * LorentzIsometryEquiv.gramO13) 0 0 < 0 := by
  rw [mat_mul, mat_negOne, mat_gramO13, neg_one_mul,
    LorentzOrthochronousSign.neg_zero_zero]
  linarith [LorentzOrthochronousSign.gram_chron.2]

/-! ### Two elements differing in either sign are in different components -/

theorem connectedComponent_ne_of_det {M N : O13}
    (hM : 0 < (mat M).det) (hN : (mat N).det < 0) :
    connectedComponent M ≠ connectedComponent N := by
  intro h
  have hsub := isClopen_detPos.connectedComponent_subset hM
  rw [h] at hsub
  have hmem := hsub (mem_connectedComponent (x := N))
  simp only [Set.mem_setOf_eq] at hmem
  linarith

theorem connectedComponent_ne_of_chron {M N : O13}
    (hM : 0 < mat M 0 0) (hN : mat N 0 0 < 0) :
    connectedComponent M ≠ connectedComponent N := by
  intro h
  have hsub := isClopen_chron.connectedComponent_subset hM
  rw [h] at hsub
  have hmem := hsub (mem_connectedComponent (x := N))
  simp only [Set.mem_setOf_eq] at hmem
  linarith

/-- **O(1,3) HAS AT LEAST FOUR CONNECTED COMPONENTS**, all six pairs separated. -/
theorem four_components :
    connectedComponent (1 : O13) ≠ connectedComponent LorentzIsometryEquiv.gramO13
      ∧ connectedComponent (1 : O13) ≠ connectedComponent negOne
      ∧ connectedComponent (1 : O13)
          ≠ connectedComponent (negOne * LorentzIsometryEquiv.gramO13)
      ∧ connectedComponent LorentzIsometryEquiv.gramO13 ≠ connectedComponent negOne
      ∧ connectedComponent LorentzIsometryEquiv.gramO13
          ≠ connectedComponent (negOne * LorentzIsometryEquiv.gramO13)
      ∧ connectedComponent negOne
          ≠ connectedComponent (negOne * LorentzIsometryEquiv.gramO13) :=
  ⟨connectedComponent_ne_of_det det_one_pos det_gram_neg,
    connectedComponent_ne_of_chron chron_one antichron_negOne,
    connectedComponent_ne_of_det det_one_pos det_negGram_neg,
    (connectedComponent_ne_of_det det_negOne_pos det_gram_neg).symm,
    connectedComponent_ne_of_chron chron_gram antichron_negGram,
    connectedComponent_ne_of_det det_negOne_pos det_negGram_neg⟩

/-- **O(1,3) IS NOT CONNECTED.** -/
theorem not_preconnectedSpace_O13 : ¬ PreconnectedSpace O13 := by
  intro hcon
  rcases isClopen_iff.mp isClopen_detPos with hempty | huniv
  · have h1 : (1 : O13) ∈ {M : O13 | 0 < (mat M).det} := det_one_pos
    rw [hempty] at h1
    exact h1
  · have hg : LorentzIsometryEquiv.gramO13 ∈ {M : O13 | 0 < (mat M).det} := by
      rw [huniv]; trivial
    simp only [Set.mem_setOf_eq] at hg
    linarith [det_gram_neg]

theorem gramO13_not_mem_Splus : LorentzIsometryEquiv.gramO13 ∉ Splus := by
  rw [not_mem_Splus]
  exact Or.inl det_gram_neg

/-- And therefore the identity component is a **proper** subgroup of O(1,3): the two inclusions
of the identification are not both automatic. -/
theorem connectedComponentOfOne_ne_top :
    Subgroup.connectedComponentOfOne O13 ≠ ⊤ := by
  intro htop
  have hmem : LorentzIsometryEquiv.gramO13 ∈ Subgroup.connectedComponentOfOne O13 := by
    rw [htop]; trivial
  exact gramO13_not_mem_Splus (connectedComponentOfOne_le hmem)

end LorentzIdentityComponent
