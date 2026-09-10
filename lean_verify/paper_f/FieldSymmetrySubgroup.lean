import FieldBlockProduct

/-!
# The symmetries are a `Subgroup`, and the product decomposition is an isomorphism of groups

`FieldSymmetryGroup` proved the group law — `one_mem`, `mul_mem`, `transpose_mem` and
`mul_transpose_self` — and then said what it could not bundle: *`Matrix V V ℝ` is a monoid, so the
bundled object is a `Submonoid`, and `transpose_mem` with `mul_transpose_self` supply the inverses
on top of it.* `FieldLinearClassified` said it in the words *Still no `Subgroup` instance*,
`FieldBlockGroup` said *upgrading `conjEigEquiv` to a `Subgroup` isomorphism … is not done here*,
and `FieldBlockProduct` said *no `Subgroup` instance is built*. **This file bundles it.**

**`symmetrySubgroup`** is a `Subgroup (Matrix.unitaryGroup V ℝ)`. The choice of ambient group is
the content: every symmetry is orthogonal by definition, so the orthogonal group is where they
already live, and the ambient group supplies the inverse rather than a matrix inversion. That is
strictly better than the `Matrix.GeneralLinearGroup` route `FieldSymmetryInclusion.linSymGL` takes
for the LINEAR symmetries — which needs the bigger ambient precisely because a linear symmetry need
not be orthogonal — and it is why `inv_coe_eq_transpose` can say the group inverse **is** the
transpose rather than merely agreeing with it.

**`symmetrySubgroup_mulEquiv_prod`** then carries `FieldBlockProduct.symmetry_mulEquiv_prod` to the
subgroup: **the symmetry group of the Gaussian field is isomorphic, as a GROUP, to the product of
the orthogonal groups of the propagator's eigenspaces.** Both sides are now groups; before this
file the left-hand side was a monoid that happened to have inverses.

## What is NOT here

* **No cardinality**, unchanged and for the same reason: a factor with a block of size two is
  infinite, and `FieldTorusRotation.oneFreq` says the torus always has one.
  `FieldTorusRotation.infinite_symmetryMatrices_torus` remains the finest statement of size.
* **No claim that this is a `Subgroup` of `Matrix.GeneralLinearGroup`.** It is not built, and the
  inclusion into that group is `FieldSymmetryInclusion`'s subject rather than this file's.
* **No relation to `linSymGL` is proved here.** That the isometric and linear symmetry groups
  coincide exactly when the propagator is a scalar is
  `FieldSymmetryProper.symmetryMatrices_eq_linSym_iff`, and it is cited, not restated.
* **Nothing new about which graphs.** No graph is named; every statement is at an arbitrary finite
  graph with a non-zero mass, and the mass enters only where `eigMu` does.
* **No `Group` instance is put on `symmetrySubmonoid` itself.** A `Submonoid` of a monoid cannot
  carry one honestly; the equivalence `submonoidEquiv` is what relates the two objects, and a
  reader who wants the group should use `symmetrySubgroup`.

**No wall moves.** `W1`'s open part is still `OS0`, `OS4` and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[Fintype V]` and `[DecidableEq V]`
throughout. **`m ≠ 0` is taken by one declaration of the six**, `symmetrySubgroup_mulEquiv_prod`,
and only because `eigMu` and `conjEigEquiv` do. The other five — `mem_unitaryGroup_of_mem`,
`symmetrySubgroup`, `mem_symmetrySubgroup`, `inv_coe_eq_transpose` and `submonoidEquiv` — **take no
mass at all** and hold at every mass including zero, where they say the symmetries of the massless
field are a group too. `symmetrySubgroup` and `submonoidEquiv` bind `G`, `m` and
`[DecidableRel G.Adj]` explicitly because they are bundled objects; the four theorems take them
from the section.

**AND THIS PARAGRAPH'S FIRST DRAFT SAID *one declaration of the four* IN A FILE OF SIX.** It was
caught by `binder_scan.py` — written one unit earlier, for exactly this defect — before the file
was committed. Recorded here rather than quietly fixed, because a tool catching its author on the
very next unit is the only evidence that it works on live prose rather than on the two headers it
was validated against (`ERRATUM 488`). **A second self-catch, by hand this time**: the paragraph
above attributed *Still no `Subgroup` instance* to `FieldBlockGroup`, and it is
`FieldLinearClassified`'s sentence — found by grepping the estate for the quotation before
committing it, which is `ERRATUM 108`'s rule applied to a quotation rather than to a lemma name.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldSymmetrySubgroup

open Matrix GraphLaplacian FieldRotationCount FieldSymmetryGroup

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Every symmetry is unitary, so the orthogonal group is the right ambient -/

/-- A symmetry is orthogonal by definition, and over `ℝ` that is unitary. -/
theorem mem_unitaryGroup_of_mem {R : Matrix V V ℝ} (hR : R ∈ symmetryMatrices G m) :
    R ∈ Matrix.unitaryGroup V ℝ :=
  (FieldBlockProduct.mem_unitaryGroup_iff_transpose R).2 hR.1

/-- **THE SYMMETRIES OF THE GAUSSIAN FIELD AS A `Subgroup` OF THE ORTHOGONAL GROUP.** No hypothesis
on the mass: the inverse is supplied by the ambient group, and `FieldSymmetryGroup.transpose_mem`
is what puts it back in the carrier. -/
def symmetrySubgroup (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Subgroup (Matrix.unitaryGroup V ℝ) where
  carrier := {U | (U : Matrix V V ℝ) ∈ symmetryMatrices G m}
  one_mem' := one_mem
  mul_mem' ha hb := mul_mem ha hb
  inv_mem' {U} h := by
    have hstar : ((U⁻¹ : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ) = (U : Matrix V V ℝ)ᵀ := by
      rw [show ((U⁻¹ : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ)
        = star (U : Matrix V V ℝ) from rfl, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [Set.mem_setOf_eq, hstar]
    exact transpose_mem h

@[simp] theorem mem_symmetrySubgroup {U : Matrix.unitaryGroup V ℝ} :
    U ∈ symmetrySubgroup G m ↔ (U : Matrix V V ℝ) ∈ symmetryMatrices G m := Iff.rfl

/-- **THE GROUP INVERSE OF A SYMMETRY IS ITS TRANSPOSE**, not merely equal to it in the presence of
some hypothesis: this is the ambient group's inverse, computed. -/
theorem inv_coe_eq_transpose (U : Matrix.unitaryGroup V ℝ) :
    ((U⁻¹ : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ) = (U : Matrix V V ℝ)ᵀ := by
  rw [show ((U⁻¹ : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ) = star (U : Matrix V V ℝ) from rfl,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-! ## 2. The subgroup and the submonoid have the same elements -/

/-- **THE `Subgroup` AND `FieldSymmetryGroup`'s `Submonoid` ARE THE SAME MONOID.** So nothing this
estate proved about the `Submonoid` is lost, and the `Subgroup` is not a second, smaller object. -/
def submonoidEquiv (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    symmetrySubgroup G m ≃* symmetrySubmonoid G m where
  toFun U := ⟨((U : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ), U.2⟩
  invFun R := ⟨⟨R.1, mem_unitaryGroup_of_mem R.2⟩, R.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-! ## 3. The product decomposition, as an isomorphism of groups -/

open FieldBlockDiagonal FieldBlockProduct

/-- **THE SYMMETRY GROUP OF THE GAUSSIAN FIELD IS THE PRODUCT OF THE ORTHOGONAL GROUPS OF THE
PROPAGATOR'S EIGENSPACES**, one factor per distinct eigenvalue, as an isomorphism of GROUPS. The
factor at `c` has dimension `c`'s multiplicity by
`FieldBlockProduct.card_fib_eq_finrank_eigenspace`, and is non-trivial by
`FieldBlockProduct.fib_nonempty`. -/
noncomputable def symmetrySubgroup_mulEquiv_prod (hm : m ≠ 0) :
    symmetrySubgroup G m ≃*
      ∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ :=
  (submonoidEquiv G m).trans (symmetry_mulEquiv_prod hm)

end FieldSymmetrySubgroup
