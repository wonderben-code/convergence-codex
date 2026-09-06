import FieldSignGroup
import FieldSymmetryIso
import FieldRotationCount

/-!
# The two symmetry groups, related: the isometric ones are the orthogonal linear ones

`FieldSignGroup` closed with a fence: *this group is a **proper** subgroup of the linear symmetry
group, and **no relation between the two is drawn here** — no inclusion of `symmetriesSubgroup` into
`linSym`, and no index.* **The relation is drawn here, at the level of matrices.**

## What is proved

**`mem_linSym_iff_comm`** — for an **orthogonal** matrix, preserving the propagator's form and
commuting with the propagator are the same condition: `L C Lᵀ = C ↔ L C = C L`. Two calculations,
one each way, using `L Lᵀ = 1` from `mul_eq_one_comm`. **No hypothesis on the mass, and nothing
about `green` beyond its being a matrix.**

**`symmetryMatrices_eq`, `symmetryMatrices_subset_linSym`** — **THE ISOMETRIC SYMMETRIES ARE
EXACTLY THE ORTHOGONAL ELEMENTS OF THE LINEAR SYMMETRY GROUP.** `symmetryMatrices G m` is
`{L ∈ linSym G m | Lᵀ L = 1}`, so the inclusion is immediate.

**`symmetryMatrices_ssubset_linSym_line`** — **and on a line of at least two sites the inclusion is
STRICT**, by `FieldSqrtConjugation.exists_nonIsometric_line`, which produces a matrix satisfying
`L C Lᵀ = C` with `Lᵀ L ≠ 1`. The fence said *proper*; this is the `⊂`.

**`isUnit_det_of_mem_linSym`, `inv_mem_linSym`** — every linear symmetry is invertible, and its
inverse is one. Taking determinants of `L C Lᵀ = C` gives `det L · det C · det L = det C`, and
`det C ≠ 0` because `green` is positive definite.

**`coe_orthIsometry_eq_mvCLM`, `mem_linSym_iff_orthIsometry_map`** — `orthIsometry` and `mvCLM` are
**the same map**, both coercing to `RayleighMatrix.mv`, and **this estate had never said so**. That
`rfl` is why `FieldInvarianceCommutes`'s biconditional and `FieldSymmetryIso`'s read as statements
about different objects. With it, the second restates in the first's packaging in two lines.

**`linSymGL`, `mem_linSymGL`** — **`linSym` AS A `Subgroup`**, of `Matrix.GeneralLinearGroup V ℝ`.
`FieldSymmetryIso` fenced *no `Subgroup` instance is constructed*; here is one. **It takes no
hypothesis on the mass**, because the ambient group supplies the inverse — only the statement about
a bare *matrix* inverse (`inv_mem_linSym`) needs `green` invertible.

## WHAT THE NAME SCANNER FOUND, and why the proof kept here is the longer one

`newnames_scan` flagged this file's measure-level theorem against one written seven hours earlier.
Chasing it produced the `rfl` above and then a second fact: **`symmetryMatrices_eq` is derivable
from `FieldInvarianceCommutes.mem_symmetryMatrices_iff_gaussianField_map` and
`FieldSymmetryIso.mem_linSym_iff_gaussianField_map` together — but only under `m ≠ 0`.** Checked,
not assumed: the two-line derivation was written and compiled. **The direct matrix proof kept here
takes no mass hypothesis at all**, so it is strictly stronger, and that is why it stays.
`ERRATUM 465` records the rule: **a duplicate is not automatically to be deleted — compare the
hypotheses first.**

## What is NOT here

**THIS IS THE MATRIX-LEVEL RELATION, NOT THE GROUP-LEVEL ONE.** `FieldSignGroup.symmetriesSubgroup`
is a `Subgroup` of the *linear isometry equivalences*; `linSymGL` is a `Subgroup` of `GL V ℝ`. **No
group homomorphism between them is constructed**, and no `MulEquiv`. The fence's word *inclusion* is
answered as an inclusion of **sets of matrices**. Not attempted, no cost claimed (`ERRATUM 246`).

**NO INDEX.** The fence also said *no index*, and there is still none: nothing here measures how
much bigger `linSym` is than `symmetryMatrices`, beyond the strictness on a line.

**THE STRICTNESS IS ONLY ON A LINE.** `exists_nonIsometric` needs two eigenvectors at **distinct**
eigenvalues, which the line supplies; **no strictness is proved on any other graph**, and none is
claimed. In particular nothing here says the inclusion is strict whenever `|V| ≥ 2`.
⚠ **SUPERSEDED THE NEXT UNIT, kept as written** (`ERRATUM 94`):
`FieldSymmetryProper.symmetryMatrices_ssubset_linSym` proves the strictness on **any** graph whose
propagator has two distinct eigenvalues, and `symmetryMatrices_eq_linSym_iff` makes that a
**dichotomy** — the two coincide exactly when the propagator has a single eigenvalue. **The fence
named the real hypothesis and then attached it to the wrong object**: it is the distinct
eigenvalues, not the line. **The last sentence stays literally true**: `|V| ≥ 2` is still not the
condition, and a propagator that is a multiple of the identity is the counterexample.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): a non-zero mass is taken by
`symmetryMatrices_ssubset_linSym_line`, `isUnit_det_of_mem_linSym`, `inv_mem_linSym` and
`mem_linSym_iff_orthIsometry_map` — **four of the ten**. It is **not** taken by
`mem_linSym_iff_comm`, `symmetryMatrices_eq`, `symmetryMatrices_subset_linSym`,
`coe_orthIsometry_eq_mvCLM`, `linSymGL` or `mem_linSymGL`; **the headline identification and the
`Subgroup` are both free of it**, and the first three of those six are pure matrix algebra with no
measure in them.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSymmetryInclusion

open Matrix GraphLaplacian FieldSymmetryIso FieldRotationCount

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. For an orthogonal matrix, preserving the form is commuting -/

theorem mem_linSym_iff_comm {L : Matrix V V ℝ} (hL : Lᵀ * L = 1) :
    L ∈ linSym G m ↔ L * green G m = green G m * L := by
  have hL' : L * Lᵀ = 1 := mul_eq_one_comm.mp hL
  rw [mem_linSym]
  constructor
  · intro h
    calc L * green G m = L * green G m * (Lᵀ * L) := by rw [hL, Matrix.mul_one]
      _ = (L * green G m * Lᵀ) * L := by simp only [Matrix.mul_assoc]
      _ = green G m * L := by rw [h]
  · intro h
    calc L * green G m * Lᵀ = green G m * L * Lᵀ := by rw [h]
      _ = green G m := by rw [Matrix.mul_assoc, hL', Matrix.mul_one]

/-- **THE ISOMETRIC SYMMETRIES ARE EXACTLY THE ORTHOGONAL ELEMENTS OF THE LINEAR ONES.** -/
theorem symmetryMatrices_eq :
    symmetryMatrices G m = {L : Matrix V V ℝ | L ∈ linSym G m ∧ Lᵀ * L = 1} := by
  ext L
  constructor
  · rintro ⟨hO, hc⟩
    exact ⟨(mem_linSym_iff_comm hO).mpr hc, hO⟩
  · rintro ⟨hm, hO⟩
    exact ⟨hO, (mem_linSym_iff_comm hO).mp hm⟩

theorem symmetryMatrices_subset_linSym :
    symmetryMatrices G m ⊆ (linSym G m : Set (Matrix V V ℝ)) := by
  rw [symmetryMatrices_eq]
  exact fun _ h => h.1

/-! ## 2. And on a line the inclusion is strict -/

open BoxGraph in
/-- **THE ISOMETRIC SYMMETRIES ARE A PROPER PART OF THE LINEAR ONES**, on a line of at least two
sites. -/
theorem symmetryMatrices_ssubset_linSym_line {k : ℕ} (hk : 1 ≤ k) {mass : ℝ} (hmass : mass ≠ 0) :
    symmetryMatrices (boxGraph 1 (k + 1)) mass ⊂
      (linSym (boxGraph 1 (k + 1)) mass : Set (Matrix (Site 1 (k + 1)) (Site 1 (k + 1)) ℝ)) := by
  refine ⟨symmetryMatrices_subset_linSym, fun hsub => ?_⟩
  obtain ⟨L, hL, hnO⟩ := FieldSqrtConjugation.exists_nonIsometric_line hk hmass
  exact hnO (hsub (mem_linSym.mpr hL)).1

/-! ## 3. Every linear symmetry is invertible, and its inverse is one -/

theorem isUnit_det_of_mem_linSym (hm : m ≠ 0) {L : Matrix V V ℝ} (hL : L ∈ linSym G m) :
    IsUnit L.det := by
  have h := congrArg Matrix.det (mem_linSym.mp hL)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hg : (green G m).det ≠ 0 := ((green_posDef G hm).det_pos).ne'
  refine isUnit_iff_ne_zero.mpr fun hz => hg ?_
  rw [hz] at h
  simpa using h.symm

/-- **AND THE INVERSE OF A LINEAR SYMMETRY IS A LINEAR SYMMETRY**, so `linSym` is a group in
substance. -/
theorem inv_mem_linSym (hm : m ≠ 0) {L : Matrix V V ℝ} (hL : L ∈ linSym G m) :
    L⁻¹ ∈ linSym G m := by
  have hu := isUnit_det_of_mem_linSym hm hL
  have hmul : L * L⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hmul' : L⁻¹ * L = 1 := Matrix.nonsing_inv_mul _ hu
  have h := mem_linSym.mp hL
  rw [mem_linSym]
  calc L⁻¹ * green G m * (L⁻¹)ᵀ
      = L⁻¹ * (L * green G m * Lᵀ) * (L⁻¹)ᵀ := by rw [h]
    _ = (L⁻¹ * L) * green G m * (Lᵀ * (L⁻¹)ᵀ) := by simp only [Matrix.mul_assoc]
    _ = green G m := by
        rw [hmul', Matrix.one_mul, ← Matrix.transpose_mul, hmul', Matrix.transpose_one,
          Matrix.mul_one]

/-! ## 4. The two packagings of the same map, and what that gives -/

/-- **`orthIsometry` AND `mvCLM` ARE THE SAME MAP.** Both coerce to `RayleighMatrix.mv`, and this
estate had never said so — which is why `FieldInvarianceCommutes`'s biconditional and
`FieldSymmetryIso`'s look like statements about different things. -/
theorem coe_orthIsometry_eq_mvCLM {R : Matrix V V ℝ} (hR : Rᵀ * R = 1) :
    ⇑(FieldOrthIsometry.orthIsometry hR) = ⇑(FieldLinearClassified.mvCLM R) := rfl

/-- **AN ORTHOGONAL MATRIX'S ISOMETRY PRESERVES THE GAUSSIAN FIELD IFF THE MATRIX LIES IN
`linSym`** — `FieldSymmetryIso.mem_linSym_iff_gaussianField_map` in the other packaging, which is
the packaging `FieldInvarianceCommutes` uses. -/
theorem mem_linSym_iff_orthIsometry_map (hm : m ≠ 0) {R : Matrix V V ℝ} (hR : Rᵀ * R = 1) :
    R ∈ linSym G m ↔
      MeasureTheory.Measure.map (FieldOrthIsometry.orthIsometry hR) (gaussianField G m)
        = gaussianField G m := by
  rw [coe_orthIsometry_eq_mvCLM hR]
  exact mem_linSym_iff_gaussianField_map hm

/-! ## 5. `linSym` as a `Subgroup` of the general linear group -/

/-- **THE LINEAR SYMMETRIES AS A `Subgroup`.** No hypothesis on the mass: the inverse is supplied
by the ambient group, not by inverting the matrix. -/
def linSymGL (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) :
    Subgroup (Matrix.GeneralLinearGroup V ℝ) where
  carrier := {U | (U : Matrix V V ℝ) ∈ linSym G m}
  one_mem' := (linSym G m).one_mem
  mul_mem' ha hb := (linSym G m).mul_mem ha hb
  inv_mem' {U} h := by
    have hmul : (↑U⁻¹ : Matrix V V ℝ) * (↑U : Matrix V V ℝ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hmul' : (↑U : Matrix V V ℝ) * (↑U⁻¹ : Matrix V V ℝ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hU := mem_linSym.mp h
    refine mem_linSym.mpr ?_
    calc (↑U⁻¹ : Matrix V V ℝ) * green G m * ((↑U⁻¹ : Matrix V V ℝ))ᵀ
        = (↑U⁻¹ : Matrix V V ℝ) * ((↑U : Matrix V V ℝ) * green G m
            * ((↑U : Matrix V V ℝ))ᵀ) * ((↑U⁻¹ : Matrix V V ℝ))ᵀ := by rw [hU]
      _ = ((↑U⁻¹ : Matrix V V ℝ) * (↑U : Matrix V V ℝ)) * green G m
            * (((↑U : Matrix V V ℝ))ᵀ * ((↑U⁻¹ : Matrix V V ℝ))ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = green G m := by
          rw [hmul, Matrix.one_mul, ← Matrix.transpose_mul, hmul, Matrix.transpose_one,
            Matrix.mul_one]

@[simp] theorem mem_linSymGL {U : Matrix.GeneralLinearGroup V ℝ} :
    U ∈ linSymGL G m ↔ (U : Matrix V V ℝ) ∈ linSym G m := Iff.rfl

end FieldSymmetryInclusion
