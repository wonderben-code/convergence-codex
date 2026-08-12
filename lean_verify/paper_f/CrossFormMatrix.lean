import GraphMirrorReflection
import IndefiniteCoupling

/-!
# The wall's hypothesis is a matrix being positive semidefinite

Every reflection-positivity theorem on this wall carries the same hypothesis:

    hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0

`GraphMirrorReflection.reflectionPositive_mirror` takes it, `StrictBiconditional` takes it, and
`IndefiniteCoupling.hcross_necessary_for_positivity` shows it cannot be dropped. It is a
**quantifier over every real vector on the whole vertex type**, and the estate has been
discharging it one graph at a time: `crossForm_nonpos_of_cross_diag` for a diagonal cross-cut,
`IndefiniteCoupling.hcross_bip` by computing the form on `K₂,₂` by hand, and
`IndefiniteCoupling.not_hcross` by exhibiting a vector.

**This file replaces the quantifier by a matrix.** `crossForm_eq_neg_adj` already says the form
is built from the cross-cut adjacency and nothing else — no mass, no Laplacian. Write that
adjacency as a matrix and the hypothesis is exactly that the matrix is positive semidefinite:

> **`crossForm_nonpos_iff_posSemidef`** —
> `(∀ w, crossForm G m θ H w ≤ 0) ↔ (crossMatrix G θ H).PosSemidef`.

## Two things this buys, and one it does not

**It makes the hypothesis finite,** and §5 spends the API rather than promising it. `hcross` for
a half implies `hcross` for every SUB-HALF, and the matrix proof is one application of
`Matrix.PosSemidef.conjTranspose_mul_mul_same` — zeroing rows and columns outside the sub-half is
conjugation by a diagonal indicator. The same theorem is then proved directly, where it needs no
hypothesis on the sub-half at all; the direct one is stronger and the matrix one is the evidence
that the reformulation works rather than merely restates.

**It subsumes the estate's existing discharges as special cases**, and each is re-derived here
rather than asserted to follow: the diagonal criterion is a nonnegative diagonal matrix
(`posSemidef_of_cross_diag`), and the two `IndefiniteCoupling` computations are instances of the
matrix being or not being PSD.

**And the symmetry is free, which is not obvious.** `crossMatrix p q` asks whether `p` is
adjacent to the MIRROR of `q`, which is not visibly symmetric in `p` and `q`. It is, and
`IsRefl` is exactly why: `θ` is an involution that preserves adjacency, so
`G.Adj q (θ p) ↔ G.Adj (θ q) p ↔ G.Adj p (θ q)`. Without that the matrix would need
symmetrising by hand and half the statements below would carry a factor of two.

**WHAT IT DOES NOT DO.** It does not decide the hypothesis for any graph the estate has not
already decided. Restating a condition is not proving one, and this file proves no new graph
reflection positive.

**The necessity question stays open, and §6 constrains it rather than answering it.** Whether
reflection positivity *implies* `hcross` in general is untouched — `IndefiniteCoupling` settled
only that the hypothesis cannot be DELETED from the theorem. What §6 adds is a consequence:
since `crossForm` does not depend on the mass and `ReflectionPositive` does, **a converse at one
nonzero mass would make reflection positivity the same statement at every nonzero mass**. So the
converse is falsifiable by a single mass-dependent example, with no cross form computed. No such
example is exhibited here and none is claimed to exist.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CrossFormMatrix

open Matrix GraphReflection GraphMirrorReflection

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H H' Mir : Finset V}

set_option linter.style.openClassical false
open scoped Classical

/-! ## 1. The cross-cut adjacency, and why it is symmetric -/

/-- `1` when `p` is adjacent to the mirror image of `q`, and `0` otherwise. This is the only
thing `crossForm` depends on — `GraphMirrorReflection.crossForm_eq_neg_adj`. -/
noncomputable def crossAdj (G : SimpleGraph V) [DecidableRel G.Adj] (θ : V ≃ V) (p q : V) : ℝ :=
  if G.Adj p (θ q) then 1 else 0

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **THE CROSS-CUT ADJACENCY IS SYMMETRIC**, which the definition does not show: it asks about
`p` and the mirror of `q`, and swapping the two is a different question. `IsRefl` answers it —
`θ` is an involution that preserves adjacency, so mirroring both arguments of `G.Adj q (θ p)`
turns it into `G.Adj (θ q) p`, and that is `G.Adj p (θ q)` by symmetry of adjacency. -/
theorem adj_cross_comm (h : IsRefl G θ) (p q : V) : G.Adj p (θ q) ↔ G.Adj q (θ p) := by
  constructor
  · intro hpq
    have := (h.adj p (θ q)).mpr hpq
    rw [h.invol q] at this
    exact this.symm
  · intro hqp
    have := (h.adj q (θ p)).mpr hqp
    rw [h.invol p] at this
    exact this.symm

omit [Fintype V] [DecidableEq V] in
theorem crossAdj_comm (h : IsRefl G θ) (p q : V) : crossAdj G θ p q = crossAdj G θ q p := by
  unfold crossAdj
  by_cases hpq : G.Adj p (θ q)
  · rw [if_pos hpq, if_pos ((adj_cross_comm h p q).mp hpq)]
  · rw [if_neg hpq, if_neg fun hc => hpq ((adj_cross_comm h q p).mp hc)]

/-! ## 2. The matrix

Defined on all of `V` and zeroed off `H`, rather than on the subtype `H`, so that
`Matrix.PosSemidef`'s quantifier `∀ x : V → ℝ` is literally `hcross`'s quantifier and no
extension-by-zero argument is needed anywhere below. -/

/-- **THE CROSS MATRIX.** The cross-cut adjacency restricted to the half, zero elsewhere. -/
noncomputable def crossMatrix (G : SimpleGraph V) [DecidableRel G.Adj] (θ : V ≃ V)
    (H : Finset V) : Matrix V V ℝ :=
  fun p q => if p ∈ H ∧ q ∈ H then crossAdj G θ p q else 0

omit [Fintype V] in
theorem crossMatrix_isHermitian (h : IsRefl G θ) : (crossMatrix G θ H).IsHermitian := by
  ext p q
  simp only [conjTranspose_apply, star_trivial, crossMatrix]
  by_cases hq : q ∈ H <;> by_cases hp : p ∈ H <;>
    simp [hp, hq, crossAdj_comm h q p]

/-- **THE FORM IS THE MATRIX'S**, with the sign the wall's convention puts on it. -/
theorem dotProduct_crossMatrix (hM : IsMirrorHalf θ H Mir) (m : ℝ) (w : V → ℝ) :
    w ⬝ᵥ (crossMatrix G θ H *ᵥ w) = - crossForm G m θ H w := by
  classical
  rw [crossForm_eq_neg_adj hM m w, neg_neg]
  have hLHS : w ⬝ᵥ (crossMatrix G θ H *ᵥ w)
      = ∑ p, ∑ q, w p * w q * crossMatrix G θ H p q := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hout : ∀ p ∈ Finset.univ, p ∉ H →
      (∑ q, w p * w q * crossMatrix G θ H p q) = 0 := by
    intro p _ hp
    exact Finset.sum_eq_zero fun q _ => by
      rw [crossMatrix, if_neg fun hc => hp hc.1, mul_zero]
  rw [hLHS, (Finset.sum_subset (Finset.subset_univ H) hout).symm]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hin : ∀ q ∈ Finset.univ, q ∉ H → w p * w q * crossMatrix G θ H p q = 0 := by
    intro q _ hq
    rw [crossMatrix, if_neg fun hc => hq hc.2, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ H) hin]
  exact Finset.sum_congr rfl fun q hq => by rw [crossMatrix, if_pos ⟨hp, hq⟩, crossAdj]

/-! ## 3. The criterion -/

/-- **THE WALL'S HYPOTHESIS IS A MATRIX BEING POSITIVE SEMIDEFINITE.** The quantifier over every
real vector on `V` is the quantifier `Matrix.PosSemidef` already carries, and the Hermitian
clause is §1's symmetry. -/
theorem crossForm_nonpos_iff_posSemidef (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ) :
    (∀ w : V → ℝ, crossForm G m θ H w ≤ 0) ↔ (crossMatrix G θ H).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · refine fun hc => ⟨crossMatrix_isHermitian h, fun x => ?_⟩
    rw [star_trivial, dotProduct_crossMatrix hM m x]
    exact neg_nonneg.mpr (hc x)
  · intro hps w
    have := hps.2 w
    rw [star_trivial, dotProduct_crossMatrix hM m w] at this
    exact neg_nonneg.mp this

/-! ## 4. The estate's existing discharges, as instances

Each of the three is re-derived through the criterion rather than declared to be an instance of
it, which is the check `ERRATUM 46`'s family exists to force. -/

/-- **THE DIAGONAL CRITERION IS A DIAGONAL MATRIX.** `crossForm_nonpos_of_cross_diag`'s
hypothesis says the cross-cut adjacency vanishes off the diagonal, and the criterion turns its
conclusion into positive semidefiniteness — stated together so that what is being claimed to be
an instance of what is visible in one place. -/
theorem cross_diag_nonpos_and_posSemidef (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ)
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) :
    (∀ w : V → ℝ, crossForm G m θ H w ≤ 0) ∧ (crossMatrix G θ H).PosSemidef :=
  let hc := fun w => crossForm_nonpos_of_cross_diag (m := m) hM hdiag w
  ⟨hc, (crossForm_nonpos_iff_posSemidef hM h m).mp hc⟩

omit [Fintype V] in
/-- And the matrix really is diagonal there, which is the content the previous theorem routes
around: off the diagonal every entry is zero. -/
theorem crossMatrix_offDiag_eq_zero
    (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) {p q : V} (hpq : p ≠ q) :
    crossMatrix G θ H p q = 0 := by
  rw [crossMatrix]
  by_cases hmem : p ∈ H ∧ q ∈ H
  · rw [if_pos hmem, crossAdj, if_neg fun hadj => hpq (hdiag p hmem.1 q hmem.2 hadj)]
  · rw [if_neg hmem]

/-- **AND THE CRITERION IS NOT VACUOUS IN EITHER DIRECTION.** `IndefiniteCoupling.crossGraph`
fails `hcross`, so its cross matrix is not positive semidefinite — which is the statement that
this reformulation can express a failure and not only a success. -/
theorem not_posSemidef_crossGraph (m : ℝ) :
    ¬ (crossMatrix IndefiniteCoupling.crossGraph IndefiniteCoupling.rho
        IndefiniteCoupling.Hh).PosSemidef :=
  fun hps => IndefiniteCoupling.not_hcross m
    ((crossForm_nonpos_iff_posSemidef IndefiniteCoupling.isMirrorHalf_Hh
      IndefiniteCoupling.isRefl_rho m).mpr hps)

/-- The other side: `IndefiniteCoupling.bipGraph` (`K₂,₂`) satisfies `hcross` without being
diagonal, so its cross matrix IS positive semidefinite and is not a diagonal one. That pair is
`IndefiniteCoupling.cross_diag_not_necessary` read through the matrix. -/
theorem posSemidef_crossGraph_bip (m : ℝ) :
    (crossMatrix IndefiniteCoupling.bipGraph IndefiniteCoupling.rho
      IndefiniteCoupling.Hh).PosSemidef :=
  (crossForm_nonpos_iff_posSemidef IndefiniteCoupling.isMirrorHalf_Hh
    IndefiniteCoupling.isRefl_rho_bip m).mp (IndefiniteCoupling.hcross_bip m)

/-! ## 5. What the matrix form is for: the hypothesis passes to sub-halves

The claim that a reformulation "makes Mathlib's API available" is worth nothing until something
is derived with it, so here is the derivation. **`hcross` for a half implies `hcross` for every
sub-half**, and the matrix proof is one application of
`Matrix.PosSemidef.conjTranspose_mul_mul_same` — zeroing the rows and columns outside `H'` is
conjugation by a diagonal indicator.

The same statement is proved directly below without the matrix, and the direct proof needs NO
hypothesis on `H'` at all. Both are here on purpose: the direct one is the stronger theorem, and
the matrix one is the evidence that the reformulation does work rather than merely restate.
-/

/-- The diagonal indicator of a subset, as a matrix. -/
noncomputable def indic (H' : Finset V) : Matrix V V ℝ :=
  Matrix.diagonal fun p => if p ∈ H' then (1 : ℝ) else 0

omit [Fintype V] in
theorem indic_conjTranspose (H' : Finset V) : (indic H' : Matrix V V ℝ)ᴴ = indic H' := by
  rw [indic, Matrix.diagonal_conjTranspose]
  rfl

/-- **ZEROING OUTSIDE A SUB-HALF IS CONJUGATION BY THE INDICATOR.** -/
theorem crossMatrix_sub (h' : H' ⊆ H) :
    crossMatrix G θ H' = (indic H')ᴴ * crossMatrix G θ H * indic H' := by
  rw [indic_conjTranspose]
  ext p q
  rw [indic, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hp : p ∈ H' <;> by_cases hq : q ∈ H'
  · simp [crossMatrix, hp, hq, h' hp, h' hq]
  · simp [crossMatrix, hp, hq]
  · simp [crossMatrix, hp, hq]
  · simp [crossMatrix, hp, hq]

/-- **AND SO THE HYPOTHESIS RESTRICTS, THROUGH THE MATRIX.** One application of
`Matrix.PosSemidef.conjTranspose_mul_mul_same`, read back through §3. -/
theorem crossForm_nonpos_sub_of_matrix (hM' : IsMirrorHalf θ H' Mir) (h : IsRefl G θ) (m : ℝ)
    (h' : H' ⊆ H) (hps : (crossMatrix G θ H).PosSemidef) :
    ∀ w : V → ℝ, crossForm G m θ H' w ≤ 0 := by
  have hsub : (crossMatrix G θ H').PosSemidef := by
    rw [crossMatrix_sub h']
    exact hps.conjTranspose_mul_mul_same _
  exact (crossForm_nonpos_iff_posSemidef hM' h m).mpr hsub

/-- **THE SAME THING WITHOUT THE MATRIX, AND WITH NO HYPOTHESIS AT ALL ON EITHER HALF.** Test the
larger half with the vector that is `w` on `H'` and zero elsewhere: the double sum over `H`
collapses onto `H'`, so a sub-half's form is literally one of the larger half's values. No
`IsMirrorHalf`, no `IsRefl`, no `crossForm_eq_neg_adj` — the indicator does all of it.

Stated beside the matrix proof deliberately. The direct one is the stronger theorem; the matrix
one is the evidence that §3 is a working reformulation rather than a restatement. -/
theorem crossForm_nonpos_sub (m : ℝ) (h' : H' ⊆ H)
    (hc : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) (w : V → ℝ) :
    crossForm G m θ H' w ≤ 0 := by
  classical
  have hkey : crossForm G m θ H (fun p => if p ∈ H' then w p else 0)
      = crossForm G m θ H' w := by
    rw [crossForm, crossForm,
      ← Finset.sum_subset h' fun p _ hp => Finset.sum_eq_zero fun q _ => by rw [if_neg hp]; ring]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_subset h' fun q _ hq => by rw [if_neg hq]; ring]
    exact Finset.sum_congr rfl fun q hq => by rw [if_pos hp, if_pos hq]
  exact hkey ▸ hc _

/-! ## 6. The open question, and the consequence that makes it falsifiable

`hcross` is SUFFICIENT for `GraphMirrorReflection.reflectionPositive_mirror` — that is the
theorem — and `IndefiniteCoupling.hcross_necessary_for_positivity` shows it cannot be DELETED,
by exhibiting one graph where it fails and reflection positivity fails with it. **Whether it is
necessary in general — whether reflection positivity implies it — is open**, and is named as
open in this wall's account and in two file headers.

It is not, however, unconstrained, and the constraint is a theorem rather than a feeling.
**`crossForm` does not depend on the mass** (`crossForm_mass_independent`, proved when the
coupling was shown to be mass-free) while `ReflectionPositive` plainly does. So a converse would
force those two facts to meet:

> **`reflectionPositive_mass_independent_of_converse`** — if reflection positivity implies
> `hcross` at ONE nonzero mass, then reflection positivity at that mass implies it at EVERY
> nonzero mass.

**That makes the converse falsifiable by a single example**: any graph and half that is
reflection positive at one nonzero mass and not at another kills it, with no need to compute a
cross form at all. No such example is exhibited here, and none is claimed to exist.
-/

/-- **A CONVERSE WOULD MAKE REFLECTION POSITIVITY MASS-INDEPENDENT.** The hypothesis is the
converse AT ONE MASS; the conclusion is reflection positivity at any other nonzero mass. The
whole content is that the two steps are at different masses and the middle term is not: `hcross`
is mass-free, so it carries across, and `reflectionPositive_mirror_of_isHalf` carries it back. -/
theorem reflectionPositive_mass_independent_of_converse (hH : GraphHalfSpace.IsHalf θ H)
    (h : IsRefl G θ) {m m' : ℝ} (hm' : m' ≠ 0)
    (hconv : GraphReflection.ReflectionPositive G m θ H → ∀ w, crossForm G m θ H w ≤ 0)
    (hrp : GraphReflection.ReflectionPositive G m θ H) :
    GraphReflection.ReflectionPositive G m' θ H := by
  have hc := hconv hrp
  have hc' : ∀ w : V → ℝ, crossForm G m' θ H w ≤ 0 := by
    intro w
    rw [← crossForm_mass_independent
      (Mir := (∅ : Finset V)) (isMirrorHalf_of_isHalf hH) m m' w]
    exact hc w
  exact reflectionPositive_mirror_of_isHalf hH h hm' hc'

/-- And the same thing said as the falsification test, so that a reader looking for a way to
attack the question finds it stated as a task: **a graph and half that is reflection positive at
one nonzero mass and NOT at another refutes the converse at that graph**, without any cross form
being computed. -/
theorem not_converse_of_mass_dependent (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    {m m' : ℝ} (hm' : m' ≠ 0)
    (hrp : GraphReflection.ReflectionPositive G m θ H)
    (hnot : ¬ GraphReflection.ReflectionPositive G m' θ H) :
    ¬ (GraphReflection.ReflectionPositive G m θ H → ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) :=
  fun hconv => hnot (reflectionPositive_mass_independent_of_converse hH h hm' hconv hrp)

end CrossFormMatrix
