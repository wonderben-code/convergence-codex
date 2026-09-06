import FieldSymmetryProper

/-!
# Which graphs? The dichotomy becomes a statement a reader can check by looking at the graph

`FieldSymmetryProper` proved that the isometric symmetries are **all** of the linear symmetries
exactly when the propagator has a single eigenvalue, and fenced the obvious next question: *`green
G m = c • 1` should be equivalent to `G` having no edges … and that equivalence is not proved here,
so nothing says which graphs fall on which side.* **It is proved here.**

## What is proved

**`no_adj_of_lapMatrix_smul`** — if the Laplacian is a multiple of the identity then the graph has
no edges. One off-diagonal entry does it: at `i ≠ j` the Laplacian is `−1` on an edge and the scalar
matrix is `0`.

**`lapMatrix_eq_zero_of_no_adj`** — and conversely an edgeless graph has Laplacian `0`, the diagonal
included, because `SimpleGraph.degree_eq_zero_iff_notMem_support` makes every degree zero.

**`massive_eq_smul_of_no_adj`, `green_eq_smul_of_no_adj`** — so on an edgeless graph the massive
operator is `m² • 1` and the propagator is `(m²)⁻¹ • 1`, by `Matrix.inv_eq_right_inv` rather than
any inversion lemma.

**`no_adj_of_green_eq_smul`** — and back the other way: a scalar propagator forces a scalar massive
operator (multiply `green * massive = 1` by `c⁻¹`), hence a scalar Laplacian, hence no edges.

**`symmetryMatrices_eq_linSym_iff_no_adj`** — **THE DICHOTOMY, ABOUT THE GRAPH.** On a non-empty
vertex set and at non-zero mass, the isometric symmetries are **all** of the linear symmetries **if
and only if the graph has no edges.**

**`symmetryMatrices_ssubset_linSym_of_ne_bot`** — **so one edge is enough.** On any graph other than
the edgeless one, the isometric symmetries are a **proper** part of the linear ones.

## What is NOT here

**NO CARDINALITY AND NO INDEX.** The inclusion is strict; **nothing measures how much is missing**,
and `FieldLineCount`'s `2^(m+1)` counts the isometric side only. Not attempted, no cost claimed
(`ERRATUM 246`).

**STILL THE MATRIX LEVEL.** `FieldSignGroup.symmetriesSubgroup` and
`FieldSymmetryInclusion.linSymGL` are group objects over different ambient types, and **no
homomorphism between them is constructed.**

**THE EMPTY VERTEX SET IS EXCLUDED.** `[Nonempty V]` is inherited from
`FieldSymmetryProper.symmetryMatrices_eq_linSym_iff`. With no vertices the statement is true for a
`Subsingleton` reason and **that proof is not written.**

**NOTHING ABOUT THE EDGELESS FIELD BEYOND ITS SYMMETRIES.** That `green` is `(m²)⁻¹ • 1` there says
the field is `|V|` independent Gaussians; **no such statement is made**, and nothing here connects
to `FieldMassNecessity`'s degenerate `m = 0`, which is a different degeneration.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. A
dichotomy about finite graphs is a shadow sorted into two heaps.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `m ≠ 0` is taken by
`green_eq_smul_of_no_adj`, `no_adj_of_green_eq_smul`, `symmetryMatrices_eq_linSym_iff_no_adj` and
`symmetryMatrices_ssubset_linSym_of_ne_bot` — **four of the seven**. The three graph-and-Laplacian
statements — `no_adj_of_lapMatrix_smul`, `lapMatrix_eq_zero_of_no_adj`, `massive_eq_smul_of_no_adj`
— take **no mass hypothesis**, and the first two mention no mass at all. `[Nonempty V]` is taken by
the last two only.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSymmetryEdgeless

open Matrix GraphLaplacian FieldSymmetryIso FieldRotationCount FieldSymmetryProper
  FieldSymmetryInclusion

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A scalar Laplacian has no edges, and an edgeless Laplacian is zero -/

theorem no_adj_of_lapMatrix_smul {a : ℝ} (h : G.lapMatrix ℝ = a • (1 : Matrix V V ℝ))
    (i j : V) : ¬ G.Adj i j := by
  intro hadj
  have hij : i ≠ j := hadj.ne
  have he := congrFun (congrFun h i) j
  rw [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    Matrix.diagonal_apply_ne _ hij, SimpleGraph.adjMatrix_apply, if_pos hadj,
    Matrix.smul_apply, Matrix.one_apply_ne hij] at he
  norm_num at he

theorem lapMatrix_eq_zero_of_no_adj (h : ∀ i j : V, ¬ G.Adj i j) :
    G.lapMatrix ℝ = 0 := by
  have hdeg : ∀ v, G.degree v = 0 := by
    intro v
    rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
    rintro ⟨w, hw⟩
    exact h v w hw
  ext i j
  rw [SimpleGraph.lapMatrix, Matrix.sub_apply, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix_apply, if_neg (h i j), Matrix.zero_apply]
  by_cases hij : i = j
  · rw [hij, Matrix.diagonal_apply_eq, hdeg]
    norm_num
  · rw [Matrix.diagonal_apply_ne _ hij]
    norm_num

/-! ## 2. So the propagator is scalar exactly when the graph is edgeless -/

theorem massive_eq_smul_of_no_adj (h : ∀ i j : V, ¬ G.Adj i j) (m : ℝ) :
    massive G m = (m ^ 2) • (1 : Matrix V V ℝ) := by
  rw [massive, lapMatrix_eq_zero_of_no_adj h, zero_add]
  ext i j
  by_cases hij : i = j <;>
    simp [hij]

theorem green_eq_smul_of_no_adj (hm : m ≠ 0) (h : ∀ i j : V, ¬ G.Adj i j) :
    green G m = (m ^ 2)⁻¹ • (1 : Matrix V V ℝ) := by
  rw [green, massive_eq_smul_of_no_adj h]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero 2 hm), one_smul]

theorem no_adj_of_green_eq_smul (hm : m ≠ 0) {c : ℝ} (hc : c ≠ 0)
    (h : green G m = c • (1 : Matrix V V ℝ)) (i j : V) : ¬ G.Adj i j := by
  have hone := green_mul_massive G hm
  rw [h, Matrix.smul_mul, Matrix.one_mul] at hone
  have hmass : massive G m = c⁻¹ • (1 : Matrix V V ℝ) := by
    rw [← hone, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hlap : G.lapMatrix ℝ = (c⁻¹ - m ^ 2) • (1 : Matrix V V ℝ) := by
    have : G.lapMatrix ℝ = massive G m - Matrix.diagonal (fun _ : V => m ^ 2) := by
      rw [massive]; abel
    rw [this, hmass]
    ext a b
    by_cases hab : a = b <;>
      simp [hab]
  exact no_adj_of_lapMatrix_smul hlap i j

/-! ## 3. So the dichotomy is a statement about the graph -/

/-- **THE ISOMETRIC SYMMETRIES ARE ALL OF THE LINEAR SYMMETRIES EXACTLY WHEN THE GRAPH HAS NO
EDGES.** -/
theorem symmetryMatrices_eq_linSym_iff_no_adj [Nonempty V] (hm : m ≠ 0) :
    symmetryMatrices G m = (linSym G m : Set (Matrix V V ℝ)) ↔ ∀ i j : V, ¬ G.Adj i j := by
  constructor
  · intro heq
    have hall := (symmetryMatrices_eq_linSym_iff hm).mp heq
    obtain ⟨i0⟩ := ‹Nonempty V›
    have hc : (green_posDef G hm).isHermitian.eigenvalues i0 ≠ 0 :=
      ((green_posDef G hm).eigenvalues_pos i0).ne'
    exact no_adj_of_green_eq_smul hm hc
      (green_eq_scalar_of_eigenvalues_const hm fun i => hall i i0)
  · intro h
    exact symmetryMatrices_eq_linSym_of_scalar (inv_ne_zero (pow_ne_zero 2 hm))
      (green_eq_smul_of_no_adj hm h)

/-- **SO ONE EDGE IS ENOUGH**: on any graph that is not edgeless, the isometric symmetries are a
**proper** part of the linear ones. -/
theorem symmetryMatrices_ssubset_linSym_of_ne_bot [Nonempty V] (hm : m ≠ 0) (hG : G ≠ ⊥) :
    symmetryMatrices G m ⊂ (linSym G m : Set (Matrix V V ℝ)) := by
  refine ⟨symmetryMatrices_subset_linSym, fun hsub => ?_⟩
  have heq : symmetryMatrices G m = (linSym G m : Set (Matrix V V ℝ)) :=
    Set.Subset.antisymm symmetryMatrices_subset_linSym hsub
  obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hG
  exact (symmetryMatrices_eq_linSym_iff_no_adj hm).mp heq a b hab

end FieldSymmetryEdgeless
