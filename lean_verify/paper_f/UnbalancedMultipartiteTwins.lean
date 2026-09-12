import UnbalancedMultipartite
import LaplacianTwoClasses

/-!
# The parts of a complete multipartite graph are twin classes

**THE PREVIOUS UNIT FENCED THE MULTIPLICITIES AND THIS FILE OPENS THEM, FROM THE OTHER SIDE.**
`UnbalancedMultipartite` determined the eigenvalue **set** exactly and said in its own words that
it *says nothing about how often each occurs*, naming the obstacle: parts of equal size share an
eigenvalue, so the count is a sum over a fibre of `i ↦ nᵢ`. **The obstacle is a twin class.** Two
vertices of one part have the **same** neighbourhood — literally the same `Finset`, because the
previous unit's `neighborFinset_eq` depends only on the part index — so this estate's twin-class
counting applies with no new spectral work at all.

**AND THE EIGENVALUE ARRIVES FROM THE DEGREE, NOT FROM A ROW IDENTITY.** `LaplacianTwinClass`
places a twin class's differences in the eigenspace at the class's **common degree**, which here is
`N − nᵢ` (`UnbalancedMultipartite.degree_multi`). The previous unit reached that same eigenvalue by
computing the Laplacian's row. **So one third of the spectrum now has two independent derivations**
— one from the row identity, one from a fact about twins that mentions no multipartite structure —
which is the double coverage `CompleteSpectrumTwoPoints` gives for the complete graph.

## What is proved

**`neighborFinset_eq_of_fst_eq`** — same part, same neighbourhood, in one rewrite.

**`partImage`, `card_partImage`, `mem_partImage`, `fst_eq_of_mem_partImage`,
`disjoint_partImage`** — a part as a `Finset` of the sigma type: the image of `Sigma.mk i`, of
cardinality `nᵢ` because `Sigma.mk i` is injective, and two parts are disjoint.

**`card_sub_one_le_finrank_part`** — **THE FAMILY'S FIRST MULTIPLICITY STATEMENT**: the eigenspace
at `N − nᵢ` has dimension at least `nᵢ − 1`.

**`sum_sub_one_le_finrank_parts`** — **AND TWO PARTS OF THE SAME SIZE CONTRIBUTE BOTH DEFICITS**:
`(nᵢ − 1) + (nⱼ − 1)` at that one eigenvalue, which is the *sum over a fibre of `i ↦ nᵢ`* the
previous unit named — for two parts of the fibre, which is as far as `LaplacianTwoClasses` reaches.

**`not_injective_eigenvalues_of_three_le`, `not_injective_eigenvalues_of_two_equal_parts`** — so
the Laplacian spectrum is **degenerate** as soon as one part holds three vertices, or two parts
hold two each. *Three* in the first case and not two: one pair of twins gives one eigenvector and
one eigenvector is no obstruction, which is exactly why the second case needs two classes.

**`infinite_symmetryMatrices_of_three_le`, `infinite_symmetryMatrices_of_two_equal_parts`** — **SO
THE GAUSSIAN FIELD ON SUCH A GRAPH HAS INFINITELY MANY SYMMETRIES**, at every non-zero mass,
through `FieldSymmetryFinite.finite_iff_lapMatrix`.

**`infinite_symmetryMatrices_equipartite_family`** — **and the balanced hypotheses are covered as
an instance**: at `V := fun _ : Fin r => Fin t` with `2 ≤ r` and `2 ≤ t`, parts `0` and `1` are two
classes of the same size. `MultipartiteEigenspace.infinite_symmetryMatrices_multi` states the same
conclusion for `completeEquipartiteGraph r t` — a **different** graph on a different vertex type —
and nothing is transported between them; this is the statement re-derived for this family by a
route that does not compute an eigenspace at all.

## What is NOT here

* **LOWER BOUNDS ONLY, AND THE TWIN BOUND IS KNOWN NOT TO BE SHARP IN GENERAL.**
  `TwinClassNotExact.class_bound_lt_finrank` exhibits two disjoint triangles where a **maximal**
  class of three sits in an eigenspace of dimension at least four. **Nothing here shows the bound
  sharp for this family**, and the eigenspace at `N − nᵢ` is not characterised. Two routes would:
  the row-identity characterisation and a rank–nullity count, which is what
  `MultipartiteEigenspace` did for the balanced middle eigenspace; or a squeeze against an upper
  bound. Neither is attempted (`ERRATUM 246`).
* **AND THE UPPER BOUND THIS ESTATE HAS WOULD NOT CLOSE IT.**
  `LaplacianMultiplicityBound.finrank_le_of_connected` gives `N − 1` at every non-zero eigenvalue
  of a **connected** graph; the gap against `nᵢ − 1` is `N − nᵢ`, which is never zero on a graph
  with an edge. **This file also does not prove this family connected**, so that bound is not even
  in hand here.
* **NOTHING AT THE EIGENVALUE `N`.** Vertices in different parts are not twins, so the twin route
  cannot see that eigenspace at all; the previous unit exhibits one eigenvector there and no more.
* **NO THIRD CLASS.** `LaplacianTwoClasses`' own header records that the general form — all classes
  at one eigenvalue together — is unproved, so a fibre of three equal part sizes is not summed here.
* **NO SIGNLESS LAPLACIAN**, and no characteristic polynomial.
* **NO WALL MOVES AND NO PUBLISHED TAG MOVES.** `W1`'s open part is still `OS0` and `OS4`, and `OS1`
  in its continuum sense.

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `ι` a `Fintype` with `DecidableEq` and each
`V i` a `Fintype` with `DecidableEq`, as in the previous unit. Beyond those: a vertex of the part
on the multiplicity bound, `i ≠ j` with a vertex each and equal sizes on the two-class bound,
`3 ≤ nᵢ` or `2 ≤ nᵢ = nⱼ` on the degeneracy statements, and `m ≠ 0` on the two symmetry statements
— the mass appears nowhere else.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace UnbalancedMultipartiteTwins

open Matrix Finset SimpleGraph UnbalancedMultipartite
open FieldRotationCount

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. Two vertices of one part have the same neighbourhood -/

omit [∀ i, DecidableEq (V i)] in
theorem neighborFinset_eq_of_fst_eq {p q : Σ i, V i} (h : p.1 = q.1) :
    (completeMultipartiteGraph V).neighborFinset p
      = (completeMultipartiteGraph V).neighborFinset q := by
  rw [neighborFinset_eq, neighborFinset_eq, h]

/-! ## 2. A part, as a set of vertices -/

/-- The vertices of part `i`, as a `Finset` of the sigma type. -/
def partImage (W : ι → Type*) [DecidableEq ι] [∀ i, Fintype (W i)] [∀ i, DecidableEq (W i)]
    (i : ι) : Finset (Σ i, W i) :=
  Finset.univ.image (Sigma.mk i)

omit [Fintype ι] in
theorem card_partImage (i : ι) : (partImage V i).card = Fintype.card (V i) := by
  rw [partImage, Finset.card_image_of_injective _ sigma_mk_injective, Finset.card_univ]

omit [Fintype ι] in
theorem fst_eq_of_mem_partImage {i : ι} {q : Σ i, V i} (h : q ∈ partImage V i) : q.1 = i := by
  rw [partImage, Finset.mem_image] at h
  obtain ⟨a, -, rfl⟩ := h
  rfl

/-! ## 3. So the part is a twin class, and its size bounds a multiplicity from below -/

theorem card_sub_one_le_finrank_part {i : ι} (a : V i) :
    Fintype.card (V i) - 1 ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
        - ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • LinearMap.id)) := by
  have h := LaplacianTwinClass.card_sub_one_le_finrank_of_open_class
    (G := completeMultipartiteGraph V) (S := partImage V i) (u₀ := ⟨i, a⟩)
    (fun u hu => neighborFinset_eq_of_fst_eq (by rw [fst_eq_of_mem_partImage hu]))
  rw [card_partImage, degree_multi, Nat.cast_sub (card_part_le i)] at h
  exact h

omit [Fintype ι] in
theorem mem_partImage {i : ι} (a : V i) : (⟨i, a⟩ : Σ i, V i) ∈ partImage V i :=
  Finset.mem_image_of_mem _ (Finset.mem_univ a)

omit [Fintype ι] in
theorem disjoint_partImage {i j : ι} (hij : i ≠ j) :
    Disjoint (partImage V i) (partImage V j) := by
  rw [Finset.disjoint_left]
  intro q hi hj
  exact hij ((fst_eq_of_mem_partImage hi).symm.trans (fst_eq_of_mem_partImage hj))

/-! ## 4. Two parts of the same size are two classes at one eigenvalue -/

theorem sum_sub_one_le_finrank_parts {i j : ι} (hij : i ≠ j) (a : V i) (b : V j)
    (hcard : Fintype.card (V j) = Fintype.card (V i)) :
    (Fintype.card (V i) - 1) + (Fintype.card (V j) - 1) ≤ Module.finrank ℝ (LinearMap.ker
      (Matrix.toLin' ((completeMultipartiteGraph V).lapMatrix ℝ)
        - ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i)) • LinearMap.id)) := by
  have hdeg : (completeMultipartiteGraph V).degree ⟨j, b⟩
      = (completeMultipartiteGraph V).degree ⟨i, a⟩ := by
    rw [degree_multi, degree_multi, hcard]
  have h := LaplacianTwoClasses.sum_sub_one_le_finrank_of_open_classes
    (G := completeMultipartiteGraph V) (S₁ := partImage V i) (S₂ := partImage V j)
    (u₁ := ⟨i, a⟩) (u₂ := ⟨j, b⟩) (mem_partImage a) (mem_partImage b) (disjoint_partImage hij)
    (fun u hu => neighborFinset_eq_of_fst_eq (by rw [fst_eq_of_mem_partImage hu]))
    (fun u hu => neighborFinset_eq_of_fst_eq (by rw [fst_eq_of_mem_partImage hu])) hdeg
  rw [card_partImage, card_partImage, degree_multi, Nat.cast_sub (card_part_le i)] at h
  exact h

/-! ## 5. So the spectrum is degenerate, and the field has infinitely many symmetries -/

theorem not_injective_eigenvalues_of_three_le {i : ι} (h : 3 ≤ Fintype.card (V i)) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian
      (completeMultipartiteGraph V)).eigenvalues := by
  obtain ⟨a⟩ : Nonempty (V i) := Fintype.card_pos_iff.mp (by omega)
  refine LaplacianTwinClass.not_injective_of_open_class (S := partImage V i) (u₀ := ⟨i, a⟩)
    (fun u hu => neighborFinset_eq_of_fst_eq (by rw [fst_eq_of_mem_partImage hu])) ?_
  rw [card_partImage]
  omega

theorem not_injective_eigenvalues_of_two_equal_parts {i j : ι} (hij : i ≠ j)
    (hcard : Fintype.card (V j) = Fintype.card (V i)) (h2 : 2 ≤ Fintype.card (V i)) :
    ¬ Function.Injective (FieldSimpleConverse.lapMatrix_isHermitian
      (completeMultipartiteGraph V)).eigenvalues := by
  intro hinj
  have hdim := FieldSimpleConverse.finrank_lapMatrix_le_one_iff_injective.mpr hinj
  obtain ⟨a⟩ : Nonempty (V i) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b⟩ : Nonempty (V j) := Fintype.card_pos_iff.mp (by omega)
  have hb := sum_sub_one_le_finrank_parts hij a b hcard
  have hle := hdim ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
  omega

theorem infinite_symmetryMatrices_of_three_le {m : ℝ} (hm : m ≠ 0) {i : ι}
    (h : 3 ≤ Fintype.card (V i)) :
    (symmetryMatrices (completeMultipartiteGraph V) m).Infinite := by
  intro hfin
  have hall := (FieldSymmetryFinite.finite_iff_lapMatrix hm).mp hfin
  obtain ⟨a⟩ : Nonempty (V i) := Fintype.card_pos_iff.mp (by omega)
  have h2 := card_sub_one_le_finrank_part (V := V) a
  have hle := hall ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
  omega

theorem infinite_symmetryMatrices_of_two_equal_parts {m : ℝ} (hm : m ≠ 0) {i j : ι}
    (hij : i ≠ j) (hcard : Fintype.card (V j) = Fintype.card (V i))
    (h2 : 2 ≤ Fintype.card (V i)) :
    (symmetryMatrices (completeMultipartiteGraph V) m).Infinite := by
  intro hfin
  have hall := (FieldSymmetryFinite.finite_iff_lapMatrix hm).mp hfin
  obtain ⟨a⟩ : Nonempty (V i) := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨b⟩ : Nonempty (V j) := Fintype.card_pos_iff.mp (by omega)
  have hb := sum_sub_one_le_finrank_parts hij a b hcard
  have hle := hall ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V i))
  omega

/-! ## 6. The equipartite family is an instance, reached without transporting anything -/

theorem infinite_symmetryMatrices_equipartite_family {m : ℝ} (hm : m ≠ 0) {r t : ℕ}
    (hr : 2 ≤ r) (ht : 2 ≤ t) :
    (symmetryMatrices (completeMultipartiteGraph (fun _ : Fin r => Fin t)) m).Infinite :=
  infinite_symmetryMatrices_of_two_equal_parts hm
    (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
    (Fin.ne_of_val_ne (by norm_num)) rfl (by simpa using ht)

end UnbalancedMultipartiteTwins
