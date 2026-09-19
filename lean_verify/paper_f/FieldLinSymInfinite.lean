import FieldSymmetryIso
import FieldRotationCount

/-!
# Two vertices and nothing else: the orthogonal group is infinite, so the linear symmetries are

**FOUR FILES SAY SOMETHING OF THIS SHAPE AND EXACTLY ONE OF THEM IS THIS THEOREM.** Counted, not
guessed (`ERRATUM 450`), and counted across line breaks because three of the four wrap the phrase:
*infinite as soon as* occurs in `FieldAffineGroup`, `FieldBlockGroup`, `FieldBlockProduct` and
`FieldEigenMultiplicity`.

**THE ONE THIS FILE PROVES** is `FieldAffineGroup`'s: *the linear symmetry group is the full
orthogonal group, **infinite as soon as `|V| ≥ 2`**, so there is no count to make.*

**THE OTHER THREE ARE ABOUT A SMALLER GROUP AND ARE NOT PROVED HERE.** `FieldBlockGroup` and
`FieldBlockProduct` say a **block-diagonal** orthogonal group is infinite as soon as one block has
size two; `FieldEigenMultiplicity` says `∏ᵢ O(dᵢ)` is infinite as soon as some `dᵢ ≥ 2`. Each needs
a circle **inside a block**, and this file's circle turns the plane of two coordinate vectors, which
may sit in different blocks.
⚠ **AND `NOT PROVED HERE` IS THE MOST THIS PARAGRAPH MAY SAY, 2026-09-19** (`ERRATUM 653`): its
first draft went on to say their sentences *stay unproved*, and **that was false** — the estate
proves all three, and `FieldBlockInfinite` now states the composition
(`FieldSymmetryFinite.infinite_symmetryMatrices_of_two_le_finrank` with
`FieldBlockProduct.card_fib_eq_finrank_eigenspace` and `symmetry_mulEquiv_prod`). **The clause that
survives is the one about THIS file**, and it is worth keeping: a circle in the plane of two
coordinate vectors does not respect a block decomposition, so the two theorems are genuinely
different and neither subsumes the other.

In all four the sentence carries the weight of a refusal — it is the reason no cardinality is
attempted — and a refusal resting on an unproved sentence is worth exactly the sentence. **One of
the four is now a theorem.**

One consequence is not about prose. The previous unit proved
`FieldRotationNonIsometric.infinite_linSym_quadForm` from an orthogonal eigenpair of equal
non-zero length at two DISTINCT eigenvalues. Its conclusion needs none of that.

## What is proved

**`infinite_setOf_orthogonal_of_pair`, `infinite_setOf_orthogonal`, `infinite_unitaryGroup`** — for
`|V| ≥ 2` the orthogonal matrices over `ℝ^V` are infinite, as a set and as Mathlib's
`Matrix.unitaryGroup V ℝ`. The witnesses are the rotations of the plane of two **coordinate
vectors** `Pi.single i 1` and `Pi.single j 1`, orthonormal exactly because `i ≠ j`, through the
angles of `Ioo 0 π`; `Real.injOn_cos` and `FieldRotationCount.rotMatrix_inj` keep them distinct.
**No graph, no mass, no propagator enters.**

**`infinite_setOf_linSym_of_pair`** — conjugating that circle by the propagator's square root lands
it in `FieldSymmetryIso.linSym`, because
`FieldSqrtConjugation.conjSq_mul_green_mul_transpose` asks only that the matrix be orthogonal.
**THE PAIR IS NOT REQUIRED TO BE AN EIGENPAIR**, and that is the whole difference from the previous
unit: a rotation that does not commute with the propagator is still carried to a linear symmetry,
just not to an isometric one.

**`infinite_setOf_linSym`** — so at **every** graph, **every** non-zero mass and at least two
vertices, `{L | L C Lᵀ = C}` is infinite.

**`det_injective_of_subsingleton`, `finite_setOf_linSym_of_subsingleton`,
`infinite_setOf_linSym_iff_nontrivial`** — **and two vertices is necessary, not merely
sufficient.** On one vertex the determinant is injective, and every linear symmetry has
`(det L)² = 1` because `det C ≠ 0`, so the set is contained in `{1, -1}`; on none it is a
singleton. **The hypothesis is therefore exactly `Nontrivial V`**, stated as an `iff`.

## What this changes elsewhere

`FieldSymmetryIndex.index_range_symHom_eq_zero` took the infinitude of the linear symmetries as a
hypothesis `hinf`. By the `iff` above that hypothesis **is** `Nontrivial V` at a non-zero mass, so
it is now an instance argument and the eigenvalue machinery drops out of
`index_range_symHom_eq_zero_of_simple` and `_line`. `FieldRotationNonIsometric`'s three
`infinite_linSym_quadForm` declarations are annotated in place as superseded (`ERRATUM 94`'s rule)
and are no longer used; their `infinite_nonIsometric` siblings are untouched, because there the
distinct eigenvalues are the point and not an accident.

## What is NOT here

**NO CARDINALITY, AND `Infinite` IS NOT A CARDINAL.** This says the set is not finite. It does not
say it has the cardinality of the continuum, which is true and is a different statement needing a
measure of the orthogonal group or an explicit `ℝ`-indexed injection into it rather than an
injection out of an interval. **Not attempted in this file**, no cost claimed (`ERRATUM 246`).

**NOTHING ABOUT THE ISOMETRIC SIDE.** The orthogonal matrices that also commute with the
propagator are the isometric symmetries, and whether *they* are infinite depends on the graph —
`FieldSymmetryFinite.finite_iff_lapMatrix` is the criterion and `FieldRotationCount`'s eigenpair
theorems are the constructions. **This file's circle is deliberately not that circle**: its
rotations are in a plane of coordinate vectors, which are eigenvectors of nothing in particular.

**NOTHING ABOUT A BLOCK.** Three of the four files quoted above need a circle inside one
block of a block-diagonal group, and this file's circle is in the plane of two coordinate vectors,
which may sit in different blocks. Restricting the construction to a block means choosing two
coordinates in the same block, which is a statement about the block decomposition and not about
the orthogonal group. **Not attempted here**, no cost claimed (`ERRATUM 246`).
⚠ **AND IT DOES NOT NEED TO BE, 2026-09-19** (`ERRATUM 653`): the first draft of this item ended
*each of the three files carries a dated note saying its own sentence is still unproved*, which was
**false**. `FieldBlockInfinite.infinite_symmetryMatrices_of_two_le_card_fib` and
`infinite_prod_unitaryGroup_of_two_le_card_fib` are those sentences, composed from theorems the
estate already held. **The fence above stands as a statement about this file** — it really does not
reach a block — and the three notes now cite the theorem instead of denying it.

**NO TOPOLOGY, NO DIMENSION, NO LIE STRUCTURE.** `|V| ≥ 2` makes the group infinite; that it is a
compact Lie group of dimension `|V|(|V|-1)/2` is standard and is not stated, invoked or needed.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. Counting
the symmetries of a finite-volume Gaussian field is knowing a shadow more exactly.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldLinSymInfinite

open Matrix GraphLaplacian FieldRotation FieldSqrtConjugation FieldSymmetryIso

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Two distinct coordinates are an orthonormal pair -/

/-- A coordinate vector has squared length `1`. -/
theorem single_dotProduct_self (i : V) :
    (Pi.single i (1 : ℝ)) ⬝ᵥ (Pi.single i (1 : ℝ)) = 1 := by
  rw [single_dotProduct, Pi.single_eq_same, one_mul]

/-- Two coordinate vectors at DISTINCT indices are orthogonal, and this is the only place `i ≠ j`
is used in the whole file. -/
theorem single_dotProduct_ne {i j : V} (hij : i ≠ j) :
    (Pi.single i (1 : ℝ)) ⬝ᵥ (Pi.single j (1 : ℝ)) = 0 := by
  rw [single_dotProduct, Pi.single_eq_of_ne hij, mul_zero]

/-! ## 2. A circle of orthogonal matrices, with no propagator in sight -/

/-- **THE UNIT CIRCLE'S WORTH OF ORTHOGONAL MATRICES IN THE PLANE OF ANY ORTHOGONAL PAIR OF EQUAL
NON-ZERO LENGTH.** `FieldRotation.rotMatrix_transpose_mul_self` supplies orthogonality from the
Pythagorean identity, `FieldRotationCount.rotMatrix_inj` reads the angle back off the matrix, and
`Real.injOn_cos` makes `Ioo 0 π` a set of distinct angles. -/
theorem infinite_setOf_orthogonal_of_pair {u v : V → ℝ} {n : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) :
    {A : Matrix V V ℝ | Aᵀ * A = 1}.Infinite := by
  have hinj : Set.InjOn (fun t : ℝ => rotMatrix u v n (Real.cos t) (Real.sin t))
      (Set.Ioo 0 Real.pi) := by
    intro a ha b hb hab
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩
      (FieldRotationCount.rotMatrix_inj hn huu hvv huv hab).1
  refine Set.Infinite.mono ?_ ((Set.Ioo_infinite Real.pi_pos).image hinj)
  rintro A ⟨t, -, rfl⟩
  exact rotMatrix_transpose_mul_self hn huu hvv huv (Real.cos_sq_add_sin_sq t)

/-- **THE ORTHOGONAL MATRICES OVER `ℝ^V` ARE INFINITE AS SOON AS `|V| ≥ 2`** — the sentence
`FieldAffineGroup`, `FieldBlockGroup` and `FieldBlockProduct` each assert and none proves. Two
distinct vertices give two orthonormal coordinate vectors and §2 does the rest. -/
theorem infinite_setOf_orthogonal [Nontrivial V] :
    {A : Matrix V V ℝ | Aᵀ * A = 1}.Infinite := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  exact infinite_setOf_orthogonal_of_pair one_ne_zero (single_dotProduct_self i)
    (single_dotProduct_self j) (single_dotProduct_ne hij)

/-- **THE SAME IN MATHLIB'S OBJECT.** `FieldSymmetryIso.mem_unitary_iff` is the bridge, kept over
`Matrix.orthogonalGroup` for the reason `ERRATUM 484` records. -/
theorem infinite_unitaryGroup [Nontrivial V] : Infinite (Matrix.unitaryGroup V ℝ) := by
  haveI : Infinite {A : Matrix V V ℝ | Aᵀ * A = 1} :=
    (infinite_setOf_orthogonal (V := V)).to_subtype
  refine Infinite.of_injective
    (fun A : {A : Matrix V V ℝ | Aᵀ * A = 1} =>
      (⟨A.1, mem_unitary_iff.mpr A.2⟩ : Matrix.unitaryGroup V ℝ)) ?_
  intro A B h
  exact Subtype.ext (congrArg (fun U : Matrix.unitaryGroup V ℝ => (U : Matrix V V ℝ)) h)

/-! ## 3. Conjugated, they are linear symmetries — and the pair need not be an eigenpair -/

/-- **CONJUGATION CARRIES THE CIRCLE INTO THE LINEAR SYMMETRIES**, and the only hypothesis it uses
is orthogonality: `FieldSqrtConjugation.conjSq_mul_green_mul_transpose` never looks at the
propagator's action on `u` or `v`. Compare `FieldRotationNonIsometric.infinite_linSym_quadForm`,
which asks in addition that `u` and `v` be eigenvectors at two distinct eigenvalues — needed for
its own *not an isometry* clause, and not for this conclusion. -/
theorem infinite_setOf_linSym_of_pair (hm : m ≠ 0) {u v : V → ℝ} {n : ℝ} (hn : n ≠ 0)
    (huu : u ⬝ᵥ u = n) (hvv : v ⬝ᵥ v = n) (huv : u ⬝ᵥ v = 0) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Infinite := by
  have hinj : Set.InjOn (fun t : ℝ => conjSq G m (rotMatrix u v n (Real.cos t) (Real.sin t)))
      (Set.Ioo 0 Real.pi) := by
    intro a ha b hb hab
    have hrot := FieldLinearClassified.conjSq_injective hm hab
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩
      (FieldRotationCount.rotMatrix_inj hn huu hvv huv hrot).1
  refine Set.Infinite.mono ?_ ((Set.Ioo_infinite Real.pi_pos).image hinj)
  rintro L ⟨t, -, rfl⟩
  exact conjSq_mul_green_mul_transpose hm
    (rotMatrix_transpose_mul_self hn huu hvv huv (Real.cos_sq_add_sin_sq t))

/-- **AT EVERY GRAPH, AT EVERY NON-ZERO MASS, ON AT LEAST TWO VERTICES.** No eigenvalue, no
eigenvector, no adjacency and no spectrum. -/
theorem infinite_setOf_linSym [Nontrivial V] (hm : m ≠ 0) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Infinite := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  exact infinite_setOf_linSym_of_pair hm one_ne_zero (single_dotProduct_self i)
    (single_dotProduct_self j) (single_dotProduct_ne hij)

/-! ## 4. And two vertices is necessary -/

/-- On one vertex or none the determinant determines the matrix: `Matrix.det_unique` reads it off
the single entry, and on an empty index type there is only one matrix to begin with. -/
theorem det_injective_of_subsingleton [Subsingleton V] :
    Function.Injective (Matrix.det : Matrix V V ℝ → ℝ) := by
  rcases isEmpty_or_nonempty V with hV | hV
  · intro A B _
    ext x y
    exact (hV.false x).elim
  · haveI : Unique V := uniqueOfSubsingleton (Classical.arbitrary V)
    intro A B h
    rw [Matrix.det_unique, Matrix.det_unique] at h
    ext x y
    rw [Subsingleton.elim x default, Subsingleton.elim y default]
    exact h

/-- **SO ON FEWER THAN TWO VERTICES THE LINEAR SYMMETRIES ARE FINITE** — at most `1` and `-1`.
Taking determinants in `L C Lᵀ = C` gives `(det L)² det C = det C`, and `det C ≠ 0` because the
propagator is positive definite, so `(det L)² = 1`; with the determinant injective that pins `L`
to two values. -/
theorem finite_setOf_linSym_of_subsingleton [Subsingleton V] (hm : m ≠ 0) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Finite := by
  have hg : (green G m).det ≠ 0 := ((green_posDef G hm).det_pos).ne'
  refine Set.Finite.of_finite_image ?_ det_injective_of_subsingleton.injOn
  refine Set.Finite.subset ((Set.finite_singleton (-1 : ℝ)).insert (1 : ℝ)) ?_
  rintro r ⟨L, hL, rfl⟩
  have h := congrArg Matrix.det hL
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have h2 : L.det * L.det = 1 := by
    refine mul_right_cancel₀ hg ?_
    rw [one_mul]
    linear_combination h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact mul_self_eq_one_iff.mp h2

/-- **THE HYPOTHESIS IS EXACTLY TWO VERTICES.** At a non-zero mass the linear symmetry group is
infinite **iff** `V` is non-trivial — so `FieldSymmetryIndex.index_range_symHom_eq_zero`'s `hinf`
was an instance argument wearing a proof obligation. -/
theorem infinite_setOf_linSym_iff_nontrivial (hm : m ≠ 0) :
    {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Infinite ↔ Nontrivial V := by
  refine ⟨fun h => ?_, fun _ => infinite_setOf_linSym hm⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact absurd (finite_setOf_linSym_of_subsingleton hm) h
  · exact hV

end FieldLinSymInfinite
