import FieldBlockInfinite
import FieldLinSymInfinite
import Mathlib.Analysis.Real.Cardinality

/-!
# Which infinity: the symmetry groups have the cardinality of the continuum

**SEVEN FILES SAY A GROUP IS `Infinite` AND DECLINE TO SAY WHICH INFINITY, AND THIS FILE ANSWERS
EXACTLY ONE OF THEM.** Counted with newlines flattened (`ERRATUM 652`'s codicil), in three
phrasings: *nothing about which infinity* in `CompleteFieldSymmetry`, `FieldSymmetryFinite` and
`MultipartiteEigenspace`; *`Infinite` is not a cardinal* in `FieldBlockGroup`, `FieldBlockProduct`
and `FieldBlockInfinite`; *it does not say it has the cardinality of the continuum* in
`FieldLinSymInfinite`.

**ONLY THE LAST IS THIS FILE'S SUBJECT.** `FieldLinSymInfinite`'s sentence is about the FULL
orthogonal group of `ℝ^V` and the Gaussian field's LINEAR symmetries, which is what is computed
below. **The other six are about the ISOMETRIC side** — the symmetry group of a degenerate
eigenvalue, the block-diagonal group, the product over eigenvalues — and three of them say so in
as many words: *the symmetry group of a degenerate eigenvalue contains a circle, and that is not
stated.* **This file does not state it**, and says so in its own fence below.

`ERRATUM 653` wrote the rule a day before this unit: *a fence is discharged by a theorem with the
same subject, not the same shape.* The first draft of this header claimed six files and named three
that do not carry the sentence at all. The rule's author walked into it again inside twenty-four
hours, which is recorded in `ERRATUM 654` as evidence about the rule rather than about the author.

**It was a rung.** What made it look otherwise is that the estate had never needed a cardinal
before, so nothing here imported `Mathlib.Analysis.Real.Cardinality` — and the two facts the proof
turns on, `Cardinal.mk_Ioo_real` and `Cardinal.power_nat_eq`, are both in Mathlib and neither is
deep. The route is the one the `Infinite` proofs already walk, with `Set.Infinite` replaced by a
cardinal at each step.

## What is proved

**`mk_setOf_orthogonal`** — `#{A : Matrix V V ℝ | Aᵀ * A = 1} = 𝔠` for `Nontrivial V`. Both
bounds come from objects already in the estate. **Below**: the circle of rotations in the plane of
two coordinate vectors is injective on `Ioo 0 π` — `FieldRotationCount.rotMatrix_inj` with
`Real.injOn_cos`, which is `FieldLinSymInfinite`'s own argument — and `Cardinal.mk_Ioo_real` makes
that interval `𝔠`. **Above**: the set sits inside `Matrix V V ℝ`, which is `V × V → ℝ`, of
cardinality `𝔠 ^ (|V| · |V|)`, and `Cardinal.power_nat_eq` collapses a finite positive power of
`𝔠` to `𝔠`.

**`mk_setOf_linSym`** — the same for the Gaussian field's linear symmetries
`{L | L C Lᵀ = C}`, at every graph and every non-zero mass. The lower bound conjugates the same
circle by the propagator's square root, which is injective by
`FieldLinearClassified.conjSq_injective`; the upper bound is the same ambient matrix count.

**`mk_unitaryGroup`** — and in Mathlib's object, `#(Matrix.unitaryGroup V ℝ) = 𝔠`, across
`FieldSymmetryIso.mem_unitary_iff`.

## What this closes, and in what words

**One sentence, in one file.** `FieldLinSymInfinite`'s *it does not say it has the cardinality of
the continuum* is no longer true of the estate, and that file carries a dated note. The
`UNLOCK_WATCHLIST` item's residue (3) — *six files say `Infinite` and none says which infinity* —
is closed **for the linear side and not for the isometric one**, and the item is re-scoped rather
than closed.

**The other six files' conclusions are untouched and their sentences remain true of their own
objects.** There is still no count in the sense any of them refuses: no formula, no `Nat.card`,
nothing that grows with the graph. `FieldBlockInfinite`, which owns the item, carries a dated note
recording what is answered and what is not; the remaining five are left alone, because a note
saying *a theorem about a different group exists* is worth writing once, where the item lives, and
not five times (`ERRATUM 651`).

## What is NOT here

**NOTHING ABOUT THE ISOMETRIC SIDE'S CARDINALITY IN THE DEGENERATE CASE.** When the spectrum is
simple the isometric group is finite with `2 ^ |V|` elements and the question does not arise; when
it is degenerate `FieldBlockInfinite` says the group is infinite, and **this file does not compute
that cardinal**. The block-diagonal group's size depends on the multiplicities, and the lower bound
here is a circle inside one block — enough for `𝔠` in fact, but **no such statement is made in
this file and no such argument is written here** (2026-09-19; the locality is deliberate, since
this paragraph knows what this unit did and not what the estate contains — `ERRATUM 293`).
**Not attempted, and the reason is scope rather than difficulty**: the residue this file exists to
close was about the LINEAR side, which is what **one** of the seven sentences is about — the other
six are the isometric side, and they stand.

**NO CARDINAL ARITHMETIC BEYOND ONE POWER.** `Cardinal.power_nat_eq` is used once. No claim is made
about `𝔠 ^ 𝔠`, about cofinality, or about anything the continuum hypothesis could touch — the
statement `#G = 𝔠` is CH-free and says nothing about what lies between `ℵ₀` and `𝔠`.

**THE STATEMENTS ARE IN UNIVERSE 0, AND THAT IS FORCED RATHER THAN CHOSEN.** `Cardinal.continuum`
is a `Cardinal.{0}`, so `#(Matrix V V ℝ) = 𝔠` does not even typecheck for `V : Type*` — it would
have to be `lift 𝔠`, which is a statement about a lifted cardinal and not the one the six sentences
name. This file therefore takes `V : Type`, where every concrete graph in this estate already lives
(`Fin n`, `BoxGraph.Site d n`, the paw's vertex type). **The general-universe form is not attempted
and is a different statement**, not a weaker one (`ERRATUM 246`).

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense — a
sense this file's `continuum` has nothing to do with, and the collision of words is worth one
sentence so nobody reads a wall as having moved.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSymmetryContinuum

open Matrix GraphLaplacian FieldRotation FieldSqrtConjugation FieldSymmetryIso Cardinal

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The ambient bound: a matrix space over `ℝ` is the continuum -/

omit [Fintype V] [DecidableEq V] in
/-- **`#(Matrix V V ℝ) = 𝔠` on a non-empty index type.** `Matrix V V ℝ` is `V → V → ℝ`, so its
cardinality is `𝔠` raised to the finite power `|V| · |V|`, and `Cardinal.power_nat_eq` collapses
any finite positive power of an infinite cardinal. -/
theorem mk_matrix [Finite V] [Nonempty V] : #(Matrix V V ℝ) = 𝔠 := by
  have hcard : #(Matrix V V ℝ) = #(V × V → ℝ) :=
    mk_congr ((Equiv.curry V V ℝ).symm)
  rw [hcard, mk_arrow, mk_real]
  simp only [lift_id]
  refine Cardinal.pow_eq aleph0_le_continuum ?_ (Cardinal.lt_aleph0_of_finite _)
  exact Cardinal.one_le_iff_ne_zero.mpr (Cardinal.mk_ne_zero (V × V))

/-! ## 2. The lower bound: a circle's worth is already `𝔠` -/

/-- **THE CIRCLE OF ROTATIONS HAS CARDINALITY `𝔠`.** `Cardinal.mk_image_eq_of_injOn` with the
injectivity `FieldLinSymInfinite` proves, and `Cardinal.mk_Ioo_real` for the interval. -/
theorem continuum_le_of_injOn {β : Type} {f : ℝ → β} {S : Set β}
    (hinj : Set.InjOn f (Set.Ioo 0 Real.pi)) (hsub : f '' Set.Ioo 0 Real.pi ⊆ S) :
    𝔠 ≤ #S := by
  have himg : #(f '' Set.Ioo 0 Real.pi) = 𝔠 :=
    (mk_image_eq_of_injOn f _ hinj).trans (mk_Ioo_real Real.pi_pos)
  calc 𝔠 = #(f '' Set.Ioo 0 Real.pi) := himg.symm
    _ ≤ #S := mk_le_mk_of_subset hsub


/-! ## 3. The orthogonal group, and the linear symmetries, are the continuum -/

/-- **`#{A | Aᵀ A = 1} = 𝔠` as soon as `|V| ≥ 2`.** Below by the circle of rotations in the plane
of two coordinate vectors — `FieldLinSymInfinite`'s construction, read for its cardinality instead
of its infinitude — and above by the ambient matrix space. -/
theorem mk_setOf_orthogonal [Nontrivial V] :
    #{A : Matrix V V ℝ | Aᵀ * A = 1} = 𝔠 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  refine le_antisymm ((mk_set_le _).trans (le_of_eq mk_matrix)) ?_
  refine continuum_le_of_injOn (f := fun t : ℝ =>
    rotMatrix (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) 1 (Real.cos t) (Real.sin t)) ?_ ?_
  · intro a ha b hb hab
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩
      (FieldRotationCount.rotMatrix_inj one_ne_zero
        (FieldLinSymInfinite.single_dotProduct_self i)
        (FieldLinSymInfinite.single_dotProduct_self j)
        (FieldLinSymInfinite.single_dotProduct_ne hij) hab).1
  · rintro A ⟨t, -, rfl⟩
    exact rotMatrix_transpose_mul_self one_ne_zero
      (FieldLinSymInfinite.single_dotProduct_self i)
      (FieldLinSymInfinite.single_dotProduct_self j)
      (FieldLinSymInfinite.single_dotProduct_ne hij) (Real.cos_sq_add_sin_sq t)

/-- **AND IN MATHLIB'S OBJECT.** `FieldSymmetryIso.mem_unitary_iff` is the only step. -/
theorem mk_unitaryGroup [Nontrivial V] : #(Matrix.unitaryGroup V ℝ) = 𝔠 := by
  rw [← mk_setOf_orthogonal (V := V)]
  exact mk_congr (Equiv.subtypeEquivRight fun _ => mem_unitary_iff)

/-- **THE GAUSSIAN FIELD'S LINEAR SYMMETRIES ARE THE CONTINUUM**, at every graph and every
non-zero mass on two or more vertices. The same circle, conjugated by the propagator's square
root, which is injective by `FieldLinearClassified.conjSq_injective` and lands in the symmetries by
`FieldSqrtConjugation.conjSq_mul_green_mul_transpose`. -/
theorem mk_setOf_linSym [Nontrivial V] (hm : m ≠ 0) :
    #{L : Matrix V V ℝ | L * green G m * Lᵀ = green G m} = 𝔠 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  refine le_antisymm ((mk_set_le _).trans (le_of_eq mk_matrix)) ?_
  refine continuum_le_of_injOn (f := fun t : ℝ => conjSq G m
    (rotMatrix (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) 1 (Real.cos t) (Real.sin t))) ?_ ?_
  · intro a ha b hb hab
    have hrot := FieldLinearClassified.conjSq_injective hm hab
    exact Real.injOn_cos ⟨ha.1.le, ha.2.le⟩ ⟨hb.1.le, hb.2.le⟩
      (FieldRotationCount.rotMatrix_inj one_ne_zero
        (FieldLinSymInfinite.single_dotProduct_self i)
        (FieldLinSymInfinite.single_dotProduct_self j)
        (FieldLinSymInfinite.single_dotProduct_ne hij) hrot).1
  · rintro L ⟨t, -, rfl⟩
    exact conjSq_mul_green_mul_transpose hm
      (rotMatrix_transpose_mul_self one_ne_zero
        (FieldLinSymInfinite.single_dotProduct_self i)
        (FieldLinSymInfinite.single_dotProduct_self j)
        (FieldLinSymInfinite.single_dotProduct_ne hij) (Real.cos_sq_add_sin_sq t))

end FieldSymmetryContinuum
