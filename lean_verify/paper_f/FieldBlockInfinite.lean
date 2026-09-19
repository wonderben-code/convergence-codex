import FieldSymmetryFinite
import FieldBlockProduct

/-!
# A block of size two, and the sentence four files have been discharging by reconstruction

**THIS FILE EXISTS BECAUSE OF A DEFECT IN THE UNIT BEFORE IT, AND THAT IS THE USEFUL PART**
(`ERRATUM 653`). `FieldLinSymInfinite` proved the FULL orthogonal group of `ℝ^V` infinite for two
or more vertices, and then wrote dated notes in `FieldBlockGroup`, `FieldBlockProduct` and
`FieldEigenMultiplicity` saying that **their** sentences — a **block-diagonal** orthogonal group,
or a **factor** of a product, is infinite as soon as one block has size two — *stay unproved*.
**That was false.** The estate proves it, and has since `FieldSymmetryFinite` was written:

* `FieldSymmetryFinite.infinite_symmetryMatrices_of_two_le_finrank` — a **degenerate eigenvalue**
  makes the symmetries infinite, at every finite graph.
* `FieldBlockProduct.card_fib_eq_finrank_eigenspace` — a **block's size IS** the eigenspace
  dimension, not merely equinumerous with it.
* `FieldBlockProduct.symmetry_mulEquiv_prod` — the symmetries **are** `∏ᵢ O(dᵢ)`, as a `MulEquiv`.

So the sentence is a two-step composition of theorems already held. **What was true in the note is
the narrow part**: `FieldLinSymInfinite`'s circle turns two coordinate vectors that may sit in
different blocks, so *that* theorem does not prove it — and it does not need to, because this one
does.

**AND THE COMPOSITION WAS NOT STATED ANYWHERE.** Grepped before writing: no declaration in
`paper_f` says the block form or the product form is `Infinite`, and
`infinite_symmetryMatrices_of_two_le_finrank` **had no consumer at all** — one docstring mention in
`FieldSymmetryCount` and one internal use inside `finite_iff_injective`. A theorem nobody cites is
exactly the kind a later unit re-declares missing, which is what happened. This file is its first
consumer, and the four fences can now cite a name instead of asking a reader to rebuild the
argument.

## What is proved

**`infinite_symmetryMatrices_of_two_le_card_fib`** — **A BLOCK OF SIZE TWO OR MORE MAKES THE
SYMMETRIES INFINITE**, at every finite graph and every non-zero mass, with the hypothesis stated
on the **block** (`Fintype.card (Fib …)`) rather than on an eigenspace dimension, because the block
is what `FieldBlockGroup` and `FieldBlockProduct` talk about.

**`infinite_symmetrySubmonoid_of_two_le_card_fib`** — the same across the `Set`/`Submonoid`
boundary, which is the step the product form needs and which nothing had taken.

**`infinite_prod_unitaryGroup_of_two_le_card_fib`** — **`∏_c O(Fib c)` IS INFINITE as soon as one
factor's index type has two elements**, carried over `symmetry_mulEquiv_prod`. This is
`FieldEigenMultiplicity`'s *`∏ᵢ O(dᵢ)` is infinite as soon as some `dᵢ ≥ 2`*, as a theorem.

**`infinite_symmetryMatrices_iff_not_injective`, `infinite_symmetryMatrices_iff_lapMatrix`** — and
the sharp form, which is one `not_congr` away from `FieldSymmetryFinite`'s criterion and had not
been written down in the positive direction: the symmetries are infinite **iff** the propagator's
spectrum is **not** simple, and in graph vocabulary **iff** some Laplacian eigenspace is more than
a line.

## What is NOT here

**NO CARDINALITY, AND THAT IS NOT A HEDGE — IT IS THE SAME FENCE THE FOUR FILES ALREADY CARRY.**
`Infinite` is not a cardinal. That these groups have the cardinality of the continuum is true,
different, and not attempted (`ERRATUM 246`). The four fences' conclusions — *no number, and there
is not going to be one* — are **untouched** by this file; what changes is that their stated REASON
is now a theorem with a name.
⚠ **AND THE CARDINAL IS NOW PROVED ON THE OTHER SIDE ONLY, 2026-09-19** (`ERRATUM 654`).
`FieldSymmetryContinuum` proves `𝔠` for the FULL orthogonal group and for the Gaussian field's
LINEAR symmetries. **It does not prove it for the groups this sentence is about** — the
block-diagonal group and the product over eigenvalues, whose infinitude comes from a circle inside
ONE BLOCK. The lower bound there would need that circle rather than the coordinate-plane one, which
is the same distinction this file's own §1 draws between the ambient group and a block, and it is
not drawn a second time by accident: **a theorem with the same shape and a different subject does
not discharge this sentence**, which is `ERRATUM 653`'s rule and `ERRATUM 654`'s repetition of it.
**So this sentence stands**, and the watchlist item's residue (3) is re-scoped to the isometric side
rather than closed.

**THE PRODUCT FORM'S `iff` IS HERE, AND THE ESTIMATE THAT NAMED IT WAS WRONG ABOUT THE ROUTE.**
`infinite_prod_unitaryGroup_iff_not_injective` is §4. The first draft of this item called it *not
attempted* and estimated one `Finite.of_equiv` across `symmetry_mulEquiv_prod`; what it actually
took was **not** a transport at all. `FieldSymmetryFinite.finite_symmetryMatrices_of_injective`
proves the product finite as a `haveI` **inside its own proof** and does not export it, so the
finite half needed exporting rather than carrying — the equiv is not used. The estimate was a
climb in the wrong direction, which is why `ERRATUM 194` says naming a route is not costing it.

**THE CALL SITES ARE REWIRED, AND THERE WERE TWO OF THEM RATHER THAN THREE.**
`UnbalancedMultipartiteTwins.infinite_symmetryMatrices_of_three_le` and `_of_two_equal_parts` each
used to open `intro hfin`, apply `FieldSymmetryFinite.finite_iff_lapMatrix` in the finite direction
and finish with `omega` — **the positive direction re-derived by hand**. Both now `rw` the `iff`
above and exhibit the eigenspace instead of reaching it by contradiction.
⚠ **THE COUNT WAS WRONG WHEN THIS FILE FIRST SAID IT, 2026-09-19** (`ERRATUM 450`'s rule applied
to my own sentence): the first draft named **three** sites, counting `_equipartite_family`, which
proves nothing by hand — it is a one-line call to `_of_two_equal_parts`. Two hand proofs, one
consumer. The rewiring is in the same commit as this correction.

**NOTHING ABOUT WHICH GRAPHS HAVE A DEGENERATE EIGENVALUE.** That is the watchlist's open question
*which finite graphs have a simple Laplacian spectrum*, and this file consumes it rather than
answering it.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldBlockInfinite

open Matrix GraphLaplacian FieldRotationCount FieldBlockDiagonal FieldBlockProduct
open FieldSymmetryGroup

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A block of size two makes the symmetries infinite -/

/-- **THE SENTENCE FOUR FILES ASSERT, STATED ON THE BLOCK.** `card_fib_eq_finrank_eigenspace` says
the block's size is the eigenspace dimension — an equality of numbers, not a bijection to be
chased — so this is `FieldSymmetryFinite.infinite_symmetryMatrices_of_two_le_finrank` with its
hypothesis rewritten into the vocabulary of the product decomposition. -/
theorem infinite_symmetryMatrices_of_two_le_card_fib (hm : m ≠ 0)
    {c : Lev (eigMu G m hm)} (h : 2 ≤ Fintype.card (Fib (eigMu G m hm) (c : ℝ))) :
    (symmetryMatrices G m).Infinite := by
  refine FieldSymmetryFinite.infinite_symmetryMatrices_of_two_le_finrank hm (μ := (c : ℝ)) ?_
  rw [← card_fib_eq_finrank_eigenspace hm c]
  exact h

/-- **ACROSS THE `Set`/`Submonoid` BOUNDARY**, which is the step the product form needs.
`symmetrySubmonoid`'s carrier is literally `symmetryMatrices`, so the lift is the identity on
matrices and injective by `Subtype.ext`. -/
theorem infinite_symmetrySubmonoid_of_two_le_card_fib (hm : m ≠ 0)
    {c : Lev (eigMu G m hm)} (h : 2 ≤ Fintype.card (Fib (eigMu G m hm) (c : ℝ))) :
    Infinite (symmetrySubmonoid G m) := by
  haveI : Infinite (symmetryMatrices G m) :=
    (infinite_symmetryMatrices_of_two_le_card_fib hm h).to_subtype
  refine Infinite.of_injective
    (fun R : symmetryMatrices G m => (⟨R.1, R.2⟩ : symmetrySubmonoid G m)) ?_
  intro a b hab
  exact Subtype.ext (congrArg Subtype.val hab)

/-! ## 2. Hence the product of orthogonal groups is infinite -/

/-- **`∏_c O(Fib c)` IS INFINITE AS SOON AS ONE FACTOR'S INDEX TYPE HAS TWO ELEMENTS.** This is
`FieldEigenMultiplicity`'s *`∏ᵢ O(dᵢ)` is infinite as soon as some `dᵢ ≥ 2`* as a theorem rather
than a sentence; the transport is `FieldBlockProduct.symmetry_mulEquiv_prod`, which is a `MulEquiv`
and so injective. -/
theorem infinite_prod_unitaryGroup_of_two_le_card_fib (hm : m ≠ 0)
    {c : Lev (eigMu G m hm)} (h : 2 ≤ Fintype.card (Fib (eigMu G m hm) (c : ℝ))) :
    Infinite (∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) := by
  haveI : Infinite (symmetrySubmonoid G m) :=
    infinite_symmetrySubmonoid_of_two_le_card_fib hm h
  exact Infinite.of_injective (symmetry_mulEquiv_prod hm)
    (symmetry_mulEquiv_prod hm).injective

/-! ## 3. The sharp form, which is a `not_congr` nobody had written -/

/-- **THE SYMMETRIES ARE INFINITE IF AND ONLY IF THE SPECTRUM IS NOT SIMPLE.**
`FieldSymmetryFinite.finite_iff_injective` is the estate's criterion in the finite direction;
`Set.Infinite` is `¬ Set.Finite`, so the positive direction is one `not_congr` and is stated here
because a reader looking for *when is it infinite* should not have to negate a criterion. -/
theorem infinite_symmetryMatrices_iff_not_injective (hm : m ≠ 0) :
    (symmetryMatrices G m).Infinite ↔ ¬ Function.Injective (eigMu G m hm) :=
  not_congr (FieldSymmetryFinite.finite_iff_injective hm)

/-- **AND IN GRAPH VOCABULARY.** No propagator on the right-hand side: the symmetries are infinite
**iff** some eigenspace of the graph's Laplacian is more than a line. -/
theorem infinite_symmetryMatrices_iff_lapMatrix (hm : m ≠ 0) :
    (symmetryMatrices G m).Infinite ↔ ∃ ν : ℝ, 1 < Module.finrank ℝ
      (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) := by
  rw [Set.Infinite, FieldSymmetryFinite.finite_iff_lapMatrix hm, not_forall]
  exact exists_congr fun _ => not_le

/-! ## 4. The product form's `iff`, and a fact the estate proved inside a proof -/

/-- **THE PRODUCT IS FINITE WHEN THE SPECTRUM IS SIMPLE.** `FieldSymmetryFinite` proves exactly
this **inside** `finite_symmetryMatrices_of_injective`, as a `haveI` two lines before its own
conclusion, and does not export it — so the estate held the fact and no statement carried it.
That is the third instance in this cluster of the shape `ERRATUM 653` records: something true,
used once, and unreachable by name. The proof here is the same two instances: every fibre is a
subsingleton, so every factor is finite, so `Pi.finite` applies. -/
theorem finite_prod_unitaryGroup_of_injective (hm : m ≠ 0)
    (hsimple : Function.Injective (eigMu G m hm)) :
    Finite (∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) := by
  haveI : ∀ c : Lev (eigMu G m hm), Subsingleton (Fib (eigMu G m hm) (c : ℝ)) :=
    fun c => FieldSymmetryFinite.subsingleton_fib hsimple _
  haveI : ∀ c : Lev (eigMu G m hm), Finite (Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) :=
    fun _ => FieldSymmetryFinite.finite_unitaryGroup_of_subsingleton
  exact Pi.finite

/-- **SO THE PRODUCT IS INFINITE IF AND ONLY IF THE SPECTRUM IS NOT SIMPLE**, which is the residue
this file's own `What is NOT here` named and left. The forward direction is the theorem above
against `not_finite`; the backward one keeps the range witness that
`FieldSymmetryFinite.exists_two_le_finrank_of_not_injective` discards: a repeated eigenvalue gives
two distinct points of **one named fibre**, so the block is exhibited, not quantified over. -/
theorem infinite_prod_unitaryGroup_iff_not_injective (hm : m ≠ 0) :
    Infinite (∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) ↔
      ¬ Function.Injective (eigMu G m hm) := by
  refine ⟨fun hinf hinj => ?_, fun hns => ?_⟩
  · have hfin := finite_prod_unitaryGroup_of_injective hm hinj
    rw [← not_finite_iff_infinite] at hinf
    exact hinf hfin
  · obtain ⟨i, j, hval, hne⟩ := Function.not_injective_iff.1 hns
    refine infinite_prod_unitaryGroup_of_two_le_card_fib hm
      (c := ⟨eigMu G m hm i, ⟨i, rfl⟩⟩) ?_
    refine Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨i, rfl⟩, ⟨j, hval.symm⟩, ?_⟩
    exact fun hEq => hne (congrArg Subtype.val hEq)

end FieldBlockInfinite
