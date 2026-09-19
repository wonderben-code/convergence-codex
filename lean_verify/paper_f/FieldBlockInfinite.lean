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

**NO IFF FOR THE PRODUCT FORM.** The `iff` above is about `symmetryMatrices`. Transporting the
finite half to the product needs `FieldSymmetryFinite.finite_symmetryMatrices_of_injective` carried
across the same `MulEquiv`, which is a further composition. **Not attempted, and the cost is
estimated rather than claimed** (`ERRATUM 246`): one `Finite.of_equiv` in the direction
`FieldSymmetryFinite` already uses at line 174, so a rung rather than a climb — which is exactly
why it is named here instead of left to be noticed.

**THE `iff` HAS THREE CALL SITES WAITING AND THEY ARE NOT REWIRED HERE.**
`UnbalancedMultipartiteTwins.infinite_symmetryMatrices_of_three_le`,
`_of_two_equal_parts` and `_equipartite_family` each prove an infinitude by opening `intro hfin`,
applying `FieldSymmetryFinite.finite_iff_lapMatrix` in the finite direction and finishing with
`omega` — **the positive direction re-derived by hand, three times**, which is the lemma
`infinite_symmetryMatrices_iff_lapMatrix` above now is. Rewiring them is not a substitution:
their proofs use the universally quantified bound to reach a contradiction and would have to be
restructured to produce a witness instead, and that file would need a new import. **Not attempted
here**, no cost claimed (`ERRATUM 246`), and the three sites are named so the next unit does not
have to find them.

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

end FieldBlockInfinite
