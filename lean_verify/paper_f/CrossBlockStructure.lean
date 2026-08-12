import CrossPosSemidef

/-!
# The coupling hypothesis is a combinatorial condition on the cut

`IndefiniteCoupling`'s header, written when the coupling hypothesis was first shown to be more
than the diagonal condition, ends with a sentence that has stood unanswered since:

> *"reducing `hcross` to a PSD check is exact but is linear algebra per graph rather than a
> combinatorial criterion, and finding one is NOT ATTEMPTED."*

This file attempts it, and the criterion exists. **`hcross` holds if and only if the cut edges
form disjoint blocks** — a bounded statement about vertices and adjacency, with no vectors, no
mass, no eigenvalues and no real numbers in it at all.

## The criterion

Write `p ~ q` for `p ∈ H`, `q ∈ H` and `G.Adj p (θ q)`: `p` is joined to the mirror image of `q`.
`IsCrossBlock` asks two things of that relation:

* **loop** — if `p ~ q` for any `q`, then `p ~ p`: a half-site with any cross-neighbour is joined
  to *its own* mirror image;
* **trans** — `p ~ q` and `q ~ r` give `p ~ r`.

Together with the symmetry `~` already has (`CrossFormMatrix.adj_cross_comm`, which is where
`IsRefl` is spent) these say `~` is an equivalence relation on the half-sites it touches. So the
cut, viewed through the mirror, is a disjoint union of complete blocks.

`hcross_iff_isCrossBlock`: **that is exactly `hcross`**, on every graph with a mirror reflection.

## And the criterion is one clause, not two

**The adversarial pass on this file killed half of its own headline.** Under `IsRefl` the cut
relation is symmetric, so `p ~ q` gives `q ~ p`, and transitivity at `(p, q, p)` gives `p ~ p`:
**the `loop` clause follows from `trans`** (`isCrossBlock_of_trans`). The two-field structure is
kept because "the cut is in blocks" is what a reader should see, but the content is one line:

`hcross_iff_cross_trans`: **the coupling hypothesis is transitivity of the cut relation, and
nothing else.**

That was found by attacking the definition after it was proved correct, not while writing it, and
it is recorded here rather than quietly absorbed because the redundant clause is the kind of
thing a criterion is judged on.

## Why it is true, and where it comes from

`CrossPosSemidef` proved that a symmetric `0/1` matrix nonnegative on the sum-zero vectors of the
half is positive semidefinite, by showing the relation `C · · = 1` is an equivalence on the block
where the diagonal is `1` and then writing `C` as a weighted sum of rank-one class projectors.
**The equivalence relation was the mechanism, not the statement.** This file promotes it: for a
symmetric `0/1` matrix supported in `H`,

    positive semidefinite  ⟺  nonnegative on sum-zero vectors  ⟺  a block-ones matrix

(`posSemidef_iff_isBlockOnes`, and the three-way statement `three_tests_agree`). The cross matrix
is symmetric and `0/1`, so the criterion transfers verbatim to the graph.

## What this buys, concretely

The old test was `Matrix.PosSemidef (crossMatrix G θ H)` — exact, but a quantifier over `V → ℝ`.
The new one is a quantifier over vertices, so on a finite graph **it is decidable**, and that is
exhibited rather than asserted: `instDecidableIsCrossBlock` is a real instance, built from
`isCrossBlock_iff_bounded`, and both worked examples are closed by `decide` alone.

* `IndefiniteCoupling.bipGraph` satisfies it, as one block of size two, and is **not** diagonal
  (`IndefiniteCoupling.cross_not_diagonal`) — `isCrossBlock_bipGraph`, by `decide`.
* `IndefiniteCoupling.crossGraph` fails it — `not_isCrossBlock_crossGraph`, by `decide` — and the
  file names the failing triple: `0 ~ 1`, `1 ~ 0`, and `0` not joined to `2 = ρ 0`, so
  transitivity fails at `(0, 1, 0)` (`crossGraph_failing_triple`). The matching `0–3`, `1–2`
  pairs each half-site with the *other* one's mirror, which is precisely a non-block cut.

So the estate's original sufficient condition — the cut is diagonal — is exactly the
**all-blocks-are-singletons** case (`isCrossBlock_of_cross_diag`), and `bipGraph` witnesses that
the containment is strict. The three conditions line up as

    cut diagonal  ⊊  cut in blocks  =  hcross  ⊊  (no condition)

with the first inclusion strict by `bipGraph` and the second by `crossGraph`.

## §4 — and then the criterion pays a second time: the coupling in closed form

`PROOF_STRATEGY` §3 says to retry the next rung before banking the last, and the block structure
carries more than a yes/no. On a block cut the coupling is not merely nonpositive, it is

    crossForm w  =  − ∑ over blocks of (block sum of w)²

(`crossForm_eq_neg_sum_cls_sq`) — an **identity**, with `hcross` as the trivial reading of it.
Two things follow that the inequality could not give:

* **the coupling's kernel is combinatorial.** `crossForm_eq_zero_iff`: the form vanishes at `w`
  exactly when every block sum of `w` vanishes. One linear condition per block, and the
  degeneracy of the coupling is therefore the number of blocks. `crossForm_neg_iff` is the
  contrapositive, and it is what a strictness argument wants.
* **an existing estate theorem is strengthened.** `IndefiniteCoupling.hcross_bip` says the
  coupling on `K₂,₂` is `≤ 0`. It is `−(w 0 + w 1)²` exactly (`crossForm_bipGraph_exact`), and it
  vanishes precisely on the antisymmetric vectors of the half (`crossForm_bipGraph_zero_iff`) —
  the one block of size two that `isCrossBlock_bipGraph` found, read as a linear condition.

The `K₂,₂` value is proved **twice by different routes** and they agree:
`crossForm_eq_neg_sq_of_complete` derives it straight from
`GraphMirrorReflection.crossForm_eq_neg_adj` with no block machinery at all, which is a check on
the closed form rather than a corollary of it.

## §5 — and the kernel is what the strictness machinery was asking for

`StrictBiconditional.strict_iff_crossForm_neg_on_reachKernel` closes strictness on *the coupling
is strictly negative on the reach kernel*. §4 says what strict negativity is, so on a block cut
(`strict_iff_reachKernel_has_nonzero_block_sum`):

> **strict exactly when the reach kernel meets the all-block-sums-zero subspace only at `0`.**

The quadratic condition is gone; both sides are conjunctions of linear equations.
`not_strict_of_reachKernel_block_sums_zero` is the same fact in the form a search consumes — one
nonzero vector in the reach kernel with all block sums zero refutes strictness.

**This is a reformulation and is not claimed to decide any graph.** The reach kernel is the other
half of the condition and nothing here computes it; what changed is that the coupling half is now
linear.

## §6 — and the item §5 opened is answered on its own named target

§5's watchlist leg said the next question is a graph with a block of size bigger than one, named
`K₂,₂` as the first target, and reduced it to a two-by-two computation nobody had done. It is done
here, and the answer is **`K₂,₂` is reflection positive and NOT strictly so**, at every nonzero
mass — which the estate did not know, `WALLS` W1's sharpness line covering the box, the torus and
the lattice `def` and nothing else.

The reason is the cleanest possible instance of §5. `bipGraph_massive_mulVec_out`: on this graph
the operator's row at either mirror site reads `−(v 0 + v 1)`. **So the reach condition and the
block's linear condition are the same equation**, the two subspaces of §5 coincide rather than
meeting at `0`, and every sum-zero vector on the half is isotropic
(`bipGraph_inReachKernel_of_sum_zero`, `bipGraph_supportedIsotropic`, `bipGraph_not_strict`).

The witness is `IndefiniteCoupling.wpos = ![1, −1, 0, 0]` — **the same vector that refutes `hcross`
on `crossGraph`**, doing the opposite job here. `the_two_graphs_fail_differently` puts the two side
by side: same reflection, same half, same mass; one is not reflection positive at all, the other is
and is degenerate.

## §7 — and then a clause of the estate's own definition turns out to be free

Retrying once more found something about a definition rather than a graph.
`StrictBiconditional.SupportedIsotropic` asks for a nonzero `v` that is (a) supported on the half,
(b) **isotropic** — `crossForm v = 0` — and (c) in the reach kernel. **(b) follows from (a) and
(c)**, on every graph with a mirror reflection, with no coupling hypothesis and no block hypothesis
(`crossForm_eq_zero_of_inReachKernel`). The reason is one line of symmetry:
`ReachIsCoupling.crossForm_symm_matrix` makes `crossForm v = ∑_{p ∈ H} v p · (massive *ᵥ v) (θ p)`,
and the reach condition kills every factor, `θ p` being exactly a site outside the half and off the
mirror.

**Precisely what is redundant, and where.** The `def` is stated without `IsMirrorHalf` or `IsRefl`,
so the clause is not redundant *in the definition*. It is redundant at **every site where the
definition is used**, since every one of them carries both.

**What this does to the criterion.**
`StrictBiconditional.strict_iff_crossForm_neg_on_reachKernel` presents strictness as *the coupling
is negative definite on the reach kernel*. The coupling is **identically zero** there, so that
condition holds only vacuously, and the criterion says (`strict_iff_reachKernel_trivial`):

> **strict exactly when the reach kernel is trivial.**

The theorem was right. The reading around it described a definiteness that cannot occur.

**Checked against `ReachIsCoupling`, which proves the same fact one quantifier up:** that file's
`ReachInside ↔ crossForm ≡ 0` is about the graph; `crossForm_eq_zero_of_reachInside` derives its
forward half here in one line, because `ReachInside` puts every supported vector in the reach
kernel. Two results, one fact, and the per-vector form is the stronger.

## §8 — and the chain closes: strictness on a block cut is a perfect matching

§6's row identity was not about `K₂,₂`. `massive_mulVec_mirror`: on any graph with a mirror
reflection, the operator's row at a mirror site `θ s` is minus the cross matrix's row at `s`. So
the reach kernel is **one linear equation per half-site** (`inReachKernel_iff_rows`), and with §7's
"strict ⟺ reach kernel trivial" the whole criterion becomes combinatorial
(`strict_iff_cut_perfect`):

> **strict exactly when every half-site is joined to its own mirror image and to no other
> half-site's** — every block a singleton, and no half-site outside a block.

No vectors, no operator, no mass. Decidable on a finite graph, like the coupling criterion it sits
on top of. The two failures it forbids are the two ways a nonzero vector survives: a half-site with
no cross-neighbour at all (take its indicator) and two half-sites sharing a block (take the
difference of theirs).

**Sufficiency needs no block hypothesis** — a perfect matching *is* a block cut
(`isCrossBlock_of_cut_perfect`), so `strict_of_cut_perfect` asks only for the matching.

**Checked against §6 by a different route.** §6 proved `K₂,₂` non-strict by exhibiting a vector and
computing; `bipGraph_not_strict_of_cut` proves the same thing by inspecting one edge
(`bipGraph_cut_not_perfect`), and the two agree.

**A prediction this file does NOT cash.** Every lattice cut in the estate is diagonal, so the
criterion reduces there to *every half-site is joined to its own mirror*, which fails as soon as
the half contains a site away from the cut — the right shape for `WALLS` W1's thresholds (box
strict at sides 1–2 and not from 3; torus 1–4 and not from 5). **Instantiating it needs each
family's cut written out and none of that is here**, so this is a prediction, not a re-derivation,
and it is recorded as one.

## §9 — the prediction cashed, on the torus

§8 said the lattice reading was a prediction. Here it is cashed on one family, and the criterion
returns the estate's own threshold.

The torus cut is diagonal at every side (`TorusAnySide.torus_cross_diag_any`), so it is a block cut
in one line (`isCrossBlock_torus`) and §8's criterion reduces to *is every half-site joined to its
own mirror?* — which `torus_adj_self_mirror_iff` answers: **only on the two extreme layers**, the
boundary layer reached by the wrap-around bond and the innermost layer of an even side. Every layer
between is joined to nothing across the cut. So

> `torus_strict_iff_le_four_lowerHalf`: **strict if and only if `n ≤ 4`**, in every dimension and
> at every nonzero mass.

**No new case is decided, and that is worth saying plainly.** The estate already has all six: two
non-strictness theorems in two files, split by parity (`TorusNotStrict.not_strict_torus`, even and
from six; `OddNotStrictInstances.not_strict_torus_odd`, odd and from five), and four strictness
theorems, one per side, in two more (`SmallSideStrict`, `MirrorStrict`). **What is new is that they
are one biconditional with one proof**, uniform in `n` and in `d`, obtained by reading a condition
off the edges — `torus_not_strict_of_five_le` and `torus_strict_of_le_four` are the two halves,
stated in the estate's own support convention so the comparison is literal and not approximate.

**Still not cashed: the box and the estate's own `def`.** Their cuts are diagonal too and the same
route should work; it is not attempted here.

## §10 — and on the box, where §9's prediction said the threshold would be smaller

§9 predicted, in writing and before checking, that the box would come out lower than the torus
because **a box does not wrap around**: its boundary layer has no bond to its mirror, so only the
innermost layer of an even side is ever joined across the cut. That is `box_adj_self_mirror_iff`,
and the criterion then gives

> `box_strict_iff_le_two_lowerHalf`: **strict if and only if `n ≤ 2`**.

`WALLS` W1 records the box as strict at sides 1–2 and not from 3. The prediction was right, and the
difference between the two thresholds is exactly the two sides the wrap-around bond buys.

**Again no new case is decided**, and again the gain is in the count: the box threshold was five
theorems in four files by three mechanisms — `BoxNotStrict.not_strict` (even, from four),
`BoxOddNotStrict.not_strict_box_odd` (odd, from three, via the reach criterion because the odd
box's cut is empty), `StrictCriterion.reflectionPositive_box_one_strict` and `_box_two_strict`, and
`SmallSideStrict.reflectionPositive_box_one_strict'`. `box_not_strict_of_three_le` and
`box_strict_of_le_two` are the two halves; `box_and_torus_thresholds` states both families at once.

**`box_cross_diag_any` is new as stated.** The estate had diagonality at even sides
(`TorusReflection.boxGraph_cross_diag`) and emptiness at odd ones
(`BoxOddReflection.not_adj_cross_odd`), both on `lowerHalf`; the uniform statement on `strictLower`
is proved here directly, because that is the shape §8 consumes.

**Still not cashed: the estate's own lattice `def`.**

## §11 — the third family, and all three in one statement

The estate's own lattice `def` is the two-dimensional box transported
(`LatticeNotStrict.reflectedForm_lattice_eq`, an *equality* of reflected forms), so §11 is a
transport of §10 and not a third instance of the criterion. `pushforward_conditions` is the
direction `SmallSideStrict.pullback_conditions` did not need, and
`lattice_strict_iff_le_two` follows: **strict if and only if `n ≤ 2`**, matching the box exactly, as
a transported statement must.

`all_three_thresholds` states the box, the torus and the `def` in one theorem. That is the
deliverable of §§8–11: **three sharpness thresholds, read off one condition about edges**, with the
torus's two extra sides explained by a single bond.

**The fifteen theorems this replaces, counted rather than estimated**, across eight files:

* torus — `TorusNotStrict.not_strict_torus`, `OddNotStrictInstances.not_strict_torus_odd`,
  `SmallSideStrict.reflectionPositive_torus_one_strict` and `_two_strict`,
  `MirrorStrict.reflectionPositive_torus_three_strict` and `_four_strict`;
* box — `BoxNotStrict.not_strict`, `BoxOddNotStrict.not_strict_box_odd`,
  `StrictCriterion.reflectionPositive_box_one_strict` and `_box_two_strict`,
  `SmallSideStrict.reflectionPositive_box_one_strict'`;
* the estate's `def` — `LatticeNotStrict.not_strict_lattice`,
  `OddNotStrictInstances.not_strict_lattice_odd`,
  `SmallSideStrict.reflectionPositive_lattice_one_strict` and `_two_strict`.

**Every one of the fifteen was checked to exist under that name before this list was written.**
None of them is deleted or weakened; what §§8–11 add is that all fifteen are instances of one
biconditional, and that the two thresholds differ for a reason the statement exhibits.

**The count in `fceefcc`'s commit message describes this list, and the edit that writes it here
failed silently in that commit** — the message was accurate about the work and wrong about the
artefact for one commit. `ERRATUM 151`.

## What this does NOT do

It says nothing new about reflection positivity **off** `GreenExpansion` §9's class.
`IsCrossBlock → ReflectionPositive` holds always (`reflectedForm_nonneg_of_isCrossBlock`, which is
`GraphMirrorReflection.reflectionPositive_mirror` with the criterion in front of it); the converse
is `reflectionPositive_iff_isCrossBlock`, and it carries §9's hypotheses because that is where the
converse is known. The remaining leg of that wall — the general remainder bound — is an estimate
and is untouched here.

It also does not subsume `GraphMirrorReflection.crossForm_nonpos_of_cross_diag` outright: that
result asks only `IsMirrorHalf`, while the route through this file spends `IsRefl` on the
symmetry of `~`. The subsumption holds wherever the reflection is a graph automorphism, which is
every application on the estate, and nowhere else.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CrossBlockStructure

open Matrix

variable {V : Type*}

/-! ## 1. Block-ones matrices, and the three-way equivalence -/

section Abstract

variable [Fintype V] {C : Matrix V V ℝ} {H : Finset V}

/-- **A BLOCK-ONES MATRIX.** Entries in `{0,1}`, symmetric, supported in `H`, and the relation
`C i j = 1` is reflexive where it is inhabited and transitive — so it is an equivalence relation
on the indices it touches, and `C` is the indicator of that equivalence. -/
structure IsBlockOnes (C : Matrix V V ℝ) (H : Finset V) : Prop where
  /-- entries are `0` or `1`. -/
  entries : ∀ i j, C i j = 0 ∨ C i j = 1
  /-- the matrix is symmetric. -/
  symm : ∀ i j, C i j = C j i
  /-- the matrix vanishes off `H × H`. -/
  support : ∀ i j, C i j = 1 → i ∈ H ∧ j ∈ H
  /-- an index with any relation has the relation to itself. -/
  diag : ∀ i j, C i j = 1 → C i i = 1
  /-- the relation is transitive. -/
  trans : ∀ i j k, C i j = 1 → C j k = 1 → C i k = 1

omit [Fintype V] in
/-- The block of `CrossPosSemidef`'s decomposition is where `IsBlockOnes` puts its support. -/
theorem mem_blk_of_isBlockOnes (hB : IsBlockOnes C H) {i j : V} (hij : C i j = 1) :
    i ∈ CrossPosSemidef.blk C H ∧ j ∈ CrossPosSemidef.blk C H := by
  classical
  obtain ⟨hiH, hjH⟩ := hB.support i j hij
  have hji : C j i = 1 := by rw [hB.symm j i]; exact hij
  refine ⟨?_, ?_⟩
  · simp only [CrossPosSemidef.blk, Finset.mem_filter]
    exact ⟨hiH, hB.diag i j hij⟩
  · simp only [CrossPosSemidef.blk, Finset.mem_filter]
    exact ⟨hjH, hB.diag j i hji⟩

/-- **A BLOCK-ONES MATRIX IS POSITIVE SEMIDEFINITE.** This is `CrossPosSemidef.form_nonneg` with
its two structural hypotheses read off the fields, and it is the easy half: each block is an
all-ones matrix. -/
theorem form_nonneg_of_isBlockOnes (hB : IsBlockOnes C H) (c : V → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * C i j :=
  CrossPosSemidef.form_nonneg hB.symm
    (fun i _ j _ l _ hij hjl => hB.trans i j l hij hjl)
    hB.entries (fun _ _ hij => mem_blk_of_isBlockOnes hB hij) c

omit [Fintype V] in
/-- **AND NONNEGATIVITY ON THE SUM-ZERO VECTORS ALREADY FORCES THE BLOCK STRUCTURE.** The pair
step supplies `diag` and the triple step supplies `trans`; this is `CrossPosSemidef`'s proof read
as a structure theorem rather than as a lemma on the way to one. -/
theorem isBlockOnes_of_zeroSum (h01 : ∀ i j, C i j = 0 ∨ C i j = 1) (hsym : ∀ i j, C i j = C j i)
    (hsupp : ∀ i j, C i j = 1 → i ∈ H ∧ j ∈ H) (hz : CrossPosSemidef.ZeroSumNonneg C H) :
    IsBlockOnes C H where
  entries := h01
  symm := hsym
  support := hsupp
  diag i j hij :=
    (CrossPosSemidef.mem_blk
      (CrossPosSemidef.mem_blk_of_offDiag h01 hsym hz hsupp i j hij).1).2
  trans i j k hij hjk :=
    CrossPosSemidef.trans_on_blk h01 hsym hz
      i (CrossPosSemidef.mem_blk_of_offDiag h01 hsym hz hsupp i j hij).1
      j (CrossPosSemidef.mem_blk_of_offDiag h01 hsym hz hsupp i j hij).2
      k (CrossPosSemidef.mem_blk_of_offDiag h01 hsym hz hsupp j k hjk).2 hij hjk

/-- A form nonnegative everywhere is nonnegative on the sum-zero vectors of the half — the only
content is that a vector supported in `H` sees only the `H × H` part of the sum. -/
theorem zeroSumNonneg_of_form_nonneg (hn : ∀ c : V → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * C i j) :
    CrossPosSemidef.ZeroSumNonneg C H := by
  classical
  intro c hcs _
  have hinner : ∀ i : V, ∑ j, c i * c j * C i j = ∑ j ∈ H, c i * c j * C i j := fun i =>
    (Finset.sum_subset (Finset.subset_univ H) fun j _ hj => by rw [hcs j hj]; ring).symm
  have houter : ∑ i, (∑ j ∈ H, c i * c j * C i j) = ∑ i ∈ H, ∑ j ∈ H, c i * c j * C i j :=
    (Finset.sum_subset (Finset.subset_univ H) fun i _ hi =>
      Finset.sum_eq_zero fun j _ => by rw [hcs i hi]; ring).symm
  calc (0 : ℝ) ≤ ∑ i, ∑ j, c i * c j * C i j := hn c
    _ = ∑ i, ∑ j ∈ H, c i * c j * C i j := Finset.sum_congr rfl fun i _ => hinner i
    _ = ∑ i ∈ H, ∑ j ∈ H, c i * c j * C i j := houter

/-- **THE STRUCTURE THEOREM.** For symmetric `0/1` matrices supported in `H`, positive
semidefinite means block-ones and nothing else. -/
theorem posSemidef_iff_isBlockOnes (h01 : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hsym : ∀ i j, C i j = C j i) (hsupp : ∀ i j, C i j = 1 → i ∈ H ∧ j ∈ H) :
    (∀ c : V → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * C i j) ↔ IsBlockOnes C H :=
  ⟨fun hn => isBlockOnes_of_zeroSum h01 hsym hsupp (zeroSumNonneg_of_form_nonneg hn),
    fun hB => form_nonneg_of_isBlockOnes hB⟩

/-- **AND SO THE THREE TESTS ARE ONE TEST**: positive semidefinite, nonnegative on the sum-zero
vectors of the half, and block-ones all coincide for symmetric `0/1` matrices supported in `H`.
The middle one is `CrossPosSemidef`'s theorem; the outer one is what this file adds. -/
theorem three_tests_agree (h01 : ∀ i j, C i j = 0 ∨ C i j = 1)
    (hsym : ∀ i j, C i j = C j i) (hsupp : ∀ i j, C i j = 1 → i ∈ H ∧ j ∈ H) :
    ((∀ c : V → ℝ, 0 ≤ ∑ i, ∑ j, c i * c j * C i j) ↔ IsBlockOnes C H)
      ∧ (CrossPosSemidef.ZeroSumNonneg C H ↔ IsBlockOnes C H) :=
  ⟨posSemidef_iff_isBlockOnes h01 hsym hsupp,
    ⟨fun hz => isBlockOnes_of_zeroSum h01 hsym hsupp hz,
      fun hB => zeroSumNonneg_of_form_nonneg (form_nonneg_of_isBlockOnes hB)⟩⟩

end Abstract

/-! ## 2. The cut relation, and the criterion -/

section Graph

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix CrossPosSemidef

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}
variable {d : ℕ}

/-- **THE CUT RELATION.** `p` and `q` are both in the half and `p` is joined to the mirror image
of `q`. Symmetric when `θ` is a graph automorphism (`CrossFormMatrix.adj_cross_comm`). -/
def CrossRel (G : SimpleGraph V) (θ : V ≃ V) (H : Finset V) (p q : V) : Prop :=
  p ∈ H ∧ q ∈ H ∧ G.Adj p (θ q)

/-- **THE CRITERION: THE CUT IS IN BLOCKS.** Every half-site with a cross-neighbour is joined to
its own mirror image, and sharing a cross-neighbour is transitive. Both clauses quantify over
vertices only, so on a finite graph this is decidable. -/
structure IsCrossBlock (G : SimpleGraph V) (θ : V ≃ V) (H : Finset V) : Prop where
  /-- a half-site with any cross-neighbour is joined to its own mirror. -/
  loop : ∀ p q, CrossRel G θ H p q → G.Adj p (θ p)
  /-- the cut relation is transitive. -/
  trans : ∀ p q r, CrossRel G θ H p q → CrossRel G θ H q r → G.Adj p (θ r)

omit [DecidableRel G.Adj] in
/-- The criterion, unfolded to bounded quantifiers over vertices — which is all "combinatorial"
means, and is what makes the next declaration possible. -/
theorem isCrossBlock_iff_bounded :
    IsCrossBlock G θ H ↔
      ((∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → G.Adj p (θ p))
        ∧ ∀ p ∈ H, ∀ q ∈ H, ∀ r ∈ H, G.Adj p (θ q) → G.Adj q (θ r) → G.Adj p (θ r)) := by
  constructor
  · intro hB
    exact ⟨fun p hp q hq hadj => hB.loop p q ⟨hp, hq, hadj⟩,
      fun p hp q hq r hr h1 h2 => hB.trans p q r ⟨hp, hq, h1⟩ ⟨hq, hr, h2⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun p q hpq => h1 p hpq.1 q hpq.2.1 hpq.2.2,
      fun p q r hpq hqr => h2 p hpq.1 q hpq.2.1 r hqr.2.1 hpq.2.2 hqr.2.2⟩

/-- **THE CRITERION IS DECIDABLE.** This is the practical content of the word *combinatorial*:
`hcross` is not merely equivalent to something finite, it is settled by `decide`. Both worked
examples in §3 are closed that way, with no test vectors. -/
instance instDecidableIsCrossBlock : Decidable (IsCrossBlock G θ H) :=
  decidable_of_iff _ isCrossBlock_iff_bounded.symm

omit [DecidableRel G.Adj] in
/-- The cut relation is symmetric when the reflection is a graph automorphism. -/
theorem crossRel_symm (h : IsRefl G θ) {p q : V} (hpq : CrossRel G θ H p q) :
    CrossRel G θ H q p :=
  ⟨hpq.2.1, hpq.1, (CrossFormMatrix.adj_cross_comm h p q).mp hpq.2.2⟩

omit [DecidableRel G.Adj] in
/-- **THE `loop` CLAUSE IS REDUNDANT, AND THIS WAS FOUND BY ATTACKING THE STRUCTURE RATHER THAN
BY WRITING IT.** Under `IsRefl` the relation is symmetric, so `p ~ q` gives `q ~ p` and
transitivity applied at `(p, q, p)` gives `p ~ p`. The two-clause structure is kept because it is
what "the cut is in blocks" says; the one-clause version is `hcross_iff_cross_trans`, and it is
the sharp statement: **`hcross` is transitivity of the cut relation, and nothing else.** -/
theorem isCrossBlock_of_trans (h : IsRefl G θ)
    (htrans : ∀ p q r, CrossRel G θ H p q → CrossRel G θ H q r → G.Adj p (θ r)) :
    IsCrossBlock G θ H where
  loop p q hpq := htrans p q p hpq (crossRel_symm h hpq)
  trans := htrans

variable [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The cross matrix carries a `1` exactly on the cut relation. -/
theorem crossMatrix_eq_one_iff (p q : V) :
    crossMatrix G θ H p q = 1 ↔ CrossRel G θ H p q := by
  rw [crossMatrix, CrossRel]
  by_cases hm : p ∈ H ∧ q ∈ H
  · rw [if_pos hm, crossAdj]
    by_cases ha : G.Adj p (θ q)
    · simp [ha, hm.1, hm.2]
    · simp [ha]
  · rw [if_neg hm]
    constructor
    · intro h; norm_num at h
    · rintro ⟨h1, h2, -⟩; exact absurd ⟨h1, h2⟩ hm

omit [Fintype V] in
/-- **THE TWO STRUCTURES ARE THE SAME STRUCTURE.** The matrix conditions `diag` and `trans` are
literally the graph conditions `loop` and `trans`, once `IsRefl` supplies the symmetry. -/
theorem isBlockOnes_iff_isCrossBlock (h : IsRefl G θ) :
    IsBlockOnes (crossMatrix G θ H) H ↔ IsCrossBlock G θ H := by
  constructor
  · intro hB
    refine ⟨fun p q hpq => ?_, fun p q r hpq hqr => ?_⟩
    · have h1 : crossMatrix G θ H p q = 1 := (crossMatrix_eq_one_iff p q).mpr hpq
      exact ((crossMatrix_eq_one_iff p p).mp (hB.diag p q h1)).2.2
    · have h1 : crossMatrix G θ H p q = 1 := (crossMatrix_eq_one_iff p q).mpr hpq
      have h2 : crossMatrix G θ H q r = 1 := (crossMatrix_eq_one_iff q r).mpr hqr
      exact ((crossMatrix_eq_one_iff p r).mp (hB.trans p q r h1 h2)).2.2
  · intro hC
    refine ⟨crossMatrix_entries, crossMatrix_symm h, fun i j hij => crossMatrix_support hij,
      fun i j hij => ?_, fun i j k hij hjk => ?_⟩
    · have hr := (crossMatrix_eq_one_iff i j).mp hij
      exact (crossMatrix_eq_one_iff i i).mpr ⟨hr.1, hr.1, hC.loop i j hr⟩
    · have hr1 := (crossMatrix_eq_one_iff i j).mp hij
      have hr2 := (crossMatrix_eq_one_iff j k).mp hjk
      exact (crossMatrix_eq_one_iff i k).mpr ⟨hr1.1, hr2.2.1, hC.trans i j k hr1 hr2⟩

/-- **THE COMBINATORIAL CRITERION FOR THE COUPLING HYPOTHESIS.** No vectors, no mass, no
eigenvalues: `hcross` says the cut is a disjoint union of blocks, and that is all it says.
`IndefiniteCoupling`'s header recorded finding such a criterion as NOT ATTEMPTED. -/
theorem hcross_iff_isCrossBlock (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ) :
    (∀ w : V → ℝ, crossForm G m θ H w ≤ 0) ↔ IsCrossBlock G θ H := by
  rw [← isBlockOnes_iff_isCrossBlock (H := H) h]
  constructor
  · intro hc
    exact isBlockOnes_of_zeroSum crossMatrix_entries (crossMatrix_symm h)
      (fun i j hij => crossMatrix_support hij)
      ((zeroSumNonneg_iff_crossForm hM m).mpr fun c _ _ => hc c)
  · intro hB w
    have hn := form_nonneg_of_isBlockOnes hB w
    rw [form_eq_dotProduct w, dotProduct_crossMatrix hM m w] at hn
    linarith

/-- **THE SHARP FORM: `hcross` IS TRANSITIVITY OF THE CUT RELATION.** One clause, quantifying
over three vertices. Reflexivity comes free from symmetry (`isCrossBlock_of_trans`), so the
`loop` clause of `IsCrossBlock` is readability and not content. -/
theorem hcross_iff_cross_trans (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ) :
    (∀ w : V → ℝ, crossForm G m θ H w ≤ 0) ↔
      ∀ p q r, CrossRel G θ H p q → CrossRel G θ H q r → G.Adj p (θ r) :=
  ⟨fun hc => ((hcross_iff_isCrossBlock hM h m).mp hc).trans,
    fun ht => (hcross_iff_isCrossBlock hM h m).mpr (isCrossBlock_of_trans h ht)⟩

/-- **SUFFICIENCY IS UNCONDITIONAL.** The criterion gives reflection positivity on every graph
with a mirror reflection — this is `GraphMirrorReflection.reflectionPositive_mirror` with the
combinatorial test in front of it. -/
theorem reflectedForm_nonneg_of_isCrossBlock (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hB : IsCrossBlock G θ H) {c : V → ℝ}
    (hc : ∀ p, p ∉ H → p ∉ Mir → c p = 0) :
    0 ≤ GraphReflection.reflectedForm G m θ c :=
  reflectionPositive_mirror hM h hm ((hcross_iff_isCrossBlock hM h m).mpr hB) hc

/-- **AND ON `GreenExpansion` §9's CLASS IT IS AN EQUIVALENCE.** Reflection positivity of the
lattice Green function is then decided by looking at the cut. -/
theorem reflectionPositive_iff_isCrossBlock (hd : G.IsRegularOfDegree d)
    (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0) {α β γ : ℝ} (hγ : 0 ≤ γ)
    (hA : G.adjMatrix ℝ * G.adjMatrix ℝ
      = α • (1 : Matrix V V ℝ) + β • G.adjMatrix ℝ + γ • allOnes V)
    (hK : 0 < ((d : ℝ) + m ^ 2) ^ 2 - α - β * ((d : ℝ) + m ^ 2)) :
    GraphReflection.ReflectionPositive G m θ H ↔ IsCrossBlock G θ H :=
  (reflectionPositive_iff_hcross_of_adjSq hd hM h hm hγ hA hK).trans
    (hcross_iff_isCrossBlock hM h m)

end Graph

/-! ## 3. The old sufficient condition is the singleton case, and the containment is strict -/

section Examples

open GraphReflection GraphMirrorReflection CrossFormMatrix

variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H : Finset V}

omit [DecidableRel G.Adj] in
/-- **THE DIAGONAL CUT IS THE ALL-SINGLETONS CASE.** `crossForm_nonpos_of_cross_diag`'s hypothesis
implies the criterion, with every block of size one. -/
theorem isCrossBlock_of_cross_diag (hdiag : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q) → p = q) :
    IsCrossBlock G θ H where
  loop p q hpq := by
    obtain ⟨hp, hq, hadj⟩ := hpq
    have hpq' : p = q := hdiag p hp q hq hadj
    subst hpq'
    exact hadj
  trans p q r hpq hqr := by
    obtain ⟨hp, hq, hadj⟩ := hpq
    obtain ⟨-, hr, hadj'⟩ := hqr
    have h1 : p = q := hdiag p hp q hq hadj
    have h2 : q = r := hdiag q hq r hr hadj'
    subst h1
    subst h2
    exact hadj

/-- Every pair of half-sites of `K₂,₂` is cross-adjacent, so its cut is a single block of size
two. Used by §4 to compute the coupling there exactly. -/
theorem bipGraph_cross_all : ∀ p ∈ IndefiniteCoupling.Hh, ∀ q ∈ IndefiniteCoupling.Hh,
    IndefiniteCoupling.bipGraph.Adj p (IndefiniteCoupling.rho q) := by decide

/-- **THE CONTAINMENT IS STRICT.** `bipGraph` satisfies the criterion — one block of size two,
not singletons — while `IndefiniteCoupling.cross_not_diagonal` says its cut is not diagonal. So
the criterion is genuinely weaker than the estate's original sufficient condition, and
`IndefiniteCoupling.hcross_bip` is recovered from it.

**Closed by `decide`.** No test vector, no all-ones matrix, no positivity argument — the machine
enumerates the half and checks adjacency. -/
theorem isCrossBlock_bipGraph :
    IsCrossBlock IndefiniteCoupling.bipGraph IndefiniteCoupling.rho IndefiniteCoupling.Hh := by
  decide

/-- **AND THE CRITERION IS NOT VACUOUS: `crossGraph` FAILS IT**, also by `decide`. -/
theorem not_isCrossBlock_crossGraph :
    ¬ IsCrossBlock IndefiniteCoupling.crossGraph IndefiniteCoupling.rho
        IndefiniteCoupling.Hh := by
  decide

/-- **AND HERE IS THE FAILING TRIPLE, NAMED.** `0 ~ 1` and `1 ~ 0`, but `0` is not joined to
`2 = ρ 0`: transitivity fails at `(0, 1, 0)`. The matching `0–3`, `1–2` pairs each half-site with
the *other* one's mirror, which is exactly the configuration a block cut forbids — and it is the
configuration the estate's counterexample has. Read against `hcross_iff_cross_trans` this is the
whole of why `crossGraph` fails the coupling hypothesis. -/
theorem crossGraph_failing_triple :
    CrossRel IndefiniteCoupling.crossGraph IndefiniteCoupling.rho IndefiniteCoupling.Hh 0 1
      ∧ CrossRel IndefiniteCoupling.crossGraph IndefiniteCoupling.rho IndefiniteCoupling.Hh 1 0
      ∧ ¬ IndefiniteCoupling.crossGraph.Adj 0 (IndefiniteCoupling.rho 0) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩, by decide⟩

/-- The two examples, side by side: the criterion separates the estate's two four-vertex graphs,
with the same reflection and the same half. -/
theorem criterion_separates_the_two_examples :
    IsCrossBlock IndefiniteCoupling.bipGraph IndefiniteCoupling.rho IndefiniteCoupling.Hh
      ∧ ¬ IsCrossBlock IndefiniteCoupling.crossGraph IndefiniteCoupling.rho
            IndefiniteCoupling.Hh :=
  ⟨isCrossBlock_bipGraph, not_isCrossBlock_crossGraph⟩

end Examples

/-! ## 4. On a block cut the coupling is not merely nonpositive — it is minus a sum of squares -/

section Exact

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix CrossPosSemidef

variable [Fintype V] [DecidableEq V] {C : Matrix V V ℝ} {H : Finset V}

omit [DecidableEq V] in
/-- The class indicator, summed against a vector, is the sum over the class. -/
theorem sum_indicator_eq_sum_cls (hB : IsBlockOnes C H) {k : V} (c : V → ℝ) :
    (∑ i, c i * (if C k i = 1 then (1 : ℝ) else 0)) = ∑ i ∈ cls C H k, c i := by
  classical
  have step : ∀ i : V, c i * (if C k i = 1 then (1 : ℝ) else 0) = if C k i = 1 then c i else 0 :=
    fun i => by by_cases hki : C k i = 1 <;> simp [hki]
  rw [Finset.sum_congr rfl fun i _ => step i, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, cls]
  exact ⟨fun hki => ⟨(mem_blk_of_isBlockOnes hB hki).2, hki⟩, fun hi => hi.2⟩

omit [DecidableEq V] in
/-- **THE FORM IN CLOSED FORM.** A block-ones matrix's quadratic form is the sum, over classes, of
the squared class sum — each class weighted by the reciprocal of its size because the outer sum
runs over members rather than over classes. -/
theorem form_eq_sum_cls_sq (hB : IsBlockOnes C H) (c : V → ℝ) :
    ∑ i, ∑ j, c i * c j * C i j
      = ∑ k ∈ blk C H, ((cls C H k).card : ℝ)⁻¹ * (∑ i ∈ cls C H k, c i) ^ 2 := by
  rw [form_eq_sum_sq hB.symm (fun i _ j _ l _ hij hjl => hB.trans i j l hij hjl)
    hB.entries (fun _ _ hij => mem_blk_of_isBlockOnes hB hij) c]
  exact Finset.sum_congr rfl fun k _ => by rw [sum_indicator_eq_sum_cls hB c]

omit [DecidableEq V] in
/-- **AND SO THE FORM VANISHES EXACTLY ON THE VECTORS WHOSE CLASS SUMS ALL VANISH.** The
degeneracy is combinatorial: one linear condition per class, and nothing else. -/
theorem form_eq_zero_iff (hB : IsBlockOnes C H) (c : V → ℝ) :
    (∑ i, ∑ j, c i * c j * C i j) = 0 ↔ ∀ k ∈ blk C H, (∑ i ∈ cls C H k, c i) = 0 := by
  have hnn : ∀ k ∈ blk C H,
      0 ≤ ((cls C H k).card : ℝ)⁻¹ * (∑ i ∈ cls C H k, c i) ^ 2 := by
    intro k _
    have : (0 : ℝ) ≤ ((cls C H k).card : ℝ)⁻¹ := by positivity
    positivity
  rw [form_eq_sum_cls_sq hB c, Finset.sum_eq_zero_iff_of_nonneg hnn]
  refine ⟨fun h k hk => ?_, fun h k hk => by rw [h k hk]; ring⟩
  have hpos : (0 : ℝ) < ((cls C H k).card : ℝ)⁻¹ :=
    inv_pos.mpr (Nat.cast_pos.mpr (cls_card_pos hk))
  have := h k hk
  rcases mul_eq_zero.mp this with hc | hs
  · exact absurd hc hpos.ne'
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs

end Exact

section ExactGraph

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix CrossPosSemidef

variable [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-- **THE COUPLING FORM ON A BLOCK CUT, EXACTLY.** `hcross` says the form is `≤ 0`; on a block cut
it is **minus a sum of squares**, one per block, and the theorem is an identity rather than an
inequality. Everything below is read off it. -/
theorem crossForm_eq_neg_sum_cls_sq (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) (m : ℝ) (w : V → ℝ) :
    crossForm G m θ H w
      = - ∑ k ∈ blk (crossMatrix G θ H) H,
            ((cls (crossMatrix G θ H) H k).card : ℝ)⁻¹
              * (∑ i ∈ cls (crossMatrix G θ H) H k, w i) ^ 2 := by
  have hB : IsBlockOnes (crossMatrix G θ H) H := (isBlockOnes_iff_isCrossBlock h).mpr hC
  have hforms : ∑ i, ∑ j, w i * w j * crossMatrix G θ H i j = - crossForm G m θ H w := by
    rw [form_eq_dotProduct w, dotProduct_crossMatrix hM m w]
  have hsum := form_eq_sum_cls_sq hB w
  linarith

/-- **THE COUPLING'S KERNEL IS COMBINATORIAL.** On a block cut the coupling form vanishes at `w`
exactly when every block sum of `w` vanishes — one linear condition per block. `hcross` and its
degeneracy are then the same statement read twice. -/
theorem crossForm_eq_zero_iff (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) (m : ℝ) (w : V → ℝ) :
    crossForm G m θ H w = 0 ↔
      ∀ k ∈ blk (crossMatrix G θ H) H, (∑ i ∈ cls (crossMatrix G θ H) H k, w i) = 0 := by
  have hB : IsBlockOnes (crossMatrix G θ H) H := (isBlockOnes_iff_isCrossBlock h).mpr hC
  rw [crossForm_eq_neg_sum_cls_sq hM h hC m w, neg_eq_zero, ← form_eq_sum_cls_sq hB w]
  exact form_eq_zero_iff hB w

/-- And so the coupling is strictly negative exactly off that subspace. -/
theorem crossForm_neg_iff (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) (m : ℝ) (w : V → ℝ) :
    crossForm G m θ H w < 0 ↔
      ∃ k ∈ blk (crossMatrix G θ H) H, (∑ i ∈ cls (crossMatrix G θ H) H k, w i) ≠ 0 := by
  have hle : crossForm G m θ H w ≤ 0 := (hcross_iff_isCrossBlock hM h m).mpr hC w
  rw [lt_iff_le_and_ne, and_iff_right hle, Ne, crossForm_eq_zero_iff hM h hC m w]
  simp

/-- **THE ONE-BLOCK CASE, WITHOUT ANY OF THE MACHINERY.** When every pair of half-sites is
cross-adjacent the cut is a single block and the coupling is exactly minus the squared total. Proved
straight from `crossForm_eq_neg_adj`, so it is an independent check on the closed form above rather
than a corollary of it. -/
theorem crossForm_eq_neg_sq_of_complete (hM : IsMirrorHalf θ H Mir) (m : ℝ)
    (hall : ∀ p ∈ H, ∀ q ∈ H, G.Adj p (θ q)) (w : V → ℝ) :
    crossForm G m θ H w = - (∑ p ∈ H, w p) ^ 2 := by
  classical
  rw [crossForm_eq_neg_adj hM m w, neg_inj, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => by
    rw [if_pos (hall p hp q hq), mul_one]

/-- **THE CROSS-CHECK, ON THE ESTATE'S OWN WITNESS.** `IndefiniteCoupling.hcross_bip` says the
coupling on `K₂,₂` is `≤ 0`. It is `−(w 0 + w 1)²` — the same fact with the slack removed, and the
single block of size two that `isCrossBlock_bipGraph` found is exactly the `w 0 + w 1`. -/
theorem crossForm_bipGraph_exact (m : ℝ) (w : Fin 4 → ℝ) :
    crossForm IndefiniteCoupling.bipGraph m IndefiniteCoupling.rho IndefiniteCoupling.Hh w
      = - (w 0 + w 1) ^ 2 := by
  rw [crossForm_eq_neg_sq_of_complete IndefiniteCoupling.isMirrorHalf_Hh m bipGraph_cross_all w,
    show IndefiniteCoupling.Hh = ({0, 1} : Finset (Fin 4)) from rfl]
  norm_num

/-- **AND THE COUPLING ON `K₂,₂` IS DEGENERATE, WITH THE DEGENERACY NAMED.** It vanishes on exactly
the antisymmetric vectors of the half and is strictly negative on every other. That is one linear
condition, which is one block. -/
theorem crossForm_bipGraph_zero_iff (m : ℝ) (w : Fin 4 → ℝ) :
    crossForm IndefiniteCoupling.bipGraph m IndefiniteCoupling.rho IndefiniteCoupling.Hh w = 0
      ↔ w 0 + w 1 = 0 := by
  rw [crossForm_bipGraph_exact m w, neg_eq_zero]
  exact pow_eq_zero_iff (n := 2) (by norm_num)

end ExactGraph

/-! ## 5. And so strictness on a block cut is a LINEAR condition on the reach kernel -/

section Strict

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix CrossPosSemidef

variable [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-- **THE STRICTNESS CRITERION, WITH THE QUADRATIC CONDITION REMOVED.**
`StrictBiconditional.strict_iff_crossForm_neg_on_reachKernel` says the reflected form is strict
exactly when the coupling is strictly negative on every nonzero vector the operator keeps inside
the region. On a block cut §4 says what strict negativity IS — some block sum is nonzero — so the
criterion becomes:

> **strict exactly when the reach kernel meets the all-block-sums-zero subspace only at `0`.**

Both sides of that sentence are conjunctions of linear equations in `v`, so the criterion is two
subspaces meeting trivially where the estate previously had a quadratic form to sign — said as a
description of the shape, since no `Submodule` is constructed here and none is needed for the
statement. The coupling hypothesis is not assumed: `IsCrossBlock` supplies it. -/
theorem strict_iff_reachKernel_has_nonzero_block_sum (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hC : IsCrossBlock G θ H) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ ∀ v : V → ℝ, StrictBiconditional.InReachKernel G m H Mir v → v ≠ 0 →
          ∃ k ∈ blk (crossMatrix G θ H) H,
            (∑ i ∈ cls (crossMatrix G θ H) H k, v i) ≠ 0 := by
  rw [StrictBiconditional.strict_iff_crossForm_neg_on_reachKernel hM h hm
    ((hcross_iff_isCrossBlock hM h m).mpr hC)]
  refine forall_congr' fun v => ?_
  exact imp_congr_right fun _ => imp_congr_right fun _ => crossForm_neg_iff hM h hC m v

/-- **AND SO A SINGLE VECTOR REFUTES STRICTNESS.** One nonzero vector that the operator keeps
inside the region and whose every block sum vanishes is enough. This is the criterion above read
backwards, and it is the form a counterexample search consumes. -/
theorem not_strict_of_reachKernel_block_sums_zero (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hm : m ≠ 0) (hC : IsCrossBlock G θ H) {v : V → ℝ}
    (hv : StrictBiconditional.InReachKernel G m H Mir v) (hv0 : v ≠ 0)
    (hz : ∀ k ∈ blk (crossMatrix G θ H) H, (∑ i ∈ cls (crossMatrix G θ H) H k, v i) = 0) :
    ¬ ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c := by
  intro hstrict
  obtain ⟨k, hk, hne⟩ :=
    (strict_iff_reachKernel_has_nonzero_block_sum hM h hm hC).mp hstrict v hv hv0
  exact hne (hz k hk)

end Strict

/-! ## 6. The item §5 opened, answered on its own named target: `K₂,₂` is NOT strict -/

section BipStrict

open GraphReflection GraphMirrorReflection CrossFormMatrix IndefiniteCoupling

/-- On `K₂,₂` every vertex outside the half is joined to both half-sites, so the operator's row
there reads off the half's total. -/
theorem bipGraph_massive_mulVec_out (m : ℝ) {v : Fin 4 → ℝ} (hv : ∀ i, i ∉ Hh → v i = 0)
    {p : Fin 4} (hp : p ∉ Hh) :
    (GraphLaplacian.massive bipGraph m *ᵥ v) p = - (v 0 + v 1) := by
  have hv2 : v 2 = 0 := hv 2 (by decide)
  have hv3 : v 3 = 0 := hv 3 (by decide)
  have hp23 : p = 2 ∨ p = 3 := by revert hp; revert p; decide
  rcases hp23 with rfl | rfl
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, GraphLaplacian.massive_apply,
      hv2, hv3, show ¬ ((2 : Fin 4) = 0) by decide, show ¬ ((2 : Fin 4) = 1) by decide,
      show ¬ ((2 : Fin 4) = 3) by decide,
      show bipGraph.Adj 2 0 by decide, show bipGraph.Adj 2 1 by decide,
      show ¬ bipGraph.Adj 2 2 by decide, show ¬ bipGraph.Adj 2 3 by decide,
      if_false, if_pos]
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, GraphLaplacian.massive_apply,
      hv2, hv3, show ¬ ((3 : Fin 4) = 0) by decide, show ¬ ((3 : Fin 4) = 1) by decide,
      show ¬ ((3 : Fin 4) = 2) by decide,
      show bipGraph.Adj 3 0 by decide, show bipGraph.Adj 3 1 by decide,
      show ¬ bipGraph.Adj 3 2 by decide, show ¬ bipGraph.Adj 3 3 by decide,
      if_false, if_pos]
    ring

/-- **AND SO EVERY SUM-ZERO VECTOR ON THE HALF IS IN THE REACH KERNEL.** On this graph the
operator's condition off the half and the block's linear condition are the *same* equation, which
is why the two subspaces of §5 do not meet only at `0`. -/
theorem bipGraph_inReachKernel_of_sum_zero (m : ℝ) {v : Fin 4 → ℝ} (hv : ∀ i, i ∉ Hh → v i = 0)
    (h0 : v 0 + v 1 = 0) :
    StrictBiconditional.InReachKernel bipGraph m Hh (∅ : Finset (Fin 4)) v :=
  ⟨hv, fun p hp _ => by rw [bipGraph_massive_mulVec_out m hv hp, h0, neg_zero]⟩

/-- `IndefiniteCoupling.wpos = ![1, −1, 0, 0]` is supported on the half and sums to zero there —
the same vector that refutes `hcross` on `crossGraph`, doing the opposite job here. -/
theorem wpos_supported : ∀ i, i ∉ Hh → wpos i = 0 := by
  intro i hi
  fin_cases i
  · exact absurd (by decide : (0 : Fin 4) ∈ Hh) hi
  · exact absurd (by decide : (1 : Fin 4) ∈ Hh) hi
  · norm_num [wpos]
  · norm_num [wpos]

/-- **`K₂,₂` IS REFLECTION POSITIVE AND NOT STRICTLY SO**, at every nonzero mass — which the
estate did not know, and which `WALLS` W1's sharpness line covers for the box, the torus and the
lattice `def` and for nothing else. The witness is a single block's kernel direction: the cut is
one block of size two, so `crossForm` vanishes on `w 0 + w 1 = 0` (§4), and on this graph that is
also exactly the reach condition. -/
theorem bipGraph_supportedIsotropic (m : ℝ) :
    StrictBiconditional.SupportedIsotropic bipGraph m rho Hh (∅ : Finset (Fin 4)) := by
  refine ⟨wpos, ?_, wpos_supported, ?_, (bipGraph_inReachKernel_of_sum_zero m wpos_supported ?_).2⟩
  · intro hc
    have : wpos 0 = 0 := by rw [hc]; rfl
    norm_num [wpos] at this
  · rw [crossForm_bipGraph_exact m wpos]
    norm_num [wpos]
  · norm_num [wpos]

/-- **THE CONCLUSION.** Reflection positivity on `K₂,₂` is degenerate: some nonzero vector on the
half has reflected form zero, so the inequality is not strict. -/
theorem bipGraph_not_strict (m : ℝ) (hm : m ≠ 0) :
    ¬ ∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
        0 < GraphReflection.reflectedForm bipGraph m rho c :=
  StrictBiconditional.not_strict_of_supportedIsotropic isMirrorHalf_Hh isRefl_rho_bip hm
    (bipGraph_supportedIsotropic m)

/-- **BOTH FOUR-VERTEX GRAPHS ARE NOW DECIDED, AND THEY FAIL DIFFERENTLY.** `crossGraph` is not
reflection positive at all (`IndefiniteCoupling.not_reflectionPositive`); `bipGraph` is reflection
positive but not strictly. Same reflection, same half, same mass. -/
theorem the_two_graphs_fail_differently (m : ℝ) (hm : m ≠ 0) :
    ¬ GraphReflection.ReflectionPositive crossGraph m rho Hh
      ∧ (∀ w : Fin 4 → ℝ, crossForm bipGraph m rho Hh w ≤ 0)
      ∧ ¬ ∀ c : Fin 4 → ℝ, c ≠ 0 → (∀ p, p ∉ Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
            0 < GraphReflection.reflectedForm bipGraph m rho c :=
  ⟨not_reflectionPositive hm, hcross_bip m, bipGraph_not_strict m hm⟩

end BipStrict

/-! ## 7. The isotropy clause was never doing any work -/

section ReachIsotropy

open GraphReflection GraphMirrorReflection CrossFormMatrix

variable [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

omit [Fintype V] [DecidableEq V] in
/-- A half-site's mirror image is off the mirror as well as out of the half. -/
theorem mirror_notMem_mir (hM : IsMirrorHalf θ H Mir) {s : V} (hs : s ∈ H) : θ s ∉ Mir := by
  intro hc
  have hfix : θ (θ s) = θ s := (hM.fixed (θ s)).mp hc
  exact hM.disj s hs ((hM.fixed s).mpr (θ.injective hfix))

/-- **A VECTOR IN THE REACH KERNEL IS AUTOMATICALLY ISOTROPIC.** The coupling's matrix is
symmetric under swapping which argument is mirrored (`ReachIsCoupling.crossForm_symm_matrix`), so
`crossForm v = ∑_{p ∈ H} v p · (massive *ᵥ v) (θ p)` — and the reach condition kills every one of
those factors, because `θ p` is exactly a site outside the half and off the mirror.

**So the isotropy clause of `StrictBiconditional.SupportedIsotropic` is implied by its other two.**
No block hypothesis, no coupling hypothesis, no `hcross`: this holds on every graph with a mirror
reflection and an involutive automorphism. -/
theorem crossForm_eq_zero_of_inReachKernel (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ)
    {v : V → ℝ} (hr : StrictBiconditional.InReachKernel G m H Mir v) :
    crossForm G m θ H v = 0 := by
  classical
  obtain ⟨hsupp, hreach⟩ := hr
  have hsymm : ∀ x y, GraphLaplacian.massive G m x y = GraphLaplacian.massive G m y x :=
    fun x y => congrFun (congrFun (GraphLaplacian.massive_isSymm (G := G) m).eq y) x
  have hrow : ∀ p ∈ H, ∑ q ∈ H, v q * GraphLaplacian.massive G m (θ p) q = 0 := by
    intro p hp
    have hz := hreach (θ p) (hM.notMem_of_mem hp) (mirror_notMem_mir hM hp)
    rw [Matrix.mulVec, dotProduct] at hz
    have hres : ∑ q ∈ H, GraphLaplacian.massive G m (θ p) q * v q
        = ∑ q : V, GraphLaplacian.massive G m (θ p) q * v q :=
      Finset.sum_subset (Finset.subset_univ H) (fun q _ hq => by rw [hsupp q hq]; ring)
    calc ∑ q ∈ H, v q * GraphLaplacian.massive G m (θ p) q
        = ∑ q ∈ H, GraphLaplacian.massive G m (θ p) q * v q :=
          Finset.sum_congr rfl fun q _ => by ring
      _ = ∑ q : V, GraphLaplacian.massive G m (θ p) q * v q := hres
      _ = 0 := hz
  rw [crossForm]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hsplit : ∑ q ∈ H, v p * v q * GraphLaplacian.massive G m p (θ q)
      = v p * ∑ q ∈ H, v q * GraphLaplacian.massive G m (θ p) q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by
      rw [ReachIsCoupling.crossForm_symm_matrix h m p q, hsymm q (θ p)]
      ring
  rw [hsplit, hrow p hp, mul_zero]

/-- **THE CONSISTENCY CHECK, AGAINST `ReachIsCoupling`.** That file proves
`ReachCriterion.ReachInside G m H Mir ↔ ∀ w, crossForm G m θ H w = 0` — a statement about the
graph. The forward half of it is one line from the theorem above, because `ReachInside` puts
*every* supported vector in the reach kernel. The two results are the same fact at two
quantifier depths, and the per-vector one is the stronger. -/
theorem crossForm_eq_zero_of_reachInside (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ)
    (hRI : ReachCriterion.ReachInside G m H Mir) {w : V → ℝ} (hw : ∀ p, p ∉ H → w p = 0) :
    crossForm G m θ H w = 0 :=
  crossForm_eq_zero_of_inReachKernel hM h m ⟨hw, hRI w hw⟩

/-- **AND SO THE ESTATE'S ISOTROPY PREDICATE IS A STATEMENT ABOUT THE REACH KERNEL ALONE.** -/
theorem supportedIsotropic_iff_reachKernel_ne_zero (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (m : ℝ) :
    StrictBiconditional.SupportedIsotropic G m θ H Mir ↔
      ∃ v : V → ℝ, v ≠ 0 ∧ StrictBiconditional.InReachKernel G m H Mir v := by
  constructor
  · rintro ⟨v, hv0, hvs, -, hvr⟩
    exact ⟨v, hv0, hvs, hvr⟩
  · rintro ⟨v, hv0, hr⟩
    exact ⟨v, hv0, hr.1, crossForm_eq_zero_of_inReachKernel hM h m hr, hr.2⟩

/-- **THE CRITERION, WITH THE DEFINITENESS READING REMOVED.**
`StrictBiconditional.strict_iff_crossForm_neg_on_reachKernel` presents strictness as *the coupling
is negative definite on the reach kernel*. The coupling is **identically zero** there, so that
condition can only ever hold vacuously, and what the criterion actually says is:

> **strict exactly when the reach kernel is trivial.**

The theorem is right; the reading was doing extra work. -/
theorem strict_iff_reachKernel_trivial (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ ∀ v : V → ℝ, StrictBiconditional.InReachKernel G m H Mir v → v = 0 := by
  rw [StrictBiconditional.strict_iff_not_supportedIsotropic hM h hm hcross,
    supportedIsotropic_iff_reachKernel_ne_zero hM h m]
  constructor
  · intro hno v hr
    by_contra hv0
    exact hno ⟨v, hv0, hr⟩
  · rintro htriv ⟨v, hv0, hr⟩
    exact hv0 (htriv v hr)

end ReachIsotropy

/-! ## 8. Strictness on a block cut, completely: the cut must be a perfect matching -/

section StrictComplete

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix CrossPosSemidef

variable [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ} {θ : V ≃ V} {H Mir : Finset V}

/-- The operator's entry from a mirror site back into the half is minus the cross matrix's. -/
theorem massive_mirror_entry (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ)
    {s q : V} (hs : s ∈ H) (hq : q ∈ H) :
    GraphLaplacian.massive G m (θ s) q = - crossMatrix G θ H s q := by
  classical
  have hne : θ s ≠ q := fun hc => hM.notMem_of_mem hs (hc ▸ hq)
  have hiff : G.Adj (θ s) q ↔ G.Adj s (θ q) :=
    ⟨fun ha => (adj_cross_comm h q s).mp ha.symm, fun ha => ((adj_cross_comm h q s).mpr ha).symm⟩
  rw [GraphLaplacian.massive_apply, if_neg hne, zero_sub,
    crossMatrix_apply_of_mem hs hq, crossAdj]
  by_cases ha : G.Adj s (θ q)
  · rw [if_pos ha, if_pos (hiff.mpr ha)]
  · rw [if_neg ha, if_neg fun hc => ha (hiff.mp hc)]

/-- **THE OPERATOR'S ROW AT A MIRROR SITE IS THE CROSS MATRIX'S ROW.** This is the identity §6
found on `K₂,₂`, and nothing about that graph was used. -/
theorem massive_mulVec_mirror (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ)
    {v : V → ℝ} (hv : ∀ i, i ∉ H → v i = 0) {s : V} (hs : s ∈ H) :
    (GraphLaplacian.massive G m *ᵥ v) (θ s) = - ∑ q ∈ H, crossMatrix G θ H s q * v q := by
  classical
  have hres : ∑ q ∈ H, GraphLaplacian.massive G m (θ s) q * v q
      = ∑ q : V, GraphLaplacian.massive G m (θ s) q * v q :=
    Finset.sum_subset (Finset.subset_univ H) (fun q _ hq => by rw [hv q hq]; ring)
  rw [Matrix.mulVec, dotProduct, ← hres, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun q hq => by
    rw [massive_mirror_entry hM h m hs hq]; ring

/-- **AND SO THE REACH KERNEL IS ONE LINEAR EQUATION PER HALF-SITE.** The condition the operator
imposes off the half is exactly that every row of the cross matrix annihilates `v`. -/
theorem inReachKernel_iff_rows (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ) (v : V → ℝ) :
    StrictBiconditional.InReachKernel G m H Mir v ↔
      (∀ i, i ∉ H → v i = 0) ∧ ∀ s ∈ H, ∑ q ∈ H, crossMatrix G θ H s q * v q = 0 := by
  constructor
  · rintro ⟨hv, hreach⟩
    refine ⟨hv, fun s hs => ?_⟩
    have := hreach (θ s) (hM.notMem_of_mem hs) (mirror_notMem_mir hM hs)
    rw [massive_mulVec_mirror hM h m hv hs, neg_eq_zero] at this
    exact this
  · rintro ⟨hv, hrows⟩
    refine ⟨hv, fun p hp hpM => ?_⟩
    have hs : θ p ∈ H := hM.mem_of_notMem hp hpM
    have hback : θ (θ p) = p := h.invol p
    rw [← hback, massive_mulVec_mirror hM h m hv hs, hrows (θ p) hs, neg_zero]

/-- A supported vector whose cross-matrix rows all vanish, and which is nonzero, refutes
triviality of the reach kernel. Packaged so the two witnesses below share it. -/
theorem ne_zero_of_rows (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (m : ℝ)
    (htriv : ∀ v : V → ℝ, StrictBiconditional.InReachKernel G m H Mir v → v = 0)
    {v : V → ℝ} (hvsupp : ∀ i, i ∉ H → v i = 0)
    (hrows : ∀ t ∈ H, ∑ r ∈ H, crossMatrix G θ H t r * v r = 0) : v = 0 :=
  htriv v ((inReachKernel_iff_rows hM h m v).mpr ⟨hvsupp, hrows⟩)

/-- **STRICTNESS ON A BLOCK CUT IS A PERFECT MATCHING OF THE CUT.** Every half-site joined to its
own mirror image and to no other half-site's — that is, every block a singleton and no half-site
outside a block. Purely combinatorial, and decidable on a finite graph.

Read against the lattice families this is the right shape: their cuts are diagonal, so the
condition reduces to *every half-site is joined to its own mirror*, which fails as soon as the half
is thick enough to contain a site not adjacent to the cut. **That reading is a prediction and is
not proved here** — instantiating it at the box, the torus and the estate's `def` needs each
family's cut written out, and none of that is done in this file. -/
theorem strict_iff_cut_perfect (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hC : IsCrossBlock G θ H) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ ∀ s ∈ H, ∀ q ∈ H, (G.Adj s (θ q) ↔ s = q) := by
  classical
  rw [strict_iff_reachKernel_trivial hM h hm ((hcross_iff_isCrossBlock hM h m).mpr hC)]
  constructor
  · intro htriv s hs q hq
    refine ⟨fun ha => ?_, fun hsq => ?_⟩
    · -- `e_s − e_q` is in the reach kernel, so it is zero, so `s = q`
      by_contra hsq
      set v : V → ℝ := fun x => if x = s then 1 else if x = q then -1 else 0 with hvdef
      have hvs : v s = 1 := by rw [hvdef]; simp
      have hvsupp : ∀ i, i ∉ H → v i = 0 := by
        intro i hi
        have h1 : i ≠ s := fun hc => hi (hc ▸ hs)
        have h2 : i ≠ q := fun hc => hi (hc ▸ hq)
        rw [hvdef]; simp [h1, h2]
      have hsq' : CrossRel G θ H s q := ⟨hs, hq, ha⟩
      have hqs' : CrossRel G θ H q s := crossRel_symm h hsq'
      have hrows : ∀ t ∈ H, ∑ r ∈ H, crossMatrix G θ H t r * v r = 0 := by
        intro t _
        have hsub : ({s, q} : Finset V) ⊆ H := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have houtside : ∀ r ∈ H, r ∉ ({s, q} : Finset V) → crossMatrix G θ H t r * v r = 0 := by
          intro r _ hr
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hr
          rw [hvdef]; simp [hr.1, hr.2]
        have hts : crossMatrix G θ H t s = crossMatrix G θ H t q := by
          have f1 : crossMatrix G θ H t s = 1 → crossMatrix G θ H t q = 1 := fun hh =>
            (crossMatrix_eq_one_iff t q).mpr
              ⟨((crossMatrix_eq_one_iff t s).mp hh).1, hq,
                hC.trans t s q ((crossMatrix_eq_one_iff t s).mp hh) hsq'⟩
          have f2 : crossMatrix G θ H t q = 1 → crossMatrix G θ H t s = 1 := fun hh =>
            (crossMatrix_eq_one_iff t s).mpr
              ⟨((crossMatrix_eq_one_iff t q).mp hh).1, hs,
                hC.trans t q s ((crossMatrix_eq_one_iff t q).mp hh) hqs'⟩
          rcases crossMatrix_entries (G := G) (θ := θ) (H := H) t s with e1 | e1
          · rcases crossMatrix_entries (G := G) (θ := θ) (H := H) t q with e2 | e2
            · rw [e1, e2]
            · exact absurd (f2 e2) (by rw [e1]; norm_num)
          · rcases crossMatrix_entries (G := G) (θ := θ) (H := H) t q with e2 | e2
            · exact absurd (f1 e1) (by rw [e2]; norm_num)
            · rw [e1, e2]
        rw [← Finset.sum_subset hsub houtside,
          Finset.sum_insert (by simpa using hsq), Finset.sum_singleton, hvdef]
        simp only [if_true, if_neg (Ne.symm hsq)]
        rw [hts]; ring
      have := ne_zero_of_rows hM h m htriv hvsupp hrows
      rw [this] at hvs
      exact absurd hvs (by norm_num)
    · -- `e_s` is in the reach kernel unless `s` is joined to its own mirror
      subst hsq
      by_contra ha
      set v : V → ℝ := fun x => if x = s then (1 : ℝ) else 0 with hvdef
      have hvs : v s = 1 := by rw [hvdef]; simp
      have hvsupp : ∀ i, i ∉ H → v i = 0 := by
        intro i hi
        have h1 : i ≠ s := fun hc => hi (hc ▸ hs)
        rw [hvdef]; simp [h1]
      have hnone : ∀ t : V, crossMatrix G θ H t s = 0 := by
        intro t
        rcases crossMatrix_entries (G := G) (θ := θ) (H := H) t s with e | e
        · exact e
        · exact absurd (hC.loop s t (crossRel_symm h ((crossMatrix_eq_one_iff t s).mp e))) ha
      have hrows : ∀ t ∈ H, ∑ r ∈ H, crossMatrix G θ H t r * v r = 0 := by
        intro t _
        have hsub : ({s} : Finset V) ⊆ H := by simpa using hs
        have houtside : ∀ r ∈ H, r ∉ ({s} : Finset V) → crossMatrix G θ H t r * v r = 0 := by
          intro r _ hr
          have : r ≠ s := by simpa using hr
          rw [hvdef]; simp [this]
        rw [← Finset.sum_subset hsub houtside, Finset.sum_singleton, hvdef]
        simp [hnone t]
      have := ne_zero_of_rows hM h m htriv hvsupp hrows
      rw [this] at hvs
      exact absurd hvs (by norm_num)
  · intro hmatch v hr
    obtain ⟨hvsupp, hrows⟩ := (inReachKernel_iff_rows hM h m v).mp hr
    funext x
    by_cases hx : x ∈ H
    · have hsub : ({x} : Finset V) ⊆ H := by simpa using hx
      have houtside : ∀ r ∈ H, r ∉ ({x} : Finset V) → crossMatrix G θ H x r * v r = 0 := by
        intro r hrH hr
        have hne : r ≠ x := by simpa using hr
        have hzero : crossMatrix G θ H x r = 0 := by
          rcases crossMatrix_entries (G := G) (θ := θ) (H := H) x r with e | e
          · exact e
          · exact absurd ((hmatch x hx r hrH).mp
              ((crossMatrix_eq_one_iff x r).mp e).2.2).symm hne
        rw [hzero, zero_mul]
      have hcollapse : ∑ r ∈ H, crossMatrix G θ H x r * v r = v x := by
        rw [← Finset.sum_subset hsub houtside, Finset.sum_singleton,
          crossMatrix_apply_of_mem hx hx, crossAdj, if_pos ((hmatch x hx x hx).mpr rfl), one_mul]
      rw [← hcollapse, hrows x hx]
      rfl
    · rw [hvsupp x hx]; rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A perfect matching of the cut IS a block cut, with every block a singleton — so the
hypothesis of the theorem above is free on its right-hand side. -/
theorem isCrossBlock_of_cut_perfect
    (hmatch : ∀ s ∈ H, ∀ q ∈ H, (G.Adj s (θ q) ↔ s = q)) : IsCrossBlock G θ H :=
  isCrossBlock_of_cross_diag (fun s hs q hq ha => (hmatch s hs q hq).mp ha)

/-- **AND SO SUFFICIENCY NEEDS NO BLOCK HYPOTHESIS AT ALL.** A cut that matches each half-site to
its own mirror image and to nothing else gives strictness outright. -/
theorem strict_of_cut_perfect (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hmatch : ∀ s ∈ H, ∀ q ∈ H, (G.Adj s (θ q) ↔ s = q)) :
    ∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
      0 < GraphReflection.reflectedForm G m θ c :=
  (strict_iff_cut_perfect hM h hm (isCrossBlock_of_cut_perfect hmatch)).mpr hmatch

/-- `K₂,₂`'s cut is not a matching: site `0` is joined to `ρ 1`. -/
theorem bipGraph_cut_not_perfect :
    ¬ ∀ s ∈ IndefiniteCoupling.Hh, ∀ q ∈ IndefiniteCoupling.Hh,
        (IndefiniteCoupling.bipGraph.Adj s (IndefiniteCoupling.rho q) ↔ s = q) := by
  intro hc
  exact absurd ((hc 0 (by decide) 1 (by decide)).mp (by decide)) (by decide)

/-- **THE CROSS-CHECK: §6's RESULT RE-DERIVED BY A DIFFERENT ROUTE.** §6 proved `K₂,₂` non-strict
by exhibiting an isotropic vector in the reach kernel and computing. This proves the same thing by
checking a condition on the graph's edges and nothing else, and the two agree. -/
theorem bipGraph_not_strict_of_cut (m : ℝ) (hm : m ≠ 0) :
    ¬ ∀ c : Fin 4 → ℝ, c ≠ 0 →
        (∀ p, p ∉ IndefiniteCoupling.Hh → p ∉ (∅ : Finset (Fin 4)) → c p = 0) →
        0 < GraphReflection.reflectedForm IndefiniteCoupling.bipGraph m IndefiniteCoupling.rho c :=
  fun hstrict => bipGraph_cut_not_perfect
    ((strict_iff_cut_perfect IndefiniteCoupling.isMirrorHalf_Hh
      IndefiniteCoupling.isRefl_rho_bip hm isCrossBlock_bipGraph).mp hstrict)

end StrictComplete

/-! ## 9. The prediction cashed on the torus: the threshold falls out of the criterion -/

section Torus

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix
open BoxOddReflection TorusReflection TorusAnySide

variable {d n : ℕ} {m : ℝ}

/-- The torus cut is diagonal at every side (`TorusAnySide.torus_cross_diag_any`), so it is a
block cut with every block a singleton or empty. One line, and it is the whole of what §8's
hypothesis needs here. -/
theorem isCrossBlock_torus (i : Fin d) (n : ℕ) :
    IsCrossBlock (torusGraph d n) (revSite (n := n) i) (strictLower i n) :=
  isCrossBlock_of_cross_diag (torus_cross_diag_any i n)

/-- **A HALF-SITE OF THE TORUS IS JOINED TO ITS OWN MIRROR EXACTLY AT THE TWO EXTREME LAYERS.**
Either it sits on the boundary layer, where the wrap-around bond reaches its mirror, or it sits on
the innermost layer of an even side, where the mirror is the neighbour across the cut. Everything
between is joined to nothing across the cut, and that is what breaks strictness. -/
theorem torus_adj_self_mirror_iff (i : Fin d) {n : ℕ} {s : BoxGraph.Site d n}
    (hs : s ∈ strictLower i n) :
    (torusGraph d n).Adj s (revSite (n := n) i s) ↔ (s i).val = 0 ∨ 2 * (s i).val + 2 = n := by
  rw [mem_strictLower] at hs
  have hlt := (s i).isLt
  have hrev : (Fin.rev (s i)).val = n - ((s i).val + 1) := Fin.val_rev (s i)
  constructor
  · rintro ⟨k, hoff, hne, hcases⟩
    have hki : k = i := by
      by_contra hk
      have hcoord := hoff i (fun hc => hk hc.symm)
      rw [revSite_apply_self] at hcoord
      have hv := congrArg Fin.val hcoord
      rw [hrev] at hv
      omega
    subst hki
    rw [revSite_apply_self] at hcases
    rw [hrev] at hcases
    omega
  · intro hor
    refine ⟨i, fun j hj => (revSite_apply_ne hj s).symm, ?_, ?_⟩
    · rw [revSite_apply_self]
      intro hc
      have := congrArg Fin.val hc
      rw [hrev] at this
      omega
    · rw [revSite_apply_self, hrev]
      omega

/-- **AND SO §8's CRITERION READS OFF THE TORUS THRESHOLD.** Strictness on the torus, at every
side length and in every dimension, is the condition that every half-site sits on one of the two
extreme layers. -/
theorem torus_strict_iff_layers (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ strictLower i n → p ∉ midLayer i n → c p = 0) →
        0 < GraphReflection.reflectedForm (torusGraph d n) m (revSite (n := n) i) c)
      ↔ ∀ s ∈ strictLower i n, (s i).val = 0 ∨ 2 * (s i).val + 2 = n := by
  rw [strict_iff_cut_perfect (isMirrorHalf_strictLower i n) (isRefl_torus i) hm
    (isCrossBlock_torus i n)]
  constructor
  · intro hall s hs
    exact (torus_adj_self_mirror_iff i hs).mp ((hall s hs s hs).mpr rfl)
  · intro hlayers s hs q hq
    exact ⟨torus_cross_diag_any i n s hs q hq,
      fun hsq => hsq ▸ (torus_adj_self_mirror_iff i hs).mpr (hlayers s hs)⟩

/-- **THE LAYER CONDITION IS `n ≤ 4`, AND NOTHING ABOUT THE DIMENSION.** Every half-site is on an
extreme layer exactly when the side is at most four: at five and above the layer `1` is strictly
inside the half and is joined to nothing across the cut. -/
theorem torus_layers_iff_le_four (i : Fin d) (n : ℕ) :
    (∀ s ∈ strictLower i n, (s i).val = 0 ∨ 2 * (s i).val + 2 = n) ↔ n ≤ 4 := by
  constructor
  · intro hall
    by_contra hn
    have h4 : 4 < n := by omega
    have h1 : (1 : ℕ) < n := by omega
    have hmem : (fun _ => (⟨1, h1⟩ : Fin n)) ∈ strictLower i n :=
      mem_strictLower.mpr (by simpa using by omega)
    rcases hall _ hmem with h | h <;> simp only [] at h <;> omega
  · intro hn s hs
    rw [mem_strictLower] at hs
    omega

/-- **THE THRESHOLD, AS `WALLS` W1 RECORDS IT — NOW A COROLLARY OF THE CUT CRITERION.** Strict at
side four and below, not from five up, in every dimension and at every nonzero mass. The estate
proved the two halves separately, by two different mechanisms
(`SmallSideStrict` upward, `TorusNotStrict.not_strict_torus` downward and only at even sides from
six); this is one statement and it covers the odd sides too. -/
theorem torus_strict_iff_le_four (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ strictLower i n → p ∉ midLayer i n → c p = 0) →
        0 < GraphReflection.reflectedForm (torusGraph d n) m (revSite (n := n) i) c)
      ↔ n ≤ 4 :=
  (torus_strict_iff_layers i n hm).trans (torus_layers_iff_le_four i n)

/-- **THE SAME STATEMENT IN THE ESTATE'S OWN SUPPORT CONVENTION**, so that the comparison with
`TorusNotStrict.not_strict_torus`, `OddNotStrictInstances.not_strict_torus_odd`,
`SmallSideStrict.reflectionPositive_torus_one_strict` / `_two_strict` and
`MirrorStrict.reflectionPositive_torus_three_strict` / `_four_strict` is literal rather than
approximate: those six theorems quantify over `c` supported on `lowerHalf`, which is
`strictLower ∪ midLayer` (`BoxOddReflection.lowerHalf_eq_union`).

**No new case is decided here.** The six cover `n ≤ 4` and `n ≥ 5` between them, in four files, by
two mechanisms each side, with the non-strict half split by parity. What this adds is that they are
**one statement with one proof**, uniform in `n` and in `d`, obtained by reading a condition off
the cut. -/
theorem torus_strict_iff_le_four_lowerHalf (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 → (∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (torusGraph d n) m (revSite (n := n) i) c)
      ↔ n ≤ 4 := by
  have hsupp : ∀ p : BoxGraph.Site d n,
      p ∉ GraphHalfSpace.lowerHalf i n ↔ (p ∉ strictLower i n ∧ p ∉ midLayer i n) := by
    intro p
    rw [lowerHalf_eq_union, Finset.mem_union, not_or]
  rw [← torus_strict_iff_le_four i n hm]
  constructor
  · intro hstrict c hc0 hcsupp
    refine hstrict c hc0 (fun p hp => ?_)
    obtain ⟨hpS, hpM⟩ := (hsupp p).mp hp
    exact hcsupp p hpS hpM
  · intro hstrict c hc0 hcsupp
    exact hstrict c hc0 (fun p hpS hpM => hcsupp p ((hsupp p).mpr ⟨hpS, hpM⟩))

/-- **THE NON-STRICT HALF, AT EVERY SIDE FROM FIVE AND WITHOUT A PARITY SPLIT.** The estate proves
this in two files: `TorusNotStrict.not_strict_torus` at EVEN sides from six, by a null-direction
construction, and `OddNotStrictInstances.not_strict_torus_odd` at ODD sides from five, by a second
one that had to dodge the wrap-around. Both are instances of this. -/
theorem torus_not_strict_of_five_le (i : Fin d) (n : ℕ) (h5 : 5 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (torusGraph d n) m (revSite (n := n) i) c) :=
  fun hstrict => absurd ((torus_strict_iff_le_four_lowerHalf i n hm).mp hstrict) (by omega)

/-- **AND THE STRICT HALF, AT EVERY SIDE UP TO FOUR.** The estate proves this in two files as well
— `SmallSideStrict.reflectionPositive_torus_one_strict` and `_two_strict`,
`MirrorStrict.reflectionPositive_torus_three_strict` and `_four_strict`, one theorem per side. All
four are instances of this, and so is `n = 0`, which none of them names. -/
theorem torus_strict_of_le_four (i : Fin d) (n : ℕ) (hn : n ≤ 4) (hm : m ≠ 0)
    {c : BoxGraph.Site d n → ℝ} (hc0 : c ≠ 0)
    (hcsupp : ∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) :
    0 < GraphReflection.reflectedForm (torusGraph d n) m (revSite (n := n) i) c :=
  (torus_strict_iff_le_four_lowerHalf i n hm).mpr hn c hc0 hcsupp

end Torus

/-! ## 10. And on the box, where there is no wrap-around, the threshold is two -/

section Box

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix
open BoxOddReflection BoxGraph TorusReflection

variable {d n : ℕ} {m : ℝ}

/-- **THE BOX CUT IS DIAGONAL AT EVERY SIDE.** The estate has this in two halves —
`TorusReflection.boxGraph_cross_diag` at even sides and `BoxOddReflection.not_adj_cross_odd`, which
says the cut is EMPTY at odd sides — and both are on `lowerHalf`. Proved directly here on
`strictLower`, at every side, because §8's criterion wants exactly this shape. -/
theorem box_cross_diag_any (i : Fin d) (n : ℕ) :
    ∀ p ∈ strictLower i n, ∀ q ∈ strictLower i n,
      (boxGraph d n).Adj p (revSite (n := n) i q) → p = q := by
  intro p hp q hq hadj
  rw [mem_strictLower] at hp hq
  obtain ⟨k, hoff, hcase⟩ := hadj
  have hrevq : ∀ j, (revSite (n := n) i q) j = if j = i then Fin.rev (q i) else q j := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [revSite_apply_ne hj, hj]
  have hvrev : (Fin.rev (q i)).val = n - ((q i).val + 1) := Fin.val_rev (q i)
  have hqlt := (q i).isLt
  have hki : k = i := by
    by_contra hk
    have hcoord := hoff i (fun hc => hk hc.symm)
    rw [hrevq i, if_pos rfl] at hcoord
    have hv := congrArg Fin.val hcoord
    rw [hvrev] at hv
    omega
  subst hki
  rw [hrevq k, if_pos rfl] at hcase
  rw [hvrev] at hcase
  have hik : (p k).val = (q k).val := by omega
  funext j
  by_cases hj : j = k
  · subst hj; exact Fin.ext hik
  · have := hoff j hj
    rwa [hrevq j, if_neg hj] at this

/-- The box cut is a block cut at every side, one line from the above. -/
theorem isCrossBlock_box (i : Fin d) (n : ℕ) :
    IsCrossBlock (boxGraph d n) (revSite (n := n) i) (strictLower i n) :=
  isCrossBlock_of_cross_diag (box_cross_diag_any i n)

/-- **AND A BOX HALF-SITE IS JOINED TO ITS OWN MIRROR ONLY ON THE INNERMOST LAYER OF AN EVEN
SIDE.** This is the whole difference from the torus: **there is no wrap-around bond**, so the
boundary layer is joined to nothing across the cut and only one layer ever is. -/
theorem box_adj_self_mirror_iff (i : Fin d) {n : ℕ} {s : BoxGraph.Site d n}
    (hs : s ∈ strictLower i n) :
    (boxGraph d n).Adj s (revSite (n := n) i s) ↔ 2 * (s i).val + 2 = n := by
  rw [mem_strictLower] at hs
  have hlt := (s i).isLt
  have hrev : (Fin.rev (s i)).val = n - ((s i).val + 1) := Fin.val_rev (s i)
  constructor
  · rintro ⟨k, hoff, hcase⟩
    have hki : k = i := by
      by_contra hk
      have hcoord := hoff i (fun hc => hk hc.symm)
      rw [revSite_apply_self] at hcoord
      have hv := congrArg Fin.val hcoord
      rw [hrev] at hv
      omega
    subst hki
    rw [revSite_apply_self, hrev] at hcase
    omega
  · intro hn
    refine ⟨i, fun j hj => (revSite_apply_ne hj s).symm, ?_⟩
    rw [revSite_apply_self, hrev]
    omega

/-- **THE BOX THRESHOLD, READ OFF THE CUT: STRICT EXACTLY AT SIDE TWO AND BELOW.** `WALLS` W1
records the box as strict at sides 1–2 and not from 3, proved by separate arguments; here it is one
biconditional, and the reason for the smaller threshold than the torus's is visible in the
statement — no wrap-around, so the boundary layer never reaches its mirror. -/
theorem box_strict_iff_le_two (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ strictLower i n → p ∉ midLayer i n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph d n) m (revSite (n := n) i) c)
      ↔ n ≤ 2 := by
  rw [strict_iff_cut_perfect (isMirrorHalf_strictLower i n) (boxGraph_revSite_aut i) hm
    (isCrossBlock_box i n)]
  constructor
  · intro hall
    by_contra hn
    have h2 : 2 < n := by omega
    have h0 : (0 : ℕ) < n := by omega
    have hmem : (fun _ => (⟨0, h0⟩ : Fin n)) ∈ strictLower i n :=
      mem_strictLower.mpr (by simpa using by omega)
    have := (box_adj_self_mirror_iff i hmem).mp ((hall _ hmem _ hmem).mpr rfl)
    simp only [] at this
    omega
  · intro hn s hs q hq
    refine ⟨box_cross_diag_any i n s hs q hq, fun hsq => hsq ▸ ?_⟩
    refine (box_adj_self_mirror_iff i hs).mpr ?_
    rw [mem_strictLower] at hs
    omega

/-- **THE SAME, IN THE ESTATE'S `lowerHalf` SUPPORT CONVENTION**, so the comparison with
`BoxNotStrict` and `SmallSideStrict.reflectionPositive_box_one_strict'` is literal. -/
theorem box_strict_iff_le_two_lowerHalf (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph d n) m (revSite (n := n) i) c)
      ↔ n ≤ 2 := by
  have hsupp : ∀ p : BoxGraph.Site d n,
      p ∉ GraphHalfSpace.lowerHalf i n ↔ (p ∉ strictLower i n ∧ p ∉ midLayer i n) := by
    intro p
    rw [lowerHalf_eq_union, Finset.mem_union, not_or]
  rw [← box_strict_iff_le_two i n hm]
  constructor
  · intro hstrict c hc0 hcsupp
    refine hstrict c hc0 (fun p hp => ?_)
    obtain ⟨hpS, hpM⟩ := (hsupp p).mp hp
    exact hcsupp p hpS hpM
  · intro hstrict c hc0 hcsupp
    exact hstrict c hc0 (fun p hpS hpM => hcsupp p ((hsupp p).mpr ⟨hpS, hpM⟩))

/-- **THE NON-STRICT HALF, AT EVERY SIDE FROM THREE AND WITHOUT A PARITY SPLIT.** The estate proves
this in two files — `BoxNotStrict.not_strict` at EVEN sides from four and
`BoxOddNotStrict.not_strict_box_odd` at ODD sides from three, the second going through the reach
criterion because the odd box's cut is empty. Both are instances of this. -/
theorem box_not_strict_of_three_le (i : Fin d) (n : ℕ) (h3 : 3 ≤ n) (hm : m ≠ 0) :
    ¬ (∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph d n) m (revSite (n := n) i) c) :=
  fun hstrict => absurd ((box_strict_iff_le_two_lowerHalf i n hm).mp hstrict) (by omega)

/-- **AND THE STRICT HALF, AT SIDES TWO AND BELOW.** Instances:
`StrictCriterion.reflectionPositive_box_one_strict` and `_box_two_strict`, and
`SmallSideStrict.reflectionPositive_box_one_strict'`. `n = 0` falls out too. -/
theorem box_strict_of_le_two (i : Fin d) (n : ℕ) (hn : n ≤ 2) (hm : m ≠ 0)
    {c : BoxGraph.Site d n → ℝ} (hc0 : c ≠ 0)
    (hcsupp : ∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) :
    0 < GraphReflection.reflectedForm (boxGraph d n) m (revSite (n := n) i) c :=
  (box_strict_iff_le_two_lowerHalf i n hm).mpr hn c hc0 hcsupp

/-- **THE TWO FAMILIES SIDE BY SIDE, AND THE WRAP-AROUND IS THE WHOLE DIFFERENCE.** Same criterion,
same reflection, same half; the torus threshold is four and the box's is two, and the extra two
sides are the boundary layer that the wrap-around bond reaches and the box has no bond to. -/
theorem box_and_torus_thresholds (i : Fin d) (n : ℕ) (hm : m ≠ 0) :
    ((∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph d n) m (revSite (n := n) i) c) ↔ n ≤ 2)
      ∧ ((∀ c : BoxGraph.Site d n → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf i n → c p = 0) →
        0 < GraphReflection.reflectedForm (torusGraph d n) m (revSite (n := n) i) c) ↔ n ≤ 4) :=
  ⟨box_strict_iff_le_two_lowerHalf i n hm, torus_strict_iff_le_four_lowerHalf i n hm⟩

end Box

/-! ## 11. And the estate's own `def`, by transport -/

section Lattice

open GreenExpansion GraphReflection GraphMirrorReflection CrossFormMatrix
open BoxGraph IsingFiniteVolume LatticeReflectionPositive

variable {n : ℕ} {m : ℝ}

/-- The push-forward of `SmallSideStrict.pullback_conditions`: a family on the general box that is
nonzero and supported on `lowerHalf` transports to one on the estate's box that is nonzero and
supported on `lowerHalfPair`, and reindexing recovers the original. -/
theorem pushforward_conditions {c' : BoxGraph.Site 2 n → ℝ} (hc0 : c' ≠ 0)
    (hsupp : ∀ p, p ∉ GraphHalfSpace.lowerHalf (0 : Fin 2) n → c' p = 0) :
    (fun q : IsingFiniteVolume.Site n => c' ((sitePair n).symm q)) ≠ 0
      ∧ (∀ q, q ∉ lowerHalfPair n → c' ((sitePair n).symm q) = 0)
      ∧ (fun p : BoxGraph.Site 2 n => c' ((sitePair n).symm (sitePair n p))) = c' := by
  classical
  refine ⟨?_, ?_, funext fun p => by rw [Equiv.symm_apply_apply]⟩
  · intro hzero
    refine hc0 (funext fun p => ?_)
    have := congrFun hzero (sitePair n p)
    rwa [Equiv.symm_apply_apply] at this
  · intro q hq
    refine hsupp _ fun hmem => hq ?_
    rw [← map_lowerHalf n]
    exact Finset.mem_map.mpr ⟨(sitePair n).symm q, hmem, by simp⟩

/-- **THE ESTATE'S OWN `def` HAS THE BOX'S THRESHOLD, WHICH IS THE ONE THING IT COULD HAVE.** The
lattice `def` is the two-dimensional box transported (`LatticeNotStrict.reflectedForm_lattice_eq`),
so this is a transport of §10 rather than a third instance of the criterion — and the transport is
an equality of forms, so nothing is lost in either direction. -/
theorem lattice_strict_iff_le_two (n : ℕ) (hm : m ≠ 0) :
    (∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 →
        (∀ p, p ∉ lowerHalfPair n → c p = 0) →
        0 < GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph n) m
              (LatticeReflection.refl n) c)
      ↔ n ≤ 2 := by
  rw [← box_strict_iff_le_two_lowerHalf (0 : Fin 2) n hm]
  constructor
  · intro hlat c' hc0 hsupp
    obtain ⟨hne, hs, hback⟩ := pushforward_conditions hc0 hsupp
    have hpos := hlat _ hne hs
    rw [LatticeNotStrict.reflectedForm_lattice_eq
      (m := m) (fun q => c' ((sitePair n).symm q)), hback] at hpos
    exact hpos
  · intro hbox c hc0 hcsupp
    rw [LatticeNotStrict.reflectedForm_lattice_eq (m := m) c]
    obtain ⟨hne, hsupp⟩ := SmallSideStrict.pullback_conditions hc0 hcsupp
    exact hbox _ hne hsupp

/-- **ALL THREE FAMILIES, IN ONE STATEMENT.** The estate's three sharpness thresholds, each
previously several theorems by several mechanisms, read off one criterion about edges. The torus
gains two sides over the other two, and the reason is a single bond: the wrap-around. -/
theorem all_three_thresholds (n : ℕ) (hm : m ≠ 0) :
    ((∀ c : BoxGraph.Site 2 n → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf (0 : Fin 2) n → c p = 0) →
        0 < GraphReflection.reflectedForm (boxGraph 2 n) m
              (revSite (n := n) (0 : Fin 2)) c) ↔ n ≤ 2)
      ∧ ((∀ c : BoxGraph.Site 2 n → ℝ, c ≠ 0 →
        (∀ p, p ∉ GraphHalfSpace.lowerHalf (0 : Fin 2) n → c p = 0) →
        0 < GraphReflection.reflectedForm (TorusReflection.torusGraph 2 n) m
              (revSite (n := n) (0 : Fin 2)) c) ↔ n ≤ 4)
      ∧ ((∀ c : IsingFiniteVolume.Site n → ℝ, c ≠ 0 →
        (∀ p, p ∉ lowerHalfPair n → c p = 0) →
        0 < GraphReflection.reflectedForm (IsingContourSeparation.latticeGraph n) m
              (LatticeReflection.refl n) c) ↔ n ≤ 2) :=
  ⟨box_strict_iff_le_two_lowerHalf (0 : Fin 2) n hm,
    torus_strict_iff_le_four_lowerHalf (0 : Fin 2) n hm,
    lattice_strict_iff_le_two n hm⟩

end Lattice

end CrossBlockStructure
