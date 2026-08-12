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

end CrossBlockStructure
