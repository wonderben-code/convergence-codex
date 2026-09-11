import FieldSymmetryFinite

/-!
# The symmetry MATRICES counted, from the product decomposition

`FieldSymmetryFinite` proved the criterion — the symmetries are finite iff every eigenspace of the
graph's Laplacian is at most a line — and fenced exactly one thing about the count it quoted:
`card_of_finite` restates `FieldLineCount.card_symmetries`, which counts **isometries**, and
*that the MATRICES number `2 ^ |V|` is not stated and would need the matrix-to-isometry map shown
injective*. **This file states it, and not by building that map.**

**`card_symmetryMatrices_of_injective`** — at a simple spectrum the symmetry matrices number
exactly `2 ^ |V|`, computed from `FieldBlockProduct.symmetry_mulEquiv_prod`: the group is a product
of one orthogonal group per distinct eigenvalue, each factor is the orthogonal group of a LINE and
so has exactly two elements, and at a simple spectrum there are `|V|` distinct eigenvalues. So the
count is `Nat.card_pi` plus arithmetic, and the isometry side is never mentioned.

**`card_symmetryMatrices_iff`** gives the same count under the graph-only hypothesis of
`FieldSymmetryFinite.finite_iff_lapMatrix`, so the sentence a reader wants — *this many symmetry
matrices, on any graph whose Laplacian has `|V|` distinct eigenvalues* — is one theorem.

## Two counts that agree, and what that does and does not show

`FieldLineCount.card_symmetries` counts the **isometries** at `2 ^ |V|`; this file counts the
**matrices** at `2 ^ |V|`. The two arguments share nothing: that one goes through sign patterns on
the eigenvector basis, this one through block diagonalisation and a product. **The agreement is
consistent with the matrix-to-isometry correspondence being a bijection and does not prove it** —
two sets of equal finite cardinality need no canonical bijection, and none is constructed here. A
reader wanting *the same symmetries counted twice* rather than *two counts that agree* still needs
`FieldOrthIsometry`'s map shown injective, which is **not attempted, 11 September 2026**, and no
cost is claimed (`ERRATUM 246`).

## What is NOT here

* **No count at a degenerate spectrum, and `Nat.card` would lie about it.** `Nat.card` of an
  infinite type is `0`, so a product formula stated without the simplicity hypothesis would read as
  *zero symmetries* where the truth is infinitely many. The hypothesis is load-bearing and the
  degenerate case is `FieldSymmetryFinite.infinite_symmetryMatrices_of_two_le_finrank`.
* **No count of the `Subgroup`.** `FieldSymmetrySubgroup.symmetrySubgroup` has the same elements by
  `submonoidEquiv`, so the number transports, but no statement about it is written here.
* **Nothing about which graphs.** Unchanged: the criterion is on the spectrum, and which graphs have
  a simple Laplacian spectrum is a separate open item.
* **No group structure identified.** That this group of order `2 ^ |V|` is `(ℤ/2)^V` is
  `FieldSignGroup.signMulEquiv`, on the isometry side; the product decomposition here gives the
  ORDER and not the isomorphism type, and deriving `(ℤ/2)^V` from `∏ᵢ O(1)` is not attempted.

**No wall moves.** `W1`'s open part is still `OS0`, `OS4` and `OS1` in its continuum sense.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[Fintype V]` and `[DecidableEq V]`
throughout. **`m ≠ 0` is taken by two of the six declarations** — the two counts in §3 — and only
because `eigMu` and `symmetry_mulEquiv_prod` do. The four in §§1–2 take no mass and no graph:
`neg_one_mem_unitaryGroup`, `coe_eq_one_or_neg_one` and `card_unitaryGroup_of_nonempty` work over
an abstract index with `[Subsingleton n]` and mention no `V` at all, and `card_lev_of_injective` is
a statement about an arbitrary `d : V → ℝ`. **`neg_one_mem_unitaryGroup` takes no `[Subsingleton n]`
either**: it holds at every finite index, which the unused-variable linter reported and which is
recorded rather than silently omitted, since a lemma stated more narrowly than it is true is the
mirror image of `ERRATUM 455`'s defect. **Its name is `_unitaryGroup`-suffixed because plain
`neg_one_mem` is taken** — `SpinVectorRep` has one about the spin group of a Clifford algebra, a
different statement in a different namespace, and `newnames_scan.py` flagged the collision; renamed
rather than accepted, so a reader grepping the estate for `neg_one_mem` finds one theorem.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldSymmetryCount

open Matrix GraphLaplacian FieldRotationCount FieldBlockDiagonal FieldBlockProduct

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The orthogonal group of a line has exactly two elements -/

section Line
variable {n : Type*} [Fintype n] [DecidableEq n] [Subsingleton n]

omit [Subsingleton n] in
/-- `-1` is orthogonal. **This one needs no `[Subsingleton n]`** — it holds at every finite index,
and the linter is what pointed that out. -/
theorem neg_one_mem_unitaryGroup : (-1 : Matrix n n ℝ) ∈ Matrix.unitaryGroup n ℝ := by
  refine (mem_unitaryGroup_iff_transpose _).2 ?_
  rw [Matrix.transpose_neg, Matrix.transpose_one, neg_mul_neg, Matrix.one_mul]

/-- **A UNITARY MATRIX ON A SUBSINGLETON INDEX IS `1` OR `-1`.** On an empty index the two
conclusions coincide, because there is only one matrix at all. -/
theorem coe_eq_one_or_neg_one (M : Matrix.unitaryGroup n ℝ) :
    (M : Matrix n n ℝ) = 1 ∨ (M : Matrix n n ℝ) = -1 := by
  rcases isEmpty_or_nonempty n with hE | hN
  · exact Or.inl (Matrix.ext fun i _ => (hE.false i).elim)
  · obtain ⟨i⟩ := hN
    have hsq := FieldSymmetryFinite.diag_mul_self M.2 i
    have hentry : ∀ j k : n, (M : Matrix n n ℝ) j k = (M : Matrix n n ℝ) i i := fun j k => by
      rw [Subsingleton.elim j i, Subsingleton.elim k i]
    have hone : ∀ j k : n, (1 : Matrix n n ℝ) j k = 1 := fun j k => by
      rw [Subsingleton.elim j k, Matrix.one_apply_eq]
    have hneg : ∀ j k : n, (-1 : Matrix n n ℝ) j k = -1 := fun j k => by
      rw [Matrix.neg_apply, hone]
    rcases mul_self_eq_one_iff.1 hsq with h1 | h1
    · exact Or.inl (Matrix.ext fun j k => by rw [hentry j k, h1, hone])
    · exact Or.inr (Matrix.ext fun j k => by rw [hentry j k, h1, hneg])

/-- **SO IT HAS EXACTLY TWO ELEMENTS** when the index is a nonempty subsingleton — the orthogonal
group of a line. No graph, no mass, no `V`. -/
theorem card_unitaryGroup_of_nonempty [Nonempty n] :
    Nat.card (Matrix.unitaryGroup n ℝ) = 2 := by
  obtain ⟨i⟩ := ‹Nonempty n›
  refine Nat.card_eq_two_iff.2 ⟨1, ⟨-1, neg_one_mem_unitaryGroup⟩, ?_, ?_⟩
  · intro hEq
    have h : (1 : Matrix n n ℝ) = -1 := congrArg Subtype.val hEq
    have := congrFun (congrFun h i) i
    rw [Matrix.one_apply_eq, Matrix.neg_apply, Matrix.one_apply_eq] at this
    norm_num at this
  · ext M
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases coe_eq_one_or_neg_one M with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

end Line

/-! ## 2. How many distinct levels an injective level function has -/

omit [DecidableEq V] in
/-- An injective level function attains `|V|` distinct levels. -/
theorem card_lev_of_injective {d : V → ℝ} (hd : Function.Injective d) :
    Nat.card (Lev d) = Fintype.card V := by
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Equiv.ofInjective d hd)).symm

/-! ## 3. The count -/

/-- **THE SYMMETRY MATRICES NUMBER `2 ^ |V|` WHENEVER THE PROPAGATOR'S SPECTRUM IS SIMPLE**, at
every finite graph. The proof is the product decomposition and arithmetic: `|V|` factors, two
elements each. **No isometry appears anywhere in it.** -/
theorem card_symmetryMatrices_of_injective (hm : m ≠ 0)
    (hsimple : Function.Injective (eigMu G m hm)) :
    Nat.card ↥(symmetryMatrices G m) = 2 ^ Fintype.card V := by
  haveI : ∀ c : Lev (eigMu G m hm), Subsingleton (Fib (eigMu G m hm) (c : ℝ)) :=
    fun c => FieldSymmetryFinite.subsingleton_fib hsimple _
  haveI : ∀ c : Lev (eigMu G m hm), Nonempty (Fib (eigMu G m hm) (c : ℝ)) :=
    fun c => fib_nonempty _ c
  have hcong : Nat.card ↥(symmetryMatrices G m)
      = Nat.card (∀ c : Lev (eigMu G m hm),
          Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) :=
    Nat.card_congr ((Equiv.subtypeEquivRight fun _ => Iff.rfl).trans
      (symmetry_mulEquiv_prod hm).toEquiv)
  have h2 : ∀ c : Lev (eigMu G m hm),
      Nat.card (Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) = 2 :=
    fun _ => card_unitaryGroup_of_nonempty
  rw [hcong, Nat.card_pi, Finset.prod_congr rfl fun c _ => h2 c, Finset.prod_const,
    Finset.card_univ, ← Nat.card_eq_fintype_card, card_lev_of_injective hsimple]

/-- **AND IN GRAPH VOCABULARY.** The hypothesis is `FieldSymmetryFinite.finite_iff_lapMatrix`'s:
every eigenspace of the graph's Laplacian is at most a line. No propagator appears in it. -/
theorem card_symmetryMatrices_of_lapMatrix (hm : m ≠ 0)
    (hdim : ∀ ν : ℝ, Module.finrank ℝ
      (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1) :
    Nat.card ↥(symmetryMatrices G m) = 2 ^ Fintype.card V :=
  card_symmetryMatrices_of_injective hm
    ((FieldSimpleConverse.finrank_lapMatrix_le_one_iff hm (green_isHermitian G m hm)).1 hdim)

end FieldSymmetryCount
