import FieldSymmetrySubgroup
import FieldSimpleConverse
import FieldLineCount

/-!
# When the symmetry group is finite: a criterion for every finite graph

This estate has counted the symmetries of the Gaussian field on the **line** (`FieldLineCount`) and
on the **paw** (`PawSimpleSpectrum`), and shown them **infinite** on the **torus**
(`FieldTorusRotation`) and on the **box** (`FieldSymmetryGroup.infinite_symmetrySubmonoid_box`).
Four graphs, four separate theorems, and no statement saying which graphs fall on which side.
**This file replaces all four with one criterion**, stated in graph vocabulary and holding at every
finite graph and every non-zero mass:

**`finite_iff_lapMatrix`** — the symmetries are **finite iff every eigenspace of the graph's
Laplacian is at most a line**, equivalently (`FieldSimpleConverse.finrank_lapMatrix_le_one_iff`)
iff the Laplacian has `|V|` distinct eigenvalues. `finite_iff_injective` is the same statement
about the propagator's spectrum, and `card_of_finite` says the count is `2 ^ |V|` whenever it is
finite — so the criterion decides the size as well as the finiteness.

## What carries it, and both halves were already most of the way here

* **INFINITE.** `FieldRotationCount.infinite_symmetryMatrices_of_independent_eigenpair` has taken a
  degenerate eigenvalue to an infinite symmetry set since 5 September, at an arbitrary graph. What
  was missing was the step from *the eigenvalue is degenerate* to *there is an independent
  eigenpair*, which is `FieldCycleRotation.exists_independent_of_two_le_finrank`, and the
  translation between eigenspace dimension and fibre size, which is
  `FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre`. **The torus theorem was this theorem
  with a graph fixed.**
* **FINITE.** This half is new and it is the product decomposition doing work.
  `FieldBlockProduct.symmetry_mulEquiv_prod` makes the symmetry monoid a product of the orthogonal
  groups of the eigenspaces; at a simple spectrum every fibre is a subsingleton, and
  `finite_unitaryGroup_of_subsingleton` says the orthogonal group of a space of dimension at most
  one is finite — two elements when the space is a line, one when it is zero. **A product of
  finitely many finite groups over a finite index is finite**, and the index `Lev` is finite
  because `V` is. That is the whole proof.

## What is NOT here

* **No new count.** `card_of_finite` is `FieldLineCount.card_symmetries` restated on the
  graph-only hypothesis; the arithmetic `2 ^ |V|` is not re-derived and the product route is **not**
  used to recompute it. Deriving `2 ^ |V|` from `∏ᵢ O(1)` would be an independent second proof:
  **not attempted by this file, 10 September 2026**, and no cost is claimed (`ERRATUM 246`). The
  route would be `Fintype.card` of the product — two elements per level, `|V|` levels at a simple
  spectrum — and nothing here computes it.
* **No characterisation of WHICH graphs have a simple Laplacian spectrum.** That is a separate
  `UNLOCK_WATCHLIST` item and this file does not touch it: the criterion is stated in terms of the
  spectrum, not in terms of edges, so it decides nothing about a graph presented combinatorially.
  Two graphs are known to satisfy it (the path, the paw) and the edgeless graph on two or more
  vertices is known to fail it.
* **No infinite CARDINAL.** `Set.Infinite` says the set is not finite and nothing about which
  infinity; the symmetry group of a degenerate eigenvalue contains a circle, and that is not
  stated.
* **THE CRITERION IS ABOUT MATRICES AND THE COUNT IS ABOUT ISOMETRIES, and the two are not the
  same set.** `FieldRotationCount.symmetryMatrices` is a set of matrices and every statement in
  §§1–5 is about it, EXCEPT `card_of_finite`, whose conclusion is about
  `FieldLineCount.symmetries` — a set of `EuclideanSpace ℝ V ≃ₗᵢ[ℝ] EuclideanSpace ℝ V` — because
  that is where this estate's count lives. So `card_of_finite` reads *the matrices being finite
  implies the isometries number `2 ^ |V|`*, which is true and is **not** the statement that the
  matrices number `2 ^ |V|`. **That statement is not made here**, and making it would need the
  matrix-to-isometry correspondence shown injective, which is `FieldOrthIsometry`'s subject and is
  not attempted (`ERRATUM 246`). A reader wanting one set counted should read the conclusion, not
  the hypothesis.
  ⚠ **THE CORRESPONDENCE IS SHOWN AND THE MATRICES ARE COUNTED, 2026-09-11, kept as written**
  (`ERRATUM 94`): `FieldSymmetryHom.symmetriesEquiv` is the bijection this paragraph asks for —
  `isoMat` one way, `FieldOrthIsometry.orthIsometry` the other, exactly as predicted — and
  `FieldSymmetryHom.card_symmetryMatrices_of_finite` is the statement this paragraph says is not
  made: the matrices being finite implies **the matrices** number `2 ^ |V|`. **Everything else in
  this paragraph stands**, including that this file states only the isometry count.

**No wall moves.** `W1`'s open part is still `OS0`, `OS4` and `OS1` in its continuum sense. A
criterion for the finiteness of a finite-volume symmetry group is a shadow known exactly.

**THE HYPOTHESES, READ OFF THE BINDERS** (`ERRATUM 455`): `[Fintype V]` and `[DecidableEq V]`
throughout. **`m ≠ 0` is taken by six of the nine declarations**, and only because `green`,
`eigMu` and the estate's rotation machinery all need the propagator to be positive definite. The
**three** that take no mass are `diag_mul_self`, `finite_unitaryGroup_of_subsingleton` and
`subsingleton_fib` — linear algebra and set theory with no graph in them, and the first two take no
`V`, `G` or `m` at all, working over their own index type with `[Subsingleton n]`.

**AND THIS PARAGRAPH'S FIRST DRAFT PUT THE DENOMINATOR AT EIGHT AND THE MASSLESS COUNT AT TWO**, in
a file of nine with three. Caught by `binder_scan.py` before the commit — the second unit running
in which that scanner has corrected its own author's header (`ERRATUM 488`). The count is
`binder_scan.py FieldSymmetryFinite.lean`, whose table also shows the split. *The wrong figures are
described here rather than quoted, because the scanner reads a quoted denominator as a live one —
a blind spot found by writing this sentence and now recorded in the mode's own output.*

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace FieldSymmetryFinite

open Matrix GraphLaplacian FieldRotationCount FieldBlockDiagonal FieldBlockProduct

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The orthogonal group of a space of dimension at most one is finite -/

/-- On a subsingleton index the orthogonality relation has a single term, so a unitary matrix's
one entry squares to `1`. -/
theorem diag_mul_self {n : Type*} [Fintype n] [DecidableEq n] [Subsingleton n]
    {M : Matrix n n ℝ} (hM : M ∈ Matrix.unitaryGroup n ℝ) (i : n) : M i i * M i i = 1 := by
  have h : Mᵀ * M = 1 := (mem_unitaryGroup_iff_transpose M).1 hM
  have hii : (Mᵀ * M) i i = (1 : Matrix n n ℝ) i i := by rw [h]
  rw [Matrix.mul_apply, Matrix.one_apply_eq,
    Fintype.sum_eq_single i fun x hx => absurd (Subsingleton.elim x i) hx] at hii
  simpa [Matrix.transpose_apply] using hii

/-- **THE ORTHOGONAL GROUP OF A SPACE OF DIMENSION AT MOST ONE IS FINITE** — two elements when the
space is a line, one when it is zero. Takes no graph and no mass. -/
theorem finite_unitaryGroup_of_subsingleton {n : Type*} [Fintype n] [DecidableEq n]
    [Subsingleton n] : Finite (Matrix.unitaryGroup n ℝ) := by
  refine Finite.of_injective
    (fun M => fun i => decide (((M : Matrix n n ℝ) i i) = 1)) fun M N h => ?_
  refine Subtype.ext (Matrix.ext fun i j => ?_)
  have hji : ∀ P : Matrix n n ℝ, P i j = P i i := fun P => by rw [Subsingleton.elim j i]
  have hd : ((M : Matrix n n ℝ) i i) = ((N : Matrix n n ℝ) i i) := by
    have hb : decide (((M : Matrix n n ℝ) i i) = 1)
        = decide (((N : Matrix n n ℝ) i i) = 1) := congrFun h i
    have hM := diag_mul_self M.2 i
    have hN := diag_mul_self N.2 i
    by_cases hM1 : ((M : Matrix n n ℝ) i i) = 1
    · have : decide (((N : Matrix n n ℝ) i i) = 1) = true := by
        rw [← hb]; simp [hM1]
      rw [hM1, of_decide_eq_true this]
    · have hMneg : ((M : Matrix n n ℝ) i i) = -1 := by
        rcases mul_self_eq_one_iff.1 hM with h1 | h1
        · exact absurd h1 hM1
        · exact h1
      have hNne : ((N : Matrix n n ℝ) i i) ≠ 1 := by
        intro hN1
        rw [hN1] at hb
        simp [hM1] at hb
      have hNneg : ((N : Matrix n n ℝ) i i) = -1 := by
        rcases mul_self_eq_one_iff.1 hN with h1 | h1
        · exact absurd h1 hNne
        · exact h1
      rw [hMneg, hNneg]
  rw [hji (M : Matrix n n ℝ), hji (N : Matrix n n ℝ), hd]

/-! ## 2. At a simple spectrum every fibre is a subsingleton -/

omit [Fintype V] [DecidableEq V] in
/-- An injective level function has at most one index at each level. -/
theorem subsingleton_fib {d : V → ℝ} (hd : Function.Injective d) (c : ℝ) :
    Subsingleton (Fib d c) :=
  ⟨fun a b => Subtype.ext (hd (a.2.trans b.2.symm))⟩

/-! ## 3. Finiteness at a simple spectrum, through the product decomposition -/

/-- **THE SYMMETRIES ARE FINITE WHENEVER THE PROPAGATOR'S SPECTRUM IS SIMPLE**, at every finite
graph. The proof is the product decomposition: every factor is the orthogonal group of a
subsingleton, and the index is finite. -/
theorem finite_symmetryMatrices_of_injective (hm : m ≠ 0)
    (hsimple : Function.Injective (eigMu G m hm)) : (symmetryMatrices G m).Finite := by
  haveI : ∀ c : Lev (eigMu G m hm), Subsingleton (Fib (eigMu G m hm) (c : ℝ)) :=
    fun c => subsingleton_fib hsimple _
  haveI : ∀ c : Lev (eigMu G m hm), Finite (Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) :=
    fun _ => finite_unitaryGroup_of_subsingleton
  haveI : Finite (∀ c : Lev (eigMu G m hm),
      Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) := Pi.finite
  haveI : Finite ↥(symmetryMatrices G m) :=
    Finite.of_equiv _ ((symmetry_mulEquiv_prod hm).toEquiv.symm.trans
      (Equiv.subtypeEquivRight fun _ => Iff.rfl))
  exact Set.toFinite _

/-! ## 4. A degenerate eigenvalue makes them infinite -/

/-- **A DEGENERATE EIGENVALUE MAKES THE SYMMETRIES INFINITE**, at every finite graph. The rotation
that witnesses it is `FieldRotationCount`'s and this is the step from a dimension count to an
independent pair. -/
theorem infinite_symmetryMatrices_of_two_le_finrank (hm : m ≠ 0) {μ : ℝ}
    (h : 2 ≤ Module.finrank ℝ (LinearMap.ker (Matrix.toLin' (green G m) - μ • LinearMap.id))) :
    (symmetryMatrices G m).Infinite := by
  obtain ⟨u, hu, v, hv, hu0, hind⟩ := FieldCycleRotation.exists_independent_of_two_le_finrank h
  exact infinite_symmetryMatrices_of_independent_eigenpair hm
    (FieldCycleRotation.dotProduct_self_ne_zero hu0) hind
    ((FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).1 hu)
    ((FieldCycleRotation.mem_eigenspace_iff_mulVec _ _ _).1 hv)

/-- A repeated eigenvalue is a fibre with two points, hence an eigenspace of dimension at least
two. This is `FieldEigenMultiplicity`'s theorem used in the direction that needs a witness. -/
theorem exists_two_le_finrank_of_not_injective (hm : m ≠ 0)
    (h : ¬ Function.Injective (eigMu G m hm)) :
    ∃ μ : ℝ, 2 ≤ Module.finrank ℝ
      (LinearMap.ker (Matrix.toLin' (green G m) - μ • LinearMap.id)) := by
  obtain ⟨i, j, hval, hne⟩ := Function.not_injective_iff.1 h
  refine ⟨eigMu G m hm i, ?_⟩
  rw [FieldEigenMultiplicity.finrank_eigenspace_eq_card_fibre hm]
  refine Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨i, rfl⟩, ⟨j, hval.symm⟩, ?_⟩
  exact fun hEq => hne (congrArg Subtype.val hEq)

/-! ## 5. The criterion -/

/-- **THE SYMMETRIES ARE FINITE IF AND ONLY IF THE PROPAGATOR'S SPECTRUM IS SIMPLE.** -/
theorem finite_iff_injective (hm : m ≠ 0) :
    (symmetryMatrices G m).Finite ↔ Function.Injective (eigMu G m hm) := by
  refine ⟨fun hfin => ?_, finite_symmetryMatrices_of_injective hm⟩
  by_contra hns
  obtain ⟨μ, hμ⟩ := exists_two_le_finrank_of_not_injective hm hns
  exact infinite_symmetryMatrices_of_two_le_finrank hm hμ hfin

/-- **AND IN GRAPH VOCABULARY: FINITE IF AND ONLY IF EVERY EIGENSPACE OF THE LAPLACIAN IS AT MOST A
LINE.** No propagator appears in the right-hand side. This is the sentence that decides the four
graphs this estate has counted, and every other finite graph. -/
theorem finite_iff_lapMatrix (hm : m ≠ 0) :
    (symmetryMatrices G m).Finite ↔ ∀ ν : ℝ, Module.finrank ℝ
      (LinearMap.ker (Matrix.toLin' (G.lapMatrix ℝ) - ν • LinearMap.id)) ≤ 1 := by
  rw [finite_iff_injective hm]
  exact (FieldSimpleConverse.finrank_lapMatrix_le_one_iff hm (green_isHermitian G m hm)).symm

/-- **AND WHEN IT IS FINITE THE COUNT IS `2 ^ |V|`**, so the criterion settles the size too. The
arithmetic is `FieldLineCount.card_symmetries`' and is not re-derived. -/
theorem card_of_finite (hm : m ≠ 0) (hfin : (symmetryMatrices G m).Finite) :
    Nat.card (FieldLineCount.symmetries G m) = 2 ^ Fintype.card V :=
  FieldLineCount.card_symmetries hm ((finite_iff_injective hm).1 hfin)

end FieldSymmetryFinite
