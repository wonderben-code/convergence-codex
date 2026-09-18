import FieldRotationNonIsometric
import FieldSymmetryHom
import FieldLineCount
import PawSimpleSpectrum

/-!
# The index, which five files have said nobody measures

**COUNTED, NOT GUESSED** (`ERRATUM 450`'s rule). The phrase *no index* occurs in **11** files of
`paper_f`; **six of those are about something else** — an index-matching between enumerations
(`FieldSimpleConverse`), an index type (`Involutions`, `LatticeWickCount`), the Weinberg angle
(`WeinbergIndex`), and two passing uses. The **five** that fence *this* index are
`FieldSymmetryInclusion`, `FieldSymmetryProper`, `FieldSignGroup`, `FieldSymmetryHom` and
`FieldLinearGroup`, each ending its *What is NOT here* with some form of **and still no index**;
`FieldRotationNonIsometric` adds a sixth, but that is the previous unit's own and says
explicitly that the index *is the next rung, not this one*. And the `UNLOCK_WATCHLIST` item
that has carried the linear-symmetry clause
since 5 September lists exactly two residues, of which one is **no index** —
*`FieldSymmetryHom.range_symHom_ne_top` says the subgroup is proper and nothing measures what is
missing.* The previous unit measured it **from below**, as a set: at two distinct eigenvalues the
linear symmetries that are not isometries are infinite in number. **This is the index itself.**

## What is proved

**`infinite_linSymGL`** — the bridge the previous unit named and declined. `FieldSymmetryIso.linSym`
is a `Submonoid` of matrices whose carrier is literally `{L | L * C * Lᵀ = C}`, and
`FieldSymmetryInclusion.linSymGL` is the corresponding `Subgroup` of `GL V ℝ`; every member of the
first has invertible determinant (`FieldSymmetryInclusion.isUnit_det_of_mem_linSym`), so
`Matrix.GeneralLinearGroup.mkOfDetNeZero` lifts it, injectively. **So a set of matrices being
infinite makes the GROUP infinite**, which is the transport the previous unit's *What is NOT here*
says is not made.

**`index_range_symHom_eq_zero`** — **THE INDEX, wherever the isometric symmetries are finite and
the linear ones are not.** `Subgroup.card_mul_index` reads `Nat.card H * H.index = Nat.card G`; with
`Nat.card G = 0` because the ambient group is infinite, and `Nat.card H ≠ 0` because the subgroup
is not, the index has nowhere to go but `0` — which is Mathlib's way of writing *infinite index*.

**`index_range_symHom_eq_zero_line`** — **AND ON A NAMED GRAPH IT IS DISCHARGED.** On
`boxGraph 1 (k + 1)` at `1 ≤ k` and every non-zero mass, the isometric symmetry group has index
**`0`** in the linear one. Both hypotheses are theorems here rather than assumptions: the linear
group is infinite by the previous unit's `infinite_linSym_quadForm_line`, and the isometric one has
exactly `2 ^ (k + 1)` elements by `FieldLineCount.card_symmetries_line` carried across
`FieldSymmetryHom.symEquivRange`.

**`nat_card_range_symHom_line`** — the finite side on its own, because it is the half that is a
number rather than a zero: `Nat.card` of `symHom`'s range **is** `2 ^ (k + 1)`.

## What this settles, and in what words

The watchlist item's residue asked what is missing between the two symmetry groups. The answer on
the line is: **everything except a set of size `2 ^ (k + 1)`** — the quotient is infinite, so no
finite index exists, and `range_symHom_ne_top`'s *proper* was an understatement of the largest
possible kind. **`no cardinality` is untouched** and remains the item's other residue: this says
how many cosets there are, not how many elements the linear group has.

## What is NOT here

**THE GENERAL GRAPH IS NOT DONE, AND THE HYPOTHESIS IS NOT THE ONE A READER WOULD GUESS**
(a snapshot of 2026-09-18, dated because it is an estate-scope negative claim and
`claims_scan.py` is right to ask — `ERRATUM 293`, `ERRATUM 302`).
`index_range_symHom_eq_zero` takes finiteness of the isometric group as a hypothesis, and
`FieldSymmetryFinite.finite_iff_injective` says that holds **iff the propagator's spectrum is
simple** — not merely iff the graph has an edge. So the general statement available from here is
*infinite index whenever the spectrum is simple and two eigenvalues differ*, and on a graph with a
repeated eigenvalue **both** groups are infinite and this argument says nothing. That case needs a
genuine quotient argument rather than a cardinality one, and **it is not attempted in this file**
(`ERRATUM 246`) — the locality is deliberate and is what `claims_scan.py` asks for: this paragraph
knows what this unit did, not what the estate contains.

**NO COSET REPRESENTATIVES, AND NO STRUCTURE FOR THE QUOTIENT.** `index = 0` is a statement that a
number does not exist. What the quotient *is* — a Grassmannian-like object, on the standard
argument — is not touched.

**No wall moves.** `W1`'s open part is `OS0` and `OS4`, and `OS1` in its continuum sense. Knowing
the index of a finite-volume symmetry group is knowing a shadow exactly.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldSymmetryIndex

open Matrix GraphLaplacian FieldSymmetryIso FieldSymmetryInclusion FieldSymmetryHom
open FieldRotationCount FieldSignGroup FieldLineCount
open BoxGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. A set of matrices being infinite makes the group of units infinite -/

/-- **THE TRANSPORT ACROSS THE `Set`/`Subgroup` BOUNDARY**, which the previous unit named and
declined. Every linear symmetry has invertible determinant
(`FieldSymmetryInclusion.isUnit_det_of_mem_linSym`), so
`Matrix.GeneralLinearGroup.mkOfDetNeZero` lifts the carrier into `GL V ℝ`, and the lift is
injective on the nose: its underlying matrix is the matrix it came from, by `rfl`. -/
theorem infinite_linSymGL (hm : m ≠ 0)
    (hinf : {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Infinite) :
    Infinite (linSymGL G m) := by
  haveI : Infinite {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m} := hinf.to_subtype
  have hdet : ∀ L : {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}, (L.1).det ≠ 0 :=
    fun L => isUnit_iff_ne_zero.mp (isUnit_det_of_mem_linSym hm (mem_linSym.mpr L.2))
  refine Infinite.of_injective
    (fun L : {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m} =>
      (⟨Matrix.GeneralLinearGroup.mkOfDetNeZero L.1 (hdet L), mem_linSym.mpr L.2⟩ :
        linSymGL G m)) ?_
  intro L₁ L₂ h
  exact Subtype.ext (congrArg (fun U : linSymGL G m => (U.1 : Matrix V V ℝ)) h)

/-! ## 2. The isometric side, as a number -/

/-- **`symHom`'s RANGE HAS EXACTLY `2 ^ |V|` ELEMENTS** wherever the propagator's spectrum is
simple: `FieldSymmetryHom.symEquivRange` is the isomorphism onto the image and
`FieldLineCount.card_symmetries` is the count. -/
theorem nat_card_range_symHom (hm : m ≠ 0)
    (hsimple : Function.Injective (green_posDef G hm).isHermitian.eigenvalues) :
    Nat.card (symHom (G := G) (m := m) hm).range = 2 ^ Fintype.card V := by
  rw [← Nat.card_congr (symEquivRange (G := G) (m := m) hm).toEquiv]
  exact FieldLineCount.card_symmetries hm hsimple

/-! ## 3. The index -/

/-- **A SUBGROUP WITH A NON-ZERO CARDINALITY INSIDE AN INFINITE GROUP HAS INDEX `0`**, which is
Mathlib's way of writing *infinite index*. `Subgroup.card_mul_index` does all of it:
`Nat.card H * H.index = Nat.card G`, the right side is `0` because the ambient group is infinite,
and `Nat.card H ≠ 0`, so the index is what is left. -/
theorem index_range_symHom_eq_zero (hm : m ≠ 0)
    (hinf : {L : Matrix V V ℝ | L * green G m * Lᵀ = green G m}.Infinite)
    (hcard : Nat.card (symHom (G := G) (m := m) hm).range ≠ 0) :
    (symHom (G := G) (m := m) hm).range.index = 0 := by
  haveI : Infinite (linSymGL G m) := infinite_linSymGL hm hinf
  have h := Subgroup.card_mul_index (symHom (G := G) (m := m) hm).range
  -- rewrite the AMBIENT card, not the subgroup's: `rw [Nat.card_eq_zero_of_infinite]` takes the
  -- first match, which is the subgroup, and then asks for an `Infinite` instance it cannot have.
  have hG : Nat.card (linSymGL G m) = 0 := Nat.card_eq_zero_of_infinite
  rw [hG] at h
  exact (Nat.mul_eq_zero.mp h).resolve_left hcard

/-! ## 4. The restrictive hypothesis removed: any graph with a simple spectrum -/

/-- **THE INDEX IS `0` ON EVERY GRAPH WHOSE PROPAGATOR HAS A SIMPLE SPECTRUM AND AT LEAST TWO
VERTICES.** `PROOF_STRATEGY` §7 rule 3 applied to the line-only statement below, and found by
`RE-SWEEP #66`: the watchlist item *which finite graphs have a SIMPLE Laplacian spectrum* is
exactly the characterisation of where this theorem applies, so an open question about graphs
acquired a new consumer.

A simple spectrum plus two vertices gives two distinct eigenvalues for free — that is the whole
content of `exists_pair_ne` against injectivity — and a simple spectrum gives the count. Nothing
about the graph enters beyond those two. -/
theorem index_range_symHom_eq_zero_of_simple [Nontrivial V] (hm : m ≠ 0)
    (hsimple : Function.Injective (green_posDef G hm).isHermitian.eigenvalues) :
    (symHom (G := G) (m := m) hm).range.index = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  refine index_range_symHom_eq_zero hm
    (FieldRotationNonIsometric.infinite_linSym_quadForm_of_eigenvalues_ne (i := i) (j := j) hm
      fun h => hij (hsimple h)) ?_
  rw [nat_card_range_symHom hm hsimple]
  positivity

/-- **AND A SECOND NAMED GRAPH, WHICH THE GENERALISATION MAKES FREE**: the paw — a triangle with a
pendant vertex — whose Laplacian spectrum `PawSimpleSpectrum.finrank_lapMatrix_le_one_paw` shows is
simple, carried to the propagator by `FieldLaplacianSimple.eigenvalues_injective_of_lapMatrix`.
Before the generalisation this needed its own eigenvalue pair and its own infinitude argument; now
it is two lines. -/
theorem index_range_symHom_eq_zero_paw {mass : ℝ} (hmass : mass ≠ 0) :
    (symHom (G := PawSimpleSpectrum.pawGraph) (m := mass) hmass).range.index = 0 :=
  index_range_symHom_eq_zero_of_simple hmass
    (FieldLaplacianSimple.eigenvalues_injective_of_lapMatrix hmass
      (green_posDef PawSimpleSpectrum.pawGraph hmass).isHermitian
      PawSimpleSpectrum.finrank_lapMatrix_le_one_paw)

/-! ## 4. And on a named graph it is discharged -/

/-- **THE ISOMETRIC SYMMETRY GROUP OF THE FIELD ON A LINE HAS INDEX `0` IN THE LINEAR ONE**, at
every `1 ≤ k` and every non-zero mass. Both hypotheses are theorems here: the linear group is
infinite by `FieldRotationNonIsometric.infinite_linSym_quadForm_line`, and the isometric one has
exactly `2 ^ (k + 1)` elements.

**So `FieldSymmetryHom.range_symHom_ne_top`'s *proper* was an understatement of the largest
possible kind**: there is no finite index at all. -/
theorem index_range_symHom_eq_zero_line {k : ℕ} (hk : 1 ≤ k) {mass : ℝ} (hmass : mass ≠ 0) :
    (symHom (G := boxGraph 1 (k + 1)) (m := mass) hmass).range.index = 0 := by
  refine index_range_symHom_eq_zero hmass
    (FieldRotationNonIsometric.infinite_linSym_quadForm_line hk hmass) ?_
  rw [nat_card_range_symHom hmass
    (FieldSimpleCriterion.eigenvalues_injective_line hmass
      (green_posDef (boxGraph 1 (k + 1)) hmass).isHermitian)]
  positivity

/-- **AND THE FINITE SIDE AS A NUMBER**, which is the half that is a count rather than a zero. -/
theorem nat_card_range_symHom_line {k : ℕ} {mass : ℝ} (hmass : mass ≠ 0) :
    Nat.card (symHom (G := boxGraph 1 (k + 1)) (m := mass) hmass).range = 2 ^ (k + 1) := by
  rw [← Nat.card_congr (symEquivRange (G := boxGraph 1 (k + 1)) (m := mass) hmass).toEquiv]
  exact FieldLineCount.card_symmetries_line hmass

end FieldSymmetryIndex
