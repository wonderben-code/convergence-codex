import FieldBlockContinuum
import FieldSymmetryCount

/-!
# One block: the orthogonal group of a fibre is two elements, or one, or the continuum

**THE LAST CARDINAL IN THIS CLUSTER THAT WAS TRUE AND UNSTATED.** `FieldBlockContinuum` computed
`#(∀ c, O(Fib c))` for the whole product and said, in as many words, that it said nothing about
one factor. The residue was filed the same hour as a `UNLOCK_WATCHLIST` item. This is it.

## What is proved

**`nat_card_unitaryGroup_of_card_le_one`** — `Nat.card (O(W)) = 2 ^ |W|` whenever `|W| ≤ 1`:
**two** elements on a one-point index (`FieldSymmetryCount.card_unitaryGroup_of_nonempty`, which
is `{1, -1}`) and **one** on an empty index, where the only matrix is the empty one. The two cases
are one formula because `2 ^ 0 = 1`, and that is not a coincidence — it is the `2 ^ |V|` count of
`FieldSymmetryCount.card_symmetryMatrices_of_injective` restricted to a single factor.

**`mk_unitaryGroup_eq_continuum_iff`** — `#(O(W)) = 𝔠` **if and only if** `1 < |W|`. The forward
half is the finite count above against `ℵ₀ ≤ 𝔠`; the backward half is
`FieldSymmetryContinuum.mk_unitaryGroup`, whose `[Nontrivial W]` **instance hypothesis this
statement removes** by turning it into an equivalence.

**`mk_unitaryGroup_lt_aleph0_or_eq_continuum`** — so one orthogonal group over `ℝ` at a finite
index is finite or exactly `𝔠`, with nothing between, exactly as the whole symmetry group is.

**`mk_unitaryGroup_fib_eq_continuum_iff`** — the same in the cluster's vocabulary:
`#(O(Fib d c)) = 𝔠 ↔ 2 ≤ Fintype.card (Fib d c)`, for an arbitrary level function `d` and an
arbitrary real `c`. No graph and no mass appear in it.

**`mk_prod_unitaryGroup_eq_continuum_iff_exists_factor`** — **and the product's cardinal is decided
factorwise**: `#(∀ c, O(Fib c)) = 𝔠` if and only if **some single factor** is `𝔠`. This is the
statement that makes the previous unit's product theorem and this unit's fibre theorem one fact
rather than two, and it is the reason the residue was worth taking.

## What is NOT here

**NO PRODUCT FORMULA.** The cardinal of the product is **not** computed as a product of the
factors' cardinals. `𝔠 · 2 = 𝔠` and `2 ^ k` are both true arithmetic and neither is used: the
proof routes through the degeneracy criterion, not through cardinal multiplication. **A formula in
the block sizes is not attempted by this file, 2026-09-19**, and no cost is claimed
(`ERRATUM 246`).

**NOTHING NEW ABOUT THE EMPTY FIBRE IN CONTEXT.** `FieldBlockProduct.fib_nonempty` says a fibre
over an ATTAINED level is never empty, so the `2 ^ 0 = 1` case cannot arise at a `c : Lev d`. It is
proved here anyway because `mk_unitaryGroup_fib_eq_continuum_iff` is stated at an arbitrary real
`c`, attained or not, and **an unattained level has an empty fibre** — the generality is the
reason the case exists, not an oversight about the estate.

**UNIVERSE 0, AND THAT IS FORCED**, for the reason `FieldSymmetryContinuum` records:
`Cardinal.continuum` is a `Cardinal.{0}`.

**NO WALL MOVES.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.

-/

namespace FieldFibreCardinal

open Matrix GraphLaplacian FieldRotationCount FieldBlockDiagonal FieldBlockProduct Cardinal

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## 1. Below two points, the group is a power of two -/

/-- On an empty index the only matrix is the empty one, so the orthogonal group is a point. -/
theorem nat_card_unitaryGroup_of_isEmpty [IsEmpty W] :
    Nat.card (Matrix.unitaryGroup W ℝ) = 1 := by
  haveI hsub : Subsingleton (Matrix W W ℝ) :=
    ⟨fun A B => Matrix.ext fun i _ => (IsEmpty.false i).elim⟩
  haveI : Subsingleton (Matrix.unitaryGroup W ℝ) :=
    Function.Injective.subsingleton Subtype.coe_injective
  exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩

/-- **`Nat.card (O(W)) = 2 ^ |W|` WHENEVER `|W| ≤ 1`** — two elements on a line, one on nothing.
The `2 ^ 0 = 1` is `FieldSymmetryCount.card_symmetryMatrices_of_injective`'s arithmetic on a
single factor. -/
theorem nat_card_unitaryGroup_of_card_le_one (h : Fintype.card W ≤ 1) :
    Nat.card (Matrix.unitaryGroup W ℝ) = 2 ^ Fintype.card W := by
  haveI : Subsingleton W := Fintype.card_le_one_iff_subsingleton.1 h
  rcases isEmpty_or_nonempty W with hW | hW
  · haveI := hW
    rw [Fintype.card_eq_zero, pow_zero]
    exact nat_card_unitaryGroup_of_isEmpty
  · haveI := hW
    haveI : Unique W := uniqueOfSubsingleton (Classical.arbitrary W)
    rw [Fintype.card_unique, pow_one]
    exact FieldSymmetryCount.card_unitaryGroup_of_nonempty

/-- And so the group is finite below two points. -/
theorem finite_unitaryGroup_of_card_le_one (h : Fintype.card W ≤ 1) :
    Finite (Matrix.unitaryGroup W ℝ) := by
  haveI : Subsingleton W := Fintype.card_le_one_iff_subsingleton.1 h
  exact FieldSymmetryFinite.finite_unitaryGroup_of_subsingleton

/-! ## 2. At two points or more, the group is the continuum -/

/-- **`#(O(W)) = 𝔠` IF AND ONLY IF `1 < |W|`.** The backward half is
`FieldSymmetryContinuum.mk_unitaryGroup`; **this statement removes its `[Nontrivial W]` instance
hypothesis** by making it an equivalence. -/
theorem mk_unitaryGroup_eq_continuum_iff :
    #(Matrix.unitaryGroup W ℝ) = 𝔠 ↔ 1 < Fintype.card W := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hle
    haveI := finite_unitaryGroup_of_card_le_one (W := W) (not_lt.1 hle)
    have hlt : #(Matrix.unitaryGroup W ℝ) < ℵ₀ := Cardinal.lt_aleph0_of_finite _
    rw [h] at hlt
    exact absurd hlt (not_lt.2 aleph0_le_continuum)
  · haveI : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.1 h
    exact FieldSymmetryContinuum.mk_unitaryGroup

/-- **THE DICHOTOMY ON ONE GROUP**: finite, or exactly `𝔠`, with nothing between. -/
theorem mk_unitaryGroup_lt_aleph0_or_eq_continuum :
    #(Matrix.unitaryGroup W ℝ) < ℵ₀ ∨ #(Matrix.unitaryGroup W ℝ) = 𝔠 := by
  rcases le_or_gt (Fintype.card W) 1 with h | h
  · haveI := finite_unitaryGroup_of_card_le_one (W := W) h
    exact Or.inl (Cardinal.lt_aleph0_of_finite _)
  · exact Or.inr (mk_unitaryGroup_eq_continuum_iff.2 h)

/-! ## 3. On a fibre, in the vocabulary the cluster uses -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **THE FIBRE FORM**, at an arbitrary level function and an arbitrary real level, attained or
not. `2 ≤ Fintype.card` is the vocabulary `FieldBlockInfinite` uses throughout. -/
theorem mk_unitaryGroup_fib_eq_continuum_iff (d : V → ℝ) (c : ℝ) :
    #(Matrix.unitaryGroup (Fib d c) ℝ) = 𝔠 ↔ 2 ≤ Fintype.card (Fib d c) :=
  mk_unitaryGroup_eq_continuum_iff

/-! ## 4. And the product is decided factorwise -/

variable {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- A repeated eigenvalue and a block of two points are the same thing, as an equivalence. -/
theorem not_injective_iff_exists_two_le_card_fib (hm : m ≠ 0) :
    ¬ Function.Injective (eigMu G m hm) ↔
      ∃ c : Lev (eigMu G m hm), 2 ≤ Fintype.card (Fib (eigMu G m hm) (c : ℝ)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨i, j, hval, hne⟩ := Function.not_injective_iff.1 h
    refine ⟨⟨eigMu G m hm i, ⟨i, rfl⟩⟩, ?_⟩
    refine Fintype.one_lt_card_iff_nontrivial.2 ⟨⟨i, rfl⟩, ⟨j, hval.symm⟩, ?_⟩
    exact fun hEq => hne (congrArg Subtype.val hEq)
  · obtain ⟨c, hc⟩ := h
    exact (FieldBlockInfinite.infinite_symmetryMatrices_iff_not_injective hm).1
      (FieldBlockInfinite.infinite_symmetryMatrices_of_two_le_card_fib hm hc)

/-- **THE PRODUCT IS THE CONTINUUM IF AND ONLY IF SOME SINGLE FACTOR IS.** This is what makes the
previous unit's product theorem and this unit's fibre theorem one fact rather than two. -/
theorem mk_prod_unitaryGroup_eq_continuum_iff_exists_factor (hm : m ≠ 0) :
    #(∀ c : Lev (eigMu G m hm), Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) = 𝔠 ↔
      ∃ c : Lev (eigMu G m hm),
        #(Matrix.unitaryGroup (Fib (eigMu G m hm) (c : ℝ)) ℝ) = 𝔠 := by
  rw [FieldBlockContinuum.mk_prod_unitaryGroup_eq_continuum_iff hm,
    not_injective_iff_exists_two_le_card_fib hm]
  exact exists_congr fun c => (mk_unitaryGroup_fib_eq_continuum_iff _ _).symm

end FieldFibreCardinal
