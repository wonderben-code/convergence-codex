import Mathlib.Data.Real.Basic
import PairWeightRep

/-!
# Pairings that cross a split, and the weight that kills them

`IsserlisAll.isserlisGeneral_all` turned `∫ ∏ᵢ⟪aᵢ,ω⟫` into a sum over the perfect matchings of
`Fin k`. Every clustering statement in this estate has the same shape underneath: **a matching
whose pairs all stay on one side of a split contributes whatever it contributes, and a matching
with a pair that crosses carries a propagator between the two sides.** When that propagator
vanishes — the two sides in different components of the graph — the crossing matchings contribute
nothing at all, and the sum collapses onto the non-crossing ones.

This file is that collapse, and nothing else. It is stated for an arbitrary symmetric weight
`w : ι → ι → ℝ` and an arbitrary `Finset` split, so the Gaussian chain can consume it without this
file mentioning a measure.

## Why it is stated at a representative set rather than at `filter (· < ·)`

`WickPairings.pairProduct` takes one index out of every pair by `filter (fun i => i < σ i)`.
`PairWeightRep.prod_repSet_eq` already established that **any** representative set gives the same
product, so the argument below is written at an arbitrary `IsRepSet` and specialised afterwards.
The specialisation matters: the crossing pair the proof finds is at some index `i`, and whether
`i` or `σ i` is the one `filter (· < ·)` kept is not something the caller controls.

## What is proved

* `RespectsSplit` — `σ` maps `S` into `S` and its complement into its complement;
* **`prod_repSet_eq_zero_of_not_respects`** — a matching that does not respect the split has
  product zero, at every representative set;
* **`sum_prod_eq_sum_respects`** — so the sum over all matchings equals the sum over the
  respecting ones;
* `not_respectsSplit_fin_two`, `sum_prod_fin_two_eq_zero` — **the check**, at `Fin 2` with
  `S = {0}`: the one perfect matching of `Fin 2` swaps the two indices, so it crosses, so the
  respecting sum is EMPTY and the theorem says the whole sum is zero. Computed the other way —
  the sum over `perfectMatchings (Fin 2)` is `w 0 1`, which the hypothesis sets to zero — the two
  agree. A statement that collapsed the sum onto the wrong set would fail this.

## What is NOT here

The factorisation. *"The respecting matchings are the matchings of `S` paired with the matchings
of `Sᶜ`"* is a bijection, and turning `∑ respecting` into `(∑ over S)·(∑ over Sᶜ)` needs it. That
is not written here and no estimate is offered (`ERRATUM 194`). Neither is any statement about a
Gaussian integral: this file is pure combinatorics.
-/
namespace PairingSplit

open Equiv Function Involutions PairWeightRep

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The split -/

/-- `σ` keeps each side of the split `S` to itself. Stated as an `Iff` rather than as
`∀ i ∈ S, σ i ∈ S` so that the two sides are symmetric in the statement as well as in fact. -/
def RespectsSplit (S : Finset ι) (σ : Equiv.Perm ι) : Prop := ∀ i, σ i ∈ S ↔ i ∈ S

instance (S : Finset ι) (σ : Equiv.Perm ι) : Decidable (RespectsSplit S σ) :=
  inferInstanceAs (Decidable (∀ i, σ i ∈ S ↔ i ∈ S))

omit [DecidableEq ι] in
theorem respectsSplit_univ (σ : Equiv.Perm ι) :
    RespectsSplit (Finset.univ : Finset ι) σ := fun _ => by simp

/-! ## 2. A crossing matching contributes nothing

The pair that crosses is at some index `i` with `i ∈ S` and `σ i ∉ S`. Which of `i` and `σ i` the
representative set kept is not known, so both are handled — and that is exactly where the
symmetry of `w` is used. -/

omit [Fintype ι] [DecidableEq ι] in
/-- **THE ONE-SIDED STEP.** `i ∈ S` and `σ i ∉ S` already force the product to vanish, at every
representative set. `IsRepSet` keeps exactly one of `i` and `σ i`; symmetry of `w` is what makes
the two cases the same factor. -/
theorem prod_repSet_eq_zero_of_mem_not_mem {σ : Equiv.Perm ι} (hσ : Function.Involutive σ)
    {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i) {S R : Finset ι} (hR : IsRepSet σ R)
    (hzero : ∀ i ∈ S, ∀ j ∉ S, w i j = 0) {i : ι} (hi : i ∈ S) (hσi : σ i ∉ S) :
    ∏ j ∈ R, w j (σ j) = 0 := by
  have hne : σ i ≠ i := fun h => hσi (by rw [h]; exact hi)
  by_cases hiR : i ∈ R
  · exact Finset.prod_eq_zero hiR (hzero i hi (σ i) hσi)
  · have hσiR : σ i ∈ R := by
      by_contra h
      exact hiR ((hR.2 i hne).mpr h)
    refine Finset.prod_eq_zero hσiR ?_
    rw [hσ i, hw (σ i) i]
    exact hzero i hi (σ i) hσi

omit [Fintype ι] [DecidableEq ι] in
/-- **A MATCHING THAT CROSSES THE SPLIT HAS PRODUCT ZERO.** The two ways of crossing — out of `S`
and into it — are the same statement at `i` and at `σ i`, which is why involutivity appears. -/
theorem prod_repSet_eq_zero_of_not_respects {σ : Equiv.Perm ι} (hσ : σ ∈ involutions ι)
    {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i) {S R : Finset ι} (hR : IsRepSet σ R)
    (hzero : ∀ i ∈ S, ∀ j ∉ S, w i j = 0) (hns : ¬ RespectsSplit S σ) :
    ∏ j ∈ R, w j (σ j) = 0 := by
  have hinv : Function.Involutive σ := hσ
  rw [RespectsSplit, not_forall] at hns
  obtain ⟨i, hi⟩ := hns
  by_cases him : i ∈ S
  · have : σ i ∉ S := fun h => hi (iff_of_true h him)
    exact prod_repSet_eq_zero_of_mem_not_mem hinv hw hR hzero him this
  · have hσim : σ i ∈ S := by
      by_contra h
      exact hi (iff_of_false h him)
    have : σ (σ i) ∉ S := by rw [hinv i]; exact him
    exact prod_repSet_eq_zero_of_mem_not_mem hinv hw hR hzero hσim this

/-! ## 3. The sum collapses -/

/-- **THE COLLAPSE.** Summed over the perfect matchings, only those respecting the split survive.
`Finset.sum_filter_of_ne` is the whole proof once the lemma above is in hand: a nonzero term
forces its matching into the filter. -/
theorem sum_prod_eq_sum_respects [LinearOrder ι] {w : ι → ι → ℝ} (hw : ∀ i j, w i j = w j i)
    {S : Finset ι} (hzero : ∀ i ∈ S, ∀ j ∉ S, w i j = 0) :
    ∑ σ : ↑(perfectMatchings ι), ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), w i (σ.1 i)
      = ∑ σ ∈ Finset.univ.filter (fun σ : ↑(perfectMatchings ι) => RespectsSplit S σ.1),
          ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), w i (σ.1 i) := by
  refine (Finset.sum_filter_of_ne ?_).symm
  intro σ _ hne
  by_contra hns
  exact hne (prod_repSet_eq_zero_of_not_respects σ.2.1 hw (isRepSet_filter_lt σ.2.1) hzero hns)

/-! ## 4. The check

At `Fin 2` with `S = {0}` the one perfect matching swaps the two indices, so it crosses, so the
filtered sum is over an EMPTY set. The theorem then says the whole sum is zero — and the sum over
`perfectMatchings (Fin 2)` is `w 0 1` by direct enumeration, which the hypothesis sets to zero.
The two routes do not pass through each other. -/

/-- No perfect matching of `Fin 2` respects the split `{0}`: the only one is the swap. -/
theorem not_respectsSplit_fin_two (σ : Equiv.Perm (Fin 2)) (hσ : σ ∈ perfectMatchings (Fin 2)) :
    ¬ RespectsSplit ({0} : Finset (Fin 2)) σ := by
  intro h
  have h0 : σ 0 ≠ 0 := hσ.2 0
  have : σ 0 ∈ ({0} : Finset (Fin 2)) := (h 0).mpr (by decide)
  exact h0 (by simpa using this)

/-- **THE CHECK.** The filtered sum is empty, so the collapse says the whole sum vanishes. -/
theorem sum_prod_fin_two_eq_zero {w : Fin 2 → Fin 2 → ℝ} (hw : ∀ i j, w i j = w j i)
    (hzero : ∀ i ∈ ({0} : Finset (Fin 2)), ∀ j ∉ ({0} : Finset (Fin 2)), w i j = 0) :
    ∑ σ : ↑(perfectMatchings (Fin 2)),
        ∏ i ∈ Finset.univ.filter (fun i => i < σ.1 i), w i (σ.1 i) = 0 := by
  rw [sum_prod_eq_sum_respects hw hzero]
  have hempty : (Finset.univ.filter
      (fun σ : ↑(perfectMatchings (Fin 2)) =>
        RespectsSplit ({0} : Finset (Fin 2)) σ.1)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun {σ} _ => not_respectsSplit_fin_two σ.1 σ.2
  rw [hempty, Finset.sum_empty]

end PairingSplit
