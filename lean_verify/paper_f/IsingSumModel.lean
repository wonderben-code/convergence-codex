/-
  IsingSumModel.lean — the rearrangement. A model whose interaction terms each live entirely in one
  of two parts IS a split model, in the estate's own `part`/`num` idiom, and its correlations are
  computed by `IsingModelSplit.split_expect`.

  WHY. `IsingModelSplit` proved that a split model's correlations ignore the other part, and that
  relabelling sites changes nothing. Both were stated for a bare energy function `E`. Every model in
  this estate is presented differently — as a family of interaction terms, `part S J` and
  `num S J A`
  summing `J i * ∏ v ∈ S i, spin (σ v)` over an index type — and the previous file's records said
  plainly that putting such a sum into split shape was **not attempted**. This file attempts it.

  * `energy_sum`: the sum over `I₁ ⊕ I₂` of terms carried into `A ⊕ B` by `Sum.inl` and `Sum.inr` is
    the first model's energy at the first part plus the second's at the second.
  * `part_sum`, `num_sum`, `expect_sum`: hence the partition function factorises, the numerator of a
    correlation among first-part sites factorises with the second part's partition function, and the
    **correlation is exactly the first model's** — the second model cancels whatever it is.
  * `part_congr_index`, `num_congr_index`: relabelling the *index* type changes nothing either. This
    is the companion of `IsingModelSplit.expect_congr`, which relabels sites; both are needed,
    because a model is a pair and either coordinate may need moving.

  WHAT THIS FILE DOES **NOT** DO, stated precisely because the residue has narrowed and a vague
  statement would now be a false one. The box's comparison model has index type
  `(Site n × Site n) ⊕ Site n` and `IsingPathComparison.pathCoup` **zeroes the coupling off the
  path** rather than removing those indices. So it is not yet in `sumSet`/`sumCoup` shape: the
  off-path indices are still present, contributing nothing, and their site sets straddle both parts.
  Reindexing the model onto the sub-type where the coupling is nonzero is the missing step, it is
  **not attempted here**, and its cost is not claimed (`ERRATUM 246`). `part_congr_index` is half of
  what that step will need and is deliberately stated for an arbitrary equivalence rather than for
  the box.

  **No wall moves. Nothing here is a bound on anything.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingModelSplit
import IsingGriffithsMono

namespace IsingSumModel

open Finset Real
open IsingTransfer2D IsingGriffithsMono

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {I₁ I₂ : Type*} [Fintype I₁] [Fintype I₂]

/-! ## 1. Two models side by side -/

/-- The interaction terms of two models, carried into the disjoint union of their site types. -/
def sumSet (S₁ : I₁ → Finset A) (S₂ : I₂ → Finset B) : I₁ ⊕ I₂ → Finset (A ⊕ B)
  | Sum.inl j => (S₁ j).map ⟨Sum.inl, Sum.inl_injective⟩
  | Sum.inr j => (S₂ j).map ⟨Sum.inr, Sum.inr_injective⟩

/-- Their couplings, side by side. -/
def sumCoup (J₁ : I₁ → ℝ) (J₂ : I₂ → ℝ) : I₁ ⊕ I₂ → ℝ := Sum.elim J₁ J₂

omit [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
/-- **THE REARRANGEMENT.** A family of interaction terms, each living entirely in one part, has an
energy of exactly the shape `IsingModelSplit.splitE` asks for. Everything in §1 follows from this
line and the factorisation `IsingModelSplit.sum_split`. -/
theorem energy_sum (S₁ : I₁ → Finset A) (S₂ : I₂ → Finset B) (J₁ : I₁ → ℝ) (J₂ : I₂ → ℝ)
    (σ : A ⊕ B → Bool) :
    ∑ i : I₁ ⊕ I₂, sumCoup J₁ J₂ i * ∏ v ∈ sumSet S₁ S₂ i, spin (σ v)
      = (∑ i : I₁, J₁ i * ∏ v ∈ S₁ i, spin (σ (Sum.inl v)))
        + ∑ i : I₂, J₂ i * ∏ v ∈ S₂ i, spin (σ (Sum.inr v)) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by rw [sumSet, sumCoup, Finset.prod_map]; rfl
  · exact Finset.sum_congr rfl fun j _ => by rw [sumSet, sumCoup, Finset.prod_map]; rfl

theorem part_sum (S₁ : I₁ → Finset A) (S₂ : I₂ → Finset B) (J₁ : I₁ → ℝ) (J₂ : I₂ → ℝ) :
    part (sumSet S₁ S₂) (sumCoup J₁ J₂) = part S₁ J₁ * part S₂ J₂ := by
  simp only [part]
  rw [← IsingModelSplit.sum_split
        (fun τ : A → Bool => exp (∑ i : I₁, J₁ i * ∏ v ∈ S₁ i, spin (τ v)))
        (fun υ : B → Bool => exp (∑ i : I₂, J₂ i * ∏ v ∈ S₂ i, spin (υ v)))]
  exact Finset.sum_congr rfl fun σ _ => by rw [energy_sum, Real.exp_add]

theorem num_sum (S₁ : I₁ → Finset A) (S₂ : I₂ → Finset B) (J₁ : I₁ → ℝ) (J₂ : I₂ → ℝ)
    (A₁ : Finset A) :
    num (sumSet S₁ S₂) (sumCoup J₁ J₂) (A₁.map ⟨Sum.inl, Sum.inl_injective⟩)
      = num S₁ J₁ A₁ * part S₂ J₂ := by
  simp only [num, part]
  rw [← IsingModelSplit.sum_split
        (fun τ : A → Bool =>
          (∏ v ∈ A₁, spin (τ v)) * exp (∑ i : I₁, J₁ i * ∏ v ∈ S₁ i, spin (τ v)))
        (fun υ : B → Bool => exp (∑ i : I₂, J₂ i * ∏ v ∈ S₂ i, spin (υ v)))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_map, energy_sum, Real.exp_add]
  simp only [Function.Embedding.coeFn_mk]
  ring

/-- **A MODEL SITTING BESIDE ANOTHER HAS ITS OWN CORRELATIONS.** The second model may be any size,
with any interaction terms and couplings of its own; it cancels. This is the estate-idiom form of
`IsingModelSplit.split_expect`, and unlike that one it computes a correlation of an arbitrary
**product** of spins, because `num` was always stated for a `Finset` of sites. -/
theorem expect_sum (S₁ : I₁ → Finset A) (S₂ : I₂ → Finset B) (J₁ : I₁ → ℝ) (J₂ : I₂ → ℝ)
    (A₁ : Finset A) :
    num (sumSet S₁ S₂) (sumCoup J₁ J₂) (A₁.map ⟨Sum.inl, Sum.inl_injective⟩)
        / part (sumSet S₁ S₂) (sumCoup J₁ J₂)
      = num S₁ J₁ A₁ / part S₁ J₁ := by
  rw [num_sum, part_sum, mul_div_mul_right _ _ (ne_of_gt (part_pos S₂ J₂))]

/-- **AND THE OTHER PART'S COUPLINGS ARE IRRELEVANT, NOT MERELY ABSENT.** `expect_sum` says the
correlation equals the first model's; this says the same thing in the form a reader checking the
argument will actually want — vary the second model's couplings however you like, arbitrarily and
independently, and no correlation among first-part sites moves at all. It is the reason the
comparison argument may put *anything* in the second part without tracking it. -/
theorem expect_indep_of_second (S₁ : I₁ → Finset A) (S₂ : I₂ → Finset B) (J₁ : I₁ → ℝ)
    (J₂ J₂' : I₂ → ℝ) (A₁ : Finset A) :
    num (sumSet S₁ S₂) (sumCoup J₁ J₂) (A₁.map ⟨Sum.inl, Sum.inl_injective⟩)
        / part (sumSet S₁ S₂) (sumCoup J₁ J₂)
      = num (sumSet S₁ S₂) (sumCoup J₁ J₂') (A₁.map ⟨Sum.inl, Sum.inl_injective⟩)
        / part (sumSet S₁ S₂) (sumCoup J₁ J₂') := by
  rw [expect_sum, expect_sum]

/-! ## 2. Relabelling the index type -/

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem part_congr_index (e : I₁ ≃ I₂) (S : I₂ → Finset V) (J : I₂ → ℝ) :
    part (fun j => S (e j)) (fun j => J (e j)) = part S J :=
  Finset.sum_congr rfl fun σ _ => by
    rw [Fintype.sum_equiv e (fun j => J (e j) * ∏ v ∈ S (e j), spin (σ v))
      (fun i => J i * ∏ v ∈ S i, spin (σ v)) (fun _ => rfl)]

theorem num_congr_index (e : I₁ ≃ I₂) (S : I₂ → Finset V) (J : I₂ → ℝ) (A₁ : Finset V) :
    num (fun j => S (e j)) (fun j => J (e j)) A₁ = num S J A₁ :=
  Finset.sum_congr rfl fun σ _ => by
    rw [Fintype.sum_equiv e (fun j => J (e j) * ∏ v ∈ S (e j), spin (σ v))
      (fun i => J i * ∏ v ∈ S i, spin (σ v)) (fun _ => rfl)]

/-- **RELABELLING THE INDEX TYPE CHANGES NO CORRELATION.** The companion of
`IsingModelSplit.expect_congr`, which relabels sites. A model is a pair and either coordinate may
need moving; the box's comparison model will need this one. -/
theorem expect_congr_index (e : I₁ ≃ I₂) (S : I₂ → Finset V) (J : I₂ → ℝ) (A₁ : Finset V) :
    num (fun j => S (e j)) (fun j => J (e j)) A₁ / part (fun j => S (e j)) (fun j => J (e j))
      = num S J A₁ / part S J := by
  rw [part_congr_index, num_congr_index]

end IsingSumModel
