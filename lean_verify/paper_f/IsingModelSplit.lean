/-
  IsingModelSplit.lean — a model that splits into two non-interacting parts, and relabelling the
  sites of a model. Together these are the transport `SPINE` and `WALLS §W3.6` name as the last
  thing between the Griffiths-comparison arm and its conclusion.

  WHY. `IsingChainDecay.chain_expect` computes a correlation along a chain, over the recursively
  built site type `IsingChainDecay.chainSite`. `IsingPathComparison` presents the box's comparison
  model over `Fin n × Fin n`. **Nothing carried one onto the other**, and both records say so. The
  obstruction is not one equivalence — the two site types have different cardinalities and are not
  equivalent — but two separate facts, and this file proves both.

  * **A model that splits does not mix.** `split_expect`: if the energy is
    `E₁` on one part plus `E₂` on the other, with nothing joining them, then a correlation at a
    site of the first part is the correlation in the `E₁` model alone. The second part cancels,
    partition function and numerator alike.
  * **Relabelling sites changes nothing.** `basePart_congr`, `baseNum_congr`, `expect_congr`: an
    equivalence of site types carries a model to a model with the same correlations.

  **THIS IS WHY THE CARDINALITY OBJECTION IS NOT AN OBJECTION.** `Site n` has `n²` sites and a
  chain of length `k` has `k + 1`, so no equivalence exists and none is needed: the box's comparison
  model splits into the path and the rest, `split_expect` discards the rest, and what is left has
  the same cardinality as the chain, at which point `expect_congr` applies.

  WHAT THIS FILE DOES **NOT** DO. It does not perform that split for the box. Doing so needs the
  box's comparison energy exhibited in the `splitE` shape — `IsingPathComparison.pathCoup_walk_eq`
  and `pathCoup_no_field_before` pin the couplings along the path, but the sum over interaction
  terms is not yet rearranged into "path part plus rest part", and that rearrangement is not
  attempted here and its cost is not claimed (`ERRATUM 246`). **No wall moves**, and nothing here
  is a bound on anything.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingPendantSite

namespace IsingModelSplit

open Finset Real
open IsingTransfer2D IsingPendantSite

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-! ## 1. A model that splits into two non-interacting parts -/

/-- The energy of two parts with nothing joining them. -/
def splitE (E₁ : (V → Bool) → ℝ) (E₂ : (W → Bool) → ℝ) (σ : V ⊕ W → Bool) : ℝ :=
  E₁ (fun v => σ (Sum.inl v)) + E₂ (fun w => σ (Sum.inr w))

/-- Summing a product over the split type factorises. This is the one computation in §1; the three
theorems after it are this lemma with different integrands. -/
theorem sum_split (f : (V → Bool) → ℝ) (g : (W → Bool) → ℝ) :
    ∑ σ : V ⊕ W → Bool, f (fun v => σ (Sum.inl v)) * g (fun w => σ (Sum.inr w))
      = (∑ τ : V → Bool, f τ) * (∑ υ : W → Bool, g υ) := by
  rw [Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow V W Bool)
        (fun σ => f (fun v => σ (Sum.inl v)) * g (fun w => σ (Sum.inr w)))
        (fun p => f p.1 * g p.2) (fun _ => rfl),
      Fintype.sum_prod_type, ← Finset.sum_mul_sum]

theorem split_part (E₁ : (V → Bool) → ℝ) (E₂ : (W → Bool) → ℝ) :
    basePart (splitE E₁ E₂) = basePart E₁ * basePart E₂ := by
  simp only [basePart]
  rw [← sum_split (fun τ => exp (E₁ τ)) (fun υ => exp (E₂ υ))]
  exact Finset.sum_congr rfl fun σ _ => by rw [splitE, Real.exp_add]

theorem split_num (E₁ : (V → Bool) → ℝ) (E₂ : (W → Bool) → ℝ) (v₀ : V) :
    baseNum (splitE E₁ E₂) (Sum.inl v₀) = baseNum E₁ v₀ * basePart E₂ := by
  simp only [baseNum, basePart]
  rw [← sum_split (fun τ => spin (τ v₀) * exp (E₁ τ)) (fun υ => exp (E₂ υ))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [splitE, Real.exp_add]
  ring

/-- **A PART THAT NOTHING JOINS TO CANCELS, NUMERATOR AND PARTITION FUNCTION ALIKE.** The second
model may be arbitrary — any size, any energy, fields and bonds of its own — and it changes no
correlation in the first. `IsingIsolatedSite.iso_expect` is the shape of this at a one-point second
part with zero energy, though it is not derived from it here: that file's site type is built with
`Option` and relating the two is a relabelling, which is §2's business and is not performed
on it here. -/
theorem split_expect (E₁ : (V → Bool) → ℝ) (E₂ : (W → Bool) → ℝ) (v₀ : V)
    (h₂ : basePart E₂ ≠ 0) :
    baseNum (splitE E₁ E₂) (Sum.inl v₀) / basePart (splitE E₁ E₂)
      = baseNum E₁ v₀ / basePart E₁ := by
  rw [split_num, split_part, mul_div_mul_right _ _ h₂]

/-- The hypothesis of `split_expect` is never an obstacle: a partition function is a sum of
exponentials over a type that is never empty, so it is positive. Stated separately so the user of
`split_expect` is not asked to prove it.

**AND IT NEEDS NO `Nonempty W`, WHICH IS NOT A DETAIL.** The first version of this file carried
one, on the reflex that a positive sum needs a witness. The witness is `fun _ => true`, and it
exists **whether or not `W` does**: the sum is over `W → Bool`, and when `W` is empty that type has
exactly one element rather than none. So the hypothesis excluded a case the proof already handled
(`ERRATUM 251`), and it would have propagated to every user of `split_expect'` — including the
intended one, where the second part is "the box's sites outside the path" and is empty exactly when
the path is the whole box. -/
theorem basePart_pos (E₂ : (W → Bool) → ℝ) : 0 < basePart E₂ := by
  rw [basePart]
  exact Finset.sum_pos (fun υ _ => Real.exp_pos _) ⟨fun _ => true, Finset.mem_univ _⟩

theorem split_expect' (E₁ : (V → Bool) → ℝ) (E₂ : (W → Bool) → ℝ) (v₀ : V) :
    baseNum (splitE E₁ E₂) (Sum.inl v₀) / basePart (splitE E₁ E₂)
      = baseNum E₁ v₀ / basePart E₁ :=
  split_expect E₁ E₂ v₀ (ne_of_gt (basePart_pos E₂))

/-! ## 2. Relabelling the sites -/

/-- The same model, read through an equivalence of site types. -/
def relabel (e : V ≃ W) (E : (W → Bool) → ℝ) (τ : V → Bool) : ℝ := E (fun w => τ (e.symm w))

theorem sum_relabel (e : V ≃ W) (f : (W → Bool) → ℝ) :
    ∑ τ : V → Bool, f (fun w => τ (e.symm w)) = ∑ υ : W → Bool, f υ :=
  Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl Bool))
    (fun τ => f (fun w => τ (e.symm w))) (fun υ => f υ) (fun _ => rfl)

theorem basePart_congr (e : V ≃ W) (E : (W → Bool) → ℝ) :
    basePart (relabel e E) = basePart E :=
  sum_relabel e (fun υ => exp (E υ))

theorem baseNum_congr (e : V ≃ W) (E : (W → Bool) → ℝ) (w₀ : W) :
    baseNum (relabel e E) (e.symm w₀) = baseNum E w₀ := by
  simp only [baseNum]
  rw [← sum_relabel e (fun υ => spin (υ w₀) * exp (E υ))]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [relabel]

/-- **RELABELLING THE SITES CHANGES NO CORRELATION**, which is the half of the transport that has
nothing to do with the model. -/
theorem expect_congr (e : V ≃ W) (E : (W → Bool) → ℝ) (w₀ : W) :
    baseNum (relabel e E) (e.symm w₀) / basePart (relabel e E)
      = baseNum E w₀ / basePart E := by
  rw [basePart_congr, baseNum_congr]

end IsingModelSplit
