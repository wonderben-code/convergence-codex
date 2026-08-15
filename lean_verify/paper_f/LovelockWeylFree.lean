import LovelockWitnessRowSum
import WeylVanishesThree

/-!
# Weyl-free means Kulkarni–Nomizu with the metric, and nothing else

`LovelockWitnessRowSum` proved `h ⊙ δ` has no Weyl part, for **every** `h`, on the way to something
else. `PROOF_STRATEGY` §6 question 1 asks what a unit unlocked, and the answer here is a converse
that costs four lines: **the implication runs both ways, so "Weyl-free" and "of the form `h ⊙ δ`"
are the same condition.**

## What is proved

* `weylFreeSeed` — the reconstructing 2-tensor, `(n−2)⁻¹·Ric₀ X + (2n(n−1))⁻¹·(scal X)·δ`;
* `eq_kn_weylFreeSeed` — if `weylPart X = 0` then `X = (weylFreeSeed X) ⊙ δ`. `decomposition` says
  `X = ricciPart X + scalPart X`, `ricciPart` is already a `⊙ δ`, and `scalPart` is one too because
  `constCurv = knSquare δ = ½ (δ ⊙ δ)`; bilinearity in the left slot collects them;
* **`weylPart_eq_zero_iff`** — the characterisation. `⟸` is
  `LovelockWitnessRowSum.weylPart_kn_delta` and `⟹` is the item above;
* **`kn_delta_inj`** — and the `h` is **unique**. `ricci_kn_delta` gives
  `Ric (h ⊙ δ) = (tr h)·δ + (n−2)·h`; the trace of that determines `tr h` when `n ≠ 1`, and then
  `h` when `n ≠ 2`. So `h ↦ h ⊙ δ` is injective and the two descriptions match up one-to-one;
* **`algCurv_three_eq_kn_delta`** — at `n = 3`, **every algebraic curvature tensor is `h ⊙ δ`**,
  by `WeylVanishesThree.weylPart_eq_zero`. This is the classical statement of why three dimensions
  are special — the curvature tensor is its Ricci tensor, written out — and the estate had the
  vanishing but never the explicit form.

## What it does and does not do for the wall

**It completes an intrinsic description of the coarse splitting.** `RicciFlatSharp` says Ricci-flat
implies pure Weyl; this says Weyl-free means exactly `⊙ δ`. Neither summand is now described only
by the formula that projects onto it.

**It is not a step toward `KillsWeyl`.** Nothing here evaluates an equivariant `T`, and the open
question — whether the `O(n)`-orbit of one Weyl tensor spans the Weyl summand — is untouched by a
theorem about the *other* summand. **`KillsWeyl` at `n ≥ 4` is untouched and the watchlist item does
not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockWeylFree

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockWitnessRowSum Finset

variable {n : ℕ}

/-- **THE RECONSTRUCTING 2-TENSOR.** Its two pieces are exactly what `ricciPart` and `scalPart`
contribute once both are written as Kulkarni–Nomizu products with the metric. -/
noncomputable def weylFreeSeed (X : Fin n → Fin n → Fin n → Fin n → ℝ) (x y : Fin n) : ℝ :=
  (1 / ((n : ℝ) - 2)) * tracefreeRicci X x y
    + (scal X / (2 * (n : ℝ) * ((n : ℝ) - 1))) * delta x y

/-- **A WEYL-FREE ARRAY IS A KULKARNI–NOMIZU PRODUCT WITH THE METRIC.** `decomposition` leaves
`ricciPart X + scalPart X`; the first is already `⊙ δ`, and the second is too, because
`constCurv = knSquare δ` is half of `δ ⊙ δ`. -/
theorem eq_kn_weylFreeSeed (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {X : Fin n → Fin n → Fin n → Fin n → ℝ} (hW : ∀ a b c d, weylPart X a b c d = 0)
    (a b c d : Fin n) :
    X a b c d = kn (weylFreeSeed X) delta a b c d := by
  have hdec : X a b c d = ricciPart X a b c d + scalPart X a b c d := by
    rw [decomposition X a b c d, hW a b c d, zero_add]
  rw [hdec]
  simp only [ricciPart, scalPart, weylFreeSeed, kn, knSquare]
  field_simp
  ring

/-- **AND THE CONVERSE, SO THE TWO CONDITIONS ARE THE SAME ONE.** `⟸` is
`LovelockWitnessRowSum.weylPart_kn_delta`, which carries no symmetry hypothesis, so neither does
this. -/
theorem weylPart_eq_zero_iff (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    (X : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∀ a b c d, weylPart X a b c d = 0)
      ↔ ∃ h : Fin n → Fin n → ℝ, ∀ a b c d, X a b c d = kn h delta a b c d := by
  constructor
  · intro hW
    exact ⟨weylFreeSeed X, eq_kn_weylFreeSeed hn0 hn1 hn2 hW⟩
  · rintro ⟨h, hh⟩ a b c d
    have hfun : X = kn h delta :=
      funext fun x => funext fun y => funext fun z => funext fun w => hh x y z w
    rw [hfun, weylPart_kn_delta hn0 hn1 hn2]

/-- **THE `h` IS UNIQUE.** From `ricci_kn_delta`: the trace of `Ric (h ⊙ δ)` pins `tr h` when
`n ≠ 1`, and then the tensor itself pins `h` when `n ≠ 2`. So `h ↦ h ⊙ δ` is injective and the
characterisation is a bijection onto the Weyl-free arrays. -/
theorem kn_delta_inj (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {h h' : Fin n → Fin n → ℝ} (he : ∀ a b c d, kn h delta a b c d = kn h' delta a b c d)
    (x y : Fin n) : h x y = h' x y := by
  have hric : ∀ p q : Fin n, ricci (kn h delta) p q = ricci (kn h' delta) p q := by
    intro p q
    simp only [ricci]
    exact Finset.sum_congr rfl fun z _ => he z p q z
  have htr : (∑ z, h z z) = (∑ z, h' z z) := by
    have hs : scal (kn h delta) = scal (kn h' delta) := by
      simp only [scal]
      exact Finset.sum_congr rfl fun p _ => hric p p
    rw [scal_kn_delta, scal_kn_delta] at hs
    have h2 : (2 * (n : ℝ) - 2) ≠ 0 := by
      intro hc
      exact hn1 (by linarith)
    exact mul_left_cancel₀ h2 hs
  have hpt := hric x y
  rw [ricci_kn_delta, ricci_kn_delta, htr] at hpt
  have := mul_left_cancel₀ hn2 (by linarith : ((n : ℝ) - 2) * h x y = ((n : ℝ) - 2) * h' x y)
  exact this

/-- **AT `n = 3` EVERY ALGEBRAIC CURVATURE TENSOR IS `h ⊙ δ`.** The classical reason three
dimensions are special, written as an explicit form rather than as a vanishing.
`WeylVanishesThree` supplied the vanishing; this supplies the form, and `kn_delta_inj` says the `h`
is the only one. -/
theorem algCurv_three_eq_kn_delta {R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ} (hR : IsAlgCurv R) :
    ∃ h : Fin 3 → Fin 3 → ℝ, ∀ a b c d, R a b c d = kn h delta a b c d := by
  have hn0 : ((3 : ℕ) : ℝ) ≠ 0 := by norm_num
  have hn1 : ((3 : ℕ) : ℝ) - 1 ≠ 0 := by norm_num
  have hn2 : ((3 : ℕ) : ℝ) - 2 ≠ 0 := by norm_num
  exact (weylPart_eq_zero_iff hn0 hn1 hn2 R).mp
    (fun a b c d => WeylVanishesThree.weylPart_eq_zero hR a b c d)

end LovelockWeylFree
