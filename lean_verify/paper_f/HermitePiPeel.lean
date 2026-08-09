/-
  HermitePiPeel.lean — the peeling engine, and a SECOND route to stair N2.

  WHY, and it is a correction to my own plan. The staircase I wrote for the
  n-dimensional item routed completeness (N2) through characteristic
  functions, because that is how the estate's one-dimensional
  `polynomials_complete` does it. `GaussPiExp` and `GaussEuclid` built two
  stairs for that route. **Then asking `PROOF_STRATEGY` §6.2's staircase
  question — which of these is one hard step wearing easy ones as a
  disguise — surfaced a second route that reduces N2 to the estate's OWN
  `hermite_complete`, twice, with no characteristic functions anywhere:**

    induct on `n`; peel coordinate 0; for each `m₀` the slice-integral
    `y ↦ ∫ F(cons x₀ y)·H_{m₀}(x₀) dγ(x₀)` is orthogonal to every
    `Hpi n m'`, so it vanishes a.e. by the inductive hypothesis; hence for
    a.e. `y` every 1-d Hermite coefficient of the slice `x₀ ↦ F(cons x₀ y)`
    vanishes, so the slice is 0 a.e. by 1-d completeness; then Fubini.

  **I designed the first route from the estate's habit rather than from
  what the estate already proves**, which is the mistake ERRATA 43 and 47
  record about routes. This file does not decide between the two — it
  builds the engine the second one needs, which is small and reusable, and
  the watchlist records both with the cost of neither assumed.

  WHAT THIS FILE PROVES:
  * **`Hpi_cons`** — the multi-index system factorises along `Fin.cons`:
    `Hpi (n+1) m (cons x₀ y) = H_{m₀}(x₀)·Hpi n (tail m) y`. Nothing above
    works without it.
  * **`integral_peel`** — an integral against `γ^{n+1}` is an integral
    against `γ ⊗ γⁿ` of the consed function, via the estate's own
    `measurePreserving_peel`.
  * **`integral_peel_fubini`** and **`integrable_slice`** — the iterated
    form, and the a.e. integrability of slices. Together these are exactly
    what an induction on dimension consumes.

  WHAT THIS DOES NOT DO. It does not prove completeness, and it does not
  claim the second route is cheaper than the first. Both are recorded; the
  costs of both are estimates, and this project's estimates are wrong
  about half the time when made before probing.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePi

namespace HermitePiPeel

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi

noncomputable section

/-! ## 1. The multi-index system factorises along `cons` -/

theorem Hpi_cons (n : ℕ) (m : Fin (n + 1) → ℕ) (x₀ : ℝ) (y : Fin n → ℝ) :
    Hpi (n + 1) m (Fin.cons x₀ y) = (H (m 0)).eval x₀ * Hpi n (Fin.tail m) y := by
  rw [Hpi, Hpi, Fin.prod_univ_succ, Fin.cons_zero]
  rfl

/-- The same factorisation with the index split supplied, which is the
    form the induction actually applies. -/
theorem Hpi_cons' (n : ℕ) (m₀ : ℕ) (m' : Fin n → ℕ) (x₀ : ℝ) (y : Fin n → ℝ) :
    Hpi (n + 1) (Fin.cons m₀ m') (Fin.cons x₀ y)
      = (H m₀).eval x₀ * Hpi n m' y := by
  rw [Hpi_cons, Fin.cons_zero, Fin.tail_cons]

/-! ## 2. Peeling an integral

The estate already proves the measure-level statement
(`measurePreserving_peel`); this is the integral form it was built for,
extracted so that consumers do not each re-derive it. `EN_eq_integral`
does exactly this inline, which is why it is worth having once.
-/

theorem integral_peel (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ p : ℝ × (Fin n → ℝ), f (Fin.cons p.1 p.2) ∂((gaussianReal 0 1).prod (gaussPi n))
      = ∫ z, f z ∂gaussPi (n + 1) := by
  rw [← (measurePreserving_peel n).integral_comp (MeasurableEquiv.measurableEmbedding _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [peel_apply, Fin.cons_self_tail]

/-- Integrability transports along the peel. -/
theorem integrable_peel (n : ℕ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f (gaussPi (n + 1))) :
    Integrable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ((gaussianReal 0 1).prod (gaussPi n)) := by
  rw [← (measurePreserving_peel n).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  have hcomp : ((fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2))
      ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0))
      = f := by
    funext z
    simp only [Function.comp_apply, peel_apply, Fin.cons_self_tail]
  rw [hcomp]
  exact hf

/-- **The iterated form.** An integral in `n+1` dimensions is the
    one-dimensional integral of the `n`-dimensional integral of the
    consed function. -/
theorem integral_peel_fubini (n : ℕ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f (gaussPi (n + 1))) :
    ∫ z, f z ∂gaussPi (n + 1)
      = ∫ x₀, (∫ y, f (Fin.cons x₀ y) ∂gaussPi n) ∂(gaussianReal 0 1) := by
  rw [← integral_peel n f]
  exact integral_prod _ (integrable_peel n hf)

/-- **The slices are integrable almost everywhere** — the other half of
    what an induction on dimension consumes. -/
theorem integrable_slice (n : ℕ) {f : (Fin (n + 1) → ℝ) → ℝ}
    (hf : Integrable f (gaussPi (n + 1))) :
    ∀ᵐ x₀ ∂(gaussianReal 0 1), Integrable (fun y => f (Fin.cons x₀ y)) (gaussPi n) :=
  (integrable_peel n hf).prod_right_ae

/-! ## 3. Review round 47 — the ways this could be hollow

**"`Hpi_cons` could be a restatement of the definition."** It is close to
one, and that is the point: it is the only place the `Fin.cons` /
`Fin.tail` bookkeeping happens, and every use above and below depends on
getting index 0 and the tail the right way round. `Hpi_cons'` states the
same fact with the index already split, which is the form a consumer
wants and the form in which a transposition error would be visible.

**"The peel lemmas could be re-derivations of what the estate has."**
`measurePreserving_peel` is the estate's; the integral and integrability
forms were previously inlined inside `EN_eq_integral`'s proof and existed
nowhere as statements. Extracting them is the point — `EN_eq_integral`
needed them once and an induction on dimension needs them at every step.

**"This might not be the engine the second route needs."** The second
route needs exactly three things at each inductive step: the
factorisation, an iterated integral, and a.e.-integrable slices. Those are
the three theorems above. What it also needs, and this file does not
supply, is the a.e.-countable-intersection argument over `m₀` and the two
appeals to `hermite_complete` — the mathematics, as opposed to the
plumbing.
-/

/-- The factorisation at `n = 0`, where the tail is empty and the product
    collapses to the single one-dimensional factor. -/
theorem Hpi_cons_zero (m : Fin 1 → ℕ) (x₀ : ℝ) (y : Fin 0 → ℝ) :
    Hpi 1 m (Fin.cons x₀ y) = (H (m 0)).eval x₀ := by
  rw [Hpi_cons, Hpi]
  simp

end

end HermitePiPeel
