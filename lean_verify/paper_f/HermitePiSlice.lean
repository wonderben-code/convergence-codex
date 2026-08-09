/-
  HermitePiSlice.lean — the inductive step's hypothesis, transferred.

  WHY. The second route to stair N2 inducts on the dimension. At each step
  it needs one thing before the inductive hypothesis can be applied: from
  *`F` is orthogonal to every multi-index Hermite product in `n+1`
  variables*, deduce that for each fixed one-dimensional index `m₀`, the
  **slice-integral**

      `G_{m₀}(y) = ∫ F(cons x₀ y)·H_{m₀}(x₀) dγ(x₀)`

  is orthogonal to every multi-index Hermite product in `n` variables.
  That is the hypothesis of the inductive call, and it is pure Fubini on
  top of `HermitePiPeel`.

  WHAT THIS FILE PROVES:
  * **`integrable_F_mul_Hpi`** — the products that appear are integrable,
    by Cauchy–Schwarz against the product measure.
  * **`slice_orthogonality`** — the transfer itself. With
    `HermitePiPeel.Hpi_cons'` supplying the factorisation and
    `integral_peel_fubini` the iterated integral, the whole content is one
    swap of the order of integration and one constant pulled out.

  WHAT THIS DOES NOT DO. The induction needs two more things this file
  does not supply: that each `G_{m₀}` is itself in `L²(γⁿ)` — a
  Cauchy–Schwarz estimate plus Fubini on the square — and the
  a.e.-countable-intersection argument over `m₀` that turns "each
  `G_{m₀}` vanishes a.e." into "for a.e. `y`, ALL of them vanish". Neither
  is hard; neither is here; and the header says so rather than letting the
  file read as though the stair were finished.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiPeel

namespace HermitePiSlice

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi HermitePiPeel

noncomputable section

/-! ## 1. The products are integrable -/

theorem integrable_F_mul_Hpi (n : ℕ) {F : (Fin n → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi n)) (m : Fin n → ℕ) :
    Integrable (fun x => F x * Hpi n m x) (gaussPi n) :=
  MemLp.integrable_mul hF (Hpi_memLp n m)

/-- The consed form of the same integrand, on the product measure. -/
theorem integrable_cons_mul (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1))) (m₀ : ℕ) (m' : Fin n → ℕ) :
    Integrable (fun p : ℝ × (Fin n → ℝ) =>
        F (Fin.cons p.1 p.2) * ((H m₀).eval p.1 * Hpi n m' p.2))
      ((gaussianReal 0 1).prod (gaussPi n)) := by
  have hbase := integrable_peel n
    (integrable_F_mul_Hpi (n + 1) hF (Fin.cons m₀ m'))
  refine hbase.congr (Filter.Eventually.of_forall fun p => ?_)
  dsimp only
  rw [Hpi_cons' n m₀ m' p.1 p.2]

/-! ## 2. The transfer -/

/-- **THE INDUCTIVE STEP'S HYPOTHESIS.** If `F` pairs to zero with the
    `(n+1)`-variable Hermite product indexed by `cons m₀ m'`, then the
    `m₀`-th slice-integral pairs to zero with the `n`-variable product
    indexed by `m'`. -/
theorem slice_orthogonality (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1))) (m₀ : ℕ) (m' : Fin n → ℕ)
    (h : ∫ x, F x * Hpi (n + 1) (Fin.cons m₀ m') x ∂gaussPi (n + 1) = 0) :
    ∫ y, (∫ x₀, F (Fin.cons x₀ y) * (H m₀).eval x₀ ∂(gaussianReal 0 1))
        * Hpi n m' y ∂gaussPi n = 0 := by
  -- peel the (n+1)-dimensional integral, then factorise the Hermite product
  have hpeel := integral_peel_fubini n (integrable_F_mul_Hpi (n + 1) hF (Fin.cons m₀ m'))
  rw [h] at hpeel
  have hfact : ∀ x₀ : ℝ, ∀ y : Fin n → ℝ,
      F (Fin.cons x₀ y) * Hpi (n + 1) (Fin.cons m₀ m') (Fin.cons x₀ y)
        = F (Fin.cons x₀ y) * ((H m₀).eval x₀ * Hpi n m' y) := by
    intro x₀ y
    rw [Hpi_cons' n m₀ m' x₀ y]
  have hinner : ∀ x₀ : ℝ,
      (∫ y, F (Fin.cons x₀ y) * Hpi (n + 1) (Fin.cons m₀ m') (Fin.cons x₀ y) ∂gaussPi n)
        = ∫ y, F (Fin.cons x₀ y) * ((H m₀).eval x₀ * Hpi n m' y) ∂gaussPi n := by
    intro x₀
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hfact x₀ y)
  simp_rw [hinner] at hpeel
  -- swap the order of integration
  have hswap : (∫ x₀, ∫ y, F (Fin.cons x₀ y) * ((H m₀).eval x₀ * Hpi n m' y)
        ∂gaussPi n ∂(gaussianReal 0 1))
      = ∫ y, ∫ x₀, F (Fin.cons x₀ y) * ((H m₀).eval x₀ * Hpi n m' y)
        ∂(gaussianReal 0 1) ∂gaussPi n :=
    integral_integral_swap (integrable_cons_mul n hF m₀ m')
  rw [hswap] at hpeel
  -- and pull the `n`-dimensional factor out of the inner integral
  have hgoal : (∫ y, (∫ x₀, F (Fin.cons x₀ y) * (H m₀).eval x₀ ∂(gaussianReal 0 1))
        * Hpi n m' y ∂gaussPi n)
      = ∫ y, ∫ x₀, F (Fin.cons x₀ y) * ((H m₀).eval x₀ * Hpi n m' y)
        ∂(gaussianReal 0 1) ∂gaussPi n := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    dsimp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x₀ => ?_)
    ring
  rw [hgoal, ← hpeel]

/-! ## 3. Review round 48 — the ways this could be hollow

**"It could be Fubini stated twice."** It is Fubini used twice, and the
content is that the two uses compose with the `cons` factorisation to move
an orthogonality hypothesis DOWN a dimension. The statement is about
`Hpi (n+1)` on one side and `Hpi n` on the other; that drop is the whole
point and is not something Fubini gives on its own.

**"The integrability side conditions could be doing no work."**
`integrable_cons_mul` is what licenses the swap, and it is obtained by
transporting the `(n+1)`-dimensional integrability along the peel rather
than re-deriving it — which is exactly why `HermitePiPeel` extracted
`integrable_peel` as a statement.

**"It might not be the hypothesis the induction needs."** It is the
hypothesis of the inductive CALL: the inductive hypothesis is applied to
`G_{m₀}` with test index `m'`, and this is the `m'`-orthogonality of
`G_{m₀}`. What is still missing before the call can be made is that
`G_{m₀} ∈ L²(γⁿ)`, and the header says so.
-/

/-- Stated for a general multi-index rather than a split one, which is the
    form the induction quantifies over — `Fin.cons_self_tail` makes them
    the same statement, and having both spellings avoids a `cons`/`tail`
    transposition at the call site. -/
theorem slice_orthogonality' (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1))) (m : Fin (n + 1) → ℕ)
    (h : ∫ x, F x * Hpi (n + 1) m x ∂gaussPi (n + 1) = 0) :
    ∫ y, (∫ x₀, F (Fin.cons x₀ y) * (H (m 0)).eval x₀ ∂(gaussianReal 0 1))
        * Hpi n (Fin.tail m) y ∂gaussPi n = 0 := by
  have hm : Fin.cons (m 0) (Fin.tail m) = m := Fin.cons_self_tail m
  refine slice_orthogonality n hF (m 0) (Fin.tail m) ?_
  rw [hm]
  exact h

end

end HermitePiSlice
