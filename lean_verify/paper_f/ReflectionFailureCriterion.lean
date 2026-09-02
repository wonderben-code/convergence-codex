import ReflectionRemainderGeneral

/-!
# The first inequality in this chain: when the reflected form is provably negative

**⚠ THIS FILE IS NOT FIRST AND THE HEADER BELOW IS KEPT AS WRITTEN** (`ERRATUM 94`,
`ERRATUM 427`). `GreenLargeMass.lean` §8's `not_reflectionPositive_of_crossForm_pos_general` is an
inequality of exactly this shape, on the same class of graphs, with the same coefficient
`Δ²/(m²)³` and the same reweighting, stated in the `ℓ¹` mass where this is in the `ℓ²` — and it
exhibits two witnesses where this file exhibits none. **`paper_f/ReflectionFailureSharper.lean`
proves the `ℓ²` hypothesis is the weaker of the two and derives §8's theorem from this one**, which
is what the difference between them is worth.

Everything this chain has produced about `WALLS.md`'s W1 has been a **restatement** —
`GreenExpansion.reflectionPositive_iff_remainder` and its general form say when reflection
positivity holds, not that it does or does not. The bounds of the last three units say how large the
remainder can be. **Composing them gives an inequality**, and this file is that composition.

> **THE STATEMENT.** If `crossForm G m θ H (c · invDeg)` exceeds `Δ² / (m²)³ · ‖c‖²`, then
> **`reflectedForm G m θ c < 0`** — reflection positivity fails at `c`, at every finite graph with a
> degree bound, with a constant that names the degree bound and the mass and **not the number of
> vertices**.

**HOW IT IS ASSEMBLED, AND EVERY PIECE IS FROM THIS AFTERNOON.**
`ReflectionRemainderGeneral.reflectionPositive_iff_remainder_general` turns the question into a
comparison; `NeumannTailBound.norm_neumann_tail_le` bounds the remainder matrix by `Δ² / (m²)³`; and
`abs_remainder_half_le` below turns that matrix bound into a bound on the double sum over the half,
by the argument `RemainderFormBound.abs_remainder_le` already contains, **stated once for an
arbitrary matrix** so that the two consumers share it. §4 recovers
`RemainderFormBound.abs_remainder_le_of_mem_half` from it, so the older statement is a corollary and
not a duplicate (`ERRATUM 201`, `ERRATUM 176`).

**WHY THE DIRECTION IS WHAT IT IS, SAID BEFORE IT CAN BE MISREAD.** `RemainderFormBound`'s header
records that a ceiling on the remainder is the ingredient of a **negative** argument. This is that
argument, and it is the only one those bounds support: **a large cross form forces failure**, and
nothing here says a small one gives success. **W1 asks for the opposite implication** — that
reflection positivity forces `hcross` — and this file does not touch it.

**WHAT THIS IS NOT.**
* **W1 does not move.** The wall wants `reflectionPositive → hcross` in general; this gives a
  sufficient condition for reflection positivity to FAIL. They are different implications and the
  wall's `WHAT WOULD HAVE TO EXIST` is unchanged.
* **No graph is exhibited.** Nothing here produces a `c` with a large cross form, on any graph, at
  any mass; whether the criterion is ever satisfiable is **not attempted, not costed**
  (`ERRATUM 246`) and **not estimated** (`ERRATUM 183`). A criterion with no witness is a criterion.
* **Nothing is sharp**: the chain spends Cauchy–Schwarz, submultiplicativity four times, and the
  degree bound on `‖A‖`, and no loss is quantified.

**No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ReflectionFailureCriterion

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection GreenExpansion
open ReflectionRemainderGeneral
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The half-restricted bound, once, for an arbitrary matrix -/

/-- **THE DOUBLE SUM OVER THE HALF, BOUNDED BY THE MATRIX NORM.** For a `c` vanishing off `H`, the
sums over `H × H` are the sums over `V × V`, and `RemainderFormBound.abs_remainder_le` finishes it.
**No hypothesis on `M`.** -/
theorem abs_remainder_half_le (M : Matrix V V ℝ) (θ : V ≃ V) {H : Finset V} {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0) :
    |∑ p ∈ H, ∑ q ∈ H, c p * c q * M (θ p) q| ≤ ‖M‖ * (c ⬝ᵥ c) := by
  have hinner : ∀ p, ∑ q ∈ H, c p * c q * M (θ p) q = ∑ q, c p * c q * M (θ p) q := by
    intro p
    refine Finset.sum_subset (Finset.subset_univ H) fun q _ hq => ?_
    rw [hc q hq]
    ring
  have houter : ∑ p ∈ H, ∑ q ∈ H, c p * c q * M (θ p) q = ∑ p, ∑ q, c p * c q * M (θ p) q := by
    rw [Finset.sum_congr rfl fun p _ => hinner p]
    refine Finset.sum_subset (Finset.subset_univ H) fun p _ hp => ?_
    rw [Finset.sum_eq_zero]
    intro q _
    rw [hc p hp]
    ring
  rw [houter]
  exact RemainderFormBound.abs_remainder_le M θ c

/-! ## 2. The remainder of the general criterion, bounded -/

/-- The general criterion's right-hand side is at most `Δ² / (m²)³` times the squared length. -/
theorem remainder_le [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    ∑ p ∈ H, ∑ q ∈ H,
        c p * c q * (green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m) (θ p) q
      ≤ Δ ^ 2 / (m ^ 2) ^ 3 * (c ⬝ᵥ c) := by
  have hccnn : 0 ≤ c ⬝ᵥ c := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
  refine le_trans (le_abs_self _) ?_
  refine le_trans (abs_remainder_half_le _ θ hc) ?_
  exact mul_le_mul_of_nonneg_right (NeumannTailBound.norm_neumann_tail_le G hΔ hm) hccnn

/-! ## 3. The inequality -/

/-- **REFLECTION POSITIVITY BOUNDS THE REWEIGHTED CROSS FORM.** At every finite graph with a degree
bound, and with a constant naming the degree bound and the mass and **not the vertex count**. -/
theorem crossForm_le_of_reflectionPositive [Nonempty V] (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0) (hrp : 0 ≤ reflectedForm G m θ c) :
    crossForm G m θ H (fun v => c v * invDeg G m v) ≤ Δ ^ 2 / (m ^ 2) ^ 3 * (c ⬝ᵥ c) :=
  le_trans ((reflectionPositive_iff_remainder_general hM h hm hc).mp hrp)
    (remainder_le hΔ hm hc)

/-- **AND ITS CONTRAPOSITIVE, WHICH IS THE USABLE FORM: A CROSS FORM THAT IS TOO LARGE FORCES THE
REFLECTED FORM NEGATIVE.** The first statement in this chain that is an inequality rather than a
restatement. **It says nothing about the converse**, which is what W1 wants. -/
theorem reflectedForm_neg_of_crossForm_gt [Nonempty V] (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0)
    (hgt : Δ ^ 2 / (m ^ 2) ^ 3 * (c ⬝ᵥ c) < crossForm G m θ H (fun v => c v * invDeg G m v)) :
    reflectedForm G m θ c < 0 := by
  by_contra hcon
  exact absurd (crossForm_le_of_reflectionPositive hM h hΔ hm hc (not_lt.mp hcon))
    (not_le.mpr hgt)

/-! ## 4. The older half-restricted bound is a corollary -/

/-- `RemainderFormBound.abs_remainder_le_of_mem_half` recovered from §1, so that the general lemma
subsumes it rather than duplicating it (`ERRATUM 201`). -/
example [Nonempty V] {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) (θ : V ≃ V)
    {H : Finset V} {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    |∑ p ∈ H, ∑ q ∈ H,
        c p * c q * (green G m * G.adjMatrix ℝ * G.adjMatrix ℝ) (θ p) q|
      ≤ Δ ^ 2 / m ^ 2 * (c ⬝ᵥ c) := by
  have hccnn : 0 ≤ c ⬝ᵥ c := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
  refine le_trans (abs_remainder_half_le _ θ hc) ?_
  exact mul_le_mul_of_nonneg_right (RemainderFormBound.norm_green_adj_adj_le G hΔ hm) hccnn

end ReflectionFailureCriterion
