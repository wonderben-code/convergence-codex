import NeumannTailSharper
import CrossBlockTopEigenvalue

/-!
# The wall chain's threshold, at the sharper constant

`NeumannTailSharper` replaced the tail constant `Δ²/(m²)³` — the value at degree **zero** — by
`Δ²/(m²(δ + m²)²)` at a minimum degree `δ`, and fenced the consequence: *"threading it through is a
separate unit and is not attempted as of 2026-09-03"*. **This is that unit**, written the same day.

Four statements, each the existing one with the sharper constant and the minimum-degree hypothesis
added, and **each proved by the same three lines as the original** — the chain is modular in exactly
the right place, because `ReflectionFailureCriterion.abs_remainder_half_le` takes an **arbitrary**
matrix and returns `‖M‖ · (c ⬝ᵥ c)`, so swapping which norm bound is supplied is a substitution:

```
remainder_le_of_min_degree                    Δ²/(m²(δ+m²)²) · (c ⬝ᵥ c)
crossForm_le_of_reflectionPositive_of_min_degree
reflectedForm_neg_of_crossForm_gt_of_min_degree
topEigen_twistedCross_le_of_min_degree
```

**THE DIRECTION MATTERS AND IT IS THE GOOD ONE.** Every statement here is a **necessary** condition
for reflection positivity, so a smaller constant makes it **harder to satisfy** and the statement
**stronger**. The refutation criterion fires on strictly more graphs than before: any `c` beating
`Δ²/(m²(δ+m²)²)·(c ⬝ᵥ c)` now forces the reflected form negative, where before it had to beat the
larger `Δ²/(m²)³`.

**On the periodic lattice** — `2d`-regular at side length ≥ 3, so `δ = Δ = 2d` — the threshold drops
from `4d²/(m²)³` to `4d²/(m²(2d + m²)²)`.

## What this is not

**Nothing existing changes** (`ERRATUM 337`). `ReflectionFailureCriterion`'s four theorems and
`CrossBlockTopEigenvalue.topEigen_twistedCross_le` keep their constants, their hypotheses and their
consumers; on a graph with an isolated vertex `δ = 0` and the two families coincide, so nothing is
superseded even where the sharper one applies.

**It is still the necessary direction only.** `W1`'s open part is `OS0`/`OS1`/`OS4` (`ERRATUM 441`),
and a sharper necessary condition is not a converse. **No wall moves.**

**The constant is still not exact.** Two of the tail's five factors remain inequalities —
`NeumannTailSharper`'s header says which and why — so this is a smaller upper bound, not the value.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ReflectionThresholdSharper

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection
open ReflectionRemainderGeneral GreenExpansion
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The remainder, at the minimum degree -/

/-- `ReflectionFailureCriterion.remainder_le` with the sharper tail constant. -/
theorem remainder_le_of_min_degree [Nonempty V] {δ Δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ p : V, δ ≤ (G.degree p : ℝ)) (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0)
    {c : V → ℝ} (hc : ∀ p, p ∉ H → c p = 0) :
    ∑ p ∈ H, ∑ q ∈ H,
        c p * c q * (green G m * G.adjMatrix ℝ * Dinv G m * G.adjMatrix ℝ * Dinv G m) (θ p) q
      ≤ Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) * (c ⬝ᵥ c) := by
  have hccnn : 0 ≤ c ⬝ᵥ c := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun v _ => mul_self_nonneg _
  refine le_trans (le_abs_self _) ?_
  refine le_trans (ReflectionFailureCriterion.abs_remainder_half_le _ θ hc) ?_
  exact mul_le_mul_of_nonneg_right
    (NeumannTailSharper.norm_neumann_tail_le_of_min_degree G hδ0 hδ hΔ hm) hccnn

/-! ## 2. The two forms of the criterion -/

/-- **REFLECTION POSITIVITY BOUNDS THE REWEIGHTED CROSS FORM, AT THE SHARPER CONSTANT.** -/
theorem crossForm_le_of_reflectionPositive_of_min_degree [Nonempty V] (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) {δ Δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ p : V, δ ≤ (G.degree p : ℝ))
    (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0) (hrp : 0 ≤ reflectedForm G m θ c) :
    crossForm G m θ H (fun v => c v * invDeg G m v)
      ≤ Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) * (c ⬝ᵥ c) :=
  le_trans ((ReflectionRemainderGeneral.reflectionPositive_iff_remainder_general hM h hm hc).mp hrp)
    (remainder_le_of_min_degree hδ0 hδ hΔ hm hc)

/-- **AND ITS CONTRAPOSITIVE, WHICH NOW FIRES ON STRICTLY MORE VECTORS.** -/
theorem reflectedForm_neg_of_crossForm_gt_of_min_degree [Nonempty V] (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) {δ Δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ p : V, δ ≤ (G.degree p : ℝ))
    (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0) {c : V → ℝ}
    (hc : ∀ p, p ∉ H → c p = 0)
    (hgt : Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) * (c ⬝ᵥ c)
      < crossForm G m θ H (fun v => c v * invDeg G m v)) :
    reflectedForm G m θ c < 0 := by
  by_contra hcon
  exact absurd
    (crossForm_le_of_reflectionPositive_of_min_degree hM h hδ0 hδ hΔ hm hc (not_lt.mp hcon))
    (not_le.mpr hgt)

/-! ## 3. And the eigenvalue form -/

/-- **THE NECESSARY SPECTRAL CONDITION AT THE SHARPER CONSTANT.**
`CrossBlockTopEigenvalue.topEigen_twistedCross_le` with `Δ²/(m²)³` replaced. -/
theorem topEigen_twistedCross_le_of_min_degree [Nonempty V] (hM : IsMirrorHalf θ H Mir)
    (h : IsRefl G θ) {δ Δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ p : V, δ ≤ (G.degree p : ℝ))
    (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (hm : m ≠ 0)
    (hrp : ∀ c : V → ℝ, (∀ p, p ∉ H → c p = 0) → 0 ≤ reflectedForm G m θ c) :
    RayleighVariational.topEigen
        (CrossBlockTopEigenvalue.twistedCross_isHermitian (G := G) (m := m) (H := H) h)
      ≤ Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) := by
  set hHerm := CrossBlockTopEigenvalue.twistedCross_isHermitian (G := G) (m := m) (H := H) h
  set T := RayleighVariational.topEigen hHerm with hT
  by_contra hcon
  have hm2 : (0 : ℝ) < m ^ 2 := by positivity
  have hδm : (0 : ℝ) < δ + m ^ 2 := by linarith
  have hKnn : 0 ≤ Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) := by
    refine div_nonneg (sq_nonneg _) ?_
    positivity
  have hTpos : 0 < T := lt_of_le_of_lt hKnn (not_le.mp hcon)
  obtain ⟨x, hx0, hx⟩ := OpNormTopEigenvalue.exists_eigenvector_sup' hHerm
  have hxT : CrossBlockTopEigenvalue.twistedCross G m θ H *ᵥ x = T • x := hx
  have hsupp : ∀ p, p ∉ H → x p = 0 := fun p hp =>
    CrossBlockTopEigenvalue.eigenvector_eq_zero_of_not_mem (ne_of_gt hTpos) hxT hp
  have hxx : 0 < x ⬝ᵥ x := by
    refine lt_of_le_of_ne ?_ (Ne.symm fun h0 => hx0 (dotProduct_self_eq_zero.1 h0))
    rw [dotProduct]
    exact Finset.sum_nonneg fun p _ => mul_self_nonneg _
  have hquad : x ⬝ᵥ CrossBlockTopEigenvalue.twistedCross G m θ H *ᵥ x = T * (x ⬝ᵥ x) := by
    rw [hxT, dotProduct_smul, smul_eq_mul]
  have hgt : Δ ^ 2 / (m ^ 2 * (δ + m ^ 2) ^ 2) * (x ⬝ᵥ x)
      < crossForm G m θ H (fun v => x v * invDeg G m v) := by
    rw [← CrossBlockTopEigenvalue.quadForm_twistedCross hM x, hquad]
    exact mul_lt_mul_of_pos_right (not_le.mp hcon) hxx
  exact absurd
    (crossForm_le_of_reflectionPositive_of_min_degree hM h hδ0 hδ hΔ hm hsupp (hrp x hsupp))
    (not_le.mpr hgt)

end ReflectionThresholdSharper
