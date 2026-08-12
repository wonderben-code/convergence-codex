import GreenLargeMass

/-!
# The concrete target `WALLS` §W1.2 posed, closed at every mass

`GreenLargeMass` §9 built a six-vertex graph — two three-vertex paths `2–0–4` and `1–3–5`,
swapped by `p ↦ p + 3` — to show the large-mass converse is not vacuous on non-regular
graphs, and it decided the graph for `m² > 100`. `WALLS` §W1.2 then named *"whether it is
reflection positive below that"* as the smallest instance of the wall's remaining question
now on the books, and as a finite computation.

**It is not reflection positive at any nonzero mass**, and the computation is three linear
equations.

## The mechanism, and it is not about small mass at all

The reflection swaps the two paths, so **every half-site's mirror lies in the other
component**. The reflected form's matrix is `N p q = green (θ p) q`, and its diagonal `N p p
= green (θ p) p` therefore vanishes — a Green function has no entry between components. A
symmetric matrix with zero diagonal is positive semidefinite only if it is zero
(`GreenLargeMass.posSemidef_abs_le`), and this one is not: `green 4 0` is strictly positive,
`4` and `0` being adjacent.

So the answer does not depend on the mass, and §9's threshold of `100` was never the
boundary of anything — it was the point past which §8's *estimate* became conclusive. **The
estimate's threshold and the graph's actual behaviour had nothing to do with each other**,
which is worth knowing about every threshold that chain produces.

## What is proved from what

Nothing here uses connectedness, components, or block decompositions. Every fact about
`green` comes from one entry of `GraphLaplacian.green_mul_massive` together with
`GraphGreenPositive.green_nonneg`:

* `green 3 0 = 0`, from the three equations at columns `0`, `2`, `4` — they force
`green 3 0 · m²(m² + 3) = 0`;
* `green 4 1 = 0`, the same three at columns `1`, `3`, `5`;
* `green 4 0 > 0`, from the two at columns `4` and `0` plus non-negativity.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace StepGraphSmallMass

open Matrix GraphLaplacian GreenLargeMass GraphReflection

variable {m : ℝ}

local notation "g" => GraphLaplacian.green stepGraph m

/-! ## 1. One entry of `green · massive = 1`, with the operator's entries substituted -/

/-- The defining identity at `(x, y)`, as a sum over the six sites. -/
theorem row_eq (hm : m ≠ 0) (x y : Fin 6) :
    ∑ r : Fin 6, g x r * GraphLaplacian.massive stepGraph m r y = if x = y then 1 else 0 := by
  have h := congrFun (congrFun (GraphLaplacian.green_mul_massive (G := stepGraph) hm) x) y
  rw [Matrix.mul_apply] at h
  rw [h, Matrix.one_apply]

/-- Column `0`: site `0` is the centre of its path, degree `2`, joined to `2` and `4`. -/
theorem col0 (hm : m ≠ 0) (x : Fin 6) :
    g x 0 * (2 + m ^ 2) - g x 2 - g x 4 = if x = 0 then 1 else 0 := by
  rw [← row_eq hm x 0]
  simp +decide [Fin.sum_univ_six, GraphLaplacian.massive_apply,
    show stepGraph.degree 0 = 2 by decide]
  ring

/-- Column `2`: a leaf, degree `1`, joined only to `0`. -/
theorem col2 (hm : m ≠ 0) (x : Fin 6) :
    g x 2 * (1 + m ^ 2) - g x 0 = if x = 2 then 1 else 0 := by
  rw [← row_eq hm x 2]
  simp +decide [Fin.sum_univ_six, GraphLaplacian.massive_apply,
    show stepGraph.degree 2 = 1 by decide]
  ring

/-- Column `4`: the other leaf of the same path. -/
theorem col4 (hm : m ≠ 0) (x : Fin 6) :
    g x 4 * (1 + m ^ 2) - g x 0 = if x = 4 then 1 else 0 := by
  rw [← row_eq hm x 4]
  simp +decide [Fin.sum_univ_six, GraphLaplacian.massive_apply,
    show stepGraph.degree 4 = 1 by decide]
  ring

/-- Column `1`: a leaf of the OTHER path, joined only to `3`. -/
theorem col1 (hm : m ≠ 0) (x : Fin 6) :
    g x 1 * (1 + m ^ 2) - g x 3 = if x = 1 then 1 else 0 := by
  rw [← row_eq hm x 1]
  simp +decide [Fin.sum_univ_six, GraphLaplacian.massive_apply,
    show stepGraph.degree 1 = 1 by decide]
  ring

/-- Column `3`: the centre of the other path, degree `2`, joined to `1` and `5`. -/
theorem col3 (hm : m ≠ 0) (x : Fin 6) :
    g x 3 * (2 + m ^ 2) - g x 1 - g x 5 = if x = 3 then 1 else 0 := by
  rw [← row_eq hm x 3]
  simp +decide [Fin.sum_univ_six, GraphLaplacian.massive_apply,
    show stepGraph.degree 3 = 2 by decide]
  ring

/-- Column `5`: the last leaf. -/
theorem col5 (hm : m ≠ 0) (x : Fin 6) :
    g x 5 * (1 + m ^ 2) - g x 3 = if x = 5 then 1 else 0 := by
  rw [← row_eq hm x 5]
  simp +decide [Fin.sum_univ_six, GraphLaplacian.massive_apply,
    show stepGraph.degree 5 = 1 by decide]
  ring

/-! ## 2. The Green function does not cross between the paths -/

/-- **`green 3 0 = 0`.** Three equations at row `3` force `green 3 0 · m²(m² + 3) = 0`. No
connectedness argument, no block decomposition. -/
theorem green_three_zero (hm : m ≠ 0) : g 3 0 = 0 := by
  have h0 : g 3 0 * (2 + m ^ 2) - g 3 2 - g 3 4 = 0 := by
    have h := col0 hm 3; rwa [if_neg (by decide : ¬((3 : Fin 6) = 0))] at h
  have h2 : g 3 2 * (1 + m ^ 2) - g 3 0 = 0 := by
    have h := col2 hm 3; rwa [if_neg (by decide : ¬((3 : Fin 6) = 2))] at h
  have h4 : g 3 4 * (1 + m ^ 2) - g 3 0 = 0 := by
    have h := col4 hm 3; rwa [if_neg (by decide : ¬((3 : Fin 6) = 4))] at h
  have hpos : (0 : ℝ) < m ^ 2 * (m ^ 2 + 3) := by positivity
  have key : g 3 0 * (m ^ 2 * (m ^ 2 + 3)) = 0 := by
    linear_combination (1 + m ^ 2) * h0 + h2 + h4
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h (ne_of_gt hpos)

/-- **`green 4 1 = 0`**, the same three equations on the other path. -/
theorem green_four_one (hm : m ≠ 0) : g 4 1 = 0 := by
  have h1 : g 4 1 * (1 + m ^ 2) - g 4 3 = 0 := by
    have h := col1 hm 4; rwa [if_neg (by decide : ¬((4 : Fin 6) = 1))] at h
  have h3 : g 4 3 * (2 + m ^ 2) - g 4 1 - g 4 5 = 0 := by
    have h := col3 hm 4; rwa [if_neg (by decide : ¬((4 : Fin 6) = 3))] at h
  have h5 : g 4 5 * (1 + m ^ 2) - g 4 3 = 0 := by
    have h := col5 hm 4; rwa [if_neg (by decide : ¬((4 : Fin 6) = 5))] at h
  have hpos : (0 : ℝ) < m ^ 2 * (m ^ 2 + 3) := by positivity
  have hCA : g 4 5 = g 4 1 := by
    have e : (g 4 5 - g 4 1) * (1 + m ^ 2) = 0 := by linear_combination h5 - h1
    rcases mul_eq_zero.mp e with h | h
    · linarith
    · exact absurd h (by positivity)
  rw [hCA] at h3
  have key : g 4 1 * (m ^ 2 * (m ^ 2 + 3)) = 0 := by
    linear_combination (2 + m ^ 2) * h1 + h3
  rcases mul_eq_zero.mp key with h | h
  · exact h
  · exact absurd h (ne_of_gt hpos)

/-! ## 3. But it is strictly positive along a path -/

/-- **`green 4 0 > 0`.** Two equations plus non-negativity: `green 4 4 ≥ (1 + m²)⁻¹ > 0`, and
`green 4 0 (2 + m²)` is at least that. -/
theorem green_four_zero_pos (hm : m ≠ 0) : 0 < g 4 0 := by
  have h4 : g 4 4 * (1 + m ^ 2) - g 4 0 = 1 := by
    have h := col4 hm 4; rwa [if_pos (by decide : (4 : Fin 6) = 4)] at h
  have h0 : g 4 0 * (2 + m ^ 2) - g 4 2 - g 4 4 = 0 := by
    have h := col0 hm 4; rwa [if_neg (by decide : ¬((4 : Fin 6) = 0))] at h
  have hn40 : 0 ≤ g 4 0 := GraphGreenPositive.green_nonneg stepGraph hm 4 0
  have hn42 : 0 ≤ g 4 2 := GraphGreenPositive.green_nonneg stepGraph hm 4 2
  have hpos : (0 : ℝ) < m ^ 2 := by positivity
  have hid : g 4 0 * (m ^ 2 * m ^ 2 + 3 * m ^ 2 + 1) = g 4 2 * (1 + m ^ 2) + 1 := by
    linear_combination (1 + m ^ 2) * h0 + h4
  nlinarith [hid, hn42, hpos, hn40]

/-! ## 4. And so the graph is not reflection positive at any nonzero mass -/

/-- **THE TARGET `WALLS` §W1.2 POSED, CLOSED.** `stepGraph` is not reflection positive at any
nonzero mass. §9's threshold `m² > 100` was the point past which an *estimate* became conclusive;
the graph itself never had a reflection-positive regime. -/
theorem stepGraph_not_reflectionPositive (hm : m ≠ 0) :
    ¬ GraphReflection.ReflectionPositive stepGraph m sigma6 Hs := by
  intro hRP
  have hc : ∀ p, p ∉ Hs → us p = 0 := us_supported
  have h := hRP us hc
  have hform : (∑ p : Fin 6, ∑ q : Fin 6, us p * us q * g (sigma6 p) q)
      = g 3 0 - g 3 1 - g 4 0 + g 4 1 := by
    rw [show (∑ p : Fin 6, ∑ q : Fin 6, us p * us q * g (sigma6 p) q)
        = GraphReflection.reflectedForm stepGraph m sigma6 us from rfl,
      GreenExpansion.reflectedForm_eq_sum_half (H := Hs) hc]
    simp only [GreenLargeMass.sum_Hs]
    norm_num [us, sigma6_apply, show ((0 : Fin 6) + 3) = 3 from rfl,
      show ((1 : Fin 6) + 3) = 4 from rfl, show ((2 : Fin 6) + 3) = 5 from rfl,
      show (![1, -1, 0, 0, 0, 0] : Fin 6 → ℝ) 2 = 0 from rfl]
    ring
  rw [hform, green_three_zero hm, green_four_one hm] at h
  have hn31 : 0 ≤ g 3 1 := GraphGreenPositive.green_nonneg stepGraph hm 3 1
  linarith [green_four_zero_pos hm, hn31]

end StepGraphSmallMass
