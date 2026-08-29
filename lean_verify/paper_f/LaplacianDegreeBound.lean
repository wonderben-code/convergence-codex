import MatrixLoewner
import BoxDegree
import LatticeUniformPoincare

/-!
# The propagator bounded BELOW, uniformly in the box

`LatticeUniformStein`'s "What this is NOT" names a gap in its own words:

> **The constant is uniform in the graph; that does not make every APPLICATION uniform.** Applying
> this to `LatticeFieldWitness.absCoordField` gives a bound whose `L` involves `(√G)⁻¹`, and
> **nothing here analyses how that grows with the box**. It plausibly does not grow — `(√G)⁻¹` is
> controlled by the largest eigenvalue of `massive`, which a degree bound controls — but that is
> **not proved here and not costed**.

This file proves the half that sentence names as the mechanism: **a degree bound controls the
largest eigenvalue of `massive`, and hence bounds the propagator below in the Loewner order.**

## The chain, and every link is one step

* **`lapMatrix_quadForm_le`** — `xᵀ L x ≤ 2Δ ‖x‖²` whenever every degree is at most `Δ`. From
  Mathlib's `lapMatrix_toLinearMap₂'` (`xᵀLx` is the edge sum of `(xᵢ − xⱼ)²`) and
  `(a − b)² ≤ 2a² + 2b²` at each edge, with `degree_eq_sum_if_adj` turning the double sum into a
  degree-weighted one. **Mathlib has the Laplacian's quadratic form and no upper bound on it**;
  `gershgorin` is `0` in the pinned dump, which `WALLS §W4` already records.
* **`lapMatrix_le_smul_one`, `massive_le_smul_one`** — the same in Mathlib's Loewner order on
  `Matrix`, the order `MatrixLoewner` established this estate can use.
* **`smul_one_le_green`** — hence `(2Δ + m²)⁻¹ • 1 ≼ green G m`, by
  `MatrixLoewner.posDef_inv_le_inv`. **The estate had the antitonicity and had never pointed it at
  a constant matrix.**
* **`smul_one_le_green_boxGraph`** — the point of the exercise. `BoxDegree.boxGraph_degree_le`
  bounds the box's degree by `2d`, **with no `n` in it**, so
  `(4d + m²)⁻¹ • 1 ≼ green (boxGraph d n) m` at every side length. **The constant names the
  dimension and not the volume.**

## What this is NOT, and the fence is the same shape as the one it half-closes

**This bounds `green` below; it does not bound `(√G)⁻¹`.** Going from one to the other is an
eigenvalue argument — `green ≽ c·1` puts every eigenvalue of `green` at or above `c`, so every
eigenvalue of `√green` is at or above `√c` and `(√G)⁻¹` has norm at most `c^{-1/2}` — and it needs
the square root's spectrum, which this file does not touch and `LatticeSqrtEquiv` states in its own
terms. **Not attempted, no cost claimed** (`ERRATUM 246`), and **no estimate offered**
(`ERRATUM 183`, and on this chain four difficulty estimates out of five were wrong).

**Nothing here is a spectral gap.** `2Δ + m²` is an upper bound on the largest eigenvalue of
`massive`, which is the *bottom* of the propagator, not the *top* of the spectrum of anything.

**`OS4` does not move.** No sequence of measures, no limit, no compactness, as in every file of
this chain.

**And this is a LOWER bound where `GreenLargeMass.green_le_smul_one` is an upper one.** The two
together sandwich the propagator: `(2Δ + m²)⁻¹ • 1 ≼ green ≼ m⁻² • 1`.

**`green_bot_attains` proves the lower bound is attained** — on the edgeless graph, where `Δ = 0`
and `LatticeUniformPoincare.green_bot` computes `green` exactly, both ends of the sandwich collapse
onto it. **Nothing here says where else it is attained, and a first draft of this paragraph did**:
it asserted attainment *"on the graphs where every degree is `Δ`"*. **That was not checked and is
withdrawn before the commit rather than left to be read charitably** (`ERRATUM 247`'s precedent,
`ERRATUM 194`'s rule) — the largest Laplacian eigenvalue of a regular graph is not `2Δ` in general,
and the claim was written from the shape of the proof rather than from a computation.

> **^ WHERE ELSE IT IS ATTAINED IS NOW ANSWERED, 2026-08-29, AND THE WITHDRAWAL STANDS.**
> `paper_f/LaplacianBoundSharp.massive_cycle_le_smul_one_iff`: on **every even cycle** of length at
> least four, `massive ≼ c·1` holds **iff** `4 + m² ≤ c`, and `4 + m² = 2Δ + m²` at `Δ = 2` — so
> the constant is exactly right there, not merely an upper bound, and
> `le_inv_of_smul_one_le_green` says the propagator's lower bound cannot be raised there either.
> **The withdrawn sentence is still withdrawn and was still right to be**: it claimed attainment on
> *every* graph with all degrees `Δ`, and this is one family at one `Δ`. **The odd cycle is
> 2-regular and is not covered** — the eigenvector is the alternating vector, which needs the
> length even — and nothing says whether the bound is attained there.
> Found by reading `CycleLaplacianSpectrum`'s eigenvalue list at `k = N/2`, one unit later.
>
> **^^ AND THE WITHDRAWN SENTENCE IS NOW FALSE RATHER THAN UNCHECKED, the same day.**
> `CycleSpectralBound.odd_cycle_lt` and `odd_cycle_green_not_attained`: on every **odd** cycle of
> length at least five — 2-regular, so `Δ = 2` — a constant **strictly below** `4 + m²` already
> dominates, so the bound is **not** attained there. **The withdrawal was right and is now known
> to have been right**, which is a stronger thing than it was: the sentence claimed attainment on
> every graph with all degrees `Δ`, and one family refutes that quantifier.
> **What is still open is the positive question**: which regular graphs *do* attain it. The even
> cycles are the only ones known to, and nothing here or there says more.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianDegreeBound

open Matrix GraphLaplacian
open scoped MatrixOrder

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## 1. The Laplacian's quadratic form, bounded by twice the maximum degree -/

/-- **`xᵀ L x ≤ 2Δ ‖x‖²`** when every degree is at most `Δ`. The edge sum of `(xᵢ − xⱼ)²` is
bounded termwise by `2xᵢ² + 2xⱼ²`, and each half of that sums to a degree-weighted square sum. -/
theorem lapMatrix_quadForm_le {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (x : V → ℝ) :
    x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x ≤ 2 * Δ * (x ⬝ᵥ x) := by
  classical
  have hq : x ⬝ᵥ (G.lapMatrix ℝ) *ᵥ x
      = (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
    rw [← Matrix.toLinearMap₂'_apply']
    exact G.lapMatrix_toLinearMap₂' ℝ x
  have hdeg : ∀ i : V, (∑ j : V, if G.Adj i j then (2 * x i ^ 2) else 0)
      = 2 * x i ^ 2 * (G.degree i : ℝ) := by
    intro i
    rw [G.degree_eq_sum_if_adj (R := ℝ) i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by by_cases h : G.Adj i j <;> simp [h]
  have hdeg' : ∀ i : V, (∑ j : V, if G.Adj i j then (2 * x j ^ 2) else 0)
      = ∑ j : V, if G.Adj i j then (2 * x j ^ 2) else 0 := fun _ => rfl
  -- the termwise bound
  have hterm : ∑ i : V, ∑ j : V, (if G.Adj i j then (x i - x j) ^ 2 else 0)
      ≤ (∑ i : V, ∑ j : V, if G.Adj i j then (2 * x i ^ 2) else 0)
        + ∑ i : V, ∑ j : V, if G.Adj i j then (2 * x j ^ 2) else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases h : G.Adj i j
    · simp only [if_pos h]
      nlinarith [sq_nonneg (x i + x j)]
    · simp [h]
  -- the swapped copy is the same degree-weighted sum
  have hswap : (∑ i : V, ∑ j : V, if G.Adj i j then (2 * x j ^ 2) else 0)
      = ∑ i : V, 2 * x i ^ 2 * (G.degree i : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hdeg j]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : G.Adj j i
    · rw [if_pos h, if_pos ((SimpleGraph.adj_comm G j i).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((SimpleGraph.adj_comm G i j).mp hc))]
  have hfirst : (∑ i : V, ∑ j : V, if G.Adj i j then (2 * x i ^ 2) else 0)
      = ∑ i : V, 2 * x i ^ 2 * (G.degree i : ℝ) := Finset.sum_congr rfl fun i _ => hdeg i
  have hdegbnd : (∑ i : V, 2 * x i ^ 2 * (G.degree i : ℝ)) ≤ ∑ i : V, 2 * x i ^ 2 * Δ := by
    refine Finset.sum_le_sum fun i _ => ?_
    have : (0 : ℝ) ≤ 2 * x i ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (hΔ i) this
  have hsum : (∑ i : V, 2 * x i ^ 2 * Δ) = 2 * Δ * (x ⬝ᵥ x) := by
    rw [dotProduct]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hq]
  rw [hfirst, hswap] at hterm
  have : ∑ i : V, ∑ j : V, (if G.Adj i j then (x i - x j) ^ 2 else 0)
      ≤ 2 * (2 * Δ * (x ⬝ᵥ x)) := by
    calc ∑ i : V, ∑ j : V, (if G.Adj i j then (x i - x j) ^ 2 else 0)
        ≤ (∑ i : V, 2 * x i ^ 2 * (G.degree i : ℝ))
          + ∑ i : V, 2 * x i ^ 2 * (G.degree i : ℝ) := hterm
      _ ≤ (∑ i : V, 2 * x i ^ 2 * Δ) + ∑ i : V, 2 * x i ^ 2 * Δ :=
          add_le_add hdegbnd hdegbnd
      _ = 2 * (2 * Δ * (x ⬝ᵥ x)) := by rw [hsum]; ring
  linarith

/-! ## 2. The same statement in the Loewner order -/

/-- **`L ≼ 2Δ · 1`.** -/
theorem lapMatrix_le_smul_one {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) :
    G.lapMatrix ℝ ≤ (2 * Δ) • (1 : Matrix V V ℝ) := by
  refine Matrix.le_iff.mpr (Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ (fun x => ?_))
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    refine Matrix.IsSymm.sub ?_ (G.isSymm_lapMatrix (R := ℝ))
    rw [Matrix.smul_one_eq_diagonal]
    exact Matrix.isSymm_diagonal _
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg]
    have h1 : x ⬝ᵥ ((2 * Δ) • (1 : Matrix V V ℝ)) *ᵥ x = 2 * Δ * (x ⬝ᵥ x) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    rw [h1]
    exact lapMatrix_quadForm_le G hΔ x

/-- **`−Δ_G + m² ≼ (2Δ + m²) · 1`.** -/
theorem massive_le_smul_one {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) (m : ℝ) :
    massive G m ≤ (2 * Δ + m ^ 2) • (1 : Matrix V V ℝ) := by
  have h1 := lapMatrix_le_smul_one G hΔ
  have h2 : ((2 * Δ + m ^ 2) • (1 : Matrix V V ℝ))
      = (2 * Δ) • (1 : Matrix V V ℝ) + Matrix.diagonal (fun _ : V => m ^ 2) := by
    rw [add_smul]
    congr 1
    exact Matrix.smul_one_eq_diagonal _
  rw [massive, h2]
  exact add_le_add h1 le_rfl

/-! ## 3. Hence the propagator is bounded below, and the constant is a degree bound -/

/-- **`(2Δ + m²)⁻¹ · 1 ≼ green G m`.** `MatrixLoewner.posDef_inv_le_inv` pointed at a constant
matrix rather than at a second graph. -/
theorem smul_one_le_green {Δ : ℝ} (hΔ : ∀ p : V, (G.degree p : ℝ) ≤ Δ) {m : ℝ} (hm : m ≠ 0)
    (hpos : 0 < 2 * Δ + m ^ 2) :
    (2 * Δ + m ^ 2)⁻¹ • (1 : Matrix V V ℝ) ≤ green G m := by
  have hle := massive_le_smul_one G hΔ m
  have hinv := MatrixLoewner.posDef_inv_le_inv (massive_posDef G hm) hle
  have hd : ((2 * Δ + m ^ 2) • (1 : Matrix V V ℝ))⁻¹
      = (2 * Δ + m ^ 2)⁻¹ • (1 : Matrix V V ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
  rwa [hd] at hinv

/-- **THE LOWER BOUND IS ATTAINED.** On the edgeless graph every degree is `0`, and
`LatticeUniformPoincare.green_bot` computes `green` there exactly — so `smul_one_le_green` at
`Δ = 0` is an equality, and so is `GreenLargeMass.green_le_smul_one`. **Both ends of the sandwich
collapse onto the propagator at the same graph**, which is what makes the constant `2Δ + m²`
un-improvable as a function of `Δ` alone at `Δ = 0`. -/
theorem green_bot_attains {m : ℝ} (hm : m ≠ 0) :
    (2 * (0 : ℝ) + m ^ 2)⁻¹ • (1 : Matrix V V ℝ) = green (⊥ : SimpleGraph V) m := by
  rw [LatticeUniformPoincare.green_bot hm]
  norm_num

omit [DecidableEq V] in
/-- The degree hypothesis at `Δ = 0` on the edgeless graph, so `green_bot_attains` is an equality
in an inequality that genuinely applies there rather than a coincidence of formulas. -/
theorem bot_degree_le : ∀ p : V, (((⊥ : SimpleGraph V).degree p : ℝ)) ≤ 0 := by
  intro p
  simp

/-! ## 4. The box, where the constant does not see the side length -/

open BoxGraph BoxDegree in
/-- **THE POINT OF THE FILE.** `(4d + m²)⁻¹ • 1 ≼ green (boxGraph d n) m` at **every** side length
`n`: the constant names the dimension and not the volume, because `BoxDegree.boxGraph_degree_le`
bounds the degree by `2d` with no `n` in it. -/
theorem smul_one_le_green_boxGraph (d n : ℕ) {m : ℝ} (hm : m ≠ 0) :
    (4 * (d : ℝ) + m ^ 2)⁻¹ • (1 : Matrix (Site d n) (Site d n) ℝ)
      ≤ green (boxGraph d n) m := by
  have hΔ : ∀ p : Site d n, ((boxGraph d n).degree p : ℝ) ≤ 2 * (d : ℝ) := by
    intro p
    have h := boxGraph_degree_le (d := d) (n := n) p
    have : ((boxGraph d n).degree p : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast h
    simpa using this
  have hpos : 0 < 2 * (2 * (d : ℝ)) + m ^ 2 := by positivity
  have h := smul_one_le_green (boxGraph d n) hΔ hm hpos
  have harith : 2 * (2 * (d : ℝ)) + m ^ 2 = 4 * (d : ℝ) + m ^ 2 := by ring
  rwa [harith] at h

end LaplacianDegreeBound
