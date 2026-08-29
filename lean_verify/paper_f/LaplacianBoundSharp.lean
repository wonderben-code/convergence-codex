import CycleLaplacianSpectrum
import LaplacianDegreeBound

/-!
# Where else the degree bound is attained: the even cycle, and the withdrawn claim stays withdrawn

`LaplacianDegreeBound` proved `massive ≼ (2Δ + m²)·1` and `(2Δ + m²)⁻¹·1 ≼ green` under a degree
bound `Δ`, and its header ends on an open question it was careful not to answer:

> **`green_bot_attains` proves the lower bound is attained** — on the edgeless graph, where `Δ = 0`
> … **Nothing here says where else it is attained, and a first draft of this paragraph did**: it
> asserted attainment *"on the graphs where every degree is `Δ`"*. **That was not checked and is
> withdrawn before the commit** … the largest Laplacian eigenvalue of a regular graph is not `2Δ`
> in general.

**This file says where else: on every even cycle, at `Δ = 2`.** And it leaves the withdrawn claim
withdrawn, because the withdrawn claim was about *all* regular graphs and this is one family.

## How it was found, which is the interesting part

By `CycleLaplacianSpectrum`, one unit earlier. That file computes the eigenvalues of `massive` on
the cycle of length `N` as `2 + m² − 2cos(2πk/N)`, and reading the list at `k = N/2` — available
exactly when `N` is even — gives `2 + m² + 2 = 4 + m²`, which is `2Δ + m²` at `Δ = 2`. **So a
sharpness question that had been open since the degree bound was written fell out of a spectrum
that was computed for a different reason**, which is what `PROOF_STRATEGY` §6's first question is
for.

**And then the proof did not need the spectrum at all.** At `k = N/2` the character `ζ^{jN/2}` is
`(−1)^j` — real — so the eigenvector is the **alternating vector** and everything here is a real
matrix computation with no complex numbers in it. `CycleLaplacianSpectrum` is cited for
`sub_one_ne_add_one` and for nothing else. **The complexification found the answer and is not on
the path to it**, which is the same shape as `ERRATUM 334` with the outcome reversed: there the
file built first and the consumer disagreed; here the file was read first and the route it
suggested turned out to be cheaper than itself.

## What is proved

* `massive_mulVec_apply` — the real analogue of `CycleLaplacianSpectrum.cx_massive_mulVec`:
  `(massive *ᵥ x) v = (deg v + m²)·x v − Σ_{u ∼ v} x u`, at every finite graph;
* `alt`, `alt_add_one`, `alt_sub_one` — the alternating vector, and the shift that needs `N` even:
  wrapping past the end must flip the sign, and on an odd cycle it does not;
* **`massive_mulVec_alt`** — `massive *ᵥ alt = (4 + m²) • alt` on every even cycle of length ≥ 4;
* `green_mulVec_alt` — hence `green *ᵥ alt = (4 + m²)⁻¹ • alt`;
* **`massive_cycle_le_smul_one_iff`** — `massive ≼ c·1` on the even cycle **iff** `4 + m² ≤ c`.
  The forward half is the alternating vector tested against the Loewner inequality; the reverse
  half is `LaplacianDegreeBound.massive_le_smul_one` itself, so the two together say the constant
  is **exactly** right and not merely an upper bound;
* **`le_inv_of_smul_one_le_green`** — and no constant above `(4 + m²)⁻¹` bounds `green` below
  there, so `smul_one_le_green` cannot be raised at `Δ = 2` either.

## What this is NOT

**It does not revive the withdrawn claim.** That claim was that the bound is attained on *every*
graph with all degrees `Δ`. This is one family at one value of `Δ`. The odd cycle is 2-regular and
is **not** covered — the alternating vector does not exist there, which is exactly why
`alt_add_one` needs the length even — and nothing here says whether the bound is attained on it.

**It is not a claim about the whole spectrum.** `4 + m²` is exhibited as *an* eigenvalue and shown
to be an upper bound for the Loewner comparison; that it is the **largest** eigenvalue is not
stated, because the `iff` above delivers the sharpness without it.

**`Δ = 2` only.** Nothing here says anything about a general `Δ`, and the estate's box graphs have
`Δ = 2d`; the box is not a cycle and this does not reach it.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LaplacianBoundSharp

open Matrix GraphLaplacian SimpleGraph
open scoped MatrixOrder

/-! ## 1. The massive operator on a real vector -/

theorem massive_mulVec_apply {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (m : ℝ) (x : V → ℝ) (v : V) :
    (massive G m *ᵥ x) v = ((G.degree v : ℝ) + m ^ 2) * x v - ∑ u ∈ G.neighborFinset v, x u := by
  rw [massive, Matrix.add_mulVec, Pi.add_apply, SimpleGraph.lapMatrix_mulVec_apply]
  have hd : (Matrix.diagonal (fun _ : V => m ^ 2) *ᵥ x) v = m ^ 2 * x v := by
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Finset.sum_ite_eq]
  rw [hd]
  ring

/-! ## 2. The alternating vector -/

/-- `(-1)^j`, the top eigenvector of the even cycle's Laplacian. -/
def alt (N : ℕ) (j : Fin N) : ℝ := (-1) ^ j.val

theorem neg_one_pow_mod_two (a : ℕ) : (-1 : ℝ) ^ a = (-1) ^ (a % 2) := by
  conv_lhs => rw [← Nat.div_add_mod a 2]
  rw [pow_add, pow_mul]
  norm_num

theorem alt_add_one (M : ℕ) (j : Fin (2 * M + 4)) :
    alt (2 * M + 4) (j + 1) = - alt (2 * M + 4) j := by
  have hdvd : (2 : ℕ) ∣ (2 * M + 4) := ⟨M + 2, by ring⟩
  have hval : (j + 1 : Fin (2 * M + 4)).val = (j.val + 1) % (2 * M + 4) := by
    simp [Fin.val_add]
  have key : ((-1 : ℝ)) ^ ((j.val + 1) % (2 * M + 4)) = -((-1 : ℝ) ^ j.val) := by
    rw [neg_one_pow_mod_two ((j.val + 1) % (2 * M + 4)), Nat.mod_mod_of_dvd _ hdvd,
      ← neg_one_pow_mod_two (j.val + 1), pow_succ]
    ring
  rw [alt, alt, hval, key]

theorem alt_sub_one (M : ℕ) (j : Fin (2 * M + 4)) :
    alt (2 * M + 4) (j - 1) = - alt (2 * M + 4) j := by
  have h := alt_add_one M (j - 1)
  rw [sub_add_cancel] at h
  rw [h, neg_neg]

theorem alt_mul_self (N : ℕ) (j : Fin N) : alt N j * alt N j = 1 := by
  rw [alt, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem dotProduct_alt_self (N : ℕ) : alt N ⬝ᵥ alt N = (N : ℝ) := by
  rw [dotProduct]
  simp [alt_mul_self]

/-! ## 3. The top eigenvalue of the even cycle -/

/-- **`massive` ON THE EVEN CYCLE HAS EIGENVALUE `4 + m²` AT THE ALTERNATING VECTOR.** -/
theorem massive_mulVec_alt (M : ℕ) (m : ℝ) :
    massive (cycleGraph (2 * M + 4)) m *ᵥ alt (2 * M + 4)
      = (4 + m ^ 2) • alt (2 * M + 4) := by
  funext j
  rw [massive_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair (CycleLaplacianSpectrum.sub_one_ne_add_one _ j), alt_sub_one, alt_add_one]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem four_add_sq_pos (m : ℝ) : (0 : ℝ) < 4 + m ^ 2 := by positivity

theorem green_mulVec_alt (M : ℕ) {m : ℝ} (hm : m ≠ 0) :
    green (cycleGraph (2 * M + 4)) m *ᵥ alt (2 * M + 4)
      = (4 + m ^ 2)⁻¹ • alt (2 * M + 4) := by
  have hne : (4 + m ^ 2) ≠ 0 := ne_of_gt (four_add_sq_pos m)
  have hmul := congrArg (fun v => green (cycleGraph (2 * M + 4)) m *ᵥ v) (massive_mulVec_alt M m)
  simp only [Matrix.mulVec_mulVec, green_mul_massive _ hm, Matrix.one_mulVec,
    Matrix.mulVec_smul] at hmul
  have h2 := congrArg (fun v : Fin (2 * M + 4) → ℝ => (4 + m ^ 2)⁻¹ • v) hmul
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  exact h2.symm

/-! ## 4. So the degree bound's constant cannot be lowered at `Δ = 2` -/

theorem cycle_degree_le (M : ℕ) :
    ∀ p : Fin (2 * M + 4), (((cycleGraph (2 * M + 4)).degree p : ℝ)) ≤ 2 := by
  intro p
  rw [cycleGraph_degree_three_le]
  norm_num

/-- **THE CONSTANT `2Δ + m²` IS EXACTLY RIGHT AT `Δ = 2`**: on the even cycle, `massive ≼ c·1`
holds **iff** `c ≥ 4 + m²`, and `4 + m² = 2·2 + m²`. -/
theorem massive_cycle_le_smul_one_iff (M : ℕ) (m c : ℝ) :
    massive (cycleGraph (2 * M + 4)) m
        ≤ c • (1 : Matrix (Fin (2 * M + 4)) (Fin (2 * M + 4)) ℝ) ↔ 4 + m ^ 2 ≤ c := by
  constructor
  · intro h
    have hN : (0 : ℝ) < ((2 * M + 4 : ℕ) : ℝ) := by positivity
    have hq := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (alt (2 * M + 4))
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg, massive_mulVec_alt] at hq
    have h1 : alt (2 * M + 4) ⬝ᵥ ((4 + m ^ 2) • alt (2 * M + 4))
        = (4 + m ^ 2) * ((2 * M + 4 : ℕ) : ℝ) := by
      rw [dotProduct_smul, smul_eq_mul, dotProduct_alt_self]
    have h2 : alt (2 * M + 4) ⬝ᵥ
        ((c • (1 : Matrix (Fin (2 * M + 4)) (Fin (2 * M + 4)) ℝ)) *ᵥ alt (2 * M + 4))
        = c * ((2 * M + 4 : ℕ) : ℝ) := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
        dotProduct_alt_self]
    rw [h1, h2] at hq
    exact le_of_mul_le_mul_right hq hN
  · intro h
    have hbase := LaplacianDegreeBound.massive_le_smul_one (cycleGraph (2 * M + 4))
      (cycle_degree_le M) m
    have hstep : ((2 : ℝ) * 2 + m ^ 2) • (1 : Matrix (Fin (2 * M + 4)) (Fin (2 * M + 4)) ℝ)
        ≤ c • (1 : Matrix (Fin (2 * M + 4)) (Fin (2 * M + 4)) ℝ) := by
      refine Matrix.le_iff.mpr ?_
      rw [← sub_smul]
      exact (Matrix.PosSemidef.one).smul (by linarith)
    exact le_trans hbase hstep

/-- **AND THE PROPAGATOR'S LOWER BOUND CANNOT BE RAISED THERE EITHER.** -/
theorem le_inv_of_smul_one_le_green (M : ℕ) {m : ℝ} (hm : m ≠ 0) (c : ℝ)
    (h : c • (1 : Matrix (Fin (2 * M + 4)) (Fin (2 * M + 4)) ℝ)
      ≤ green (cycleGraph (2 * M + 4)) m) :
    c ≤ (4 + m ^ 2)⁻¹ := by
  have hN : (0 : ℝ) < ((2 * M + 4 : ℕ) : ℝ) := by positivity
  have hq := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg (alt (2 * M + 4))
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg, green_mulVec_alt _ hm] at hq
  have h1 : alt (2 * M + 4) ⬝ᵥ ((4 + m ^ 2)⁻¹ • alt (2 * M + 4))
      = (4 + m ^ 2)⁻¹ * ((2 * M + 4 : ℕ) : ℝ) := by
    rw [dotProduct_smul, smul_eq_mul, dotProduct_alt_self]
  have h2 : alt (2 * M + 4) ⬝ᵥ
      ((c • (1 : Matrix (Fin (2 * M + 4)) (Fin (2 * M + 4)) ℝ)) *ᵥ alt (2 * M + 4))
      = c * ((2 * M + 4 : ℕ) : ℝ) := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_alt_self]
  rw [h1, h2] at hq
  exact le_of_mul_le_mul_right hq hN

end LaplacianBoundSharp
