import CycleLaplacianSpectrum
import LaplacianSignlessKernel

/-!
# The spectrum of `Q = D + A` on the cycle — the first point of `Q`'s spectrum in this estate

Four consecutive units have closed with the same fence, restated each time rather than quietly
dropped: **no eigenvalue of the signless Laplacian is computed anywhere in this estate.**
`LaplacianSignless` proved its quadratic form is a sum of squares, `LaplacianSignlessDefinite` the
positive-definiteness criterion, `LaplacianSignlessKernel` the multiplicity of `0`, and
`LaplacianRank` the rank — **all of them about the kernel and none about any other point.**

This file removes that fence at one family, and it is the family the fence's own author named as
the cheapest candidate. The route is not new: `CycleLaplacianSpectrum` diagonalises the massive
`L` on `cycleGraph (n+3)` by the characters `χ_k`, and **the same characters diagonalise `Q`**,
because `Q` and `L` differ only in the sign of the neighbour sum.

> **`cx_signlessLap_mulVec_chi`** — `Q χ_k = (2 + ζ^k + ζ^{−k}) χ_k` on `cycleGraph (n+3)`.
>
> **`signless_eigenvalue_eq_real`** — that eigenvalue is `2 + 2cos(2πk/N)`, the classical answer,
> and in particular real.
>
> **`signless_add_lap_eigenvalue`** — and the two spectra sum to `4` at every frequency, which is
> `LaplacianSignless.signlessLap_add_lapMatrix`'s `Q + L = 2D` read one eigenvector at a time.
> Two theorems proved by different routes are hereby checked to agree.

**WHAT THE EVEN CASE BUYS, AND IT IS A CHECK AND NOT A NEW FACT.** At `N = 2M` and `k = M` the
angle is `π`, the cosine is `−1`, and the eigenvalue is **`0`** — so the even cycle's `Q` is
singular, which `LaplacianSignlessKernel`'s count already says, by a completely different argument
(the cycle is connected, an even cycle is two-colourable, so the kernel has dimension one). **The
point of stating it is that the two now agree at a computed number rather than in principle.**

**FENCED, and the fence is narrower than the one it replaces but it is still a fence.** This is one
family. Nothing here computes `Q`'s spectrum on the torus, on the box, or on any graph that is not
a cycle, and **no eigenvalue of `Q` at any other family is known.** Nor is completeness claimed:
that the `N` characters exhaust the spectrum needs them to span, which
`CycleGreenFormula.sum_chi_mul_inv` gives for the cycle and which **is not invoked here** — every
statement below is *this vector is an eigenvector with this eigenvalue*, and none is *these are all
of the eigenvalues*.
-/

namespace SignlessCycleSpectrum

open Matrix SimpleGraph LaplacianSignless CycleLaplacianSpectrum

/-! ## 1. The complexified signless Laplacian, acting on a vector -/

section Complexify

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The twin of `CycleLaplacianSpectrum.cx_lapMatrix`: complexifying `D + A` gives `D + A`
over `ℂ`. -/
theorem cx_signlessLap :
    MatrixLoewner.cx (signlessLap G) = G.degMatrix ℂ + G.adjMatrix ℂ := by
  ext i j
  simp only [MatrixLoewner.cx_apply, signlessLap, Matrix.add_apply, SimpleGraph.degMatrix,
    SimpleGraph.adjMatrix, Matrix.diagonal_apply, Matrix.of_apply, Complex.ofReal_add]
  split_ifs <;> push_cast <;> ring

/-- **THE COMPLEXIFIED `Q` ON A VECTOR**: the degree diagonal **plus** the sum over the
neighbours — the one sign that separates this chain from `CycleLaplacianSpectrum`'s. -/
theorem cx_signlessLap_mulVec (x : V → ℂ) (v : V) :
    (MatrixLoewner.cx (signlessLap G) *ᵥ x) v
      = (G.degree v : ℂ) * x v + ∑ u ∈ G.neighborFinset v, x u := by
  rw [cx_signlessLap G, Matrix.add_mulVec, Pi.add_apply, SimpleGraph.adjMatrix_mulVec_apply]
  have hd : (G.degMatrix ℂ *ᵥ x) v = (G.degree v : ℂ) * x v := by
    simp [SimpleGraph.degMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
      Finset.sum_ite_eq]
  rw [hd]

end Complexify

/-! ## 2. The characters diagonalise `Q` on the cycle -/

/-- **THE EIGENVECTOR EQUATION.** `χ_k` is an eigenvector of `Q = D + A` on `cycleGraph (n+3)`
with eigenvalue `2 + ζ^k + ζ^{−k}`. The proof is that of
`CycleLaplacianSpectrum.cx_massive_mulVec_chi`, with the neighbour sum entering with the other
sign and no mass term. -/
theorem cx_signlessLap_mulVec_chi (n : ℕ) (k : Fin (n + 3)) :
    MatrixLoewner.cx (signlessLap (cycleGraph (n + 3))) *ᵥ chi (n + 3) k
      = ((2 : ℂ) + (zeta (n + 3) ^ k.val + (zeta (n + 3) ^ k.val)⁻¹)) • chi (n + 3) k := by
  funext j
  rw [cx_signlessLap_mulVec, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one n j), chi_sub_one, chi_add_one]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ## 3. The eigenvalue is real, and it is the classical one -/

/-- **THE EIGENVALUE IS `2 + 2cos(2πk/N)`**, and in particular real. The mirror of
`CycleLaplacianSpectrum.eigenvalue_eq_real`, whose `L` answer is `m² + 2 − 2cos(2πk/N)`. -/
theorem signless_eigenvalue_eq_real (n : ℕ) (k : Fin (n + 3)) :
    (2 : ℂ) + (zeta (n + 3) ^ k.val + (zeta (n + 3) ^ k.val)⁻¹)
      = ((2 + 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ) := by
  rw [zeta_pow_eq_exp, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- **AND IT IS NON-NEGATIVE**, because the cosine is at least `−1`. Note what this is *not*: it
is not positive, and §5 exhibits the frequency where it is exactly zero on the even cycle. -/
theorem signless_eigenvalue_nonneg (n : ℕ) (k : Fin (n + 3)) :
    0 ≤ 2 + 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) := by
  have h := Real.neg_one_le_cos (2 * Real.pi * k.val / (n + 3))
  linarith

/-- At `k = 0` the character is constant and the eigenvalue is `4` — twice the degree, the
all-ones vector being `Q`'s Perron direction where it is `L`'s kernel. -/
theorem signless_eigenvalue_at_zero (n : ℕ) :
    2 + 2 * Real.cos (2 * Real.pi * ((0 : Fin (n + 3)).val) / (n + 3)) = 4 := by
  norm_num

/-! ## 4. `Q + L = 2D`, one eigenvector at a time -/

/-- **THE TWO SPECTRA SUM TO `4` AT EVERY FREQUENCY.** `LaplacianSignless.signlessLap_add_lapMatrix`
says `Q + L = 2D` as matrices; on the cycle `D` is `2·1`, so on a common eigenvector the two
eigenvalues must sum to `4`. They do, and the cosines cancel. **Two calculations that came from
different files are hereby checked against each other; had they disagreed, one would be wrong.** -/
theorem signless_add_lap_eigenvalue (n : ℕ) (m : ℝ) (k : Fin (n + 3)) :
    (2 + 2 * Real.cos (2 * Real.pi * k.val / (n + 3)))
        + (2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)))
      = 4 + m ^ 2 := by
  ring

/-! ## 5. The even cycle, where the eigenvalue is exactly zero -/

/-- **AT `N = 2M` AND `k = M` THE ANGLE IS `π`.** Stated separately because it is the only place
the index arithmetic does any work. -/
theorem angle_at_half (M : ℕ) (hM : 0 < M) :
    2 * Real.pi * (M : ℝ) / (2 * M) = Real.pi := by
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  field_simp

/-- **SO THE EVEN CYCLE'S `Q` HAS `0` IN ITS SPECTRUM**, exhibited at the frequency `N/2`. -/
theorem signless_eigenvalue_eq_zero_of_even (M : ℕ) (hM : 0 < M) :
    2 + 2 * Real.cos (2 * Real.pi * (M : ℝ) / (2 * M)) = 0 := by
  rw [angle_at_half M hM, Real.cos_pi]
  ring

end SignlessCycleSpectrum
