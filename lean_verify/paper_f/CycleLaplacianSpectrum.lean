import MatrixLoewner
import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# The first eigenvalue of a graph Laplacian in this estate: the cycle, exactly

`WALLS.md` §W2.1 §4 says what step 1b of `W2` needs: `G_n(x,y) → G(x,y)` for the box or torus
approximants. **Nothing can be said about a sequence of `G_n` until one `G_n` can be computed**, and
this estate has never computed an eigenvalue of a graph Laplacian at all. Every mention of one is
prose in a header — `LaplacianDegreeBound`, `LatticeUniformStein`, `LatticeWitnessBound` each name
an eigenvalue argument they do not take — and the `eigen`-named declarations in `paper_f` all live
in the `F*` spectral-triple files, about Dirac operators. **This file is the first spectral
computation for `massive`, on the graph where it is exactly solvable.**

## The probe, run before the file and recorded because `ERRATUM 335` says it was not

Against the pinned Mathlib v4.29.1:

* **`Matrix.circulant` exists and is 188 lines of algebra with no spectral theory**: `eigen`
  appears **0** times in it, and so do `det` and `charpoly`. So the classical "a circulant is
  diagonalised by characters" is *not* available and has to be done by hand;
* **the discrete Fourier transform on `ZMod N` does exist** — `Mathlib/Analysis/Fourier/ZMod.lean`,
  `dft` as a `≃ₗ[ℂ]` with an inverse — which is the obvious route to the *basis* half, and is
  **not used here** (see below);
* `SimpleGraph.cycleGraph` exists with `cycleGraph_adj`, `cycleGraph_neighborFinset`,
  `cycleGraph_degree_three_le` **and its own `DecidableRel` instance** — a first draft of this file
  declared a second one and the mismatch broke every rewrite through `degree`;
* `riemannSum` / `RiemannSum` are **0** as identifiers, though `BoxIntegral` carries `integralSum`
  and a `UnitPartition` file.

**No price is attached to any of that** (`ERRATUM 194`): what is recorded is what is present.

## What is proved

General, and new to the estate:

* `cx_lapMatrix`, `cx_massive` — the complexification of the graph Laplacian and of `massive` are
  the complex Laplacian and the complex Laplacian plus `m²`;
* **`cx_massive_mulVec`** — so `(massive ·)` acting on a complex vector is
  `(deg v + m²)·x v − Σ_{u ∼ v} x u`, at every finite graph.

On the cycle of length `N = n + 3`:

* `zeta`, `zeta_pow_card`, `zeta_pow_congr` — the `N`-th root of unity and the fact that its powers
  see the exponent only mod `N`;
* `chi`, `chi_add_one`, `chi_sub_one` — the character vectors and the shift they satisfy, which is
  where the wrap-around is actually used;
* **`cx_massive_mulVec_chi`** — `massive *ᵥ χ_k = ((2 + m²) − (ζ^k + ζ^{-k})) • χ_k`;
* **`eigenvalue_eq_real`** — that eigenvalue is the real number `2 + m² − 2cos(2πk/N)`;
* `eigenvalue_pos` — it is at least `m²`, because the cosine is at most one, and
  `eigenvalue_at_zero` — it **is** `m²` at `k = 0`, the constant vector in the Laplacian's kernel;
* **`cx_green_mulVec_chi`** — hence the propagator's eigenvalues are
  `(2 + m² − 2cos(2πk/N))⁻¹`.

## And it is about the estate's own object, not a detached example

`TorusCycleGraph.torusGraph_one_iso` proves the estate's `d = 1` torus **is** Mathlib's
`cycleGraph`, and `FieldIsoInvariance.gaussianField_torus_eq_cycleGraph` carries that to the
measures: the estate's one-dimensional torus field **is** the cycle-graph field. So these are the
eigenvalues of the covariance of a field this project already has.

## What this is NOT

**An eigenvector family is not a diagonalisation, and nothing here says the `χ_k` span.** No basis,
no linear independence, no orthogonality is proved. **So no entry of `green` is computed**, and
`G_n(x,y)` is not available from this file. Mathlib's `dft` is the obvious route to that half and
is deliberately not taken here; it is a separate unit and is on the watchlist.

**`d = 1` only.** The cycle is a circulant; a `d`-dimensional torus is a tensor product of
circulants and a **box is not a circulant at all** — it has a boundary, and its degree is not
constant. Nothing here reaches either.

**Length at least three.** Everything is stated on `Fin (n + 3)`, because at length two a vertex's
two neighbours coincide and the neighbour sum has one term, not two.

**No limit, no convergence, and `W2` step 1b does not move.** This computes eigenvalues at a fixed
`N`; there is no sequence, no limit and no `G` here.

**Nothing is claimed about the measure.** These are statements about a covariance matrix.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleLaplacianSpectrum

open Matrix GraphLaplacian SimpleGraph

/-! ## 1. The complexified massive operator, acting on a vector -/

section Complexify

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem cx_lapMatrix : MatrixLoewner.cx (G.lapMatrix ℝ) = G.lapMatrix ℂ := by
  ext i j
  simp only [MatrixLoewner.cx_apply, SimpleGraph.lapMatrix, Matrix.sub_apply,
    SimpleGraph.degMatrix, SimpleGraph.adjMatrix, Matrix.diagonal_apply, Matrix.of_apply,
    Complex.ofReal_sub]
  split_ifs <;> push_cast <;> ring

theorem cx_massive (m : ℝ) :
    MatrixLoewner.cx (massive G m) = G.lapMatrix ℂ + Matrix.diagonal (fun _ => (m : ℂ) ^ 2) := by
  rw [massive, ← cx_lapMatrix]
  ext i j
  simp only [MatrixLoewner.cx_apply, Matrix.add_apply, Matrix.diagonal_apply,
    Complex.ofReal_add]
  split_ifs <;> push_cast <;> ring

/-- **THE COMPLEXIFIED MASSIVE OPERATOR ON A VECTOR**: the degree-plus-mass diagonal, minus the
sum over the neighbours. -/
theorem cx_massive_mulVec (m : ℝ) (x : V → ℂ) (v : V) :
    (MatrixLoewner.cx (massive G m) *ᵥ x) v
      = ((G.degree v : ℂ) + (m : ℂ) ^ 2) * x v - ∑ u ∈ G.neighborFinset v, x u := by
  rw [cx_massive G m, Matrix.add_mulVec, Pi.add_apply, SimpleGraph.lapMatrix_mulVec_apply]
  have hd : (Matrix.diagonal (fun _ : V => (m : ℂ) ^ 2) *ᵥ x) v = (m : ℂ) ^ 2 * x v := by
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Finset.sum_ite_eq]
  rw [hd]
  ring

end Complexify

/-! ## 2. The root of unity -/

noncomputable def zeta (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

theorem zeta_ne_zero (N : ℕ) : zeta N ≠ 0 := Complex.exp_ne_zero _

theorem zeta_pow_card {N : ℕ} (hN : N ≠ 0) : zeta N ^ N = 1 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [zeta, ← Complex.exp_nat_mul]
  have : (N : ℂ) * (2 * Real.pi * Complex.I / N) = 2 * Real.pi * Complex.I := by
    field_simp
  rw [this]
  exact Complex.exp_two_pi_mul_I

theorem zeta_pow_mod {N : ℕ} (hN : N ≠ 0) (a : ℕ) : zeta N ^ (a % N) = zeta N ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a N]
  rw [pow_add, pow_mul, zeta_pow_card hN, one_pow, one_mul]

theorem zeta_pow_congr {N : ℕ} (hN : N ≠ 0) {a b : ℕ} (h : a ≡ b [MOD N]) :
    zeta N ^ a = zeta N ^ b := by
  rw [← zeta_pow_mod hN a, ← zeta_pow_mod hN b, h]

/-! ## 3. The character vectors -/

noncomputable def chi (N : ℕ) (k j : Fin N) : ℂ := zeta N ^ (j.val * k.val)

theorem chi_ne_zero (N : ℕ) (k j : Fin N) : chi N k j ≠ 0 := pow_ne_zero _ (zeta_ne_zero N)

theorem chi_add_one (n : ℕ) (k j : Fin (n + 3)) :
    chi (n + 3) k (j + 1) = zeta (n + 3) ^ k.val * chi (n + 3) k j := by
  have hN : (n + 3) ≠ 0 := by omega
  have hval : (j + 1 : Fin (n + 3)).val = (j.val + 1) % (n + 3) := by
    simp [Fin.val_add]
  have hmod : ((j.val + 1) % (n + 3)) * k.val ≡ (j.val + 1) * k.val [MOD (n + 3)] :=
    (Nat.mod_modEq _ _).mul_right _
  rw [chi, chi, hval, zeta_pow_congr hN hmod, add_mul, one_mul, pow_add, mul_comm]

theorem chi_sub_one (n : ℕ) (k j : Fin (n + 3)) :
    chi (n + 3) k (j - 1) = (zeta (n + 3) ^ k.val)⁻¹ * chi (n + 3) k j := by
  have h := chi_add_one n k (j - 1)
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (zeta_ne_zero (n + 3))), one_mul]

/-! ## 4. The eigenvector equation -/

theorem sub_one_ne_add_one (n : ℕ) (j : Fin (n + 3)) : (j - 1 : Fin (n + 3)) ≠ j + 1 := by
  intro h
  have hcard : Finset.card ({j - 1, j + 1} : Finset (Fin (n + 3))) = 2 := by
    rw [← cycleGraph_degree_two_le, cycleGraph_degree_three_le]
  rw [h] at hcard
  simp at hcard

/-- **THE CHARACTER VECTORS ARE EIGENVECTORS OF THE MASSIVE OPERATOR ON THE CYCLE.** -/
theorem cx_massive_mulVec_chi (n : ℕ) (m : ℝ) (k : Fin (n + 3)) :
    MatrixLoewner.cx (massive (cycleGraph (n + 3)) m) *ᵥ chi (n + 3) k
      = ((2 + (m : ℂ) ^ 2) - (zeta (n + 3) ^ k.val + (zeta (n + 3) ^ k.val)⁻¹))
        • chi (n + 3) k := by
  funext j
  rw [cx_massive_mulVec, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one n j), chi_sub_one, chi_add_one]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ## 5. The eigenvalue is real, and it is the classical one -/

theorem zeta_pow_eq_exp (n : ℕ) (k : Fin (n + 3)) :
    zeta (n + 3) ^ k.val
      = Complex.exp (((2 * Real.pi * k.val / (n + 3) : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **THE EIGENVALUE IS `m² + 2 − 2cos(2πk/N)`**, and in particular it is real. -/
theorem eigenvalue_eq_real (n : ℕ) (m : ℝ) (k : Fin (n + 3)) :
    (2 + (m : ℂ) ^ 2) - (zeta (n + 3) ^ k.val + (zeta (n + 3) ^ k.val)⁻¹)
      = ((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ) := by
  rw [zeta_pow_eq_exp, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- **AND IT IS POSITIVE**, bounded below by `m²` because the cosine is at most one. -/
theorem eigenvalue_pos (n : ℕ) {m : ℝ} (hm : m ≠ 0) (k : Fin (n + 3)) :
    0 < 2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) := by
  have h1 : Real.cos (2 * Real.pi * k.val / (n + 3)) ≤ 1 := Real.cos_le_one _
  have h2 : (0 : ℝ) < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  linarith

/-- At `k = 0` the character is constant and the eigenvalue is exactly `m²` — the constant vector
in the Laplacian's kernel, shifted by the mass. -/
theorem eigenvalue_at_zero (n : ℕ) (m : ℝ) :
    2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * ((0 : Fin (n + 3)).val) / (n + 3)) = m ^ 2 := by
  simp

/-! ## 6. Hence the propagator's eigenvalues -/

theorem cx_green_mul_cx_massive {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {m : ℝ} (hm : m ≠ 0) :
    MatrixLoewner.cx (green G m) * MatrixLoewner.cx (massive G m) = 1 := by
  rw [← MatrixLoewner.cx_mul, green_mul_massive G hm, MatrixLoewner.cx_one]

/-- **THE PROPAGATOR ON THE CYCLE HAS EIGENVALUES `(m² + 2 − 2cos(2πk/N))⁻¹`.** -/
theorem cx_green_mulVec_chi (n : ℕ) {m : ℝ} (hm : m ≠ 0) (k : Fin (n + 3)) :
    MatrixLoewner.cx (green (cycleGraph (n + 3)) m) *ᵥ chi (n + 3) k
      = (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ))⁻¹
        • chi (n + 3) k := by
  have hne : (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (eigenvalue_pos n hm k)
  have heq : MatrixLoewner.cx (massive (cycleGraph (n + 3)) m) *ᵥ chi (n + 3) k
      = (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ))
        • chi (n + 3) k := by
    rw [cx_massive_mulVec_chi, eigenvalue_eq_real]
  have hmul := congrArg (fun v => MatrixLoewner.cx (green (cycleGraph (n + 3)) m) *ᵥ v) heq
  simp only [Matrix.mulVec_mulVec, cx_green_mul_cx_massive _ hm, Matrix.one_mulVec,
    Matrix.mulVec_smul] at hmul
  have h2 := congrArg
    (fun v : Fin (n + 3) → ℂ =>
      (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ))⁻¹ • v) hmul
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  exact h2.symm

end CycleLaplacianSpectrum
