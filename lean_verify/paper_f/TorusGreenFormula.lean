import TorusLaplacianSpectrum
import CycleGreenFormula

/-!
# `G_n` on the periodic lattice, in every dimension

`TorusLaplacianSpectrum` proved the product characters are eigenvectors of
`massive (torusGraph d n) m` in every dimension, and fenced itself exactly where the `d = 1` chain
had to be corrected afterwards (`ERRATUM 339`): *an eigenvector family is not a diagonalisation —
the characters are not shown to span, so no entry of `green` is computed.* **This file removes that
fence**, and it is `WALLS §W2.1` §4's `G_n` for the torus approximants in every dimension.

> **`green_torus_apply`** — at every side length `n ≥ 3`, every dimension `d`, and every non-zero
> mass,
>
> ```
> G(x,y)  =  n^{-d} · Σ_k  ( 2d + m² − 2 Σ_i cos(2π k_i / n) )^{-1} · χ_k(y)⁻¹ · χ_k(x)
> ```
>
> with the sum over all `n^d` frequencies `k`. **`green_torus_diag`** is the diagonal, where the
> characters cancel and the formula is a bare sum of reciprocals.

**THE SPANNING STATEMENT IS ORTHOGONALITY, AND IT FACTORISES.** `sum_chiD_mul_inv` says
`Σ_p χ_k(p)·χ_{k'}(p)⁻¹` is `n^d` when `k = k'` and `0` otherwise. The summand is a product over the
axes, so `Finset.sum_prod_piFinset` turns the sum over `Site d n` into a **product of `d` copies of
the ring's own orthogonality** — `CycleGreenFormula.sum_chi_mul_inv`, which is a geometric sum. The
`k ≠ k'` case is then a single vanishing factor at any axis where they differ.

**SO NO `d`-DIMENSIONAL FOURIER THEORY APPEARS HERE EITHER.** The previous unit made that point for
the eigenvector equation; it survives the completeness statement, which is the half one would expect
to need a transform. Mathlib's `dft` on `ZMod N` is not used, and neither is any character theory of
`(ZMod n)^d` — the estate has none, and this file does not build one.

## What this is NOT

**It is still not `WALLS §W2.1` §4's step, and the third clause is why.** That section wants
`G_n(x,y) → G(x,y)` as the side length grows. **There is no sequence here, no limit, and no `ℤ^d`
propagator `G` defined anywhere in this estate**; a closed form at each fixed `n` is a formula, not
a convergence statement. What the wall's account can now drop is its *first* clause, for the torus
as well as the ring.

**The box is not reached and is not close.** `boxGraph` has a boundary and a non-constant degree
(`BoxDegree.boxGraph_degree_le` is an inequality for that reason), so it has no character family at
all and nothing here transfers to it.

**It does not reprove `CycleGreenFormula.green_cycle_apply`, and the two are about different
graphs.** That theorem is about `cycleGraph N`; the `d = 1` case of this one is about
`torusGraph 1 N`. `TorusCycleGraph.torusGraph_one_iso` is an isomorphism between them and **nothing
here is transported along it** — neither statement is derived from the other, and the shared
content is that both proofs run the same geometric sum.

**Nothing is transported to the field either.** The theorem
`FieldIsoInvariance.gaussianField_torus_eq_cycleGraph` relates the `d = 1` lattice's *field* to
the ring's, and is not used: every statement here is about a matrix — a formula for the entries of
an inverse, with no probability anywhere in it. Nothing in the OS chain changes and no published
tag is touched.

**Side length `≥ 3` and `m ≠ 0` are both real hypotheses.** The first is where the `2d` cyclic steps
become distinct neighbours; the second is what makes `massive` invertible and its eigenvalues
non-zero — at `m = 0` the constant character sits in the kernel and there is no propagator to write.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TorusGreenFormula

open Matrix GraphLaplacian SimpleGraph BoxGraph TorusReflection CycleLaplacianSpectrum
open TorusLaplacianSpectrum CycleGreenFormula

variable {d n : ℕ}

/-! ## 1. Orthogonality, one axis at a time -/

/-- The product character is symmetric in its two arguments, as each factor is. -/
theorem chiD_symm (n : ℕ) (k p : Site d n) : chiD n k p = chiD n p k :=
  Finset.prod_congr rfl fun i _ => chi_symm n (k i) (p i)

/-- **ORTHOGONALITY OF THE PRODUCT CHARACTERS.** The sum over the `n^d` sites factorises into `d`
copies of the ring's orthogonality, and a single vanishing axis kills the whole product. -/
theorem sum_chiD_mul_inv (hn : n ≠ 0) (k k' : Site d n) :
    (∑ p : Site d n, chiD n k p * (chiD n k' p)⁻¹)
      = if k = k' then ((n : ℂ) ^ d) else 0 := by
  classical
  have hterm : ∀ p : Site d n, chiD n k p * (chiD n k' p)⁻¹
      = ∏ i : Fin d, (chi n (k i) (p i) * (chi n (k' i) (p i))⁻¹) := by
    intro p
    rw [chiD, chiD, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  have hfac : (∑ p : Site d n, ∏ i : Fin d, (chi n (k i) (p i) * (chi n (k' i) (p i))⁻¹))
      = ∏ i : Fin d, ∑ j : Fin n, (chi n (k i) j * (chi n (k' i) j)⁻¹) := by
    have h := Finset.sum_prod_piFinset (ι := Fin d) (Finset.univ : Finset (Fin n))
      (fun i j => chi n (k i) j * (chi n (k' i) j)⁻¹)
    rwa [Fintype.piFinset_univ] at h
  rw [Finset.sum_congr rfl fun p _ => hterm p, hfac,
    Finset.prod_congr rfl fun i _ => sum_chi_mul_inv hn (k i) (k' i)]
  by_cases hkk : k = k'
  · subst hkk
    simp
  · rw [if_neg hkk]
    obtain ⟨i, hi⟩ : ∃ i : Fin d, k i ≠ k' i := by
      by_contra hc
      exact hkk (funext fun i => not_not.mp fun h => hc ⟨i, h⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-! ## 2. Hence a delta is a sum of characters -/

/-- **THE CHARACTERS SPAN**, in the one form the propagator needs: the indicator of a single site is
their average against its own conjugate. -/
theorem single_eq_sum_chiD (hn : n ≠ 0) (y : Site d n) :
    (Pi.single y (1 : ℂ))
      = ((n : ℂ) ^ d)⁻¹ • ∑ k : Site d n, (chiD n k y)⁻¹ • chiD n k := by
  classical
  have hNc : ((n : ℂ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hn)
  funext x
  have hsum : (∑ k : Site d n, (chiD n k y)⁻¹ • chiD n k) x
      = ∑ k : Site d n, chiD n x k * (chiD n y k)⁻¹ := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, chiD_symm n k x, chiD_symm n k y, mul_comm]
  rw [Pi.smul_apply, hsum, sum_chiD_mul_inv hn x y, Pi.single_apply, smul_eq_mul]
  by_cases hxy : x = y
  · simp [hxy, inv_mul_cancel₀ hNc]
  · simp [hxy]

/-! ## 3. The eigenvalue is positive, so the propagator acts on a character by its reciprocal -/

/-- **THE EIGENVALUE IS POSITIVE**, bounded below by `m²` because each of the `d` cosines is at most
one — the `d = 1` argument with a sum in place of its single term. -/
theorem nu_real_pos (N : ℕ) {m : ℝ} (hm : m ≠ 0) (k : Site d (N + 3)) :
    0 < 2 * d + m ^ 2
      - ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) := by
  have hbound : (∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)))
      ≤ ∑ _i : Fin d, (2 : ℝ) :=
    Finset.sum_le_sum fun i _ => by
      have := Real.cos_le_one (2 * Real.pi * (k i).val / ((N : ℝ) + 3)); linarith
  have hconst : (∑ _i : Fin d, (2 : ℝ)) = 2 * d := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hm2 : (0 : ℝ) < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  rw [hconst] at hbound
  linarith

/-- **THE PROPAGATOR ACTS ON A PRODUCT CHARACTER BY THE RECIPROCAL EIGENVALUE.** -/
theorem cx_green_mulVec_chiD (N : ℕ) {m : ℝ} (hm : m ≠ 0) (k : Site d (N + 3)) :
    MatrixLoewner.cx (green (torusGraph d (N + 3)) m) *ᵥ chiD (N + 3) k
      = (((2 * d + m ^ 2
            - ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) : ℝ) : ℂ))⁻¹
          • chiD (N + 3) k := by
  set c : ℂ := (((2 * d + m ^ 2
      - ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) : ℝ) : ℂ)) with hc
  have hne : c ≠ 0 := by
    rw [hc]
    exact_mod_cast ne_of_gt (nu_real_pos N hm k)
  have heq : MatrixLoewner.cx (massive (torusGraph d (N + 3)) m) *ᵥ chiD (N + 3) k
      = c • chiD (N + 3) k := by
    rw [cx_massive_mulVec_chiD, nu_eq_real, hc]
  have hmul := congrArg
    (fun v => MatrixLoewner.cx (green (torusGraph d (N + 3)) m) *ᵥ v) heq
  simp only [Matrix.mulVec_mulVec, cx_green_mul_cx_massive _ hm, Matrix.one_mulVec,
    Matrix.mulVec_smul] at hmul
  have h2 := congrArg (fun v : Site d (N + 3) → ℂ => c⁻¹ • v) hmul
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  exact h2.symm

/-! ## 4. The propagator of the periodic lattice, entry by entry -/

/-- **`G_n` ON THE PERIODIC LATTICE, IN EVERY DIMENSION.** -/
theorem green_torus_apply (N : ℕ) {m : ℝ} (hm : m ≠ 0) (x y : Site d (N + 3)) :
    ((green (torusGraph d (N + 3)) m x y : ℝ) : ℂ)
      = (((N + 3 : ℕ) : ℂ) ^ d)⁻¹ * ∑ k : Site d (N + 3),
          (((2 * d + m ^ 2
              - ∑ i : Fin d, 2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) : ℝ) : ℂ))⁻¹
            * ((chiD (N + 3) k y)⁻¹ * chiD (N + 3) k x) := by
  classical
  have hN : (N + 3 : ℕ) ≠ 0 := by omega
  have hcol : MatrixLoewner.cx (green (torusGraph d (N + 3)) m) *ᵥ (Pi.single y (1 : ℂ))
      = fun x => ((green (torusGraph d (N + 3)) m x y : ℝ) : ℂ) := by
    funext z
    rw [Matrix.mulVec, dotProduct]
    simp [Pi.single_apply]
  have hexp : MatrixLoewner.cx (green (torusGraph d (N + 3)) m) *ᵥ (Pi.single y (1 : ℂ))
      = MatrixLoewner.cx (green (torusGraph d (N + 3)) m) *ᵥ
        ((((N + 3 : ℕ) : ℂ) ^ d)⁻¹ • ∑ k : Site d (N + 3),
          (chiD (N + 3) k y)⁻¹ • chiD (N + 3) k) := by
    rw [single_eq_sum_chiD hN y]
  rw [hcol] at hexp
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    cx_green_mulVec_chiD N hm] at hexp
  have hx := congrFun hexp x
  rw [hx]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-- **THE DIAGONAL**, where the characters cancel and the formula is a bare sum of reciprocals over
the `n^d` frequencies. -/
theorem green_torus_diag (N : ℕ) {m : ℝ} (hm : m ≠ 0) (x : Site d (N + 3)) :
    ((green (torusGraph d (N + 3)) m x x : ℝ) : ℂ)
      = (((N + 3 : ℕ) : ℂ) ^ d)⁻¹ * ∑ k : Site d (N + 3),
          (((2 * d + m ^ 2
              - ∑ i : Fin d,
                  2 * Real.cos (2 * Real.pi * (k i).val / ((N : ℝ) + 3)) : ℝ) : ℂ))⁻¹ := by
  rw [green_torus_apply N hm x x]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [inv_mul_cancel₀ (chiD_ne_zero (N + 3) k x), mul_one]

end TorusGreenFormula
