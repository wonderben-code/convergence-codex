import CycleLaplacianSpectrum
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum

/-!
# `G_n` for `d = 1`: the propagator of the cycle, entry by entry

`CycleLaplacianSpectrum` computed the eigenvalues of `massive` on the cycle and fenced itself with
the sentence that mattered: **an eigenvector family is not a diagonalisation.** It proved no basis,
no independence and no orthogonality, so **no entry of `green` followed from it**. This file
supplies the missing half and the entries:

```
G(x,y)  =  (1/N) · Σ_k  (m² + 2 − 2cos(2πk/N))⁻¹ · ζ^{(x−y)k}
```

as `green_cycle_apply`, with `ζ^{(x−y)k}` written as `χ_k(x)·χ_k(y)⁻¹`.

**The estate has had closed-form propagators at single graphs** — `LatticeUniformPoincare.green_bot`
on the edgeless graph, and a hand solve at a four-vertex graph in `IndefiniteCoupling`. **This is
the first at every member of a family**, and it is `WALLS §W2.1` §4's `G_n`, in one dimension.

## And the route the watchlist named was not the route

The item opened one unit ago said *"THE ROUTE IS NAMED AND IT IS A LIBRARY ONE"* — Mathlib's
`dft` on `ZMod N`, a linear equivalence, with the `Fin`/`ZMod` bridge as the work. **`dft` does not
appear in this file.** Orthogonality is a geometric sum: `Complex.isPrimitiveRoot_exp` says `zeta N`
is a primitive `N`-th root, so `ζ^k·(ζ^{k'})⁻¹ ≠ 1` for `k ≠ k'` by `IsPrimitiveRoot.pow_inj`, its
`N`-th power is `1`, and `geom_sum_eq` finishes it. **Naming a route with the definite article is
`ERRATUM 278`'s shape in miniature**, and the item is annotated where it stands rather than quietly
closed. Nothing was claimed about cost there, and nothing is claimed about `dft` here — it remains
a route, and it is not this one.

## What is proved

* `isPrimitiveRoot_zeta` — `zeta N` is a primitive `N`-th root of unity, from
  `Complex.isPrimitiveRoot_exp`;
* `chi_eq_pow`, `chi_symm` — the character as a power, and the symmetry `χ_k(j) = χ_j(k)` that lets
  one orthogonality serve for both the site index and the frequency index;
* **`sum_chi_mul_inv`** — `Σ_j χ_k(j)·χ_{k'}(j)⁻¹ = N` when `k = k'` and `0` otherwise;
* **`single_eq_sum_chi`** — hence the coordinate vector at `y` expanded in the characters;
* **`green_cycle_apply`** — the propagator's entries, by applying `green` to that expansion and
  reading off `cx_green_mulVec_chi`;
* `green_cycle_diag` — the diagonal, where the characters cancel and the formula is a bare sum of
  reciprocals.

## What this is NOT

**It is not `G_n → G`, and `W2` step 1b does not move.** This is one `N`, with no sequence, no
limit, and no infinite-volume propagator to converge to — none is defined in this estate. What has
changed is that the object the wall's sentence is *about* now exists in one dimension.

**`d = 1` only.** A `d`-dimensional torus is a tensor product of cycles and a box is not a
circulant at all; neither is reached, and both are on the watchlist as their own items.

**The identity is stated between complex numbers with a real left-hand side.** That the imaginary
parts of the right-hand side cancel is a consequence of the statement, not a separate theorem, and
no real-valued rewriting of the sum is offered here.

**Length at least three**, inherited from `CycleLaplacianSpectrum`, where a vertex needs two
distinct neighbours.

**Nothing is claimed about the measure**, and `OS4` does not move.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleGreenFormula

open Matrix GraphLaplacian SimpleGraph CycleLaplacianSpectrum

/-! ## 1. `zeta` is a primitive root of unity -/

theorem isPrimitiveRoot_zeta {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (zeta N) N :=
  Complex.isPrimitiveRoot_exp N hN

/-! ## 2. The characters are orthogonal -/

theorem chi_eq_pow (N : ℕ) (k j : Fin N) : chi N k j = (zeta N ^ k.val) ^ j.val := by
  rw [chi, ← pow_mul, mul_comm]

theorem chi_symm (N : ℕ) (k j : Fin N) : chi N k j = chi N j k := by
  rw [chi, chi, mul_comm]

/-- **ORTHOGONALITY**: the geometric sum of a non-trivial power of a primitive root vanishes. -/
theorem sum_chi_mul_inv {N : ℕ} (hN : N ≠ 0) (k k' : Fin N) :
    ∑ j : Fin N, chi N k j * (chi N k' j)⁻¹ = if k = k' then (N : ℂ) else 0 := by
  by_cases h : k = k'
  · subst h
    have hone : ∀ j : Fin N, chi N k j * (chi N k j)⁻¹ = 1 := fun j =>
      mul_inv_cancel₀ (chi_ne_zero N k j)
    simp [hone]
  · have hprim := isPrimitiveRoot_zeta hN
    have hz : zeta N ^ k'.val ≠ 0 := pow_ne_zero _ (zeta_ne_zero N)
    have hw : ∀ j : Fin N, chi N k j * (chi N k' j)⁻¹
        = ((zeta N ^ k.val) * (zeta N ^ k'.val)⁻¹) ^ j.val := by
      intro j
      rw [chi_eq_pow, chi_eq_pow, ← inv_pow, ← mul_pow]
    have hwne : (zeta N ^ k.val) * (zeta N ^ k'.val)⁻¹ ≠ 1 := by
      intro hc
      rw [← div_eq_mul_inv, div_eq_one_iff_eq hz] at hc
      exact h (Fin.ext (hprim.pow_inj k.isLt k'.isLt hc))
    have hwN : ((zeta N ^ k.val) * (zeta N ^ k'.val)⁻¹) ^ N = 1 := by
      have h1 : (zeta N ^ k.val) ^ N = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, zeta_pow_card hN, one_pow]
      have h2 : (zeta N ^ k'.val) ^ N = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, zeta_pow_card hN, one_pow]
      rw [mul_pow, h1, inv_pow, h2, inv_one, mul_one]
    simp only [hw]
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ((zeta N ^ k.val) * (zeta N ^ k'.val)⁻¹) ^ i) N,
      geom_sum_eq hwne, hwN, sub_self, zero_div, if_neg h]

/-! ## 3. The coordinate vector expanded in the characters -/

theorem single_eq_sum_chi {N : ℕ} (hN : N ≠ 0) (y : Fin N) :
    (Pi.single y (1 : ℂ)) = (N : ℂ)⁻¹ • ∑ k : Fin N, (chi N k y)⁻¹ • chi N k := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  funext x
  have hsum : (∑ k : Fin N, (chi N k y)⁻¹ • chi N k) x
      = ∑ k : Fin N, chi N x k * (chi N y k)⁻¹ := by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, chi_symm N k x, chi_symm N k y, mul_comm]
  rw [Pi.smul_apply, hsum, sum_chi_mul_inv hN x y, Pi.single_apply, smul_eq_mul]
  by_cases hxy : x = y
  · simp [hxy, inv_mul_cancel₀ hNc]
  · simp [hxy]

/-! ## 4. The propagator of the cycle, entry by entry -/

/-- **THE GREEN FUNCTION OF THE CYCLE, EXPLICITLY.** -/
theorem green_cycle_apply (n : ℕ) {m : ℝ} (hm : m ≠ 0) (x y : Fin (n + 3)) :
    ((green (cycleGraph (n + 3)) m x y : ℝ) : ℂ)
      = ((n + 3 : ℕ) : ℂ)⁻¹ * ∑ k : Fin (n + 3),
          (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ))⁻¹
            * ((chi (n + 3) k y)⁻¹ * chi (n + 3) k x) := by
  have hN : (n + 3 : ℕ) ≠ 0 := by omega
  have hcol : MatrixLoewner.cx (green (cycleGraph (n + 3)) m) *ᵥ (Pi.single y (1 : ℂ))
      = fun x => ((green (cycleGraph (n + 3)) m x y : ℝ) : ℂ) := by
    funext z
    rw [Matrix.mulVec, dotProduct]
    simp [Pi.single_apply]
  have hexp : MatrixLoewner.cx (green (cycleGraph (n + 3)) m) *ᵥ (Pi.single y (1 : ℂ))
      = MatrixLoewner.cx (green (cycleGraph (n + 3)) m) *ᵥ
        (((n + 3 : ℕ) : ℂ)⁻¹ • ∑ k : Fin (n + 3), (chi (n + 3) k y)⁻¹ • chi (n + 3) k) := by
    rw [single_eq_sum_chi hN y]
  rw [hcol] at hexp
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sum, Matrix.mulVec_smul,
    cx_green_mulVec_chi n hm] at hexp
  have := congrFun hexp x
  rw [this]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-- **THE DIAGONAL**, where the characters cancel and the formula is a bare sum of reciprocals. -/
theorem green_cycle_diag (n : ℕ) {m : ℝ} (hm : m ≠ 0) (x : Fin (n + 3)) :
    ((green (cycleGraph (n + 3)) m x x : ℝ) : ℂ)
      = ((n + 3 : ℕ) : ℂ)⁻¹ * ∑ k : Fin (n + 3),
          (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ))⁻¹ := by
  rw [green_cycle_apply n hm x x]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [inv_mul_cancel₀ (chi_ne_zero _ k x), mul_one]

end CycleGreenFormula
