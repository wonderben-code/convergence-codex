import SpectralEntryRatio
import PerronGap

/-!
# Two-sided bounds on the top eigenvalue, and the first bound this estate has on a free energy

`TransferPowerSum.log_partition2_tendsto_log_top` proves that the free energy per row of the
two-dimensional Ising strip **is** `log λ_top`. Nothing in this estate bounds `λ_top`: the only
statements about it are that it is the maximum (`IsingTopRatio.topIndex_max`) and that it is
positive. Mathlib has no eigenvalue-versus-Frobenius-norm bound either — probed, zero hits.

`SpectralEntryRatio.sum_sq_eigenvalues` makes `∑ λ²` the sum of the squared entries, and that one
identity sandwiches the top eigenvalue from both sides at once:

> `top_le_sqrt_frobenius` — `λ_top ≤ ‖A‖_F`, because one square is at most their sum.
>
> `sqrt_frobenius_le_sqrt_card_mul_top` — `‖A‖_F ≤ √N · λ_top`, because each of the `N` squares is
> at most the largest.

The second needs `|λ_j| ≤ λ_top` for every `j` — which is **not** automatic; it is Perron's, and
`abs_le_top_of_all` derives it here from `PerronGap.abs_le_top_of_eigenvector` for a matrix with
non-negative entries.

## The weakness, stated first because it is the honest headline

The two bounds differ by a factor of `√N`. On the Ising strip `N = 2ⁿ⁺¹`, so as a bound on the
free energy per ROW — which is `log λ_top` and is itself of order `n` — the window is
`½ log N = ½(n+1) log 2`, **the same order as the quantity being bounded**. Per SITE the window is
`½ log 2 ≈ 0.347`, a constant.

So this is a bound of the crude kind, and it is worth having only because there was none:
* it is the **first** two-sided bound on `λ_top` in this estate, hence the first on a free energy;
* it is **general** — every finite Hermitian matrix with non-negative entries — and computable,
  since `‖A‖_F²` is a sum of entries rather than a spectral quantity;
* and it **does not touch** `W4`'s open item, which is about `n → ∞` at fixed `β`. A window that
  is `Θ(n)` on a quantity that is `Θ(n)` says nothing about that limit, and this file claims
  nothing about it.

`PerronBound`'s row-sum bound is the estate's other `λ_top` estimate and is an upper bound only;
the lower half here is what is new, and the lower half is the one a free energy needs.
-/

namespace FrobeniusTopBound

open Finset Matrix RayleighMatrix SpectralEntryRatio

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-! ## 1. Perron's bound, applied to every eigenvalue at once -/

/-- **EVERY EIGENVALUE IS DOMINATED IN MODULUS BY THE TOP ONE**, for a Hermitian matrix with
non-negative entries. `PerronGap.abs_le_top_of_eigenvector` states this for an eigenvalue given
with an eigenvector; the eigenbasis supplies one for each. -/
theorem abs_le_top_of_all (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀) (j : ι) :
    |hA.eigenvalues j| ≤ hA.eigenvalues p₀ := by
  haveI : Nonempty ι := ⟨p₀⟩
  exact PerronGap.abs_le_top_of_eigenvector hA hpos htop
    (RayleighMatrix.mv_eigenvectorBasis hA j)
    (PerronGap.eigenvectorBasis_ne_zero hA j)

/-! ## 2. The upper bound -/

/-- **`λ_top² ≤ ‖A‖_F²`** — one square is at most the sum of all of them. -/
theorem sq_top_le_frobenius (hA : A.IsHermitian) (p₀ : ι) :
    (hA.eigenvalues p₀) ^ 2 ≤ ∑ i, ∑ j, (A i j) ^ 2 := by
  rw [← sum_sq_eigenvalues hA]
  exact Finset.single_le_sum (f := fun j => (hA.eigenvalues j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ p₀)

/-- **`λ_top ≤ ‖A‖_F`**, given that the top eigenvalue is not negative. -/
theorem top_le_sqrt_frobenius (hA : A.IsHermitian) {p₀ : ι}
    (hnn : 0 ≤ hA.eigenvalues p₀) :
    hA.eigenvalues p₀ ≤ Real.sqrt (∑ i, ∑ j, (A i j) ^ 2) := by
  have h := sq_top_le_frobenius hA p₀
  calc hA.eigenvalues p₀ = Real.sqrt ((hA.eigenvalues p₀) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt (∑ i, ∑ j, (A i j) ^ 2) := Real.sqrt_le_sqrt h

/-! ## 3. The lower bound, which is the half that is new -/

/-- **`‖A‖_F² ≤ N · λ_top²`** — each of the `N` squared eigenvalues is at most the largest, and
Perron makes the largest in modulus the top one. -/
theorem frobenius_le_card_mul_sq_top (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀) :
    ∑ i, ∑ j, (A i j) ^ 2 ≤ (Fintype.card ι : ℝ) * (hA.eigenvalues p₀) ^ 2 := by
  rw [← sum_sq_eigenvalues hA]
  have hbound : ∀ j ∈ (univ : Finset ι),
      (hA.eigenvalues j) ^ 2 ≤ (hA.eigenvalues p₀) ^ 2 := by
    intro j _
    have habs := abs_le_top_of_all hA hpos htop j
    nlinarith [abs_nonneg (hA.eigenvalues j), sq_abs (hA.eigenvalues j)]
  calc ∑ j, (hA.eigenvalues j) ^ 2 ≤ ∑ _j : ι, (hA.eigenvalues p₀) ^ 2 :=
        Finset.sum_le_sum hbound
    _ = (Fintype.card ι : ℝ) * (hA.eigenvalues p₀) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ]; ring

/-- **`‖A‖_F ≤ √N · λ_top`.** -/
theorem sqrt_frobenius_le_sqrt_card_mul_top (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀)
    (hnn : 0 ≤ hA.eigenvalues p₀) :
    Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)
      ≤ Real.sqrt (Fintype.card ι : ℝ) * hA.eigenvalues p₀ := by
  have h := frobenius_le_card_mul_sq_top hA hpos htop
  calc Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)
      ≤ Real.sqrt ((Fintype.card ι : ℝ) * (hA.eigenvalues p₀) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (Fintype.card ι : ℝ) * hA.eigenvalues p₀ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hnn]

/-! ## 4. The sandwich -/

/-- **THE TOP EIGENVALUE, BETWEEN TWO SUMS OF ENTRIES.**
`‖A‖_F / √N ≤ λ_top ≤ ‖A‖_F`, for every finite Hermitian matrix with non-negative entries and a
non-negative top eigenvalue. **The two ends differ by a factor of `√N`**, which is the whole
weakness and is stated in this file's header rather than left for a reader to notice. -/
theorem top_sandwich (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀)
    (hnn : 0 ≤ hA.eigenvalues p₀) (hne : Nonempty ι) :
    Real.sqrt (∑ i, ∑ j, (A i j) ^ 2) / Real.sqrt (Fintype.card ι : ℝ)
        ≤ hA.eigenvalues p₀ ∧
      hA.eigenvalues p₀ ≤ Real.sqrt (∑ i, ∑ j, (A i j) ^ 2) := by
  haveI := hne
  refine ⟨?_, top_le_sqrt_frobenius hA hnn⟩
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr hcard
  rw [div_le_iff₀ hsq, mul_comm]
  exact sqrt_frobenius_le_sqrt_card_mul_top hA hpos htop hnn

/-- **AND SO THE FREE ENERGY IS PINNED WITHIN `½ log N`.** Taking logarithms of the sandwich:
`log ‖A‖_F − ½ log N ≤ log λ_top ≤ log ‖A‖_F`.

For the Ising strip `N = 2ⁿ⁺¹`, so per ROW the window is `½(n+1) log 2` — of the same order as
`log λ_top` itself — and per SITE it is the constant `½ log 2`. **A crude bound, and the first
one.** -/
theorem log_top_sandwich (hA : A.IsHermitian) (hpos : ∀ i j, 0 ≤ A i j)
    {p₀ : ι} (htop : ∀ j, hA.eigenvalues j ≤ hA.eigenvalues p₀)
    (hp : 0 < hA.eigenvalues p₀) (hne : Nonempty ι) :
    Real.log (Real.sqrt (∑ i, ∑ j, (A i j) ^ 2))
        - Real.log (Real.sqrt (Fintype.card ι : ℝ))
        ≤ Real.log (hA.eigenvalues p₀) ∧
      Real.log (hA.eigenvalues p₀) ≤ Real.log (Real.sqrt (∑ i, ∑ j, (A i j) ^ 2)) := by
  haveI := hne
  obtain ⟨hlo, hhi⟩ := top_sandwich hA hpos htop hp.le hne
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsq : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr hcard
  have hfro : 0 < ∑ i, ∑ j, (A i j) ^ 2 :=
    lt_of_lt_of_le (pow_pos hp 2) (sq_top_le_frobenius hA p₀)
  have hfs : 0 < Real.sqrt (∑ i, ∑ j, (A i j) ^ 2) := Real.sqrt_pos.mpr hfro
  refine ⟨?_, Real.log_le_log hp hhi⟩
  rw [← Real.log_div (ne_of_gt hfs) (ne_of_gt hsq)]
  exact Real.log_le_log (div_pos hfs hsq) hlo

end FrobeniusTopBound
