import CycleGreenFormula
import LaplacianDegreeBound

/-!
# The odd cycle settles it: the withdrawn claim is not merely unchecked, it is false

`LaplacianDegreeBound` proved `massive ≼ (2Δ + m²)·1` and withdrew, before committing, a claim
that the matching lower bound on `green` is attained *"on the graphs where every degree is `Δ`"* —
withdrawn because it had not been checked. `LaplacianBoundSharp` then proved it **is** attained on
every **even** cycle at `Δ = 2`, and said plainly what it did not settle:

> **The odd cycle is 2-regular and is not covered** — the alternating vector does not exist there,
> which is exactly why `alt_add_one` needs the length even — and nothing here says whether the
> bound is attained on it.

**It is not.** `odd_cycle_lt` and `odd_cycle_green_not_attained` give, on every odd cycle of length
at least five, a constant strictly below `4 + m²` that already dominates — so the withdrawn claim
is **refuted**, not merely unproven, and the two cycles together settle the question for that
family in both directions.

## The step this needed, and where it came from

Refuting attainment needs the **opposite** direction from exhibiting it. `LaplacianBoundSharp`
needed only one eigenvector above a candidate constant; ruling attainment out needs *every*
eigenvalue below one, which needs the eigenvalue list to be **complete**. That was the blocker this
item was opened with, and `CycleGreenFormula` removed it one unit ago by putting every coordinate
vector in the characters' span.

**And the completeness is used without Parseval.** The route here is
`apply_eq_of_mulVec_chi` — a generalisation of `CycleGreenFormula.green_cycle_apply` to **any**
matrix the characters diagonalise, with the propagator case instantiated below it (`ERRATUM 201`) —
followed by exhibiting the difference `c·1 − massive` as `B·Bᴴ` for
`B x k = √(dₖ/N)·χ_k(x)`. Positive-semidefiniteness is then Mathlib's
`posSemidef_self_mul_conjTranspose` and no quadratic form is expanded.

## And the odd case is parity, not a range argument

`cos(2πk/N) = −1` forces `N·(1 + 2j) = 2k` for an integer `j` (`Real.cos_eq_neg_one_iff`, then
`field_simp` clears `π` and the denominator). With `N` odd, the left side is **odd** and the right
side is **even**. That is the whole argument: `k` never enters it, and no bound on `k` is used.

## What is proved

* `zeta_conj`, `chi_conj` — conjugation inverts the characters;
* **`apply_eq_of_mulVec_chi`** — a matrix the characters diagonalise is its own Fourier sum, at
  every `N`, for any scalars;
* `gapMat`, `gapMat_mul_conjTranspose`, **`posSemidef_of_mulVec_chi`** — non-negative eigenvalues
  make it positive semidefinite, by factorisation;
* **`massive_le_smul_one_of_eigenvalues_le`** — an eigenvalue bound on the cycle is a Loewner
  bound;
* `cos_ne_neg_one_of_odd` — the parity argument;
* **`odd_cycle_lt`**, **`odd_cycle_green_not_attained`** — so the degree bound is **not** attained
  on the odd cycle, on either side of the inversion.

## What this is NOT

> **THE STATEMENT IS NOW ALSO AVAILABLE WITHOUT THE SPECTRUM, 2026-08-29.**
> `LaplacianLoewnerConverse.massive_le_smul_one_iff_colorable` proves that any CONNECTED regular
> graph fails to attain `2Δ + m²` exactly when it is not two-colourable, using
> `Matrix.IsHermitian.eigenvectorBasis` and never inspecting it — so the odd cycle's case is an
> instance at `Δ = 2` and the odd periodic lattice follows in every dimension.
> **THIS FILE IS NOT SUPERSEDED AND THE DIFFERENCES RUN BOTH WAYS**: `odd_cycle_lt` assumes
> `m ≠ 0`, which the general theorem does not need, and delivers `0 < c`, which the general theorem
> does not prove. The explicit eigenvalue list here is also what `CycleGreenFormula` consumes, and
> nothing about it moves.

**It does not identify the constant.** `odd_cycle_lt` produces the supremum of the eigenvalue list
as a `Finset.sup'` and proves it is below `4 + m²`; **no closed form for it is given**, and none is
needed for the refutation. Whether that supremum equals `2 + m² − 2cos(π(N−1)/N)` — the value one
expects — is **not** proved here.

**It settles the cycle family and nothing wider.** The withdrawn claim quantified over all graphs
with all degrees `Δ`; what is refuted is that quantifier, by one counterexample family at `Δ = 2`.
**Nothing here says which regular graphs do attain the bound**, and the even cycles are the only
ones known to.

**`d = 1` only, `Δ = 2` only, and no measure is involved.** `OS4` does not move and no published
tag moves.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace CycleSpectralBound

open Matrix GraphLaplacian SimpleGraph CycleLaplacianSpectrum CycleGreenFormula
open scoped MatrixOrder ComplexOrder

/-! ## 1. Conjugation on the characters -/

theorem zeta_conj (N : ℕ) : (starRingEnd ℂ) (zeta N) = (zeta N)⁻¹ := by
  rw [zeta, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp only [map_div₀, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal,
    Complex.conj_natCast]
  ring

theorem chi_conj (N : ℕ) (k j : Fin N) :
    (starRingEnd ℂ) (chi N k j) = (chi N k j)⁻¹ := by
  rw [chi, map_pow, zeta_conj, inv_pow]

/-! ## 2. A matrix the characters diagonalise is its own Fourier sum -/

/-- **THE GENERALISATION OF `CycleGreenFormula.green_cycle_apply`**: any matrix whose action on
each character is a scalar is recovered from those scalars. -/
theorem apply_eq_of_mulVec_chi (N : ℕ) (hN : N ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ)
    (ν : Fin N → ℂ) (hA : ∀ k, A *ᵥ chi N k = ν k • chi N k) (x y : Fin N) :
    A x y = (N : ℂ)⁻¹ * ∑ k : Fin N, ν k * ((chi N k y)⁻¹ * chi N k x) := by
  have hcol : A *ᵥ (Pi.single y (1 : ℂ)) = fun z => A z y := by
    funext z
    rw [Matrix.mulVec, dotProduct]
    simp [Pi.single_apply]
  have hexp : A *ᵥ (Pi.single y (1 : ℂ))
      = A *ᵥ ((N : ℂ)⁻¹ • ∑ k : Fin N, (chi N k y)⁻¹ • chi N k) := by
    rw [single_eq_sum_chi hN y]
  rw [hcol] at hexp
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sum, hA] at hexp
  have hx := congrFun hexp x
  rw [hx]
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  ring

/-- `CycleGreenFormula.green_cycle_apply` is the instance of the lemma above at the propagator,
so the generalisation is checked against the statement it generalises. -/
example (n : ℕ) {m : ℝ} (hm : m ≠ 0) (x y : Fin (n + 3)) :
    ((green (cycleGraph (n + 3)) m x y : ℝ) : ℂ)
      = ((n + 3 : ℕ) : ℂ)⁻¹ * ∑ k : Fin (n + 3),
          (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ))⁻¹
            * ((chi (n + 3) k y)⁻¹ * chi (n + 3) k x) := by
  have h := apply_eq_of_mulVec_chi (n + 3) (by omega)
    (MatrixLoewner.cx (green (cycleGraph (n + 3)) m))
    (fun k => (((2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) : ℝ) : ℂ))⁻¹)
    (fun k => CycleLaplacianSpectrum.cx_green_mulVec_chi n hm k) x y
  simpa using h

/-! ## 3. A non-negative eigenvalue list makes the matrix positive semidefinite -/

/-- The characters as columns, each scaled by `√(dₖ/N)`. -/
noncomputable def gapMat (N : ℕ) (d : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun x k => (((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (d k) : ℝ) : ℂ) * chi N k x

theorem gapMat_mul_conjTranspose (N : ℕ) (hN : N ≠ 0) (d : Fin N → ℝ) (hd : ∀ k, 0 ≤ d k)
    (x y : Fin N) :
    (gapMat N d * (gapMat N d)ᴴ) x y
      = (N : ℂ)⁻¹ * ∑ k : Fin N, ((d k : ℝ) : ℂ) * ((chi N k y)⁻¹ * chi N k x) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsq : ((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (d k))
      * ((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (d k)) = (N : ℝ)⁻¹ * d k := by
    calc ((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (d k))
          * ((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (d k))
        = (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ))⁻¹
            * (Real.sqrt (d k) * Real.sqrt (d k)) := by
          rw [mul_inv]; ring
      _ = (N : ℝ)⁻¹ * d k := by
          rw [Real.mul_self_sqrt hNpos.le, Real.mul_self_sqrt (hd k)]
  have hkey : (((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (d k) : ℝ) : ℂ)
      * (((Real.sqrt (N : ℝ))⁻¹ * Real.sqrt (d k) : ℝ) : ℂ)
      = (N : ℂ)⁻¹ * ((d k : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, hsq]
    push_cast
    ring
  rw [Matrix.conjTranspose_apply, gapMat]
  simp only [Matrix.of_apply, ← starRingEnd_apply, map_mul, Complex.conj_ofReal, chi_conj]
  linear_combination (chi N k x * (chi N k y)⁻¹) * hkey

/-- **A MATRIX THE CHARACTERS DIAGONALISE WITH NON-NEGATIVE EIGENVALUES IS POSITIVE
SEMIDEFINITE**, by exhibiting it as `B · Bᴴ`. -/
theorem posSemidef_of_mulVec_chi (N : ℕ) (hN : N ≠ 0) (A : Matrix (Fin N) (Fin N) ℂ)
    (d : Fin N → ℝ) (hd : ∀ k, 0 ≤ d k)
    (hA : ∀ k, A *ᵥ chi N k = ((d k : ℝ) : ℂ) • chi N k) : A.PosSemidef := by
  have hEq : A = gapMat N d * (gapMat N d)ᴴ := by
    ext x y
    rw [apply_eq_of_mulVec_chi N hN A (fun k => ((d k : ℝ) : ℂ)) hA x y,
      gapMat_mul_conjTranspose N hN d hd x y]
  rw [hEq]
  exact Matrix.posSemidef_self_mul_conjTranspose _

/-! ## 4. Applied to `massive` on the cycle -/

/-- **AN EIGENVALUE BOUND IS A LOEWNER BOUND.** -/
theorem massive_le_smul_one_of_eigenvalues_le (n : ℕ) (m c : ℝ)
    (h : ∀ k : Fin (n + 3), 2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3)) ≤ c) :
    massive (cycleGraph (n + 3)) m ≤ c • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ) := by
  refine Matrix.le_iff.mpr (MatrixLoewner.posSemidef_of_cx ?_)
  have hcx : MatrixLoewner.cx (c • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ)
        - massive (cycleGraph (n + 3)) m)
      = (c : ℂ) • (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ)
        - MatrixLoewner.cx (massive (cycleGraph (n + 3)) m) := by
    ext i j
    simp only [MatrixLoewner.cx_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  rw [hcx]
  refine posSemidef_of_mulVec_chi (n + 3) (by omega) _
    (fun k => c - (2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / (n + 3))))
    (fun k => by linarith [h k]) (fun k => ?_)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    CycleLaplacianSpectrum.cx_massive_mulVec_chi n m k,
    CycleLaplacianSpectrum.eigenvalue_eq_real n m k, ← sub_smul]
  congr 1
  push_cast
  ring

/-! ## 5. The odd cycle does not attain the degree bound -/

theorem cos_ne_neg_one_of_odd {N k : ℕ} (hN : Odd N) :
    Real.cos (2 * Real.pi * (k : ℝ) / (N : ℝ)) ≠ -1 := by
  intro hc
  obtain ⟨j, hj⟩ := Real.cos_eq_neg_one_iff.mp hc
  obtain ⟨t, ht⟩ := hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have hpos : 0 < N := by omega
    positivity
  field_simp at hj
  have h2 : (N : ℝ) * (1 + 2 * (j : ℝ)) = 2 * (k : ℝ) := by linear_combination hj
  have h3 : (N : ℤ) * (1 + 2 * j) = 2 * (k : ℤ) := by exact_mod_cast h2
  have hoddN : Odd ((N : ℤ)) := by rw [Int.odd_iff]; omega
  have hoddJ : Odd (1 + 2 * j) := by rw [Int.odd_iff]; omega
  have hodd := hoddN.mul hoddJ
  rw [h3, Int.odd_iff] at hodd
  omega

/-- **THE DEGREE BOUND IS NOT ATTAINED ON THE ODD CYCLE.** -/
theorem odd_cycle_lt (M : ℕ) {m : ℝ} (hm : m ≠ 0) :
    ∃ c : ℝ, c < 4 + m ^ 2 ∧ 0 < c ∧ massive (cycleGraph (2 * M + 5)) m
      ≤ c • (1 : Matrix (Fin (2 * M + 5)) (Fin (2 * M + 5)) ℝ) := by
  classical
  have hne : (Finset.univ : Finset (Fin (2 * M + 5))).Nonempty := Finset.univ_nonempty
  have hm2 : (0 : ℝ) < m ^ 2 := lt_of_le_of_ne (sq_nonneg m) (Ne.symm (pow_ne_zero 2 hm))
  refine ⟨Finset.univ.sup' hne
    (fun k : Fin (2 * M + 5) =>
      2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / ((2 * M + 2 : ℕ) + 3))), ?_, ?_, ?_⟩
  · rw [Finset.sup'_lt_iff]
    intro k _
    have hcast : ((2 * M + 2 : ℕ) : ℝ) + 3 = ((2 * M + 5 : ℕ) : ℝ) := by push_cast; ring
    have hcos : Real.cos (2 * Real.pi * (k.val : ℝ) / ((2 * M + 5 : ℕ) : ℝ)) ≠ -1 :=
      cos_ne_neg_one_of_odd ⟨M + 2, by ring⟩
    rw [hcast]
    have hle := Real.neg_one_le_cos (2 * Real.pi * (k.val : ℝ) / ((2 * M + 5 : ℕ) : ℝ))
    have hlt : -1 < Real.cos (2 * Real.pi * (k.val : ℝ) / ((2 * M + 5 : ℕ) : ℝ)) :=
      lt_of_le_of_ne hle (Ne.symm hcos)
    linarith
  · have h0 := Finset.le_sup'
      (fun k : Fin (2 * M + 5) =>
        2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / ((2 * M + 2 : ℕ) + 3)))
      (Finset.mem_univ (0 : Fin (2 * M + 5)))
    have hc1 := Real.cos_le_one
      (2 * Real.pi * ((0 : Fin (2 * M + 5)).val : ℝ) / (((2 * M + 2 : ℕ) : ℝ) + 3))
    simp only at h0
    linarith
  · exact massive_le_smul_one_of_eigenvalues_le (2 * M + 2) m _
      (fun k => Finset.le_sup'
        (fun k : Fin (2 * M + 5) =>
          2 + m ^ 2 - 2 * Real.cos (2 * Real.pi * k.val / ((2 * M + 2 : ℕ) + 3)))
        (Finset.mem_univ k))

/-- **AND SO THE PROPAGATOR'S LOWER BOUND CAN BE RAISED THERE**, which is the side of the
statement `LaplacianDegreeBound` is about. -/
theorem odd_cycle_green_not_attained (M : ℕ) {m : ℝ} (hm : m ≠ 0) :
    ∃ c : ℝ, c < 4 + m ^ 2 ∧ 0 < c ∧
      c⁻¹ • (1 : Matrix (Fin (2 * M + 5)) (Fin (2 * M + 5)) ℝ)
        ≤ green (cycleGraph (2 * M + 5)) m := by
  obtain ⟨c, hclt, hcpos, hle⟩ := odd_cycle_lt M hm
  refine ⟨c, hclt, hcpos, ?_⟩
  have hinv := MatrixLoewner.posDef_inv_le_inv (massive_posDef _ hm) hle
  have hd : (c • (1 : Matrix (Fin (2 * M + 5)) (Fin (2 * M + 5)) ℝ))⁻¹
      = c⁻¹ • (1 : Matrix (Fin (2 * M + 5)) (Fin (2 * M + 5)) ℝ) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hcpos), one_smul]
  rwa [hd] at hinv

end CycleSpectralBound
