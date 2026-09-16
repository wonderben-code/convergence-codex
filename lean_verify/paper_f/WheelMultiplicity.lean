/-
  WheelMultiplicity: the rim multiplicity is at least TWO — and the independence this chain
  called its missing ingredient for eight units costs two coordinate evaluations

  WHY THIS FILE EXISTS. `PROOF_STRATEGY` §6's third question. Unit 87 exhibited the wheel's rim
  eigenvalues and left one residue, in its own words: *`Re(chi k)` and `Im(chi k)` are both
  eigenvectors at the same value and independent for `k ∉ {0, N/2}` — and proving that
  independence is exactly the step this chain has avoided in every unit.*

  **IT IS NOT A STEP. IT IS TWO COORDINATE EVALUATIONS.** Suppose `a · Re(chi) = Im(chi)`. At
  `j = 0` the character is `1`, so its real part is `1` and its imaginary part is `0`: the
  equation reads `a = 0`. That leaves `Im(chi) = 0`, and at `j = 1` the character is `zeta ^ k`,
  whose imaginary part is `sin(2πk/N)`. So the two are independent whenever that sine is
  non-zero, and **no independence theory, no orthogonality, no basis and no spectral theorem
  appears anywhere.**

  **THE SIXTH TIME IN THIS CHAIN THAT A NAMED OBSTACLE WAS REAL AND ATTACHED TO THE WRONG
  CLAIM.** `ERRATUM 617` lists four; unit 87's residue is the fifth; this is the sixth, and it
  is the one that had been repeated longest — every unit from 79 onward names *independence of
  `G`'s eigenvectors* as the thing it cannot supply, and no unit has ever needed independence
  **in general**. What was needed here is independence of **two specific vectors**, which is a
  different and much smaller question, and the difference is exactly the mistake.

  WHAT IS PROVED.

  * **`ichi`, `ichi_zero`, `chi_one`, `ichi_one`** — the imaginary part of the character, its
    vanishing at `0`, and its value `sin(2πk/N)` at `1`. `chi_one` comes off the estate's own
    `chi_add_one` at `j = 0` rather than by computing a `Fin` coercion.
  * **`adj_mulVec_ichi`, `sum_ichi_eq_zero`, `ichi_mem_rimEig`** — the imaginary part is an
    eigenvector of the rim's adjacency matrix at the same real eigenvalue, sums to zero, and so
    lands in the same zero-sum eigenspace as unit 87's real part. Both depend on unit 87's
    `zeta_add_inv`: the multiplier has to be real before parts can be taken.
  * **`ichi_ne_zero`** — non-zero when `sin(2πk/N) ≠ 0`.
  * **`rchi_ichi_linearIndependent`** — the two coordinate evaluations, as
    `LinearIndependent ℝ ![rchi, ichi]`.
  * **`two_le_finrank_rimEig`** — so the rim's zero-sum eigenspace at `2cos(2πk/N)` is at least
    **two**-dimensional, by `finrank_span_eq_card` and `Submodule.finrank_mono`.
  * **`two_le_finrank_wheel_rim`** — and therefore the wheel's eigenspace at
    `3 + 2cos(2πk/(n+3))` is too: **the first multiplicity above one anywhere in this chain.**

  WHAT IS **NOT** CLAIMED.

  * **THE MULTIPLICITY IS NOT PINNED AT TWO.** Only `2 ≤`. The true value is `2` for
    `k ∉ {0, N/2}`, and the upper bound needs the rim's zero-sum spectrum to be EXHAUSTED by
    these vectors — a dimension count over all `k` at once, which is a different unit and is not
    attempted. Unit 82's `finrank_coneEig_bounds` bounds the cone's dimension by the rim's plus
    one, so **an upper bound on the rim would transfer immediately**; there is none.
  * **NOTHING ABOUT `k = 0` OR `sin = 0`.** At `k = 0` the character is constant, so the
    zero-sum condition fails; at `sin(2πk/N) = 0` — which for `0 < k < N` means `k = N/2` and
    `N` even — the imaginary part vanishes identically and the multiplicity really is one from
    these vectors. The hypothesis is stated as the sine rather than as a condition on `k`,
    because that is what the proof uses.
  * **NO ORDERING, NO ENUMERATION, NO CHARACTERISTIC POLYNOMIAL**, and nothing about Mathlib's
    `IsHermitian.eigenvalues` indexing — unchanged from every unit of this chain.
  * **NOTHING ABOUT THE CASCADE, THE SPINE OR ANY WALL.**

  Lean 4, pinned Mathlib. 0 sorry, no new axioms.
-/

import WheelSpectrum

namespace WheelMultiplicity

open SimpleGraph LaplacianSignless Matrix
open CycleLaplacianSpectrum SignlessCycleSpectrum
open ConeSignlessSpectrum ConeSignlessExhaustion ConeMultiplicity ConeMultiplicityExact
open WheelSpectrum

/-! ## The imaginary part of the character -/

section Imag

variable (n : ℕ) (k : Fin (n + 3))

/-- The imaginary part of the character — unit 87 took the real part. -/
noncomputable def ichi : Fin (n + 3) → ℝ := fun j => (chi (n + 3) k j).im

theorem ichi_zero : ichi n k 0 = 0 := by
  simp [ichi, chi]

/-- The character at `1` is `zeta ^ k`, off the estate's `chi_add_one` at `j = 0` rather than
by computing a `Fin` coercion. -/
theorem chi_one : chi (n + 3) k 1 = zeta (n + 3) ^ (k : ℕ) := by
  have h := chi_add_one n k 0
  rw [zero_add] at h
  rw [h]
  simp [chi]

theorem ichi_one : ichi n k 1 = Real.sin (2 * Real.pi * (k : ℕ) / (n + 3)) := by
  rw [ichi, chi_one, zeta_pow_eq_exp, Complex.exp_ofReal_mul_I_im]

/-- **THE IMAGINARY PART IS AN EIGENVECTOR TOO**, at the same real eigenvalue. As with unit 87's
real part this works only because `zeta_add_inv` made the multiplier real. -/
theorem adj_mulVec_ichi :
    (cycleGraph (n + 3)).adjMatrix ℝ *ᵥ ichi n k
      = (2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3))) • ichi n k := by
  funext j
  have h := congrFun (adj_mulVec_chi n k) j
  rw [adjMatrix_mulVec_apply, zeta_add_inv] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [adjMatrix_mulVec_apply]
  simp only [ichi, Pi.smul_apply, smul_eq_mul]
  rw [← Complex.im_sum, h, Complex.im_ofReal_mul]

theorem sum_ichi_eq_zero (hk : k ≠ 0) : ∑ j, ichi n k j = 0 := by
  simp only [ichi]
  rw [← Complex.im_sum, sum_chi_eq_zero n k hk, Complex.zero_im]

theorem ichi_mem_rimEig (hk : k ≠ 0) :
    ichi n k ∈ rimEig (cycleGraph (n + 3))
      (2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3))) :=
  (mem_rimEig _).2 ⟨adj_mulVec_ichi n k, sum_ichi_eq_zero n k hk⟩

theorem ichi_ne_zero (hs : Real.sin (2 * Real.pi * (k : ℕ) / (n + 3)) ≠ 0) :
    ichi n k ≠ 0 := by
  intro hc
  have h1 := congrFun hc 1
  rw [ichi_one] at h1
  exact hs h1

end Imag

/-! ## The two coordinate evaluations -/

section Independent

variable (n : ℕ) (k : Fin (n + 3))

/-- **THE WHOLE OF THE INDEPENDENCE.** At `j = 0` the real part is `1` and the imaginary part is
`0`, which forces the coefficient; what is left is `Im(chi) = 0`, and `ichi_ne_zero` refuses it.
No independence theory, no orthogonality, no basis. -/
theorem rchi_ichi_linearIndependent
    (hs : Real.sin (2 * Real.pi * (k : ℕ) / (n + 3)) ≠ 0) :
    LinearIndependent ℝ ![rchi n k, ichi n k] := by
  refine (LinearIndependent.pair_iff' (rchi_ne_zero n k)).2 ?_
  intro a hc
  have h0 := congrFun hc 0
  rw [Pi.smul_apply, smul_eq_mul, rchi_zero, mul_one, ichi_zero] at h0
  rw [h0, zero_smul] at hc
  exact ichi_ne_zero n k hs hc.symm

/-- **SO THE RIM'S ZERO-SUM EIGENSPACE IS AT LEAST A PLANE.** -/
theorem two_le_finrank_rimEig (hk : k ≠ 0)
    (hs : Real.sin (2 * Real.pi * (k : ℕ) / (n + 3)) ≠ 0) :
    2 ≤ Module.finrank ℝ (rimEig (cycleGraph (n + 3))
      (2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)))) := by
  have hli := rchi_ichi_linearIndependent n k hs
  have hspan : Submodule.span ℝ (Set.range ![rchi n k, ichi n k])
      ≤ rimEig (cycleGraph (n + 3))
        (2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3))) := by
    rw [Submodule.span_le]
    intro v hv
    obtain ⟨i, hi⟩ := hv
    fin_cases i
    · rw [← hi]; exact rchi_mem_rimEig n k hk
    · rw [← hi]; exact ichi_mem_rimEig n k hk
  have hcard : Module.finrank ℝ (Submodule.span ℝ (Set.range ![rchi n k, ichi n k])) = 2 := by
    rw [finrank_span_eq_card hli]
    simp
  calc 2 = Module.finrank ℝ (Submodule.span ℝ (Set.range ![rchi n k, ichi n k])) := hcard.symm
    _ ≤ _ := Submodule.finrank_mono hspan

/-- **AND SO IS THE WHEEL'S**, at `3 + 2cos(2πk/(n+3))` — the first multiplicity above one
anywhere in this chain. -/
theorem two_le_finrank_wheel_rim (hk : k ≠ 0)
    (hs : Real.sin (2 * Real.pi * (k : ℕ) / (n + 3)) ≠ 0) :
    2 ≤ Module.finrank ℝ (coneEig (cycleGraph (n + 3))
      (3 + 2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)))) := by
  have hb := finrank_coneEig_bounds (cycleGraph (n + 3)) (cycle_reg n)
    (3 + 2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)))
  have hr := two_le_finrank_rimEig n k hk hs
  have hshift : (3 : ℝ) + 2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3))
      - ((2 : ℕ) : ℝ) - 1 = 2 * Real.cos (2 * Real.pi * (k : ℕ) / (n + 3)) := by
    push_cast
    ring
  rw [hshift] at hb
  omega

end Independent

end WheelMultiplicity
