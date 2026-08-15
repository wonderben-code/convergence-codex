import LovelockSectionalOrthogonal

/-!
# Orthonormal pairs are enough — and now the residual gap is *only* a statement about matrices

`LovelockSectionalOrthogonal` cut the sectional theorem's hypothesis from all pairs to
**orthogonal** pairs, and its header said what remained: *"every orthonormal pair in `Fin n → ℝ` is
a pair of rows of some orthogonal matrix, plus the scaling that turns an orthogonal pair into an
orthonormal one."* **This file does the scaling.** What is left is the matrix statement, with
nothing else attached to it.

## What is proved

* `mult_smul_two`, `mult_smul_three` — homogeneity in the inner slots, completing the four;
* **`sec_smul`** — `sec Z (λx) (μy) = λ²μ²·sec Z x y`;
* `dotp_nonneg`, `dotp_smul_left`, `dotp_smul_right`, **`dotp_normalise`** — dividing a non-null
  vector by `√⟨x,x⟩` makes it a unit vector, by `Real.mul_self_sqrt`;
* **`sec_eq_zero_of_orthonormal`** — **vanishing on ORTHONORMAL pairs forces vanishing on ALL
  pairs.** Chained through `sec_eq_zero_of_orthogonal`: an orthogonal pair with either vector null
  has that vector zero and the entry vanishes outright; otherwise normalise both and the entry
  scales back by `⟨u,u⟩⟨v,v⟩ > 0`;
* **`eq_zero_of_sec_orthonormal`** — the sectional theorem on the weakest hypothesis the elementary
  argument can reach.

## The residual gap, in one sentence

> **Every orthonormal pair in `Fin n → ℝ` is a pair of rows of some orthogonal matrix.**

That is all that stands between `LovelockWitnessPairing.eq_zero_of_ip_orbit` and its hypothesis, and
it mentions neither curvature nor equivariance. Mathlib's `OrthonormalBasis` and
`Orthonormal.exists_orthonormalBasis_extension` are the obvious source; two Householder reflections
are the obvious hand construction. **Neither is attempted here and neither is asserted to be hard**
— `ERRATUM 175` is about the habit of ruling on unattempted work, and the sentence above is written
to be picked up rather than ruled on.

**`KillsWeyl` at `n ≥ 4` does not follow, the estate has no equivariant `T` anywhere in this file,
and the watchlist item does not move.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockSectionalUnit

open AlgebraicCurvature LovelockSectional LovelockSectionalOrthogonal Finset

variable {n : ℕ}

theorem mult_smul_two (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (lam : ℝ) (x y z w : Fin n → ℝ) :
    mult Z x (fun t => lam * y t) z w = lam * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

theorem mult_smul_three (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (lam : ℝ) (x y z w : Fin n → ℝ) :
    mult Z x y (fun t => lam * z t) w = lam * mult Z x y z w := by
  simp only [mult, Finset.mul_sum]
  exact Finset.sum_congr rfl fun p _ => by ring

/-- **THE SECTIONAL ENTRY IS BIQUADRATIC.** -/
theorem sec_smul (Z : Fin n → Fin n → Fin n → Fin n → ℝ) (lam mu : ℝ) (x y : Fin n → ℝ) :
    sec Z (fun t => lam * x t) (fun t => mu * y t) = lam ^ 2 * mu ^ 2 * sec Z x y := by
  simp only [sec]
  rw [mult_smul_one, mult_smul_two, mult_smul_three, mult_smul_four]
  ring

theorem dotp_nonneg (x : Fin n → ℝ) : 0 ≤ dotp x x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem dotp_smul_left (lam : ℝ) (x y : Fin n → ℝ) :
    dotp (fun t => lam * x t) y = lam * dotp x y := by
  simp only [dotp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem dotp_smul_right (lam : ℝ) (x y : Fin n → ℝ) :
    dotp x (fun t => lam * y t) = lam * dotp x y := by
  simp only [dotp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **NORMALISING A NON-NULL VECTOR**, by `Real.mul_self_sqrt`. -/
theorem dotp_normalise {x : Fin n → ℝ} (hx : dotp x x ≠ 0) :
    dotp (fun t => (Real.sqrt (dotp x x))⁻¹ * x t) (fun t => (Real.sqrt (dotp x x))⁻¹ * x t)
      = 1 := by
  have hpos : 0 < dotp x x := lt_of_le_of_ne (dotp_nonneg x) (Ne.symm hx)
  have hr : Real.sqrt (dotp x x) * Real.sqrt (dotp x x) = dotp x x :=
    Real.mul_self_sqrt (le_of_lt hpos)
  have hrne : Real.sqrt (dotp x x) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  rw [dotp_smul_left, dotp_smul_right]
  field_simp
  linarith [hr]

/-- **ORTHONORMAL PAIRS ARE ENOUGH.** Null vectors are zero and give nothing; everything else
normalises, and `sec_smul` carries the value back. -/
theorem sec_eq_zero_of_orthonormal {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (h : ∀ x y : Fin n → ℝ, dotp x x = 1 → dotp y y = 1 → dotp x y = 0 → sec Z x y = 0)
    (x y : Fin n → ℝ) : sec Z x y = 0 := by
  refine sec_eq_zero_of_orthogonal hZ (fun u v huv => ?_) x y
  by_cases hu : dotp u u = 0
  · have hfun : u = fun _ => (0 : ℝ) := funext fun t => dotp_self_eq_zero hu t
    rw [hfun]
    have := mult_self_left hZ (fun _ => (0 : ℝ)) v v
    simp only [sec, mult]
    exact Finset.sum_eq_zero fun p _ => by ring
  · by_cases hv : dotp v v = 0
    · have hfun : v = fun _ => (0 : ℝ) := funext fun t => dotp_self_eq_zero hv t
      rw [hfun, sec_zero_right]
    · set r := Real.sqrt (dotp u u) with hrdef
      set s := Real.sqrt (dotp v v) with hsdef
      have hrne : r ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (dotp_nonneg u) (Ne.symm hu))
      have hsne : s ≠ 0 := Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (dotp_nonneg v) (Ne.symm hv))
      have hun : dotp (fun t => r⁻¹ * u t) (fun t => r⁻¹ * u t) = 1 := dotp_normalise hu
      have hvn : dotp (fun t => s⁻¹ * v t) (fun t => s⁻¹ * v t) = 1 := dotp_normalise hv
      have hperp : dotp (fun t => r⁻¹ * u t) (fun t => s⁻¹ * v t) = 0 := by
        rw [dotp_smul_left, dotp_smul_right, huv, mul_zero, mul_zero]
      have hkey := h _ _ hun hvn hperp
      have hback : sec Z u v = r ^ 2 * s ^ 2 *
          sec Z (fun t => r⁻¹ * u t) (fun t => s⁻¹ * v t) := by
        rw [← sec_smul]
        congr 1 <;> funext t <;> field_simp
      rw [hback, hkey, mul_zero]

/-- **THE SECTIONAL THEOREM ON THE WEAKEST HYPOTHESIS THE ELEMENTARY ARGUMENT REACHES.** Read the
header for the one statement that is left. -/
theorem eq_zero_of_sec_orthonormal {Z : Fin n → Fin n → Fin n → Fin n → ℝ} (hZ : IsAlgCurv Z)
    (h : ∀ x y : Fin n → ℝ, dotp x x = 1 → dotp y y = 1 → dotp x y = 0 → sec Z x y = 0)
    (a b c d : Fin n) : Z a b c d = 0 :=
  eq_zero_of_sec hZ (sec_eq_zero_of_orthonormal hZ h) a b c d

end LovelockSectionalUnit
