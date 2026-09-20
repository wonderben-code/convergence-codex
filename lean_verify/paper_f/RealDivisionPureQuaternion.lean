/-
  RealDivisionPureQuaternion.lean — the pure part AT the three algebras themselves: `ℍ` has a
  three-dimensional pure part and it IS the imaginary quaternions; `ℂ`'s is the imaginary line;
  `ℝ`'s is zero.

  SPINE L14 (three generations, POSTULATE) — the Caesar order's item 6, second line, as re-counted
  on 20 September: *"`finrank ℝ (pureSubmodule ℍ) = 3` is likewise unwritten at `ℍ` itself … one
  line from Mathlib's dimension of `ℍ`"* — hardening unit 154, 2026-09-20.

  WHY. The Frobenius chain (`RealDivisionPure*`, 1 September) proves for an ABSTRACT
  finite-dimensional real division algebra `D` that the pure part `V = {d | d² ∈ ℝ_{≤0}·1}` is a
  submodule with `1 + dim V = dim D` and `dim V ∈ {0, 1, 3}`. The L14 row's sentence *"3 generations
  = 3 imaginary quaternion directions"* names the CONCRETE `ℍ`, and no theorem in the chain said
  what its `pureSubmodule` is there (`grep -rn '\.re = 0' paper_f/RealDivision*.lean` → nothing).
  This file says it: at `ℍ[ℝ]` the pure part is exactly `{q | q.re = 0}` and has dimension 3; at
  `ℂ` it is `{z | z.re = 0}`, dimension 1; at `ℝ` it is `{0}`, dimension 0.

  WHAT IS PROVED.
  * `finrank_pure_quaternion : finrank ℝ (pureSubmodule ℍ[ℝ]) = 3`, `finrank_pure_complex … = 1`,
    `finrank_pure_real … = 0` — each one line from `RealDivisionPureSpace.finrank_eq_succ` and
    Mathlib's `Quaternion.finrank_eq_four`, `Complex.finrank_real_complex`, `Module.finrank_self`.
  * `isPure_quaternion_iff : IsPure q ↔ q.re = 0` and `mem_pureSubmodule_quaternion_iff` — the
    chain's abstract pure part, at `ℍ`, is the imaginary quaternions. Componentwise: `q² = c·1`
    forces `2·re·imI = 2·re·imJ = 2·re·imK = 0`, so a nonzero real part makes `q` real and
    `q² = re²·1 > 0`, against `c ≤ 0`; conversely `re = 0` gives `q² = −(imI² + imJ² + imK²)·1`.
  * `isPure_complex_iff : IsPure z ↔ z.re = 0`, `isPure_real_iff : IsPure r ↔ r = 0`.

  WHAT IS **NOT** PROVED, said exactly.
  * Anything about generations. `3` is the dimension of a subspace of `ℍ`; that three fermion
    generations correspond to it is L14's postulate (`DECISIONS NEEDED` 4) and is not touched.
  * No basis `{i, j, k}` of the pure part is exhibited here; the dimension is counted, not spanned
    (`RealDivisionQuaternionCase.pureQuatBasis` builds one abstractly from a normalised pair).
  * Nothing about which of `ℝ`, `ℂ`, `ℍ` the cascade selects: `RealDivisionQuaternionCase.frobenius`
    gives the trichotomy, and the selection of `ℍ` is a separate input.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import RealDivisionPureSpace

namespace RealDivisionPureQuaternion

open RealDivisionPure RealDivisionPureSpace Quaternion

/-! ## The dimension of the pure part at the three algebras -/

/-- **THE LINE THE CAESAR ORDER SAID WAS UNWRITTEN**: the pure part of `ℍ` is three-dimensional. -/
theorem finrank_pure_quaternion : Module.finrank ℝ (pureSubmodule ℍ[ℝ]) = 3 := by
  have h := (finrank_eq_succ (D := ℍ[ℝ])).trans Quaternion.finrank_eq_four
  omega

/-- The pure part of `ℂ` is a line. -/
theorem finrank_pure_complex : Module.finrank ℝ (pureSubmodule ℂ) = 1 := by
  have h := (finrank_eq_succ (D := ℂ)).trans Complex.finrank_real_complex
  omega

/-- The pure part of `ℝ` is zero. -/
theorem finrank_pure_real : Module.finrank ℝ (pureSubmodule ℝ) = 0 := by
  have h := (finrank_eq_succ (D := ℝ)).trans (Module.finrank_self ℝ)
  omega

/-! ## The pure part IS the imaginary part -/

/-- **PURE = IMAGINARY, at `ℍ`.** The chain's abstract pure part is the imaginary quaternions. -/
theorem isPure_quaternion_iff (q : ℍ[ℝ]) : IsPure q ↔ q.re = 0 := by
  constructor
  · rintro ⟨c, hc, h⟩
    have hre := congrArg (fun x : ℍ[ℝ] => x.re) h
    have hi := congrArg (fun x : ℍ[ℝ] => x.imI) h
    have hj := congrArg (fun x : ℍ[ℝ] => x.imJ) h
    have hk := congrArg (fun x : ℍ[ℝ] => x.imK) h
    simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_smul, imI_smul, imJ_smul, imK_smul,
      re_one, imI_one, imJ_one, imK_one, smul_eq_mul, mul_one, mul_zero] at hre hi hj hk
    by_contra hne
    have h2 : (2 * q.re) ≠ 0 := by
      intro h2; exact hne (by linarith)
    have hi0 : q.imI = 0 := by
      have : (2 * q.re) * q.imI = 0 := by linear_combination hi
      exact (mul_eq_zero.1 this).resolve_left h2
    have hj0 : q.imJ = 0 := by
      have : (2 * q.re) * q.imJ = 0 := by linear_combination hj
      exact (mul_eq_zero.1 this).resolve_left h2
    have hk0 : q.imK = 0 := by
      have : (2 * q.re) * q.imK = 0 := by linear_combination hk
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [hi0, hj0, hk0] at hre
    have hpos : 0 < q.re * q.re := mul_self_pos.2 hne
    nlinarith
  · intro h0
    have hnn : 0 ≤ q.imI * q.imI + q.imJ * q.imJ + q.imK * q.imK := by
      nlinarith [mul_self_nonneg q.imI, mul_self_nonneg q.imJ, mul_self_nonneg q.imK]
    refine ⟨-(q.imI * q.imI + q.imJ * q.imJ + q.imK * q.imK), by linarith, ?_⟩
    apply Quaternion.ext <;>
      simp only [re_mul, imI_mul, imJ_mul, imK_mul, re_smul, imI_smul, imJ_smul, imK_smul,
        re_one, imI_one, imJ_one, imK_one, smul_eq_mul, mul_one, mul_zero, h0] <;>
      ring

/-- The same, as membership in the bundled submodule. -/
theorem mem_pureSubmodule_quaternion_iff (q : ℍ[ℝ]) : q ∈ pureSubmodule ℍ[ℝ] ↔ q.re = 0 :=
  isPure_quaternion_iff q

/-- **PURE = IMAGINARY, at `ℂ`.** -/
theorem isPure_complex_iff (z : ℂ) : IsPure z ↔ z.re = 0 := by
  constructor
  · rintro ⟨c, hc, h⟩
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [Complex.mul_re, Complex.mul_im, Complex.smul_re, Complex.smul_im, Complex.one_re,
      Complex.one_im, smul_eq_mul, mul_one, mul_zero] at hre him
    by_contra hne
    have h2 : (2 * z.re) ≠ 0 := by
      intro h2; exact hne (by linarith)
    have him0 : z.im = 0 := by
      have : (2 * z.re) * z.im = 0 := by linear_combination him
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [him0] at hre
    have hpos : 0 < z.re * z.re := mul_self_pos.2 hne
    nlinarith
  · intro h0
    refine ⟨-(z.im * z.im), by nlinarith [mul_self_nonneg z.im], ?_⟩
    apply Complex.ext <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.smul_re, Complex.smul_im, Complex.one_re,
        Complex.one_im, smul_eq_mul, mul_one, mul_zero, h0] <;>
      ring

/-- **PURE = ZERO, at `ℝ`.** -/
theorem isPure_real_iff (r : ℝ) : IsPure r ↔ r = 0 := by
  constructor
  · rintro ⟨c, hc, h⟩
    simp only [smul_eq_mul, mul_one] at h
    exact mul_self_eq_zero.1 (le_antisymm (h ▸ hc) (mul_self_nonneg r))
  · rintro rfl
    exact isPure_zero

end RealDivisionPureQuaternion
