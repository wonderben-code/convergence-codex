import Mathlib

/-!
# R15 and R14 · Real Yukawas carry no CP phase; an equal-magnitude bidoublet vacuum ties up to down

From the v3 work list of *The Refined Gaps* v2 (DOI 10.5281/zenodo.23724193, §A8).

**R15 (where the three generations live).** Under L14's quaternion reading, the generation space
is Im ℍ ⊗ ℂ with the real structure of Im ℍ: a basis (i, j, k) with no intrinsic phase, so the Yukawa
matrices are real in that basis. CP violation in quark mixing is measured by the Jarlskog invariant
J. Following Jarlskog (1985), det [H_u, H_d] = 2i·J·Π(mass-squared differences), where
H = M Mᴴ. The theorems below show that real mass matrices give det [H_u, H_d] = 0, and hence J = 0.
The relation between det [H_u, H_d] and J is cited, not proved here. Since the measured J is about
3 × 10⁻⁵, the quaternion reading needs a phase from outside the Yukawas.

**R14 (the Higgs cells).** The Tree's Higgs is the Pati–Salam bidoublet Φ ~ (1,2,2), with
⟨Φ⟩ = diag(κ₁, κ₂). With SU(2)_R-symmetric Yukawas Y, Ỹ, the mass matrices are
M_u = κ₁Y + κ̄₂Ỹ and M_d = κ₂Y + κ̄₁Ỹ. Read as a two-qubit ket, ⟨Φ⟩ is maximally entangled
exactly when |κ₁| = |κ₂|. In that case M_d = u·M_u with |u| = 1, so M_d M_dᴴ = M_u M_uᴴ: up-type and
down-type quarks would have the same masses. The measured m_t/m_b ≈ 60 rules this out.

Genuine Mathlib proofs; no `sorry`, no `native_decide`, no new axioms.
-/

open Matrix

namespace ChainTheory.R15

/-- In odd dimension, the commutator of two symmetric matrices over a field of characteristic
zero has determinant zero. (It is antisymmetric, and an odd antisymmetric matrix is singular.) -/
theorem det_commutator_of_symm {K : Type*} [Field K] [CharZero K] {n : ℕ} (hn : Odd n)
    {A B : Matrix (Fin n) (Fin n) K} (hA : Aᵀ = A) (hB : Bᵀ = B) :
    (A * B - B * A).det = 0 := by
  set C := A * B - B * A with hC
  have hCt : Cᵀ = -C := by
    rw [hC, transpose_sub, transpose_mul, transpose_mul, hA, hB, neg_sub]
  have h1 : C.det = -C.det := by
    calc C.det = Cᵀ.det := (det_transpose C).symm
      _ = (-C).det := by rw [hCt]
      _ = (-1) ^ n * C.det := by rw [det_neg, Fintype.card_fin]
      _ = -C.det := by rw [hn.neg_one_pow, neg_one_mul]
  have h2 : (2 : K) * C.det = 0 := by linear_combination h1
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

/-- **R15, the theorem.** For real 3 × 3 mass matrices, with H = M Mᵀ, det [H_u, H_d] = 0: no CP
violation in quark mixing comes from real Yukawas with real vacuum values. -/
theorem no_cp_phase_from_real_masses (Mu Md : Matrix (Fin 3) (Fin 3) ℝ) :
    ((Mu * Muᵀ) * (Md * Mdᵀ) - (Md * Mdᵀ) * (Mu * Muᵀ)).det = 0 := by
  apply det_commutator_of_symm ⟨1, rfl⟩
  · rw [transpose_mul, transpose_transpose]
  · rw [transpose_mul, transpose_transpose]

end ChainTheory.R15

namespace ChainTheory.R14

/-- **R14, the theorem.** If the bidoublet's two vacuum values have equal magnitude, κ₁ = k real and
κ₂ = u·k with |u| = 1 (the maximally entangled vacuum ket), then M_d = u • M_u. -/
theorem equal_vevs_tie_down_to_up (Y Yt : Matrix (Fin 3) (Fin 3) ℂ) (k : ℝ) (u : ℂ)
    (hu : u * (starRingEnd ℂ) u = 1) :
    ((u * k) • Y + (starRingEnd ℂ) (k : ℂ) • Yt)
      = u • ((k : ℂ) • Y + (starRingEnd ℂ) (u * k) • Yt) := by
  rw [smul_add, smul_smul, smul_smul, map_mul, Complex.conj_ofReal, ← mul_assoc, hu, one_mul]

/-- … and so the up-type and down-type mass-squared matrices coincide: the same spectra. -/
theorem equal_vevs_equal_spectra (Mu : Matrix (Fin 3) (Fin 3) ℂ) (u : ℂ)
    (hu : u * (starRingEnd ℂ) u = 1) :
    (u • Mu) * (u • Mu)ᴴ = Mu * Muᴴ := by
  rw [conjTranspose_smul, smul_mul_smul_comm]
  simp [hu]

end ChainTheory.R14
