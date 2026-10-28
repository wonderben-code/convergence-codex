import Mathlib

/-!
# Q5 · Are Chain Theory's three attach sites the Tree's three imaginary quaternions?

The Tree's L14 (POSTULATE): the three generations are the three imaginary quaternions i, j, k
inside M₂(ℂ). Chain Theory 197.4: "the attach sites are a basis of a generation space of
dimension three", the three qutrit corners of the closed core triangle, carried cyclically by
the shift (197.2), with the mixing the order-three Fourier matrix (166.1).

Chain Theory's own derivation of Theorem 2.9 says where each structure lives: "at a qubit end
the commutator phase of two reads is a sign and their product one further traceless operator
fixed under every matching, while a qutrit end carries a cube root." The quaternion triple is the
qubit's: two anticommuting reads and their product.

This file proves the dichotomy and what the two triples share.

* **Theorem A (`twist_pow_eq_one`).** If invertible A, B on an n-dimensional space satisfy
  AB = c·BA, then cⁿ = 1. The commutator phase at a d-dimensional end is a d-th root of unity:
  a sign at a qubit, a cube root at a qutrit. (A second proof of the clause above.)
* **Theorem B (`no_anticommuting_pair_of_odd`).** In odd dimension, no two invertible operators
  anticommute. So on Chain Theory's three-dimensional generation space the quaternion twist
  c = −1 is impossible, even "up to a phase" for the squares.
* **Theorem C (`no_quaternion_action_of_odd`).** There is no unital ℝ-algebra map ℍ → Mₙ(ℂ) for
  odd n; in particular none into M₃(ℂ). The three generations of 197.4 cannot be i, j, k as
  operators on the generation space.
* **What is shared (`cycle_is_inner`, `no_orientation_reversing_swap`).** The cycle
  i ↦ j ↦ k ↦ i is an automorphism of ℍ (conjugation by u = (1 + i + j + k)/2), so the Tree's
  triple carries Chain Theory's cyclic Z₃. Swapping two units while fixing the third is not an
  automorphism (ji = −k): the quaternion triple is *oriented*, with symmetry Z₃ rather than S₃,
  like a triangle carried by a directed shift.

Verdict, recorded in `docs/chain-theory/09_results_second_pass.md`: two different threes (a qubit's
three traceless directions against a qutrit triangle's three sites) sharing one structure, the
oriented cyclic Z₃.

Genuine Mathlib proofs; no `sorry`, no `native_decide`, no new axioms.
-/

open Matrix Quaternion

namespace ChainTheory.Q5

variable {K : Type*} [Field K]

/-- **Theorem A (the commutator phase is an n-th root of unity).** -/
theorem twist_pow_eq_one {n : ℕ} {A B : Matrix (Fin n) (Fin n) K} {c : K}
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (h : A * B = c • (B * A)) : c ^ n = 1 := by
  have hd := congrArg Matrix.det h
  rw [det_smul, det_mul, det_mul, Fintype.card_fin] at hd
  have hne : A.det * B.det ≠ 0 := mul_ne_zero hA hB
  apply mul_right_cancel₀ hne
  rw [mul_comm B.det A.det] at hd
  rw [one_mul]
  exact hd.symm

/-- **Theorem B (no anticommuting pair in odd dimension).** -/
theorem no_anticommuting_pair_of_odd [CharZero K] {n : ℕ} (hn : Odd n)
    {A B : Matrix (Fin n) (Fin n) K} (hA : A.det ≠ 0) (hB : B.det ≠ 0) :
    A * B ≠ -(B * A) := by
  intro h
  have h' : A * B = (-1 : K) • (B * A) := by rw [h, neg_one_smul]
  have := twist_pow_eq_one hA hB h'
  rw [hn.neg_one_pow] at this
  norm_num at this

/-- The three imaginary units of ℍ (Mathlib's `ℍ[ℝ]`, with i² = j² = −1). -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem qi_mul_qi : qi * qi = -1 := by ext <;> simp [qi]
theorem qj_mul_qj : qj * qj = -1 := by ext <;> simp [qj]
theorem qk_mul_qk : qk * qk = -1 := by ext <;> simp [qk]
theorem qi_mul_qj : qi * qj = qk := by ext <;> simp [qi, qj, qk]
theorem qj_mul_qi : qj * qi = -qk := by ext <;> simp [qi, qj, qk]
/-- The cyclic product around the triple is −1 … -/
theorem qi_qj_qk : qi * qj * qk = -1 := by ext <;> simp [qi, qj, qk]
/-- … and +1 the other way round: the triple is oriented. -/
theorem qk_qj_qi : qk * qj * qi = 1 := by ext <;> simp [qi, qj, qk]

/-- **Theorem C (no quaternion action in odd dimension).** There is no unital ℝ-algebra map
ℍ → Mₙ(ℂ) for odd n. -/
theorem no_quaternion_action_of_odd {n : ℕ} (hn : Odd n) :
    IsEmpty (ℍ[ℝ] →ₐ[ℝ] Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨fun φ => ?_⟩
  -- A = φ i and B = φ j are invertible (A·(−A) = 1) and anticommute
  have hA : (φ qi).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_left_inverse (B := φ (-qi))
    have h2 : -qi * qi = 1 := by rw [neg_mul, qi_mul_qi, neg_neg]
    rw [← map_mul, h2, map_one]
  have hB : (φ qj).det ≠ 0 := by
    apply Matrix.det_ne_zero_of_left_inverse (B := φ (-qj))
    have h2 : -qj * qj = 1 := by rw [neg_mul, qj_mul_qj, neg_neg]
    rw [← map_mul, h2, map_one]
  apply no_anticommuting_pair_of_odd hn hA hB
  rw [← map_mul, ← map_mul, qi_mul_qj, qj_mul_qi, map_neg]
  exact (neg_neg _).symm

/-- In particular, none into M₃(ℂ), the algebra of Chain Theory's generation space. -/
theorem no_quaternion_action_on_generation_space :
    IsEmpty (ℍ[ℝ] →ₐ[ℝ] Matrix (Fin 3) (Fin 3) ℂ) :=
  no_quaternion_action_of_odd ⟨1, rfl⟩

/-- The cycling element u = (1 + i + j + k)/2. -/
noncomputable def qu : ℍ[ℝ] := ⟨1 / 2, 1 / 2, 1 / 2, 1 / 2⟩

theorem qu_ne_zero : qu ≠ 0 := by
  intro h
  have := congrArg QuaternionAlgebra.re h
  simp [qu] at this

/-- **What is shared.** Conjugation by u cycles the triple, i ↦ j ↦ k ↦ i: the cyclic Z₃ of the
triangle is an (inner) automorphism of ℍ. -/
theorem cycle_is_inner :
    qu * qi = qj * qu ∧ qu * qj = qk * qu ∧ qu * qk = qi * qu := by
  refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp [qu, qi, qj, qk]

/-- **Orientation.** No algebra automorphism of ℍ swaps i and j while fixing k. -/
theorem no_orientation_reversing_swap :
    ¬ ∃ φ : ℍ[ℝ] →ₐ[ℝ] ℍ[ℝ], φ qi = qj ∧ φ qj = qi ∧ φ qk = qk := by
  rintro ⟨φ, hi, hj, hk⟩
  have h1 : φ qk = -qk := by
    calc φ qk = φ (qi * qj) := by rw [qi_mul_qj]
      _ = qj * qi := by rw [map_mul, hi, hj]
      _ = -qk := qj_mul_qi
  rw [hk] at h1
  have := congrArg QuaternionAlgebra.imK h1
  simp [qk] at this
  norm_num at this

end ChainTheory.Q5
