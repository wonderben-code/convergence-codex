/-
  HermitianSignatureEven.lean — the real quadratic form of a Hermitian twist has EVEN signature
  entries, so no ⋆-structure on `Mₙ(ℂ)` induces a Lorentzian form, and the seed's star in
  particular carries no `(1, 3)`.

  SPINE link L3 (seed realisation), rated GENUINE, and `UNLOCK_WATCHLIST` *what could select a
  SIGNATURE* — hardening unit 153 (`RE-SWEEP #71`), 2026-09-20.

  WHY. That watchlist item waits for *"the first cascade construction that carries a quadratic
  form rather than only an algebra"*. Unit 150 (`SeedStarStructure`) is such a construction: the
  seed's ⋆-structure is `X ↦ (P X P⁻¹)ᴴ` for a Hermitian unit `P`, and `P` IS a real quadratic
  form — `HermitianRealForm.realQuad P : QuadraticForm ℝ (Fin 2 → ℂ)`, `x ↦ re ⟪x, P x⟫` on the
  seed's `ℂ²` read as `ℝ⁴`. The sweep that noticed this asked the item's question of it — can that
  form be Lorentzian? — and the answer is a two-line consequence of unit 73's formula
  `signature P = (2·#{λ > 0}, 2·#{λ < 0})`, written here so the watchlist cites a declaration
  rather than an inference.

  WHAT IS PROVED.
  * `signature_fst_even`, `signature_snd_even` — for Hermitian `P` on `Mₙ(ℂ)`, both entries of
    `signature P` are even.
  * `signature_ne_of_odd`, `usignature_ne_of_odd` — the (unordered) signature is never a pair
    with an odd entry.
  * `signature_ne_lorentz`, `usignature_ne_lorentz` — in particular never `(1, 3)`, `(3, 1)` or
    `s(1, 3)`: **no Hermitian twist on any `Mₙ(ℂ)` induces a Lorentzian real form.**
  * `star_not_lorentz` — EVERY ⋆-structure on `Mₙ(ℂ)` (`n ≠ 0`) is presented by a Hermitian
    unit whose unordered signature is not `s(1, 3)`, off `StarStructureHermitian`'s
    `exists_hermitian_twist`; so no level of the cascade's tower, once identified with a matrix
    algebra, carries a Lorentzian form through its star.
  * `seed_star_not_lorentz` — `seed_star_hermitian`'s conclusion with the clause
    `usignature P ≠ s(1, 3)` added: the seed's star, transported to `M₂(ℂ)`, is definite or split
    and never Lorentzian.

  WHAT IS **NOT** PROVED, said exactly.
  * That the seed's `ℂ²` has anything to do with spacetime. The theorem is about the form a
    ⋆-structure induces on the seed's own two-dimensional complex space; that this space is
    four-dimensional over `ℝ` is a coincidence of dimension, not an identification, and none is
    made here.
  * A ⋆-structure at level `k ≥ 1` of the tower: `CascadeTowerRecursive.towerEquiv` is an
    equivalence of `ℂ`-algebras and transports none, so none is in hand there. What
    `star_not_lorentz` says is that IF one is supplied on the matrix algebra at any level, its
    form is not Lorentzian either; it does not supply one.
  * Anything about the Clifford quadratic forms of `LorentzianChosen`, which live on `ℝ⁴`
    directly and are a different object. The watchlist item's route (a) — a cascade STEP that
    carries a form — is not built, and its route (b) — that the cascade's output is
    signature-blind — is not proved in general. What is proved is the negative for the one form
    the construction carries, at level 0.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SeedStarStructure

namespace HermitianSignatureEven

open Module Matrix HermitianRealForm HermitianSignatureEigenvalues
  HermitianSignatureClassification StarStructureProductMatrix SeedStarStructure

variable {n : ℕ}

/-! ## Both signature entries are even -/

/-- The positive index of a Hermitian twist's real form is even. -/
theorem signature_fst_even (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    Even (signature P).1 := by
  rw [signature_isHermitian P hP]
  exact even_two_mul _

/-- The negative index of a Hermitian twist's real form is even. -/
theorem signature_snd_even (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    Even (signature P).2 := by
  rw [signature_isHermitian P hP]
  exact even_two_mul _

/-! ## Hence no odd entry, and in particular no Lorentzian value -/

/-- A Hermitian twist's signature is never a pair with an odd entry. -/
theorem signature_ne_of_odd (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) {a b : ℕ}
    (h : Odd a ∨ Odd b) : signature P ≠ (a, b) := by
  intro heq
  have h1 := signature_fst_even P hP
  have h2 := signature_snd_even P hP
  rw [heq] at h1 h2
  rcases h with h | h
  · exact Nat.not_even_iff_odd.2 h h1
  · exact Nat.not_even_iff_odd.2 h h2

/-- **NEVER LORENTZIAN, ORDERED.** Neither `(1, 3)` nor `(3, 1)` is the signature of a Hermitian
twist's real form, at any size `n`. -/
theorem signature_ne_lorentz (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    signature P ≠ (1, 3) ∧ signature P ≠ (3, 1) :=
  ⟨signature_ne_of_odd P hP (Or.inl odd_one), signature_ne_of_odd P hP (Or.inr odd_one)⟩

/-- The unordered signature is never a pair with an odd entry. -/
theorem usignature_ne_of_odd (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) {a b : ℕ}
    (h : Odd a ∨ Odd b) : usignature P ≠ s(a, b) := by
  intro heq
  have h1 := signature_fst_even P hP
  have h2 := signature_snd_even P hP
  rw [usignature, Sym2.eq_iff] at heq
  rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha] at h1
    rw [hb] at h2
    rcases h with h | h
    · exact Nat.not_even_iff_odd.2 h h1
    · exact Nat.not_even_iff_odd.2 h h2
  · rw [ha] at h1
    rw [hb] at h2
    rcases h with h | h
    · exact Nat.not_even_iff_odd.2 h h2
    · exact Nat.not_even_iff_odd.2 h h1

/-- **NEVER LORENTZIAN, UNORDERED.** The conjugacy invariant of a ⋆-structure presented by a
Hermitian unit is never `s(1, 3)`. -/
theorem usignature_ne_lorentz (P : Matrix (Fin n) (Fin n) ℂ) (hP : P.IsHermitian) :
    usignature P ≠ s(1, 3) :=
  usignature_ne_of_odd P hP (Or.inl odd_one)

/-! ## Every ⋆-structure on a matrix algebra, and the seed -/

/-- **NO ⋆-STRUCTURE ON `Mₙ(ℂ)` CARRIES A LORENTZIAN FORM.** Every ⋆-structure is presented by a
Hermitian unit (`StarStructureHermitian.exists_hermitian_twist`), and that unit's unordered
signature is not `s(1, 3)`. -/
theorem star_not_lorentz [NeZero n] (s : StarStructureMatrix.StarStructure n) :
    ∃ P : (Matrix (Fin n) (Fin n) ℂ)ˣ,
      (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ) ∧
      (∀ X, s.map X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
        * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ) ∧
      usignature (P : Matrix (Fin n) (Fin n) ℂ) ≠ s(1, 3) := by
  obtain ⟨P, hP, hs⟩ := StarStructureHermitian.exists_hermitian_twist s
  exact ⟨P, hP, hs, usignature_ne_lorentz _ hP⟩

/-! ## The seed -/

/-- **THE SEED'S STAR IS NEVER LORENTZIAN.** `SeedStarStructure.seed_star_hermitian` with one
more clause: the Hermitian unit that presents the transported star has unordered signature
`s(4, 0)` or `s(2, 2)` (that theorem) and in particular not `s(1, 3)` (this one). -/
theorem seed_star_not_lorentz (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : finrank ℂ A = 4) (s : StarStrC A) :
    ∃ (e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) (P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ),
      (P : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (P : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (∀ x : A, e (s.map x) = ((P : Matrix (Fin 2) (Fin 2) ℂ) * e x
        * ((P⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) ∧
      usignature (P : Matrix (Fin 2) (Fin 2) ℂ) ≠ s(1, 3) := by
  obtain ⟨e, P, hP, hs, -⟩ := seed_star_hermitian A hnc hdim s
  exact ⟨e, P, hP, hs, usignature_ne_lorentz _ hP⟩

end HermitianSignatureEven
