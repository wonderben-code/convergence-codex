/-
  SeedStarPositivity.lean — WHICH of the two stars: the pointed ⋆-structures on `M₂(ℂ)` are exactly
  the definite class, so a seed whose star has a pointed positive cone is `M₂(ℂ)` with the
  conjugate transpose.

  SPINE link L3 (seed realisation), rated GENUINE — hardening unit 151, 2026-09-20.

  WHY. Unit 150 (`SeedStarStructure`) carried the seed's ⋆-structure to `M₂(ℂ)` and found it in one
  of exactly two conjugacy classes, definite (`s(4, 0)`) or indefinite (`s(2, 2)`), and
  `ASSUMPTIONS_LEDGER` 4's amendment recorded the fork it left: *"a C⋆-involution is the definite
  class … but no norm, no C⋆ identity and no positivity is modelled anywhere in the estate, and the
  theorem that the `(2, 2)` class violates `x⋆x ≥ 0` for every candidate norm is not written."* This
  file writes it, without a norm. The property used is the weakest algebraic shadow of C⋆
  positivity: the positive cone `{x⋆x}` is POINTED — `x⋆x + y⋆y = 0` forces `x⋆x = 0`. Every
  C⋆-algebra has it (positive elements with zero sum are zero), and it is stated with `*`, `+`
  and `0` alone.

  WHAT IS PROVED.
  * `Pointed s` for a ⋆-structure on `Mₙ(ℂ)`; `PointedA s` for a `StarStrC` on any algebra.
  * `pointed_conjTransposeStar` — the definite class is pointed, by the trace of `xᴴ x`
    (`Matrix.posSemidef_conjTranspose_mul_self`, `trace_conjTranspose_mul_self_eq_zero_iff`).
  * `not_pointed_diagTwist` — the indefinite class is NOT pointed: with `⋆ = X ↦ (D X D)ᴴ`,
    `D = diag(1, −1)`, the matrix units give `e₁₂⋆ e₁₂ = −e₂₂` and `e₂₂⋆ e₂₂ = e₂₂`, a sum of two
    "squares" that vanishes with neither term zero.
  * `conjugate_symm`, `pointed_of_conjugate` — conjugacy is symmetric and preserves pointedness.
  * **`pointed_iff_usignature`** — for a Hermitian unit `P` on `M₂(ℂ)`, `hermitianStar P` is
    pointed **iff** `usignature P = s(4, 0)`: the pointed ⋆-structures on `M₂(ℂ)` are exactly the
    definite class.
  * `pointedA_iff_transport` — pointedness of a seed's star is the pointedness of its transport.
  * **`seed_star_definite_of_pointed`** — for the seed (finite-dimensional semisimple over `ℂ`,
    non-commutative, `finrank = 4`) with a POINTED ⋆-structure, `seed_unique_dim_four`'s equivalence
    carries the star to a Hermitian twist of unordered signature `s(4, 0)`; and
    `seed_star_conjugate_conjTransposeStar` — the transported star is conjugate to the conjugate
    transpose itself. **The choice of class is a theorem under one named C⋆ property.**

  WHAT IS **NOT** PROVED, said exactly.
  * That the seed's star IS pointed. That is the C⋆ input, now reduced to one algebraic sentence
    (`PointedA s`) and recorded as the live residue of `ASSUMPTIONS_LEDGER` 4. Nothing here
    supplies it, and nothing in the estate models a norm.
  * Anything about the C⋆ NORM identity `‖x⋆x‖ = ‖x‖²`, or about states and positivity of
    functionals.
  * `Pointed` is one consequence of C⋆ positivity, not an equivalent of it; a ⋆-algebra can be
    pointed without being a C⋆-algebra. The theorem is that the indefinite class fails even this
    weakest test.
  * The classification consumed (units 69–75, 150) is not re-proved.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SeedStarStructure
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace SeedStarPositivity

open scoped ComplexOrder

open Matrix StarStructureMatrix StarStructureProductMatrix StarStructureTwistFibre
  StarStructureInequivalent HermitianSignatureClassification SeedStarStructure

variable {n : ℕ}

/-! ## 1. Pointedness -/

/-- The positive cone `{x⋆x}` is pointed: two squares summing to zero are each zero. Stated with
`*`, `+`, `0` and the involution alone — no norm. -/
def Pointed (s : StarStructure n) : Prop :=
  ∀ x y : Matrix (Fin n) (Fin n) ℂ, s.map x * x + s.map y * y = 0 → s.map x * x = 0

/-- The same, for a ⋆-structure on an arbitrary `ℂ`-algebra. -/
def PointedA {A : Type*} [Ring A] [Algebra ℂ A] (s : StarStrC A) : Prop :=
  ∀ x y : A, s.map x * x + s.map y * y = 0 → s.map x * x = 0

theorem pointed_congr {s t : StarStructure n} (h : ∀ X, s.map X = t.map X) :
    Pointed s ↔ Pointed t := by
  unfold Pointed
  simp only [h]

/-! ## 2. The definite class is pointed -/

theorem pointed_conjTransposeStar (m : ℕ) : Pointed (conjTransposeStar m) := by
  intro x y h
  change xᴴ * x + yᴴ * y = 0 at h
  change xᴴ * x = 0
  have hx := (Matrix.posSemidef_conjTranspose_mul_self x).trace_nonneg
  have hy := (Matrix.posSemidef_conjTranspose_mul_self y).trace_nonneg
  have hsum : (xᴴ * x).trace + (yᴴ * y).trace = 0 := by
    rw [← Matrix.trace_add, h, Matrix.trace_zero]
  have hx0 : (xᴴ * x).trace = 0 := ((add_eq_zero_iff_of_nonneg hx hy).mp hsum).1
  rw [Matrix.trace_conjTranspose_mul_self_eq_zero_iff] at hx0
  rw [hx0]
  simp

/-! ## 3. The indefinite class is not -/

/-- `D X D` for `D = diag(1, −1)`, entrywise. -/
theorem diagTwist_conj_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ((diagTwist : Matrix (Fin 2) (Fin 2) ℂ) * X
      * ((diagTwist⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ)) i j
      = (![1, -1] : Fin 2 → ℂ) i * X i j * (![1, -1] : Fin 2 → ℂ) j := by
  change (Matrix.diagonal (![1, -1] : Fin 2 → ℂ) * X * Matrix.diagonal (![1, -1] : Fin 2 → ℂ)) i j
    = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem twistMap_diagTwist_apply (X : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    twistMap diagTwist X i j
      = star ((![1, -1] : Fin 2 → ℂ) j * X j i * (![1, -1] : Fin 2 → ℂ) i) := by
  rw [twistMap_apply, Matrix.conjTranspose_apply, diagTwist_conj_apply]

/-- `e₁₂⋆ e₁₂ = −e₂₂` under the indefinite star. -/
theorem indefinite_square_single01 :
    (hermitianStar diagTwist diagTwist_hermitian).map (Matrix.single (0 : Fin 2) (1 : Fin 2) (1
      : ℂ))
      * Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = - Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  change twistMap diagTwist _ * _ = _
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [twistMap_diagTwist_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- `e₂₂⋆ e₂₂ = e₂₂` under the indefinite star. -/
theorem indefinite_square_single11 :
    (hermitianStar diagTwist diagTwist_hermitian).map (Matrix.single (1 : Fin 2) (1 : Fin 2) (1
      : ℂ))
      * Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ)
      = Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) := by
  change twistMap diagTwist _ * _ = _
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [twistMap_diagTwist_apply]
  fin_cases i <;> fin_cases j <;> simp

theorem not_pointed_diagTwist : ¬ Pointed (hermitianStar diagTwist diagTwist_hermitian) := by
  intro h
  have h0 := h (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : ℂ))
    (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ))
    (by rw [indefinite_square_single01, indefinite_square_single11]; simp)
  rw [indefinite_square_single01, neg_eq_zero] at h0
  have := congrFun (congrFun h0 1) 1
  simp at this

/-! ## 4. Conjugacy preserves pointedness -/

theorem conjugate_symm {s t : StarStructure n} (h : Conjugate s t) : Conjugate t s := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S⁻¹, fun Y => ?_⟩
  have := hS (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Y
    * (S : Matrix (Fin n) (Fin n) ℂ))
  rw [inv_inv]
  -- `this : t.map (S⁻¹ Y S) = S⁻¹ * s.map (S * (S⁻¹ Y S) * S⁻¹) * S`; simplify the inner product
  have hmid : (S : Matrix (Fin n) (Fin n) ℂ)
      * (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Y
        * (S : Matrix (Fin n) (Fin n) ℂ))
      * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Y := by
    simp [Matrix.mul_assoc]
  rw [hmid] at this
  rw [this]
  simp [Matrix.mul_assoc]

theorem pointed_of_conjugate {s t : StarStructure n} (h : Conjugate s t) (hs : Pointed s) :
    Pointed t := by
  obtain ⟨S, hS⟩ := h
  have key : ∀ z : Matrix (Fin n) (Fin n) ℂ, t.map z * z
      = ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (s.map ((S : Matrix (Fin n) (Fin n) ℂ) * z
            * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
          * ((S : Matrix (Fin n) (Fin n) ℂ) * z
            * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)))
        * (S : Matrix (Fin n) (Fin n) ℂ) := by
    intro z
    rw [hS]
    simp [Matrix.mul_assoc]
  intro x y hxy
  rw [key, key, ← Matrix.add_mul, ← Matrix.mul_add] at hxy
  have hin : s.map ((S : Matrix (Fin n) (Fin n) ℂ) * x
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      * ((S : Matrix (Fin n) (Fin n) ℂ) * x
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      + s.map ((S : Matrix (Fin n) (Fin n) ℂ) * y
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))
      * ((S : Matrix (Fin n) (Fin n) ℂ) * y
        * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
    have := congrArg (fun M => (S : Matrix (Fin n) (Fin n) ℂ) * M
      * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) hxy
    simpa [Matrix.mul_assoc] using this
  rw [key, hs _ _ hin]
  simp

/-! ## 5. The pointed ⋆-structures on `M₂(ℂ)` are exactly the definite class -/

theorem pointed_iff_usignature (P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ)
    (hP : (P : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (P : Matrix (Fin 2) (Fin 2) ℂ)) :
    Pointed (hermitianStar P hP) ↔ usignature (P : Matrix (Fin 2) (Fin 2) ℂ) = s(4, 0) := by
  have hmem := mem_achievable_of_unit P hP
  rw [achievable_two_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
  constructor
  · intro hpt
    rcases hmem with h | h
    · exact h
    · exfalso
      have hconj : Conjugate (hermitianStar P hP) (hermitianStar diagTwist diagTwist_hermitian) :=
        (conjugate_iff_usignature P diagTwist hP diagTwist_hermitian).mpr
          (by rw [h, both_classes_occur.2])
      exact not_pointed_diagTwist (pointed_of_conjugate hconj hpt)
  · intro h
    have hconj : Conjugate (hermitianStar P hP)
        (hermitianStar (1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (by simp)) :=
      (conjugate_iff_usignature P 1 hP (by simp)).mpr (by rw [h, both_classes_occur.1])
    have h1 : Pointed (hermitianStar (1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (by simp)) := by
      rw [hermitianStar_one]
      exact pointed_conjTransposeStar 2
    exact pointed_of_conjugate (conjugate_symm hconj) h1

/-! ## 6. Back to the seed -/

variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem pointedA_iff_transport (s : StarStrC A) (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    PointedA s ↔ Pointed (transport s e) := by
  constructor
  · intro hs X Y hXY
    have hX : (transport s e).map X * X = e (s.map (e.symm X) * e.symm X) := by
      rw [transport_map, map_mul, AlgEquiv.apply_symm_apply]
    have hY : (transport s e).map Y * Y = e (s.map (e.symm Y) * e.symm Y) := by
      rw [transport_map, map_mul, AlgEquiv.apply_symm_apply]
    rw [hX, hY, ← map_add, map_eq_zero_iff _ e.injective] at hXY
    rw [hX, hs _ _ hXY, map_zero]
  · intro ht x y hxy
    have hx : (transport s e).map (e x) * e x = e (s.map x * x) := by
      rw [transport_map_apply, map_mul]
    have hy : (transport s e).map (e y) * e y = e (s.map y * y) := by
      rw [transport_map_apply, map_mul]
    have := ht (e x) (e y) (by rw [hx, hy, ← map_add, hxy, map_zero])
    rw [hx, map_eq_zero_iff _ e.injective] at this
    exact this

/-- **WHICH OF THE TWO: A THEOREM.** A seed whose star has a pointed positive cone is `M₂(ℂ)` with a
twist of unordered signature `s(4, 0)` — the definite class, the C⋆ one. -/
theorem seed_star_definite_of_pointed (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : Module.finrank ℂ A = 4) (s : StarStrC A)
    (hs : PointedA s) :
    ∃ (e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) (P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ)
      (hP : (P : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (P : Matrix (Fin 2) (Fin 2) ℂ)),
      (∀ X, (transport s e).map X = (hermitianStar P hP).map X) ∧
      usignature (P : Matrix (Fin 2) (Fin 2) ℂ) = s(4, 0) := by
  obtain ⟨e, P, hP, hmap⟩ := seed_star_eq_hermitianStar A hnc hdim s
  refine ⟨e, P, hP, hmap, ?_⟩
  rw [← pointed_iff_usignature P hP, ← pointed_congr hmap, ← pointedA_iff_transport]
  exact hs

/-- The same, read as conjugacy: the seed's star, carried to `M₂(ℂ)`, is conjugate to the conjugate
transpose. -/
theorem seed_star_conjugate_conjTransposeStar (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : Module.finrank ℂ A = 4) (s : StarStrC A)
    (hs : PointedA s) :
    ∃ e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ, Conjugate (transport s e) (conjTransposeStar 2) := by
  obtain ⟨e, P, hP, hmap, hu⟩ := seed_star_definite_of_pointed A hnc hdim s hs
  refine ⟨e, ?_⟩
  have hconj : Conjugate (hermitianStar P hP)
      (hermitianStar (1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (by simp)) :=
    (conjugate_iff_usignature P 1 hP (by simp)).mpr (by rw [hu, both_classes_occur.1])
  rw [hermitianStar_one] at hconj
  obtain ⟨S, hS⟩ := hconj
  exact ⟨S, fun X => by rw [hmap]; exact hS X⟩

end SeedStarPositivity
