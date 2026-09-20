/-
  SeedStarStructure.lean — the seed WITH its star: a ⋆-structure on the seed algebra is one of
  exactly two, and `seed_unique_dim_four`'s equivalence carries it.

  SPINE link L3 (seed realisation `D → M₂(ℂ)`), rated GENUINE — hardening unit 150, 2026-09-20.

  WHY. `ASSUMPTIONS_LEDGER` 4, in its own words: *"The seed conclusion is a bare ℂ-algebra
  equivalence — the ⋆-structure never appears … `Nonempty (A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)`
  transports multiplication but not the adjoint … 'the seed C⋆-algebra is `M₂(ℂ)`' is being
  supported by a theorem that delivers only the underlying ℂ-algebra."* The L3 row says the same
  in its *what is not* column: *the isomorphism is of ℂ-algebras, no ⋆*. Since 15–16 September the
  estate knows exactly which ⋆-structures `M₂(ℂ)` carries — every one is `X ↦ (P X P⁻¹)ᴴ` for a
  Hermitian unit `P`, two of them up to conjugacy, classified by the unordered signature of `P`
  (`StarStructureMatrix`, `StarStructureHermitian`, `HermitianSignatureClassification`). This file
  puts the two chains together.

  WHAT IS PROVED.
  * `transport s e : StarStructure n` — a ⋆-structure `s` on any `ℂ`-algebra `A` (a `StarStrC`:
    additive, conjugate-linear, anti-multiplicative, involutive) carried along an algebra
    equivalence `e : A ≃ₐ[ℂ] Mₙ(ℂ)`, with `transport_map`.
  * `seed_star_hermitian` — for the SEED (`A` finite-dimensional semisimple over `ℂ`,
    non-commutative, `finrank ℂ A = 4`) with a ⋆-structure `s`: there are `e : A ≃ₐ[ℂ] M₂(ℂ)` and
    a Hermitian unit `P` with `e (s.map x) = (P * e x * P⁻¹)ᴴ` for every `x`, and
    `usignature P ∈ achievable 2`. **The equivalence `e` is `seed_unique_dim_four`'s, so the
    algebra half of L3 is unchanged and the star is now carried by it.**
  * `seed_star_two_classes` — `(achievable 2).card = 2`: the seed's star is one of EXACTLY two
    conjugacy classes, and `seed_star_usignature` names them, `s(4, 0)` or `s(2, 2)`.
  * `seed_star_conjugate_iff` — two ⋆-structures on the seed, transported along the same `e`, are
    conjugate on `M₂(ℂ)` iff their twists have the same unordered signature.
  * **§5, the arrow OUT of the seed theorem into the tower** — `UNLOCK_WATCHLIST` entry 259 asks
    for *"one theorem that takes `seed_forced`'s conclusion as its HYPOTHESIS and produces the
    cascade's first step"*: `seedEndEquiv e : Module.End ℂ A ≃ₐ[ℂ] SpineSharpenings.D 1` for any
    `e : A ≃ₐ[ℂ] M₂(ℂ)`, hence `seed_end_equiv_D1` for the seed itself, and `finrank_end_seed = 16`.
    `endAlgConj` (conjugation of endomorphisms by a linear equivalence, as an ALGEBRA equivalence)
    is the general step; this Mathlib has `LinearEquiv.conj` only as a linear one.

  WHAT IS **NOT** PROVED, said exactly.
  * **Which of the two the seed carries.** Both classes occur (`exists_twist_usignature`), and
    nothing here or anywhere in the estate selects the definite one (`conjTransposeStar`, `P = 1`,
    signature `(4, 0)`) over the indefinite one (`diagTwist`, signature `(2, 2)`). That choice is a
    physical input, not a theorem; it is recorded in `ASSUMPTIONS_LEDGER` 4's amendment.
  * **No norm and no C⋆ identity.** `StarStrC` is an algebraic involution. Nothing here says
    `‖x⋆x‖ = ‖x‖²`, and "trace-faithful C⋆-algebra" is still modelled as `IsSemisimpleRing`
    (`ASSUMPTIONS_LEDGER` 4's related note, unchanged).
  * **Positivity of the star is not discussed.** A C⋆-algebra's involution makes `x⋆x` positive;
    the indefinite class has `P` of signature `(2, 2)`, and whether it could be a C⋆-involution for
    SOME norm is not asked here.
  * The classification consumed is the estate's own (units 69–75); nothing about it is re-proved.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SeedUniqueness
import SpineSharpenings
import StarStructureHermitian
import StarStructureProductMatrix
import StarStructureInequivalent
import HermitianSignatureClassification

namespace SeedStarStructure

open Module Matrix StarStructureMatrix StarStructureProductMatrix StarStructureTwistFibre
  StarStructureInequivalent HermitianSignatureClassification

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

/-! ## 1. Transport of a ⋆-structure along an algebra equivalence -/

/-- A ⋆-structure on `A`, read on `Mₙ(ℂ)` through `e`. -/
noncomputable def transport (s : StarStrC A) (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) :
    StarStructure n where
  map X := e (s.map (e.symm X))
  map_add X Y := by
    rw [map_add, s.map_add, map_add]
  map_smul c X := by
    rw [map_smul, s.map_smul, map_smul]
  map_mul X Y := by
    rw [map_mul, s.map_mul, map_mul]
  map_involutive X := by
    rw [AlgEquiv.symm_apply_apply, s.map_involutive, AlgEquiv.apply_symm_apply]

theorem transport_map (s : StarStrC A) (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (X) :
    (transport s e).map X = e (s.map (e.symm X)) := rfl

theorem transport_map_apply (s : StarStrC A) (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (x : A) :
    (transport s e).map (e x) = e (s.map x) := by
  rw [transport_map, AlgEquiv.symm_apply_apply]

/-! ## 2. The seed's star is a Hermitian twist on `M₂(ℂ)`, of one of two signatures -/

/-- **THE SEED WITH ITS STAR.** `seed_unique_dim_four` gives the algebra equivalence; through it,
the seed's ⋆-structure is `X ↦ (P X P⁻¹)ᴴ` for a Hermitian unit `P` whose unordered signature is
one of `achievable 2`'s elements. -/
theorem seed_star_hermitian (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : finrank ℂ A = 4) (s : StarStrC A) :
    ∃ (e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) (P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ),
      (P : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (P : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (∀ x : A, e (s.map x) = ((P : Matrix (Fin 2) (Fin 2) ℂ) * e x
        * ((P⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) ∧
      usignature (P : Matrix (Fin 2) (Fin 2) ℂ) ∈ achievable 2 := by
  obtain ⟨e⟩ := SeedUniqueness.seed_unique_dim_four A hnc hdim
  obtain ⟨P, hP, hs⟩ := StarStructureHermitian.exists_hermitian_twist (transport s e)
  refine ⟨e, P, hP, fun x => ?_, mem_achievable_of_unit P hP⟩
  rw [← transport_map_apply s e x]
  exact hs (e x)

/-- The seed's star, as the estate's named object `hermitianStar P hP`, read through `e`. -/
theorem seed_star_eq_hermitianStar (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : finrank ℂ A = 4) (s : StarStrC A) :
    ∃ (e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) (P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ)
      (hP : (P : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (P : Matrix (Fin 2) (Fin 2) ℂ)),
      ∀ X, (transport s e).map X = (hermitianStar P hP).map X := by
  obtain ⟨e⟩ := SeedUniqueness.seed_unique_dim_four A hnc hdim
  obtain ⟨P, hP, hs⟩ := StarStructureHermitian.exists_hermitian_twist (transport s e)
  exact ⟨e, P, hP, fun X => hs X⟩

/-- **EXACTLY TWO.** `achievable 2` has two elements, so the seed's star falls into one of exactly
two conjugacy classes. -/
theorem seed_star_two_classes : (achievable 2).card = 2 := card_achievable_two

/-- **AND THEY ARE `s(4, 0)` AND `s(2, 2)`.** -/
theorem achievable_two_eq : achievable 2 = {s(4, 0), s(2, 2)} := by
  decide

theorem seed_star_usignature (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : finrank ℂ A = 4) (s : StarStrC A) :
    ∃ (e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) (P : (Matrix (Fin 2) (Fin 2) ℂ)ˣ),
      (P : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (P : Matrix (Fin 2) (Fin 2) ℂ) ∧
      (∀ x : A, e (s.map x) = ((P : Matrix (Fin 2) (Fin 2) ℂ) * e x
        * ((P⁻¹ : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ))ᴴ) ∧
      (usignature (P : Matrix (Fin 2) (Fin 2) ℂ) = s(4, 0)
        ∨ usignature (P : Matrix (Fin 2) (Fin 2) ℂ) = s(2, 2)) := by
  obtain ⟨e, P, hP, hs, hmem⟩ := seed_star_hermitian A hnc hdim s
  refine ⟨e, P, hP, hs, ?_⟩
  rw [achievable_two_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

/-! ## 3. Two stars on the seed are conjugate iff their twists have the same signature -/

/-- Two ⋆-structures on the seed, read through ONE equivalence `e` as the Hermitian twists `P`,
`Q` that `seed_star_eq_hermitianStar` supplies, are conjugate on `M₂(ℂ)` iff
`usignature Q = usignature P`. This is `HermitianSignatureClassification.conjugate_iff_usignature`
carried to the seed's own structures. -/
theorem seed_star_conjugate_iff (s t : StarStrC A) (e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (P Q : (Matrix (Fin 2) (Fin 2) ℂ)ˣ)
    (hP : (P : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (P : Matrix (Fin 2) (Fin 2) ℂ))
    (hQ : (Q : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = (Q : Matrix (Fin 2) (Fin 2) ℂ))
    (hs : ∀ X, (transport s e).map X = (hermitianStar P hP).map X)
    (ht : ∀ X, (transport t e).map X = (hermitianStar Q hQ).map X) :
    Conjugate (transport s e) (transport t e)
      ↔ usignature (Q : Matrix (Fin 2) (Fin 2) ℂ) = usignature (P : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [← conjugate_iff_usignature P Q hP hQ]
  unfold Conjugate
  simp only [hs, ht]

/-! ## 4. Both classes occur on the seed's own model `M₂(ℂ)` -/

/-- The definite class is realised by the conjugate transpose (`P = 1`, signature `(4, 0)`) and the
indefinite one by `diagTwist` (signature `(2, 2)`): both are ⋆-structures on `M₂(ℂ)` itself, so
neither class is empty at the seed. -/
theorem both_classes_occur :
    usignature ((1 : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) : Matrix (Fin 2) (Fin 2) ℂ) = s(4, 0) ∧
    usignature (diagTwist : Matrix (Fin 2) (Fin 2) ℂ) = s(2, 2) := by
  constructor
  · rw [usignature, signature_one_two]
  · rw [usignature, signature_diagTwist]

/-! ## 5. The arrow OUT of the seed theorem into the tower -/

/-- Conjugating endomorphisms by a linear equivalence is an ALGEBRA equivalence of `End`s:
`LinearEquiv.conj` upgraded through `AlgEquiv.ofLinearEquiv`, with `conj_id` and `conj_comp`
supplying the two laws. -/
noncomputable def endAlgConj {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N]
    (e : M ≃ₗ[ℂ] N) : Module.End ℂ M ≃ₐ[ℂ] Module.End ℂ N :=
  AlgEquiv.ofLinearEquiv e.conj (LinearEquiv.conj_id e) (fun f g => LinearEquiv.conj_comp e g f)

theorem endAlgConj_apply_apply {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] (e : M ≃ₗ[ℂ] N) (f : Module.End ℂ M) (x : N) :
    endAlgConj e f x = e (f (e.symm x)) :=
  LinearEquiv.conj_apply_apply e f x

/-- `M₂(ℂ)` is the tower's level `0`, up to the size arithmetic `towerSize 0 = 2`. -/
noncomputable def m2ToD0 : Matrix (Fin 2) (Fin 2) ℂ ≃ₐ[ℂ] SpineSharpenings.D 0 :=
  Matrix.reindexAlgEquiv ℂ ℂ (finCongr SpineSharpenings.towerSize_zero.symm)

/-- **THE ARROW OUT OF THE SEED THEOREM INTO THE TOWER.** Given the seed's identification with
`M₂(ℂ)`, its endomorphism algebra IS the tower's level `1` — `SpineSharpenings.endTower 0` with
`D 0` supplied by the seed rather than written as `Matrix (Fin 2) (Fin 2) ℂ`. -/
noncomputable def seedEndEquiv (e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) :
    Module.End ℂ A ≃ₐ[ℂ] SpineSharpenings.D 1 :=
  (endAlgConj (e.trans m2ToD0).toLinearEquiv).trans (SpineSharpenings.endTower 0)

/-- For the seed itself: `End(A) ≃ₐ[ℂ] D 1 = M₄(ℂ)`, with `A` DERIVED by `seed_unique_dim_four`
rather than written down. -/
theorem seed_end_equiv_D1 (A : Type*) [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : finrank ℂ A = 4) :
    Nonempty (Module.End ℂ A ≃ₐ[ℂ] SpineSharpenings.D 1) := by
  obtain ⟨e⟩ := SeedUniqueness.seed_unique_dim_four A hnc hdim
  exact ⟨seedEndEquiv e⟩

/-- The seed's endomorphism algebra has dimension `16 = 4²`, the tower's second size. -/
theorem finrank_end_seed (A : Type*) [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    (hdim : finrank ℂ A = 4) : finrank ℂ (Module.End ℂ A) = 16 := by
  rw [Module.finrank_linearMap, hdim]

end SeedStarStructure
