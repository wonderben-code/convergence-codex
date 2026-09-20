/-
  TripleSelectsStar.lean — the estate's own spectral-triple structure selects its involution: a
  `SpectralTripleBimodule.Triple` with injective `π` has a pointed positive cone, so its star,
  carried to `Mₙ(ℂ)`, is the conjugate transpose's class; on `Mₙ(ℂ) × Mₙ(ℂ)` the componentwise
  conjugate transpose's inner class; the indefinite twists carry no faithful `Triple`; and a seed
  that is the algebra of a faithful `Triple` is `M₂(ℂ)` with the conjugate transpose. Only the
  fields `π` and `star_π` are consumed — `J` plays no part.

  SPINE L6 / `WALLS` §W9 rung 2, FIRST half in §W9.8's words (which involutions — now which one,
  for the structure §W9.1 asked for), L3 (`ASSUMPTIONS_LEDGER` 4) and L11 (Caesar item 2).
  Hardening unit 166, 2026-09-20.

  WHY. Unit 165 proved that a faithful ⋆-representation makes the cone pointed, for a bare ring
  homomorphism into the operators on an inner-product space. The estate's real spectral triple,
  `SpectralTripleBimodule.Triple`, carries exactly that hypothesis as its field `star_π`
  (`⟪π a u, v⟫ = ⟪u, π (star a) v⟫`) with `π` an `AlgHom` — the same field
  `SpectralTripleBimodule.isSemisimple_of_faithful_pi` feeds to rung 1 — so the theorem applies
  to every `Triple` whose `π` is injective, and the estate's only non-scalar instance,
  `RealSpectralWitness.realWitness`, is one (`OrderOneNontrivial.piW_injective`). Two consequences
  are worth the file. (1) The structure `WALLS` §W9.1 asked for, once faithful, SELECTS its
  involution: the ⋆-representation axiom, not the real structure, fixes the star — the proof
  consumes `π` and `star_π` alone, never `J`, `D`, `γ`, `πOp`, the order conditions or the KO-6
  signs. Units 160 and 164 had written that *"CCM's second half is that the real structure `J`
  selects the involution"*; in this structure `J` CONSUMES the star (`πOp_impl` reads
  `π (star b)`) and selects nothing — `ERRATUM 674`. (2) The negative: no `Triple` over an algebra
  whose carried star is an indefinite twist is faithful.

  The `StarRing` bookkeeping. `Triple` takes Mathlib's `[StarRing A]`; the estate's ⋆-structures
  are `StarStr`/`StarStrC`/`StarStructure`. `starStrCOfStarRing` turns a conjugate-linear
  `StarRing` into a `StarStrC`, and `transportC` carries a `StarStrC` along any `ℂ`-algebra
  isomorphism (`SeedStarStructure.transport` with an arbitrary target). The theorems are stated
  for an ARBITRARY `ℂ`-algebra `A` with `e : A ≃ₐ[ℂ] Mₙ(ℂ)` (or `Mₙ(ℂ) × Mₙ(ℂ)`) rather than for
  `Mₙ(ℂ)` with a variable `StarRing`: on a concrete type with a global `Star` instance a bare
  `star` resolves to Mathlib's instance and not to the variable one, which the first two drafts
  found the hard way (`hxy : star x * x + … = 0` elaborated with `Matrix.instStar` against a
  `Triple` built on the variable, and a `letI` in a statement registered no instance at all).

  WHAT IS PROVED.
  * **`Triple.star_pointed`** — `T : Triple 𝕂 𝕜 A H`, `Function.Injective T.π` ⟹
    `star x * x + star y * y = 0 → star x * x = 0`, for any `StarRing A`.
  * `starStrCOfStarRing`, `transportC`, `pointedA_transportC` — the bookkeeping, with pointedness
    carried along the isomorphism.
  * **`pointedA_of_faithful_triple`** — `PointedA (starStrCOfStarRing hsmul)`;
    **`conjugate_conjTransposeStar_of_faithful_triple`** — carried to `Mₙ(ℂ)`, conjugate to the
    conjugate transpose; `usignature_of_faithful_triple` — a conjugate Hermitian twist is definite;
    **`not_faithful_triple_of_indefinite`** — no faithful `Triple` over an indefinite twist;
    **`innerConjugate_prodConjTransposeC_of_faithful_triple`** — on `Mₙ(ℂ) × Mₙ(ℂ)`;
    **`seed_star_conjugate_conjTransposeStar_of_faithful_triple`** — the seed.
  * `pointed_conjTransposeStar_via_realWitness`, `realWitness_conjugate_conjTransposeStar` —
    non-vacuity on the estate's real spectral triple.

  WHAT IS **NOT** PROVED, said exactly.
  * Anything about the order-one condition — rung 2's SECOND half in §W9.8's words; `J`, `D`, `γ`
    and the KO-6 signs are carried by every `T` here and used by nothing.
  * That any estate algebra other than `M₂(ℂ)` with the conjugate transpose IS the algebra of a
    faithful `Triple`: `realWitness` is the only non-scalar instance (`scalarWitness` is the
    other), and its star is Mathlib's. No `Triple` over `Mₙ(ℂ) × Mₙ(ℂ)` exists in the estate, so
    the product theorem has no instance here.
  * More than two factors, unequal sizes, `ℝ`/`ℍ`. `[NeZero n]` stands on the classification
    statements.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import StarStructureFromRep
import RealSpectralWitness

namespace TripleSelectsStar

open Matrix StarStructureMatrix StarStructureProduct StarStructureTwistFibre
  StarStructureInequivalent HermitianSignatureClassification SeedStarPositivity
  StarStructurePointed StarStructureProductMatrix StarStructureSwapConjugacy
  StarStructureFixConjugacy StarStructureFromRep SeedStarStructure
  SpectralTripleBimodule RealSpectralWitness OrderOneNontrivial
open scoped InnerProductSpace

variable {n : ℕ}

/-! ## 1. A faithful `Triple` has a pointed positive cone -/

/-- **A FAITHFUL `Triple` HAS A POINTED POSITIVE CONE.** Only the fields `π` and `star_π` are
consumed; `J`, `D`, `γ`, `πOp`, both order conditions and the KO-6 signs are not. -/
theorem Triple.star_pointed {𝕂 𝕜 A H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜]
    [Ring A] [StarRing A] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]
    (T : Triple 𝕂 𝕜 A H) (hinj : Function.Injective T.π) (x y : A)
    (hxy : star x * x + star y * y = 0) : star x * x = 0 :=
  pointed_of_faithful_star_rep (star : A → A) T.π.toRingHom hinj
    (fun a u v => T.star_π a u v) x y hxy

/-! ## 2. From a `StarRing` to the estate's ⋆-structures, and transport along an isomorphism -/

/-- A `StarRing` on a `ℂ`-algebra whose star is conjugate-linear is a `StarStrC`. -/
noncomputable def starStrCOfStarRing {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x) : StarStrC A where
  map := star
  map_add := star_add
  map_mul := star_mul
  map_involutive := star_star
  map_smul := hsmul

theorem starStrCOfStarRing_map {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x) (x : A) :
    (starStrCOfStarRing hsmul).map x = star x := rfl

/-- A `StarStrC` carried along a `ℂ`-algebra isomorphism — `SeedStarStructure.transport` with
an arbitrary target. -/
noncomputable def transportC {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (s : StarStrC A) (e : A ≃ₐ[ℂ] B) : StarStrC B where
  map X := e (s.map (e.symm X))
  map_add X Y := by rw [map_add, s.map_add, map_add]
  map_mul X Y := by rw [map_mul, s.map_mul, map_mul]
  map_involutive X := by rw [e.symm_apply_apply, s.map_involutive, e.apply_symm_apply]
  map_smul c X := by rw [map_smul, s.map_smul, map_smul]

theorem transportC_map {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (s : StarStrC A) (e : A ≃ₐ[ℂ] B) (X : B) :
    (transportC s e).map X = e (s.map (e.symm X)) := rfl

/-- Pointedness travels along the isomorphism. -/
theorem pointedA_transportC {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]
    (s : StarStrC A) (e : A ≃ₐ[ℂ] B) (hs : PointedA s) : PointedA (transportC s e) := by
  intro X Y h
  have h' : s.map (e.symm X) * e.symm X + s.map (e.symm Y) * e.symm Y = 0 := by
    apply e.injective
    rw [map_add, map_mul, map_mul, _root_.map_zero, e.apply_symm_apply, e.apply_symm_apply]
    exact h
  have h0 := hs _ _ h'
  change e (s.map (e.symm X)) * X = 0
  calc e (s.map (e.symm X)) * X = e (s.map (e.symm X) * e.symm X) := by
        rw [map_mul, e.apply_symm_apply]
    _ = 0 := by rw [h0, _root_.map_zero]

/-! ## 3. So a faithful `Triple` selects the involution -/

/-- For any `ℂ`-algebra with a conjugate-linear `StarRing`: a faithful `Triple` makes the star
pointed. -/
theorem pointedA_of_faithful_triple {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x)
    {𝕂 𝕜 H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]
    (T : Triple 𝕂 𝕜 A H) (hinj : Function.Injective T.π) :
    PointedA (starStrCOfStarRing hsmul) :=
  fun x y (hxy : star x * x + star y * y = 0) => Triple.star_pointed T hinj x y hxy

/-- **THE SELECTION, FOR THE ESTATE'S OWN SPECTRAL-TRIPLE STRUCTURE.** If the algebra of a
faithful `Triple` is `Mₙ(ℂ)` up to `ℂ`-algebra isomorphism, its star carried to `Mₙ(ℂ)` is
conjugate to the conjugate transpose. -/
theorem conjugate_conjTransposeStar_of_faithful_triple [NeZero n] {A : Type*} [Ring A]
    [Algebra ℂ A] [StarRing A]
    (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x)
    (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    {𝕂 𝕜 H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]
    (T : Triple 𝕂 𝕜 A H) (hinj : Function.Injective T.π) :
    Conjugate (conjTransposeStar n) (transport (starStrCOfStarRing hsmul) e) :=
  (pointed_iff_conjugate_conjTransposeStar _).mp
    ((pointedA_iff_transport _ e).mp (pointedA_of_faithful_triple hsmul T hinj))

/-- In signature form: if the carried star is conjugate to `hermitianStar P`, then `P` is
definite. -/
theorem usignature_of_faithful_triple [NeZero n] {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A]
    (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x)
    (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hconj : Conjugate (transport (starStrCOfStarRing hsmul) e) (hermitianStar P hP))
    {𝕂 𝕜 H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]
    (T : Triple 𝕂 𝕜 A H) (hinj : Function.Injective T.π) :
    usignature (P : Matrix (Fin n) (Fin n) ℂ) = s(2 * n, 0) :=
  (pointed_iff_definite P hP).mp (pointed_of_conjugate hconj
    ((pointedA_iff_transport _ e).mp (pointedA_of_faithful_triple hsmul T hinj)))

/-- **THE INDEFINITE TWISTS CARRY NO FAITHFUL `Triple`.** -/
theorem not_faithful_triple_of_indefinite [NeZero n] {A : Type*} [Ring A] [Algebra ℂ A]
    [StarRing A] (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x)
    (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ) (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hind : usignature (P : Matrix (Fin n) (Fin n) ℂ) ≠ s(2 * n, 0))
    (hconj : Conjugate (transport (starStrCOfStarRing hsmul) e) (hermitianStar P hP))
    {𝕂 𝕜 H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]
    (T : Triple 𝕂 𝕜 A H) : ¬ Function.Injective T.π :=
  fun hinj => hind (usignature_of_faithful_triple hsmul e P hP hconj T hinj)

/-- **On `Mₙ(ℂ) × Mₙ(ℂ)`**, up to `ℂ`-algebra isomorphism: the carried star of a faithful
`Triple` is inner-conjugate to the componentwise conjugate transpose. -/
theorem innerConjugate_prodConjTransposeC_of_faithful_triple [NeZero n] {A : Type*} [Ring A]
    [Algebra ℂ A] [StarRing A]
    (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x)
    (e : A ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
    {𝕂 𝕜 H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]
    (T : Triple 𝕂 𝕜 A H) (hinj : Function.Injective T.π) :
    InnerConjugate (prodConjTransposeC n n) (transportC (starStrCOfStarRing hsmul) e) :=
  (pointedA_iff_innerConjugate _).mp
    (pointedA_transportC _ e (pointedA_of_faithful_triple hsmul T hinj))

/-- **THE SEED AS THE ALGEBRA OF A FAITHFUL `Triple`** is `M₂(ℂ)` with the conjugate transpose. -/
theorem seed_star_conjugate_conjTransposeStar_of_faithful_triple (A : Type*) [Ring A]
    [Algebra ℂ A] [FiniteDimensional ℂ A] [IsSemisimpleRing A] [StarRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : Module.finrank ℂ A = 4)
    (hsmul : ∀ (c : ℂ) (x : A), star (c • x) = (starRingEnd ℂ) c • star x)
    {𝕂 𝕜 H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜] [Algebra 𝕂 A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]
    (T : Triple 𝕂 𝕜 A H) (hinj : Function.Injective T.π) :
    ∃ e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ,
      Conjugate (transport (starStrCOfStarRing hsmul) e) (conjTransposeStar 2) :=
  seed_star_conjugate_conjTransposeStar A hnc hdim _ (pointedA_of_faithful_triple hsmul T hinj)

/-! ## 4. Non-vacuity: the estate's real spectral triple -/

/-- `realWitness` is faithful (`piW_injective`), so its star — Mathlib's, the conjugate
transpose — is pointed by §1. -/
theorem pointed_conjTransposeStar_via_realWitness : Pointed (conjTransposeStar 2) :=
  fun x y hxy => Triple.star_pointed realWitness piW_injective x y hxy

/-- Mathlib's star on `M₂(ℂ)` is conjugate-linear, so `realWitness` is an instance of §3 at
`e = refl`, and §3 returns the conjugate transpose's class — as it must. -/
theorem realWitness_conjugate_conjTransposeStar :
    Conjugate (conjTransposeStar 2)
      (transport (starStrCOfStarRing (fun c X => star_smul c X)) AlgEquiv.refl) :=
  conjugate_conjTransposeStar_of_faithful_triple _ AlgEquiv.refl realWitness piW_injective

end TripleSelectsStar
