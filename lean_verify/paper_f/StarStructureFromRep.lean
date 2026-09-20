/-
  StarStructureFromRep.lean — a faithful ⋆-representation on an inner-product space makes the
  positive cone pointed, so it SELECTS the involution: on `Mₙ(ℂ)` the conjugate transpose's class,
  on `Mₙ(ℂ) × Mₙ(ℂ)` the componentwise conjugate transpose's, and on the seed `M₂(ℂ)` with the
  conjugate transpose — and the indefinite classes admit no faithful ⋆-representation at all.

  SPINE L6 / `WALLS` §W9 rung 2, FIRST half in §W9.8's own words (*which involutions the product
  admits* — now narrowed to one under rung 1's hypothesis), L3 (`ASSUMPTIONS_LEDGER` 4's C⋆ input)
  and L11 (Caesar item 2). Hardening unit 165, 2026-09-20.

  WHY. Unit 164 (`StarStructurePointed`) showed that the weakest C⋆ shadow — a pointed positive
  cone — picks exactly one class among all the ⋆-structures on `Mₙ(ℂ)` and on `Mₙ(ℂ) × Mₙ(ℂ)`, and
  said what it did not do: supply pointedness for any ⋆-structure in the estate. Unit 6
  (`StarRepSemisimple`) had already isolated the estate's C⋆ input in a different place: a FAITHFUL
  ⋆-REPRESENTATION, `π : A →+* Module.End 𝕜 H` injective with `⟪π a u, v⟫ = ⟪u, π (a⋆) v⟫`, which
  makes the algebra semisimple (rung 1). The two meet in five lines: under such a `π`, a vanishing
  sum of two squares gives `‖π x v‖² + ‖π y v‖² = 0` for every `v`, so `π x = 0`, so `x = 0`. Hence
  the ⋆-structure of a faithful ⋆-representation is pointed, hence definite. Rung 1's hypothesis
  therefore finishes rung 2's FIRST half by itself — the list of involutions narrows to one: the
  Hilbert space the algebra acts on selects the conjugate transpose, and the indefinite twists are
  not ⋆-representable on any inner-product space. Rung 2's SECOND half — what the order-one
  condition does to the pair `(A, A°)` — is untouched.

  WHAT IS PROVED.
  * **`pointed_of_faithful_star_rep`** — for any ring `A`, map `m : A → A`, and injective
    `π : A →+* Module.End 𝕜 H` with `⟪π a u, v⟫ = ⟪u, π (m a) v⟫`:
    `m x * x + m y * y = 0 → m x * x = 0`. `pointed_of_faithful_star_rep_matrix` (as `Pointed`),
    `pointedA_of_faithful_star_rep` (as `PointedA`).
  * **`conjugate_conjTransposeStar_of_faithful_star_rep`** — the involution of a faithful
    ⋆-representation of `Mₙ(ℂ)` is conjugate to the conjugate transpose;
    `usignature_of_faithful_star_rep` — its Hermitian twist has `usignature = s(2n, 0)`;
    **`not_faithful_star_rep_of_indefinite`** — an indefinite twist has no faithful
    ⋆-representation on any inner-product space.
  * **`innerConjugate_prodConjTransposeC_of_faithful_star_rep`** — on `Mₙ(ℂ) × Mₙ(ℂ)`,
    inner-conjugate to the componentwise conjugate transpose.
  * **`seed_star_conjugate_conjTransposeStar_of_faithful_star_rep`** — the seed with a faithfully
    ⋆-represented star is `M₂(ℂ)` with the conjugate transpose up to conjugacy: unit 151's
    theorem with `PointedA s` discharged.
  * `conjTransposeStar_map_eq_star`, `pointed_conjTransposeStar_via_rep` — non-vacuity through
    `StarRepSemisimple.matrixRep`.

  WHAT IS **NOT** PROVED, said exactly.
  * That the estate's algebras HAVE a faithful ⋆-representation with THEIR ⋆-structure. `matrixRep`
    and `KOSixAlgebraAction.particleRep` are faithful ⋆-representations of `Mₙ(ℂ)` with the
    conjugate transpose already; the theorem says any other ⋆-structure so represented is conjugate
    to it. The seed's C⋆ input moves from *the cone is pointed* to *the star is faithfully
    ⋆-represented on an inner-product space* — a hypothesis about the Hilbert space, still supplied
    by nothing in the estate; `ASSUMPTIONS_LEDGER` 4 records the move.
  * Rung 2's second half in §W9.1's wording — the order-one condition on `(A, A°)` — and CCM's
    own mechanism, in which the real structure `J` carries `A°`. The selection here comes from the
    adjoint on `H`, not from a `J` and not from order-one; nothing relates them. (Units 160 and 164
    called the `J`-selection *the second half*; `ERRATUM 673` records the misnomer.)
  * Anything about the order-one condition, the pair `(A, A°)`, more than two factors, unequal
    sizes, or `ℝ`/`ℍ`. `[NeZero n]` stands on the classification statements.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import StarStructurePointed
import StarRepSemisimple

namespace StarStructureFromRep

open Matrix StarStructureMatrix StarStructureTwistFibre StarStructureInequivalent
  HermitianSignatureClassification SeedStarPositivity StarStructurePointed
  StarStructureProductMatrix StarStructureSwapConjugacy StarStructureFixConjugacy StarRepSemisimple
  SeedStarStructure
open scoped InnerProductSpace

variable {n : ℕ}

/-! ## 1. A faithful ⋆-representation makes the positive cone pointed -/

/-- **A FAITHFUL ⋆-REPRESENTATION MAKES THE POSITIVE CONE POINTED.** For any ring `A` with an
involution-like map `m`, an injective ring homomorphism `π` into the operators on an inner-product
space with `⟪π a u, v⟫ = ⟪u, π (m a) v⟫` (the shape of `StarRepSemisimple`'s hypothesis and of
`KOSixSpectralTriple.piRep_adjoint`) forces `m x * x + m y * y = 0 → m x * x = 0`: apply `π`, read
the identity at `v`, and `‖π x v‖² + ‖π y v‖² = 0` kills `π x v` for every `v`; faithfulness kills
`x`. No finite-dimensionality, no norm on `A`. -/
theorem pointed_of_faithful_star_rep {𝕜 A H : Type*} [RCLike 𝕜] [Ring A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (m : A → A) (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (m a) v⟫_𝕜)
    (x y : A) (hxy : m x * x + m y * y = 0) : m x * x = 0 := by
  have hx0 : π x = 0 := by
    ext v
    have h1 : ⟪π x v, π x v⟫_𝕜 = ⟪v, π (m x * x) v⟫_𝕜 := by
      rw [hstar, map_mul, Module.End.mul_apply]
    have h2 : ⟪π y v, π y v⟫_𝕜 = ⟪v, π (m y * y) v⟫_𝕜 := by
      rw [hstar, map_mul, Module.End.mul_apply]
    have hsum : ⟪π x v, π x v⟫_𝕜 + ⟪π y v, π y v⟫_𝕜 = 0 := by
      rw [h1, h2, ← inner_add_right, ← LinearMap.add_apply, ← map_add, hxy, map_zero]
      simp
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hsum
    have hreal : ‖π x v‖ ^ 2 + ‖π y v‖ ^ 2 = 0 := by exact_mod_cast hsum
    have ha : ‖π x v‖ ^ 2 = 0 := by linarith [sq_nonneg ‖π x v‖, sq_nonneg ‖π y v‖]
    rw [LinearMap.zero_apply]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp ha)
  have hx : x = 0 := hinj (by rw [hx0, map_zero])
  rw [hx, mul_zero]

/-- The same, as `SeedStarPositivity.Pointed` for a ⋆-structure on `Mₙ(ℂ)`. -/
theorem pointed_of_faithful_star_rep_matrix {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (s : StarStructure n)
    (π : Matrix (Fin n) (Fin n) ℂ →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (s.map a) v⟫_𝕜) :
    Pointed s :=
  fun x y hxy => pointed_of_faithful_star_rep s.map π hinj hstar x y hxy

/-- The same, as `SeedStarPositivity.PointedA` for a `StarStrC` on any `ℂ`-algebra. -/
theorem pointedA_of_faithful_star_rep {𝕜 A H : Type*} [RCLike 𝕜] [Ring A] [Algebra ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (s : StarStrC A)
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (s.map a) v⟫_𝕜) :
    PointedA s :=
  fun x y hxy => pointed_of_faithful_star_rep s.map π hinj hstar x y hxy

/-! ## 2. So a faithful ⋆-representation of `Mₙ(ℂ)` selects the definite class -/

/-- **THE SELECTION.** A ⋆-structure on `Mₙ(ℂ)` that is the involution of a faithful
⋆-representation on an inner-product space is conjugate to the conjugate transpose: the Hilbert
space picks the definite class among the `n/2 + 1` (`StarStructurePointed`). -/
theorem conjugate_conjTransposeStar_of_faithful_star_rep [NeZero n] {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (s : StarStructure n)
    (π : Matrix (Fin n) (Fin n) ℂ →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (s.map a) v⟫_𝕜) :
    Conjugate (conjTransposeStar n) s :=
  (pointed_iff_conjugate_conjTransposeStar s).mp
    (pointed_of_faithful_star_rep_matrix s π hinj hstar)

/-- In signature form: a Hermitian twist that is ⋆-represented faithfully has `usignature P =
s(2n, 0)`. -/
theorem usignature_of_faithful_star_rep [NeZero n] {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (π : Matrix (Fin n) (Fin n) ℂ →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : Matrix (Fin n) (Fin n) ℂ) (u v : H),
      ⟪π a u, v⟫_𝕜 = ⟪u, π ((hermitianStar P hP).map a) v⟫_𝕜) :
    usignature (P : Matrix (Fin n) (Fin n) ℂ) = s(2 * n, 0) :=
  (pointed_iff_definite P hP).mp (pointed_of_faithful_star_rep_matrix _ π hinj hstar)

/-- **THE INDEFINITE CLASSES ARE NOT ⋆-REPRESENTABLE**: for `usignature P ≠ s(2n, 0)`, no injective
ring homomorphism into the operators on ANY inner-product space intertwines `hermitianStar P` with
the adjoint — the C⋆ obstruction, stated without a norm. -/
theorem not_faithful_star_rep_of_indefinite [NeZero n] {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hind : usignature (P : Matrix (Fin n) (Fin n) ℂ) ≠ s(2 * n, 0))
    (π : Matrix (Fin n) (Fin n) ℂ →+* Module.End 𝕜 H) (hinj : Function.Injective π) :
    ¬ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (u v : H),
      ⟪π a u, v⟫_𝕜 = ⟪u, π ((hermitianStar P hP).map a) v⟫_𝕜 :=
  fun hstar => hind (usignature_of_faithful_star_rep P hP π hinj hstar)

/-! ## 3. On the product, and on the seed -/

/-- **On `Mₙ(ℂ) × Mₙ(ℂ)`**: the involution of a faithful ⋆-representation is inner-conjugate to the
componentwise conjugate transpose — one class of the `(n/2 + 1)² + 1`. -/
theorem innerConjugate_prodConjTransposeC_of_faithful_star_rep [NeZero n] {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
    (π : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) →+* Module.End 𝕜 H)
    (hinj : Function.Injective π)
    (hstar : ∀ (a : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) (u v : H),
      ⟪π a u, v⟫_𝕜 = ⟪u, π (s.map a) v⟫_𝕜) :
    InnerConjugate (prodConjTransposeC n n) s :=
  (pointedA_iff_innerConjugate s).mp (pointedA_of_faithful_star_rep s π hinj hstar)

/-- **THE SEED, WITH ITS C⋆ INPUT SUPPLIED BY A REPRESENTATION**: a seed (finite-dimensional
semisimple over `ℂ`, non-commutative, `finrank = 4`) whose ⋆-structure is faithfully ⋆-represented
on an inner-product space is `M₂(ℂ)` with the conjugate transpose, up to conjugacy — unit 151's
`seed_star_conjugate_conjTransposeStar` with its `PointedA s` hypothesis discharged. -/
theorem seed_star_conjugate_conjTransposeStar_of_faithful_star_rep (A : Type*) [Ring A]
    [Algebra ℂ A] [FiniteDimensional ℂ A] [IsSemisimpleRing A]
    (hnc : ∃ a b : A, a * b ≠ b * a) (hdim : Module.finrank ℂ A = 4) (s : StarStrC A)
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (s.map a) v⟫_𝕜) :
    ∃ e : A ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ, Conjugate (transport s e) (conjTransposeStar 2) :=
  seed_star_conjugate_conjTransposeStar A hnc hdim s (pointedA_of_faithful_star_rep s π hinj hstar)

/-! ## 4. Non-vacuity: the standard representation is such a representation -/

/-- The conjugate transpose IS Mathlib's `star` on matrices. -/
theorem conjTransposeStar_map_eq_star (a : Matrix (Fin n) (Fin n) ℂ) :
    (conjTransposeStar n).map a = star a := rfl

/-- **Non-vacuity**: the standard representation `StarRepSemisimple.matrixRep` is a faithful
⋆-representation of the conjugate transpose, so §1 re-derives `pointed_conjTransposeStar` from a
representation rather than from a trace. -/
theorem pointed_conjTransposeStar_via_rep : Pointed (conjTransposeStar n) :=
  pointed_of_faithful_star_rep_matrix (conjTransposeStar n) (matrixRep n) (matrixRep_injective n)
    fun a u v => by rw [conjTransposeStar_map_eq_star]; exact matrixRep_star n a u v

end StarStructureFromRep
