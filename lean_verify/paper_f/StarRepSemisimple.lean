/-
  StarRepSemisimple.lean — a finite-dimensional ⋆-algebra with a FAITHFUL
  ⋆-representation on an inner-product space is SEMISIMPLE, and therefore a
  finite product of matrix algebras over ℝ, ℂ and ℍ.

  **SPINE link L6 (n = 4 selection), clause (b) — SPINE CAMPAIGN unit 6.**
  **This is CCM step 1, the step with the highest cascade on the spine: the L6
  audit recorded it as unblocking L8, L11, L12, L13, L16 and L18.**

  ## The gap this closes, stated as the recompute stated it

  L6's headline has two clauses. Clause (a) — among even `n ≥ 2` with
  `n² − 1 ≥ 12`, four is least — is a theorem (`CascadeMinimality.four_isLeast`),
  and the same file proves the criterion does NOT force four. Clause (b) is the
  real content: **the spectral-triple axioms force the algebra class**, so that
  `M₄(ℂ)` is derived rather than stipulated. The recompute's L6 audit found no
  covering theorem and named this as the nearest next step:

  > *a theorem that takes a finite-dimensional real ⋆-algebra with a faithful
  > ⋆-representation on a finite-dimensional Hilbert space and concludes the
  > algebra is semisimple — CCM step 1 — since every CCM-named declaration in
  > the estate checks `ℕ`-records instead.*

  Queried before writing: `grep -rln 'IsSemisimpleRing' paper_f/*.lean *.lean`
  returns `RealSimpleAlgebra`, `SeedUniqueness` and `TracelessSkewLie` (the last
  in the Lie-algebra sense), and none of the three derives semisimplicity from a
  representation — `RealSimpleAlgebra` takes `[IsSemisimpleRing A]` as a
  hypothesis. Mathlib has no such theorem either: `grep -rn 'IsSemisimpleRing'
  Mathlib/Analysis/` is empty, so nothing connects the analytic hypotheses to
  the algebraic conclusion there.

  ## What is proved

  1. **`symmetric_eq_zero_of_isNilpotent`** — a symmetric nilpotent operator on
     an inner-product space is zero. No finite-dimensionality: from
     `T ^ (2 ^ (k+1)) = 0` one gets `T ^ (2 ^ k) = 0` because
     `⟪Sv, Sv⟫ = ⟪v, S²v⟫ = 0` for `S = T ^ (2 ^ k)` symmetric. Absent from
     Mathlib (`grep -rn 'IsSymmetric' Mathlib/ | grep -i 'nilpotent'`: nothing);
     Mathlib's nearest is the C⋆ identity `IsSelfAdjoint.nnnorm_pow_two_pow`,
     which needs a `CStarRing`, and `Module.End ℂ H` is not one.
  2. **`isSemisimpleRing_of_faithful_star_rep`** — the theorem. `A` any
     **Artinian** ring with a star operation, `π : A →+* Module.End 𝕜 H` a ring
     homomorphism into the operators on an inner-product space over any
     `RCLike 𝕜`, injective, with `⟪π a u, v⟫ = ⟪u, π (star a) v⟫`. Conclusion:
     `IsSemisimpleRing A`. The proof: the Jacobson radical of an Artinian ring
     is nilpotent, so for `a` in it `star a * a` is nilpotent; its image is
     symmetric and nilpotent, hence zero; faithfulness gives `star a * a = 0`;
     positivity gives `π a = 0`; faithfulness again gives `a = 0`. So the radical
     is trivial, and an Artinian ring with trivial radical is semisimple.
     **No algebra structure, no `AlgHom`, no finite dimension of `H`.**
  3. **`isSemisimpleRing_of_faithful_star_rep_real` / `_complex`** — the two
     corollaries a spectral triple actually presents: `A` finite-dimensional over
     `ℝ` or over `ℂ` (Artinian-ness then comes from
     `IsArtinianRing.of_finite`). The real one is the case CCM is about, because
     the finite algebra of a real spectral triple is a real ⋆-algebra.
  4. **`exists_pi_matrix_of_faithful_star_rep_real`** — **CCM steps 1 and 2 over
     `ℝ`.** Composing 3 with this estate's own `RealSimpleAlgebra.exists_pi_matrix_over_three`
     (which rests on `RealDivisionQuaternionCase.frobenius`, proved here on
     1 September): a finite-dimensional real ⋆-algebra with a faithful
     ⋆-representation is `≃ₐ[ℝ]` a finite product `∏ Mₐᵢ(Dᵢ)` with each `Dᵢ` one
     of `ℝ`, `ℂ`, `ℍ`. **That is the shape CCM's classification starts from**, and
     it is now a consequence of representation-theoretic hypotheses rather than a
     posit.
  5. **`exists_pi_matrix_of_faithful_star_rep_complex`** — the same over `ℂ`
     through Mathlib's `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`:
     a product of complex matrix algebras.
  6. **`matrixRep`, `matrixRep_injective`, `matrixRep_star`,
     `matrix_isSemisimple_via_rep`** — non-vacuity,
     because a theorem whose hypotheses might be empty is worth nothing. The
     standard representation of `Mₙ(ℂ)` on `EuclideanSpace ℂ (Fin n)` satisfies
     them, read off Mathlib's `Matrix.toEuclideanCLM` — which is already a
     `StarAlgEquiv` onto the bounded operators, so injectivity and the
     ⋆-condition are its `injective` and its `map_star`. So the hypotheses hold
     for the algebra the cascade actually uses, and §2 is not a statement about
     an empty class.

  ## What is NOT proved, said exactly

  - **The KO-6 signs, the commutant condition and the order-one condition are
    NOT USED.** This theorem needs only a faithful ⋆-representation. That makes
    it weaker than CCM, whose classification uses the remaining axioms (with
    Poincaré duality and irreducibility) to cut the list of semisimple algebras
    down to `M_a(ℍ) ⊕ M_k(ℂ)` and then to `k = 2a`. **Rung 1 of the staircase,
    not the wall.** The next rung is the ⋆-structure on the product: which
    involutions a product of matrix algebras admits, and what the order-one
    condition does to the pair `(A, A°)`.
  - **`n = 4` is not selected, and neither is `ℂ ⊕ ℍ ⊕ M₃(ℂ)`.** Nothing here
    prefers one factor list to another; `ASSUMPTIONS_LEDGER` 7's three modelling
    inputs (a single `Mₙ(ℂ)`, `n` even for Poincaré duality, `n² − 1 ≥ 12` for
    Standard-Model containment) are untouched, and clause (a) still cannot supply
    "forces" (`CascadeMinimality.not_forall_eq_four`).
  - **It is not instantiated at the estate's own KO-6 triple.**
    `KOSixSpectralTriple.piRep_adjoint` has exactly the shape of `hstar` here —
    that is where the shape came from — but `KOSixSpectralTriple.Hf n` carries a
    bespoke sesquilinear form `ip` and no Mathlib `InnerProductSpace` instance, so
    the theorem cannot be applied to it without building that instance. Queried:
    `grep -n 'InnerProductSpace\|instInner' paper_f/KOSixSpectralTriple.lean` is
    empty. That instance is a unit's work and is named here rather than done.
    [**`ERRATUM 565`: the paragraph above is kept and names ONE obstacle when there
    are TWO, and the second is the harder one.** `isSemisimpleRing_of_faithful_star_rep`
    takes a `RingHom`, and `piRep` is **not** one:
    `KOSixAlgebraAction.piRep_not_additive_in_matrix` proves it is not additive in
    the matrix argument, because the antiparticle blocks are returned unchanged. So
    building the `InnerProductSpace` instance would not have been enough, and the
    sentence *"the theorem cannot be applied to it without building that instance"*
    understates the gap. The theorem IS applied to the estate's particle sector, at
    `KOSixAlgebraAction.matrix_isSemisimple_via_particleRep` — so the shape was
    right and it is the four-block extension that breaks it.]
  - **The real classification's presentation** stays as `RealSimpleAlgebra` left
    it — division algebras named rather than dispatched through a `Fin 3 → Type` —
    which is `ASSUMPTIONS_LEDGER` 49, an author's decision, and is not made here.
  - Nothing about `A` being a C⋆-algebra: no norm is assumed, and the C⋆ identity
    is not used. The argument is purely the Jacobson radical plus positivity of
    the inner product.

  ## Adversarial review, folded in

  **"Artinian is doing the work, and it is just finite-dimensionality."** It is
  finite-dimensionality, and it is doing half the work — the half that says the
  radical is nilpotent. The other half is the ⋆-representation, and without it the
  statement is false: `ℂ[x]/(x²)` is finite-dimensional over `ℂ` and not
  semisimple. What the representation buys is that a nilpotent element's image is
  a symmetric nilpotent operator, which the inner product kills.

  **"The hypothesis `⟪π a u, v⟫ = ⟪u, π (star a) v⟫` with `star` unconstrained is
  vacuous nonsense."** It constrains `star` to be the adjoint under `π`, which is
  all the proof uses: `star (star a * a) = star a * a` needs `star_mul` and
  `star_star`, which `StarRing` supplies, and nothing else about `star` appears.
  The involution is not assumed isometric, positive, or continuous.

  **"The `show` in §4 changes the goal."** It did, and the build's style linter said
  so; it is a `change`. Recorded because the baseline is 76 warnings of 76 and this
  file must not move it.

  **"`Module.End` versus `H →ₗ H` is a trap."** They are the same type; the ring
  structure is on `Module.End`, so `π` is stated into `Module.End 𝕜 H` and
  `map_mul` reads `π (a * b) = π a ∘ₗ π b`. `Module.End.mul_apply` is the rewrite
  that turns the product back into composition — `LinearMap.mul_apply` does not
  exist in the pinned Mathlib, which is the one name this file got wrong first.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import RealSimpleAlgebra
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace StarRepSemisimple

open scoped InnerProductSpace

/-! ## 1. A symmetric nilpotent operator is zero -/

/-- **A SYMMETRIC NILPOTENT OPERATOR ON AN INNER-PRODUCT SPACE IS ZERO.** No
finite-dimensionality: if `S := T ^ (2 ^ k)` is symmetric with `S * S = 0` then
`⟪S v, S v⟫ = ⟪v, (S * S) v⟫ = 0` for every `v`, so `S = 0`; halving the exponent
down from `2 ^ m ≥ m` gives `T = 0`.

Absent from Mathlib: its nearest statement is the C⋆-algebra identity
`IsSelfAdjoint.nnnorm_pow_two_pow`, which needs a `CStarRing` instance that
`Module.End 𝕜 H` does not have. -/
theorem symmetric_eq_zero_of_isNilpotent {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E}
    (hT : T.IsSymmetric) (hn : IsNilpotent T) : T = 0 := by
  obtain ⟨m, hm⟩ := hn
  have h2 : T ^ (2 ^ m) = 0 := pow_eq_zero_of_le (Nat.lt_two_pow_self).le hm
  have key : ∀ k : ℕ, T ^ (2 ^ k) = 0 → T = 0 := by
    intro k
    induction k with
    | zero => intro h; simpa using h
    | succ k ih =>
      intro h
      apply ih
      have hsq : (T ^ (2 ^ k)) * (T ^ (2 ^ k)) = 0 := by
        rw [← pow_add, ← two_mul, ← pow_succ']
        exact h
      ext v
      have hs := hT.pow (2 ^ k)
      have hzero : ⟪(T ^ (2 ^ k)) v, (T ^ (2 ^ k)) v⟫_𝕜 = 0 := by
        rw [hs, ← Module.End.mul_apply, hsq]
        simp
      simpa using inner_self_eq_zero.mp hzero
  exact key m h2

/-! ## 2. The theorem: a faithful ⋆-representation makes an Artinian ring semisimple -/

/-- **CCM STEP 1.** An Artinian ring with a star operation that admits a FAITHFUL
ring homomorphism into the operators on an inner-product space, intertwining the
star with the adjoint, is SEMISIMPLE.

The `⋆`-condition is stated as the inner-product identity
`⟪π a u, v⟫ = ⟪u, π (star a) v⟫`, which is exactly the shape of the estate's own
`KOSixSpectralTriple.piRep_adjoint`. Neither an algebra structure on `A` nor
finite-dimensionality of `H` is needed. -/
theorem isSemisimpleRing_of_faithful_star_rep
    {𝕜 A H : Type*} [RCLike 𝕜] [Ring A] [StarRing A] [IsArtinianRing A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (star a) v⟫_𝕜) :
    IsSemisimpleRing A := by
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson]
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [Ideal.jacobson_bot] at hn
  refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
  -- `star a * a` lies in the radical, hence is nilpotent
  have hb : star a * a ∈ Ring.jacobson A := Ideal.mul_mem_left _ _ ha
  have hbn : IsNilpotent (star a * a) := ⟨n, by
    have hmem := Ideal.pow_mem_pow hb n
    rw [hn] at hmem
    simpa using hmem⟩
  -- its image is symmetric, because `star (star a * a) = star a * a`
  have hsym : (π (star a * a)).IsSymmetric := fun u v => by
    rw [hstar]
    simp [star_mul]
  -- symmetric and nilpotent, hence zero; faithfulness transports that back
  have hπb : π (star a * a) = 0 :=
    symmetric_eq_zero_of_isNilpotent hsym (hbn.map π)
  have hb0 : star a * a = 0 := hinj (by rw [hπb, map_zero])
  -- positivity of the inner product then kills `π a`, and faithfulness kills `a`
  have hπa : π a = 0 := by
    ext v
    have hzero : ⟪π a v, π a v⟫_𝕜 = 0 := by
      rw [hstar, ← Module.End.mul_apply, ← map_mul, hb0, map_zero]
      simp
    simpa using inner_self_eq_zero.mp hzero
  exact hinj (by rw [hπa, map_zero])

/-- The same with the ⋆-condition through `LinearMap.adjoint` (which needs `H`
finite-dimensional, as the adjoint of a bare linear map does). -/
theorem isSemisimpleRing_of_faithful_star_rep_adjoint
    {𝕜 A H : Type*} [RCLike 𝕜] [Ring A] [StarRing A] [IsArtinianRing A]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ a : A, π (star a) = LinearMap.adjoint (π a)) :
    IsSemisimpleRing A :=
  isSemisimpleRing_of_faithful_star_rep π hinj fun a u v => by
    rw [hstar, LinearMap.adjoint_inner_right]

/-- The real case — the one a real spectral triple presents. -/
theorem isSemisimpleRing_of_faithful_star_rep_real
    {𝕜 A H : Type*} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra ℝ A]
    [Module.Finite ℝ A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (star a) v⟫_𝕜) :
    IsSemisimpleRing A :=
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℝ A
  isSemisimpleRing_of_faithful_star_rep π hinj hstar

/-- The complex case. -/
theorem isSemisimpleRing_of_faithful_star_rep_complex
    {𝕜 A H : Type*} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra ℂ A]
    [Module.Finite ℂ A] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (star a) v⟫_𝕜) :
    IsSemisimpleRing A :=
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℂ A
  isSemisimpleRing_of_faithful_star_rep π hinj hstar

/-! ## 3. CCM steps 1 and 2: the algebra CLASS from the representation -/

open Quaternion in
/-- **THE ALGEBRA CLASS, FROM A FAITHFUL ⋆-REPRESENTATION.** A finite-dimensional
real ⋆-algebra with a faithful ⋆-representation on an inner-product space is
`≃ₐ[ℝ]` a finite product of matrix algebras over division algebras each of which
is `ℝ`, `ℂ` or `ℍ`.

This is the shape Chamseddine–Connes–Marcolli's classification of finite real
spectral triples STARTS from, and here it is a consequence of the
representation-theoretic hypotheses rather than a posit. The Wedderburn half is
Mathlib's; the identification of the division algebras is this estate's
`RealDivisionQuaternionCase.frobenius`.

**It does not select a factor list.** Cutting the list down to `M_a(ℍ) ⊕ M_k(ℂ)`
uses axioms this theorem never sees — the KO-6 signs, the order-one condition,
Poincaré duality — and that is rung 2, not this one. -/
theorem exists_pi_matrix_of_faithful_star_rep_real
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A : Type u) [Ring A] [StarRing A] [Algebra ℝ A] [Module.Finite ℝ A]
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (star a) v⟫_𝕜) :
    ∃ (n : ℕ) (D : Fin n → Type u) (d : Fin n → ℕ) (_ : ∀ i, DivisionRing (D i))
      (_ : ∀ i, Algebra ℝ (D i)),
      (∀ i, Nonempty (ℝ ≃ₐ[ℝ] D i) ∨ Nonempty (ℂ ≃ₐ[ℝ] D i) ∨
        Nonempty (ℍ[ℝ] ≃ₐ[ℝ] D i)) ∧
      Nonempty (A ≃ₐ[ℝ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  haveI : IsSemisimpleRing A :=
    isSemisimpleRing_of_faithful_star_rep_real π hinj hstar
  RealSimpleAlgebra.exists_pi_matrix_over_three A

/-- The complex counterpart, through Mathlib's algebraically-closed Wedderburn:
a finite-dimensional complex ⋆-algebra with a faithful ⋆-representation is a
finite product of COMPLEX matrix algebras. -/
theorem exists_pi_matrix_of_faithful_star_rep_complex
    {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] [FiniteDimensional ℂ A]
    (π : A →+* Module.End 𝕜 H) (hinj : Function.Injective π)
    (hstar : ∀ (a : A) (u v : H), ⟪π a u, v⟫_𝕜 = ⟪u, π (star a) v⟫_𝕜) :
    ∃ (n : ℕ) (d : Fin n → ℕ), (∀ i, NeZero (d i)) ∧
      Nonempty (A ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :=
  haveI : IsSemisimpleRing A :=
    isSemisimpleRing_of_faithful_star_rep_complex π hinj hstar
  IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ A

/-! ## 4. Non-vacuity: the hypotheses hold for the cascade's own algebra -/

/-- The standard representation of `Mₙ(ℂ)` on `EuclideanSpace ℂ (Fin n)` as a ring
homomorphism, read off Mathlib's `Matrix.toEuclideanCLM`, which is already a
`StarAlgEquiv` onto the bounded operators. -/
noncomputable def matrixRep (n : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →+* Module.End ℂ (EuclideanSpace ℂ (Fin n)) where
  toFun A := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A : _ →ₗ[ℂ] _)
  map_one' := by simp
  map_mul' _ _ := by simp
  map_zero' := by simp
  map_add' _ _ := by simp

theorem matrixRep_injective (n : ℕ) : Function.Injective (matrixRep n) := fun _ _ h =>
  Matrix.toEuclideanCLM.injective (ContinuousLinearMap.coe_injective h)

/-- **THE HYPOTHESES ARE NOT EMPTY.** The standard representation of `Mₙ(ℂ)`
satisfies the ⋆-condition of §2, with the conjugate transpose as the star: this is
`Matrix.toEuclideanCLM`'s own `map_star` together with
`ContinuousLinearMap.adjoint_inner_right`. -/
theorem matrixRep_star (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) :
    ⟪matrixRep n A u, v⟫_ℂ = ⟪u, matrixRep n (star A) v⟫_ℂ := by
  have h : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (star A))
      = ContinuousLinearMap.adjoint
          (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
    rw [map_star]; rfl
  change ⟪(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) u, v⟫_ℂ
      = ⟪u, (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (star A)) v⟫_ℂ
  rw [h, ContinuousLinearMap.adjoint_inner_right]

/-- The theorem applied to the cascade's own matrix algebra: `Mₙ(ℂ)` is semisimple
BECAUSE it carries a faithful ⋆-representation, not because Mathlib declares it so.
A sanity instance; its point is that §2's hypotheses are satisfiable at the object
the cascade uses, so the theorem above is not a statement about an empty class. -/
theorem matrix_isSemisimple_via_rep (n : ℕ) :
    IsSemisimpleRing (Matrix (Fin n) (Fin n) ℂ) :=
  isSemisimpleRing_of_faithful_star_rep_complex (𝕜 := ℂ)
    (H := EuclideanSpace ℂ (Fin n)) (matrixRep n) (matrixRep_injective n)
    (matrixRep_star n)

end StarRepSemisimple
