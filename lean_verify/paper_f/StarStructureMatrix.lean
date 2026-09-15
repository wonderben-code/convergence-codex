/-
  StarStructureMatrix: every ⋆-structure on `Mₙ(ℂ)` is the conjugate transpose twisted by an
  inner automorphism

  SPINE LINK L11 — `SPINE.md`'s Caesar item **2 of the remaining order**, in its own words:
  *"With Skolem–Noether in hand, the next honest step is the ⋆-structure on a product of matrix
  algebras — the same rung as L6's, approached from the cascade side."* This unit takes the
  single-factor case, which is the whole of the difficulty: the product case is a direct sum and
  the involution either fixes a factor or swaps two.

  WHY IT IS THE RUNG. Both L6 and L11 arrive at the same question from opposite ends. L6 climbs
  from spectral-triple axioms: rung 1 gives a product `∏ Mₐᵢ(Dᵢ)` and rung 2 asks **which
  involutions that product admits**. L11 descends from the cascade: `M₁₆` decomposes as
  `M₄ ⊗ M₂ ⊗ M₂` and every other `abc = 16` equally, and what could prefer one is the
  ⋆-structure. **Neither link can move without a classification of involutions on a matrix
  algebra, and this estate had none.**

  WHAT IS PROVED.
  * **`StarStructure`** — the structure itself: a conjugate-linear, ANTI-multiplicative
    involution of `Mₙ(ℂ)`. Unitality is not a field; `map_one` derives it, because
    `map 1 * map X = map (X * 1) = map X` and `map` is surjective, so `map 1` is a left identity
    on everything.
  * **`toAlgEquiv`** — `X ↦ (s X)ᴴ` is a `ℂ`-ALGEBRA automorphism. Two cancellations do the
    work: anti-multiplicative composed with anti-multiplicative is multiplicative, and
    conjugate-linear composed with conjugate-linear is `ℂ`-linear. Its inverse is `X ↦ s (Xᴴ)`.
  * **`exists_inner_conjTranspose`** — **the classification.** Feeding `toAlgEquiv` to this
    estate's own `SkolemNoether.skolemNoether`:

    > every ⋆-structure on `Mₙ(ℂ)` is `X ↦ (P X P⁻¹)ᴴ` for an invertible `P`.

  * **`matrix_center_scalar`** — an aside that is also a correction. `SPINE.md`'s L11 row says
    the missing ingredient for `Aut(Mₙ) ≅ PGLₙ` is the centre of `Mₙ(K)`, and that *"the pinned
    Mathlib has no `Matrix.mem_center_iff`"*. **The second clause is true and the first no longer
    blocks anything**: `Module.End.mem_center_iff` DOES exist, for any free module, and
    `Matrix.toLinAlgEquiv (Pi.basisFun K (Fin n))` transports it to matrices in eight lines. The
    centre of `Mₙ(K)` is the scalars, proved here.
  * **`involution_forces_central`** and **`involution_scalar`** — what involutivity costs. From
    `s (s X) = X` for all `X`, the matrix `Q := (Pᴴ)⁻¹ * P` commutes with everything, so it is a
    scalar: `P = c • Pᴴ`. **That is the fork the classification of real forms runs through** —
    over `ℝ` the two signs of an analogous constant separate `Mₙ(ℝ)` from `Mₙ(ℍ)` — and it is
    obtained here as a consequence rather than posited.
  * **`conjTransposeStar`** and **`starStructure_inhabited`** — the conjugate transpose is a
    `StarStructure`, so nothing above is vacuous. `ERRATUM 557` is the reason this is exhibited
    rather than assumed.

  WHAT IS **NOT** CLAIMED.
  * **The PRODUCT case is not done.** The header's first paragraph says the single factor is the
    whole difficulty; that is a claim about the shape of the remaining work, not a theorem, and
    no statement here quantifies over `∏ Mₐᵢ(Dᵢ)`.
  * **`|c| = 1` and the Hermitian normalisation are NOT proved.** `involution_scalar` gives
    `P = c • Pᴴ`; that forces `|c| = 1`, and rescaling `P` by a square root of `c` would make it
    Hermitian without changing the inner automorphism. **Neither step is here**, so the
    orthogonal/symplectic fork is located and not taken.
  * **No real forms.** Everything is over `ℂ`. `Mₙ(ℝ)` and `Mₙ(ℍ)` appear nowhere, and the
    sentence above about the two signs is a pointer to the classical statement, not to a theorem
    of this estate.
  * **Nothing about the cascade is cut.** `a·b·c = 16` still has the alternatives `SPINE.md`'s
    L11 row records; this unit supplies the object that could cut them and does not cut them.
    Cascade depth, which factor decomposes, and `b = 2` remain postulates
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35).
  * **`Aut(Mₙ) ≅ PGLₙ` is still not stated.** The centre is now available, which was the half
    L11's row named; the statement itself is not written.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import SkolemNoether

namespace StarStructureMatrix

open Matrix

noncomputable section

variable {n : ℕ}

/-! ## 1. The structure -/

/-- A **⋆-structure on `Mₙ(ℂ)`**: conjugate-linear, ANTI-multiplicative, involutive. Unitality
is deliberately not a field — `map_one` derives it. -/
structure StarStructure (n : ℕ) where
  /-- The involution. -/
  map : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ
  /-- Additive. -/
  map_add : ∀ X Y, map (X + Y) = map X + map Y
  /-- CONJUGATE-linear, which is what makes this a ⋆-structure rather than an anti-automorphism. -/
  map_smul : ∀ (c : ℂ) (X), map (c • X) = (starRingEnd ℂ) c • map X
  /-- ANTI-multiplicative. -/
  map_mul : ∀ X Y, map (X * Y) = map Y * map X
  /-- Involutive, hence bijective. -/
  map_involutive : ∀ X, map (map X) = X

variable (s : StarStructure n)

theorem map_bijective : Function.Bijective s.map :=
  Function.bijective_iff_has_inverse.mpr ⟨s.map, s.map_involutive, s.map_involutive⟩

/-- **Unitality is a consequence, not an axiom.** `map 1 * map X = map (X * 1) = map X` for
every `X`, and `map` is onto, so `map 1` is a left identity on all of `Mₙ(ℂ)`. -/
theorem map_one : s.map 1 = 1 := by
  have h : ∀ Y, s.map 1 * Y = Y := by
    intro Y
    obtain ⟨X, hX⟩ := (map_bijective s).surjective Y
    rw [← hX, ← s.map_mul, mul_one]
  simpa using h 1

/-! ## 2. Conjugate transpose twisted by an algebra automorphism -/

/-- **`X ↦ (s X)ᴴ` is a `ℂ`-ALGEBRA automorphism.** Anti-multiplicative twice is
multiplicative; conjugate-linear twice is `ℂ`-linear. The inverse is `X ↦ s (Xᴴ)`. -/
def toAlgEquiv : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ where
  toFun X := (s.map X)ᴴ
  invFun X := s.map Xᴴ
  left_inv X := by
    simp only [Matrix.conjTranspose_conjTranspose, s.map_involutive]
  right_inv X := by
    simp only [s.map_involutive, Matrix.conjTranspose_conjTranspose]
  map_mul' X Y := by
    simp only [s.map_mul, Matrix.conjTranspose_mul]
  map_add' X Y := by
    simp only [s.map_add, Matrix.conjTranspose_add]
  commutes' c := by
    have h : (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) = algebraMap ℂ _ c := by
      simp [Algebra.algebraMap_eq_smul_one]
    simp only [← h, s.map_smul, map_one s, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one]
    simp

@[simp] theorem toAlgEquiv_apply (X : Matrix (Fin n) (Fin n) ℂ) :
    toAlgEquiv s X = (s.map X)ᴴ := rfl

/-- **THE CLASSIFICATION.** Every ⋆-structure on `Mₙ(ℂ)` is the conjugate transpose twisted by
an inner automorphism — from this estate's own `SkolemNoether.skolemNoether`, which is what
makes the step available at all. -/
theorem exists_inner_conjTranspose [NeZero n] :
    ∃ P : (Matrix (Fin n) (Fin n) ℂ)ˣ,
      ∀ X, s.map X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
        * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  obtain ⟨P, hP⟩ := SkolemNoether.skolemNoether ℂ n (toAlgEquiv s)
  refine ⟨P, fun X => ?_⟩
  have h := hP X
  rw [toAlgEquiv_apply] at h
  rw [← h, Matrix.conjTranspose_conjTranspose]

/-! ## 3. The centre of a matrix algebra, and an aside that is a correction -/

/-- **The centre of `Mₙ(K)` is the scalars.** `SPINE.md`'s L11 row names this as the missing
half of `Aut(Mₙ) ≅ PGLₙ` and says *"the pinned Mathlib has no `Matrix.mem_center_iff`"*. **That
clause is true and it was never the obstacle**: `Module.End.mem_center_iff` exists for any FREE
module, and `Matrix.toLinAlgEquiv (Pi.basisFun K (Fin n))` transports it. Eight lines, and the
transport direction that matters is surjectivity of the equivalence — the centre condition has
to be checked against every endomorphism, and every endomorphism is a matrix. -/
theorem matrix_center_scalar {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (h : ∀ A : Matrix (Fin m) (Fin m) K, M * A = A * M) :
    ∃ c : K, M = c • (1 : Matrix (Fin m) (Fin m) K) := by
  have hc : (Matrix.toLinAlgEquiv (Pi.basisFun K (Fin m)) M) ∈
      Set.center (Module.End K (Fin m → K)) := by
    refine Semigroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨B, hB⟩ := (Matrix.toLinAlgEquiv (Pi.basisFun K (Fin m))).surjective g
    rw [← hB, ← map_mul, ← map_mul, h]
  obtain ⟨c, _, hcc⟩ := Module.End.mem_center_iff.mp hc
  refine ⟨c, (Matrix.toLinAlgEquiv (Pi.basisFun K (Fin m))).injective ?_⟩
  rw [hcc, map_smul, _root_.map_one]
  rfl

/-! ## 4. What involutivity costs -/

/-- **Involutivity forces `P⁻¹ Pᴴ` to commute with everything.** Written with no matrix
inverse: the only cancellations used are `Pᴴ (P⁻¹)ᴴ = (P⁻¹ P)ᴴ = 1` and its mirror, so `P`
enters only through the unit it already is. The round trip is `X ↦ R X R'` with `R = P⁻¹ Pᴴ`,
`R' = (P⁻¹)ᴴ P` and `R R' = R' R = 1`; demanding it be the identity gives `X R = R X`. -/
theorem involution_forces_central (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : ∀ X, s.map X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
      * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    A * (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (P : Matrix (Fin n) (Fin n) ℂ)ᴴ)
      = (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (P : Matrix (Fin n) (Fin n) ℂ)ᴴ) * A := by
  set Q : Matrix (Fin n) (Fin n) ℂ := (P : Matrix (Fin n) (Fin n) ℂ) with hQ
  set Qi : Matrix (Fin n) (Fin n) ℂ :=
    ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) with hQi
  have h1 : Q * Qi = 1 := by simp [hQ, hQi]
  have h2 : Qi * Q = 1 := by simp [hQ, hQi]
  have h3 : Qᴴ * Qiᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have h4 : Qiᴴ * Qᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  -- the round trip, with both conjugate transposes expanded
  have hrt : Qiᴴ * (Q * A * Qi) * Qᴴ = A := by
    have := s.map_involutive A
    rw [hP, hP] at this
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using this
  -- peel the outer factors off `hrt`
  have hmid : Q * A * Qi = Qᴴ * A * Qiᴴ := by
    have := congrArg (fun M => Qᴴ * M * Qiᴴ) hrt
    simp only at this
    calc Q * A * Qi
        = Qᴴ * Qiᴴ * (Q * A * Qi) * (Qᴴ * Qiᴴ) := by rw [h3, Matrix.one_mul, Matrix.mul_one]
      _ = Qᴴ * (Qiᴴ * (Q * A * Qi) * Qᴴ) * Qiᴴ := by
          simp only [Matrix.mul_assoc]
      _ = Qᴴ * A * Qiᴴ := by rw [hrt]
  -- and turn it into the commutation statement
  calc A * (Qi * Qᴴ)
      = Qi * (Q * A * Qi) * Qᴴ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Qi Q, h2, Matrix.one_mul]
    _ = Qi * (Qᴴ * A * Qiᴴ) * Qᴴ := by rw [hmid]
    _ = (Qi * Qᴴ) * A * (Qiᴴ * Qᴴ) := by simp only [Matrix.mul_assoc]
    _ = (Qi * Qᴴ) * A := by rw [h4, Matrix.mul_one]

/-- **The fork.** `P⁻¹ Pᴴ` is a scalar, so `Pᴴ = c • P`. **Over `ℝ` the two signs of the
analogous constant are what separate `Mₙ(ℝ)` from `Mₙ(ℍ)`** — the orthogonal from the
symplectic case — and here that constant is obtained as a consequence of involutivity rather
than posited. What is NOT proved: that `|c| = 1`, nor the rescaling of `P` that would make it
Hermitian. So the fork is located, not taken. -/
theorem involution_scalar (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : ∀ X, s.map X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
      * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ) :
    ∃ c : ℂ, (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = c • (P : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨c, hc⟩ := matrix_center_scalar
    (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      * (P : Matrix (Fin n) (Fin n) ℂ)ᴴ)
    (fun A => (involution_forces_central s P hP A).symm)
  refine ⟨c, ?_⟩
  have h1 : (P : Matrix (Fin n) (Fin n) ℂ)
      * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    simp
  calc (P : Matrix (Fin n) (Fin n) ℂ)ᴴ
      = (P : Matrix (Fin n) (Fin n) ℂ)
        * (((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
          * (P : Matrix (Fin n) (Fin n) ℂ)ᴴ) := by
        rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    _ = c • (P : Matrix (Fin n) (Fin n) ℂ) := by
        rw [hc, Matrix.mul_smul, Matrix.mul_one]

/-! ## 5. The structure is inhabited -/

/-- The conjugate transpose is a `StarStructure`, so nothing above is vacuous. Exhibited
because a structure nobody can instantiate is a vacuous object (`ERRATUM 557`). -/
def conjTransposeStar (m : ℕ) : StarStructure m where
  map X := Xᴴ
  map_add X Y := Matrix.conjTranspose_add X Y
  map_smul c X := by simp [Matrix.conjTranspose_smul]
  map_mul X Y := Matrix.conjTranspose_mul X Y
  map_involutive X := Matrix.conjTranspose_conjTranspose X

theorem starStructure_inhabited (m : ℕ) : Nonempty (StarStructure m) :=
  ⟨conjTransposeStar m⟩

end

end StarStructureMatrix
