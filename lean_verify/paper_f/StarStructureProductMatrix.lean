/-
  StarStructureProductMatrix: the classification of ⋆-structures on `Mₘ(ℂ) × Mₖ(ℂ)`, both
  branches, with nothing left existential

  SPINE LINKS L6 and L11. `UNLOCK_WATCHLIST` 266's item (2), the two residues the unit before
  this one named and explicitly did not close.

  WHAT WAS LEFT OPEN, in that unit's own words. `StarStructureProduct` proved the dichotomy —
  a ⋆-structure on `B × C` fixes the two factors or swaps them — and then said two things were
  missing: *"the swap case is not classified … it is NOT shown that matrix factors must have
  equal size; `Mₘ(ℂ) ≃ Mₖ(ℂ)ᵐᵒᵖ` forcing `m = k` is a dimension count this file does not do"*,
  and *"the restrictions are not composed with the single-factor result, so nothing states the
  combined classification"*, with the reason for the second spelled out: the restrictions land in
  `StarStr`, which has **forgotten the conjugate-linearity**, so `map_smul` has to be carried
  through the restriction before a composition can even be stated. **This file does both.**

  THE ONE NEW PIECE OF STRUCTURE. `StarStrC A` is `StarStructureProduct.StarStr A` plus
  `map_smul` — conjugate-linearity — over a `ℂ`-algebra. It is deliberately NOT a new notion at a
  single matrix factor: `toStarStructure` and `ofStarStructure` are field-for-field both ways, so
  `StarStrC (Mₙ(ℂ))` and `StarStructureMatrix.StarStructure n` are the same thing and the
  single-factor classification applies to either. The point of `StarStrC` is that it exists **on a
  product**, which `StarStructure n` cannot state.

  THE SWAP CASE IS NOW CLASSIFIED, and the dimension count is over `ℂ` rather than `ℝ`.
  * **`swapLin`** — `StarStructureProduct.swapMap` is additive and anti-multiplicative and, with
    `map_smul`, conjugate-linear; **post-composing it with the conjugate transpose makes it
    `ℂ`-LINEAR**, because antilinear twice is linear. That is the whole trick, and it is why no
    real structure and no `IsScalarTower` appears anywhere below. The naive route counts
    `finrank ℝ = 2m²` and needs `ℝ` to act on a complex matrix algebra, which is the shape
    `UNLOCK_WATCHLIST` 261 measured and found blocked: at `H = EuclideanSpace ℂ ι`,
    `IsScalarTower ℝ ℂ H` is TRUE by `mul_assoc` and **instance search will not use it**,
    because there are two `Module ℝ` paths. This route never leaves `ℂ`, so the question does
    not arise — which is worth recording as a technique and not only as a proof.
  * **`swapLin_bijective`** — `swapMap` is bijective (`StarStructureProduct.swapMap_bijective`)
    and the conjugate transpose is an involution, so the composite is bijective.
  * **`swap_forces_eq_size`** — therefore `Mₘ(ℂ) ≃ₗ[ℂ] Mₖ(ℂ)`, so `m * m = k * k` by
    `Module.finrank_matrix`, so **`m = k`**. The swapping branch of the dichotomy is empty unless
    the two factors have the same size.

  THE FIXING CASE IS NOW COMPOSED WITH THE SINGLE-FACTOR RESULT.
  * **`restrictLeftC`** and **`restrictRightC`** carry `map_smul` through the restriction:
    `(c • X, 0) = c • (X, 0)`, so conjugate-linearity of `s` is conjugate-linearity of the
    restriction. That is the one line the previous unit was missing.
  * **`StarStructureProduct.map_eq_of_fixes`**, added to that file in this unit, is the other
    half and it is a STRENGTHENING rather than a lemma: the two restrictions **determine** `s`,
    they do not merely bound it. `(b, c) = (b, 0) + (0, c)` and each summand's image has one
    component zero.
  * **`fixing_classification`** — so in the fixing case
    `s (X, Y) = (twist P X, twist Q Y)` — that is, `((P X P⁻¹)ᴴ, (Q Y Q⁻¹)ᴴ)` — for
    **Hermitian** units `P` and `Q`, by applying
    `StarStructureHermitian.exists_hermitian_twist` to each restriction.

  AND **`matrixProd_classification`** is the two branches in one statement, with the swap branch
  carrying `m = k` rather than an unanalysed existential.

  AND AT UNEQUAL SIZES THERE IS ONLY ONE BRANCH, which is the form the cascade side wants.
  * **`fixes_of_ne_size`** — if `m ≠ k` then EVERY ⋆-structure on `Mₘ(ℂ) × Mₖ(ℂ)` fixes the two
    factors, because the swapping branch would force the sizes equal. **Said carefully for the
    cascade**, because the loose version of this sentence is false and I wrote it five times
    before catching it (`ERRATUM 578`): `M₁₆` as `M₄ ⊗ M₂ ⊗ M₂` has
    factor sizes `4, 2, 2`, which are NOT all distinct. What follows is that no involution can
    exchange the `M₄` factor with either `M₂` — those pairs have unequal sizes — and **nothing
    here forbids exchanging the two `M₂` factors with each other**; `prodSwapTransposeC` shows
    such an exchange exists at every equal size. So the only exchange the size count leaves open
    in that factorisation is the one between the two equal factors.
  * **`classification_of_ne_size`** — so at `m ≠ k` the classification is a **normal form and
    not a disjunction**: `s (X, Y) = (twist P X, twist Q Y)` for Hermitian units `P` and `Q`.

  WHAT IS **NOT** CLAIMED.
  * **Two factors, not `n`.** Unchanged, and this is now the ONLY thing left of the two-factor
    story: `∏ᵢ Mₐᵢ(Dᵢ)` needs an induction that is not written, and permuting `n` minimal central
    idempotents is a different statement from a two-element case split.
  * **The swap branch is shown to force `m = k` and is not otherwise described.** No normal form
    for a swapping ⋆-structure is given: `prodSwapTranspose` exhibits one at every size, and
    nothing here says every swapping structure is that one twisted, which would be the analogue
    of `exists_hermitian_twist` for the swap branch.
  * **`P` and `Q` are not pinned down.** The single-factor residue is unchanged — a Hermitian
    form up to scalars, that is, a signature — and it is not computed, so two ⋆-structures are
    still neither shown equivalent nor shown inequivalent. The product classification is exactly
    as sharp as the single-factor one and no sharper.
  * **Real and quaternionic factors do not appear.** Everything is over `ℂ`, and
    `exists_hermitian_twist` needs `ℂ` algebraically closed, which is where the real-form story
    differs.
  * **Nothing about the cascade is cut.** `a·b·c = 16` keeps every alternative
    (`ASSUMPTIONS_LEDGER` 5, 10, 11, 30, 35). The classification now says what a ⋆-structure on a
    two-factor product looks like; it still does not prefer one factorisation of `M₁₆`, and L6's
    rung 2 is not climbed.

  AND THE THREE-FILE DEVELOPMENT STILL NEVER USES A MATRIX INVERSE OPERATION, only units.
  `StarStructureMatrix` recorded that for itself and `StarStructureHermitian` extended it to two
  files; every `⁻¹` below is `Units.inv` in `(Mₙ(ℂ))ˣ`, and Mathlib's matrix inverse (the `Inv`
  instance, `nonsing_inv`) and `Ring.inverse` appear in none of the three — grepped, not assumed.

  0 sorry. 0 new axioms. 23 declarations, every one of them on
  `[propext, Classical.choice, Quot.sound]` — and unlike `StarStructureProduct`, where 15 of 28
  needed fewer, here the census is uniform, because `Algebra ℂ A` and `Module.finrank` reach the
  full three everywhere. That contrast is the point of the two files being separate: the
  dichotomy is cheap and scalar-free, and the classification is not.
-/

import StarStructureHermitian

namespace StarStructureProductMatrix

open Matrix StarStructureProduct

noncomputable section

/-! ## 1. A ⋆-structure that remembers the scalars, on any ℂ-algebra -/

/-- A **⋆-structure on a `ℂ`-algebra**: `StarStructureProduct.StarStr` plus conjugate-linearity.
The parent is an involution of an arbitrary ring, which is all the product dichotomy needs; this
adds back the one field the single-factor classification uses. -/
structure StarStrC (A : Type*) [Ring A] [Algebra ℂ A] extends StarStr A where
  /-- CONJUGATE-linear, which is what makes this a ⋆-structure rather than an anti-automorphism. -/
  map_smul : ∀ (c : ℂ) (x : A), map (c • x) = (starRingEnd ℂ) c • map x

variable {n m k : ℕ}

/-- At a single matrix factor the two notions are the same, field for field. -/
def toStarStructure (s : StarStrC (Matrix (Fin n) (Fin n) ℂ)) :
    StarStructureMatrix.StarStructure n where
  map := s.map
  map_add := s.map_add
  map_smul := s.map_smul
  map_mul := s.map_mul
  map_involutive := s.map_involutive

/-- The other direction, so nothing is gained or lost by passing through `StarStrC`. -/
def ofStarStructure (s : StarStructureMatrix.StarStructure n) :
    StarStrC (Matrix (Fin n) (Fin n) ℂ) where
  map := s.map
  map_add := s.map_add
  map_smul := s.map_smul
  map_mul := s.map_mul
  map_involutive := s.map_involutive

@[simp] theorem toStarStructure_map (s : StarStrC (Matrix (Fin n) (Fin n) ℂ)) (X) :
    (toStarStructure s).map X = s.map X := rfl

@[simp] theorem ofStarStructure_map (s : StarStructureMatrix.StarStructure n) (X) :
    (ofStarStructure s).map X = s.map X := rfl

/-! ## 2. The restrictions carry the scalars -/

variable {B C : Type*} [Ring B] [Ring C] [Algebra ℂ B] [Algebra ℂ C]

/-- **The one line the previous unit was missing.** `(c • b, 0) = c • (b, 0)` in `B × C`, so
conjugate-linearity of `s` restricts along with the rest. -/
def restrictLeftC (s : StarStrC (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) : StarStrC B where
  toStarStr := restrictLeft s.toStarStr hfix
  map_smul c b := by
    have h : ((c • b : B), (0 : C)) = c • (b, (0 : C)) := by
      refine Prod.ext ?_ ?_ <;> simp
    change (s.map ((c • b : B), (0 : C))).1 = _
    rw [h, s.map_smul]
    rfl

/-- The mirror. -/
def restrictRightC (s : StarStrC (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) : StarStrC C where
  toStarStr := restrictRight s.toStarStr hfix
  map_smul c x := by
    have h : ((0 : B), (c • x : C)) = c • ((0 : B), x) := by
      refine Prod.ext ?_ ?_ <;> simp
    change (s.map ((0 : B), (c • x : C))).2 = _
    rw [h, s.map_smul]
    rfl

@[simp] theorem restrictLeftC_map (s : StarStrC (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) (b : B) :
    (restrictLeftC s hfix).map b = (s.map (b, (0 : C))).1 := rfl

@[simp] theorem restrictRightC_map (s : StarStrC (B × C))
    (hfix : s.map ((1 : B), (0 : C)) = ((1 : B), (0 : C))) (x : C) :
    (restrictRightC s hfix).map x = (s.map ((0 : B), x)).2 := rfl

/-! ## 3. The swapping case forces the two sizes to agree -/

/-- **Antilinear twice is linear.** `swapMap` is conjugate-linear, the conjugate transpose is
conjugate-linear, so their composite is a `ℂ`-LINEAR map `Mₘ(ℂ) → Mₖ(ℂ)`. No real scalars and no
`IsScalarTower` appear; the count below never leaves `ℂ`. -/
def swapLin (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ)) :
    Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ where
  toFun X := (swapMap s.toStarStr X)ᴴ
  map_add' X Y := by
    change (swapMap s.toStarStr (X + Y))ᴴ = _
    rw [swapMap_add]
    exact conjTranspose_add _ _
  map_smul' c X := by
    change (swapMap s.toStarStr (c • X))ᴴ = _
    have h : ((c • X : Matrix (Fin m) (Fin m) ℂ), (0 : Matrix (Fin k) (Fin k) ℂ))
        = c • (X, (0 : Matrix (Fin k) (Fin k) ℂ)) := by
      refine Prod.ext ?_ ?_ <;> simp
    have h2 : swapMap s.toStarStr (c • X) = (starRingEnd ℂ) c • swapMap s.toStarStr X := by
      change (s.map ((c • X : Matrix (Fin m) (Fin m) ℂ), (0 : _))).2 = _
      rw [h, s.map_smul]
      rfl
    rw [h2, conjTranspose_smul]
    simp

@[simp] theorem swapLin_apply
    (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ)) (X) :
    swapLin s X = (swapMap s.toStarStr X)ᴴ := rfl

theorem swapLin_bijective (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ))
    (hswap : s.map (1, 0) = (0, 1)) : Function.Bijective (swapLin s) := by
  have hc : Function.Bijective (conjTranspose : Matrix (Fin k) (Fin k) ℂ → _) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨conjTranspose, conjTranspose_conjTranspose, conjTranspose_conjTranspose⟩
  exact hc.comp (swapMap_bijective s.toStarStr hswap)

/-- **The dimension count, and it is the residue the previous unit named.** A `ℂ`-linear
bijection `Mₘ(ℂ) ≃ Mₖ(ℂ)` gives `m * m = k * k` through `Module.finrank_matrix`, hence `m = k`:
**the swapping branch of the dichotomy is empty unless the two factors have the same size.** -/
theorem swap_forces_eq_size
    (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ))
    (hswap : s.map (1, 0) = (0, 1)) : m = k := by
  have e : Matrix (Fin m) (Fin m) ℂ ≃ₗ[ℂ] Matrix (Fin k) (Fin k) ℂ :=
    LinearEquiv.ofBijective (swapLin s) (swapLin_bijective s hswap)
  have h := e.finrank_eq
  rw [Module.finrank_matrix, Module.finrank_matrix] at h
  simp only [Fintype.card_fin, Module.finrank_self, mul_one] at h
  exact (mul_self_inj (Nat.zero_le m) (Nat.zero_le k)).mp h

/-! ## 4. The fixing case, composed with the single-factor classification -/

/-- **The single-factor normal form, named** so the product statement below reads as one line:
`twist P X = (P X P⁻¹)ᴴ`, which is exactly what `StarStructureHermitian.exists_hermitian_twist`
produces. An abbreviation and nothing more — `twist_apply` is `rfl`. -/
def twist (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((P : Matrix (Fin n) (Fin n) ℂ) * X
    * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ

@[simp] theorem twist_apply (P : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X) :
    twist P X = ((P : Matrix (Fin n) (Fin n) ℂ) * X
      * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ := rfl


/-- **The combined statement in the fixing branch.** `map_eq_of_fixes` says the two restrictions
determine `s`; `exists_hermitian_twist` classifies each; so `s` is the pair. -/
theorem fixing_classification [NeZero m] [NeZero k]
    (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ))
    (hfix : s.map (1, 0) = (1, 0)) :
    ∃ (P : (Matrix (Fin m) (Fin m) ℂ)ˣ) (Q : (Matrix (Fin k) (Fin k) ℂ)ˣ),
      (P : Matrix (Fin m) (Fin m) ℂ)ᴴ = (P : Matrix (Fin m) (Fin m) ℂ) ∧
      (Q : Matrix (Fin k) (Fin k) ℂ)ᴴ = (Q : Matrix (Fin k) (Fin k) ℂ) ∧
      ∀ X Y, s.map (X, Y) = (twist P X, twist Q Y) := by
  obtain ⟨P, hPh, hP⟩ :=
    StarStructureHermitian.exists_hermitian_twist (toStarStructure (restrictLeftC s hfix))
  obtain ⟨Q, hQh, hQ⟩ :=
    StarStructureHermitian.exists_hermitian_twist (toStarStructure (restrictRightC s hfix))
  refine ⟨P, Q, hPh, hQh, fun X Y => ?_⟩
  have h := map_eq_of_fixes s.toStarStr hfix X Y
  rw [h]
  refine Prod.ext ?_ ?_
  · exact hP X
  · exact hQ Y

/-! ## 5. Both branches in one statement -/

/-- **The classification of ⋆-structures on `Mₘ(ℂ) × Mₖ(ℂ)`.** Either the factors are fixed and
the structure is the pair of single-factor normal forms with Hermitian twists, or the factors are
swapped and **`m = k`**. Both disjuncts are now statements about `s`; neither is an unanalysed
existential, which is what `UNLOCK_WATCHLIST` 266's item (2) asked for. -/
theorem matrixProd_classification [NeZero m] [NeZero k]
    (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ)) :
    (∃ (P : (Matrix (Fin m) (Fin m) ℂ)ˣ) (Q : (Matrix (Fin k) (Fin k) ℂ)ˣ),
        (P : Matrix (Fin m) (Fin m) ℂ)ᴴ = (P : Matrix (Fin m) (Fin m) ℂ) ∧
        (Q : Matrix (Fin k) (Fin k) ℂ)ᴴ = (Q : Matrix (Fin k) (Fin k) ℂ) ∧
        ∀ X Y, s.map (X, Y) = (twist P X, twist Q Y))
      ∨ m = k := by
  rcases matrixProd_dichotomy s.toStarStr with hfix | hswap
  · exact Or.inl (fixing_classification s hfix)
  · exact Or.inr (swap_forces_eq_size s hswap)

/-! ## 6. At UNEQUAL sizes there is only one branch -/

/-- **A product of matrix algebras of DIFFERENT sizes admits only factor-fixing ⋆-structures.**
The dichotomy plus the dimension count. For `M₁₆` as `M₄ ⊗ M₂ ⊗ M₂` the factor sizes are
`4, 2, 2` — **not all distinct** — so what this gives is that no involution exchanges the `M₄`
factor with either `M₂`, and it leaves the exchange of the two `M₂` factors open, which
`prodSwapTransposeC` shows really does occur. -/
theorem fixes_of_ne_size [NeZero m] [NeZero k] (h : m ≠ k)
    (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ)) :
    s.map (1, 0) = (1, 0) := by
  rcases matrixProd_dichotomy s.toStarStr with hfix | hswap
  · exact hfix
  · exact absurd (swap_forces_eq_size s hswap) h

/-- **So at unequal sizes the classification is a NORMAL FORM and not a disjunction**: every
⋆-structure on `Mₘ(ℂ) × Mₖ(ℂ)` with `m ≠ k` is `(X, Y) ↦ ((P X P⁻¹)ᴴ, (Q Y Q⁻¹)ᴴ)` for
Hermitian units `P` and `Q`. -/
theorem classification_of_ne_size [NeZero m] [NeZero k] (h : m ≠ k)
    (s : StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ)) :
    ∃ (P : (Matrix (Fin m) (Fin m) ℂ)ˣ) (Q : (Matrix (Fin k) (Fin k) ℂ)ˣ),
      (P : Matrix (Fin m) (Fin m) ℂ)ᴴ = (P : Matrix (Fin m) (Fin m) ℂ) ∧
      (Q : Matrix (Fin k) (Fin k) ℂ)ᴴ = (Q : Matrix (Fin k) (Fin k) ℂ) ∧
      ∀ X Y, s.map (X, Y) = (twist P X, twist Q Y) :=
  fixing_classification s (fixes_of_ne_size h s)

/-! ## 7. Neither branch is empty -/


/-- The componentwise conjugate transpose, as a `StarStrC` — the fixing branch, realised. -/
def prodConjTransposeC (m k : ℕ) :
    StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin k) (Fin k) ℂ) where
  toStarStr := prodConjTranspose m k
  map_smul c X := by
    refine Prod.ext ?_ ?_ <;> simp [prodConjTranspose, conjTranspose_smul]

theorem prodConjTransposeC_fixes (m k : ℕ) :
    (prodConjTransposeC m k).map (1, 0) = (1, 0) := prodConjTranspose_fixes m k

/-- `(X, Y) ↦ (Yᴴ, Xᴴ)` at equal sizes, as a `StarStrC` — the swapping branch, realised, which
is what makes `swap_forces_eq_size` a constraint rather than a vacuous truth. -/
def prodSwapTransposeC (m : ℕ) :
    StarStrC (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ) where
  toStarStr := prodSwapTranspose m
  map_smul c X := by
    refine Prod.ext ?_ ?_ <;> simp [prodSwapTranspose, conjTranspose_smul]

theorem prodSwapTransposeC_swaps (m : ℕ) :
    (prodSwapTransposeC m).map (1, 0) = (0, 1) := prodSwapTranspose_swaps m

end

end StarStructureProductMatrix
