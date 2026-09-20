/-
  StarStructureSwapNormalForm.lean — the normal form of a SWAPPING ⋆-structure on `Mₙ(ℂ) × Mₙ(ℂ)`:
  every one is `(X, Y) ↦ (S⁻¹ Yᴴ S, (S X S⁻¹)ᴴ)` for one invertible `S`, every `S` occurs, and the
  equal-size classification is two normal forms rather than a normal form and a size equation.

  SPINE L11 (Pati–Salam uniqueness, OPEN) and L6 / `WALLS` §W9 — the Caesar order's item 2, whose
  20 September re-count says *"that every swapping structure is `prodSwapTransposeC` twisted is
  still not stated"*. Hardening unit 156, 2026-09-20.

  WHY. Units 34–35 (`StarStructureProduct`, `StarStructureProductMatrix`) proved the dichotomy — a
  ⋆-structure on `Mₘ(ℂ) × Mₖ(ℂ)` either fixes the two factors or swaps them — and classified the
  fixing branch as a pair of single-factor twists `(twist P X, twist Q Y)`. For the swapping branch
  they proved `m = k` and exhibited one example, `prodSwapTransposeC : (X, Y) ↦ (Yᴴ, Xᴴ)`, and left
  the normal form unstated. The ingredients were all present: `swapLin s = X ↦ (swapMap s X)ᴴ` is
  `ℂ`-linear and bijective (unit 35), `swapMap` is anti-multiplicative (unit 34), so `swapLin` is a
  `ℂ`-algebra AUTOMORPHISM of `Mₙ(ℂ)`, and this estate's `SkolemNoether.skolemNoether` makes it
  inner. Involutivity then forces the other block map to be the inverse twist.

  WHAT IS PROVED (`s` a `StarStrC` on `Mₙ(ℂ) × Mₙ(ℂ)` with `s (1, 0) = (0, 1)`).
  * `swapMap_one`, `swapLin_one`, `swapLin_mul`, `swapAlgEquiv : Mₙ(ℂ) ≃ₐ[ℂ] Mₙ(ℂ)` — the swap
    map after one conjugate transpose is a unital algebra automorphism.
  * `exists_swap_twist` — `swapMap s X = (S X S⁻¹)ᴴ` for one invertible `S` (Skolem–Noether).
  * **`swapping_classification`** — `s (X, Y) = (S⁻¹ Yᴴ S, (S X S⁻¹)ᴴ)` for every `X`, `Y`.
  * `swapTwist S` — that map, packaged as a `StarStrC` for EVERY invertible `S`, with
    `swapTwist_swaps` (it swaps) and `swapTwist_one_map` (at `S = 1` it is `prodSwapTransposeC`).
  * **`swapping_iff`** — `s` swaps the factors **iff** `s = swapTwist S` for some `S`.
  * **`matrixProd_classification_eq`** — at equal sizes: fixing normal form OR swapping normal form.

  WHAT IS **NOT** PROVED, said exactly.
  * Which `S` give the SAME ⋆-structure (the fibre of `S ↦ swapTwist S`) — expected the `ℂˣ`-orbit
    by the centre of `Mₙ(ℂ)`, not proved here; and no conjugacy classification of the swapping
    structures under algebra automorphisms of the product, so no COUNT analogous to
    `HermitianSignatureClassification.card_achievable`.
  * Anything at more than two factors: `StarStructurePi.blockMap` carries block `i` to block `σ i`
    for any involution `σ`, and this file's argument would run on each 2-cycle, but that composite
    is not written.
  * Nothing about the cascade is cut, exactly as Caesar item 2 says: `M₁₆` as `M₄ ⊗ M₂ ⊗ M₂` may
    still exchange its two `M₂` factors, and knowing every such exchange is a `swapTwist S` prefers
    no factorisation. Nothing real or quaternionic appears.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import StarStructureProductMatrix

namespace StarStructureSwapNormalForm

open Matrix StarStructureProduct StarStructureProductMatrix

variable {n : ℕ}

section Swap

variable (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))

/-! ## 1. The swap map is a unital algebra automorphism after one conjugate transpose -/

theorem swapMap_one (hswap : s.map (1, 0) = (0, 1)) : swapMap s.toStarStr 1 = 1 :=
  congrArg Prod.snd hswap

theorem swapLin_one (hswap : s.map (1, 0) = (0, 1)) : swapLin s 1 = 1 := by
  rw [swapLin_apply, swapMap_one s hswap, conjTranspose_one]

theorem swapLin_mul (X Y : Matrix (Fin n) (Fin n) ℂ) :
    swapLin s (X * Y) = swapLin s X * swapLin s Y := by
  rw [swapLin_apply, swapLin_apply, swapLin_apply, swapMap_antimul, conjTranspose_mul]

/-- `X ↦ (swapMap s X)ᴴ` as a `ℂ`-algebra automorphism of `Mₙ(ℂ)`: `swapLin` is linear and
bijective (unit 35), and the two lemmas above make it unital and multiplicative. -/
noncomputable def swapAlgEquiv (hswap : s.map (1, 0) = (0, 1)) :
    Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  AlgEquiv.ofLinearEquiv (LinearEquiv.ofBijective (swapLin s) (swapLin_bijective s hswap))
    (swapLin_one s hswap) (swapLin_mul s)

theorem swapAlgEquiv_apply (hswap : s.map (1, 0) = (0, 1)) (X : Matrix (Fin n) (Fin n) ℂ) :
    swapAlgEquiv s hswap X = (swapMap s.toStarStr X)ᴴ := rfl

/-! ## 2. Skolem–Noether pins the swap map to one twist -/

/-- **The swap map is an inner twist**: `swapMap s X = (S X S⁻¹)ᴴ` for one invertible `S`. -/
theorem exists_swap_twist [NeZero n] (hswap : s.map (1, 0) = (0, 1)) :
    ∃ S : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ X : Matrix (Fin n) (Fin n) ℂ,
      swapMap s.toStarStr X
        = ((S : Matrix (Fin n) (Fin n) ℂ) * X
          * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ := by
  obtain ⟨S, hS⟩ := SkolemNoether.skolemNoether ℂ n (swapAlgEquiv s hswap)
  refine ⟨S, fun X => ?_⟩
  have h := hS X
  rw [swapAlgEquiv_apply] at h
  rw [← h, conjTranspose_conjTranspose]

/-! ## 3. The normal form of a swapping ⋆-structure -/

/-- **THE SWAPPING NORMAL FORM.** Every ⋆-structure on `Mₙ(ℂ) × Mₙ(ℂ)` that exchanges the two
factors is `(X, Y) ↦ (S⁻¹ Yᴴ S, (S X S⁻¹)ᴴ)` for one invertible `S`. The second component is
`exists_swap_twist`; the first is forced by involutivity, which makes the `0 × Mₙ → Mₙ × 0` block
map the inverse of the `Mₙ × 0 → 0 × Mₙ` one. -/
theorem swapping_classification [NeZero n] (hswap : s.map (1, 0) = (0, 1)) :
    ∃ S : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      s.map (X, Y)
        = (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Yᴴ
            * (S : Matrix (Fin n) (Fin n) ℂ),
          ((S : Matrix (Fin n) (Fin n) ℂ) * X
            * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ) := by
  obtain ⟨S, hS⟩ := exists_swap_twist s hswap
  refine ⟨S, fun X Y => ?_⟩
  have h1 : s.map (X, 0)
      = (0, ((S : Matrix (Fin n) (Fin n) ℂ) * X
          * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ) :=
    Prod.ext (fst_eq_zero_of_swaps s.toStarStr hswap X) (hS X)
  have hX' : swapMap s.toStarStr
      (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Yᴴ
        * (S : Matrix (Fin n) (Fin n) ℂ)) = Y := by
    rw [hS, Matrix.mul_assoc ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ),
      Units.mul_inv_cancel_left, Units.mul_inv_cancel_right, conjTranspose_conjTranspose]
  have h2 : s.map (0, Y)
      = (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Yᴴ
          * (S : Matrix (Fin n) (Fin n) ℂ), 0) := by
    have hm : s.map (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Yᴴ
        * (S : Matrix (Fin n) (Fin n) ℂ), 0) = (0, Y) :=
      Prod.ext (fst_eq_zero_of_swaps s.toStarStr hswap _) hX'
    have := s.map_involutive (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      * Yᴴ * (S : Matrix (Fin n) (Fin n) ℂ), 0)
    rw [hm] at this
    exact this
  have hsplit : ((X, Y) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
      = (X, 0) + (0, Y) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [hsplit, s.map_add, h1, h2]
  refine Prod.ext ?_ ?_ <;> simp

end Swap

/-! ## 4. Every twist occurs: the swapping structures are exactly the `swapTwist S` -/

/-- **The swapping ⋆-structure with twist `S`**: `(X, Y) ↦ (S⁻¹ Yᴴ S, (S X S⁻¹)ᴴ)`. At `S = 1`
this is `prodSwapTransposeC`. -/
noncomputable def swapTwist (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) where
  map p := (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * p.2ᴴ
      * (S : Matrix (Fin n) (Fin n) ℂ),
    ((S : Matrix (Fin n) (Fin n) ℂ) * p.1
      * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ)
  map_add p q := by
    refine Prod.ext ?_ ?_ <;> simp [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
  map_mul p q := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_mul, Prod.snd_mul, conjTranspose_mul, Matrix.mul_assoc]
      rw [Units.mul_inv_cancel_left]
    · simp only [Prod.fst_mul, Prod.snd_mul]
      rw [← conjTranspose_mul]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [Units.inv_mul_cancel_left]
  map_involutive p := by
    refine Prod.ext ?_ ?_
    · simp only [conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]
    · simp only [Matrix.mul_assoc]
      rw [Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one, conjTranspose_conjTranspose]
  map_smul c p := by
    refine Prod.ext ?_ ?_ <;> simp [conjTranspose_smul]

theorem swapTwist_apply (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    (swapTwist S).map (X, Y)
      = (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * Yᴴ
          * (S : Matrix (Fin n) (Fin n) ℂ),
        ((S : Matrix (Fin n) (Fin n) ℂ) * X
          * ((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ))ᴴ) := rfl

/-- Every `swapTwist S` swaps the factors, so every invertible `S` occurs. -/
theorem swapTwist_swaps (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : (swapTwist S).map (1, 0) = (0, 1) := by
  rw [swapTwist_apply]
  refine Prod.ext ?_ ?_ <;> simp

/-- At `S = 1` the twist is the conjugate-transpose swap of unit 34. -/
theorem swapTwist_one_map (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    (swapTwist 1).map p = (prodSwapTransposeC n).map p := by
  simp [swapTwist, prodSwapTransposeC, prodSwapTranspose]

/-! ## 5. The swapping structures are EXACTLY the twists, and the equal-size classification -/

/-- **SWAPPING ⟺ A TWIST.** `s` exchanges the factors iff it is `swapTwist S` for some `S`. -/
theorem swapping_iff [NeZero n]
    (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    s.map (1, 0) = (0, 1)
      ↔ ∃ S : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
          s.map (X, Y) = (swapTwist S).map (X, Y) := by
  constructor
  · intro hswap
    obtain ⟨S, hS⟩ := swapping_classification s hswap
    exact ⟨S, fun X Y => by rw [hS, swapTwist_apply]⟩
  · rintro ⟨S, hS⟩
    rw [hS, swapTwist_swaps]

/-- **THE CLASSIFICATION AT EQUAL SIZES, BOTH BRANCHES AS NORMAL FORMS.** A ⋆-structure on
`Mₙ(ℂ) × Mₙ(ℂ)` is either `(X, Y) ↦ (twist P X, twist Q Y)` with `P`, `Q` Hermitian units (the
factor-fixing branch, unit 35) or `(X, Y) ↦ (S⁻¹ Yᴴ S, (S X S⁻¹)ᴴ)` for one invertible `S` (the
swapping branch, this file). `matrixProd_classification`'s second disjunct was `m = k`; here it is
the structure itself. -/
theorem matrixProd_classification_eq [NeZero n]
    (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    (∃ (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ),
        (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ) ∧
        (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ) ∧
        ∀ X Y : Matrix (Fin n) (Fin n) ℂ, s.map (X, Y) = (twist P X, twist Q Y))
      ∨ ∃ S : (Matrix (Fin n) (Fin n) ℂ)ˣ, ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
          s.map (X, Y) = (swapTwist S).map (X, Y) := by
  rcases matrixProd_dichotomy s.toStarStr with hfix | hswap
  · exact Or.inl (fixing_classification s hfix)
  · exact Or.inr ((swapping_iff s).1 hswap)

end StarStructureSwapNormalForm
