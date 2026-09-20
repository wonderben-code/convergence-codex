/-
  StarStructureSwapConjugacy.lean — the swapping branch is ONE inner-conjugacy class: every
  `swapTwist S` is conjugate to the plain swap by the unit `(S, 1)`, two swapping ⋆-structures on
  `Mₙ(ℂ) × Mₙ(ℂ)` are always inner-conjugate, the fibre of `S ↦ swapTwist S` is the nonzero
  scalars, and inner conjugacy never crosses the fixing/swapping dichotomy.

  SPINE L11 (Pati–Salam uniqueness, OPEN) and L6 / `WALLS` §W9 — the B→C follow-up
  (`PROOF_STRATEGY` §6 q3) to unit 156's normal form. Hardening unit 157, 2026-09-20.

  WHY. Unit 156 (`StarStructureSwapNormalForm`) put every factor-swapping ⋆-structure on
  `Mₙ(ℂ) × Mₙ(ℂ)` in the form `swapTwist S : (X, Y) ↦ (S⁻¹ Yᴴ S, (S X S⁻¹)ᴴ)` and listed two things
  it did not do: compute the fibre of `S ↦ swapTwist S`, and classify the swapping structures up to
  conjugacy. Both are cheap once the normal form exists. The fibre is unit 69's `twist_unique`
  argument (`M := Q⁻¹ P` is central, so a scalar) with its Hermitian hypotheses and their real
  conclusion removed; the conjugacy is one computation — conjugating the plain swap by the unit
  `(S, 1)` of the product gives exactly `swapTwist S`.

  WHAT IS PROVED.
  * `twistMap_eq_iff_complex` — `twistMap P = twistMap Q ↔ ∃ c ≠ 0, P = c • Q`, for any invertible
    `P`, `Q` (unit 69's `twistMap_eq_iff` is the Hermitian case, where `c` is then real).
  * **`swapTwist_eq_iff`** — `swapTwist S = swapTwist S'` (as maps) **iff** `S = c • S'` for a
    nonzero complex `c`: the swapping structures are `GLₙ(ℂ) / ℂˣ`, as maps.
  * `InnerConjugate s t` — `t p = U⁻¹ · s (U p U⁻¹) · U` for a unit `U` of the product, with
    `innerConjugate_refl`, `_symm`, `_trans`.
  * `unitFst S = (S, 1)` and **`swapTwist_innerConjugate_one`** — `swapTwist S` is inner-conjugate
    to `swapTwist 1 = prodSwapTransposeC` by that unit.
  * **`swapping_innerConjugate`** — any two swapping ⋆-structures are inner-conjugate: the
    swapping branch is a single class.
  * `innerConjugate_swaps`, **`not_innerConjugate_of_fixes_of_swaps`** — `(1, 0)` is central, so
    conjugacy preserves the dichotomy, and a fixing structure is never conjugate to a swapping one.

  WHAT IS **NOT** PROVED, said exactly.
  * The fixing branch up to inner conjugacy. `InnerConjugate` on the product with `U = (U₁, U₂)`
    conjugates the two twists separately, so the fixing classes should be pairs of single-factor
    classes — `(n/2 + 1)²` by `card_achievable` — but that count is not composed here, and the
    conjugacy by the factor-SWAPPING automorphism `(X, Y) ↦ (Y, X)`, which is not inner, is not
    considered at all; `InnerConjugate` is inner conjugacy only.
    ⚠ DONE 20 SEP 2026 (unit 160, `StarStructureFixConjugacy`), bullet kept as written
    (`ERRATUM 94`): the count IS composed there — `fixTwist_innerConjugate_iff_usignature` (inner
    conjugacy of two fixing normal forms ⟺ both unordered signatures agree) and
    `classification_count` (exactly `(n/2 + 1)² + 1` classes on `Mₙ(ℂ) × Mₙ(ℂ)` up to INNER
    conjugacy, by a complete irredundant family of representatives). The factor-swapping
    automorphism is still not considered, there or here.
  * Anything at more than two factors, anything real or quaternionic, and — as items 2 and (3) of
    the two-spine-links block say — anything about the cascade: that the two `M₂` factors of
    `M₄ ⊗ M₂ ⊗ M₂` may be exchanged in essentially one way does not prefer that factorisation.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import StarStructureSwapNormalForm
import StarStructureTwistFibre

namespace StarStructureSwapConjugacy

open Matrix StarStructureProduct StarStructureProductMatrix StarStructureSwapNormalForm
  StarStructureTwistFibre

variable {n : ℕ}

/-! ## 1. The complex fibre of a twist: `twistMap P = twistMap Q` iff `P` is a nonzero scalar
multiple of `Q` — unit 69's `twist_unique` without its Hermitian hypotheses and without the
realness it bought with them -/

theorem twistMap_eq_iff_complex [NeZero n] (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    twistMap P = twistMap Q
      ↔ ∃ c : ℂ, c ≠ 0 ∧ (P : Matrix (Fin n) (Fin n) ℂ) = c • (Q : Matrix (Fin n) (Fin n) ℂ) := by
  constructor
  · intro h
    have hconj : ∀ X : Matrix (Fin n) (Fin n) ℂ,
        (P : Matrix (Fin n) (Fin n) ℂ) * X
            * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
          = (Q : Matrix (Fin n) (Fin n) ℂ) * X
            * ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := fun X =>
      Matrix.conjTranspose_injective (by simpa using congrFun h X)
    set M : Matrix (Fin n) (Fin n) ℂ :=
      ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
        * (P : Matrix (Fin n) (Fin n) ℂ) with hM
    have hcent : ∀ A : Matrix (Fin n) (Fin n) ℂ, M * A = A * M := by
      intro A
      have hA := hconj A
      calc M * A
          = ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
              * ((P : Matrix (Fin n) (Fin n) ℂ) * A
                * ((P⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
                * (P : Matrix (Fin n) (Fin n) ℂ)) := by
              rw [hM, Matrix.mul_assoc, Units.inv_mul_cancel_right]
        _ = ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
              * ((Q : Matrix (Fin n) (Fin n) ℂ) * A
                * ((Q⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
                * (P : Matrix (Fin n) (Fin n) ℂ)) := by rw [hA]
        _ = A * M := by
              rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul_cancel_left]
    obtain ⟨c, hc⟩ := StarStructureMatrix.matrix_center_scalar M hcent
    have hPQ : (P : Matrix (Fin n) (Fin n) ℂ) = c • (Q : Matrix (Fin n) (Fin n) ℂ) := by
      have hQM : (Q : Matrix (Fin n) (Fin n) ℂ) * M = (P : Matrix (Fin n) (Fin n) ℂ) := by
        rw [hM, Units.mul_inv_cancel_left]
      rw [← hQM, hc, Matrix.mul_smul, Matrix.mul_one]
    refine ⟨c, fun h0 => ?_, hPQ⟩
    rw [h0, zero_smul] at hPQ
    exact unit_ne_zero P hPQ
  · rintro ⟨c, hc, hPQ⟩
    calc twistMap P = twistMap (smulTwist c hc Q) := twistMap_congr (by simpa using hPQ)
      _ = twistMap Q := twistMap_smulTwist _ _ _

/-! ## 2. The fibre of `S ↦ swapTwist S` -/

/-- **THE FIBRE.** Two twists give the same swapping ⋆-structure iff they differ by a nonzero
complex scalar: the swapping structures are parametrised by `GLₙ(ℂ) / ℂˣ`. -/
theorem swapTwist_eq_iff [NeZero n] (S S' : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (∀ p, (swapTwist S).map p = (swapTwist S').map p)
      ↔ ∃ c : ℂ, c ≠ 0 ∧ (S : Matrix (Fin n) (Fin n) ℂ) = c • (S' : Matrix (Fin n) (Fin n) ℂ) := by
  constructor
  · intro h
    refine (twistMap_eq_iff_complex S S').1 ?_
    funext X
    have := congrArg Prod.snd (h (X, 0))
    simpa [swapTwist_apply, twistMap_apply] using this
  · rintro ⟨c, hc, hSS'⟩ p
    have hS : S = smulTwist c hc S' := Units.ext (by simpa using hSS')
    subst hS
    obtain ⟨X, Y⟩ := p
    rw [swapTwist_apply, swapTwist_apply]
    simp only [smulTwist_val, smulTwist_inv_val]
    refine Prod.ext ?_ ?_
    · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]

/-! ## 3. Inner conjugacy on the product, and the swapping branch is ONE class -/

/-- Inner conjugacy of two ⋆-structures on `Mₙ(ℂ) × Mₙ(ℂ)`: `t p = U⁻¹ · s (U p U⁻¹) · U` for a
unit `U` of the product — the product-algebra analogue of `StarStructureInequivalent.Conjugate`. -/
def InnerConjugate (s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    Prop :=
  ∃ U : (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)ˣ,
    ∀ p, t.map p = (U⁻¹ : _ˣ).val * s.map (U.val * p * (U⁻¹ : _ˣ).val) * U.val

theorem innerConjugate_refl (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    InnerConjugate s s :=
  ⟨1, fun p => by simp⟩

theorem innerConjugate_symm
    {s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (h : InnerConjugate s t) : InnerConjugate t s := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U⁻¹, fun q => ?_⟩
  have hq : U.val * ((U⁻¹ : _ˣ).val * q * U.val) * (U⁻¹ : _ˣ).val = q := by
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  have := hU ((U⁻¹ : _ˣ).val * q * U.val)
  rw [hq] at this
  rw [inv_inv, this]
  simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]

theorem innerConjugate_trans
    {s t u : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (h₁ : InnerConjugate s t) (h₂ : InnerConjugate t u) : InnerConjugate s u := by
  obtain ⟨U, hU⟩ := h₁
  obtain ⟨V, hV⟩ := h₂
  refine ⟨U * V, fun p => ?_⟩
  rw [hV, hU]
  simp only [_root_.mul_inv_rev, Units.val_mul, mul_assoc]

/-- The unit `(S, 1)` of the product. -/
def unitFst (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := ((S : Matrix (Fin n) (Fin n) ℂ), 1)
  inv := (((S⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ), 1)
  val_inv := by refine Prod.ext ?_ ?_ <;> simp
  inv_val := by refine Prod.ext ?_ ?_ <;> simp

/-- **Every swapping twist is inner-conjugate to the plain swap**, by the unit `(S, 1)`. -/
theorem swapTwist_innerConjugate_one (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    InnerConjugate (swapTwist 1) (swapTwist S) := by
  refine ⟨unitFst S, fun p => ?_⟩
  obtain ⟨X, Y⟩ := p
  refine Prod.ext ?_ ?_ <;> simp [swapTwist_apply, unitFst, Matrix.mul_assoc]

/-- **THE SWAPPING BRANCH IS ONE CLASS.** Any two ⋆-structures on `Mₙ(ℂ) × Mₙ(ℂ)` that exchange
the factors are inner-conjugate. -/
theorem swapping_innerConjugate [NeZero n]
    (s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
    (hs : s.map (1, 0) = (0, 1)) (ht : t.map (1, 0) = (0, 1)) : InnerConjugate s t := by
  obtain ⟨S, hS⟩ := (swapping_iff s).1 hs
  obtain ⟨T, hT⟩ := (swapping_iff t).1 ht
  have hs' : InnerConjugate (swapTwist S) s :=
    ⟨1, fun p => by obtain ⟨X, Y⟩ := p; simp [hS]⟩
  have ht' : InnerConjugate (swapTwist T) t :=
    ⟨1, fun p => by obtain ⟨X, Y⟩ := p; simp [hT]⟩
  exact innerConjugate_trans (innerConjugate_symm hs')
    (innerConjugate_trans (innerConjugate_symm (swapTwist_innerConjugate_one S))
      (innerConjugate_trans (swapTwist_innerConjugate_one T) ht'))

/-! ## 4. Inner conjugacy respects the dichotomy: `(1, 0)` is central -/

theorem innerConjugate_swaps
    {s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (h : InnerConjugate s t) (hs : s.map (1, 0) = (0, 1)) : t.map (1, 0) = (0, 1) := by
  obtain ⟨U, hU⟩ := h
  have hc : U.val * ((1, 0) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
      * (U⁻¹ : _ˣ).val = (1, 0) := by
    obtain ⟨⟨a, b⟩, ⟨a', b'⟩, hv, hi⟩ := U
    have ha : a * a' = 1 := congrArg Prod.fst hv
    simp [ha]
  have hc' : (U⁻¹ : _ˣ).val * ((0, 1) : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
      * U.val = (0, 1) := by
    obtain ⟨⟨a, b⟩, ⟨a', b'⟩, hv, hi⟩ := U
    have hb : b' * b = 1 := congrArg Prod.snd hi
    simp [hb]
  rw [hU, hc, hs, hc']

/-- **Fixing and swapping structures are never inner-conjugate**: conjugacy preserves the
dichotomy, because the idempotent `(1, 0)` is central. -/
theorem not_innerConjugate_of_fixes_of_swaps
    {s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (hs : s.map (1, 0) = (1, 0)) (ht : t.map (1, 0) = (0, 1)) [NeZero n] :
    ¬ InnerConjugate s t := by
  intro h
  have := innerConjugate_swaps (innerConjugate_symm h) ht
  rw [hs] at this
  have h1 := congrArg Prod.fst this
  simp at h1

end StarStructureSwapConjugacy
