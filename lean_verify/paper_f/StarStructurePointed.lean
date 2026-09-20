/-
  StarStructurePointed.lean — the pointed ⋆-structures on `Mₙ(ℂ)` are exactly the definite class,
  at every `n`; and on `Mₙ(ℂ) × Mₙ(ℂ)` exactly one of the `(n/2 + 1)² + 1` inner classes is
  pointed —
  the componentwise conjugate transpose's — while no swapping structure is.

  SPINE L3 (the seed's star, `ASSUMPTIONS_LEDGER` 4), L6 / `WALLS` §W9 rung 2 and L11 (Caesar
  item 2):
  the C⋆ shadow that selects one class among all. Hardening unit 164, 2026-09-20.

  WHY. Unit 151 (`SeedStarPositivity`) named the weakest algebraic shadow of C⋆ positivity — the
  positive cone `{x⋆x}` is POINTED, `x⋆x + y⋆y = 0 → x⋆x = 0` — and proved at `n = 2` that the
  pointed ⋆-structures on `M₂(ℂ)` are exactly the definite class, by a two-by-two matrix-unit
  computation. The computation never used `n = 2`: a sign twist with one plus and one minus sign
  has `e_{ij}⋆ e_{ij} = −e_{jj}` and `e_{jj}⋆ e_{jj} = e_{jj}` in any size, and unit 75's
  classification says every non-definite class contains such a twist. So the theorem holds at
  every `n`, and with units 156–160's classification of the product it extends to `Mₙ(ℂ) × Mₙ(ℂ)`:
  a fixing structure is pointed iff both factors are, a swapping one never is (`(e₀₀, e₀₀)` and
  `(e₀₀, −e₀₀)` under the plain swap), so exactly one inner class of the `(n/2 + 1)² + 1` is
  pointed.
  This is what §W9 rung 2 has called *the second half*: among the ⋆-structures the classification
  lists, a C⋆ condition — here its weakest shadow — picks one.

  WHAT IS PROVED.
  * `setTwist_inv_val`, `twistMap_setTwist_single` — the sign twist on a matrix unit;
    **`not_pointed_setTwist`** — one plus and one minus sign break pointedness, at every `n`.
  * `usignature_one`, `usignature_setTwist`; **`pointed_iff_definite`** — `hermitianStar P` is
    pointed iff `usignature P = s(2n, 0)` (`n ≥ 1`); **`pointed_iff_conjugate_conjTransposeStar`** —
    any ⋆-structure on `Mₙ(ℂ)` is pointed iff conjugate to the conjugate transpose.
  * `pointedA_congr`, `pointedA_of_innerConjugate`; **`pointedA_fixTwist_iff`** — a fixing normal
    form is pointed iff both factors are; `single_zero_conjTranspose`, `not_pointedA_swapTwist_one`,
    **`not_pointedA_of_swaps`** — no swapping ⋆-structure is pointed; `fixTwist_one_one_map`,
    `pointedA_prodConjTransposeC`.
  * **`pointedA_iff_innerConjugate`** — a ⋆-structure on `Mₙ(ℂ) × Mₙ(ℂ)` is pointed iff
    inner-conjugate to `prodConjTransposeC n n`; **`pointedA_classRep_iff`** — of unit 160's
    representatives exactly `classRep (Sum.inl (0, 0))` is pointed.

  WHAT IS **NOT** PROVED, said exactly.
  * That any ⋆-structure in the estate IS pointed. Pointedness is the C⋆ input; nothing here or
    anywhere in the estate models a norm, the C⋆ identity, or states. As in unit 151, `Pointed` is
    a consequence of C⋆ positivity and not an equivalent of it.
  * The second half of §W9 rung 2 as CCM states it — that the real structure `J` of a spectral
    triple selects the involution. What is proved is that a C⋆ shadow selects one class; nothing
    relates it to a `J`.
  * Anything at more than two factors, at unequal sizes (`Mₘ × Mₖ`, `m ≠ k`, where only the fixing
    branch exists and the same factorwise statement would hold), or over `ℝ`/`ℍ`.
  * `n = 0`: the branches coincide there; `[NeZero n]` stands on every classification statement.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import SeedStarPositivity
import StarStructureFixConjugacy

namespace StarStructurePointed

open Matrix StarStructureMatrix StarStructureTwistFibre StarStructureInequivalent
  HermitianSignatureClassification HermitianRealForm SeedStarPositivity StarStructureFixConjugacy

variable {n : ℕ}

/-! ## 1. The sign twist on a matrix unit -/

/-- A `±1` diagonal is its own inverse. -/
theorem setTwist_inv_val (S : Finset (Fin n)) :
    (((setTwist S)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Matrix.diagonal fun i => ((setVec S i : ℝ) : ℂ) := by
  change Matrix.diagonal (fun i => (((setVec S i : ℝ) : ℂ))⁻¹) = _
  congr 1
  funext i
  rw [setVec]
  by_cases h : i ∈ S <;> simp [h]

/-- The sign twist on a matrix unit: `(D e_{ij} D)ᴴ = d_i d_j · e_{ji}`. -/
theorem twistMap_setTwist_single (S : Finset (Fin n)) (i j : Fin n) :
    twistMap (setTwist S) (Matrix.single i j (1 : ℂ))
      = Matrix.single j i (((setVec S i : ℝ) : ℂ) * ((setVec S j : ℝ) : ℂ)) := by
  rw [twistMap_apply, setTwist_val, setTwist_inv_val]
  ext a b
  rw [conjTranspose_apply, mul_diagonal, diagonal_mul]
  by_cases hab : a = j ∧ b = i
  · obtain ⟨rfl, rfl⟩ := hab
    simp [Matrix.single_apply_same, mul_comm]
  · have hne : ¬ (i = b ∧ j = a) := by tauto
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hne, Matrix.single_apply_of_ne _ _ _ _ _ (by tauto)]
    simp

/-! ## 2. One plus and one minus sign make the star fail pointedness -/

/-- **ONE PLUS SIGN AND ONE MINUS SIGN BREAK POINTEDNESS**, at every `n`: with `d_i = 1`, `d_j =
−1`,
`e_{ij}⋆ e_{ij} = −e_{jj}` and `e_{jj}⋆ e_{jj} = e_{jj}` — two "squares" summing to zero with
neither
zero. Unit 151's computation at `n = 2`, `i = 0`, `j = 1`, with the indices free. -/
theorem not_pointed_setTwist (S : Finset (Fin n)) {i j : Fin n} (hi : i ∈ S) (hj : j ∉ S) :
    ¬ Pointed (hermitianStar (setTwist S) (setTwist_hermitian S)) := by
  intro h
  have hx : (hermitianStar (setTwist S) (setTwist_hermitian S)).map (Matrix.single i j (1 : ℂ))
      * Matrix.single i j (1 : ℂ) = Matrix.single j j (-1 : ℂ) := by
    rw [hermitianStar_map, twistMap_setTwist_single, Matrix.single_mul_single_same]
    simp [setVec, hi, hj]
  have hy : (hermitianStar (setTwist S) (setTwist_hermitian S)).map (Matrix.single j j (1 : ℂ))
      * Matrix.single j j (1 : ℂ) = Matrix.single j j (1 : ℂ) := by
    rw [hermitianStar_map, twistMap_setTwist_single, Matrix.single_mul_single_same]
    simp [setVec, hj]
  have h0 := h (Matrix.single i j (1 : ℂ)) (Matrix.single j j (1 : ℂ))
    (by rw [hx, hy, ← Matrix.single_add]; simp)
  rw [hx] at h0
  have := congrFun (congrFun h0 j) j
  simp at this

/-! ## 3. The pointed ⋆-structures on `Mₙ(ℂ)` are exactly the definite class -/

/-- The identity twist has unordered signature `s(2n, 0)`. -/
theorem usignature_one : usignature (1 : Matrix (Fin n) (Fin n) ℂ) = s(2 * n, 0) := by
  rw [usignature, signature_one]

/-- The unordered signature of a sign twist counts its plus signs. -/
theorem usignature_setTwist (S : Finset (Fin n)) :
    usignature ((setTwist S : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = s(2 * S.card, 2 * (n - S.card)) := by
  rw [usignature, signature_setTwist]

/-- **THE POINTED ⋆-STRUCTURES ON `Mₙ(ℂ)` ARE EXACTLY THE DEFINITE CLASS**, at every `n ≥ 1`:
`hermitianStar P` is pointed iff `usignature P = s(2n, 0)`. Forward: an unordered signature
`s(2p, 2(n−p))` with `0 < p ≤ n/2` is that of a sign twist with a plus and a minus sign, which is
not pointed, and pointedness is a conjugacy invariant; backward: `s(2n, 0)` is the class of the
conjugate transpose, which is pointed. `SeedStarPositivity.pointed_iff_usignature` is the case
`n = 2`. -/
theorem pointed_iff_definite [NeZero n] (P : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ)) :
    Pointed (hermitianStar P hP) ↔ usignature (P : Matrix (Fin n) (Fin n) ℂ) = s(2 * n, 0) := by
  constructor
  · intro hpt
    obtain ⟨p, hp, hup⟩ := exists_le_half_of_mem_achievable (mem_achievable_of_unit P hP)
    by_cases hp0 : p = 0
    · rw [hup, hp0]
      simp [Sym2.eq_swap]
    · exfalso
      obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
        (n := p) (by simp; omega)
      obtain ⟨i, hi⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨j, hj⟩ : ∃ j, j ∉ S := by
        by_contra hall
        push Not at hall
        have huniv : S = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
        have := Finset.card_univ (α := Fin n)
        rw [← huniv, hS, Fintype.card_fin] at this
        omega
      have hconj : Conjugate (hermitianStar P hP)
          (hermitianStar (setTwist S) (setTwist_hermitian S)) :=
        (conjugate_iff_usignature P (setTwist S) hP (setTwist_hermitian S)).mpr
          (by rw [usignature_setTwist, hS, hup])
      exact not_pointed_setTwist S hi hj (pointed_of_conjugate hconj hpt)
  · intro h
    have hconj : Conjugate (hermitianStar P hP)
        (hermitianStar (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) (by simp)) :=
      (conjugate_iff_usignature P 1 hP (by simp)).mpr (by rw [Units.val_one, usignature_one, h])
    have h1 : Pointed (hermitianStar (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) (by simp)) := by
      rw [hermitianStar_one]
      exact pointed_conjTransposeStar n
    exact pointed_of_conjugate (conjugate_symm hconj) h1

/-- **The same, for an arbitrary ⋆-structure**: pointed iff conjugate to the conjugate transpose.
Of the `n/2 + 1` conjugacy classes (`card_achievable`), exactly one is pointed. -/
theorem pointed_iff_conjugate_conjTransposeStar [NeZero n] (s : StarStructure n) :
    Pointed s ↔ Conjugate (conjTransposeStar n) s := by
  obtain ⟨P, hP, rfl⟩ := hermitianStar_surjective s
  rw [pointed_iff_definite, ← hermitianStar_one n,
    conjugate_iff_usignature (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) P (by simp) hP, Units.val_one,
    usignature_one]

/-! ## 4. On `Mₙ(ℂ) × Mₙ(ℂ)`: the pointed ⋆-structures are exactly the inner class of the
componentwise conjugate transpose -/

open StarStructureProduct StarStructureProductMatrix StarStructureSwapNormalForm
  StarStructureSwapConjugacy

/-- Pointedness on the product depends only on the map. -/
theorem pointedA_congr {s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (h : ∀ p, s.map p = t.map p) (hs : PointedA s) : PointedA t := by
  intro x y hxy
  rw [← h, ← h] at hxy
  rw [← h]
  exact hs x y hxy

/-- Inner conjugacy on `Mₙ(ℂ) × Mₙ(ℂ)` preserves pointedness — the product analogue of
`SeedStarPositivity.pointed_of_conjugate`. -/
theorem pointedA_of_innerConjugate
    {s t : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)}
    (h : InnerConjugate s t) (hs : PointedA s) : PointedA t := by
  obtain ⟨U, hU⟩ := h
  have key : ∀ z, t.map z * z
      = (U⁻¹ : _ˣ).val * (s.map (U.val * z * (U⁻¹ : _ˣ).val) * (U.val * z * (U⁻¹ : _ˣ).val))
        * U.val := by
    intro z
    rw [hU]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  intro x y hxy
  rw [key, key, ← add_mul, ← mul_add] at hxy
  have hin : s.map (U.val * x * (U⁻¹ : _ˣ).val) * (U.val * x * (U⁻¹ : _ˣ).val)
      + s.map (U.val * y * (U⁻¹ : _ˣ).val) * (U.val * y * (U⁻¹ : _ˣ).val) = 0 := by
    have := congrArg (fun M => U.val * M * (U⁻¹ : _ˣ).val) hxy
    simpa [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using this
  rw [key, hs _ _ hin]
  simp

/-- **A fixing normal form is pointed iff both factors are**: the cone of `fixTwist P Q` is the
product of the two cones. -/
theorem pointedA_fixTwist_iff (P Q : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (hP : (P : Matrix (Fin n) (Fin n) ℂ)ᴴ = (P : Matrix (Fin n) (Fin n) ℂ))
    (hQ : (Q : Matrix (Fin n) (Fin n) ℂ)ᴴ = (Q : Matrix (Fin n) (Fin n) ℂ)) :
    PointedA (fixTwist P Q hP hQ)
      ↔ Pointed (hermitianStar P hP) ∧ Pointed (hermitianStar Q hQ) := by
  constructor
  · intro h
    refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
    · have h0 := h (x, 0) (y, 0) (Prod.ext hxy (by simp))
      exact congrArg Prod.fst h0
    · have h0 := h (0, x) (0, y) (Prod.ext (by simp) hxy)
      exact congrArg Prod.snd h0
  · rintro ⟨hp, hq⟩ x y hxy
    exact Prod.ext (hp x.1 y.1 (congrArg Prod.fst hxy)) (hq x.2 y.2 (congrArg Prod.snd hxy))

/-- `e₀₀ᴴ = e₀₀`. -/
theorem single_zero_conjTranspose [NeZero n] :
    (Matrix.single (0 : Fin n) 0 (1 : ℂ))ᴴ = Matrix.single (0 : Fin n) 0 (1 : ℂ) := by
  ext a b
  rw [conjTranspose_apply]
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    simp
  · rw [Matrix.single_apply_of_ne _ _ _ _ _ (by tauto), Matrix.single_apply_of_ne _ _ _ _ _ (by
  tauto)]
    simp

/-- **The plain swap is not pointed**: with `x = (e₀₀, e₀₀)` and `y = (e₀₀, −e₀₀)`,
`x⋆x = (e₀₀, e₀₀)` and `y⋆y = (−e₀₀, −e₀₀)`. -/
theorem not_pointedA_swapTwist_one [NeZero n] :
    ¬ PointedA (swapTwist (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ)) := by
  intro h
  set e : Matrix (Fin n) (Fin n) ℂ := Matrix.single (0 : Fin n) 0 (1 : ℂ) with he_def
  have hee : e * e = e := by
    rw [he_def, Matrix.single_mul_single_same, mul_one]
  have hmap : ∀ X Y : Matrix (Fin n) (Fin n) ℂ,
      (swapTwist (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ)).map (X, Y) = (Yᴴ, Xᴴ) := by
    intro X Y
    rw [swapTwist_apply]
    simp
  have hx : (swapTwist (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ)).map (e, e) * (e, e) = (e, e) := by
    rw [hmap, Prod.mk_mul_mk, he_def, single_zero_conjTranspose, ← he_def, hee]
  have hy : (swapTwist (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ)).map (e, -e) * (e, -e) = (-e, -e) := by
    rw [hmap, Prod.mk_mul_mk, conjTranspose_neg, he_def, single_zero_conjTranspose, ← he_def,
      neg_mul, mul_neg, hee]
  have h0 := h (e, e) (e, -e) (by rw [hx, hy]; simp)
  rw [hx] at h0
  have h1 := congrArg Prod.fst h0
  have := congrFun (congrFun h1 0) 0
  simp [he_def] at this

/-- **NO SWAPPING ⋆-STRUCTURE IS POINTED**: every one is inner-conjugate to the plain swap
(`swapping_innerConjugate`). -/
theorem not_pointedA_of_swaps [NeZero n]
    (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ))
    (hs : s.map (1, 0) = (0, 1)) : ¬ PointedA s := fun h =>
  not_pointedA_swapTwist_one
    (pointedA_of_innerConjugate (swapping_innerConjugate s _ hs (swapTwist_swaps 1)) h)

/-- `fixTwist 1 1` is the componentwise conjugate transpose, as a map. -/
theorem fixTwist_one_one_map (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    (fixTwist (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) 1 (by simp) (by simp)).map p
      = (prodConjTransposeC n n).map p := by
  obtain ⟨X, Y⟩ := p
  rw [fixTwist_apply]
  simp [prodConjTransposeC, prodConjTranspose]

/-- The componentwise conjugate transpose is pointed. -/
theorem pointedA_prodConjTransposeC : PointedA (prodConjTransposeC n n) := by
  refine pointedA_congr fixTwist_one_one_map ?_
  rw [pointedA_fixTwist_iff, hermitianStar_one]
  exact ⟨pointed_conjTransposeStar n, pointed_conjTransposeStar n⟩

/-- **THE POINTED ⋆-STRUCTURES ON `Mₙ(ℂ) × Mₙ(ℂ)` ARE EXACTLY ONE INNER CLASS — the componentwise
conjugate transpose's.** A pointed structure fixes the factors (no swapping one is pointed), so it
is `fixTwist P Q` with both factors pointed, hence both definite, hence inner-conjugate to
`fixTwist 1 1 = prodConjTransposeC`; and conversely pointedness is an inner-conjugacy invariant. -/
theorem pointedA_iff_innerConjugate [NeZero n]
    (s : StarStrC (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)) :
    PointedA s ↔ InnerConjugate (prodConjTransposeC n n) s := by
  constructor
  · intro h
    rcases matrixProd_classification_eq s with ⟨P, Q, hP, hQ, hmap⟩ | ⟨S, hS⟩
    · have hfix : PointedA (fixTwist P Q hP hQ) :=
        pointedA_congr (fun p => by obtain ⟨X, Y⟩ := p; rw [hmap, fixTwist_apply]) h
      obtain ⟨hp, hq⟩ := (pointedA_fixTwist_iff P Q hP hQ).mp hfix
      rw [pointed_iff_definite] at hp hq
      have h11 : InnerConjugate (fixTwist (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) 1 (by simp) (by simp))
          (fixTwist P Q hP hQ) := by
        rw [fixTwist_innerConjugate_iff_usignature, Units.val_one, usignature_one]
        exact ⟨hp, hq⟩
      have h0 : InnerConjugate (prodConjTransposeC n n)
          (fixTwist (1 : (Matrix (Fin n) (Fin n) ℂ)ˣ) 1 (by simp) (by simp)) :=
        innerConjugate_of_map_eq fun X Y => (fixTwist_one_one_map (X, Y)).symm
      have h2 : InnerConjugate (fixTwist P Q hP hQ) s :=
        innerConjugate_of_map_eq fun X Y => by rw [hmap, fixTwist_apply]
      exact innerConjugate_trans h0 (innerConjugate_trans h11 h2)
    · exact absurd h (not_pointedA_of_swaps s ((swapping_iff s).mpr ⟨S, hS⟩))
  · intro h
    exact pointedA_of_innerConjugate h pointedA_prodConjTransposeC

/-- **In unit 160's count**: of the `(n/2 + 1)² + 1` inner classes on `Mₙ(ℂ) × Mₙ(ℂ)`, exactly one
representative is pointed — `classRep (Sum.inl (0, 0))`, the pair of sign twists with no plus
sign, i.e. the class of `(−1, −1)`, which is the conjugate transpose's class (`hermitianStar (−P)
= hermitianStar P`). -/
theorem pointedA_classRep_iff [NeZero n] (i : ClassIndex n) :
    PointedA (classRep i) ↔ i = Sum.inl (0, 0) := by
  rcases i with ⟨p, q⟩ | ⟨⟩
  · rw [classRep_inl, pointedA_fixTwist_iff, pointed_iff_definite, pointed_iff_definite,
      usignature_halfTwist p.val (by omega), usignature_halfTwist q.val (by omega)]
    constructor
    · rintro ⟨hp, hq⟩
      rw [Sym2.eq_iff] at hp hq
      have hp0 : p.val = 0 := by omega
      have hq0 : q.val = 0 := by omega
      have hp' : p = 0 := Fin.ext hp0
      have hq' : q = 0 := Fin.ext hq0
      rw [hp', hq']
    · intro h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Sum.inl.inj h)
      simp [Sym2.eq_swap]
  · rw [classRep_inr]
    simp only [reduceCtorEq, iff_false]
    exact not_pointedA_of_swaps _ (swapTwist_swaps 1)

end StarStructurePointed
