/-
  PinImage.lean — the pin group covers exactly half of O(1,3), and the
  half it misses is space inversion.

  WHY. `SpinSurjective` closed W7 step (d): `Spin(1,3) ⧸ {±1} ≅ SO⁺(1,3)`.
  The sentence a reader supplies next, by analogy and without being told,
  is **"and Pin(1,3) covers O(1,3)"**. It does not — not in Mathlib's
  normalisation — and this file proves the exact statement instead of
  leaving the analogy standing.

  The question only became askable today. While the spin image was
  unknown, "what does the LARGER group reach" had no baseline; with
  SO⁺(1,3) reached in full it becomes a coset count.

  WHAT DECIDES IT. Mathlib's `pinGroup` asks `star x · x = 1`. For a
  single vector that reads `−Q(v) = 1`, so the generators are the
  SPACELIKE units and the timelike ones are excluded. `SpinOrthochronous`'s
  `chronParity` already carries the invariant that settles the
  consequence: for every Lipschitz element there is a scalar `n` with
  `star x · x = n` and `0 < (det Λ · n) · Λ⁰₀`. **Unitarity is exactly
  `n = 1`**, so for a pin element `det Λ` and `Λ⁰₀` have the SAME SIGN.
  That is the whole theorem, and the induction that proves it was written
  a day earlier for a different purpose.

  WHAT THIS FILE PROVES:
  1. **`pin_det_chron_same_sign`** — `0 < det(Λ) · Λ⁰₀` for every pin
     element.
  2. **`mem_pin_image_iff`** — and that is the ONLY constraint: a real
     4×4 matrix is the Lorentz matrix of a pin element **iff** it is
     Lorentz and satisfies `0 < det · Λ⁰₀`. Both directions. The reverse
     is the orbit argument again, one coset up: multiply by the
     reflection in `e₁` and land in SO⁺(1,3), which `SpinSurjective`
     covers.
  3. **`space_inversion_not_in_pin_image`** — so `diag(1,−1,−1,−1)` is
     NOT reached. It is a genuine Lorentz matrix (it is the Gram matrix),
     it has determinant −1 and `Λ⁰₀ = 1`, and the product of those signs
     is negative. **`pin_not_onto_O13`** states the consequence.
  4. **`pin_strictly_larger_than_spin`** — and the negative is not the
     whole story: the reflection in `e₁` IS a pin element, with
     determinant −1, so the pin image strictly contains the spin image.
     Two of O(1,3)'s four components, not one and not four.

  WHAT THIS DOES NOT DO. It says nothing about a DIFFERENT normalisation
  of the pin group. `Pin⁺` and `Pin⁻` are genuinely different groups and
  which one Mathlib's definition gives is a convention; the theorem here
  is about `pinGroup` as Mathlib defines it (root namespace, in
  `Mathlib/LinearAlgebra/CliffordAlgebra/SpinGroup.lean`; this line said
  `CliffordAlgebra.pinGroup`, which does not resolve — ERRATUM 50), and the
  header says so rather than saying "the pin group". Nothing here is
  topological either — same caveat as `SpinSurjective` §5, ASSUMPTIONS 41
  and 42.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SpinSurjective

namespace PinImage

open SpinVectorRep SpinToOrthogonal MinkowskiSignature LorentzGroup
open SpinToLorentzMat SpinDetOne SpinOrthochronous SpinPair
open LipschitzVectorRep LorentzReflection LorentzOrthochronousSign
open SpinMinkowskiBridge SpinSurjective
open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

/-! ## 1. A pin element, and its determinant

A pin element is a Lipschitz unit whose star-square is 1. Stated with
the two conditions as hypotheses rather than through `pinGroup`
membership, because everything downstream wants the UNIT and Mathlib's
`pinGroup` is a submonoid of the algebra; §5 supplies the bridge.
-/

theorem det_lipMat {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) :
    (lipMat hx).det = LinearMap.det (lipToEndo hx) := by
  rw [lipMat, LinearMap.det_toMatrix']
  exact LinearMap.det_conj (lipToEndo hx) coordEquiv

/-- Every Lorentz matrix has determinant `±1`. Immediate from
    `ΛᵀGΛ = G` and `det G = −1 ≠ 0`; the estate had this only for the
    SL₂(ℂ) image (`det_lorentzMat_sq`). -/
theorem det_sq_of_isLorentz {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : IsLorentzMat M) : M.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h
  have hg : (gram : Matrix (Fin 4) (Fin 4) ℝ).det = -1 := LorentzGroup.det_gram
  rw [hg] at h
  nlinarith [h]

/-! ## 2. The sign law

`chronParity` carries a scalar `n` with `star x · x = n`, and the
invariant `0 < (det Λ · n) · Λ⁰₀`. Unitarity says `n = 1`.
-/

/-- **For a pin element, the determinant and `Λ⁰₀` have the same sign.**
    The whole content of this file; the induction behind it was written
    a day earlier for the spin case, where `n = 1` came from
    `unitary` and the conclusion was `0 < Λ⁰₀`. -/
theorem pin_det_chron_same_sign {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃)
    (hu : star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1) :
    0 < (lipMat hx).det * (lipMat hx) 0 0 := by
  obtain ⟨n, _, hnorm, hpos⟩ := chronParity hx
  have hn1 : n = 1 := by
    have hcast : algebraMap ℝ Cl n = algebraMap ℝ Cl 1 := by
      rw [← hnorm, hu, map_one]
    exact FaithfulSMul.algebraMap_injective ℝ Cl hcast
  have h := hpos hx
  rw [hn1, mul_one] at h
  rwa [det_lipMat]

/-! ## 3. The reflection in `e₁`, as the coset representative

It is a pin element — `star(ι v) · ι v = −Q₁₃ v`, which is `1` exactly
when `v` is a spacelike unit — and its matrix is
`diag(−1, 1, −1, −1)`: determinant `−1`, `Λ⁰₀ = −1`. Same sign, as §2
requires, and in the component the spin group cannot reach.
-/

/-- `P₁`, the Minkowski reflection in the `x` axis. -/
def P₁ : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, -1, -1]

theorem lipMat_e₁ : lipMat (vecUnit_mem e₁ Q₁₃_e₁_ne) = P₁ := by
  rw [lipMat_vecUnit, reflMat_e₁, P₁]

theorem vecUnit_e₁_unitary :
    star (((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl))
      * ((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl) = 1 := by
  change star (ι Q₁₃ e₁) * ι Q₁₃ e₁ = 1
  rw [star_ι, neg_mul, ι_sq_scalar, Q₁₃_e₁]
  simp

theorem det_P₁ : P₁.det = -1 := by
  rw [P₁, Matrix.det_diagonal, Fin.prod_univ_four]
  simp

theorem P₁_zero_zero : P₁ 0 0 = -1 := by
  rw [P₁, Matrix.diagonal_apply_eq]
  norm_num

theorem P₁_isLorentz : IsLorentzMat P₁ := by
  rw [← lipMat_e₁]
  exact lipMat_isLorentz _

theorem P₁_sq : P₁ * P₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [P₁, Matrix.mul_apply, Matrix.diagonal_apply]

/-! ## 4. The image, exactly

One direction is §2. The other is the orbit argument one coset up: a
matrix with `det = −1` and `Λ⁰₀ < 0` becomes, after multiplication by
`P₁`, a matrix with `det = 1` and `Λ⁰₀ > 0`, which `SpinSurjective`
covers.
-/

/-- The reverse inclusion. -/
theorem pin_reaches (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : IsLorentzMat M)
    (hsign : 0 < M.det * M 0 0) :
    ∃ (x : Clˣ) (hx : x ∈ lipschitzGroup Q₁₃),
      star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1 ∧ lipMat hx = M := by
  have hd2 := det_sq_of_isLorentz hM
  have hd : M.det = 1 ∨ M.det = -1 := by
    rcases mul_self_eq_one_iff.1 (by nlinarith [hd2] : M.det * M.det = 1) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hd with hd | hd
  · -- proper: already in the spin image
    have h0 : 0 < M 0 0 := by rw [hd, one_mul] at hsign; exact hsign
    obtain ⟨g, hg⟩ := spin_surjective M hM hd h0
    refine ⟨spinGroup.toUnits g, units_mem_lip (toUnits_mem g), g.2.1.2.1, ?_⟩
    rw [← spinToO13_eq_lipMat g]
    exact hg
  · -- improper: multiply by the reflection and land in SO⁺(1,3)
    have h0 : M 0 0 < 0 := by
      rw [hd] at hsign
      nlinarith [hsign]
    have hN : IsLorentzMat (P₁ * M) := P₁_isLorentz.mul hM
    have hNdet : (P₁ * M).det = 1 := by
      rw [Matrix.det_mul, det_P₁, hd]; ring
    have hN0 : 0 < (P₁ * M) 0 0 :=
      orthochronous_mul_neg_neg P₁_isLorentz hM (by rw [P₁_zero_zero]; norm_num) h0
    obtain ⟨g, hg⟩ := spin_surjective (P₁ * M) hN hNdet hN0
    refine ⟨vecUnit e₁ Q₁₃_e₁_ne * spinGroup.toUnits g,
      mul_mem (vecUnit_mem e₁ Q₁₃_e₁_ne) (units_mem_lip (toUnits_mem g)), ?_, ?_⟩
    · have ha := vecUnit_e₁_unitary
      have hb : star ((spinGroup.toUnits g : Clˣ) : Cl)
          * ((spinGroup.toUnits g : Clˣ) : Cl) = 1 := g.2.1.2.1
      change star (((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl)
          * ((spinGroup.toUnits g : Clˣ) : Cl))
        * (((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl)
          * ((spinGroup.toUnits g : Clˣ) : Cl)) = 1
      rw [star_mul]
      calc star ((spinGroup.toUnits g : Clˣ) : Cl)
            * star ((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl)
            * (((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl)
              * ((spinGroup.toUnits g : Clˣ) : Cl))
          = star ((spinGroup.toUnits g : Clˣ) : Cl)
            * (star ((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl)
              * ((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl))
            * ((spinGroup.toUnits g : Clˣ) : Cl) := by noncomm_ring
        _ = 1 := by rw [ha, mul_one, hb]
    · have hg' : ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ)
          : Matrix (Fin 4) (Fin 4) ℝ) = P₁ * M := hg
      rw [lipMat_mul (vecUnit_mem e₁ Q₁₃_e₁_ne) (units_mem_lip (toUnits_mem g)),
        lipMat_e₁, ← spinToO13_eq_lipMat g, hg',
        ← Matrix.mul_assoc, P₁_sq, Matrix.one_mul]

/-- **THE PIN IMAGE, EXACTLY.** A real 4×4 matrix is the Lorentz matrix
    of a pin element iff it is Lorentz and `det · Λ⁰₀ > 0`. -/
theorem mem_pin_image_iff (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (∃ (x : Clˣ) (hx : x ∈ lipschitzGroup Q₁₃),
        star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1 ∧ lipMat hx = M)
      ↔ (IsLorentzMat M ∧ 0 < M.det * M 0 0) := by
  constructor
  · rintro ⟨x, hx, hu, rfl⟩
    exact ⟨lipMat_isLorentz hx, pin_det_chron_same_sign hx hu⟩
  · rintro ⟨hM, hsign⟩
    exact pin_reaches M hM hsign

/-! ## 5. Two of four components, and which two -/

/-- **Space inversion is not reached.** The Gram matrix IS a Lorentz
    matrix — that is `gram_chron` — with determinant `−1` and
    `Λ⁰₀ = 1`, so the product of the signs is negative. -/
theorem space_inversion_not_in_pin_image :
    IsLorentzMat (gram : Matrix (Fin 4) (Fin 4) ℝ)
      ∧ ¬ ∃ (x : Clˣ) (hx : x ∈ lipschitzGroup Q₁₃),
            star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1
              ∧ lipMat hx = (gram : Matrix (Fin 4) (Fin 4) ℝ) := by
  refine ⟨gram_chron.1, ?_⟩
  intro h
  have hsign := ((mem_pin_image_iff _).1 h).2
  rw [LorentzGroup.det_gram] at hsign
  have h00 : (gram : Matrix (Fin 4) (Fin 4) ℝ) 0 0 = 1 := by
    rw [gram, Matrix.diagonal_apply_eq]; simp [mw]
  rw [h00] at hsign
  norm_num at hsign

/-- **So the pin group is NOT onto O(1,3)** — the sentence the analogy
    with `SpinSurjective` would supply, refuted. -/
theorem pin_not_onto_O13 :
    ¬ ∀ M : Matrix (Fin 4) (Fin 4) ℝ, IsLorentzMat M →
        ∃ (x : Clˣ) (hx : x ∈ lipschitzGroup Q₁₃),
          star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1 ∧ lipMat hx = M := by
  intro h
  exact space_inversion_not_in_pin_image.2
    (h (gram : Matrix (Fin 4) (Fin 4) ℝ) gram_chron.1)

/-- **And it is not merely the spin group either.** The reflection in
    `e₁` is a pin element of determinant `−1`, which no spin element is
    (`SpinDetOne.det_spinToO13_eq_one`). Two components, not one. -/
theorem pin_strictly_larger_than_spin :
    (∃ (x : Clˣ) (hx : x ∈ lipschitzGroup Q₁₃),
        star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1
          ∧ (lipMat hx).det = -1)
      ∧ ∀ g : spinGroup Q₁₃, (lmat g).det = 1 := by
  refine ⟨⟨vecUnit e₁ Q₁₃_e₁_ne, vecUnit_mem e₁ Q₁₃_e₁_ne, vecUnit_e₁_unitary, ?_⟩,
    lmat_det⟩
  rw [lipMat_e₁, det_P₁]

/-! ## 6. Review round 34 — that §4 is a constraint and not a tautology

Three ways this file could be saying nothing.

* If EVERY Lorentz matrix satisfied `0 < det · Λ⁰₀`, `mem_pin_image_iff`
  would be "pin covers O(1,3)" in disguise and §5 would be false. It is
  not: `gram` is the counterexample and §5 is the proof.
* If NO Lorentz matrix with `det = −1` satisfied it, the pin image would
  be the spin image and the word "pin" would be doing no work. It is
  not: `P₁` has `det = −1` and `Λ⁰₀ = −1`.
* If `pinGroup` membership did not actually imply the unitarity §2
  consumes, the whole file would be about a hypothesis nothing
  satisfies. `mem_pin_bridge` supplies the implication from Mathlib's
  definition.
-/

/-- Mathlib's `pinGroup` membership, unpacked into the two facts §2
    consumes. Without this the file would be about a hypothesis and not
    about the pin group. -/
theorem mem_pin_bridge {y : Cl} (hy : y ∈ pinGroup Q₁₃) :
    ∃ (x : Clˣ) (_ : x ∈ lipschitzGroup Q₁₃),
      (x : Cl) = y ∧ star ((x : Clˣ) : Cl) * ((x : Clˣ) : Cl) = 1 := by
  obtain ⟨h1, h2, -⟩ := hy
  obtain ⟨x, hx, rfl⟩ := h1
  exact ⟨x, hx, rfl, h2⟩

/-- And the reflection in `e₁` really is in Mathlib's `pinGroup`, so §3's
    coset representative is not a fiction of this file's hypotheses. -/
theorem vecUnit_e₁_mem_pin :
    ((vecUnit e₁ Q₁₃_e₁_ne : Clˣ) : Cl) ∈ pinGroup Q₁₃ := by
  refine ⟨?_, vecUnit_e₁_unitary, ?_⟩
  · exact lipschitzGroup.coe_mem_iff_mem.2 (vecUnit_mem e₁ Q₁₃_e₁_ne)
  · change ι Q₁₃ e₁ * star (ι Q₁₃ e₁) = 1
    rw [star_ι, mul_neg, ι_sq_scalar, Q₁₃_e₁]
    simp

/-- The sign law is a genuine CONSTRAINT: there is a Lorentz matrix it
    excludes and a Lorentz matrix it admits with `det = −1`. Both halves,
    so neither reading of §4 collapses. -/
theorem sign_law_is_a_constraint :
    (IsLorentzMat (gram : Matrix (Fin 4) (Fin 4) ℝ)
        ∧ ¬ (0 < (gram : Matrix (Fin 4) (Fin 4) ℝ).det
              * (gram : Matrix (Fin 4) (Fin 4) ℝ) 0 0))
      ∧ (IsLorentzMat P₁ ∧ P₁.det = -1 ∧ 0 < P₁.det * P₁ 0 0) := by
  refine ⟨⟨gram_chron.1, ?_⟩, P₁_isLorentz, det_P₁, ?_⟩
  · rw [LorentzGroup.det_gram,
      show (gram : Matrix (Fin 4) (Fin 4) ℝ) 0 0 = 1 by
        rw [gram, Matrix.diagonal_apply_eq]; simp [mw]]
    norm_num
  · rw [det_P₁, P₁_zero_zero]
    norm_num

end

end PinImage
