/-
  SpinMeetsSL2.lean — the two chains are compared, not merely co-located.

  WHAT THE RE-SWEEP FOUND. `SpinToLorentzMat` put the Clifford/spin chain
  into `LorentzGroup.O13`, the same object the SL₂(ℂ) chain has lived in
  since it was built, and its header said flatly what that did NOT give:
  "no theorem here relates the two homomorphisms, so a shared codomain is
  not a comparison". That is still true in general — relating them
  everywhere IS the double-cover statement, which is W7 step (d). But it
  is not true at every level of generality, and the re-sweep asked the
  question the header did not: **are the specific spin elements the
  estate has built actually hit by the SL₂(ℂ) map?**

  They are, and the two ingredients were both already on the shelf. The
  estate proved SL₂(ℂ) ↠ SO⁺(1,3) in `LorentzSurjectivity` on 1 Aug;
  this week's work computed the two spin elements as explicit Lorentz
  matrices. All that was missing was checking those matrices satisfy
  SO⁺(1,3)'s two extra conditions — det = 1 and Λ⁰₀ > 0.

  WHAT THIS FILE PROVES:
  1. **`spinToO13_R₁₂'_mem_SOplus`** and **`spinToO13_B'_mem_SOplus`** —
     both spin elements land in the PROPER ORTHOCHRONOUS group, not
     merely in O(1,3).
  2. **`R₁₂'_in_SL2_image`** and **`B'_in_SL2_image`** — hence each is
     `Λ(A)` for some `A ∈ SL₂(ℂ)`. **The first theorems in the estate
     relating the Clifford chain to the SL₂(ℂ) chain.**
  3. **`SOplus13_lt_O13`** — added by review round 24, and it is what
     makes item 1 worth proving: SO⁺(1,3) is STRICTLY smaller than
     O(1,3), witnessed by the Gram matrix, which is a Lorentz matrix of
     determinant −1. Without it, "both elements land in SO⁺(1,3)" could
     have been free.
  4. `det_boost_block` — the determinant recomputed by a second route,
     since the Laplace expansion in item 1 is opaque.

  WHAT THIS DOES NOT DO, and the gap is exactly as wide as it was.
  Two elements are not a group. This says nothing about whether the
  spin image lies in SO⁺(1,3) in general — that needs `det = 1` and
  `Λ⁰₀ > 0` for EVERY spin element, and the `det` half was probed and
  found blocked (no matrix determinant lemma in Mathlib; see the
  watchlist). It says nothing about whether the two images coincide.
  **W7 step (d) is untouched.** What has changed is that the two chains
  now have a theorem between them rather than only a shared codomain.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/

import SpinToLorentzMat
import LorentzSurjectivity
import LorentzIsometryEquiv

open MinkowskiSignature LorentzGroup SpinVectorRep SpinToOrthogonal
open SpinMinkowskiBridge SpinToLorentzMat CliffordAlgebra CliffordRealMinkowski
open LorentzSurjectivity
open scoped Matrix

noncomputable section

namespace SpinMeetsSL2

/-! ## 1. The determinants -/

/-- The boost matrix has determinant 1. Laplace expansion; Mathlib has
    `det_fin_two` and `det_fin_three` but no `det_fin_four`. -/
theorem det_boost_matrix :
    (!![17/8, -(15/8), 0, 0; -(15/8), 17/8, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]
      : Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  norm_num

theorem det_spinToO13_B' :
    ((spinToO13 B' : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
  rw [spinToO13_B'_matrix]
  exact det_boost_matrix

/-! ## 2. The time-time entries are positive -/

theorem entry00_R₁₂' :
    ((spinToO13 R₁₂' : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) 0 0 = 1 := by
  rw [spinToO13_R₁₂'_matrix]
  simp

theorem entry00_B' :
    ((spinToO13 B' : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ) 0 0 = 17 / 8 := by
  rw [spinToO13_B'_matrix]
  simp

/-! ## 3. Both land in SO⁺(1,3) -/

/-- **The π-rotation is proper and orthochronous.** -/
theorem spinToO13_R₁₂'_mem_SOplus :
    (spinToO13 R₁₂' : Matrix.GeneralLinearGroup (Fin 4) ℝ) ∈ SOplus13 :=
  ⟨(spinToO13 R₁₂').2, det_spinToO13_R₁₂', by rw [entry00_R₁₂']; norm_num⟩

/-- **And so is the boost.** -/
theorem spinToO13_B'_mem_SOplus :
    (spinToO13 B' : Matrix.GeneralLinearGroup (Fin 4) ℝ) ∈ SOplus13 :=
  ⟨(spinToO13 B').2, det_spinToO13_B', by rw [entry00_B']; norm_num⟩

/-! ## 4. Hence both are hit by SL₂(ℂ)

The estate proved `SL₂(ℂ) ↠ SO⁺(1,3)` in `LorentzSurjectivity`. Combined
with §3, each spin element the Clifford chain produced is the image of an
SL₂(ℂ) matrix — which is the first statement in the estate relating the
two chains rather than merely placing them in the same group. -/

/-- **The π-rotation from the spin side is `Λ(A)` for some `A ∈ SL₂(ℂ)`.** -/
theorem R₁₂'_in_SL2_image :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1),
      lorentzUnit A hA = (spinToO13 R₁₂' : Matrix.GeneralLinearGroup (Fin 4) ℝ) :=
  SOplus13_surjective _ spinToO13_R₁₂'_mem_SOplus

/-- **And so is the boost.** -/
theorem B'_in_SL2_image :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1),
      lorentzUnit A hA = (spinToO13 B' : Matrix.GeneralLinearGroup (Fin 4) ℝ) :=
  SOplus13_surjective _ spinToO13_B'_mem_SOplus

/-- Stated without the existential, as the sentence it is: the images of
    the two chains overlap. Not that they coincide — see the header. -/
theorem images_overlap :
    ∃ M : Matrix.GeneralLinearGroup (Fin 4) ℝ,
      (∃ g : spinGroup Q₁₃, (spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) = M)
      ∧ (∃ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1), lorentzUnit A hA = M)
      ∧ M ≠ 1 := by
  refine ⟨(spinToO13 R₁₂' : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    ⟨R₁₂', rfl⟩, R₁₂'_in_SL2_image, ?_⟩
  intro h
  exact spinToO13_R₁₂'_ne_one (Subtype.ext h)

/-! ## 5. Why §3 was worth proving, and a second route to the determinant

Review round 24's fold. -/

/-- The determinant, recomputed. `det_boost_matrix` goes through Laplace
    expansion, which is opaque; the matrix is block diagonal with a 2×2
    boost block and `I₂`, and `det_fin_two` computes that block's
    determinant directly. Same number, different lemma, and this is
    where `17² − 15² = 8²` is visibly doing the work. -/
theorem det_boost_block :
    (!![17/8, -(15/8); -(15/8), 17/8] : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  norm_num

/-- **SO⁺(1,3) is strictly smaller than O(1,3)**, witnessed by the Gram
    matrix. This is what makes §3 worth proving: if every element of
    O(1,3) were proper and orthochronous, `spinToO13_R₁₂'_mem_SOplus`
    would follow from membership in `O13` alone and would say nothing. -/
theorem gramO13_not_mem_SOplus :
    (LorentzIsometryEquiv.gramO13 :
      Matrix.GeneralLinearGroup (Fin 4) ℝ) ∉ SOplus13 := by
  rintro ⟨-, hdet, -⟩
  rw [LorentzIsometryEquiv.det_gramO13] at hdet
  norm_num at hdet

theorem SOplus13_lt_O13 :
    ∃ M : Matrix.GeneralLinearGroup (Fin 4) ℝ, M ∈ O13 ∧ M ∉ SOplus13 :=
  ⟨(LorentzIsometryEquiv.gramO13 : Matrix.GeneralLinearGroup (Fin 4) ℝ),
    LorentzIsometryEquiv.gramO13.2, gramO13_not_mem_SOplus⟩

/-- And the preimage in §4 is not a trivial one. `R₁₂'_in_SL2_image` is
    an existential, worth much less if its witness could act trivially —
    `Λ(±1) = 1`. It cannot: whatever `A` is, its image is the
    π-rotation, which is not the identity. -/
theorem preimage_nontrivial (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1)
    (heq : lorentzUnit A hA
      = (spinToO13 R₁₂' : Matrix.GeneralLinearGroup (Fin 4) ℝ)) :
    lorentzUnit A hA ≠ 1 := by
  rw [heq]
  intro h
  exact spinToO13_R₁₂'_ne_one (Subtype.ext h)

end SpinMeetsSL2
