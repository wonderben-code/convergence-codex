/-
  SpinDetOne.lean — every spin element is a PROPER Lorentz transformation.

  WHAT THIS CLOSES. W7 step (d) asks three things of the spin
  representation: that the image lies in SO⁺(1,3), that it is onto, and
  that the kernel is ±1. The kernel fell to `SpinKernel`. "Image inside
  SO⁺(1,3)" is two conditions — `det = 1` and `Λ⁰₀ > 0` — and this file
  proves the first of them, **for every element of `spinGroup Q₁₃`, not
  for a family**:

    **`det_spinToO13_eq_one (g : spinGroup Q₁₃) : (spinToO13 g).det = 1`**

  Orthochronicity is untouched, so the image question is half closed and
  no more. That is stated again at the bottom of this header because
  "every spin element is proper" is exactly the kind of sentence that
  gets rounded up.

  THE ARGUMENT, which is the classical one and is worth naming because
  the estate has now recorded two wrong guesses about which of its steps
  was hard. A spin element is a word in vectors; each vector acts by a
  reflection, which has determinant −1; an even word therefore has
  determinant +1; and spin elements are even because `involute` fixes
  them. Formally the induction cannot carry "word length", which is not
  a function of the group element, so it carries the pair
  **(determinant, behaviour under `involute`)** and the two move
  together:

    `parity : ∃ ε = ±1, det (lipToEndo hx) = ε ∧ involute x = ε • x`

  over `Subgroup.closure_induction` on `lipschitzGroup Q₁₃`. For a spin
  element `involute x = x`, and `ε = −1` would give `x = −x`, hence
  `2x = 0`, hence `x = 0` — impossible for a unit. So `ε = 1`.

  THE THREE INGREDIENTS were each built separately and each was recorded
  as absent or blocked at some point:
  * the reflection determinant `−1` — `LorentzReflection.det_reflMat`,
    which needed the matrix determinant lemma that ERRATUM 42 records as
    wrongly declared missing from Mathlib;
  * a group with generators to induct over — `LipschitzVectorRep`,
    since `spinGroup` is defined by conditions and has no closure
    principle;
  * `spinGroup.involute_eq` and `involute_ι`, both in Mathlib.

  WHERE THE EVENNESS HYPOTHESIS IS LOAD-BEARING, added by review round 26
  because §3 gives a reader no way to see it. **`vecUnit_not_mem_spinGroup`
  — no vector unit is a spin element — and its proof is the collision
  between §1 and §4**: a vector unit acts with determinant −1 and a spin
  element with +1, so had any vector unit been a spin element two theorems
  here would contradict each other. `involute_ne_vecUnit` shows the same
  thing one step earlier, and `parity_neg_realised` confirms the sign the
  induction carries genuinely takes both values.

  THE ROTATION'S DETERMINANT HAS NOW BEEN COMPUTED THREE WAYS — an
  explicit diagonal matrix (`SpinToLorentzMat`), two reflection
  determinants (`LorentzReflection`), and the parity induction here — and
  they agree.

  WHAT IS STILL OPEN, precisely. `Λ⁰₀ > 0` has no route, no sketch and no
  probe; `SOplus13` membership therefore does NOT follow from this file.
  Surjectivity onto SO⁺(1,3) is untouched. **W7 step (d) is not closed**,
  and what has changed is that one of its two remaining parts is now half
  done rather than entirely open.

  **SUPERSEDED 8 AUG 2026** — the sentence above was true when written
  and is now false: `SpinSurjective.spin_surjective` proves the spin map
  onto SO⁺(1,3), and `SpinSurjective.spinDoubleCover` bundles W7 step (d)
  as `Spin(1,3) ⧸ {±1} ≃* SO⁺(1,3)`. Left standing per the house rule;
  what remains open is the TOPOLOGICAL reading (ASSUMPTIONS 41 and 42),
  not the algebraic one.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import LipschitzVectorRep
import LorentzReflection

namespace SpinDetOne

open SpinVectorRep SpinPair SpinToOrthogonal LipschitzVectorRep LorentzReflection
open MinkowskiSignature LorentzGroup SpinMinkowskiBridge SpinToLorentzMat
open CliffordAlgebra CliffordRealMinkowski
open scoped Matrix

noncomputable section

/-! ## 1. Determinants read through the coordinate map

Everything below computes determinants of endomorphisms of
`(ℝ×ℝ)×(ℝ×ℝ)`, but the matrices the estate can compute live on
`Fin 4 → ℝ`. This is the bridge, and it is used three times.
-/

/-- If a linear map on `V` is the matrix `M` in coordinates, its
    determinant is `M`'s. -/
theorem det_of_coord (f : V →ₗ[ℝ] V) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∀ u, coordEquiv (f u) = M *ᵥ coordEquiv u) :
    LinearMap.det f = M.det := by
  have hconj : (coordEquiv : V →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ f ∘ₗ
      (coordEquiv.symm : (Fin 4 → ℝ) →ₗ[ℝ] V) = Matrix.mulVecLin M := by
    refine LinearMap.ext fun u => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    rw [h, LinearEquiv.apply_symm_apply]
  have hd : LinearMap.det (Matrix.mulVecLin M) = M.det := by
    rw [← LinearMap.det_toMatrix' (Matrix.mulVecLin M)]
    congr 1
    ext i j
    simp [LinearMap.toMatrix'_apply, Matrix.mulVecLin, Matrix.mulVec_single]
  rw [← LinearMap.det_conj f coordEquiv, hconj, hd]

/-- **A generator acts with determinant −1.** `LipschitzVectorRep` said a
    vector unit acts as `vreflect v`; `LorentzReflection` said that
    reflection's matrix has determinant −1; this joins them. -/
theorem det_lipToEndo_vecUnit {v : V} (hv : Q₁₃ v ≠ 0) :
    LinearMap.det (lipToEndo (vecUnit_mem v hv)) = -1 := by
  rw [det_of_coord _ (reflMat (coordEquiv v)) fun u => by
    rw [lipToEndo_vecUnit hv u, coord_vreflect hv u]]
  exact det_reflMat (by rwa [minkowskiForm_coordEquiv])

/-! ## 2. `involute` on inverses

The induction's `inv` case needs that the sign survives inversion. It is
not automatic from `involute` being a ring hom, because `x⁻¹` is a unit
inverse rather than an algebra operation.
-/

theorem involute_inv {x : Clˣ} {ε : ℝ} (hε : ε * ε = 1)
    (h : involute (x : Cl) = ε • (x : Cl)) :
    involute ((x⁻¹ : Clˣ) : Cl) = ε • (((x⁻¹ : Clˣ) : Cl)) := by
  have hmul : involute ((x⁻¹ : Clˣ) : Cl) * involute ((x : Cl)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [h] at hmul
  have hcancel : (ε • (x : Cl)) * (ε • (((x⁻¹ : Clˣ) : Cl))) = 1 := by
    rw [smul_mul_smul_comm, hε, Units.mul_inv, one_smul]
  calc involute ((x⁻¹ : Clˣ) : Cl)
      = involute ((x⁻¹ : Clˣ) : Cl) * ((ε • (x : Cl)) * (ε • (((x⁻¹ : Clˣ) : Cl)))) := by
        rw [hcancel, mul_one]
    _ = (involute ((x⁻¹ : Clˣ) : Cl) * (ε • (x : Cl))) * (ε • (((x⁻¹ : Clˣ) : Cl))) := by
        rw [mul_assoc]
    _ = ε • (((x⁻¹ : Clˣ) : Cl)) := by rw [hmul, one_mul]

/-! ## 3. The parity induction

The whole argument. `lipschitzGroup Q₁₃` is a `Subgroup.closure`, so
`Subgroup.closure_induction` applies — in its dependent form, which hands
the membership proof back, because `lipToEndo` is indexed by one.
-/

/-- **Determinant and `involute`-parity move together.** For every
    Lipschitz element there is a sign `ε = ±1` that is simultaneously the
    determinant of its action and the factor by which `involute` scales
    it. -/
theorem parity {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ LinearMap.det (lipToEndo hx) = ε
      ∧ involute (x : Cl) = ε • (x : Cl) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨v, hv⟩ := hy
    have hvne : Q₁₃ v ≠ 0 := generator_not_null hv.symm
    have hyeq : y = vecUnit v hvne := Units.ext hv.symm
    refine ⟨-1, Or.inr rfl, ?_, ?_⟩
    · exact Eq.trans (congrArg LinearMap.det
        (LinearMap.ext fun u => lipToEndo_congr _ (vecUnit_mem v hvne) hyeq u))
        (det_lipToEndo_vecUnit hvne)
    · rw [← hv, involute_ι]
      module
  | one =>
    refine ⟨1, Or.inl rfl, ?_, by simp⟩
    exact Eq.trans (congrArg LinearMap.det
      (LinearMap.ext fun u => lipToEndo_one u)) LinearMap.det_id
  | mul y z hy hz ihy ihz =>
    obtain ⟨εy, hεy, hdy, hiy⟩ := ihy
    obtain ⟨εz, hεz, hdz, hiz⟩ := ihz
    refine ⟨εy * εz, ?_, ?_, ?_⟩
    · rcases hεy with h1 | h1 <;> rcases hεz with h2 | h2 <;>
        rw [h1, h2] <;> norm_num
    · rw [show lipToEndo (mul_mem hy hz)
          = lipToEndo hy ∘ₗ lipToEndo hz from
        LinearMap.ext fun v => lipToEndo_mul hy hz v,
        LinearMap.det_comp, hdy, hdz]
    · rw [Units.val_mul, map_mul, hiy, hiz, smul_mul_smul_comm]
  | inv y hy ihy =>
    obtain ⟨ε, hε, hd, hi⟩ := ihy
    have hεsq : ε * ε = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    refine ⟨ε, hε, ?_, involute_inv hεsq hi⟩
    have hcomp : LinearMap.det (lipToEndo (inv_mem hy))
        * LinearMap.det (lipToEndo hy) = 1 := by
      rw [← LinearMap.det_comp]
      rw [show lipToEndo (inv_mem hy) ∘ₗ lipToEndo hy
          = LinearMap.id from
        LinearMap.ext fun v => lipToEndo_inv hy v]
      exact LinearMap.det_id
    rw [hd] at hcomp
    calc LinearMap.det (lipToEndo (inv_mem hy))
        = LinearMap.det (lipToEndo (inv_mem hy)) * (ε * ε) := by rw [hεsq, mul_one]
      _ = ε := by rw [← mul_assoc, hcomp, one_mul]

/-! ## 4. Spin elements are even, so the sign is `+1` -/

/-- **An `involute`-fixed Lipschitz element acts with determinant 1.**
    The other branch of `parity` would force `x = −x` and hence `x = 0`,
    which no unit is. -/
theorem det_lipToEndo_eq_one {x : Clˣ} (hx : x ∈ lipschitzGroup Q₁₃)
    (hinv : involute (x : Cl) = (x : Cl)) :
    LinearMap.det (lipToEndo hx) = 1 := by
  obtain ⟨ε, hε, hd, hi⟩ := parity hx
  rcases hε with h1 | h1
  · rw [hd, h1]
  · exfalso
    rw [h1, neg_smul, one_smul] at hi
    have heq : (x : Cl) = -(x : Cl) := hinv.symm.trans hi
    have h2 : (2 : ℝ) • (x : Cl) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [heq]
      exact add_neg_cancel _
    have hzero : (x : Cl) = 0 := by
      rcases smul_eq_zero.1 h2 with h | h
      · exact absurd h (by norm_num)
      · exact h
    exact x.ne_zero hzero

/-- The same for the estate's spin action, which `LipschitzVectorRep`
    proved is the same map. -/
theorem det_spinToEndo_eq_one {x : Clˣ} (hx : (x : Cl) ∈ spinGroup Q₁₃) :
    LinearMap.det (spinToEndo hx) = 1 := by
  have hlip : x ∈ lipschitzGroup Q₁₃ := units_mem_lip hx
  rw [show spinToEndo hx = lipToEndo hlip from
    (LinearMap.ext fun v => lipToEndo_eq_spinToEndo hlip hx v).symm]
  exact det_lipToEndo_eq_one hlip (spinGroup.involute_eq hx)

/-! ## 5. …and therefore the Lorentz matrix is proper -/

/-- The matrix `spinToO13` produces is the coordinate transport of the
    action, spelled out so its determinant can be computed. -/
theorem spinToO13_toMatrix (g : spinGroup Q₁₃) :
    ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ)
      = LinearMap.toMatrix' ((coordEquiv : V →ₗ[ℝ] (Fin 4 → ℝ)) ∘ₗ endo g ∘ₗ
          (coordEquiv.symm : (Fin 4 → ℝ) →ₗ[ℝ] V)) := by
  ext i j
  rw [spinToO13_apply_entry, LinearMap.toMatrix'_apply]
  rfl

/-- **Every spin element has a proper Lorentz matrix.** Not a family, not
    a hand-picked pair: every element of `spinGroup Q₁₃`. -/
theorem det_spinToO13_eq_one (g : spinGroup Q₁₃) :
    ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
      Matrix (Fin 4) (Fin 4) ℝ).det = 1 := by
  rw [spinToO13_toMatrix, LinearMap.det_toMatrix', LinearMap.det_conj]
  exact det_spinToEndo_eq_one (toUnits_mem g)

/-- Restated as membership in the special orthogonal group's defining
    condition, which is how the SO⁺(1,3) question will consume it. -/
theorem spinToO13_isLorentzMat_and_det (g : spinGroup Q₁₃) :
    IsLorentzMat ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ)
      ∧ ((spinToO13 g : Matrix.GeneralLinearGroup (Fin 4) ℝ) :
        Matrix (Fin 4) (Fin 4) ℝ).det = 1 :=
  ⟨(spinToO13 g).2, det_spinToO13_eq_one g⟩

/-! ## 6. What this does NOT give

`SOplus13` is `IsLorentzMat ∧ det = 1 ∧ 0 < Λ⁰₀`. Two of three are now
theorems for every spin element. The third has no route, and the file
says so with a statement rather than a sentence: the pair above is
exactly what is proved, and it is not membership.
-/

/-- The Gram matrix satisfies the first condition and fails the second,
    so the two are independent and `det = 1` is genuine content. -/
theorem gram_satisfies_first_not_second :
    IsLorentzMat (LorentzGroup.gram)
      ∧ (LorentzGroup.gram).det ≠ 1 := by
  refine ⟨gram_isLorentzMat_det_neg.1, ?_⟩
  rw [gram_isLorentzMat_det_neg.2]
  norm_num

/-! ## 7. Where the evenness hypothesis is doing the work

Review round 26's fold. §4's argument turns entirely on spin elements
being `involute`-fixed, and a reader has no way to see from §3 whether
that hypothesis is a real restriction or a formality. It is real, and the
sharpest way to say so is that **the file would be inconsistent without
it**: §1 says a vector unit acts with determinant −1 and §4 says a spin
element acts with determinant +1, so if any vector unit were a spin
element two theorems here would contradict each other.
-/

/-- **No vector unit is a spin element**, and the proof is exactly the
    collision. This is the soundness check on the pair of theorems above:
    had it failed, one of them would be false. -/
theorem vecUnit_not_mem_spinGroup {v : V} (hv : Q₁₃ v ≠ 0) :
    ((vecUnit v hv : Clˣ) : Cl) ∉ spinGroup Q₁₃ := by
  intro hmem
  have h1 : LinearMap.det (lipToEndo (vecUnit_mem v hv)) = 1 :=
    det_lipToEndo_eq_one _ (spinGroup.involute_eq hmem)
  rw [det_lipToEndo_vecUnit hv] at h1
  norm_num at h1

/-- …and the reason is visible one step earlier: `involute` does NOT fix
    a vector unit. So `spinGroup.involute_eq` selects rather than holding
    of everything in sight. -/
theorem involute_ne_vecUnit {v : V} (hv : Q₁₃ v ≠ 0) :
    involute ((vecUnit v hv : Clˣ) : Cl) ≠ ((vecUnit v hv : Clˣ) : Cl) := by
  intro h
  change involute (ι Q₁₃ v) = ι Q₁₃ v at h
  rw [involute_ι] at h
  have h2 : (2 : ℝ) • ι Q₁₃ v = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  have h3 : ι Q₁₃ v = 0 := by
    rcases smul_eq_zero.1 h2 with hh | hh
    · exact absurd hh (by norm_num)
    · exact hh
  refine hv ?_
  apply FaithfulSMul.algebraMap_injective ℝ Cl
  rw [← ι_sq_scalar, h3, mul_zero, map_zero]

/-- **The `−1` branch of `parity` is realised**, so the sign the induction
    carries is genuinely two-valued and the `involute` clause is not
    decoration. -/
theorem parity_neg_realised :
    ¬ ∀ (x : Clˣ) (hx : x ∈ lipschitzGroup Q₁₃),
      LinearMap.det (lipToEndo hx) = 1 := by
  intro h
  have hone := h (vecUnit e₁ Q₁₃_e₁_ne) (vecUnit_mem e₁ Q₁₃_e₁_ne)
  rw [det_lipToEndo_vecUnit Q₁₃_e₁_ne] at hone
  norm_num at hone

/-- And the conclusion is not free from triviality either: the map whose
    determinants are all `1` is not itself trivial. -/
theorem spinToO13_nontrivial : spinToO13 R₁₂' ≠ 1 := spinToO13_R₁₂'_ne_one

end

end SpinDetOne
