/-
  EvenGradingObstruction: CCM's remaining grading axioms, and why one of them cannot be met on
  the regular bimodule

  SPINE LINK L6 — WALL W9, §W9.7. The residue three units have now flagged, turned into a
  theorem about why.

  THE TWO AXIOMS `Triple` STILL DOES NOT ASK FOR. `ERRATUM 573` found that the structure was
  missing CCM's relation `πOp b = J π(b*) J` and added it. Two more of CCM's conditions on the
  grading are still absent, and they are of exactly the same shape — conditions a reader would
  assume from the name:
  * **`D` is ODD**: `Dγ = -γD`. The Dirac operator exchanges the two halves of the grading.
  * **`γ` is EVEN**: `γ` commutes with every `π a`. The representation is graded.

  WHAT HAPPENS TO EACH, and the two answers are different.
  * **The first is SATISFIABLE and is now satisfied.** `RealSpectralWitness.Dccm_anticomm_gammaCcm`
    — bought by changing that witness's `D` from the symmetric sum built on `σ₁` to the one
    built on `σ₃`. Found by solving `Dγ + γD = 0` as a LINEAR system: `JDJ = D` together with
    order-one and a non-zero one-form force `D = A ⊗ 1 + 1 ⊗ Ā`, and the solutions for `A` are
    spanned by `i·1` (scalar, one-form zero) and `σ₃`.
  * **The second is NOT SATISFIABLE ON THAT SPACE AT ALL**, and that is this file's theorem.

  THE OBSTRUCTION, and the route actually taken is the SHORT one, not the conceptual one.
  The conceptual argument would run: an even `γ` also commutes with `πOp` (because
  `πOp b = J π(b*) J` and moving `γ` past each `J` costs a sign, and the two cancel), so it
  commutes with both images; where those generate the endomorphisms it is central, hence
  scalar; and a scalar cannot be a KO-6 grading. **Both ends of that argument are proved here
  and the middle is not**: `gamma_commutes_piOp` is the first step in full generality and
  `no_scalar_KO6_grading` the last, but *"the two images generate everything"* is the double
  commutant, which this estate does not have. **So the concrete theorem below does not use
  either of them**, and they are stated as the general half rather than as steps of a proof.
  Saying which lemmas a proof does NOT consume is the point of this paragraph.

  **What `no_even_KO6_grading_on_Hw` actually does**, and it needs ONE instance of evenness:
  commuting with `σ₃ ⊗ 1` kills every entry whose two FIRST-slot indices differ (`key`). The
  `J`-condition then relays that to entries whose first-slot indices agree and second-slot
  indices differ, because `prodSwap` exchanges the two roles. So the `(0,0)` row and column of
  `γ` meet only on the diagonal, `γ² = 1` at that entry reads `d² = 1`, and the `J`-condition
  at the same entry reads `conj d = -d`. Then `d · conj d = -d² = -1` while `d · conj d` is
  `‖d‖² ≥ 0`. **No commutant classification, no dimension count, and `σ₁` never appears.**

  **And it lifts to operators**, because `matAlg_surjective`: every linear map on a
  finite-dimensional normed space is continuous, so `matAlg` is onto `Module.End ℂ Hw` and
  `no_even_KO6_grading_operator` applies to an arbitrary `γ` rather than only to one presented
  as a matrix.

  > **`no_even_KO6_grading_operator`** — no endomorphism of `Hw` is at once an involution, EVEN
  > for the left action, and anticommuting with `Jprod`.

  **`gammaCcm_not_even`** is then a one-line corollary, and it matters: the estate's own witness
  **realises** the obstruction rather than dodging it.

  WHAT THIS MEANS, stated plainly because it is the point of the unit.
  **`RealSpectralWitness.realWitness` is as close to a CCM real spectral triple as anything on
  that space can be.** It satisfies order-zero, order-one with a non-zero one-form, `J² = 1`,
  `JD = DJ`, `Jγ = -γJ`, `γ² = 1`, `Dγ = -γD` and `πOp b = J π(b*) J`. The one CCM condition it
  fails — `γ` even — is **provably unattainable there**, so what looked for three units like an
  omission in the witness is a fact about the space. **And it is a reason CCM's `H` is large**:
  an even KO-6 real spectral triple cannot live on a regular bimodule of a matrix algebra, so
  the 96-dimensional space of the physical model is not extravagance.

  WHAT IS **NOT** CLAIMED.
  * **`Triple` is NOT amended with either axiom.** Adding `γ`-evenness would delete
    `realWitness` and, by the theorem here, admit **no** non-scalar replacement on that space —
    the estate would be back to the scalar witness alone. That is a decision about what the
    estate's structure should mean, not a repair, and it goes to the author rather than being
    taken here. `D`-oddness could be added today, and is not, because adding one of a matched
    pair invites exactly the confusion `ERRATUM 573` came from.
  * **No claim about larger spaces.** The obstruction is proved for `Hw`; nothing here says an
    even KO-6 triple exists on the 96-dimensional space, nor that it does not. The *reason*
    given for CCM's `H` being large is a consistency remark, not a theorem about `H`.
  * **`jointCommutant_piW_piOpW` is proved entrywise for `Fin 2 × Fin 2`**, not derived from a
    double-commutant theorem. ~~It is the one step that does not generalise as written.~~
    **AMENDED 2026-09-15 (`ERRATUM 580`): that clause was right about the writing and wrong
    about the step.** On a MATRIX space the commutant needs no double-commutant theorem at all:
    every vector is `π(X) 1` for `X` the vector read as a matrix, so an operator commuting with
    every left multiplication is determined by its value at the identity and equals right
    multiplication by it — three lines, at every size
    (`BimoduleRealStructure.even_eq_piR`). **And the obstruction itself is now proved at every
    non-empty size**: `BimoduleRealStructure.no_even_KO6_grading`, with
    `no_even_KO6_grading_on_witness` CHECKING that it specialises to this file's theorem, since
    `piW` is `piL (Fin 2)` and `Jprod` is `Jbi (Fin 2)` definitionally. **BE EXACT ABOUT WHICH
    OF THE TWO THEOREMS BELOW THAT SUBSUMES, because they do not have the same hypothesis.**
    `no_even_KO6_grading_operator` assumes evenness against EVERY `a`, and the general theorem
    has exactly that hypothesis, so that one IS subsumed. **`no_even_KO6_grading_on_Hw` is
    not**: it needs only ONE instance of evenness — commuting with `σ₃ ⊗ 1` — so at `Fin 2` it is
    STRONGER than the general theorem, which needs all of them. Nothing is deleted here, and the
    reason is not caution: **the entrywise proof buys a weaker hypothesis and the general proof
    buys every size, and neither implies the other.** That is a factoring question, filed rather
    than settled.
  * Rung 2 is not climbed; no factor list is cut; no `K`-theory.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import OrderOneUnderCCM

namespace EvenGradingObstruction

open Matrix MulOpposite SpectralTripleBimodule OrderOneNontrivial
open OppositeFromRealStructure RealSpectralWitness OrderOneUnderCCM
open scoped Kronecker ComplexConjugate

noncomputable section

/-! ## 1. An even grading commutes with the right action too -/

variable {𝕂 𝕜 A H : Type*} [Field 𝕂] [RCLike 𝕜] [Algebra 𝕂 𝕜]
  [Ring A] [StarRing A] [Algebra 𝕂 A]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [Module 𝕂 H] [IsScalarTower 𝕂 𝕜 H]

/-- **An EVEN grading commutes with `πOp` as well.** `πOp b = J π(b*) J`, and moving `γ` past
each `J` costs a minus sign; the two cancel. Nothing here is special to `γ` beyond
`J_anticomm_γ`. -/
theorem gamma_commutes_piOp (T : Triple 𝕂 𝕜 A H)
    (heven : ∀ a : A, T.γ * T.π a = T.π a * T.γ) (b : Aᵐᵒᵖ) :
    T.γ * T.πOp b = T.πOp b * T.γ := by
  have hJ : ∀ w : H, T.J (T.γ w) = -(T.γ (T.J w)) := fun w => by
    simpa using LinearMap.congr_fun T.J_anticomm_γ w
  have hev : ∀ (a : A) (w : H), T.γ (T.π a w) = T.π a (T.γ w) := fun a w => by
    simpa [Module.End.mul_apply] using LinearMap.congr_fun (heven a) w
  refine LinearMap.ext fun v => ?_
  simp only [Module.End.mul_apply, T.πOp_impl]
  rw [hJ v, map_neg, map_neg, ← hev, hJ, neg_neg]

/-! ## 2. A scalar cannot be a KO-6 grading -/

/-- **The clean half of the obstruction, and it is general.** If `γ` is a scalar multiple of the
identity then `γ² = 1` forces `α·conj α = -1`, while `α·conj α` is `‖α‖²` and cannot be
negative. No case analysis, no dimension count, nothing specific to any index type. The
non-zero vector is needed because on the zero space `γ² = 1` is vacuous. -/
theorem no_scalar_KO6_grading (T : Triple 𝕂 𝕜 A H) (α : 𝕜)
    (hscalar : ∀ v : H, T.γ v = α • v) (v : H) (hv : v ≠ 0) : False := by
  have hsq : α * α = 1 := by
    have h : T.γ (T.γ v) = v := by
      have := LinearMap.congr_fun (congrArg (fun x : Module.End 𝕜 H => (x : H →ₗ[𝕜] H)) T.γ_sq) v
      simpa [Module.End.mul_apply] using this
    rw [hscalar, hscalar, smul_smul] at h
    have h0 : (α * α - 1) • v = 0 := by rw [sub_smul, h, one_smul, sub_self]
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact sub_eq_zero.mp h1
    · exact absurd h1 hv
  have hJv : T.J v ≠ 0 := by
    intro h
    exact hv (by rw [← OppositeFromRealStructure.J_apply_J T v, h, map_zero])
  have hconj : (starRingEnd 𝕜) α = -α := by
    have h := LinearMap.congr_fun T.J_anticomm_γ v
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, hscalar] at h
    rw [LinearMap.map_smulₛₗ] at h
    have h0 : ((starRingEnd 𝕜) α + α) • T.J v = 0 := by
      rw [add_smul, h]
      exact neg_add_cancel _
    rcases smul_eq_zero.mp h0 with h1 | h1
    · linear_combination h1
    · exact absurd h1 hJv
  have hnorm : α * (starRingEnd 𝕜) α = -(1 : 𝕜) := by rw [hconj, mul_neg, hsq]
  rw [RCLike.mul_conj, ← RCLike.ofReal_pow] at hnorm
  have h2 : ‖α‖ ^ 2 = (-1 : ℝ) := by exact_mod_cast hnorm
  nlinarith [sq_nonneg ‖α‖]

/-! ## 3. On the regular bimodule, no even KO-6 grading exists -/

/-- **THE OBSTRUCTION.** No matrix on `Hw` is at once an involution, commuting with the LEFT
action, and anticommuting with `Jprod`. **Three hypotheses, and the proof needs only one
instance of the first** — commuting with `σ₃ ⊗ 1` — which is what makes it short.

The shape: `σ₃ ⊗ 1` commutation kills every entry whose two FIRST-slot indices differ; the
`J`-condition then relays that to the entries whose first-slot indices agree and whose
second-slot indices differ, because `prodSwap` exchanges the roles. So the `(0,0)` row and
column of `G` meet only at the diagonal, `G² = 1` at that entry reads `d² = 1`, and the
`J`-condition at the same entry reads `conj d = -d`. Then `d · conj d = -d² = -1`, while
`d · conj d = ‖d‖² ≥ 0`. -/
theorem no_even_KO6_grading_on_Hw (G : Matrix Slots Slots ℂ)
    (hcomm : G * (pauli3 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ))
      = (pauli3 ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * G)
    (hsq : G * G = 1)
    (hJ : (G.submatrix prodSwap prodSwap).map (starRingEnd ℂ) = -G) : False := by
  have key : ∀ i j k l : Fin 2, i ≠ k → G (i, j) (k, l) = 0 := by
    intro i j k l hik
    have e := congrFun (congrFun hcomm (i, j)) (k, l)
    fin_cases i <;> fin_cases k
    · exact absurd rfl hik
    · change G (0, j) (1, l) = 0
      simp [Matrix.mul_apply, Matrix.kroneckerMap, Matrix.one_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, pauli3] at e
      linear_combination -e / 2
    · change G (1, j) (0, l) = 0
      simp [Matrix.mul_apply, Matrix.kroneckerMap, Matrix.one_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, pauli3] at e
      linear_combination e / 2
    · exact absurd rfl hik
  have hJe : ∀ (p q : Slots), (starRingEnd ℂ) (G (p.2, p.1) (q.2, q.1)) = -G p q := by
    intro p q
    have := congrFun (congrFun hJ p) q
    simpa [prodSwap] using this
  have z1 : G (0, 0) (0, 1) = 0 := by
    have := hJe (0, 0) (0, 1)
    rw [key 0 0 1 0 (by decide)] at this
    simpa using this.symm
  have z2 : G (0, 1) (0, 0) = 0 := by
    have := hJe (0, 1) (0, 0)
    rw [key 1 0 0 0 (by decide)] at this
    simpa using this.symm
  have hd : G (0, 0) (0, 0) * G (0, 0) (0, 0) = 1 := by
    have := congrFun (congrFun hsq (0, 0)) (0, 0)
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply] at this
    rw [z1, z2, key 0 0 1 0 (by decide), key 0 0 1 1 (by decide),
      key 1 0 0 0 (by decide), key 1 1 0 0 (by decide)] at this
    simpa using this
  have hc : (starRingEnd ℂ) (G (0, 0) (0, 0)) = -G (0, 0) (0, 0) := hJe (0, 0) (0, 0)
  have hmul : G (0, 0) (0, 0) * (starRingEnd ℂ) (G (0, 0) (0, 0)) = -1 := by
    rw [hc, mul_neg, hd]
  rw [Complex.mul_conj] at hmul
  have := congrArg Complex.re hmul
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.one_re] at this
  nlinarith [Complex.normSq_nonneg (G (0, 0) (0, 0))]

/-! ## 4. The same, at the operator level, and what it does to the estate's witness -/

/-- `matAlg` is ONTO `Module.End ℂ Hw`: every linear map on a finite-dimensional normed space
is continuous (`LinearMap.toContinuousLinearMap`), and `Matrix.toEuclideanCLM` is an
equivalence onto the continuous ones. Needed so the matrix theorem above applies to an
arbitrary `γ` rather than only to one presented as a matrix. -/
theorem matAlg_surjective : Function.Surjective (matAlg Slots) := by
  intro f
  refine ⟨(Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Slots)).symm
    (LinearMap.toContinuousLinearMap f), ?_⟩
  refine LinearMap.ext fun v => ?_
  rw [matAlg_apply]
  simp

/-- **THE OBSTRUCTION, at the operator level.** No endomorphism of `Hw` is at once an
involution, EVEN for the left action, and anticommuting with `Jprod`. So **the four-dimensional
regular bimodule of `M₂(ℂ)` carries no even KO-6 real structure**, and the one CCM condition
`RealSpectralWitness.realWitness` fails is a fact about the space rather than a defect of the
witness. -/
theorem no_even_KO6_grading_operator (g : Module.End ℂ Hw)
    (heven : ∀ a : Matrix (Fin 2) (Fin 2) ℂ, g * piW a = piW a * g)
    (hsq : g * g = 1)
    (hJ : ∀ v : Hw, Jprod (g (Jprod v)) = -(g v)) : False := by
  obtain ⟨G, hG⟩ := matAlg_surjective g
  subst hG
  refine no_even_KO6_grading_on_Hw G ?_ ?_ ?_
  · refine matAlg_injective Slots ?_
    rw [map_mul, map_mul]
    exact heven pauli3
  · refine matAlg_injective Slots ?_
    rw [map_mul, map_one]
    exact hsq
  · refine matAlg_injective Slots ?_
    rw [map_neg]
    refine LinearMap.ext fun v => ?_
    rw [matAlg_apply, ← conjPerm_conj prodSwap prodSwap_involutive]
    have h := hJ v
    rw [matAlg_apply, matAlg_apply] at h
    simpa [Jprod] using h

/-- **And the estate's witness realises the obstruction rather than dodging it**: `gammaCcm` is
NOT even. A one-line corollary — it is an involution and it anticommutes with `Jprod`, so if it
also commuted with `π` the theorem above would give `False`. **This is why `realWitness` is not
an even spectral triple, and by the theorem no choice of `γ` would make it one.** -/
theorem gammaCcm_not_even :
    ¬ (∀ a : Matrix (Fin 2) (Fin 2) ℂ, gammaCcm * piW a = piW a * gammaCcm) := fun heven =>
  no_even_KO6_grading_operator gammaCcm heven gammaCcm_sq Jprod_anticomm_gammaCcm

end

end EvenGradingObstruction
