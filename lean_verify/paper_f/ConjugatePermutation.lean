/-
  ConjugatePermutation: conjugate-linear maps on a Euclidean space, and how they move matrices

  SPINE LINK L6 / L18 — the tool `ERRATUM 571` forces, and the repair it makes possible.

  WHY THIS FILE EXISTS, AND IT IS A REPAIR OF MY OWN CLAIM.
  `SpectralTripleBimodule` carries the real structure `J` of a finite real spectral triple as
  a field of type `Module.End 𝕜 H` — a `𝕜`-LINEAR map. A real structure is conjugate-linear,
  so that field was weaker than a real structure, and three of this estate's file headers
  excused it with the sentence *"Mathlib's `LinearMap` cannot express that at this
  signature."* **That sentence was false** (`ERRATUM 571`): Mathlib's `LinearMap` is
  SEMILINEAR by default, `H →ₛₗ[starRingEnd ℂ] H` is exactly a conjugate-linear map, and it
  has its own notation `→ₗ⋆[ℂ]`. `KOSixRealStructureE.Jmap` was the first conjugate-linear map
  built here and it refuted the sentence by construction.

  Refuting the sentence left the defect in place: the FIELD was still `Module.End 𝕜 H`, so the
  three KO-6 sign axioms `J_sq`, `J_comm_D`, `J_anticomm_γ` were constraints on the wrong kind
  of object. This file is the tool that lets the field be widened and both of the estate's
  `Triple` witnesses re-built with genuine real structures — which is done in
  `SpectralTripleBimodule` and `OrderOneNontrivial`, in the same unit as this file.

  WHAT IS HERE.
  * **`conjPerm σ`** — for a permutation `σ` of the index type, the map
    `v ↦ (i ↦ conj (v (σ i)))` on `EuclideanSpace ℂ ι`, as a bundled
    `EuclideanSpace ℂ ι →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ ι`. Every real structure in this
    estate is of this shape: conjugate the coordinates, then move them.
  * **`conjPerm_comp`** — composing two of them gives a genuinely `ℂ`-LINEAR map, and says
    which one: `(conjPerm σ).comp (conjPerm τ) = permLin (σ.trans τ)`. This is what
    `RingHomCompTriple (starRingEnd ℂ) (starRingEnd ℂ) (RingHom.id ℂ)` buys, and it is why
    `J² = 1` is even a statable identity for a conjugate-linear `J`.
  * **`conjPerm_comp_self`** — `J² = 1` whenever `σ` is an involution. The KO-6 sign `ε = 1`.
  * **`conjPerm_inner`** and **`conjPerm_norm`** — it is ANTIUNITARY: `⟪Ju, Jv⟫ = conj ⟪u, v⟫`,
    hence an isometry. **Proved because "real structure" carries this and `Triple` does not ask
    for it**: nothing in that structure constrains `J` metrically, so the three KO-6 signs
    alone would leave a `J` free to distort the inner product. Both witnesses' `J` is a
    `conjPerm`, so both are antiunitary — which is what makes "genuine real structure" an
    earned phrase rather than a hopeful one.
  * **`conjPerm_not_linear`** — and it is genuinely NOT `ℂ`-linear, proved rather than assumed
    from the type. A map that were both would be zero; `conjPerm σ` is an involution. Stated
    because a real structure that quietly turned out to be linear is the shape of
    `ERRATUM 565`.
  * **`conjPerm_toEuclideanCLM`** — **the lemma the whole unit turns on.** A conjugate-linear
    `conjPerm σ` does not commute past a matrix; it CHANGES THE MATRIX, to
    `(M.submatrix σ σ).map conj`. Conjugating the entries is the antilinearity; the
    `submatrix` is the permutation. Both witnesses' `J_comm_D` and `J_anticomm_γ` are
    corollaries of this one identity, so neither has to reason about sums again.
  * **`conjPerm_commute_of_eq`** and **`conjPerm_anticommute_of_neg`** — the two corollaries,
    stated as the criteria a witness actually checks: `J` commutes with `M`'s action exactly
    when `(M.submatrix σ σ).map conj = M`, and anticommutes exactly when that is `-M`.

  WHAT IS **NOT** CLAIMED.
  * **These are not all the conjugate-linear maps.** `conjPerm σ` is a monomial antilinear map
    with unit coefficients; the general antilinear map on `EuclideanSpace ℂ ι` is
    `conj` followed by an arbitrary matrix, and nothing here says that the KO-6 real structure
    must be of the restricted `conjPerm` shape. It is a sufficient supply of witnesses, not a
    classification.
  * **No `J` here is claimed to be CCM's `J`.** Which real structure the cascade carries is
    `ASSUMPTIONS_LEDGER` 18 and 48, a DECISIONS NEEDED item, and untouched.
  * **`conjPerm` is not related here to `KOSixRealStructureE.Jmap`.** `Jmap` is the same shape
    (conjugate, then swap particle against antiparticle blocks) and predates this file by one
    unit; the identification is not proved, because `blockSwap` is a bare function there and
    would have to be re-bundled as an `Equiv` first. Stated so that the overlap is on the
    record rather than discovered later.

  0 sorry. 0 new axioms. `#print axioms` on every declaration below:
  [propext, Classical.choice, Quot.sound].
-/

import Mathlib.Analysis.CStarAlgebra.Matrix

namespace ConjugatePermutation

open Matrix
open scoped ComplexConjugate

noncomputable section

variable {ι : Type*} [Fintype ι]

/-! ## 1. The conjugate-linear maps -/

/-- **A conjugate-linear map on a Euclidean space**: conjugate the coordinates and permute
them by `σ`. The `→ₛₗ[starRingEnd ℂ]` in the type is what `ERRATUM 571` says Mathlib has had
all along; Lean prints it as `→ₗ⋆[ℂ]`. -/
def conjPerm (σ : Equiv.Perm ι) :
    EuclideanSpace ℂ ι →ₛₗ[starRingEnd ℂ] EuclideanSpace ℂ ι where
  toFun v := (WithLp.toLp 2 fun i => conj (v (σ i)))
  map_add' u v := by ext i; simp
  map_smul' c v := by ext i; simp

@[simp] theorem conjPerm_apply (σ : Equiv.Perm ι) (v : EuclideanSpace ℂ ι) (i : ι) :
    conjPerm σ v i = conj (v (σ i)) := rfl

/-- Antilinearity spelled out, so that no reader has to decode the semilinear notation to see
that this is the conjugate-linear condition and not the linear one. -/
theorem conjPerm_conj_smul (σ : Equiv.Perm ι) (c : ℂ) (v : EuclideanSpace ℂ ι) :
    conjPerm σ (c • v) = conj c • conjPerm σ v :=
  (conjPerm σ).map_smul' c v

/-- The `ℂ`-linear permutation map, the value of a composite of two conjugate-linear ones. -/
def permLin (σ : Equiv.Perm ι) : Module.End ℂ (EuclideanSpace ℂ ι) where
  toFun v := (WithLp.toLp 2 fun i => v (σ i))
  map_add' u v := by ext i; simp
  map_smul' c v := by ext i; simp

@[simp] theorem permLin_apply (σ : Equiv.Perm ι) (v : EuclideanSpace ℂ ι) (i : ι) :
    permLin σ v i = v (σ i) := rfl

/-- **Two conjugate-linear maps compose to a LINEAR one**, and this says which. The type
`EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι` on the left is produced by
`RingHomCompTriple (starRingEnd ℂ) (starRingEnd ℂ) (RingHom.id ℂ)`, which Mathlib supplies
from `RingHomInvPair (starRingEnd R) (starRingEnd R)`. -/
theorem conjPerm_comp (σ τ : Equiv.Perm ι) :
    (conjPerm σ).comp (conjPerm τ) = permLin (σ.trans τ) := by
  ext v i
  simp

/-- `J² = 1` pointwise. Reached for three times before it was stated; `conjPerm_comp_self` is
the bundled form and this is the one proofs actually rewrite with. -/
theorem conjPerm_involutive (σ : Equiv.Perm ι) (hσ : ∀ i, σ (σ i) = i)
    (v : EuclideanSpace ℂ ι) : conjPerm σ (conjPerm σ v) = v := by
  ext i; simp [hσ]

/-- **KO-6 sign `ε = 1` for `conjPerm`**: an involutive `σ` gives `J² = 1`. -/
theorem conjPerm_comp_self (σ : Equiv.Perm ι) (hσ : ∀ i, σ (σ i) = i) :
    (conjPerm σ).comp (conjPerm σ) = LinearMap.id := by
  ext v i
  simp [hσ]

/-- **`conjPerm σ` is NOT `ℂ`-linear**, so the conjugate-linear typing is not decoration.
Proved rather than asserted because a map that were both linear and conjugate-linear would be
zero, and a "real structure" that quietly turned out to be linear is exactly the kind of
object `ERRATUM 565` was about. Needs `ι` inhabited: on the empty index type every map is
zero and the statement is false. -/
theorem conjPerm_not_linear [Nonempty ι] (σ : Equiv.Perm ι) :
    ¬ ∀ (c : ℂ) (v : EuclideanSpace ℂ ι), conjPerm σ (c • v) = c • conjPerm σ v := by
  intro h
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hv := h Complex.I (WithLp.toLp 2 fun _ => (1 : ℂ))
  have h2 := congrArg (fun w : EuclideanSpace ℂ ι => w i) hv
  simp only [conjPerm_apply, PiLp.smul_apply, smul_eq_mul, mul_one,
    Complex.conj_I, map_one] at h2
  exact Complex.I_ne_zero (by linear_combination -h2 / 2)

/-- **`conjPerm σ` is ANTIUNITARY**: it conjugates the inner product rather than preserving
it, `⟪Ju, Jv⟫ = conj ⟪u, v⟫`. **Proved because the word "real structure" carries this and the
`Triple` structure does not ask for it** — nothing in that structure constrains `J`
metrically, so a `J` satisfying the three KO-6 signs could still distort the inner product.
Every `conjPerm` does not, and `conjPerm_norm` is the norm form. -/
theorem conjPerm_inner (σ : Equiv.Perm ι) (u v : EuclideanSpace ℂ ι) :
    inner ℂ (conjPerm σ u) (conjPerm σ v) = conj (inner ℂ u v) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conjPerm_apply, map_sum, map_mul,
    RingHomCompTriple.comp_apply, RingHom.id_apply]
  exact Fintype.sum_equiv σ _ _ (fun _ => rfl)

/-- `conjPerm σ` is an isometry, from `conjPerm_inner` at `u = v` (conjugation fixes the real
number `⟪v, v⟫`). -/
theorem conjPerm_norm (σ : Equiv.Perm ι) (v : EuclideanSpace ℂ ι) :
    ‖conjPerm σ v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), conjPerm_inner,
    RCLike.conj_re]

/-! ## 2. How a conjugate-linear map moves a matrix -/

variable [DecidableEq ι]

/-- **The lemma the unit turns on.** Pushing `conjPerm σ` past the action of a matrix `M` does
not leave `M` alone: it replaces `M` by `(M.submatrix σ σ).map conj`. The entrywise `conj` is
the antilinearity and the `submatrix` is the permutation, and the two are independent, so a
`J` built from a real, `σ`-invariant matrix commutes and one built from a real,
`σ`-anti-invariant matrix anticommutes. -/
theorem conjPerm_toEuclideanCLM (σ : Equiv.Perm ι) (M : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    conjPerm σ (Matrix.toEuclideanCLM (𝕜 := ℂ) M v)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) ((M.submatrix σ σ).map (starRingEnd ℂ))
          (conjPerm σ v) := by
  ext i
  have hL : conjPerm σ (Matrix.toEuclideanCLM (𝕜 := ℂ) M v) i
      = ∑ j, conj (M (σ i) j) * conj (v j) := by
    simp [Matrix.mulVec, dotProduct, map_sum]
  have hR : Matrix.toEuclideanCLM (𝕜 := ℂ)
        ((M.submatrix σ σ).map (starRingEnd ℂ)) (conjPerm σ v) i
      = ∑ k, conj (M (σ i) (σ k)) * conj (v (σ k)) := by
    simp [Matrix.mulVec, dotProduct]
  rw [hL, hR]
  exact (Fintype.sum_equiv σ _ _ (fun _ => rfl)).symm

/-- **The commuting criterion.** `J = conjPerm σ` commutes with `M`'s action as soon as
conjugating `M`'s entries and permuting its indices by `σ` returns `M`. -/
theorem conjPerm_commute_of_eq (σ : Equiv.Perm ι) (M : Matrix ι ι ℂ)
    (hM : (M.submatrix σ σ).map (starRingEnd ℂ) = M) (v : EuclideanSpace ℂ ι) :
    conjPerm σ (Matrix.toEuclideanCLM (𝕜 := ℂ) M v)
      = Matrix.toEuclideanCLM (𝕜 := ℂ) M (conjPerm σ v) := by
  rw [conjPerm_toEuclideanCLM, hM]

/-- **The anticommuting criterion**, which is the KO-6 sign `ε″ = -1` for a grading `γ`. -/
theorem conjPerm_anticommute_of_neg (σ : Equiv.Perm ι) (M : Matrix ι ι ℂ)
    (hM : (M.submatrix σ σ).map (starRingEnd ℂ) = -M) (v : EuclideanSpace ℂ ι) :
    conjPerm σ (Matrix.toEuclideanCLM (𝕜 := ℂ) M v)
      = -Matrix.toEuclideanCLM (𝕜 := ℂ) M (conjPerm σ v) := by
  rw [conjPerm_toEuclideanCLM, hM, map_neg, ContinuousLinearMap.neg_apply]

end

end ConjugatePermutation
