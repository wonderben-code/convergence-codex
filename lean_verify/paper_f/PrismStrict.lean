/-
  PrismStrict.lean — strict reflection positivity on the two-layer stack.

  WHY. `PrismTransfer`'s header recorded an overclaim: its draft advertised
  `reflectedForm_prism_eq` and `reflectionPositive_prism_strict` and had
  neither. `PrismGreen` did three steps of the leg the watchlist wrote out,
  `PrismReflectedForm` did the fourth and delivered the first theorem, and left
  the second as a **one-ingredient problem** with the ingredient named:
  strict antitonicity of matrix inversion, absent from the estate and — at the
  scopes searched — from Mathlib.

  **This supplies the ingredient and closes the second theorem. The recorded
  overclaim is now fully discharged.**

  WHAT THIS FILE PROVES:
  1. **`PosDef.mul_self`** — `P * P` is positive definite when `P` is. The
     smallest missing piece. Mathlib has `posSemidef_conjTranspose_mul_self`
     and no definite analogue; for Hermitian `P` the product IS `Pᴴ * P`, and
     what upgrades semidefinite to definite is that `P *ᵥ x ≠ 0` for `x ≠ 0` —
     which falls straight out of positive definiteness itself, with no
     determinant argument.
  2. **`inv_sub_inv`** — `P⁻¹ − M⁻¹ = P⁻¹ (M − P) M⁻¹` for invertible `P`, `M`.
  3. **`inv_sub_inv_posDef`** — **STRICT ANTITONICITY, in the shape this chain
     needs**: for positive definite `P` and `M = P + 1 + 1`, the difference
     `P⁻¹ − M⁻¹` is positive DEFINITE. Via the identity, `M − P = 1 + 1`, and
     `P⁻¹M⁻¹ = (M P)⁻¹` with `M P = P P + P + P`.
  4. **`green_sub_green_posDef`** — hence on any finite graph the massive Green
     function at mass `m` strictly dominates the one at `√(m² + 2)`.
  5. **`reflectionPositive_prism_strict`** — **the reflected form of the
     two-layer stack is STRICTLY positive for every nonzero coefficient
     family.** The theorem `PrismTransfer` advertised and did not have.

  WHAT THIS DOES NOT DO.
  * **It does not prove strict antitonicity in general.** §3 is stated for
    `M = P + 1 + 1`, the shape this chain produces, not for an arbitrary pair
    with `M − P` positive definite. The general statement is true and this
    proof would give it with `M − P = D` for positive definite `D`; **it is
    not what was needed, it is not written, and it is not claimed.**
    ^ **THAT CLAUSE HAS BEEN FALSE SINCE 10 AUGUST 2026 AND IS KEPT AS
      WRITTEN** (`ERRATUM 94`, `ERRATUM 362`). `StrictCriterion.
      inv_sub_inv_posDef_gen` proves exactly it — positive definite `P` and
      `M` with `M − P` positive definite give `P⁻¹ − M⁻¹` positive definite —
      the day after this file, and says in its own summary that it is closing
      the sentence above. **This file was never told**, and carried the
      clause for twenty-one days.
      **AND THE ROUTE WAS NOT THE ONE PREDICTED EITHER.** *"This proof would
      give it"* names the `PosDef.mul_self`-and-determinant argument;
      `StrictCriterion` uses none of it, feeding the variational optimiser for
      `M` into the bound for `P` in six lines.
  * **It says nothing about the box or the torus.** Neither has the
    identification `PrismTransfer` proved, so on those graphs the reflected
    form is not a difference of two base-graph Green functions and this route
    does not reach them. **For the lattice cases the non-strict statement
    remains the only one available.**
  * **No spectral content, two layers, free field, finite graph** — unchanged
    from the four files this one completes.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import PrismReflectedForm

namespace PrismStrict

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace PrismReflection
open PrismTransfer PrismGreen PrismReflectedForm

/-! ## 1. The missing ingredient -/

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- **`P * P` IS POSITIVE DEFINITE WHEN `P` IS.** -/
theorem PosDef.mul_self {P : Matrix n n ℝ} (hP : P.PosDef) : (P * P).PosDef := by
  obtain ⟨hherm, hpos⟩ := Matrix.posDef_iff_dotProduct_mulVec.mp hP
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_mul, hherm.eq]
  · intro x hx
    have hy : P *ᵥ x ≠ 0 := by
      intro hc
      have h0 := hpos hx
      rw [hc, dotProduct_zero] at h0
      exact lt_irrefl 0 h0
    have hstep : star x ⬝ᵥ ((P * P) *ᵥ x) = star (P *ᵥ x) ⬝ᵥ (P *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hherm.eq]
    rw [hstep]
    simp only [dotProduct, Pi.star_apply, star_trivial]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_self_pos.mpr (by simpa using hi)

/-- `P⁻¹ − M⁻¹ = P⁻¹ (M − P) M⁻¹`, for invertible `P` and `M`. -/
theorem inv_sub_inv {P M : Matrix n n ℝ} (hP : IsUnit P.det) (hM : IsUnit M.det) :
    P⁻¹ - M⁻¹ = P⁻¹ * (M - P) * M⁻¹ := by
  have h1 : P⁻¹ * (M - P) * M⁻¹ = P⁻¹ * M * M⁻¹ - P⁻¹ * P * M⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [h1, Matrix.mul_assoc P⁻¹ M M⁻¹, Matrix.mul_nonsing_inv M hM, Matrix.mul_one,
    Matrix.nonsing_inv_mul P hP, Matrix.one_mul]

/-- **STRICT ANTITONICITY, in the shape this chain needs.** -/
theorem inv_sub_inv_posDef {P : Matrix n n ℝ} (hP : P.PosDef) :
    (P⁻¹ - (P + 1 + 1)⁻¹).PosDef := by
  have hone : (1 : Matrix n n ℝ).PosDef := Matrix.PosDef.one
  have hM : (P + 1 + 1 : Matrix n n ℝ).PosDef :=
    Matrix.PosDef.add (Matrix.PosDef.add hP hone) hone
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  have hMu : IsUnit (P + 1 + 1 : Matrix n n ℝ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hM.isUnit
  have hdiff : (P + 1 + 1 : Matrix n n ℝ) - P = 1 + 1 := by abel
  have hprod : (P + 1 + 1 : Matrix n n ℝ) * P = P * P + P + P := by
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
  have hQ : ((P + 1 + 1 : Matrix n n ℝ) * P)⁻¹.PosDef := by
    rw [hprod]
    exact Matrix.PosDef.inv
      (Matrix.PosDef.add (Matrix.PosDef.add (PosDef.mul_self hP) hP) hP)
  have hsplit : P⁻¹ - (P + 1 + 1 : Matrix n n ℝ)⁻¹
      = ((P + 1 + 1 : Matrix n n ℝ) * P)⁻¹ + ((P + 1 + 1 : Matrix n n ℝ) * P)⁻¹ := by
    rw [inv_sub_inv hPu hMu, hdiff, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul,
      Matrix.mul_inv_rev]
  rw [hsplit]
  exact Matrix.PosDef.add hQ hQ

end Algebra

/-! ## 2. The two Green functions of a graph, compared strictly -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

theorem massive_shift (hm : m ≠ 0) :
    massive K (Real.sqrt (m ^ 2 + 2)) = massive K m + 1 + 1 := by
  have hsq : Real.sqrt (m ^ 2 + 2) ^ 2 = m ^ 2 + 2 :=
    Real.sq_sqrt (by positivity)
  ext i j
  by_cases h : i = j
  · subst h
    simp [massive, Matrix.add_apply, hsq]
    ring
  · simp [massive, Matrix.add_apply, h]

/-- **THE PROPAGATOR AT MASS `m` STRICTLY DOMINATES THE ONE AT `√(m² + 2)`**,
    on every finite graph. -/
theorem green_sub_green_posDef (hm : m ≠ 0) :
    (green K m - green K (Real.sqrt (m ^ 2 + 2))).PosDef := by
  have h := inv_sub_inv_posDef (massive_posDef K hm)
  rw [← massive_shift K hm] at h
  exact h

/-! ## 3. And therefore the reflected form is strictly positive -/

/-- **STRICT REFLECTION POSITIVITY ON THE TWO-LAYER STACK.** The theorem
    `PrismTransfer`'s header advertised and did not have; the overclaim
    recorded there is discharged by this line. -/
theorem reflectionPositive_prism_strict (hm : m ≠ 0) {v : V → ℝ} (hv : v ≠ 0) :
    0 < GraphReflection.reflectedForm (prism K) m (swap (V := V))
          (GraphReflectionPositive.ext (lower V) (fun x => v (lowerEquiv V x))) := by
  have hgap :=
    (Matrix.posDef_iff_dotProduct_mulVec.mp (green_sub_green_posDef K hm)).2 hv
  rw [Matrix.sub_mulVec, dotProduct_sub] at hgap
  have h4 := reflectedForm_prism_eq' K hm v
  linarith

/-! ## 4. Review round 93 — the ways this could be hollow

**"Four files to get one strict inequality."** Three of them were doing other
things and said so; the chain is `PrismTransfer` (the identification),
`PrismGreen` (the matrices and inverses), `PrismReflectedForm` (the equality)
and this one (the strictness). **What made the last step small is the
equality**, which turned "prove a form strictly positive" into "prove a
difference of two matrices positive definite" — and the file that produced the
equality said so at the time rather than in hindsight.

**"Is `PosDef.mul_self` really absent from Mathlib?"** The claim made is
narrower than that and is the one the search supports: Mathlib has
`posSemidef_conjTranspose_mul_self` and **no definite analogue was found under
`LinearAlgebra/Matrix/PosDef.lean`**. It is a four-line proof here because for
Hermitian `P` the product is `Pᴴ P`, and the only extra fact needed is that
`P *ᵥ x ≠ 0` for `x ≠ 0` — **which comes out of positive definiteness
directly, with no determinant and no invertibility lemma**: if `P *ᵥ x` were
zero the defining inequality would read `0 < 0`.

**"§1's strict antitonicity is stated only for `M = P + 1 + 1`. Is that
cheating?"** It is narrower than the general theorem and the header says so in
the caveats rather than the claims. The general form — `M − P` positive
definite — is true and this proof gives it, since nothing below uses more than
`M − P = 1 + 1` to split the product. **It is not written because it was not
needed, and writing it to look general would be inventing scope.**

**"Does the trap recorded last unit still stand?"** Yes, and this file does
not walk into it. `CStarAlgebra.inv_le_inv_iff` gives strictness in the ORDER;
what §3 needs and §1 supplies is that the DIFFERENCE is positive definite.
**The proof here never mentions the order on matrices at all** — it factors
the difference as `Q + Q` for an explicitly positive definite `Q`, which is a
stronger and more direct route than anything the order relation would give.

**"So is the prism now finished?"** For this axiom, on this graph, yes: the
form is evaluated and strictly positive. **Nothing here extends to the box or
the torus**, and the reason is structural rather than technical — those graphs
have no identification of the blocks with base-graph operators, so their
reflected forms are not differences of Green functions. Strictness for the
lattice cases would need a different argument and none is offered.
-/

end PrismStrict
