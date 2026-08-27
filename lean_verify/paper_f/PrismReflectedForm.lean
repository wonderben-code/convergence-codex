/-
  PrismReflectedForm.lean — the reflected form of the two-layer stack,
  evaluated.

  WHY. `PrismTransfer`'s header carries a recorded overclaim: its draft
  advertised `reflectedForm_prism_eq` and `reflectionPositive_prism_strict`,
  and it had neither. `UNLOCK_WATCHLIST.md` wrote the remaining leg out in
  four steps and `PrismGreen` did the first three. **This is step (iv), and it
  discharges the first of the two advertised theorems.** The second is still
  not proved and §4 says exactly what is missing.

  WHAT THIS FILE PROVES:
  1. **`dotProduct_submatrix_equiv`** — a quadratic form against a submatrix
     along an `Equiv` is the same form against the original matrix, reindexed.
     Small, general, and the only thing standing between `PrismGreen`'s
     inverses and the evaluation.
  2. **`energy_sym_prism`, `energy_anti_prism`** — the symmetric and
     antisymmetric energies of the stack, as base-graph Green-function forms
     at masses `m` and `√(m² + 2)`.
  3. **`reflectedForm_prism_eq` — THE EVALUATION.** For coefficients supported
     on one layer, `4 · (reflected form) = 2·⟨v, G_m v⟩ − 2·⟨v, G_{√(m²+2)} v⟩`:
     **the reflected form of a two-layer stack is half the difference of two
     base-graph Green functions.** `PrismReflection` proved this quantity
     non-negative; this says what it IS.
  4. **`reflectedForm_prism_nonneg_iff`** — and therefore reflection
     positivity on the prism is EXACTLY the statement that the base graph's
     propagator dominates its own shifted-mass propagator in the quadratic-form
     sense. Not a new proof of positivity — a translation of it into a
     statement with no reflection in it.

  WHAT THIS DOES NOT DO.


  * **`reflectionPositive_prism_strict` IS STILL NOT PROVED**, and the
    recorded overclaim in `PrismTransfer`'s header is therefore only half
    discharged. The equality above makes strictness equivalent to
    `G_m − G_{√(m²+2)}` being positive DEFINITE rather than semidefinite, and
    that needs strict antitonicity of matrix inversion. **The estate has only
    `MatrixLoewner.posDef_inv_le_inv`, which is non-strict.** Searched, and
    the scope of the search is stated because a narrowed absence claim is
    worthless (ERRATA 59, 62): no `inv_lt_inv` anywhere under
    `Analysis/CStarAlgebra/` or `Analysis/Matrix/`; and no product-of-
    commuting-positive-definites lemma in `LinearAlgebra/Matrix/PosDef.lean`,
    which is the other route.

  **SUPERSEDED 2026-08-27 IN ITS FIRST CLAUSE, kept as written (`ERRATUM 94`,
  found by `ERRATUM 305`).** *"`reflectionPositive_prism_strict` IS STILL NOT
  PROVED"* is false: `PrismStrict.reflectionPositive_prism_strict` proves it,
  and `PrismStrict` IMPORTS this file, so the sentence was falsified from
  directly above it in the import graph. **Still true** is everything the
  bullet says about what the equality reduces strictness TO, and the trap
  named in the paragraph after it — the search was accurate and the reading
  of `CStarAlgebra.inv_le_inv_iff` is still the right reading.

    **One thing the search did turn up, and it is a trap rather than a
    solution.** `CStarAlgebra.inv_le_inv_iff` exists — an `iff`, not just an
    implication — so `a⁻¹ ≤ b⁻¹ ↔ b ≤ a`, and from `b ≤ a` with `a ≠ b` one
    gets `a⁻¹ ≤ b⁻¹` with `a⁻¹ ≠ b⁻¹`. **That is strictness in the ORDER and
    it is not what strict reflection positivity needs**, which is that the
    DIFFERENCE be positive definite. The two coincide for real numbers and
    come apart for operators, and mistaking one for the other would produce a
    theorem that looks right and says less. The route is on the watchlist;
    **it is not attempted here and nothing below should be read as
    approaching it.**
  * **No spectral content.** Two Green functions at two masses is not a gap
    statement; there is no eigenvalue in this file.
  * **Two layers, free field, finite graph**, all inherited.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import PrismGreen

namespace PrismReflectedForm

open Finset Matrix GraphLaplacian GraphReflection GraphHalfSpace PrismReflection
open PrismTransfer PrismGreen

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : SimpleGraph V) [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. Reindexing a quadratic form along an equivalence -/

/-- A quadratic form against `X.submatrix e e` is the form against `X`, with
    the vector carried across by `e`. Stated over arbitrary index types; the
    only content is two applications of `Equiv.sum_comp`. -/
theorem dotProduct_submatrix_equiv {α β : Type*} [Fintype α] [Fintype β]
    (X : Matrix β β ℝ) (e : α ≃ β) (w : α → ℝ) :
    star w ⬝ᵥ (X.submatrix e e) *ᵥ w
      = star (w ∘ e.symm) ⬝ᵥ X *ᵥ (w ∘ e.symm) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Pi.star_apply,
    star_trivial, Function.comp_apply]
  have hinner : ∀ a : α, (∑ b, X (e a) (e b) * w b) = ∑ y, X (e a) y * w (e.symm y) := by
    intro a
    simpa using Equiv.sum_comp e (fun y => X (e a) y * w (e.symm y))
  have houter := Equiv.sum_comp e (fun x => w (e.symm x) * ∑ y, X x y * w (e.symm y))
  simp only [Equiv.symm_apply_apply] at houter
  rw [← houter]
  exact Finset.sum_congr rfl fun a _ => by rw [hinner a]

/-! ## 2. The two energies -/

theorem energy_sym_prism (hm : m ≠ 0) (w : ↥(lower V) → ℝ) :
    GraphReflection.energy (prism K) m
        (symExt (swap (V := V)) (lower V) (GraphReflectionPositive.ext (lower V) w))
      = 2 * (star (w ∘ (lowerEquiv V).symm) ⬝ᵥ (green K m) *ᵥ (w ∘ (lowerEquiv V).symm)) := by
  rw [GraphReflectionPositive.energy_symExt_eq isHalf_lower (isRefl_swap K) hm w,
    plusOp_inv, dotProduct_submatrix_equiv]

theorem energy_anti_prism (hm : m ≠ 0) (w : ↥(lower V) → ℝ) :
    GraphReflection.energy (prism K) m
        (antiExt (swap (V := V)) (lower V) (GraphReflectionPositive.ext (lower V) w))
      = 2 * (star (w ∘ (lowerEquiv V).symm) ⬝ᵥ
          (green K (Real.sqrt (m ^ 2 + 2))) *ᵥ (w ∘ (lowerEquiv V).symm)) := by
  rw [GraphReflectionPositive.energy_antiExt_eq isHalf_lower (isRefl_swap K) hm w,
    minusOp_inv, dotProduct_submatrix_equiv]

/-! ## 3. The evaluation

`PrismReflection` proved this quantity non-negative, through the criterion.
This says what it is.
-/

/-- **THE REFLECTED FORM OF A TWO-LAYER STACK IS HALF THE DIFFERENCE OF TWO
    BASE-GRAPH GREEN FUNCTIONS**, at masses `m` and `√(m² + 2)`. -/
theorem reflectedForm_prism_eq (hm : m ≠ 0) (w : ↥(lower V) → ℝ) :
    4 * GraphReflection.reflectedForm (prism K) m (swap (V := V))
          (GraphReflectionPositive.ext (lower V) w)
      = 2 * (star (w ∘ (lowerEquiv V).symm) ⬝ᵥ (green K m) *ᵥ (w ∘ (lowerEquiv V).symm))
        - 2 * (star (w ∘ (lowerEquiv V).symm) ⬝ᵥ
            (green K (Real.sqrt (m ^ 2 + 2))) *ᵥ (w ∘ (lowerEquiv V).symm)) := by
  have hc : ∀ p, p ∉ lower V → GraphReflectionPositive.ext (lower V) w p = 0 :=
    fun _ hp => GraphReflectionPositive.ext_notMem w hp
  rw [GraphReflection.reflectedForm_eq (isRefl_swap K),
    GraphHalfSpace.sym_eq_symExt isHalf_lower hc,
    GraphHalfSpace.anti_eq_antiExt isHalf_lower hc,
    energy_sym_prism K hm w, energy_anti_prism K hm w]

/-- The same, with the coefficients given on the base graph directly. -/
theorem reflectedForm_prism_eq' (hm : m ≠ 0) (v : V → ℝ) :
    4 * GraphReflection.reflectedForm (prism K) m (swap (V := V))
          (GraphReflectionPositive.ext (lower V) (fun x => v (lowerEquiv V x)))
      = 2 * (star v ⬝ᵥ (green K m) *ᵥ v)
        - 2 * (star v ⬝ᵥ (green K (Real.sqrt (m ^ 2 + 2))) *ᵥ v) := by
  have h := reflectedForm_prism_eq K hm (fun x => v (lowerEquiv V x))
  have hv : (fun x => v (lowerEquiv V x)) ∘ (lowerEquiv V).symm = v := by
    funext p
    simp
  rwa [hv] at h

/-- **REFLECTION POSITIVITY ON THE PRISM, WITH THE REFLECTION REMOVED.** It is
    exactly the statement that the base graph's propagator dominates its own
    shifted-mass propagator in the quadratic-form sense. Not a new proof of
    `PrismReflection.reflectionPositive_prism` — a translation of it. -/
theorem reflectedForm_prism_nonneg_iff (hm : m ≠ 0) (v : V → ℝ) :
    0 ≤ GraphReflection.reflectedForm (prism K) m (swap (V := V))
          (GraphReflectionPositive.ext (lower V) (fun x => v (lowerEquiv V x)))
      ↔ star v ⬝ᵥ (green K (Real.sqrt (m ^ 2 + 2))) *ᵥ v
          ≤ star v ⬝ᵥ (green K m) *ᵥ v := by
  constructor
  · intro h
    have h4 := reflectedForm_prism_eq' K hm v
    nlinarith [h4]
  · intro h
    have h4 := reflectedForm_prism_eq' K hm v
    nlinarith [h4]

/-! ## 4. Review round 92 — the ways this could be hollow

**"Half an overclaim discharged is still half an overclaim."** Correct, and
the header says so in its own list rather than in a footnote.
`PrismTransfer`'s draft advertised two theorems; this delivers one. The other,
`reflectionPositive_prism_strict`, is not here and **the equality proved above
is precisely what makes it a one-ingredient problem rather than an open one**:
strictness is now equivalent to `G_m − G_{√(m²+2)}` being positive definite,
which needs a strict form of an inequality the estate has only non-strictly.
**Naming that ingredient is the useful part of this file's negative half**, and
it is on the watchlist rather than in a promise.

**"Is `reflectedForm_prism_nonneg_iff` a new result or a restatement?"** A
restatement, and the docstring says so twice. `reflectionPositive_prism`
already gives the left side. What the `iff` adds is that the right side —
a statement about two propagators of the BASE graph, with no reflection, no
stack and no half in it — is equivalent. **That is a translation into a form
someone studying the base graph could use**, and translations are worth having
only when labelled as such.

**"§1 looks like it should be in Mathlib."** It may be; it was written because
`PrismGreen`'s inverses are submatrices and nothing in scope moved a quadratic
form across a submatrix along an `Equiv`. **No claim is made that Mathlib
lacks it** — the search was not run at the generality that would justify one,
and after ERRATUM 62 an unsearched absence claim is worse than none.

**"Does the equality actually depend on the identification?"** Entirely.
`energy_sym_prism` is `GraphReflectionPositive.energy_symExt_eq` composed with
`PrismGreen.plusOp_inv`, and the second is what turns an inverse over a
subtype into a Green function over the base graph. **Remove the prism and this
file has no content**: on a general graph the two blocks are not Green
functions of anything smaller, which is exactly why `PrismTransfer`'s
cancellation was recorded as specific to the stack rather than general.
-/

end PrismReflectedForm
