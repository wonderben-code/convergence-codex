/-
  HermitePiComplete.lean — **STAIR N2. Completeness of the multi-index
  Hermite system in every dimension.**

  WHAT THIS IS. The n-dimensional staircase called N2 "the stair that decides
  whether the item is a build or a project", and left it unprobed for a day
  and then routed through characteristic functions for two more. This file
  closes it, and by the route the staircase named on the FIRST day and that
  a probe then talked me out of (ERRATUM 49): **induction on the dimension,
  reducing to the estate's own one-dimensional `hermite_complete` twice —
  once through the inductive hypothesis, once on the slices.** No
  characteristic functions, no exponential series, no transport to an
  inner-product space.

  THE STATEMENT: if `F ∈ L²(γⁿ)` pairs to zero with every multi-index
  Hermite product `Hpi n m`, then `F = 0` almost everywhere. Equivalently,
  the multi-index Hermite system is TOTAL.

  HOW THE INDUCTION GOES, in one paragraph. Fix `F` on `ℝⁿ⁺¹` orthogonal to
  every `Hpi (n+1) m`. For each one-dimensional index `m₀`, the
  slice-integral `G_{m₀}(y) = ∫ F(cons x₀ y)·H_{m₀}(x₀) dγ(x₀)` is in
  `L²(γⁿ)` (`memLp_G`) and is orthogonal to every `Hpi n m'`
  (`slice_orthogonality`) — together `slice_hypothesis`, which is exactly
  the inductive hypothesis's input. So each `G_{m₀}` vanishes a.e. The index
  runs over `ℕ`, which is COUNTABLE, so `ae_all_iff` upgrades "for each `m₀`,
  a.e. `y`" to "**for a.e. `y`, every `m₀` at once**" — that is the step
  `HermitePiSlice`'s header called residue (ii), and it is where countability
  does the work. For such a `y` the slice `x₀ ↦ F(cons x₀ y)` is an `L²(γ)`
  function all of whose Hermite coefficients vanish, so it is zero a.e. by
  `hermite_complete`. Finally `∫|F|` peels and swaps to `∫ᵧ ∫ₓ₀ |F(cons x₀ y)|`,
  whose inner integral is a.e. zero — so `∫|F| = 0` and `F = 0` a.e.

  WHAT IS AND IS NOT NEW HERE. The plumbing is `HermitePiPeel`; the transfer
  is `HermitePiSlice`; the `L²` bound is `HermitePiSliceL2`. What this file
  adds is the induction itself, the base case, and the countable-intersection
  step — and the honest accounting is that the previous three files are where
  the work went.

  THE OTHER ROUTE IS NOT WASTED AND IS NOT DELETED. `GaussPiExp` and
  `GaussEuclid` were built for the characteristic-function route. They remain
  correct, they remain in the estate, and one of them gives the estate a
  characteristic-function uniqueness theorem on the space it actually works
  in (`ext_of_charFun_pi`), which it did not have and may want elsewhere.
  **They are simply not on the path that closed N2**, and saying so plainly
  is better than retro-fitting a story in which every unit was necessary.

  WHAT THIS DOES NOT DO. It does not build the `HilbertBasis` — that is N3b,
  the `HilbertBasis.mkOfOrthogonalEqBot` call, which consumes this theorem
  but needs it translated from "orthogonal to every `Hpi n m`" into
  "`(span (range eHpi))ᗮ = ⊥` in `Lp ℝ 2 (gaussPi n)`". That translation is
  `Lp` bookkeeping, it is not free, and it is a separate unit. Nothing here
  says anything about Sobolev spaces, weak derivatives, or Poincaré in n
  dimensions; those are N4–N6 and they are untouched.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiSliceL2

namespace HermitePiComplete

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiPeel HermitePiSlice HermitePiSliceL2

noncomputable section

/-! ## 1. The base case

At `n = 0` the index type is empty, so `Hpi 0 m` is the empty product `1`
and `Fin 0 → ℝ` is a subsingleton. The hypothesis at any index reads
`∫ F = 0`, and on a subsingleton with a probability measure that is
`F(pt) = 0`.
-/

-- The empty product is `1`: `HermitePi.Hpi_zero_dim`, which stair N1 already
-- proved rather than leaving to the reader. Nothing is restated here.

theorem complete_zero {F : (Fin 0 → ℝ) → ℝ}
    (h : ∀ m : Fin 0 → ℕ, ∫ x, F x * Hpi 0 m x ∂gaussPi 0 = 0) :
    F =ᵐ[gaussPi 0] 0 := by
  have hconst : ∀ x : Fin 0 → ℝ, F x = F 0 := by
    intro x
    congr 1
    funext i
    exact i.elim0
  have h0 := h 0
  have hrw : ∀ x : Fin 0 → ℝ, F x * Hpi 0 0 x = F 0 := by
    intro x
    rw [Hpi_zero_dim, mul_one, hconst x]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw), integral_const] at h0
  rw [probReal_univ, one_smul] at h0
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Pi.zero_apply, hconst x]
  exact h0

/-! ## 2. Residue (ii): countability, where "each" becomes "all at once"

`ae_all_iff` needs the index type to be countable, and the one-dimensional
Hermite index is `ℕ`. This is the only place countability is used, and
without it the whole induction fails: "for every `m₀`, almost every `y`"
would leave a different null set for each `m₀`, and their union need not be
null.
-/

theorem ae_all_slice_zero (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hG : ∀ m₀ : ℕ, G n F m₀ =ᵐ[gaussPi n] 0) :
    ∀ᵐ y ∂gaussPi n, ∀ m₀ : ℕ, G n F m₀ y = 0 := by
  rw [ae_all_iff]
  intro m₀
  filter_upwards [hG m₀] with y hy
  exact hy

/-- With countability spent, one-dimensional completeness applies to the
    slice: for almost every `y` the function `x₀ ↦ F(cons x₀ y)` vanishes
    almost everywhere. -/
theorem ae_slice_eq_zero (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1)))
    (hG : ∀ m₀ : ℕ, G n F m₀ =ᵐ[gaussPi n] 0) :
    ∀ᵐ y ∂gaussPi n, ∀ᵐ x₀ ∂(gaussianReal 0 1), F (Fin.cons x₀ y) = 0 := by
  filter_upwards [ae_all_slice_zero n hG, memLp_slice_ae n hF] with y hy hmem
  have hzero := hermite_complete (fun x₀ => F (Fin.cons x₀ y)) hmem
    (fun m₀ => hy m₀)
  filter_upwards [hzero] with x₀ hx₀
  exact hx₀

/-! ## 3. From "every slice vanishes" to "`F` vanishes"

Peel, swap, and integrate the absolute value. Working with `|F|` rather than
with a product-measure a.e. statement keeps the argument inside the Fubini
theorems `HermitePiPeel` already exports.
-/

theorem eq_zero_of_ae_slice (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi (n + 1)))
    (hs : ∀ᵐ y ∂gaussPi n, ∀ᵐ x₀ ∂(gaussianReal 0 1), F (Fin.cons x₀ y) = 0) :
    F =ᵐ[gaussPi (n + 1)] 0 := by
  have hFint : Integrable F (gaussPi (n + 1)) := hF.integrable one_le_two
  have habs : Integrable (fun z => |F z|) (gaussPi (n + 1)) := hFint.abs
  have hzero : ∫ z, |F z| ∂gaussPi (n + 1) = 0 := by
    rw [← integral_peel n (fun z => |F z|),
      integral_prod_symm _ (integrable_peel n hFint).abs]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hs] with y hy
    simp only [Pi.zero_apply]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hy] with x₀ hx₀
    simp only [Pi.zero_apply]
    rw [hx₀, abs_zero]
  have := (integral_eq_zero_iff_of_nonneg (fun z => abs_nonneg (F z)) habs).mp hzero
  filter_upwards [this] with z hz
  exact abs_eq_zero.mp hz

/-! ## 4. STAIR N2 -/

/-- **COMPLETENESS OF THE MULTI-INDEX HERMITE SYSTEM IN EVERY DIMENSION.**
    A square-integrable function on `ℝⁿ` orthogonal to every product of
    Hermite polynomials is zero almost everywhere.

    This is the deciding stair of the n-dimensional item, and the induction
    reduces it to the estate's own one-dimensional `hermite_complete`. -/
theorem hpi_complete : ∀ (n : ℕ) (F : (Fin n → ℝ) → ℝ), MemLp F 2 (gaussPi n) →
    (∀ m : Fin n → ℕ, ∫ x, F x * Hpi n m x ∂gaussPi n = 0) → F =ᵐ[gaussPi n] 0 := by
  intro n
  induction n with
  | zero => exact fun F _ h => complete_zero h
  | succ n ih =>
    intro F hF h
    have hG : ∀ m₀ : ℕ, G n F m₀ =ᵐ[gaussPi n] 0 := by
      intro m₀
      obtain ⟨hmem, horth⟩ := slice_hypothesis n hF m₀ h
      exact ih (G n F m₀) hmem horth
    exact eq_zero_of_ae_slice n hF (ae_slice_eq_zero n hF hG)

/-- The contrapositive, which is the form a reader looking for "total" will
    recognise: a nonzero `L²` function has a nonzero Hermite coefficient. -/
theorem exists_nonzero_coeff (n : ℕ) {F : (Fin n → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi n)) (hne : ¬ F =ᵐ[gaussPi n] 0) :
    ∃ m : Fin n → ℕ, ∫ x, F x * Hpi n m x ∂gaussPi n ≠ 0 := by
  by_contra hc
  push Not at hc
  exact hne (hpi_complete n F hF hc)

/-- Uniqueness of the coefficients: two `L²` functions with the same Hermite
    coefficients agree almost everywhere. -/
theorem eq_of_coeff_eq (n : ℕ) {F F' : (Fin n → ℝ) → ℝ}
    (hF : MemLp F 2 (gaussPi n)) (hF' : MemLp F' 2 (gaussPi n))
    (h : ∀ m : Fin n → ℕ, ∫ x, F x * Hpi n m x ∂gaussPi n
        = ∫ x, F' x * Hpi n m x ∂gaussPi n) :
    F =ᵐ[gaussPi n] F' := by
  have hsub : (fun x => F x - F' x) =ᵐ[gaussPi n] 0 := by
    refine hpi_complete n _ (hF.sub hF') fun m => ?_
    have hpt : ∀ x, (F x - F' x) * Hpi n m x
        = F x * Hpi n m x - F' x * Hpi n m x := fun x => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      integral_sub (integrable_F_mul_Hpi n hF m) (integrable_F_mul_Hpi n hF' m),
      h m, sub_self]
  filter_upwards [hsub] with x hx
  have : F x - F' x = 0 := hx
  linarith

/-! ## 5. Non-vacuity: the theorem is not about an empty class

`hpi_complete` would be uninteresting if its hypothesis were unsatisfiable
in a nontrivial way, or if the conclusion were automatic. Neither: the
Hermite products themselves are `L²` functions that are NOT a.e. zero, and
each has a nonzero coefficient against itself.
-/

theorem Hpi_not_ae_zero (n : ℕ) (m : Fin n → ℕ) : ¬ Hpi n m =ᵐ[gaussPi n] 0 := by
  intro hz
  have hcoeff : ∫ x, Hpi n m x * Hpi n m x ∂gaussPi n = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hz] with x hx
    simp only [Pi.zero_apply] at hx ⊢
    rw [hx, mul_zero]
  rw [Hpi_orthogonal, if_pos rfl] at hcoeff
  have hpos : (0:ℝ) < ∏ i, ((m i).factorial : ℝ) :=
    Finset.prod_pos fun i _ => by positivity
  exact absurd hcoeff (ne_of_gt hpos)

/-- So the system separates points of `L²` in the strongest sense the
    statement allows: `hpi_complete` applied to a Hermite product would force
    it to vanish, and it does not. -/
theorem exists_nonzero_coeff_Hpi (n : ℕ) (m : Fin n → ℕ) :
    ∃ k : Fin n → ℕ, ∫ x, Hpi n m x * Hpi n k x ∂gaussPi n ≠ 0 :=
  exists_nonzero_coeff n (Hpi_memLp n m) (Hpi_not_ae_zero n m)

/-! ## 6. Review round 50 — the ways this could be hollow

**"The induction could be circular — `hermite_complete` in disguise."** It
uses `hermite_complete` twice and neither use is the theorem being proved:
once through the INDUCTIVE HYPOTHESIS at dimension `n` (which is this
theorem at a strictly smaller index, so the recursion is well-founded on
`n`), and once at dimension 1 on the slices (which is the estate's
pre-existing one-dimensional result, proved by a completely different
argument — characteristic functions — in `HermiteCompleteness`). The base
case is `n = 0` and is proved outright.

**"The countability step could be doing nothing."** It is the load-bearing
step and §2 says why: "for every `m₀`, almost every `y`" gives a null set
depending on `m₀`, and an arbitrary union of null sets is not null. `ℕ` is
countable, so the union is null, and only then is there a single `y` at
which ALL coefficients of the slice vanish — which is what
`hermite_complete` needs. Remove countability and the proof does not
degrade, it fails.

**"The base case could be vacuous or wrong."** `Fin 0 → ℝ` is a
subsingleton and `gaussPi 0` is a probability measure on it, so `∫ F = F(pt)`
and the single hypothesis instance gives `F(pt) = 0`. Stated as
`complete_zero` rather than dispatched by `simp`, because a base case that
`simp` closes is a base case nobody has read.

**"It might not be the statement N3b needs."** It is not, YET, and the
header says so: `mkOfOrthogonalEqBot` wants `(span (range eHpi))ᗮ = ⊥` in
`Lp ℝ 2 (gaussPi n)`, and this theorem is about integrals of raw functions.
The translation is `Lp` bookkeeping and is a separate unit. Claiming N3b
here would be exactly the joint-between-two-files error of ERRATUM 48.

**"The non-vacuity could be circular."** `Hpi_not_ae_zero` is proved from
`Hpi_orthogonal` — stair N1, which is independent of this file — and not
from `hpi_complete`. `exists_nonzero_coeff_Hpi` then combines the two, so it
is a consequence rather than a check; the check is `Hpi_not_ae_zero`.
-/

end

end HermitePiComplete
