/-
  AbsSteinWitnessPi.lean — **a NON-POLYNOMIAL member of the n-dimensional
  Stein class**, and with it the retraction in `HermitePiPoincare`'s header
  becomes a theorem.

  WHY THIS FILE EXISTS, AND IT IS A CORRECTION OF MINE. `HermitePiPoincare`
  proves the Gaussian Poincaré inequality in n dimensions on the class
  `HermitePiStein.SteinPairPi`. An earlier draft of that file's header
  claimed the class is strictly LARGER than the polynomials. **It was false
  when written**: every member that file exhibits is a Hermite product, and
  Hermite products are polynomials. The claim was shrunk to the true one and
  the gap was named on the watchlist. This file closes it.

  WHAT IS PROVED. **`absCoord_steinPairPi`**: for each coordinate `i`,
  `x ↦ |xᵢ|` is in `SteinPairPi n` with gradient `sgn(xᵢ)·eᵢ`. And
  **`abs_not_polynomial`** — for `n ≥ 1`, `|xᵢ|` is not a.e. equal to any
  everywhere-differentiable function, hence not to any polynomial. Together:
  **the class is strictly larger than the polynomials in every dimension
  `n ≥ 1`**, and the n-dimensional Poincaré inequality is genuinely beyond
  polynomials.

  THE MECHANISM, WHICH IS WHY THIS IS ONE UNIT AND NOT FIVE. The integrand
  `|xᵢ|·Hpi n k x` is a PRODUCT OF ONE-VARIABLE FUNCTIONS — `|t|·H_{kᵢ}(t)`
  in coordinate `i`, `H_{k_l}(t)` elsewhere — so Mathlib's
  **`integral_fintype_prod_eq_prod`** (no integrability hypothesis; the same
  lemma that flattened stair N1) splits both sides of the pairing into
  products of one-dimensional integrals. Then:

  * at coordinate `i`, the condition collapses to
    `∫|t|·H_{mᵢ+1} dγ = ∫ sgn(t)·H_{mᵢ} dγ`, which is exactly the estate's
    `AbsSteinWitness.steinPair_abs` tested at `q = H_{mᵢ}`;
  * at every other coordinate `j`, the factor `∫ H_{mⱼ+1} dγ` vanishes
    because `mⱼ + 1 ≥ 1`, and the gradient component is `0` by definition.

  So the whole transport is the one-dimensional witness plus the product
  formula plus `∫ H_k dγ = δ_{k,0}`. **No new analysis.** The estimate made
  after probing — kind routine, amount one unit — is recorded here so it can
  be checked against this file.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import HermitePiPoincare
import AbsSteinWitness

namespace AbsSteinWitnessPi

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare HermiteCompleteness GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiStein HermitePiPoincare AbsSteinWitness GaussPiDensity

noncomputable section

/-! ## 1. One-dimensional facts, in the form the product formula wants -/

/-- `∫ H_k dγ = δ_{k,0}` — orthogonality against `H₀ = 1`. -/
theorem integral_H (k : ℕ) :
    ∫ t, (H k).eval t ∂gauss = if k = 0 then 1 else 0 := by
  have hone : (fun t : ℝ => (H k).eval t)
      = fun t => (H k).eval t * (H 0).eval t := by
    funext t; rw [H_zero]; simp
  rw [hone, hermite_orthogonal_gauss]
  split_ifs with hk
  · rw [hk]; simp
  · rfl

/-- The one-dimensional Stein pairing at `q = H k`, written with the
    recurrence already applied: `∫ |t|·H_{k+1} dγ = ∫ sgn(t)·H_k dγ`. -/
theorem abs_pairing (k : ℕ) :
    ∫ t, |t| * (H (k + 1)).eval t ∂gauss = ∫ t, sgn t * (H k).eval t ∂gauss := by
  have h := steinPair_abs.2.2 (H k)
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [H_succ k]

/-! ## 2. The n-dimensional witness

Both sides of the pairing are integrals of a product of one-variable
functions, so `integral_fintype_prod_eq_prod` turns each into a product of
one-dimensional integrals. Everything after that is §1 and case analysis on
whether the coordinate being tested is the one carrying the absolute value.
-/

/-- The absolute value of the `i`-th coordinate. -/
def absCoord (n : ℕ) (i : Fin n) (x : Fin n → ℝ) : ℝ := |x i|

/-- Its gradient: `sgn(xᵢ)` in the `i`-th slot, `0` elsewhere. -/
def sgnCoord (n : ℕ) (i : Fin n) (j : Fin n) (x : Fin n → ℝ) : ℝ :=
  if j = i then sgn (x i) else 0

theorem memLp_absCoord (n : ℕ) (i : Fin n) : MemLp (absCoord n i) 2 (gaussPi n) := by
  have hco : MemLp (fun x : Fin n → ℝ => x i) 2 (gaussPi n) :=
    (memLp_congr_ae (Filter.Eventually.of_forall fun x => Hpi_single_eq_coord n i x)).mp
      (Hpi_memLp n (Pi.single i 1))
  exact hco.abs

theorem memLp_sgnCoord (n : ℕ) (i j : Fin n) :
    MemLp (sgnCoord n i j) 2 (gaussPi n) := by
  by_cases hj : j = i
  · have heq : sgnCoord n i j = fun x : Fin n → ℝ => sgn (x i) := by
      funext x; rw [sgnCoord, if_pos hj]
    rw [heq]
    refine memLp_of_bounded (a := -1) (b := 1) ?_ ?_ 2
    · exact Filter.Eventually.of_forall fun x =>
        Set.mem_Icc.mpr (abs_le.mp (abs_sgn_le (x i)))
    · exact (measurable_sgn.comp (measurable_pi_apply i)).aestronglyMeasurable
  · have heq : sgnCoord n i j = fun _ : Fin n → ℝ => (0:ℝ) := by
      funext x; rw [sgnCoord, if_neg hj]
    rw [heq]
    exact memLp_const 0

/-- Both sides of the pairing are integrals of a PRODUCT OF ONE-VARIABLE
    functions, differing from the plain Hermite product only in slot `i`.
    `Function.update` names that family without an `if` whose branches are
    functions — which is what made a first attempt's typeclass resolution
    stick.

    **No hypothesis on `w` whatsoever**, because
    `integral_fintype_prod_eq_prod` carries none: if the integrals do not
    converge both sides are `0` and the identity still holds. That is
    stronger than the two uses below need, and it is stated at the strength
    the proof actually gives. -/
theorem integral_coordFamily (n : ℕ) (i : Fin n) (k : Fin n → ℕ) (w : ℝ → ℝ) :
    (∫ x, w (x i) * Hpi n k x ∂gaussPi n)
      = (∫ t, w t * (H (k i)).eval t ∂gauss)
        * ∏ l ∈ Finset.univ.erase i, ∫ t, (H (k l)).eval t ∂gauss := by
  classical
  set u : Fin n → ℝ → ℝ :=
    Function.update (fun l t => (H (k l)).eval t) i
      (fun t => w t * (H (k i)).eval t) with hu
  have hui : u i = fun t => w t * (H (k i)).eval t := by
    rw [hu, Function.update_self]
  have hul : ∀ l, l ≠ i → u l = fun t => (H (k l)).eval t := by
    intro l hl
    rw [hu, Function.update_of_ne hl]
  have hfac : (fun x : Fin n → ℝ => w (x i) * Hpi n k x) = fun x => ∏ l, u l (x l) := by
    funext x
    rw [Hpi,
      ← Finset.mul_prod_erase Finset.univ (fun l => (H (k l)).eval (x l)) (Finset.mem_univ i),
      ← Finset.mul_prod_erase Finset.univ (fun l => u l (x l)) (Finset.mem_univ i)]
    simp only [hui, ← mul_assoc]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [hul l (Finset.ne_of_mem_erase hl)]
  rw [hfac, gaussPi, integral_fintype_prod_eq_prod,
    ← Finset.mul_prod_erase Finset.univ
      (fun l => ∫ t, u l t ∂(gaussianReal 0 1)) (Finset.mem_univ i)]
  simp only [hui]
  congr 1
  refine Finset.prod_congr rfl fun l hl => ?_
  rw [hul l (Finset.ne_of_mem_erase hl)]

/-- The left-hand side of the pairing, factorised. -/
theorem integral_abs_mul_Hpi (n : ℕ) (i : Fin n) (k : Fin n → ℕ) :
    (∫ x, absCoord n i x * Hpi n k x ∂gaussPi n)
      = (∫ t, |t| * (H (k i)).eval t ∂gauss)
        * ∏ l ∈ Finset.univ.erase i, ∫ t, (H (k l)).eval t ∂gauss :=
  integral_coordFamily n i k (fun t => |t|)

/-- The right-hand side of the pairing, factorised — only the `j = i` slot
    survives, and there the `sgn` sits in coordinate `i`. -/
theorem integral_sgn_mul_Hpi (n : ℕ) (i : Fin n) (m : Fin n → ℕ) :
    (∫ x, sgnCoord n i i x * Hpi n m x ∂gaussPi n)
      = (∫ t, sgn t * (H (m i)).eval t ∂gauss)
        * ∏ l ∈ Finset.univ.erase i, ∫ t, (H (m l)).eval t ∂gauss := by
  have heq : (fun x : Fin n → ℝ => sgnCoord n i i x * Hpi n m x)
      = fun x => sgn (x i) * Hpi n m x := by
    funext x
    rw [sgnCoord, if_pos rfl]
  rw [show (∫ x, sgnCoord n i i x * Hpi n m x ∂gaussPi n)
      = ∫ x, sgn (x i) * Hpi n m x ∂gaussPi n from by rw [heq]]
  exact integral_coordFamily n i m sgn

/-- **THE WITNESS.** `|xᵢ|` is in the n-dimensional Stein class with
    gradient `sgn(xᵢ)·eᵢ`. -/
theorem absCoord_steinPairPi (n : ℕ) (i : Fin n) :
    SteinPairPi n (absCoord n i) (sgnCoord n i) := by
  classical
  refine ⟨memLp_absCoord n i, fun j => memLp_sgnCoord n i j, fun j m => ?_⟩
  -- turn the left-hand side into the pairing at the raised index
  have hL : (∫ x, absCoord n i x
        * (x j * Hpi n m x - fderiv ℝ (Hpi n m) x (Pi.single j (1:ℝ))) ∂gaussPi n)
      = ∫ x, absCoord n i x * Hpi n (succAt m j) x ∂gaussPi n :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp only; rw [Hpi_succ])
  rw [hL, integral_abs_mul_Hpi]
  by_cases hj : j = i
  · -- the coordinate carrying the absolute value: the 1-d witness
    subst hj
    rw [integral_sgn_mul_Hpi, succAt_self]
    congr 1
    · exact abs_pairing (m j)
    · refine Finset.prod_congr rfl fun l hl => ?_
      rw [succAt_of_ne m (Finset.ne_of_mem_erase hl)]
  · -- any other coordinate: the raised factor integrates to zero
    have hgz : (∫ x, sgnCoord n i j x * Hpi n m x ∂gaussPi n) = 0 := by
      have hz : (fun x : Fin n → ℝ => sgnCoord n i j x * Hpi n m x)
          = fun _ => (0:ℝ) := by
        funext x; rw [sgnCoord, if_neg hj, zero_mul]
      rw [hz, integral_zero]
    rw [hgz]
    -- the `j`-th factor of the product is `∫ H_{mⱼ+1} dγ = 0`
    have hjmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hfacj : ∫ t, (H (succAt m j j)).eval t ∂gauss = 0 := by
      rw [succAt_self, integral_H, if_neg (Nat.succ_ne_zero (m j))]
    rw [Finset.prod_eq_zero hjmem hfacj, mul_zero]

/-! ## 3. The witness is genuinely non-polynomial

Without this section the file would exhibit a member and leave open whether
it is one `poincare_MV` already covers. The one-dimensional argument
(`AbsSteinWitness.abs_not_ae_differentiable`) needs no slicing and neither
does this one: against a measure of FULL SUPPORT, a.e.-equality of
continuous functions is equality, so a differentiable `g` agreeing a.e. with
`|xᵢ|` would BE `|xᵢ|`, and restricting to the `i`-th coordinate contradicts
`not_differentiableAt_abs_zero`.

The one thing that had to be built is the full-support instance: Mathlib has
no `IsOpenPosMeasure` for a `Measure.pi`, and `gaussPi_eq_withDensity` — the
identity forced out of me two days ago — supplies it in three lines.

**⚠ THE SENTENCE ABOVE IS FALSE. Kept per `ERRATUM 94`; `ERRATUM 356` records it.**
`Mathlib.MeasureTheory.Constructions.Pi` line 627 declares
`instance pi.isOpenPosMeasure [∀ i, TopologicalSpace (α i)] [∀ i, IsOpenPosMeasure (μ i)] :
IsOpenPosMeasure (Measure.pi μ)` — **exactly the general statement the sentence denies**, and it
needs nothing this estate did not already have: `AbsSteinWitness` supplies
`(gauss : Measure ℝ).IsOpenPosMeasure`, and `gaussPi n` **is** `Measure.pi (fun _ => gaussianReal
0 1)`. Two lines now prove the instance, checked in Lean and not by reading.

**WHERE THE REAL GAP IS, since one exists and the sentence points at the wrong place.** Mathlib
lacks `IsOpenPosMeasure` **for the one-dimensional Gaussian** — that is the piece this estate had
to build, and it is in `AbsSteinWitness`, not here. The `Measure.pi` step was free.
**And the reason it did not look free**: `gaussPi` is a `def`, so instance search does not see
through it to `Measure.pi`; `unfold` first and it resolves. A `def`'s opacity is not a library
absence, and the sentence recorded it as one.
-/

/-- Lebesgue measure is absolutely continuous with respect to the Gaussian product measure.
**No longer what proves the full-support instance** (`ERRATUM 356`) — it stands as a fact in its
own right, and is kept rather than deleted because it is about the two measures and not about the
instance that used to consume it. -/
theorem volume_absolutelyContinuous_gaussPi (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) ≪ gaussPi n := by
  rw [gaussPi_eq_withDensity]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact ((measurable_rhoPi n).ennreal_ofReal).aemeasurable
  · exact Filter.Eventually.of_forall fun x =>
      (ENNReal.ofReal_ne_zero_iff).mpr (rhoPi_pos n x)

/-- **FULL SUPPORT, STRAIGHT OFF MATHLIB'S `pi` INSTANCE** (`ERRATUM 356`). The proof that stood
here went through `volume_absolutelyContinuous_gaussPi` because the header believed Mathlib had no
`IsOpenPosMeasure` for a `Measure.pi`. It has one; all it wants is the one-dimensional instance,
which `AbsSteinWitness` supplies. The `unfold` is needed only because `gaussPi` is a `def` and
instance search will not see through it. -/
instance instIsOpenPosMeasureGaussPi (n : ℕ) : (gaussPi n).IsOpenPosMeasure := by
  unfold gaussPi
  infer_instance

theorem continuous_absCoord (n : ℕ) (i : Fin n) : Continuous (absCoord n i) :=
  continuous_abs.comp (continuous_apply i)

theorem differentiable_update (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    Differentiable ℝ fun t : ℝ => Function.update x i t := by
  refine differentiable_pi.mpr fun j => ?_
  by_cases hj : j = i
  · subst hj; simp
  · simp only [Function.update_of_ne hj]
    exact differentiable_const _

/-- **`|xᵢ|` IS NOT A.E. EQUAL TO ANY DIFFERENTIABLE FUNCTION**, hence not to
    any polynomial. So the class `SteinPairPi` is strictly larger than the
    polynomials, and `HermitePiPoincare.poincare_steinPi` is genuinely
    beyond `poincare_MV`. -/
theorem absCoord_not_ae_differentiable (n : ℕ) (i : Fin n)
    (g : (Fin n → ℝ) → ℝ) (hdiff : Differentiable ℝ g) :
    ¬ (g =ᵐ[gaussPi n] absCoord n i) := by
  intro hae
  have heq : g = absCoord n i :=
    (Continuous.ae_eq_iff_eq (gaussPi n) hdiff.continuous (continuous_absCoord n i)).mp hae
  -- restrict to the `i`-th coordinate through the origin
  have hcomp : DifferentiableAt ℝ
      (fun t : ℝ => g (Function.update (0 : Fin n → ℝ) i t)) 0 :=
    (hdiff _).comp 0 ((differentiable_update n 0 i) 0)
  have hslice : (fun t : ℝ => g (Function.update (0 : Fin n → ℝ) i t)) = abs := by
    funext t
    rw [heq, absCoord, Function.update_self]
  rw [hslice] at hcomp
  exact not_differentiableAt_abs_zero hcomp

/-- **THE STRICT CONTAINMENT, as one statement.** For every `n ≥ 1` and
    every coordinate, there is a member of the n-dimensional Stein class
    that no differentiable function — in particular no polynomial —
    represents. -/
theorem steinPairPi_strictly_beyond_differentiable (n : ℕ) (i : Fin n) :
    (∃ g : Fin n → ((Fin n → ℝ) → ℝ), SteinPairPi n (absCoord n i) g)
      ∧ ∀ p : (Fin n → ℝ) → ℝ, Differentiable ℝ p →
          ¬ (p =ᵐ[gaussPi n] absCoord n i) :=
  ⟨⟨sgnCoord n i, absCoord_steinPairPi n i⟩, absCoord_not_ae_differentiable n i⟩

/-! ## 4. Review round 57 — the ways this could be hollow

**"The transport could be the 1-d theorem restated."** It consumes the 1-d
theorem exactly once, at `q = H_{mᵢ}`, and everything around it is the
product structure: `integral_coordFamily` factorises BOTH sides through
`integral_fintype_prod_eq_prod`, and the vanishing at the other coordinates
is `∫ H_{mⱼ+1} dγ = 0`, which has no 1-dimensional content at all.

**"`integral_coordFamily` might need hypotheses it is not carrying."** It
carries none on `w`, deliberately: `integral_fintype_prod_eq_prod` has no
integrability hypothesis, so if the integrals diverge both sides are `0` and
the identity still holds. Stated at the strength the proof gives rather than
the strength the two uses need.

**"The strictness might be about the wrong thing."** It is about exactly the
thing that was retracted: `HermitePiPoincare`'s header claimed the class is
strictly larger than the polynomials, and could not back it. §3 backs it, and
does so in the stronger form — not merely non-polynomial but not a.e. equal
to any DIFFERENTIABLE function.

**"The full-support instance could be doing hidden work."** It is the only
new ingredient, and it exists because Mathlib has no `IsOpenPosMeasure` for
`Measure.pi`. It comes straight off `gaussPi_eq_withDensity`, which was
itself forced by a failed prediction two days ago — the second time that
identity has paid for having been proved unconditionally.
-/

end

end AbsSteinWitnessPi
