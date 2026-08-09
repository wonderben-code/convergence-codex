/-
  SteinSmoothPi.lean — the reverse containment, and with it the n-dimensional
  classes coincide.

  WHY. Three files landed today, and each ended by saying it does not settle
  this. `W6ConversePi` proved `SmoothSteinPairPi ⊆ SteinPairPi` — the
  direction the Poincaré inequality needs — and said plainly that the
  reverse "is not proved and is not a corollary of anything here".
  `SteinGeneralPi` and `HermitePiProper` repeated the caveat. In one
  dimension both containments are theorems and `W6Converse.stein_iff_smooth`
  closes WALLS W6 outright; in `n` the estate had one arrow.

  **THE THIRD FILE IS WHAT MAKES THIS ONE POSSIBLE, AND I DID NOT SEE IT
  WHILE WRITING IT.** The 1-dimensional proof
  (`SteinSmoothTest.smoothSteinPair_of_steinPair`) runs on the TEST FUNCTION
  being in the class. `SteinGeneralPi.steinPairPi_of_contDiff` puts every
  `Cc^∞` function there — a compactly supported smooth function is `C¹` with
  itself and its gradient in `L²(γⁿ)` for nothing. That was the missing
  ingredient, and it was sitting in a file whose own header says the reverse
  containment is out of reach.

  WHAT THIS FILE PROVES:
  1. **`fderiv_Hpi`** — `∂ᵢ(Hpi n m) = mᵢ·Hpi n (m−eᵢ)`, pointwise. The
     estate did not have this: `HermitePiPoincare.Hpi_mem` sidesteps it with
     `Hpi_succ` and orthogonality. It is the n-dimensional twin of
     `GaussianPoincare.derivative_H`, and it is what makes the Hermite
     partial continuous and what turns a pairing into a coefficient.
  2. **`integral_stein_testfun`** — for `ψ ∈ Cc^∞`,
     `∫ (xᵢψ − ∂ᵢψ)·Hpi n m dγⁿ = mᵢ·facPi(m−eᵢ)·c_{m−eᵢ}(ψ)`. The proof
     needs no integration by parts of its own: the `xᵢψ·Hpi m` terms on the
     two sides of `ψ`'s own Stein pairing are the SAME integrand, so they
     cancel, and what is left is `∫ ψ·∂ᵢ(Hpi m)`.
  3. **`smoothSteinPairPi_of_steinPairPi`** — the containment.
  4. **`steinPairPi_iff_smoothSteinPairPi`**, **`steinPairPi_iff_sobolevWeakPi`**
     and **`w6_answered_pi`** — **the three n-dimensional classes COINCIDE**,
     stated in the shape WALLS W6 asks the question, one dimension at a
     time no longer being a restriction.

  WHAT THIS DOES NOT DO. It does not give the n-dimensional coefficient
  CHARACTERISATION — membership certified by a summability condition on
  `c_m(f)` alone. In one dimension that is
  `HermiteHilbertBasis.steinPair_iff_sobolev`, and it needs a Riesz–Fischer
  argument constructing the PARTNER from the coefficients, which is not what
  any file today does. `HermitePiProper` gets properness from the one
  direction the estate already had; certifying membership from coefficients
  alone is still open. Nor does this file give a σ-scaled n-dimensional
  statement — the 1-d chain has one (`TextbookSobolevScaled`) and `n` does
  not.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new
  axioms.
-/
import SteinGeneralPi

namespace SteinSmoothPi

open MeasureTheory ProbabilityTheory Polynomial Filter Topology
open GaussianPoincare GaussianProductMeasure HermitePi
open HermitePiBessel HermitePiBasis HermitePiRiesz
open GaussPiDensity HermitePiStein HermitePiPoincare TextbookSobolevPi
open W6ConversePi SteinGeneralPi

noncomputable section

variable {n : ℕ}

/-! ## 1. The pointwise Hermite derivative in n variables

`GaussianPoincare.derivative_H` says `H_k′ = k·H_{k−1}` on the line, with
`0 < k` as a hypothesis because `H_{-1}` does not exist. Carried through the
product by `fderiv_coordProd`, that gives the multi-index statement — and at
`mᵢ = 0` both sides are `0`, so the hypothesis disappears from the n-variable
form rather than being carried along.
-/

theorem deriv_H_zero (t : ℝ) : deriv (fun s : ℝ => (H 0).eval s) t = 0 := by
  rw [deriv_H_eval, H_zero]
  simp

theorem deriv_H_pred {k : ℕ} (hk : k ≠ 0) (t : ℝ) :
    deriv (fun s : ℝ => (H k).eval s) t = (k : ℝ) * (H (k - 1)).eval t := by
  rw [deriv_H_eval, derivative_H k (Nat.pos_of_ne_zero hk)]
  simp

/-- **`∂ᵢ(Hpi n m)(x) = mᵢ·Hpi n (m−eᵢ)(x)`.** The estate did not have this;
    `Hpi_mem` avoids needing it by routing through `Hpi_succ` and
    orthogonality. Below it is what turns a test function's pairing into its
    Hermite coefficients. -/
theorem fderiv_Hpi (n : ℕ) (m : Fin n → ℕ) (i : Fin n) (x : Fin n → ℝ) :
    fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)) = (m i : ℝ) * Hpi n (predAt m i) x := by
  classical
  have hprod : Hpi n m = fun y : Fin n → ℝ => ∏ j, (H (m j)).eval (y j) := rfl
  rw [hprod, fderiv_coordProd n (fun j => fun t : ℝ => (H (m j)).eval t)
    (fun j => H_differentiable (m j)) i x]
  by_cases hmi : m i = 0
  · rw [hmi]
    simp only [Nat.cast_zero, zero_mul]
    rw [deriv_H_zero, zero_mul]
  · rw [deriv_H_pred hmi]
    have hR : Hpi n (predAt m i) x
        = (H (m i - 1)).eval (x i) * ∏ j ∈ Finset.univ.erase i, (H (m j)).eval (x j) := by
      have h1 : Hpi n (predAt m i) x = ∏ j, (H (predAt m i j)).eval (x j) := rfl
      rw [h1, ← Finset.mul_prod_erase Finset.univ
        (fun j => (H (predAt m i j)).eval (x j)) (Finset.mem_univ i), predAt_self]
      congr 1
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [predAt_of_ne m (Finset.ne_of_mem_erase hj)]
    rw [hR]
    ring

/-! ## 2. Continuous with compact support, against a probability measure

Used six times below and worth two names rather than six repetitions.
`gaussPi n` is a probability measure, hence finite on compacts, which is all
either fact needs.
-/

theorem integrable_of_compactSupport {u : (Fin n → ℝ) → ℝ} (hu : Continuous u)
    (hcu : HasCompactSupport u) : Integrable u (gaussPi n) :=
  hu.integrable_of_hasCompactSupport (μ := gaussPi n) hcu

theorem memLp_of_compactSupport {u : (Fin n → ℝ) → ℝ} (hu : Continuous u)
    (hcu : HasCompactSupport u) : MemLp u 2 (gaussPi n) :=
  hu.memLp_of_hasCompactSupport (μ := gaussPi n) hcu

/-! ## 3. What a `Cc^∞` test function's Stein pairing says about its
       Hermite coefficients

The one place `SteinGeneralPi` enters, and it enters as a citation: `ψ` is
smooth with compact support, hence `C¹` with itself and its gradient in
`L²(γⁿ)`, hence a member of the Stein class. Nothing about `ψ` is assumed
here that is not automatic.
-/

theorem testfun_steinPairPi {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) :
    SteinPairPi n ψ (fun i x => fderiv ℝ ψ x (Pi.single i (1:ℝ))) := by
  have hc1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
  refine steinPairPi_of_contDiff hc1 (memLp_of_compactSupport hψ.continuous hcψ)
    fun i => memLp_of_compactSupport (continuous_gradient hc1 i)
      (hasCompactSupport_partial n hcψ i)

/-- **`∫ (xᵢψ − ∂ᵢψ)·Hpi m dγⁿ = ∫ ψ·∂ᵢ(Hpi m) dγⁿ`.** No integration by
    parts is performed here. `ψ`'s own Stein pairing says
    `∫ ψ·(xᵢ·Hpi m − ∂ᵢ Hpi m) = ∫ (∂ᵢψ)·Hpi m`, and the `xᵢ·ψ·Hpi m` term
    appearing on both sides is literally the same integrand, so it cancels. -/
theorem integral_stein_testfun_eq {ψ : (Fin n → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ) (i : Fin n)
    (m : Fin n → ℕ) :
    (∫ x, (x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ))) * Hpi n m x ∂gaussPi n)
      = ∫ x, ψ x * fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)) ∂gaussPi n := by
  have hst := (testfun_steinPairPi hψ hcψ).2.2 i m
  -- integrability of each of the three pieces
  have hcont : Continuous ψ := hψ.continuous
  have hgc : Continuous fun x : Fin n → ℝ => fderiv ℝ ψ x (Pi.single i (1:ℝ)) :=
    continuous_gradient (hψ.of_le (by exact_mod_cast le_top)) i
  have hHc : Continuous (Hpi n m) := Hpi_continuous n m
  have hHd : Continuous fun x : Fin n → ℝ =>
      fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)) := by
    have heq : (fun x : Fin n → ℝ => fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)))
        = fun x => (m i : ℝ) * Hpi n (predAt m i) x :=
      funext fun x => fderiv_Hpi n m i x
    rw [heq]
    exact continuous_const.mul (Hpi_continuous n (predAt m i))
  have hint : ∀ u : (Fin n → ℝ) → ℝ, Continuous u →
      Integrable (fun x => ψ x * u x) (gaussPi n) :=
    fun u hu => integrable_of_compactSupport (hcont.mul hu) hcψ.mul_right
  have hA : Integrable (fun x : Fin n → ℝ => ψ x * (x i * Hpi n m x)) (gaussPi n) :=
    hint _ ((continuous_apply i).mul hHc)
  have hB : Integrable (fun x : Fin n → ℝ =>
      ψ x * fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ))) (gaussPi n) := hint _ hHd
  have hC : Integrable (fun x : Fin n → ℝ =>
      fderiv ℝ ψ x (Pi.single i (1:ℝ)) * Hpi n m x) (gaussPi n) :=
    integrable_of_compactSupport (hgc.mul hHc)
      (hasCompactSupport_partial n hcψ i).mul_right
  -- split ψ's pairing into the two pieces
  have hsplit : (∫ x, ψ x * (x i * Hpi n m x
        - fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ))) ∂gaussPi n)
      = (∫ x, ψ x * (x i * Hpi n m x) ∂gaussPi n)
        - ∫ x, ψ x * fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)) ∂gaussPi n := by
    rw [← integral_sub hA hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  rw [hsplit] at hst
  -- and split the goal the same way
  have hgoal : (∫ x, (x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ))) * Hpi n m x
        ∂gaussPi n)
      = (∫ x, ψ x * (x i * Hpi n m x) ∂gaussPi n)
        - ∫ x, fderiv ℝ ψ x (Pi.single i (1:ℝ)) * Hpi n m x ∂gaussPi n := by
    rw [← integral_sub hA hC]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    ring
  rw [hgoal]
  linarith [hst]

/-- **The coefficient identity.** `xᵢψ − ∂ᵢψ` pairs with `Hpi m` exactly as
    `ψ` pairs with `Hpi (m−eᵢ)`, up to the factor `mᵢ`. -/
theorem integral_stein_testfun {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin n) (m : Fin n → ℕ) :
    (∫ x, (x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ))) * Hpi n m x ∂gaussPi n)
      = (m i : ℝ) * (facPi n (predAt m i) * coeffPi n (predAt m i) ψ) := by
  rw [integral_stein_testfun_eq hψ hcψ i m]
  have heq : (∫ x, ψ x * fderiv ℝ (Hpi n m) x (Pi.single i (1:ℝ)) ∂gaussPi n)
      = (m i : ℝ) * ∫ x, ψ x * Hpi n (predAt m i) x ∂gaussPi n := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [fderiv_Hpi]
    ring
  rw [heq, coeffPi, mul_div_cancel₀ _ (facPi_ne_zero n (predAt m i))]

/-- The same statement as a COEFFICIENT, which is the form the assembly
    consumes. Named rather than unfolded inline, because `rw [coeffPi]`
    inside the assembly hits the wrong occurrence. -/
theorem coeffPi_stein_testfun {ψ : (Fin n → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) (i : Fin n) (m : Fin n → ℕ) :
    coeffPi n m (fun x => x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ)))
      = (m i : ℝ) * (facPi n (predAt m i) * coeffPi n (predAt m i) ψ) / facPi n m := by
  rw [coeffPi, integral_stein_testfun hψ hcψ i m]

/-! ## 4. The containment

Polarised Parseval on each side, one reindex along `succAt · i`, and the two
series are equal term by term. The reindex is the same bijection
`poincare_steinPi` uses, for the same reason: the left-hand terms carry a
factor `mᵢ` and so vanish off the range.
-/

/-- **THE REVERSE CONTAINMENT.** A Hermite-tested pair is a `Cc^∞`-tested
    pair. -/
theorem smoothSteinPairPi_of_steinPairPi (n : ℕ) {f : (Fin n → ℝ) → ℝ}
    {g : Fin n → ((Fin n → ℝ) → ℝ)} (h : SteinPairPi n f g) :
    SmoothSteinPairPi n f g := by
  classical
  obtain ⟨hf, hg, hpair⟩ := h
  refine ⟨hf, hg, fun i ψ hψ hcψ => ?_⟩
  have hst : SteinPairPi n f g := ⟨hf, hg, hpair⟩
  -- ψ and the transformed test function are in L²(γⁿ)
  have hψmem : MemLp ψ 2 (gaussPi n) := memLp_of_compactSupport hψ.continuous hcψ
  have hΦc : Continuous fun x : Fin n → ℝ =>
      x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ)) :=
    ((continuous_apply i).mul hψ.continuous).sub
      (continuous_gradient (hψ.of_le (by exact_mod_cast le_top)) i)
  have hΦsupp : HasCompactSupport fun x : Fin n → ℝ =>
      x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ)) :=
    HasCompactSupport.sub hcψ.mul_left (hasCompactSupport_partial n hcψ i)
  have hΦmem : MemLp (fun x : Fin n → ℝ =>
      x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ))) 2 (gaussPi n) :=
    memLp_of_compactSupport hΦc hΦsupp
  -- polarised Parseval on the two sides
  rw [integral_mul_eq_tsum_coeffPi n hf hΦmem,
    integral_mul_eq_tsum_coeffPi n (hg i) hψmem]
  -- the left-hand terms, computed
  have hL : ∀ m : Fin n → ℕ,
      facPi n m * (coeffPi n m f
          * coeffPi n m fun x => x i * ψ x - fderiv ℝ ψ x (Pi.single i (1:ℝ)))
        = (m i : ℝ) * (facPi n (predAt m i) * coeffPi n (predAt m i) ψ)
            * coeffPi n m f := by
    intro m
    have hne := facPi_ne_zero n m
    rw [coeffPi_stein_testfun hψ hcψ i m]
    field_simp
  rw [tsum_congr hL]
  -- off the range of `succAt · i` the factor `mᵢ` is zero
  have hsupp : Function.support (fun m : Fin n → ℕ =>
      (m i : ℝ) * (facPi n (predAt m i) * coeffPi n (predAt m i) ψ)
        * coeffPi n m f)
      ⊆ Set.range fun k : Fin n → ℕ => succAt k i := by
    intro m hm
    refine mem_range_succAt n i ?_
    intro h0
    apply hm
    simp [h0]
  rw [← (succAt_injective n i).tsum_eq hsupp]
  -- and term by term the two series agree
  refine tsum_congr fun k => ?_
  rw [succAt_self, predAt_succAt, coeffPi_recursion n hst i k]
  push_cast
  ring

/-! ## 5. WALLS W6, in n dimensions -/

/-- **THE TWO CLASSES COINCIDE IN EVERY DIMENSION.** -/
theorem steinPairPi_iff_smoothSteinPairPi (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (g : Fin n → ((Fin n → ℝ) → ℝ)) :
    SteinPairPi n f g ↔ SmoothSteinPairPi n f g :=
  ⟨smoothSteinPairPi_of_steinPairPi n, steinPairPi_of_smoothSteinPairPi n⟩

/-- **AND SO DO THE HERMITE-TESTED AND THE TEXTBOOK CLASSES**, through stair
    N5. Three descriptions of one class: Hermite pairing, `Cc^∞` pairing,
    Lebesgue weak derivative. -/
theorem steinPairPi_iff_sobolevWeakPi (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (g : Fin n → ((Fin n → ℝ) → ℝ)) :
    SteinPairPi n f g ↔ SobolevWeakPi n f g :=
  (steinPairPi_iff_smoothSteinPairPi n f g).trans
    (smoothSteinPairPi_iff_sobolevWeakPi n f g)

/-- **The answer, in the shape WALLS W6 asks the question — now in every
    dimension.** Testing the Gaussian integration-by-parts pairing against
    the Hermite products and testing it against `Cc^∞` define the SAME class,
    even though neither test family contains the other. Neither containment
    is formal; both are theorems, and they were proved a day apart by
    completely different arguments — a cutoff and a limit one way, a
    coefficient expansion the other. -/
theorem w6_answered_pi (n : ℕ) :
    (∀ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
        SteinPairPi n f g ↔ SmoothSteinPairPi n f g)
      ∧ (∀ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
        SteinPairPi n f g ↔ SobolevWeakPi n f g) :=
  ⟨steinPairPi_iff_smoothSteinPairPi n, steinPairPi_iff_sobolevWeakPi n⟩

/-! ## 6. What the equality immediately buys

Everything proved about either class is now proved about both. Two
consequences are worth naming, because before today each was known on one
side only and the arrow pointed the wrong way to move it.
-/

/-- `|xᵢ|` is in the TEXTBOOK class. `AbsSteinWitnessPi` proved it a Hermite
    pair; `SteinGeneralPi`'s header recorded that whether it lies in
    `SobolevWeakPi` "is not settled anywhere in the estate, because the one
    arrow runs out of `SobolevWeakPi` rather than into it". The arrow now
    runs both ways. -/
theorem absCoord_sobolevWeakPi (n : ℕ) (i : Fin n) :
    SobolevWeakPi n (AbsSteinWitnessPi.absCoord n i) (AbsSteinWitnessPi.sgnCoord n i) :=
  (steinPairPi_iff_sobolevWeakPi n _ _).mp (AbsSteinWitnessPi.absCoord_steinPairPi n i)

/-- **AND THEREFORE `SteinGeneralPi`'s C¹ CRITERION IS STRICTLY SUFFICIENT**
    — the statement that file explicitly declined to make. `|xᵢ|` is in the
    textbook class and is not a.e. equal to any differentiable function, so
    the containment `{C¹ with L² data} ⊆ SobolevWeakPi` is proper. -/
theorem contDiff_criterion_strict (n : ℕ) (i : Fin n) :
    ∃ (f : (Fin n → ℝ) → ℝ) (g : Fin n → ((Fin n → ℝ) → ℝ)),
      SobolevWeakPi n f g
        ∧ ∀ h : (Fin n → ℝ) → ℝ, Differentiable ℝ h → ¬ (h =ᵐ[gaussPi n] f) :=
  ⟨AbsSteinWitnessPi.absCoord n i, AbsSteinWitnessPi.sgnCoord n i,
    absCoord_sobolevWeakPi n i,
    fun h hh => AbsSteinWitnessPi.absCoord_not_ae_differentiable n i h hh⟩

/-! ## 7. Review round 61 — the ways this could be hollow

**"The equality could be vacuous — both classes could be empty."** They are
not, and by now the catalogue is real: the constants, every coordinate,
every Hermite product with its gradient, `sin xᵢ`, `|xᵢ|`, and every C¹
function with `L²` data. §5 moves two of those across the new arrow.

**"It could be an equality of everything, i.e. both classes could be all of
`L²(γⁿ)`."** `HermitePiProper.exists_memLp_not_steinPairPi` refutes that in
every dimension `n ≥ 1`. **That was already true this morning and this file
adds nothing to it** — `HermitePiProper` reached all three classes through
`W6ConversePi`'s arrow, which runs the direction properness needs. What the
biconditional adds is the OTHER direction, and §6 is where that shows.

**"The proof could secretly assume what it is proving."** The one input
about `ψ` is `testfun_steinPairPi`, which puts `ψ` — not `f` — in the
Hermite-tested class, and gets it from `SteinGeneralPi`'s C¹ criterion,
whose proof runs through Mathlib's integration by parts and
`W6ConversePi`'s cutoff. Neither touches `f` or `g`. The hypothesis
`SteinPairPi n f g` is used exactly once, in `coeffPi_recursion` at the last
step.

**"`integral_stein_testfun_eq` might be doing an integration by parts it
does not admit to."** It does not: it applies `ψ`'s pairing once and
subtracts. The term `∫ ψ·xᵢ·Hpi m` is the same integrand on both sides, and
the three integrability facts it needs are all "continuous times compactly
supported". The genuine analysis is in `SteinGeneralPi` and `W6ConversePi`,
cited rather than repeated.

**"The `mᵢ = 0` terms could be being dropped silently."** They are dropped,
and the reason is proved rather than asserted: `integral_stein_testfun`
carries the factor `mᵢ`, so those terms are literally zero, and `hsupp`
records exactly that before `succAt_injective.tsum_eq` uses it.
-/

end

end SteinSmoothPi
