import WickPairings

/-!
# The lattice field is symmetric under `ω ↦ −ω`, and every odd correlation vanishes

`LatticeMomentsGeneral.moment_odd` says `∫⟪f,ω⟫^(2k+1) = 0` — one test function, raised to an odd
power — and proves it by iterated differentiation of the generating functional. **That route says
nothing about a product of DISTINCT test functions**, and the estate had nothing that did.

This proves the symmetry the statement really rests on, and gets the general odd case from it:

```
∫ ⟪f₀,ω⟫⟪f₁,ω⟫⋯⟪f_{2n},ω⟫ dμ = 0     for ANY 2n+1 test functions.
```

**And that is exactly `WickPairings.IsserlisGeneral`'s odd half, at every order.** An odd set has
no pairing at all (`Involutions.perfectMatchings_eq_empty_of_odd`), so the sum over pairings is
empty; the theorem below says the integral is too. Where the even case is proved at `n ≤ 2` and on
the diagonal, **the odd case is now proved outright**.

## The route

`gaussianField G m` is `multivariateGaussian 0 (green G m)`, a **centred** Gaussian, so its
characteristic function `exp(⟪t,0⟫i − tᵀGt/2)` is real and even in `t`. Two finite measures with
the same characteristic function are equal (`Measure.ext_of_charFun`), and
`MeasureTheory.charFun_map_smul` at `r = −1` turns the pushforward's characteristic function into
`charFun μ (−t)`. So the measure is invariant under negation, which Mathlib packages as
`Measure.IsNegInvariant`, and `MeasureTheory.integral_neg_eq_self` then does the rest: an integrand
that flips sign under `ω ↦ −ω` integrates to itself and to its negative at once.

**The centredness is load-bearing and is the only hypothesis doing work.** A Gaussian with nonzero
mean is not symmetric and none of this holds for it.

## What is proved

* `gaussianField_map_neg` and the `IsNegInvariant` instance;
* `integral_odd_eq_zero` — any integrand with `F (−ω) = −F ω` integrates to `0` against a
  negation-invariant measure, with no integrability hypothesis, because
  `MeasureTheory.integral_neg_eq_self` needs none (`∫` of a non-integrable function is `0` by
  convention, and the identity holds either way);
* **`integral_prod_odd_eq_zero`** — the general odd correlation;
* `isserlisGeneral_odd` — the same, stated against the empty pairing sum, so it reads as the odd
  half of the general theorem rather than as a separate fact.

## What this is NOT

**It is not the even case**, which is the whole content of Isserlis and is unchanged: still
`n ≤ 2` plus the diagonal, still blocked on Gaussian integration by parts at a product observable.
Finite volume throughout. **No wall moves. No published tag moves.**
-/

namespace LatticeOddVanishing

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlis Involutions WickPairings

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-- **THE FIELD IS SYMMETRIC.** A centred Gaussian's characteristic function is real and even, and
two finite measures with the same characteristic function are equal. -/
theorem gaussianField_map_neg (hm : m ≠ 0) :
    Measure.map (Neg.neg : EuclideanSpace ℝ V → EuclideanSpace ℝ V) (gaussianField G m)
      = gaussianField G m := by
  have hpsd : (green G m).PosSemidef := (green_posDef (G := G) hm).posSemidef
  have hfun : (Neg.neg : EuclideanSpace ℝ V → EuclideanSpace ℝ V)
      = fun x => (-1 : ℝ) • x := by
    funext x; simp
  refine Measure.ext_of_charFun ?_
  funext t
  rw [hfun, charFun_map_smul]
  simp only [gaussianField]
  rw [charFun_multivariateGaussian hpsd, charFun_multivariateGaussian hpsd]
  simp only [neg_one_smul, inner_zero_right]
  have hq : ((-t : EuclideanSpace ℝ V)).ofLp ⬝ᵥ green G m *ᵥ ((-t : EuclideanSpace ℝ V)).ofLp
      = t.ofLp ⬝ᵥ green G m *ᵥ t.ofLp := by
    rw [WithLp.ofLp_neg, Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, neg_neg]
  rw [hq]

instance isNegInvariant_gaussianField (hm : m ≠ 0) :
    (gaussianField G m).IsNegInvariant :=
  ⟨gaussianField_map_neg (G := G) hm⟩

/-- An integrand that flips sign under `ω ↦ −ω` integrates to zero. -/
theorem integral_odd_eq_zero (hm : m ≠ 0) {F : EuclideanSpace ℝ V → ℝ}
    (hF : ∀ ω, F (-ω) = -F ω) : ∫ ω, F ω ∂(gaussianField G m) = 0 := by
  haveI := isNegInvariant_gaussianField (G := G) hm
  have h := integral_neg_eq_self F (gaussianField G m)
  simp only [hF, integral_neg] at h
  linarith

/-- **EVERY ODD CORRELATION VANISHES**, at any number of distinct test functions. -/
theorem integral_prod_odd_eq_zero (hm : m ≠ 0) (n : ℕ)
    (f : Fin (2 * n + 1) → EuclideanSpace ℝ V) :
    ∫ ω, ∏ i, (inner ℝ (f i) ω : ℝ) ∂(gaussianField G m) = 0 := by
  refine integral_odd_eq_zero (G := G) hm (fun ω => ?_)
  have h1 : ∀ i, (inner ℝ (f i) (-ω) : ℝ) = -(inner ℝ (f i) ω : ℝ) := fun i =>
    inner_neg_right (f i) ω
  simp only [h1, Finset.prod_neg, Finset.card_univ, Fintype.card_fin]
  rw [Odd.neg_one_pow ⟨n, by ring⟩]
  ring

/-- **AND THAT IS THE ODD HALF OF `IsserlisGeneral`**, written against the empty pairing sum so it
reads as part of the general theorem rather than beside it. -/
theorem isserlisGeneral_odd (hm : m ≠ 0) (n : ℕ) : IsserlisGeneral G m (2 * n + 1) := by
  intro f
  rw [integral_prod_odd_eq_zero (G := G) hm n]
  have hempty : (Finset.univ : Finset ↑(perfectMatchings (Fin (2 * n + 1)))) = ∅ := by
    rw [Finset.univ_eq_empty_iff]
    refine ⟨fun σ => ?_⟩
    have h := even_card_of_mem_perfectMatchings σ.2
    rw [Fintype.card_fin, Nat.even_iff] at h
    omega
  rw [Finset.sum_congr hempty (fun _ _ => rfl), Finset.sum_empty]

end LatticeOddVanishing
