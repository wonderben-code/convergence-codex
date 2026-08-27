import LatticeSteinTwo

/-!
# The rung majorant at every order, written once instead of doubled by hand

`LatticeSteinTwo` derives a ladder whose rung `k` is

```
T_k(a₁,…,a_k; f) = ∫ ∏ᵢ⟪aᵢ,ω⟫·exp⟪f,ω⟫ dμ,
```

each rung one differentiation of the one below it, and `T_k(·;0)` is general-order Isserlis.
That file builds rungs 2 and 3 and states that the general `k` is **derived and not costed**
(`ERRATUM 194`). This file costs one half of it, and the number is smaller than it looked.

## What actually stands in the way, stated as a size

Differentiating rung `k` under the integral sign needs a dominating function for

```
ω ↦ (∏ᵢ⟪aᵢ,ω⟫)·⟪c,ω⟫·exp(⟪f,ω⟫ + s⟪c,ω⟫),   uniformly in |s| ≤ 1,
```

and the two rungs that exist supply it by **writing the majorant out as a literal**:
`deriv_bound_two` has six terms and `deriv_bound_three` has twelve, each an `exp` of an affine
function with an independent sign on every linear factor. That is `3·2ᵏ⁻¹` terms at rung `k` —
six at rung 2 and twelve at rung 3, as written, then twenty-four at rung 4 and ninety-six at
rung 6. **And rung 6 at `f = 0` is exactly the first open case of
`WickPairings.IsserlisGeneral`.** `integrable_deriv_bound_three` is thirty lines of
`Integrable.add` for twelve terms; the same proof at rung 6 is a two-hundred-line term nobody
should write and nobody could read.

**The doubling is in the notation and not in the mathematics.** `∏ᵢ|yᵢ| ≤ ∏ᵢ(e^{yᵢ}+e^{−yᵢ})` is
one application of `Finset.prod_le_prod`, and the product on the right is integrable against this
field by **induction on the number of factors** — each step splits one factor and shifts the test
function by `±aᵢ`, which is a case the induction hypothesis already covers. Expanding it into
`2ᵏ` summands, which is what writing the literal does, is what makes the object grow.

## What is proved, and what is not

* `prod_abs_le_prod_cosh`, `norm_prod_mul_exp_le` — the majorant at **every** number of linear
  factors, one lemma;
* `integrable_prod_cosh_mul_exp` — and it is integrable at every order, by induction and never
  by expansion;
* `integrable_rung_majorant`, `norm_rung_le` — the **domination pair**, at every rung, in this
  estate's own notation. `hasDerivAt_integral_of_dominated_loc_of_deriv_le` asks for six
  hypotheses and these are two of them; they are named here because they are the two whose
  *statements* grow with the order, which is the thing that was making rungs expensive. The
  other four — measurability of the family and of its derivative, the pointwise `HasDerivAt`,
  and integrability at the base point — do not turn into literals, and the last of them is
  §4 below;
* `integrable_prod_inner_mul_exp`, `integrable_prod_inner` — **the rung's own integrand is
  integrable at every order**, so `T_k` and `IsserlisGeneral`'s left-hand side are genuine
  integrals and not Mathlib's junk value (see below);
* `deriv_bound_two_of_generic`, `deriv_bound_three_of_generic` — the two hand-written majorants
  re-derived from the generic one, with `prod_cosh_one_eq`/`prod_cosh_two_eq` showing the bounds
  are **equal** and not merely comparable. A general lemma that were weaker than the special
  cases it claims to replace would be a loss dressed as a gain, so the equality is proved rather
  than asserted.

## And a thing the review found, which is worth more than the majorant

`WickPairings.IsserlisGeneral G m k` is stated as an equation whose left side is
`∫ ω, ∏ᵢ⟪fᵢ,ω⟫ ∂μ`, and **nothing in this estate said that integrand is integrable.** Mathlib's
Bochner integral of a non-integrable function is `0` by convention, so at every `k` where the
statement is not yet proved, it was not known to be a claim about an integral rather than a
claim about a junk value. The sharpest case is `LatticeOddVanishing.integral_prod_odd_eq_zero`:
its proof is that the measure is invariant under `ω ↦ −ω` and the integrand is odd, so the
integral equals its own negation — **an argument that goes through unchanged when the integral
is `0` because the convention says so.** That proof was and remains correct; what it did not
establish is that it was talking about anything.

`integrable_prod_inner` settles it at every order, and the majorant above is what settles it:
`‖∏ᵢ⟪aᵢ,ω⟫‖ ≤ ∏ᵢ(e^{⟪aᵢ,ω⟫}+e^{−⟪aᵢ,ω⟫})`, whose integrability is §3. So the odd vanishing, the
`IsserlisGeneral` statement, and every rung `T_k` are now known to be about genuine integrals.
This is recorded as `ERRATUM 295`.

**THIS DOES NOT PROVE THE LADDER.** It removes the analytic half of one rung's cost at every
order at once. What remains for rung `k+1` is the *closed* reading — the derivative of a
polynomial in `s` times `exp` of a quadratic in `s`, whose value is a sum over the partial
pairings that `Involutions` supplies — and that half is combinatorial, is untouched here, and
is still not costed. The honest summary is: **of the two things every rung needs, one is now
paid for once and the other is still paid per rung.**
-/

namespace LatticeSteinMajorant

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeSteinIdentity LatticeSteinTwo

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The pointwise bound, at every number of linear factors -/

/-- `∏|yᵢ| ≤ ∏(e^{yᵢ} + e^{−yᵢ})`, one application of `Finset.prod_le_prod` to
`abs_le_exp_add_exp_neg`. The right-hand side is a **product**, and stays a product: the `2ⁿ`
summands appear only if one insists on expanding it. -/
theorem prod_abs_le_prod_cosh {n : ℕ} (y : Fin n → ℝ) :
    ∏ i, |y i| ≤ ∏ i, (Real.exp (y i) + Real.exp (-(y i))) :=
  Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => abs_le_exp_add_exp_neg _)

/-- **THE MAJORANT AT EVERY ORDER.** `deriv_bound` handles the factor that also sits in the
exponent; every other linear factor is absorbed by `prod_abs_le_prod_cosh`. The bound does not
mention `s`, which is what dominated convergence needs. -/
theorem norm_prod_mul_exp_le {n : ℕ} (y : Fin n → ℝ) (x z s : ℝ) (hs : |s| ≤ 1) :
    ‖(∏ i, y i) * z * Real.exp (x + s * z)‖
      ≤ (∏ i, (Real.exp (y i) + Real.exp (-(y i))))
        * (Real.exp (x + 2 * z) + 2 * Real.exp x + Real.exp (x - 2 * z)) := by
  have hz := deriv_bound x z s hs
  have hy := prod_abs_le_prod_cosh y
  have hregroup : ‖(∏ i, y i) * z * Real.exp (x + s * z)‖
      = (∏ i, |y i|) * ‖z * Real.exp (x + s * z)‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, mul_assoc, abs_mul, Finset.abs_prod]
  rw [hregroup]
  exact mul_le_mul hy hz (norm_nonneg _) (by positivity)

/-! ## 2. The two hand-written majorants are this one, and are not weaker -/

/-- At one linear factor the generic bound **equals** `deriv_bound_two`'s six terms. -/
theorem prod_cosh_one_eq (x y z : ℝ) :
    (∏ i : Fin 1, (Real.exp (![y] i) + Real.exp (-(![y] i))))
        * (Real.exp (x + 2 * z) + 2 * Real.exp x + Real.exp (x - 2 * z))
      = Real.exp (x + y + 2 * z) + 2 * Real.exp (x + y) + Real.exp (x + y - 2 * z)
        + (Real.exp (x - y + 2 * z) + 2 * Real.exp (x - y) + Real.exp (x - y - 2 * z)) := by
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero, Real.exp_add, Real.exp_sub, Real.exp_neg]
  field_simp

/-- And at two linear factors it equals `deriv_bound_three`'s twelve. -/
theorem prod_cosh_two_eq (x y z w : ℝ) :
    (∏ i : Fin 2, (Real.exp (![y, z] i) + Real.exp (-(![y, z] i))))
        * (Real.exp (x + 2 * w) + 2 * Real.exp x + Real.exp (x - 2 * w))
      = Real.exp (x + y + z + 2 * w) + 2 * Real.exp (x + y + z)
          + Real.exp (x + y + z - 2 * w)
        + (Real.exp (x + y - z + 2 * w) + 2 * Real.exp (x + y - z)
          + Real.exp (x + y - z - 2 * w))
      + (Real.exp (x - y + z + 2 * w) + 2 * Real.exp (x - y + z)
          + Real.exp (x - y + z - 2 * w)
        + (Real.exp (x - y - z + 2 * w) + 2 * Real.exp (x - y - z)
          + Real.exp (x - y - z - 2 * w))) := by
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.exp_add, Real.exp_sub, Real.exp_neg]
  field_simp

/-- **`deriv_bound_two` IS THE GENERIC BOUND AT `n = 1`.** -/
theorem deriv_bound_two_of_generic (x y z s : ℝ) (hs : |s| ≤ 1) :
    ‖y * z * Real.exp (x + s * z)‖
      ≤ Real.exp (x + y + 2 * z) + 2 * Real.exp (x + y) + Real.exp (x + y - 2 * z)
        + (Real.exp (x - y + 2 * z) + 2 * Real.exp (x - y) + Real.exp (x - y - 2 * z)) := by
  have h := norm_prod_mul_exp_le ![y] x z s hs
  rw [prod_cosh_one_eq] at h
  simpa using h

/-- **AND `deriv_bound_three` IS THE GENERIC BOUND AT `n = 2`.** -/
theorem deriv_bound_three_of_generic (x y z w s : ℝ) (hs : |s| ≤ 1) :
    ‖y * z * w * Real.exp (x + s * w)‖
      ≤ Real.exp (x + y + z + 2 * w) + 2 * Real.exp (x + y + z)
          + Real.exp (x + y + z - 2 * w)
        + (Real.exp (x + y - z + 2 * w) + 2 * Real.exp (x + y - z)
          + Real.exp (x + y - z - 2 * w))
      + (Real.exp (x - y + z + 2 * w) + 2 * Real.exp (x - y + z)
          + Real.exp (x - y + z - 2 * w)
        + (Real.exp (x - y - z + 2 * w) + 2 * Real.exp (x - y - z)
          + Real.exp (x - y - z - 2 * w))) := by
  have h := norm_prod_mul_exp_le ![y, z] x w s hs
  rw [prod_cosh_two_eq] at h
  simpa [mul_assoc] using h

/-! ## 3. Integrability at every order, by induction and never by expansion -/

/-- **THE PRODUCT MAJORANT IS INTEGRABLE AT EVERY ORDER.** The induction is on the number of
linear factors with the test function `f` general: splitting off one factor turns
`∏ᵢ₌₀ⁿ(e^{⟪aᵢ,ω⟫}+e^{−⟪aᵢ,ω⟫})·e^{⟪f,ω⟫}` into the same expression at `n` factors with `f`
replaced by `f + a₀` and by `f − a₀`, both of which the hypothesis covers. No step ever names
more than two summands, and `2ⁿ` never appears. -/
theorem integrable_prod_cosh_mul_exp (hm : m ≠ 0) (n : ℕ) (a : Fin n → EuclideanSpace ℝ V)
    (f : EuclideanSpace ℝ V) :
    Integrable (fun ω => (∏ i, (Real.exp (inner ℝ (a i) ω : ℝ)
        + Real.exp (-(inner ℝ (a i) ω : ℝ)))) * Real.exp (inner ℝ f ω : ℝ))
      (gaussianField G m) := by
  induction n generalizing f with
  | zero =>
      simpa using LatticeGeneratingFunctional.integrable_exp_inner (G := G) hm f
  | succ n ih =>
      have hsplit : ∀ ω : EuclideanSpace ℝ V,
          (∏ i : Fin n, (Real.exp (inner ℝ (a i.succ) ω : ℝ)
              + Real.exp (-(inner ℝ (a i.succ) ω : ℝ))))
              * Real.exp (inner ℝ (f + a 0) ω : ℝ)
            + (∏ i : Fin n, (Real.exp (inner ℝ (a i.succ) ω : ℝ)
              + Real.exp (-(inner ℝ (a i.succ) ω : ℝ))))
              * Real.exp (inner ℝ (f + (-(a 0))) ω : ℝ)
          = (∏ i, (Real.exp (inner ℝ (a i) ω : ℝ)
              + Real.exp (-(inner ℝ (a i) ω : ℝ)))) * Real.exp (inner ℝ f ω : ℝ) := by
        intro ω
        rw [Fin.prod_univ_succ]
        simp only [inner_add_left, inner_neg_left, Real.exp_add]
        ring
      exact ((ih (fun i => a i.succ) (f + a 0)).add
        (ih (fun i => a i.succ) (f + (-(a 0))))).congr
          (Filter.Eventually.of_forall hsplit)

/-- **THE RUNG'S MAJORANT, INTEGRABLE AT EVERY ORDER.** Three shifts of the test function, and
the product of `n` factors is carried by the lemma above rather than expanded. -/
theorem integrable_rung_majorant (hm : m ≠ 0) (n : ℕ) (a : Fin n → EuclideanSpace ℝ V)
    (f c : EuclideanSpace ℝ V) :
    Integrable (fun ω => (∏ i, (Real.exp (inner ℝ (a i) ω : ℝ)
        + Real.exp (-(inner ℝ (a i) ω : ℝ))))
        * (Real.exp ((inner ℝ f ω : ℝ) + 2 * (inner ℝ c ω : ℝ))
          + 2 * Real.exp (inner ℝ f ω : ℝ)
          + Real.exp ((inner ℝ f ω : ℝ) - 2 * (inner ℝ c ω : ℝ))))
      (gaussianField G m) := by
  have hp := integrable_prod_cosh_mul_exp (G := G) hm n a (f + (2 : ℝ) • c)
  have hz := integrable_prod_cosh_mul_exp (G := G) hm n a f
  have hn := integrable_prod_cosh_mul_exp (G := G) hm n a (f - (2 : ℝ) • c)
  refine ((hp.add (hz.const_mul 2)).add hn).congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, inner_add_left, inner_sub_left, real_inner_smul_left]
  ring

/-! ## 4. The rung's own integrand is integrable, at every order

Not a step of the ladder but a precondition for the ladder meaning anything: without this, every
`∫ ω, ∏ᵢ⟪aᵢ,ω⟫ · e^{⟪f,ω⟫}` in this development is a symbol that Mathlib evaluates to `0` unless
someone shows otherwise, and nobody had. -/

/-- **THE RUNG'S INTEGRAND IS INTEGRABLE AT EVERY ORDER**, by domination against the same
product majorant. -/
theorem integrable_prod_inner_mul_exp (hm : m ≠ 0) (n : ℕ) (a : Fin n → EuclideanSpace ℝ V)
    (f : EuclideanSpace ℝ V) :
    Integrable (fun ω => (∏ i, (inner ℝ (a i) ω : ℝ)) * Real.exp (inner ℝ f ω : ℝ))
      (gaussianField G m) := by
  refine (integrable_prod_cosh_mul_exp (G := G) hm n a f).mono' ?_ ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (prod_abs_le_prod_cosh _) (Real.exp_pos _).le

/-- **AND THEREFORE `WickPairings.IsserlisGeneral`'s LEFT-HAND SIDE IS A GENUINE INTEGRAL**, at
every order and every choice of test functions — the `f = 0` case of the lemma above. Before
this, `∫ ω, ∏ᵢ⟪fᵢ,ω⟫` was a symbol nothing distinguished from the junk value `0`
(`ERRATUM 295`). -/
theorem integrable_prod_inner (hm : m ≠ 0) (n : ℕ) (a : Fin n → EuclideanSpace ℝ V) :
    Integrable (fun ω => ∏ i, (inner ℝ (a i) ω : ℝ)) (gaussianField G m) := by
  simpa using integrable_prod_inner_mul_exp (G := G) hm n a 0

/-! ## 5. The domination pair, in the field's own notation -/

omit [DecidableEq V] in
/-- **AND THE RUNG'S INTEGRAND IS DOMINATED BY IT, AT EVERY ORDER, UNIFORMLY IN `|s| ≤ 1`.**
This and `integrable_rung_majorant` are exactly the two hypotheses
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` asks for; at `n = 1` and `n = 2` they are what
`LatticeSteinTwo` spells out by hand, and at every larger `n` they are what it would have had to. -/
theorem norm_rung_le {n : ℕ} (a : Fin n → EuclideanSpace ℝ V) (f c : EuclideanSpace ℝ V)
    (s : ℝ) (hs : |s| ≤ 1) (ω : EuclideanSpace ℝ V) :
    ‖(∏ i, (inner ℝ (a i) ω : ℝ)) * (inner ℝ c ω : ℝ)
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ))‖
      ≤ (∏ i, (Real.exp (inner ℝ (a i) ω : ℝ) + Real.exp (-(inner ℝ (a i) ω : ℝ))))
        * (Real.exp ((inner ℝ f ω : ℝ) + 2 * (inner ℝ c ω : ℝ))
          + 2 * Real.exp (inner ℝ f ω : ℝ)
          + Real.exp ((inner ℝ f ω : ℝ) - 2 * (inner ℝ c ω : ℝ))) :=
  norm_prod_mul_exp_le (fun i => (inner ℝ (a i) ω : ℝ)) _ _ s hs

end LatticeSteinMajorant
