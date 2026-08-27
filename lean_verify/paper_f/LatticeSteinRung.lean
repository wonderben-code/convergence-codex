import LatticeSteinMajorant

/-!
# The rung step's integral side, at every order

`LatticeSteinTwo` builds its ladder one rung at a time, and each rung's **integral reading** —
that differentiating

```
s ↦ ∫ ∏ᵢ⟪aᵢ,ω⟫·exp(⟪f,ω⟫ + s⟪c,ω⟫) dμ
```

at `s = 0` gains the factor `⟪c,ω⟫` under the integral sign — is written out per rung, because
each rung's dominating function was written out per rung. `LatticeSteinMajorant` made the
majorant one lemma at every order, and this is what that buys: **the integral side of the rung
step, once, at every order.**

## What this is and is not

`hasDerivAt_rung_ray` is `LatticeSteinTwo.hasDerivAt_stein_two_ray` and
`hasDerivAt_stein_three_ray` at arbitrary `n`. **That is proved rather than asserted**:
`hasDerivAt_stein_two_ray_of_rung` and `hasDerivAt_stein_three_ray_of_rung` restate those two
propositions **verbatim** and derive them here, at `n = 1` and `n = 2`. Exhibiting the integrands
as equal would have been weaker — the statements also carry the derivative and the point — so the
whole proposition is re-derived instead.

**IT IS HALF OF A RUNG.** A rung is the integral reading and the **closed** reading equated. The
closed reading at general order is the derivative of a sum over involutions —
`SteinSumRecursion.sum_steinTerm_option` is its recursion, and **differentiating it is not done
here.** So this file does not build a rung at general order; it removes the analytic obstacle to
building one, which is a different claim and the smaller of the two. **Not costed**
(`ERRATUM 194`).

## What is proved

* `integrable_rung_integrand` — the integrand is integrable at every `s` and every order, so the
  function being differentiated is real-valued rather than `0` by convention (`ERRATUM 295`);
* **`hasDerivAt_rung_ray`** — the derivative at `s = 0`, at every order;
* `rung_ray_one_eq`, `rung_ray_two_eq` — the integrand identifications, and
  **`hasDerivAt_stein_two_ray_of_rung`, `hasDerivAt_stein_three_ray_of_rung`** — the two
  hand-written rungs' full propositions, restated verbatim and derived from the general one.
-/

namespace LatticeSteinRung

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeMoments LatticeIsserlis LatticeIsserlisSmeared LatticeIsserlisFour
open LatticeSteinIdentity LatticeSteinMajorant

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. Continuity and integrability of the family -/

omit [DecidableEq V] in
/-- The integrand is continuous in `ω`, at every `s` and every order. -/
theorem continuous_rung_integrand {n : ℕ} (a : Fin n → EuclideanSpace ℝ V)
    (f c : EuclideanSpace ℝ V) (s : ℝ) :
    Continuous (fun ω : EuclideanSpace ℝ V => (∏ i, (inner ℝ (a i) ω : ℝ))
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ))) :=
  (continuous_finset_prod _ fun i _ => LatticeIsserlisFour.continuous_pair (a i)).mul
    (Real.continuous_exp.comp ((LatticeIsserlisFour.continuous_pair f).add
      (continuous_const.mul (LatticeIsserlisFour.continuous_pair c))))

/-- **THE FUNCTION BEING DIFFERENTIATED IS AN INTEGRAL AND NOT A CONVENTION.** At every `s` the
integrand is `LatticeSteinMajorant.integrable_prod_inner_mul_exp` at test function `f + s•c`.
`ERRATUM 295` is why this is stated rather than assumed. -/
theorem integrable_rung_integrand (hm : m ≠ 0) {n : ℕ} (a : Fin n → EuclideanSpace ℝ V)
    (f c : EuclideanSpace ℝ V) (s : ℝ) :
    Integrable (fun ω => (∏ i, (inner ℝ (a i) ω : ℝ))
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ))) (gaussianField G m) := by
  refine (integrable_prod_inner_mul_exp (G := G) hm n a (f + s • c)).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [inner_add_left, real_inner_smul_left]

/-! ## 2. The derivative -/

/-- **THE INTEGRAL READING OF THE RUNG STEP, AT EVERY ORDER.** Differentiating in a new direction
`c` at `s = 0` puts `⟪c,ω⟫` under the integral sign — which is rung `n+1` with the new test
function appended. The domination is `LatticeSteinMajorant.norm_rung_le` and
`integrable_rung_majorant`, both stated once at every order; nothing here grows with `n`. -/
theorem hasDerivAt_rung_ray (hm : m ≠ 0) {n : ℕ} (a : Fin n → EuclideanSpace ℝ V)
    (f c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ))
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) ∂(gaussianField G m))
      (∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) * (inner ℝ c ω : ℝ)
        * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)) 0 := by
  set μ := gaussianField G m with hμ
  set F : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => (∏ i, (inner ℝ (a i) ω : ℝ))
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) with hF
  set F' : ℝ → EuclideanSpace ℝ V → ℝ :=
    fun s ω => (∏ i, (inner ℝ (a i) ω : ℝ)) * ((inner ℝ c ω : ℝ)
      * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ))) with hF'
  have hcont : ∀ s : ℝ, Continuous (F s) := fun s => continuous_rung_integrand a f c s
  have hcont' : ∀ s : ℝ, Continuous (F' s) := fun s =>
    (continuous_finset_prod _ fun i _ => LatticeIsserlisFour.continuous_pair (a i)).mul
      ((LatticeIsserlisFour.continuous_pair c).mul
        (Real.continuous_exp.comp ((LatticeIsserlisFour.continuous_pair f).add
          (continuous_const.mul (LatticeIsserlisFour.continuous_pair c)))))
  have hderiv : ∀ (ω : EuclideanSpace ℝ V) (s : ℝ), HasDerivAt (F · ω) (F' s ω) s := by
    intro ω s
    have hlin : HasDerivAt
        (fun t : ℝ => (inner ℝ f ω : ℝ) + t * (inner ℝ c ω : ℝ)) (inner ℝ c ω : ℝ) s := by
      simpa using ((hasDerivAt_id s).mul_const (inner ℝ c ω : ℝ)).const_add (inner ℝ f ω : ℝ)
    have hp := hlin.exp.const_mul (∏ i, (inner ℝ (a i) ω : ℝ))
    simp only [hF, hF']
    convert hp using 1
    ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (x₀ := (0 : ℝ))
    (bound := fun ω => (∏ i, (Real.exp (inner ℝ (a i) ω : ℝ)
        + Real.exp (-(inner ℝ (a i) ω : ℝ))))
      * (Real.exp ((inner ℝ f ω : ℝ) + 2 * (inner ℝ c ω : ℝ))
        + 2 * Real.exp (inner ℝ f ω : ℝ)
        + Real.exp ((inner ℝ f ω : ℝ) - 2 * (inner ℝ c ω : ℝ))))
    (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds _ one_pos)
    (Filter.Eventually.of_forall fun s => (hcont s).aestronglyMeasurable)
    (integrable_rung_integrand (G := G) hm a f c 0)
    ((hcont' 0).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω s hsm => by
      have hs : |s| ≤ 1 := le_of_lt (by simpa [Real.dist_eq] using hsm)
      simpa [hF', mul_assoc] using norm_rung_le a f c s hs ω)
    (integrable_rung_majorant (G := G) hm n a f c)
    (Filter.Eventually.of_forall fun ω s _ => hderiv ω s)
  have hval : (∫ ω, F' 0 ω ∂μ)
      = ∫ ω, (∏ i, (inner ℝ (a i) ω : ℝ)) * (inner ℝ c ω : ℝ)
          * Real.exp (inner ℝ f ω : ℝ) ∂μ := by
    simp only [hF', zero_mul, add_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  rw [← hval]
  simpa [hF] using hres.2

/-! ## 3. The two hand-written rungs are its cases

`LatticeSteinTwo` states the same derivative at one and two linear factors. Those are `n = 1` and
`n = 2` here, and the integrands are exhibited as equal rather than the relation being asserted. -/

omit [DecidableEq V] in
/-- At one linear factor the integrand is `hasDerivAt_stein_two_ray`'s. -/
theorem rung_ray_one_eq (a : EuclideanSpace ℝ V) (ω : EuclideanSpace ℝ V) :
    (∏ i, (inner ℝ (![a] i) ω : ℝ)) = (inner ℝ a ω : ℝ) := by
  simp

omit [DecidableEq V] in
/-- And at two, `hasDerivAt_stein_three_ray`'s. -/
theorem rung_ray_two_eq (a b : EuclideanSpace ℝ V) (ω : EuclideanSpace ℝ V) :
    (∏ i, (inner ℝ (![a, b] i) ω : ℝ)) = (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) := by
  simp [Fin.prod_univ_two]

/-- **`LatticeSteinTwo.hasDerivAt_stein_two_ray`, RESTATED VERBATIM AND DERIVED HERE** as the case
`n = 1`. A weaker check would compare the integrands; this compares the propositions. -/
theorem hasDerivAt_stein_two_ray_of_rung (hm : m ≠ 0) (f a b : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ)
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ b ω : ℝ)) ∂(gaussianField G m))
      (∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)) 0 := by
  simpa using hasDerivAt_rung_ray (G := G) hm ![a] f b

/-- And **`LatticeSteinTwo.hasDerivAt_stein_three_ray`** as the case `n = 2`. -/
theorem hasDerivAt_stein_three_ray_of_rung (hm : m ≠ 0) (f a b c : EuclideanSpace ℝ V) :
    HasDerivAt (fun s : ℝ => ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ)
        * Real.exp ((inner ℝ f ω : ℝ) + s * (inner ℝ c ω : ℝ)) ∂(gaussianField G m))
      (∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
        * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField G m)) 0 := by
  simpa [Fin.prod_univ_two] using hasDerivAt_rung_ray (G := G) hm ![a, b] f c

end LatticeSteinRung
