import LatticeGeneratingFunctional

/-!
# The moments of the lattice field, up to the fourth

`UNLOCK_WATCHLIST`'s OS-axioms item, after `GreenClustering` closed the higher-correlation gap in
the generating-functional sense, left this standing:

> *"no individual higher correlation is written down. Extracting one means differentiating under
> the integral `k` times, and the identity that would come out **IS** Wick's formula. So the
> generating functional clusters; extraction does not follow, and **Wick is still wanted**."*

and its trigger names *"someone wants the Wick MOMENT formula"* first of three.

**This writes down the first four moments of every linear functional of the lattice field, and
hence the first individual higher correlation the estate has: `∫ (ω p)⁴ = 3 · G(p,p)²`.**

## The route, which is not the one the item describes

The item says extraction *"means differentiating under the integral `k` times"*. That is the
textbook route and it is not the one taken. **Mathlib already differentiates under the integral
for exactly this object**: `ProbabilityTheory.iteratedDeriv_mgf_zero` says the `n`-th derivative
of a moment-generating function at `0` is the `n`-th moment, provided `0` is interior to the set
where the exponential is integrable. So the differentiation is done once, in the library, for the
mgf — and what is left is:

* `integrableExpSet_pair` — that set is **all of `ℝ`** here, straight from
  `LatticeGeneratingFunctional.integrable_exp_inner` applied at `t • f`. That lemma was built for
  the growth statement and this is a second use of it;
* `mgf_pair` — and the mgf is `exp (c t² / 2)` with `c = fᵀ G f`, which is
  `generatingFunctional_smul` verbatim;
* §2 — so the moments are the derivatives of `exp (c t² / 2)` at `0`, an elementary calculation
  that never mentions the measure.

**No functional analysis, no dominated convergence written by hand, and no Wick combinatorics.**

## What is proved

* `hasDerivAt_expQuad`, `hasDerivAt_poly_mul_expQuad` — the chain rule and the product rule for
  `P(t) · exp(c t² / 2)`, once, so the four steps below are four lines;
* `deriv_step_zero` … `deriv_step_three` — the four derivatives, with the polynomial prefactors
  `1`, `c t`, `c + c²t²`, `3c²t + c³t³`, `3c² + 6c³t² + c⁴t⁴`;
* `iteratedDeriv_four_expQuad` and the lower three;
* **`moment_one`, `moment_two`, `moment_three`, `moment_four`** — `∫ ⟪f,ω⟫ⁿ` for `n = 1,2,3,4`:
  `0`, `c`, `0`, **`3c²`**. The odd ones vanish and `moment_two` recovers the variance, which is a
  check rather than news: `LatticeGeneratingFunctional` §4 already has the two-point function;
* `inner_single`, `linVar_single`, `moment_three_single`, and **`moment_four_single`** — at
  `f = δₚ`, `∫ (ω p)⁴ = 3 · green G m p p ^ 2`. **An individual fourth correlation, which the estate
  did not have**: `GraphLaplacian.twoPoint` stops at the second moment and nothing stood above it;
* `moment_four_single_pos` — and it is not zero, at every nonzero mass, from
  `GraphLaplacian.twoPoint_diag_pos`. An identity whose right-hand side could vanish identically
  would be worth much less, so it is checked rather than assumed.

## What this is NOT, and the item does not move

**It is not Isserlis.** Isserlis is the whole 4-index statement
`E[ωₚ ω_q ω_r ω_s] = G_{pq}G_{rs} + G_{pr}G_{qs} + G_{ps}G_{qr}`, and what is here is its
**diagonal** — the quartic form `f ↦ E[⟪f,ω⟫⁴]`, plus the one index pattern
(`p,p,p,p`) that reads off it directly. Recovering the full symmetric 4-linear form from the
quartic is **polarisation**, and ~~polarisation of a quartic is sixteen terms, not four~~. It is not
done here and nothing below should be read as if it were.

*AMENDED 16 AUGUST 2026 (`ERRATUM 181`). The struck clause is withdrawn. Sixteen is the count for
the ONE-SHOT polarisation, the alternating sum over the subsets of `{a,b,c,d}`; polarising **one
slot at a time** costs two steps of two terms, because `(x+y)² − (x−y)² = 4xy` leaves the rest of
the integrand alone. `LatticeIsserlisFour.isserlis_four` is those two steps. **What is NOT
withdrawn is the sentence around it**: Isserlis is still not proved in THIS file, and the rest of
this paragraph stands.*

**And OS4 does not move.** The watchlist lists OS4's two remaining pieces as the infinite-volume
limit and the continuum; neither is touched, and this file is finite-volume throughout. What moves
is one clause of one trigger — *"someone wants the Wick moment formula"* — and it moves partly:
the fourth moment exists now, the general one does not.

**No published tag moves**, and nothing in `GreenClustering` or `LatticeGeneratingFunctional` is
restated.
-/

namespace LatticeMoments

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian LatticeGeneratingFunctional

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The variance of a linear functional -/

/-- The variance of `⟪f, ·⟫` under the lattice field: `fᵀ G f`, with `G` the Green function.
Named because it appears in every statement below; `LatticeGeneratingFunctional` writes it out. -/
noncomputable def linVar (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)
    (f : EuclideanSpace ℝ V) : ℝ :=
  f.ofLp ⬝ᵥ green G m *ᵥ f.ofLp

/-- **THE MOMENT-GENERATING FUNCTION OF `⟪f, ·⟫`.** This is `generatingFunctional_smul` with
`ProbabilityTheory.mgf` unfolded — the estate had the integral and not the name, and the name is
what Mathlib's differentiation lemmas are stated for. -/
theorem mgf_pair (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    mgf (fun ω => (inner ℝ f ω : ℝ)) (gaussianField G m)
      = fun t => Real.exp (linVar G m f * t ^ 2 / 2) := by
  funext t
  rw [mgf]
  simpa [linVar] using generatingFunctional_smul (G := G) hm f t

/-- **AND EVERY REAL `t` IS IN THE INTEGRABLE-EXPONENTIAL SET**, because `t • f` is a test function
too. This is the hypothesis Mathlib's `iteratedDeriv_mgf_zero` needs, and
`LatticeGeneratingFunctional.integrable_exp_inner` supplies it with one rescaling. -/
theorem integrableExpSet_pair (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    integrableExpSet (fun ω => (inner ℝ f ω : ℝ)) (gaussianField G m) = Set.univ := by
  ext t
  simp only [integrableExpSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  refine (integrable_exp_inner (G := G) hm (t • f)).congr
    (Filter.Eventually.of_forall fun ω => ?_)
  simp [real_inner_smul_left]

/-- Hence `0` is interior to it. -/
theorem zero_mem_interior_integrableExpSet (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    (0 : ℝ) ∈ interior (integrableExpSet (fun ω => (inner ℝ f ω : ℝ)) (gaussianField G m)) := by
  rw [integrableExpSet_pair hm f]
  simp

/-! ## 2. The derivatives of `exp (c t² / 2)`

Everything here is calculus on one real variable. No measure appears. -/

/-- The chain rule for `exp (c t² / 2)`. -/
theorem hasDerivAt_expQuad (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (c * s ^ 2 / 2)) (c * t * Real.exp (c * t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s ^ 2 / 2) (c * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul c).div_const 2
    convert this using 1
    ring
  have := h1.exp
  convert this using 1
  ring

/-- The product rule with a polynomial prefactor: differentiating `P(t)·exp(c t²/2)` replaces `P`
by `P' + P·c t`. Every derivative below is one application of this. -/
theorem hasDerivAt_poly_mul_expQuad {P P' : ℝ → ℝ} {t : ℝ} (c : ℝ) (hP : HasDerivAt P (P' t) t) :
    HasDerivAt (fun s => P s * Real.exp (c * s ^ 2 / 2))
      ((P' t + P t * (c * t)) * Real.exp (c * t ^ 2 / 2)) t := by
  have h := hP.mul (hasDerivAt_expQuad c t)
  convert h using 1
  ring

theorem deriv_step_zero (c : ℝ) :
    deriv (fun s : ℝ => Real.exp (c * s ^ 2 / 2))
      = fun t => (c * t) * Real.exp (c * t ^ 2 / 2) :=
  funext fun t => (hasDerivAt_expQuad c t).deriv

theorem deriv_step_one (c : ℝ) :
    deriv (fun s : ℝ => (c * s) * Real.exp (c * s ^ 2 / 2))
      = fun t => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2) := by
  funext t
  have hP : HasDerivAt (fun s : ℝ => c * s) c t := by simpa using (hasDerivAt_id t).const_mul c
  rw [(hasDerivAt_poly_mul_expQuad (P' := fun _ => c) c hP).deriv]
  ring

theorem deriv_step_two (c : ℝ) :
    deriv (fun s : ℝ => (c + c ^ 2 * s ^ 2) * Real.exp (c * s ^ 2 / 2))
      = fun t => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2) := by
  funext t
  have hP : HasDerivAt (fun s : ℝ => c + c ^ 2 * s ^ 2) (2 * c ^ 2 * t) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_add c
    convert this using 1
    ring
  rw [(hasDerivAt_poly_mul_expQuad (P' := fun t => 2 * c ^ 2 * t) c hP).deriv]
  ring

theorem deriv_step_three (c : ℝ) :
    deriv (fun s : ℝ => (3 * c ^ 2 * s + c ^ 3 * s ^ 3) * Real.exp (c * s ^ 2 / 2))
      = fun t => (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2) := by
  funext t
  have hP : HasDerivAt (fun s : ℝ => 3 * c ^ 2 * s + c ^ 3 * s ^ 3)
      (3 * c ^ 2 + 3 * c ^ 3 * t ^ 2) t := by
    have h1 : HasDerivAt (fun s : ℝ => 3 * c ^ 2 * s) (3 * c ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul (3 * c ^ 2)
    have h2 : HasDerivAt (fun s : ℝ => c ^ 3 * s ^ 3) (3 * c ^ 3 * t ^ 2) t := by
      have := (hasDerivAt_pow 3 t).const_mul (c ^ 3)
      convert this using 1
      ring
    have := h1.add h2
    convert this using 1
  rw [(hasDerivAt_poly_mul_expQuad (P' := fun t => 3 * c ^ 2 + 3 * c ^ 3 * t ^ 2) c hP).deriv]
  ring

/-- **THE FOURTH DERIVATIVE OF `exp (c t² / 2)` AT `0` IS `3c²`** — and the three below it are
`0`, `c`, `0`. The `3` is the whole content of the fourth-order Wick identity. -/
theorem iteratedDeriv_expQuad (c : ℝ) :
    iteratedDeriv 1 (fun s : ℝ => Real.exp (c * s ^ 2 / 2)) 0 = 0
      ∧ iteratedDeriv 2 (fun s : ℝ => Real.exp (c * s ^ 2 / 2)) 0 = c
      ∧ iteratedDeriv 3 (fun s : ℝ => Real.exp (c * s ^ 2 / 2)) 0 = 0
      ∧ iteratedDeriv 4 (fun s : ℝ => Real.exp (c * s ^ 2 / 2)) 0 = 3 * c ^ 2 := by
  have h1 : iteratedDeriv 1 (fun s : ℝ => Real.exp (c * s ^ 2 / 2))
      = fun t => (c * t) * Real.exp (c * t ^ 2 / 2) := by
    rw [iteratedDeriv_one, deriv_step_zero]
  have h2 : iteratedDeriv 2 (fun s : ℝ => Real.exp (c * s ^ 2 / 2))
      = fun t => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, h1, deriv_step_one]
  have h3 : iteratedDeriv 3 (fun s : ℝ => Real.exp (c * s ^ 2 / 2))
      = fun t => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, h2, deriv_step_two]
  have h4 : iteratedDeriv 4 (fun s : ℝ => Real.exp (c * s ^ 2 / 2))
      = fun t => (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2) := by
    rw [iteratedDeriv_succ, h3, deriv_step_three]
  refine ⟨by rw [h1]; simp, by rw [h2]; simp, by rw [h3]; simp, by rw [h4]; simp⟩

/-! ## 3. The moments -/

/-- The `n`-th moment of `⟪f, ·⟫` is the `n`-th derivative of `exp (c t² / 2)` at `0`. -/
theorem moment_eq_iteratedDeriv (hm : m ≠ 0) (f : EuclideanSpace ℝ V) (n : ℕ) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ n ∂(gaussianField G m)
      = iteratedDeriv n (fun s : ℝ => Real.exp (linVar G m f * s ^ 2 / 2)) 0 := by
  rw [← mgf_pair hm f, iteratedDeriv_mgf_zero (zero_mem_interior_integrableExpSet hm f) n]
  rfl

/-- **THE FIRST MOMENT VANISHES** — the field is centred. -/
theorem moment_one (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ∂(gaussianField G m) = 0 := by
  have h := moment_eq_iteratedDeriv (G := G) hm f 1
  simpa using h.trans (iteratedDeriv_expQuad (linVar G m f)).1

/-- **THE SECOND MOMENT IS THE VARIANCE.** A check, not news: `LatticeGeneratingFunctional` §4
already states the two-point function. It is here because a moment calculation that got `n = 2`
wrong would be believed at `n = 4`. -/
theorem moment_two (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m) = linVar G m f :=
  (moment_eq_iteratedDeriv (G := G) hm f 2).trans (iteratedDeriv_expQuad (linVar G m f)).2.1

/-- **THE THIRD MOMENT VANISHES.** -/
theorem moment_three (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 3 ∂(gaussianField G m) = 0 :=
  (moment_eq_iteratedDeriv (G := G) hm f 3).trans (iteratedDeriv_expQuad (linVar G m f)).2.2.1

/-- **THE FOURTH MOMENT IS `3` TIMES THE SQUARE OF THE VARIANCE.** This is the fourth-order Wick
identity in its smeared form, for the estate's lattice field, at every finite graph and every
nonzero mass.

It is **not** Isserlis — see the file header. Isserlis is the 4-index statement and this is its
diagonal. -/
theorem moment_four (hm : m ≠ 0) (f : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 4 ∂(gaussianField G m) = 3 * (linVar G m f) ^ 2 :=
  (moment_eq_iteratedDeriv (G := G) hm f 4).trans (iteratedDeriv_expQuad (linVar G m f)).2.2.2

/-! ## 4. One site: an individual higher correlation

The moments above are of a smeared field. Taking `f = δₚ` turns them into moments of the field AT A
SITE — which is an individual correlation function, the thing the watchlist item says the estate
does not have. -/

/-- `⟪δₚ, ω⟫ = ω p`. -/
theorem inner_single (p : V) (ω : EuclideanSpace ℝ V) :
    (inner ℝ (EuclideanSpace.single p (1 : ℝ)) ω : ℝ) = ω p := by
  simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) p (1 : ℝ) ω

/-- And the variance of `⟪δₚ, ·⟫` is the Green function on the diagonal. -/
theorem linVar_single (p : V) :
    linVar G m (EuclideanSpace.single p (1 : ℝ)) = green G m p p := by
  simp [linVar]

/-- **THE THIRD MOMENT AT A SITE VANISHES.** -/
theorem moment_three_single (hm : m ≠ 0) (p : V) :
    ∫ ω, (ω p) ^ 3 ∂(gaussianField G m) = 0 :=
  Eq.trans
    (integral_congr_ae (Filter.Eventually.of_forall fun _ => by simp only [inner_single]))
    (moment_three (G := G) hm (EuclideanSpace.single p (1 : ℝ)))

/-- **`∫ (ω p)⁴ = 3 · G(p,p)²`.**

`GraphLaplacian.twoPoint` has had `∫ ω p · ω q = green G m p q` since the field was defined. **This
is the next one up, and the estate had nothing above the second moment.** The watchlist's OS-axioms
item says *"no individual higher correlation is written down"*; this is one.

**It is one index pattern, not Isserlis** — see the file header. -/
theorem moment_four_single (hm : m ≠ 0) (p : V) :
    ∫ ω, (ω p) ^ 4 ∂(gaussianField G m) = 3 * (green G m p p) ^ 2 := by
  have h := moment_four (G := G) hm (EuclideanSpace.single p (1 : ℝ))
  rw [linVar_single] at h
  exact Eq.trans
    (integral_congr_ae (Filter.Eventually.of_forall fun _ => by simp only [inner_single])) h

/-- **AND IT IS NOT ZERO**, at every nonzero mass — `green G m p p > 0` is
`GraphLaplacian.twoPoint_diag_pos` read through `twoPoint`. A moment identity whose right-hand side
could vanish identically would be worth much less. -/
theorem moment_four_single_pos (hm : m ≠ 0) (p : V) :
    0 < ∫ ω, (ω p) ^ 4 ∂(gaussianField G m) := by
  rw [moment_four_single hm p]
  have hpos : 0 < green G m p p := by
    have := GraphLaplacian.twoPoint_diag_pos (G := G) hm p
    rwa [GraphLaplacian.twoPoint G hm p p] at this
  positivity

end LatticeMoments
