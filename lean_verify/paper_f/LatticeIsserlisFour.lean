import LatticeIsserlisSmeared

/-!
# Isserlis at four arbitrary test functions

For five consecutive units the `UNLOCK_WATCHLIST` sub-trigger has read *"someone wants Isserlis at
four arbitrary arguments"*, and five consecutive file headers have costed it the same way:

> *"the patterns `(p,p,p,q)` and `(p,q,r,s)` need three and fifteen further polarisation terms"*
> — `LatticeIsserlis`
> *"that is the fifteen-term polarisation the watchlist sub-trigger names"*
> — `LatticeIsserlisSmeared`

**Fifteen is the count for the one-shot polarisation of a quartic**, `24·T(a,b,c,d) =
∑_{∅≠S} (−1)^{4−|S|} Q(σ_S)` over the sixteen subsets. **Nobody has to do it that way.** Polarising
*one slot at a time* is two steps of two terms each, because

    (x + y)² − (x − y)² = 4xy

turns a square into a product without touching the other factor. Two applications take
`LatticeIsserlisSmeared.isserlis_smeared` — the `(f,f,g,g)` pattern — to the general one. **So the
cost was quadratic and it was written down as exponential, five times, by me.** `ERRATUM 181`.

## What is proved

* `integrable_sq_mul_sq`, `integrable_mul_mul_sq`, `integrable_four` — the three integrability
  facts, each dominating onto the previous by an `AM–GM` inequality that `nlinarith` gets from one
  square. **This is the only analysis in the file**; everything else is bilinear algebra;
* `dotG_add_left`, `dotG_sub_left`, `dotG_add_right`, `dotG_sub_right` — bilinearity of the smeared
  Green form in each slot separately;
* **`isserlis_two_one`** — the first polarisation:
  `∫ ⟪a,ω⟫⟪b,ω⟫⟪g,ω⟫² = ⟨a,Gb⟩·⟨g,Gg⟩ + 2·⟨a,Gg⟩⟨b,Gg⟩`, the pattern `(a,b,g,g)`;
* **`isserlis_four`** — the second, and the theorem:
  `∫ ⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫⟪d,ω⟫ = ⟨a,Gb⟩⟨c,Gd⟩ + ⟨a,Gc⟩⟨b,Gd⟩ + ⟨a,Gd⟩⟨b,Gc⟩`. **The sum over the three
  pairings of four points, at four arbitrary test functions. This is Isserlis' theorem.**
* `isserlis_smeared_of_four` — and the `(f,f,g,g)` case recovered from it, which is the check that
  the general statement specialises to the one it was built from.

## What this does and does not close

**It closes the sub-trigger**, which has been the named next step on the OS-axioms item since the
fourth-moment unit. The estate now has Wick's formula at fourth order for its lattice field.

**It does not close the item and OS4 does not move.** OS4's two remaining pieces are, as they have
been throughout, the infinite-volume limit and the continuum; every statement here is at a fixed
finite graph. **And it is fourth order only** — Isserlis at order `2n` is a sum over `(2n−1)!!`
pairings and nothing here touches `n ≥ 3`.

**No published tag moves.**
-/

namespace LatticeIsserlisFour

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian LatticeMoments LatticeIsserlis
open LatticeIsserlisSmeared

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

omit [DecidableEq V] in
/-- The smeared field is continuous in `ω`, which is all the measurability any of the dominations
below needs. -/
theorem continuous_pair (f : EuclideanSpace ℝ V) :
    Continuous (fun ω : EuclideanSpace ℝ V => (inner ℝ f ω : ℝ)) :=
  (innerSL ℝ f).continuous

/-! ## 1. Integrability

Three dominations, each onto the one above. **This is the only analysis in the file.** -/

/-- `x²y² ≤ (x⁴ + y⁴)/2`, from `(x² − y²)² ≥ 0`. -/
theorem integrable_sq_mul_sq (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    Integrable (fun ω => (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2) (gaussianField G m) := by
  have hdom : Integrable
      (fun ω => ((inner ℝ f ω : ℝ) ^ 4 + (inner ℝ g ω : ℝ) ^ 4) / 2) (gaussianField G m) :=
    ((integrable_pow_pair (G := G) hm f 4).add (integrable_pow_pair (G := G) hm g 4)).div_const 2
  have hmeas := Continuous.aestronglyMeasurable
    (μ := gaussianField G m)
    (((continuous_pair f).pow 2).mul ((continuous_pair g).pow 2))
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg ((inner ℝ f ω : ℝ) ^ 2 - (inner ℝ g ω : ℝ) ^ 2)]

/-- `|x y z²| ≤ (x²z² + y²z²)/2`, from `(|x| − |y|)² ≥ 0` multiplied by `z² ≥ 0`. -/
theorem integrable_mul_mul_sq (hm : m ≠ 0) (a b g : EuclideanSpace ℝ V) :
    Integrable
      (fun ω => (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ g ω : ℝ) ^ 2)
      (gaussianField G m) := by
  have hdom : Integrable
      (fun ω => ((inner ℝ a ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2
        + (inner ℝ b ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2) / 2) (gaussianField G m) :=
    ((integrable_sq_mul_sq (G := G) hm a g).add (integrable_sq_mul_sq (G := G) hm b g)).div_const 2
  have hmeas := Continuous.aestronglyMeasurable
    (μ := gaussianField G m)
    (((continuous_pair a).mul (continuous_pair b)).mul ((continuous_pair g).pow 2))
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  rcases abs_cases ((inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ g ω : ℝ) ^ 2)
    with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;>
    nlinarith [sq_nonneg ((inner ℝ a ω : ℝ) - (inner ℝ b ω : ℝ)),
      sq_nonneg ((inner ℝ a ω : ℝ) + (inner ℝ b ω : ℝ)), sq_nonneg (inner ℝ g ω : ℝ),
      sq_nonneg ((inner ℝ g ω : ℝ) ^ 2)]

/-- `|abcd| ≤ (a²c² + b²d²)/2`, from `(|ac| − |bd|)² ≥ 0`. The statement below is not vacuous. -/
theorem integrable_four (hm : m ≠ 0) (a b c d : EuclideanSpace ℝ V) :
    Integrable
      (fun ω => (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ) * (inner ℝ d ω : ℝ))
      (gaussianField G m) := by
  have hdom : Integrable
      (fun ω => ((inner ℝ a ω : ℝ) ^ 2 * (inner ℝ c ω : ℝ) ^ 2
        + (inner ℝ b ω : ℝ) ^ 2 * (inner ℝ d ω : ℝ) ^ 2) / 2) (gaussianField G m) :=
    ((integrable_sq_mul_sq (G := G) hm a c).add (integrable_sq_mul_sq (G := G) hm b d)).div_const 2
  have hmeas := Continuous.aestronglyMeasurable
    (μ := gaussianField G m)
    ((((continuous_pair a).mul (continuous_pair b)).mul (continuous_pair c)).mul
      (continuous_pair d))
  refine Integrable.mono' hdom hmeas (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  rcases abs_cases ((inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ)
      * (inner ℝ d ω : ℝ)) with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h] <;>
    nlinarith [sq_nonneg ((inner ℝ a ω : ℝ) * (inner ℝ c ω : ℝ)
        - (inner ℝ b ω : ℝ) * (inner ℝ d ω : ℝ)),
      sq_nonneg ((inner ℝ a ω : ℝ) * (inner ℝ c ω : ℝ)
        + (inner ℝ b ω : ℝ) * (inner ℝ d ω : ℝ))]

/-! ## 2. Bilinearity of the smeared Green form, in each slot separately -/

theorem dotG_add_left (a b g : EuclideanSpace ℝ V) :
    dotG G m (a + b) g = dotG G m a g + dotG G m b g := by
  simp [dotG, add_dotProduct]

theorem dotG_sub_left (a b g : EuclideanSpace ℝ V) :
    dotG G m (a - b) g = dotG G m a g - dotG G m b g := by
  simp [dotG, sub_dotProduct]

theorem dotG_add_right (a c d : EuclideanSpace ℝ V) :
    dotG G m a (c + d) = dotG G m a c + dotG G m a d := by
  simp [dotG, Matrix.mulVec_add, dotProduct_add]

theorem dotG_sub_right (a c d : EuclideanSpace ℝ V) :
    dotG G m a (c - d) = dotG G m a c - dotG G m a d := by
  simp [dotG, Matrix.mulVec_sub, dotProduct_sub]

/-! ## 3. The first polarisation: one slot opened -/

/-- **`∫ ⟪a,ω⟫⟪b,ω⟫⟪g,ω⟫² = ⟨a,Gb⟩⟨g,Gg⟩ + 2⟨a,Gg⟩⟨b,Gg⟩`.**

Two instances of `isserlis_smeared`, subtracted. `(x+y)² − (x−y)² = 4xy` opens the first slot
without touching the `⟪g,ω⟫²` factor, which is why this costs two terms and not fifteen. -/
theorem isserlis_two_one (hm : m ≠ 0) (a b g : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m)
      = dotG G m a b * linVar G m g + 2 * (dotG G m a g * dotG G m b g) := by
  have hP : Integrable
      (fun ω => (inner ℝ (a + b) ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2) (gaussianField G m) :=
    integrable_sq_mul_sq (G := G) hm _ _
  have hM : Integrable
      (fun ω => (inner ℝ (a - b) ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2) (gaussianField G m) :=
    integrable_sq_mul_sq (G := G) hm _ _
  have hpt : ∀ ω : EuclideanSpace ℝ V,
      (inner ℝ (a + b) ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2
          - (inner ℝ (a - b) ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2
        = 4 * ((inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ g ω : ℝ) ^ 2) := by
    intro ω
    rw [inner_add_left, inner_sub_left]
    ring
  have hstep := integral_sub hP hM
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    isserlis_smeared hm (a + b) g, isserlis_smeared hm (a - b) g,
    linVar_add hm a b, linVar_sub hm a b, dotG_add_left, dotG_sub_left] at hstep
  nlinarith [hstep]

/-! ## 4. The second polarisation, and the theorem -/

/-- **ISSERLIS' THEOREM AT FOURTH ORDER, FOR FOUR ARBITRARY TEST FUNCTIONS.**

`∫ ⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫⟪d,ω⟫ = ⟨a,Gb⟩⟨c,Gd⟩ + ⟨a,Gc⟩⟨b,Gd⟩ + ⟨a,Gd⟩⟨b,Gc⟩` — the sum over the three
ways of pairing four points, each pair contributing its two-point function.

The same trick again, in the second slot: `⟪a,ω⟫⟪b,ω⟫` rides along untouched while
`(c+d)² − (c−d)²` opens `⟪c,ω⟫⟪d,ω⟫`. **Two polarisations, four instances of a theorem that was
already there.** -/
theorem isserlis_four (hm : m ≠ 0) (a b c d : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ) * (inner ℝ d ω : ℝ)
        ∂(gaussianField G m)
      = dotG G m a b * dotG G m c d + dotG G m a c * dotG G m b d
        + dotG G m a d * dotG G m b c := by
  have hP : Integrable
      (fun ω => (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ (c + d) ω : ℝ) ^ 2)
      (gaussianField G m) := integrable_mul_mul_sq (G := G) hm _ _ _
  have hM : Integrable
      (fun ω => (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ (c - d) ω : ℝ) ^ 2)
      (gaussianField G m) := integrable_mul_mul_sq (G := G) hm _ _ _
  have hpt : ∀ ω : EuclideanSpace ℝ V,
      (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ (c + d) ω : ℝ) ^ 2
          - (inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ (c - d) ω : ℝ) ^ 2
        = 4 * ((inner ℝ a ω : ℝ) * (inner ℝ b ω : ℝ) * (inner ℝ c ω : ℝ) * (inner ℝ d ω : ℝ)) := by
    intro ω
    rw [inner_add_left, inner_sub_left]
    ring
  have hstep := integral_sub hP hM
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    isserlis_two_one hm a b (c + d), isserlis_two_one hm a b (c - d),
    linVar_add hm c d, linVar_sub hm c d,
    dotG_add_right, dotG_sub_right, dotG_add_right, dotG_sub_right] at hstep
  nlinarith [hstep]

/-- **AND `isserlis_smeared` IS ITS `(f,f,g,g)` CASE.** A generalisation that does not specialise
back is a different theorem wearing the same name; this is the check. -/
theorem isserlis_smeared_of_four (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m)
      = linVar G m f * linVar G m g + 2 * (dotG G m f g) ^ 2 := by
  have h := isserlis_four (G := G) hm f f g g
  rw [← linVar_eq_dotG, ← linVar_eq_dotG] at h
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) (h.trans ?_)
  · ring
  · ring

end LatticeIsserlisFour
