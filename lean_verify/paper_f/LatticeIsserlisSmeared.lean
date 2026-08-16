import LatticeIsserlis

/-!
# Isserlis at two test functions, not two sites

`LatticeIsserlis` proved `∫ (ω p)²(ω q)² = G(p,p)G(q,q) + 2G(p,q)²` — Isserlis at the index pattern
`(p,p,q,q)`. Every statement in it is about the field **at a site**.

**The OS axioms are not about sites.** They quantify over test functions, and every one of them —
`OS2Exponential`, `LatticeGeneratingFunctional`, `GreenDecay`'s covariance form — is stated in this
estate for smeared fields `⟪f, ω⟫`. So the site version is a special case of the statement that is
actually wanted, and the restriction to `δₚ` is a hypothesis to remove rather than a feature.

**This removes it.** The whole file is `LatticeIsserlis` with `δₚ, δ_q` replaced by arbitrary
`f, g`, and the proof is the same two-term polarisation — because that polarisation never used
anything about delta functions.

## What is proved

* `dotG` — the smeared Green form `f ᵀ G g`, and `dotG_comm`, from `green_isSymm` through
  `dotProduct_mulVec` and `vecMul_transpose`;
* `linVar_add`, `linVar_sub` — `v(f ± g) = v(f) ± 2·dotG f g + v(g)`. **Bilinearity is the whole
  content**, and it is what the site version was getting for free from three-term expansions of
  `Pi.single`;
* **`smeared_twoPoint`** — `∫ ⟪f,ω⟫⟪g,ω⟫ = dotG f g`. The two-point function of the SMEARED field,
  by polarising `moment_two`. `GraphLaplacian.twoPoint` has the site version and the estate had no
  smeared one;
* **`isserlis_smeared`** — `∫ ⟪f,ω⟫²⟪g,ω⟫² = v(f)·v(g) + 2·(dotG f g)²`;
* **`connected_smeared`** — hence the truncated correlation is `2·(dotG f g)²`, and
  **`connected_smeared_eq_two_mul_sq`** writes it with no Green function at all:
  `2·(∫ ⟪f,ω⟫⟪g,ω⟫)²`;
* `connected_smeared_nonneg`, `connected_smeared_eq_zero_iff`;
* `isserlis_sq_sq_of_smeared` — **the site version recovered as an instance**, which is the check
  that the generalisation is the same theorem and not a different one that happens to typecheck.

## What this is NOT

**It is still the pattern `(f,f,g,g)`.** Isserlis proper is
`E[⟪a,ω⟫⟪b,ω⟫⟪c,ω⟫⟪d,ω⟫] = ⟨a,Gb⟩⟨c,Gd⟩ + ⟨a,Gc⟩⟨b,Gd⟩ + ⟨a,Gd⟩⟨b,Gc⟩` at four arbitrary test
functions, and that is the watchlist sub-trigger. Generalising the *arguments* from sites to test
functions is orthogonal to generalising the *pattern*, and only the first is done here.

*AMENDED 16 AUGUST 2026 (`ERRATUM 181`). This sentence used to call that "~~the fifteen-term
polarisation~~". **Withdrawn**: one slot at a time costs two steps of two terms, and
`LatticeIsserlisFour.isserlis_four` (`4d35d08`) does it. **What is NOT withdrawn is the point of
the paragraph** — the two axes really are orthogonal, and this file moves only the first. What the
sequel showed is that THIS unit was the prerequisite for it: the polarisation substitutes `c + d`
into a slot, and a slot that only accepts `δₚ` cannot receive it.*

**And OS4 does not move.** Finite volume throughout, as before. **No published tag moves.**
-/

namespace LatticeIsserlisSmeared

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian LatticeMoments LatticeIsserlis

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {m : ℝ}

/-! ## 1. The smeared Green form -/

/-- The bilinear form behind `linVar`: `f ᵀ G g`, the Green function smeared against two test
functions. `linVar G m f` is `dotG G m f f`. -/
noncomputable def dotG (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ)
    (f g : EuclideanSpace ℝ V) : ℝ := f.ofLp ⬝ᵥ green G m *ᵥ g.ofLp

theorem linVar_eq_dotG (f : EuclideanSpace ℝ V) : linVar G m f = dotG G m f f := rfl

/-- **IT IS SYMMETRIC**, because the Green function is. This is the only place `green_isSymm` is
used, and everything downstream that looks like a symmetry is this one. -/
theorem dotG_comm (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) : dotG G m f g = dotG G m g f := by
  simp only [dotG]
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, green_isSymm (G := G) hm,
    dotProduct_comm]

/-- **AND BILINEAR**, which is what the site version got for free from `Pi.single`. -/
theorem linVar_add (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    linVar G m (f + g) = linVar G m f + 2 * dotG G m f g + linVar G m g := by
  have hc := dotG_comm (G := G) hm g f
  simp only [linVar, dotG] at *
  simp only [WithLp.ofLp_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add]
  linarith [hc]

theorem linVar_sub (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    linVar G m (f - g) = linVar G m f - 2 * dotG G m f g + linVar G m g := by
  have hc := dotG_comm (G := G) hm g f
  simp only [linVar, dotG] at *
  simp only [WithLp.ofLp_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub]
  linarith [hc]

/-! ## 2. The smeared two-point function -/

/-- **`∫ ⟪f,ω⟫⟪g,ω⟫ = fᵀ G g`.** `GraphLaplacian.twoPoint` is the site version; the estate had no
smeared one. Polarising `LatticeMoments.moment_two` is the whole proof — `⟪f+g,ω⟫² − ⟪f,ω⟫² −
⟪g,ω⟫² = 2⟪f,ω⟫⟪g,ω⟫` pointwise, and the three squares are all integrable. -/
theorem smeared_twoPoint (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) * (inner ℝ g ω : ℝ) ∂(gaussianField G m) = dotG G m f g := by
  have hfg : Integrable (fun ω => (inner ℝ (f + g) ω : ℝ) ^ 2) (gaussianField G m) :=
    integrable_pow_pair (G := G) hm _ 2
  have hf : Integrable (fun ω => (inner ℝ f ω : ℝ) ^ 2) (gaussianField G m) :=
    integrable_pow_pair (G := G) hm _ 2
  have hg : Integrable (fun ω => (inner ℝ g ω : ℝ) ^ 2) (gaussianField G m) :=
    integrable_pow_pair (G := G) hm _ 2
  have hpt : ∀ ω : EuclideanSpace ℝ V,
      (inner ℝ (f + g) ω : ℝ) ^ 2 - ((inner ℝ f ω : ℝ) ^ 2 + (inner ℝ g ω : ℝ) ^ 2)
        = 2 * ((inner ℝ f ω : ℝ) * (inner ℝ g ω : ℝ)) := by
    intro ω
    rw [inner_add_left]
    ring
  have hrest : Integrable
      (fun ω => (inner ℝ f ω : ℝ) ^ 2 + (inner ℝ g ω : ℝ) ^ 2) (gaussianField G m) := hf.add hg
  have hstep := integral_sub hfg hrest
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add hf hg, moment_two hm (f + g), moment_two hm f, moment_two hm g,
    linVar_add hm f g] at hstep
  linarith [hstep]

/-! ## 3. Isserlis at two test functions -/

/-- **`∫ ⟪f,ω⟫²⟪g,ω⟫² = v(f)·v(g) + 2·(fᵀGg)²`.** The same two-term polarisation as
`LatticeIsserlis.isserlis_sq_sq`, which never used anything about delta functions. -/
theorem isserlis_smeared (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    ∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m)
      = linVar G m f * linVar G m g + 2 * (dotG G m f g) ^ 2 := by
  have hA : Integrable (fun ω => (inner ℝ (f + g) ω : ℝ) ^ 4) (gaussianField G m) :=
    integrable_pow_pair (G := G) hm _ 4
  have hB : Integrable (fun ω => (inner ℝ (f - g) ω : ℝ) ^ 4) (gaussianField G m) :=
    integrable_pow_pair (G := G) hm _ 4
  have hC : Integrable (fun ω => (inner ℝ f ω : ℝ) ^ 4) (gaussianField G m) :=
    integrable_pow_pair (G := G) hm _ 4
  have hD : Integrable (fun ω => (inner ℝ g ω : ℝ) ^ 4) (gaussianField G m) :=
    integrable_pow_pair (G := G) hm _ 4
  have hpt : ∀ ω : EuclideanSpace ℝ V,
      ((inner ℝ (f + g) ω : ℝ) ^ 4 + (inner ℝ (f - g) ω : ℝ) ^ 4)
          - (2 * (inner ℝ f ω : ℝ) ^ 4 + 2 * (inner ℝ g ω : ℝ) ^ 4)
        = 12 * ((inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2) := by
    intro ω
    rw [inner_add_left, inner_sub_left]
    ring
  have hsum : Integrable
      (fun ω => (inner ℝ (f + g) ω : ℝ) ^ 4 + (inner ℝ (f - g) ω : ℝ) ^ 4)
      (gaussianField G m) := hA.add hB
  have hrest : Integrable
      (fun ω => 2 * (inner ℝ f ω : ℝ) ^ 4 + 2 * (inner ℝ g ω : ℝ) ^ 4)
      (gaussianField G m) := (hC.const_mul 2).add (hD.const_mul 2)
  have hstep := integral_sub hsum hrest
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
    integral_add hA hB, integral_add (hC.const_mul 2) (hD.const_mul 2),
    integral_const_mul, integral_const_mul,
    moment_four hm (f + g), moment_four hm (f - g), moment_four hm f, moment_four hm g,
    linVar_add hm f g, linVar_sub hm f g] at hstep
  nlinarith [hstep]

/-! ## 4. The connected form -/

/-- **THE SMEARED CONNECTED FOUR-POINT FUNCTION IS `2·(fᵀGg)²`.** The disconnected part cancels
exactly, as at two sites. -/
theorem connected_smeared (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
      = 2 * (dotG G m f g) ^ 2 := by
  rw [isserlis_smeared hm f g, moment_two hm f, moment_two hm g]
  ring

/-- **AND WITH NO GREEN FUNCTION IN THE STATEMENT AT ALL**: it is twice the square of the smeared
two-point function. Both sides are things a test-function-indexed axiom can talk about. -/
theorem connected_smeared_eq_two_mul_sq (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
      = 2 * (∫ ω, (inner ℝ f ω : ℝ) * (inner ℝ g ω : ℝ) ∂(gaussianField G m)) ^ 2 := by
  rw [connected_smeared hm f g, smeared_twoPoint hm f g]

theorem connected_smeared_nonneg (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    0 ≤ (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m)) := by
  rw [connected_smeared hm f g]
  positivity

/-- It vanishes exactly when the two smeared fields are uncorrelated. -/
theorem connected_smeared_eq_zero_iff (hm : m ≠ 0) (f g : EuclideanSpace ℝ V) :
    (∫ ω, (inner ℝ f ω : ℝ) ^ 2 * (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m))
        - (∫ ω, (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField G m))
          * (∫ ω, (inner ℝ g ω : ℝ) ^ 2 ∂(gaussianField G m)) = 0
      ↔ dotG G m f g = 0 := by
  rw [connected_smeared hm f g]
  constructor
  · intro h
    have h2 : (dotG G m f g) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  · intro h; rw [h]; ring

/-! ## 5. The site version, recovered

A generalisation that does not specialise back is a different theorem wearing the same name. This
is the check.

**DELIBERATE DUPLICATE, DECLARED RATHER THAN LEFT FOR A GREP TO FIND (`ERRATUM 176`).** The
theorem below has the *same statement* as `LatticeIsserlis.isserlis_sq_sq`, which is exactly the
shape `ERRATA 173`, `174` and `176` are about. It is kept because the two proofs share no step —
that one expands `Pi.single` into explicit Green entries, this one goes through general bilinearity
and never mentions a basis vector until the last line — so it is a cross-check with content, in the
same sense as `Matrix.trace_eq_sum_roots_charpoly_of_pow` checking against Mathlib's `k = 1` case.
An undeclared duplicate is a defect; a declared one used as a check is not, and the difference is
that this paragraph exists.

**And `LatticeIsserlis.linVar_addSingle` / `linVar_subSingle` are now instances of `linVar_add` /
`linVar_sub` above.** They are not restated here and their file is untouched; the record of which
came first is worth more than the three lines saved. -/

/-- **`LatticeIsserlis.isserlis_sq_sq` IS THIS THEOREM AT `f = δₚ`, `g = δ_q`.** -/
theorem isserlis_sq_sq_of_smeared (hm : m ≠ 0) (p q : V) :
    ∫ ω, (ω p) ^ 2 * (ω q) ^ 2 ∂(gaussianField G m)
      = green G m p p * green G m q q + 2 * (green G m p q) ^ 2 := by
  have h := isserlis_smeared (G := G) hm
    (EuclideanSpace.single p (1 : ℝ)) (EuclideanSpace.single q (1 : ℝ))
  have hd : dotG G m (EuclideanSpace.single p (1 : ℝ)) (EuclideanSpace.single q (1 : ℝ))
      = green G m p q := by
    simp [dotG, Matrix.mulVec_single]
  rw [linVar_single, linVar_single, hd] at h
  exact Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun _ => by
    simp only [inner_single])) h

end LatticeIsserlisSmeared
