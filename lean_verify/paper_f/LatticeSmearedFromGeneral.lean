import LatticeCorrelatedPoincare
import LatticeIsserlisSmeared
import LatticePoincare
import LatticeGeneratingFunctional
import DifferentiableNotC1
import LatticeFieldDifferentiable

/-!
# The two Poincaré lines of this estate agree on their overlap

The estate grew **two** Poincaré inequalities for `gaussianField K m`, weeks apart and by different
routes:

* `LatticePoincare.poincare_smeared` — for observables of **one smearing**, `F(⟪f,ω⟫)`, with
  constant `fᵀGf`, hypotheses *everywhere differentiable + polynomial growth*;
* `LatticeCorrelatedPoincare.poincare_correlated_general` — for observables of **all coordinates**,
  with constant `∂Φ ⬝ᵥ G ∂Φ`, hypotheses *`C¹` + two `L²` conditions*.

The second is presented as the generalisation of the first, and every reader — including me, until
this file — will assume it subsumes it. **It does not, and that is the first thing proved here by
being stated precisely rather than assumed.**

## The hypothesis classes are INCOMPARABLE, which nothing recorded

`poincare_smeared` asks for `HasDerivAt F (F' x) x` at every `x` and **never asks `F'` to be
continuous**. `poincare_correlated_general` asks for `ContDiff ℝ 1`. So:

* a differentiable `F` with discontinuous derivative and polynomial growth is inside
  `poincare_smeared` and **outside** `poincare_correlated_general`. **PROVED, in §6** —
  `poincare_smeared_reaches_wig` and `not_contDiff_wig_smear`. The witness is `x² sin(1/x)`
  extended by `0`, differentiable everywhere with a derivative discontinuous at the origin and
  bounded by `2|x| + 1`; it is **built in `DifferentiableNotC1`**, which has no lattice imports
  and no measure in it. *This bullet read "**STILL ASSERTED, NOT PROVED** … it is not built here"
  until `30a5193`, quoted per `ERRATUM 94` rather than deleted, because that label is the reason
  the witness got built;*
* `Real.exp` is inside `poincare_correlated_general` and **outside** `poincare_smeared`, which
  cannot state it. **PROVED, in §5** — `exp_not_polyGrowth` and `poincare_reaches_exp`;
* and an observable of two smearings is inside `poincare_correlated_general` and outside
  `poincare_smeared`, for the trivial reason that the latter has no room to state it.

Neither theorem implies the other — **both directions now exhibited by witnesses rather than
asserted**, and `separation_both_directions` states the pair as one proposition. **No file in the
estate claimed otherwise** — checked by reading all three headers — so this is an unrecorded fact
rather than an erratum. But "the general one covers the special one" is exactly the sort of thing a
later reader assumes, and it is false.

**The `wig` direction is about the OBSERVABLE, not merely the profile.** `wig` failing `C¹` would
not by itself stop `ω ↦ wig ⟪f,ω⟫` from being `C¹` — compositions can be smoother than what they
compose. §6 proves the observable itself fails, for every `f ≠ 0`, by restricting to a line on
which the smearing is the identity. At `f = 0` the observable is constant and the separation
correctly does not hold, which is why that hypothesis is there.

**AND THE SEPARATION IS BETWEEN HYPOTHESIS CLASSES AND NOT BETWEEN CONCLUSIONS, WHICH §7 MAKES
PRECISE RATHER THAN MERELY CAREFUL.** §6 said only that `poincare_correlated_general`'s hypothesis
fails at `wig ⟪f,·⟫`, and added that nothing ruled out the inequality holding by another route.
`LatticeFieldDifferentiable` has since built that route, so **`poincare_reaches_wigSmear`** proves
the inequality **does** hold there. *A caveat that can be turned into a theorem should be, and this
one was written knowing the route was missing rather than knowing it was absent.*

**AND "INCOMPARABLE" IS TRUE BUT VAGUER THAN IT NEEDS TO BE, WHICH §4 FIXES.** The general
theorem's two `L²` side conditions are **implied** by `poincare_smeared`'s own polynomial-growth
bounds (`LatticePoincare.memLp_comp_pair`). Feeding them in leaves a statement whose hypotheses are
`poincare_smeared`'s **verbatim** plus `ContDiff ℝ 1 F` — so on observables of a single smearing
**the entire difference between the estate's two Poincaré theorems is the continuity of the
derivative**, one named condition. The incomparability is not withdrawn: the general theorem still
reaches several smearings, and still reaches `C¹` functions of super-polynomial growth that remain
`L²`, which `poincare_smeared` excludes outright.

## What IS true, and is a theorem here

On the overlap — `C¹` observables of one smearing — the two agree, and the smeared statement comes
out of the general one with the constant it should have:

**`poincare_smeared_of_correlated`**: `Var F(⟪f,ω⟫) ≤ (fᵀGf) · ∫ F′(⟪f,ω⟫)²`, derived from
`poincare_correlated_general`.

The content is one chain rule and one scalar extraction: `∂ⱼ[F(⟪f,ω⟫)] = F′(⟪f,ω⟫)·fⱼ`, so the
gradient tuple is `F′` times the fixed vector `f`, and the quadratic form pulls the scalar out
squared — leaving exactly `linVar K m f`. **The propagator never has to be touched.**

**`poincare_smeared_of_correlated_polyGrowth`** is the same conclusion with the `L²` conditions
discharged from polynomial growth, so its hypothesis list can be compared with
`poincare_smeared`'s line by line.

## What this is NOT

**IT NOW DOES REPROVE `poincare_smeared`, AND §8 IS WHERE.** This paragraph read:

> **It does not reprove `poincare_smeared`**, whose hypotheses this cannot reach (see above). It
> proves the same *conclusion* under the *general* theorem's hypotheses, which is what "the two
> lines agree" can honestly mean.

That was true when written and is quoted rather than deleted (`ERRATUM 94`). The hypotheses were
unreachable because the correlated line demanded `ContDiff ℝ 1`;
`LatticeFieldDifferentiable.poincare_correlated_differentiable` removed that demand, and
**`poincare_smeared_of_correlated_general`** now takes `hm`, `f`, `hderiv`, `hb`, `hb'` and nothing
else. A machine-checked `example` confirms the result **is** `poincare_smeared`'s statement rather
than something resembling it.

**§5 and §6 are untouched by this.** `poincare_smeared` and `poincare_correlated_general` — the
`C¹` theorem — remain incomparable, with a witness each way. What §8 changes is a claim about *this
file's* reach, closed by later units of the same campaign rather than by a better proof of the same
thing.

**Nothing here is new mathematics.** It is a consistency link between two existing results, of the
kind that is invisible to every automated check in this project — both files build, both are
correct, and nothing asks whether they fit together.

**`OS4` does not move, no spectral gap is claimed, and no published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LatticeSmearedFromGeneral

open MeasureTheory ProbabilityTheory Matrix GraphLaplacian
open LatticeCorrelatedPoincare LatticeIsserlisSmeared LatticeMoments
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : SimpleGraph W} [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The chain rule through one smearing -/

omit [DecidableEq W] in
/-- `ω ↦ F ⟪f,ω⟫` is `C¹` when `F` is: it is `F` after a continuous linear map. -/
theorem contDiff_smear {f : EuclideanSpace ℝ W} {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) :
    ContDiff ℝ 1 (fun ω : EuclideanSpace ℝ W => (F (inner ℝ f ω : ℝ))) :=
  hF.comp (innerSL ℝ f).contDiff

/-- **The gradient tuple is `F′` times the fixed vector `f`.** -/
theorem fderiv_smear {f : EuclideanSpace ℝ W} {F F' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt F (F' x) x) (ω : EuclideanSpace ℝ W) (j : W) :
    fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
        (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
      = F' (inner ℝ f ω : ℝ) * (WithLp.ofLp f) j := by
  have hcomp : HasFDerivAt (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ))
      ((F' (inner ℝ f ω : ℝ)) • (innerSL ℝ f)) ω := by
    have h1 : HasFDerivAt (fun z : EuclideanSpace ℝ W => (inner ℝ f z : ℝ)) (innerSL ℝ f) ω :=
      (innerSL ℝ f).hasFDerivAt
    exact (hderiv (inner ℝ f ω : ℝ)).comp_hasFDerivAt ω h1
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  congr 1
  have hinner : ∀ x : W, (inner ℝ ((WithLp.ofLp f) x) (if x = j then (1 : ℝ) else 0) : ℝ)
      = (WithLp.ofLp f) x * (if x = j then (1 : ℝ) else 0) := fun x =>
    (RCLike.inner_apply (𝕜 := ℝ) _ _).trans (by simp [mul_comm])
  simp [PiLp.inner_apply, hinner]

/-! ## 2. The quadratic form pulls the scalar out -/

/-- `(c • w) ⬝ᵥ G *ᵥ (c • w) = c² · (w ⬝ᵥ G *ᵥ w)`, which is where `linVar` appears. -/
theorem quadForm_smul (c : ℝ) (w : W → ℝ) :
    (fun j => c * w j) ⬝ᵥ green K m *ᵥ (fun j => c * w j)
      = c ^ 2 * (w ⬝ᵥ green K m *ᵥ w) := by
  have hw : (fun j => c * w j) = c • w := by funext j; simp [Pi.smul_apply]
  rw [hw, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

/-! ## 3. The smeared inequality, out of the general one -/

/-- **THE ONE-SMEARING POINCARÉ INEQUALITY, DERIVED FROM THE ALL-COORDINATES ONE.**

`∫F(⟪f,ω⟫)² − (∫F(⟪f,ω⟫))² ≤ (fᵀGf)·∫F′(⟪f,ω⟫)²`, under `poincare_correlated_general`'s
hypotheses. The two Poincaré lines of this estate agree on their overlap. -/
theorem poincare_smeared_of_correlated (hm : m ≠ 0) (f : EuclideanSpace ℝ W)
    {F F' : ℝ → ℝ} (hFc : ContDiff ℝ 1 F) (hderiv : ∀ x, HasDerivAt F (F' x) x)
    (hmem : MemLp (fun ω : EuclideanSpace ℝ W => (F (inner ℝ f ω) : ℝ)) 2 (gaussianField K m))
    (hgrad : ∀ j : W, MemLp
      (fun ω : EuclideanSpace ℝ W => F' (inner ℝ f ω : ℝ) * (WithLp.ofLp f) j) 2
      (gaussianField K m)) :
    (∫ ω, (F (inner ℝ f ω) : ℝ) * (F (inner ℝ f ω) : ℝ) ∂(gaussianField K m))
        - (∫ ω, (F (inner ℝ f ω) : ℝ) ∂(gaussianField K m)) ^ 2
      ≤ linVar K m f * ∫ ω, (F' (inner ℝ f ω : ℝ)) ^ 2 ∂(gaussianField K m) := by
  classical
  have hgrad' : ∀ j : W, MemLp (fun ω : EuclideanSpace ℝ W =>
      fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
        (WithLp.toLp 2 (Pi.single j (1 : ℝ)))) 2 (gaussianField K m) := by
    intro j
    have hEq : (fun ω : EuclideanSpace ℝ W =>
        fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
          (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        = fun ω => F' (inner ℝ f ω : ℝ) * (WithLp.ofLp f) j :=
      funext fun ω => fderiv_smear hderiv ω j
    rw [hEq]
    exact hgrad j
  have key := poincare_correlated_general (K := K) hm (contDiff_smear hFc) hmem hgrad'
  refine key.trans (le_of_eq ?_)
  have hpt : ∀ ω : EuclideanSpace ℝ W,
      (fun j => fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
          (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ⬝ᵥ green K m *ᵥ
          (fun j => fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
            (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
      = linVar K m f * (F' (inner ℝ f ω : ℝ)) ^ 2 := by
    intro ω
    simp only [fderiv_smear hderiv ω]
    rw [quadForm_smul]
    rw [linVar_eq_dotG]
    unfold dotG
    ring
  simp only [hpt]
  rw [integral_const_mul]

/-! ## 4. The gap is EXACTLY one hypothesis, which §3 left vaguer than it needed to be

§3 carries the general theorem's two `L²` conditions as hypotheses, and the header called the two
classes "incomparable". Both are true, and both understate what can be said: **`poincare_smeared`'s
own polynomial-growth bounds already imply those `L²` conditions**, via
`LatticePoincare.memLp_comp_pair`. Feeding them in leaves a statement whose hypotheses are
`poincare_smeared`'s **verbatim**, plus `ContDiff ℝ 1 F` and nothing else.

So on one-smearing observables the difference between the estate's two Poincaré theorems is
**exactly the continuity of the derivative** — one hypothesis, named, rather than a two-sided
"incomparable".

*The incomparability itself still stands and is not withdrawn: the general theorem reaches
observables of several smearings, which the smeared one cannot state, and it also reaches `C¹`
functions of super-polynomial growth that are still `L²` — `poincare_smeared` requires polynomial
growth outright. What §4 adds is that in the one direction that can be compared cleanly, the gap is
a single named condition rather than a tangle.*

**AND §8 CLOSES THAT GAP.** The single named condition is removed by
`LatticeFieldDifferentiable.poincare_correlated_differentiable`, so
`poincare_smeared_of_correlated_general` needs no `ContDiff ℝ 1` at all. §4 is left standing
because **measuring a gap and closing it are two different results**, and the measurement is what
told the campaign which hypothesis to attack. -/

/-- **THE SMEARED INEQUALITY UNDER `poincare_smeared`'S OWN HYPOTHESES, PLUS `C¹`.**

Compare `LatticePoincare.poincare_smeared`, which takes `hm`, `f`, `hderiv`, `hb`, `hb'`. This
takes those five and `ContDiff ℝ 1 F`. **That one hypothesis is the entire difference between the
estate's two Poincaré theorems on observables of a single smearing.** -/
theorem poincare_smeared_of_correlated_polyGrowth (hm : m ≠ 0) (f : EuclideanSpace ℝ W)
    {F F' : ℝ → ℝ} (hFc : ContDiff ℝ 1 F) (hderiv : ∀ x, HasDerivAt F (F' x) x)
    {C : ℝ} {k : ℕ}
    (hb : ∀ x, |F x| ≤ C * (1 + x ^ 2) ^ k)
    (hb' : ∀ x, |F' x| ≤ C * (1 + x ^ 2) ^ k) :
    (∫ ω, (F (inner ℝ f ω) : ℝ) * (F (inner ℝ f ω) : ℝ) ∂(gaussianField K m))
        - (∫ ω, (F (inner ℝ f ω) : ℝ) ∂(gaussianField K m)) ^ 2
      ≤ linVar K m f * ∫ ω, (F' (inner ℝ f ω : ℝ)) ^ 2 ∂(gaussianField K m) := by
  have hF'eq : F' = deriv F := funext fun x => (hderiv x).deriv.symm
  have hF'c : Continuous F' := by
    rw [hF'eq]; exact hFc.continuous_deriv le_rfl
  refine poincare_smeared_of_correlated hm f hFc hderiv
    (LatticePoincare.memLp_comp_pair (G := K) hm f hFc.continuous hb) (fun j => ?_)
  exact (LatticePoincare.memLp_comp_pair (G := K) hm f hF'c hb').mul_const _

/-! ## 5. One of the two separations, exhibited rather than asserted

The header claims the classes separate in **both** directions. Both claims were **asserted**, which
is the failure this campaign has logged repeatedly: a statement about the estate written in prose
while the Lean file stays silent. §5 discharges the direction that the estate's own tools reach.

`Real.exp` is `C¹`, its composition with a smearing is square-integrable against the field
(the Gaussian has exponential moments), and it is **not** of polynomial growth — so
`poincare_correlated_general` applies to it and `poincare_smeared` **cannot state it**. -/

/-- **`exp` is not of polynomial growth**, so it fails `poincare_smeared`'s hypothesis outright. -/
theorem exp_not_polyGrowth :
    ¬ ∃ (C : ℝ) (k : ℕ), ∀ x : ℝ, |Real.exp x| ≤ C * (1 + x ^ 2) ^ k := by
  rintro ⟨C, k, hb⟩
  have hbound : ∀ x : ℝ, 1 ≤ x → Real.exp x / x ^ (2 * k) ≤ C * 2 ^ k := by
    intro x hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
    have hxk : (0 : ℝ) < x ^ (2 * k) := by positivity
    have h1 : (1 : ℝ) + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
    have h2 : (1 + x ^ 2) ^ k ≤ (2 * x ^ 2) ^ k := by
      exact pow_le_pow_left₀ (by positivity) h1 k
    have hC : (0 : ℝ) ≤ C := by
      have h0 := hb 0
      norm_num at h0
      linarith
    have h3 : Real.exp x ≤ C * (2 * x ^ 2) ^ k := by
      have := hb x
      rw [abs_of_pos (Real.exp_pos x)] at this
      exact this.trans (by nlinarith [h2])
    have h4 : (2 * x ^ 2 : ℝ) ^ k = 2 ^ k * x ^ (2 * k) := by
      rw [mul_pow, ← pow_mul]
    rw [div_le_iff₀ hxk]
    calc Real.exp x ≤ C * (2 * x ^ 2) ^ k := h3
      _ = C * 2 ^ k * x ^ (2 * k) := by rw [h4]; ring
  have hev := (Real.tendsto_exp_div_pow_atTop (2 * k)).eventually_gt_atTop (C * 2 ^ k)
  obtain ⟨x, hx1, hx2⟩ := ((Filter.eventually_ge_atTop (1 : ℝ)).and hev).exists
  exact absurd (hbound x hx1) (not_le.mpr hx2)

/-- The exponential of a smearing is square-integrable against the field: its square is the
exponential of the smearing at `2•f`, and the Gaussian has exponential moments. -/
theorem memLp_exp_smear (hm : m ≠ 0) (f : EuclideanSpace ℝ W) :
    MemLp (fun ω : EuclideanSpace ℝ W => Real.exp (inner ℝ f ω : ℝ)) 2 (gaussianField K m) := by
  have hmeas : AEStronglyMeasurable
      (fun ω : EuclideanSpace ℝ W => Real.exp (inner ℝ f ω : ℝ)) (gaussianField K m) :=
    (Real.continuous_exp.comp (LatticeIsserlisFour.continuous_pair f)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hsq : (fun ω : EuclideanSpace ℝ W => (Real.exp (inner ℝ f ω : ℝ)) ^ 2)
      = fun ω : EuclideanSpace ℝ W => Real.exp (inner ℝ ((2 : ℝ) • f) ω : ℝ) := by
    funext ω
    rw [inner_smul_left]
    simp [two_mul, Real.exp_add, sq]
  rw [hsq]
  exact LatticeGeneratingFunctional.integrable_exp_inner (G := K) hm _

/-- **THE SEPARATION, EXHIBITED.** The general theorem's inequality holds for the exponential
observable — which `poincare_smeared` cannot state, by `exp_not_polyGrowth`. -/
theorem poincare_reaches_exp (hm : m ≠ 0) (f : EuclideanSpace ℝ W) :
    (∫ ω, Real.exp (inner ℝ f ω : ℝ) * Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField K m))
        - (∫ ω, Real.exp (inner ℝ f ω : ℝ) ∂(gaussianField K m)) ^ 2
      ≤ linVar K m f * ∫ ω, (Real.exp (inner ℝ f ω : ℝ)) ^ 2 ∂(gaussianField K m) :=
  poincare_smeared_of_correlated hm f Real.contDiff_exp (fun x => Real.hasDerivAt_exp x)
    (memLp_exp_smear (K := K) hm f)
    (fun _ => (memLp_exp_smear (K := K) hm f).mul_const _)

/-! ## 6. The OTHER separation, also exhibited — and the observable, not just the profile

§5 left the second half of the header's claim marked **STILL ASSERTED, NOT PROVED** and named the
witness anyone would need: `x²sin(1/x)` extended by `0`. `DifferentiableNotC1` builds it, with no
lattice in sight. §6 is where it earns its place here.

**The instantiation was available all along, which is why leaving it as a caveat would have been
the wrong call.** `LatticePoincare.poincare_smeared` asks for `hderiv`, `hb`, `hb'` and nothing
else about `F`; `DifferentiableNotC1.exists_differentiable_polyGrowth_not_contDiff` proves exactly
those three at `C = 2`, `k = 1`. So `poincare_smeared_reaches_wig` is a one-line application.

**AND THE HALF THAT IS NOT A ONE-LINE APPLICATION IS THE HALF THAT MATTERS.** `wig` not being `C¹`
says nothing yet about the *observable* `ω ↦ wig ⟪f,ω⟫` — a composition can be smoother than the
function composed. `not_contDiff_wig_smear` closes that: restrict along the line
`t ↦ t·(‖f‖²)⁻¹·f`, on which the smearing reads off `⟪f, t·(‖f‖²)⁻¹·f⟫ = t`, so a `C¹` observable
would compose with a linear map to give a `C¹` `wig`. It needs `f ≠ 0`, and it should: at `f = 0`
the observable is constant and perfectly smooth, so the separation genuinely has a hypothesis
rather than merely inheriting one.

**What this does NOT say.** It says `poincare_correlated_general`'s **hypothesis** fails at this
observable — not that its **conclusion** does. Nothing here rules out the inequality holding for
`wig ⟪f,·⟫` by some other route, and the estate's own `LatticeSqrtEquiv` line is precisely such a
route for other non-smooth observables. The claim is about the reach of a theorem as stated, which
is what "the hypothesis classes are incomparable" means and all it means. -/

/-- **THE SMEARED THEOREM REACHES `wig`.** `poincare_smeared`'s three hypotheses, verbatim, are
what `DifferentiableNotC1` proves — so the inequality holds for an observable whose profile is
differentiable everywhere with a **discontinuous** derivative. -/
theorem poincare_smeared_reaches_wig (hm : m ≠ 0) (f : EuclideanSpace ℝ W) :
    (∫ ω, DifferentiableNotC1.wig (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField K m))
        - (∫ ω, DifferentiableNotC1.wig (inner ℝ f ω : ℝ) ∂(gaussianField K m)) ^ 2
      ≤ linVar K m f
          * ∫ ω, DifferentiableNotC1.wig' (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField K m) :=
  LatticePoincare.poincare_smeared (G := K) hm f DifferentiableNotC1.hasDerivAt_wig
    (fun x => (DifferentiableNotC1.wig_bound x).trans (by nlinarith [sq_nonneg x]))
    DifferentiableNotC1.wig'_bound

omit [DecidableEq W] in
/-- **AND THE GENERAL THEOREM DOES NOT REACH IT — AT THE OBSERVABLE, NOT MERELY AT THE PROFILE.**

`ω ↦ wig ⟪f,ω⟫` is not `ContDiff ℝ 1` for any `f ≠ 0`. The line `t ↦ t·(‖f‖²)⁻¹·f` is smooth and
the smearing restricted to it is the identity, so a `C¹` observable would give a `C¹` `wig`. -/
theorem not_contDiff_wig_smear {f : EuclideanSpace ℝ W} (hf : f ≠ 0) :
    ¬ ContDiff ℝ 1 (fun ω : EuclideanSpace ℝ W => DifferentiableNotC1.wig (inner ℝ f ω : ℝ)) := by
  intro h
  have hnn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
  have hline : ContDiff ℝ 1 (fun t : ℝ => t • ((‖f‖ ^ 2)⁻¹ • f)) :=
    contDiff_id.smul contDiff_const
  have hinner : ∀ t : ℝ, (inner ℝ f (t • ((‖f‖ ^ 2)⁻¹ • f)) : ℝ) = t := by
    intro t
    rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hcomp := h.comp hline
  have heq : (fun t : ℝ => DifferentiableNotC1.wig
      (inner ℝ f (t • ((‖f‖ ^ 2)⁻¹ • f)) : ℝ)) = DifferentiableNotC1.wig :=
    funext fun t => by rw [hinner t]
  rw [Function.comp_def, heq] at hcomp
  exact DifferentiableNotC1.not_contDiff_wig hcomp

/-- **THE SECOND SEPARATION, EXHIBITED RATHER THAN ASSERTED.**

One observable, `ω ↦ wig ⟪f,ω⟫` at any `f ≠ 0`: the smeared theorem's inequality **holds** for it,
and the general theorem's `C¹` hypothesis **fails** for it. Together with `poincare_reaches_exp`
and `exp_not_polyGrowth` — which do the same in the opposite direction — the header's
incomparability claim is now a pair of witnesses in both directions, with nothing left asserted. -/
theorem separation_both_directions (hm : m ≠ 0) {f : EuclideanSpace ℝ W} (hf : f ≠ 0) :
    ((∫ ω, DifferentiableNotC1.wig (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField K m))
        - (∫ ω, DifferentiableNotC1.wig (inner ℝ f ω : ℝ) ∂(gaussianField K m)) ^ 2
        ≤ linVar K m f
            * ∫ ω, DifferentiableNotC1.wig' (inner ℝ f ω : ℝ) ^ 2 ∂(gaussianField K m))
      ∧ ¬ ContDiff ℝ 1 (fun ω : EuclideanSpace ℝ W => DifferentiableNotC1.wig (inner ℝ f ω : ℝ))
      ∧ ¬ ∃ (C : ℝ) (k : ℕ), ∀ x : ℝ, |Real.exp x| ≤ C * (1 + x ^ 2) ^ k :=
  ⟨poincare_smeared_reaches_wig hm f, not_contDiff_wig_smear hf, exp_not_polyGrowth⟩

/-! ## 7. The §6 caveat, discharged — the conclusion DOES hold, by another route

§6 was careful to say that it proved `poincare_correlated_general`'s **hypothesis** fails at
`ω ↦ wig ⟪f,ω⟫`, **not** that its conclusion does, and named where a different route might come
from. `LatticeFieldDifferentiable` has since built that route:
`poincare_correlated_differentiable` proves the same inequality for any differentiable observable of
polynomial growth, with no continuity of the gradient. `wig ⟪f,·⟫` is such an observable.

**So the separation §6 exhibited is exactly a separation between HYPOTHESIS CLASSES, and §7 is what
makes that precise rather than merely careful.** The observable is outside the `C¹` theorem's reach
and the inequality holds for it anyway. A caveat that can be turned into a theorem should be. -/

/-- `ω ↦ wig ⟪f,ω⟫`, the observable §6 showed is not `C¹`. -/
noncomputable def wigSmear (f : EuclideanSpace ℝ W) : EuclideanSpace ℝ W → ℝ :=
  fun ω => DifferentiableNotC1.wig (inner ℝ f ω : ℝ)

omit [DecidableEq W] in
/-- A coordinate of a vector is bounded by its norm — Cauchy–Schwarz against a unit basis vector. -/
theorem abs_coord_le_norm (f : EuclideanSpace ℝ W) (j : W) : |(WithLp.ofLp f) j| ≤ ‖f‖ := by
  classical
  have hj : (inner ℝ f (WithLp.toLp 2 (Pi.single j (1 : ℝ))) : ℝ) = (WithLp.ofLp f) j := by
    have hinner : ∀ x : W, (inner ℝ ((WithLp.ofLp f) x) (if x = j then (1 : ℝ) else 0) : ℝ)
        = (WithLp.ofLp f) x * (if x = j then (1 : ℝ) else 0) := fun x =>
      (RCLike.inner_apply (𝕜 := ℝ) _ _).trans (by simp [mul_comm])
    simp [PiLp.inner_apply, hinner]
  have hcs := abs_real_inner_le_norm f (WithLp.toLp 2 (Pi.single j (1 : ℝ)))
  rw [hj] at hcs
  have hn : ‖(WithLp.toLp 2 (Pi.single j (1 : ℝ)) : EuclideanSpace ℝ W)‖ = 1 := by
    simp
  rwa [hn, mul_one] at hcs

omit [DecidableEq W] in
/-- **POLYNOMIAL GROWTH SURVIVES ONE SMEARING, WITH THE EXPONENT UNTOUCHED.**
`|F t| ≤ C(1+t²)^k` gives `|F ⟪f,ω⟫| ≤ C(1+‖f‖²)^k·(1+‖ω‖²)^k`, by Cauchy–Schwarz on the smearing
and one elementary factorisation. -/
theorem smear_polyGrowth {F : ℝ → ℝ} {C : ℝ} {k : ℕ}
    (hb : ∀ x, |F x| ≤ C * (1 + x ^ 2) ^ k) (f ω : EuclideanSpace ℝ W) :
    |F (inner ℝ f ω : ℝ)| ≤ C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖ω‖ ^ 2) ^ k := by
  have hC : 0 ≤ C := by
    have h0 := hb 0
    norm_num at h0
    exact le_trans (abs_nonneg _) h0
  have hcs : |(inner ℝ f ω : ℝ)| ≤ ‖f‖ * ‖ω‖ := abs_real_inner_le_norm f ω
  have hsq : (inner ℝ f ω : ℝ) ^ 2 ≤ ‖f‖ ^ 2 * ‖ω‖ ^ 2 := by
    nlinarith [abs_nonneg (inner ℝ f ω : ℝ), sq_abs (inner ℝ f ω : ℝ),
      norm_nonneg f, norm_nonneg ω]
  refine (hb _).trans ?_
  have hstep : (1 + (inner ℝ f ω : ℝ) ^ 2) ^ k ≤ ((1 + ‖f‖ ^ 2) * (1 + ‖ω‖ ^ 2)) ^ k := by
    refine pow_le_pow_left₀ (by positivity) ?_ k
    nlinarith [sq_nonneg ‖f‖, sq_nonneg ‖ω‖]
  calc C * (1 + (inner ℝ f ω : ℝ) ^ 2) ^ k
      ≤ C * ((1 + ‖f‖ ^ 2) * (1 + ‖ω‖ ^ 2)) ^ k := mul_le_mul_of_nonneg_left hstep hC
    _ = C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖ω‖ ^ 2) ^ k := by rw [mul_pow]; ring

/-- **AND SO DOES THE GRADIENT'S**, paying one factor of `‖f‖`: `∂ⱼ[F⟪f,ω⟫] = F′⟪f,ω⟫·fⱼ` by
`fderiv_smear`, and a coordinate is bounded by the norm. -/
theorem fderiv_smear_polyGrowth {F F' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt F (F' x) x)
    {C : ℝ} {k : ℕ} (hb' : ∀ x, |F' x| ≤ C * (1 + x ^ 2) ^ k)
    (f : EuclideanSpace ℝ W) (j : W) (ω : EuclideanSpace ℝ W) :
    |fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
        (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖f‖) * (1 + ‖ω‖ ^ 2) ^ k := by
  rw [fderiv_smear hderiv ω j, abs_mul]
  have h1 := smear_polyGrowth hb' f ω
  have h2 : |(WithLp.ofLp f) j| ≤ 1 + ‖f‖ :=
    (abs_coord_le_norm f j).trans (by linarith [norm_nonneg f])
  have hnn : (0:ℝ) ≤ C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖ω‖ ^ 2) ^ k := le_trans (abs_nonneg _) h1
  calc |F' (inner ℝ f ω : ℝ)| * |(WithLp.ofLp f) j|
      ≤ (C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖ω‖ ^ 2) ^ k) * (1 + ‖f‖) :=
        mul_le_mul h1 h2 (abs_nonneg _) hnn
    _ = C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖f‖) * (1 + ‖ω‖ ^ 2) ^ k := by ring

omit [DecidableEq W] in
theorem differentiable_wigSmear (f : EuclideanSpace ℝ W) : Differentiable ℝ (wigSmear f) :=
  DifferentiableNotC1.differentiable_wig.comp (innerSL ℝ f).differentiable

omit [DecidableEq W] in
/-- Polynomial growth of the observable — `smear_polyGrowth` at `F = wig`, `C = 2`, `k = 1`,
with `1 ≤ 1 + ‖f‖` supplying the extra factor the gradient bound needs. -/
theorem wigSmear_bound (f : EuclideanSpace ℝ W) (ω : EuclideanSpace ℝ W) :
    |wigSmear f ω| ≤ 2 * (1 + ‖f‖ ^ 2) * (1 + ‖f‖) * (1 + ‖ω‖ ^ 2) ^ 1 := by
  have hb2 : ∀ x : ℝ, |DifferentiableNotC1.wig x| ≤ 2 * (1 + x ^ 2) ^ 1 := fun x =>
    (DifferentiableNotC1.wig_bound x).trans (by nlinarith [sq_nonneg x])
  have h := smear_polyGrowth hb2 f ω
  simp only [pow_one] at h
  simp only [wigSmear, pow_one]
  refine h.trans ?_
  have hA : (0:ℝ) ≤ 2 * (1 + ‖f‖ ^ 2) * (1 + ‖ω‖ ^ 2) := by positivity
  nlinarith [mul_nonneg hA (norm_nonneg f)]

/-- The same bound for every partial derivative — `fderiv_smear_polyGrowth` at `F = wig`. -/
theorem fderiv_wigSmear_bound (f : EuclideanSpace ℝ W) (j : W) (ω : EuclideanSpace ℝ W) :
    |fderiv ℝ (wigSmear f) ω (WithLp.toLp 2 (Pi.single j (1 : ℝ)))|
      ≤ 2 * (1 + ‖f‖ ^ 2) * (1 + ‖f‖) * (1 + ‖ω‖ ^ 2) ^ 1 := by
  have h := fderiv_smear_polyGrowth (F := DifferentiableNotC1.wig)
    (F' := DifferentiableNotC1.wig') DifferentiableNotC1.hasDerivAt_wig
    DifferentiableNotC1.wig'_bound f j ω
  simpa [wigSmear] using h

/-- **THE CAVEAT §6 WROTE, NOW A THEOREM.** The inequality `poincare_correlated_general` states
**does** hold at `ω ↦ wig ⟪f,ω⟫`, by `LatticeFieldDifferentiable`'s differentiable route — even
though that theorem's `C¹` hypothesis fails there for every `f ≠ 0` (`not_contDiff_wig_smear`).

So what §6 exhibited is a gap between **hypothesis classes** and not between what can be concluded,
and §7 is what turns "nothing here rules that out" into "and here it is". -/
theorem poincare_reaches_wigSmear (hm : m ≠ 0) (f : EuclideanSpace ℝ W) :
    (∫ ω, wigSmear f ω * wigSmear f ω ∂(gaussianField K m))
        - (∫ ω, wigSmear f ω ∂(gaussianField K m)) ^ 2
      ≤ ∫ ω, (fun j => fderiv ℝ (wigSmear f) ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
          ⬝ᵥ green K m *ᵥ (fun j => fderiv ℝ (wigSmear f) ω (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ∂(gaussianField K m) :=
  LatticeFieldDifferentiable.poincare_correlated_differentiable hm (differentiable_wigSmear f)
    (wigSmear_bound f) (fun j ω => fderiv_wigSmear_bound f j ω)

/-! ## 8. And now the correlated line DOES subsume `poincare_smeared` — this file's own
"What this is NOT" has been overtaken

§4 established that on observables of a single smearing the entire difference between the estate's
two Poincaré theorems is `ContDiff ℝ 1 F`, one named condition. The "What this is NOT" section
concluded, correctly at the time, that this file **does not reprove `poincare_smeared`**, *"whose
hypotheses this cannot reach"*.

**`LatticeFieldDifferentiable.poincare_correlated_differentiable` reaches them.** It asks for a
differentiable observable of polynomial growth and no continuity of the gradient — and `§7`'s
`smear_polyGrowth` and `fderiv_smear_polyGrowth` say exactly that `ω ↦ F⟪f,ω⟫` is one whenever `F`
satisfies `poincare_smeared`'s own three hypotheses. So the `C¹` §4 isolated is not merely small;
it is **gone**, and `poincare_smeared_of_correlated_general` takes `hm`, `f`, `hderiv`, `hb`, `hb'`
and nothing else.

**WHAT DOES AND DOES NOT CHANGE, because the header above is not simply wrong.**

* `poincare_smeared` and `poincare_correlated_general` — the `C¹` theorem — **remain
  incomparable**, and §5 and §6 both stand: `Real.exp` is in one and not the other, `wig ⟪f,·⟫` is
  in the other and not the one. Nothing in §8 touches either witness.
* What §8 changes is a claim about **this file's own reach**, not about those two theorems: the
  *correlated line as a whole*, which now includes the differentiable route, subsumes
  `poincare_smeared` completely. `§4`'s "the gap is exactly one hypothesis" was a true measurement
  of a gap that has since been closed **by this campaign's own later units**, not by a better proof
  of the same thing.

*The superseded sentence is quoted rather than deleted (`ERRATUM 94`) because a file that measured a
gap and then closed it should show both, and because "cannot reach" was a statement about the estate
on the day it was written and never about mathematics.* -/

/-- **`poincare_smeared`, REPROVED FROM THE CORRELATED LINE, ON ITS OWN HYPOTHESES VERBATIM.**

`hm`, `f`, `hderiv`, `hb`, `hb'` — the five arguments of `LatticePoincare.poincare_smeared`, with
**no `ContDiff ℝ 1`**. Compare `poincare_smeared_of_correlated_polyGrowth`, which is this statement
plus that hypothesis; §4 called it the entire remaining difference and it is now removed. -/
theorem poincare_smeared_of_correlated_general (hm : m ≠ 0) (f : EuclideanSpace ℝ W)
    {F F' : ℝ → ℝ} (hderiv : ∀ x, HasDerivAt F (F' x) x) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |F x| ≤ C * (1 + x ^ 2) ^ k)
    (hb' : ∀ x, |F' x| ≤ C * (1 + x ^ 2) ^ k) :
    (∫ ω, (F (inner ℝ f ω) : ℝ) ^ 2 ∂(gaussianField K m))
        - (∫ ω, (F (inner ℝ f ω) : ℝ) ∂(gaussianField K m)) ^ 2
      ≤ linVar K m f * ∫ ω, (F' (inner ℝ f ω : ℝ)) ^ 2 ∂(gaussianField K m) := by
  classical
  have hΦd : Differentiable ℝ (fun ω : EuclideanSpace ℝ W => (F (inner ℝ f ω) : ℝ)) := by
    intro ω
    exact ((hderiv (inner ℝ f ω : ℝ)).comp_hasFDerivAt ω
      (innerSL ℝ f).hasFDerivAt).differentiableAt
  have hB : ∀ ω : EuclideanSpace ℝ W, |(F (inner ℝ f ω) : ℝ)|
      ≤ C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖f‖) * (1 + ‖ω‖ ^ 2) ^ k := by
    intro ω
    refine (smear_polyGrowth hb f ω).trans ?_
    have hA : (0:ℝ) ≤ C * (1 + ‖f‖ ^ 2) ^ k * (1 + ‖ω‖ ^ 2) ^ k :=
      le_trans (abs_nonneg _) (smear_polyGrowth hb f ω)
    nlinarith [mul_nonneg hA (norm_nonneg f)]
  have key := LatticeFieldDifferentiable.poincare_correlated_differentiable (K := K) hm hΦd hB
    (fun j ω => fderiv_smear_polyGrowth hderiv hb' f j ω)
  have hconv : ∀ ω : EuclideanSpace ℝ W,
      (F (inner ℝ f ω) : ℝ) * (F (inner ℝ f ω) : ℝ) = (F (inner ℝ f ω) : ℝ) ^ 2 :=
    fun ω => (sq _).symm
  simp only [hconv] at key
  refine key.trans (le_of_eq ?_)
  have hpt : ∀ ω : EuclideanSpace ℝ W,
      (fun j => fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
          (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
        ⬝ᵥ green K m *ᵥ
          (fun j => fderiv ℝ (fun z : EuclideanSpace ℝ W => (F (inner ℝ f z) : ℝ)) ω
            (WithLp.toLp 2 (Pi.single j (1 : ℝ))))
      = linVar K m f * (F' (inner ℝ f ω : ℝ)) ^ 2 := by
    intro ω
    simp only [fderiv_smear hderiv ω]
    rw [quadForm_smul, linVar_eq_dotG]
    unfold dotG
    ring
  simp only [hpt]
  rw [integral_const_mul]

/-- **MACHINE-CHECKED: §8 IS `poincare_smeared`, NOT MERELY SOMETHING LIKE IT.**

Proof irrelevance closes `A = B` by `rfl` exactly when the two propositions coincide, so this
`example` fails to compile if the hypothesis lists or the conclusions differ in any way. It is the
check that "subsumes" was not asserted. -/
example (hm : m ≠ 0) (f : EuclideanSpace ℝ W) {F F' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt F (F' x) x) {C : ℝ} {k : ℕ}
    (hb : ∀ x, |F x| ≤ C * (1 + x ^ 2) ^ k)
    (hb' : ∀ x, |F' x| ≤ C * (1 + x ^ 2) ^ k) :
    LatticePoincare.poincare_smeared (G := K) hm f hderiv hb hb'
      = poincare_smeared_of_correlated_general hm f hderiv hb hb' := rfl

end LatticeSmearedFromGeneral
