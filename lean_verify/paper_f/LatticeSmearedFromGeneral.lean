import LatticeCorrelatedPoincare
import LatticeIsserlisSmeared
import LatticePoincare

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
  `poincare_smeared` and **outside** `poincare_correlated_general`;
* an observable of two smearings is inside `poincare_correlated_general` and **outside**
  `poincare_smeared`, which cannot state it.

Neither theorem implies the other. **No file in the estate claimed otherwise** — checked by reading
all three headers — so this is an unrecorded fact rather than an erratum. But "the general one
covers the special one" is exactly the sort of thing a later reader assumes, and it is false.

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

**It does not reprove `poincare_smeared`**, whose hypotheses this cannot reach (see above). It
proves the same *conclusion* under the *general* theorem's hypotheses, which is what "the two lines
agree" can honestly mean.

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
a single named condition rather than a tangle.* -/

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

end LatticeSmearedFromGeneral
