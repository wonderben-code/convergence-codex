import LovelockInnerPositive
import LovelockInnerInvariant

/-!
# The disclaimer that outlived its reason: `ip` is the inner product of a Euclidean space

`LovelockOrthogonality` built the full contraction `ip R S = ∑_{abcd} R_{abcd} S_{abcd}`,
`LovelockInnerPositive` proved it positive definite, and both files then say the same thing:

> **It is not an inner-product-space instance** … no `InnerProductSpace`, no completeness, no
> norm. **Bundling would mean choosing a carrier for four-index arrays that nothing in the estate
> consumes.**

**The carrier objection is answered by not choosing one.** No instance is placed on
`Fin n → Fin n → Fin n → Fin n → ℝ` here — that type keeps its pi-type instances and there is no
diamond to worry about. What is built is an explicit **linear equivalence** onto a carrier
Mathlib already owns, `EuclideanSpace ℝ (Fin n × Fin n × Fin n × Fin n)`, together with the one
theorem that makes it worth having: **the equivalence carries `ip` to that space's inner product.**

## What is proved

* **`arrEquiv`** — the currying equivalence, a bare `≃ₗ[ℝ]`, with `arrEquiv_apply` and
  `arrEquiv_symm_apply` so nothing downstream has to unfold it;
* **`inner_arrEquiv`** — `⟪arrEquiv R, arrEquiv S⟫_ℝ = ip R S`. This is the whole content: `ip`
  **is** an inner product, not merely a form with an inner product's properties;
* **`norm_arrEquiv`** — `‖arrEquiv R‖ = √(ip R R)`, so "length" in `LovelockInnerPositive`'s
  prose becomes a norm rather than a metaphor;
* **`ip_abs_le`** — **Cauchy–Schwarz for the full contraction**, `|ip R S| ≤ √(ip R R) · √(ip S S)`;
* **`ip_add_sqrt_le`** — the triangle inequality, `√(ip (R+S) (R+S)) ≤ √(ip R R) + √(ip S S)`;
* **`inner_weylPart_ricciPart`, `inner_weylPart_scalPart`, `inner_ricciPart_scalPart`** — the
  three orthogonality theorems restated against the inner product rather than the bare form, and
  **`norm_sq_eq`**, Pythagoras on norms: the squared length of a curvature tensor is the sum of
  the squared lengths of its three summands. `ERRATUM 201` — the claim to cover them is
  discharged by instantiating them;
* **`norm_arrEquiv_act`** and its three summand versions — `LovelockInnerInvariant` proved the
  three squared lengths independent of the frame; they are now **norms**, so that is invariance
  of a length rather than of a number;
* **`ip_weylPart_abs_le`** — the consumer, and the reason this is not a bundling exercise: taking
  the Weyl summand does not increase a contraction. `|ip (weylPart R) S| ≤ √(ip R R) · √(ip S S)`,
  with the whole tensor on the right where the summand used to be.

## Why the last two are the point (`ERRATUM 48`)

**A construction that produces no new member has its usefulness merely asserted.** Cauchy–Schwarz
and the triangle inequality are not available from `ip_self_nonneg`, `ip_self_pos` and
`eq_zero_of_ip_self_eq_zero`; proving them on the bare form means the discriminant argument by
hand. They come free with the identification, and `ip_weylPart_abs_le` is a statement about
curvature that the estate could not previously make: it combines Cauchy–Schwarz with
`LovelockInnerPositive.ip_weylPart_le_self`, and neither half gives it alone.

## What this still does not do

**No completeness is claimed and none is needed** — the carrier is finite-dimensional, so Mathlib
supplies it, but nothing here uses it. **No instance is added to the array type**, deliberately:
the estate's other files state `ip` results about the bare pi type and continue to, and
`arrEquiv` is the bridge rather than a replacement. And **`KillsWeyl` is untouched**: this
sharpens the metric vocabulary around the Weyl summand and says nothing about what an equivariant
`T` does to it, so that watchlist item does not move.


**⚠ CORRECTED 2026-08-22 — THE SENTENCE ABOVE IS TRUE AND ITS FRAMING IS NOT, and it is kept per
`ERRATUM 94`.** `KillsWeyl` is **proved**, at every `n ≥ 3`, by
`LovelockKillsWeyl.killsWeyl_of_equivariant` (`171d474`, 15 August), and the watchlist's Lovelock
item is CLOSED. *"The watchlist item does not move"* is therefore true only in the sense that a
closed item cannot move — **and it invites the reading that `KillsWeyl` is open, which is false.**
What this file does not bear on is the wall's actual remaining step, which is rung 2 of `WALLS`
§W5.1's staircase: an **affine connection and Levi-Civita**, zero names in Mathlib. `ERRATUM 230`
records that this framing was inherited from the headers being extended and repeated across a
day's units without being checked.

**^ THE CLAUSE ABOVE PUTTING THE AFFINE CONNECTION AT *ZERO NAMES IN MATHLIB* IS FALSE, AND IS
KEPT AS WRITTEN** (`ERRATUM 416`, 2026-09-02). Mathlib has **`CovariantDerivative`** — 73 names in
this estate's own `env_names.txt` — and `IsCovariantDerivativeOn` (24), with `torsion` beside them;
the probe behind the clause asked for the lower-case `covariantDerivative`, which is **0**
(`ERRATUM 411`). **EVERY OTHER CLAUSE STANDS, RE-PROBED TODAY RATHER THAN INHERITED**: `LeviCivita`
**0**, `HeatKernel` and `heatKernel` **0** each, and curvature **0** in four spellings
(`Curvature`, `curvature`, `riemannianCurvature`, `RiemannCurvature`). **So rung 2 is still the
wall's remaining step, this file still does not bear on it, and no verdict here changes** — what
moved is the rung W5 fails at, which `WALLS` §W5.1 records. **The clause reached eight files by
header inheritance, which is the mechanism `ERRATUM 230` already names**, and no absence mode caught
it because the sentence names no identifier to probe.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace LovelockInnerSpace

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockInnerPositive
  LovelockInnerInvariant LovelockEquivariance Finset

variable {n : ℕ} {Q : Fin n → Fin n → ℝ}

/-! ## 1. The carrier, and the equivalence onto it -/

/-- The index type of a four-index array. -/
abbrev ArrIdx (n : ℕ) := Fin n × Fin n × Fin n × Fin n

/-- **Four-index arrays as a Euclidean space.** Currying, packaged as a linear equivalence onto
`EuclideanSpace ℝ (ArrIdx n)`. Nothing is asserted here beyond re-association of the arguments;
the content is `inner_arrEquiv` below. -/
def arrEquiv (n : ℕ) :
    (Fin n → Fin n → Fin n → Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (ArrIdx n) where
  toFun R := WithLp.toLp 2 (fun p => R p.1 p.2.1 p.2.2.1 p.2.2.2)
  invFun x := fun a b c d => WithLp.ofLp x (a, b, c, d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem arrEquiv_apply (R : Fin n → Fin n → Fin n → Fin n → ℝ) (p : ArrIdx n) :
    WithLp.ofLp (arrEquiv n R) p = R p.1 p.2.1 p.2.2.1 p.2.2.2 := rfl

@[simp] theorem arrEquiv_symm_apply (x : EuclideanSpace ℝ (ArrIdx n)) (a b c d : Fin n) :
    (arrEquiv n).symm x a b c d = WithLp.ofLp x (a, b, c, d) := rfl

/-! ## 2. The identification, which is the whole content -/

/-- **`ip` IS the inner product of `EuclideanSpace ℝ (ArrIdx n)`**, carried along `arrEquiv`. -/
theorem inner_arrEquiv (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    inner ℝ (arrEquiv n R) (arrEquiv n S) = ip R S := by
  have hpt : ∀ a b : ℝ, inner ℝ a b = a * b := by
    intro a b
    simpa using RCLike.inner_apply' (𝕜 := ℝ) a b
  rw [PiLp.inner_apply, ip]
  simp only [arrEquiv_apply, hpt, Fintype.sum_prod_type]

/-- And the norm is the square root of the self-contraction. -/
theorem norm_arrEquiv (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ‖arrEquiv n R‖ = Real.sqrt (ip R R) := by
  rw [← inner_arrEquiv, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-! ## 3. What the identification buys -/

/-- **CAUCHY–SCHWARZ FOR THE FULL CONTRACTION.** Not available from positive definiteness alone
without redoing the discriminant argument by hand. -/
theorem ip_abs_le (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    |ip R S| ≤ Real.sqrt (ip R R) * Real.sqrt (ip S S) := by
  have h := abs_real_inner_le_norm (arrEquiv n R) (arrEquiv n S)
  rwa [inner_arrEquiv, norm_arrEquiv, norm_arrEquiv] at h

/-- **THE TRIANGLE INEQUALITY** for the length `√(ip R R)`. -/
theorem ip_add_sqrt_le (R S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    Real.sqrt (ip (fun a b c d => R a b c d + S a b c d)
        (fun a b c d => R a b c d + S a b c d))
      ≤ Real.sqrt (ip R R) + Real.sqrt (ip S S) := by
  have hsum : arrEquiv n (fun a b c d => R a b c d + S a b c d)
      = arrEquiv n R + arrEquiv n S := rfl
  have h := norm_add_le (arrEquiv n R) (arrEquiv n S)
  rwa [← hsum, norm_arrEquiv, norm_arrEquiv, norm_arrEquiv] at h

/-! ## 4. The Ricci decomposition as an orthogonal decomposition

`ERRATUM 201`: a claim that a structure "covers" existing results is discharged by INSTANTIATING
them, not by saying it would. `LovelockOrthogonality`'s three orthogonality theorems and its
Pythagoras identity are stated against the bare form; here they are, against the inner product. -/

/-- **THE WEYL AND RICCI SUMMANDS ARE ORTHOGONAL**, in a genuine inner-product space. -/
theorem inner_weylPart_ricciPart (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    inner ℝ (arrEquiv n (weylPart R)) (arrEquiv n (ricciPart R)) = 0 := by
  rw [inner_arrEquiv]; exact ip_weylPart_ricciPart hn1 hn2 hR

/-- **AND THE WEYL AND SCALAR SUMMANDS.** -/
theorem inner_weylPart_scalPart (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    inner ℝ (arrEquiv n (weylPart R)) (arrEquiv n (scalPart R)) = 0 := by
  rw [inner_arrEquiv]; exact ip_weylPart_scalPart hn1 hn2 hR

/-- **AND THE OTHER TWO.** -/
theorem inner_ricciPart_scalPart (hn0 : (n : ℝ) ≠ 0)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    inner ℝ (arrEquiv n (ricciPart R)) (arrEquiv n (scalPart R)) = 0 := by
  rw [inner_arrEquiv]; exact ip_ricciPart_scalPart hn0 hR

/-- **PYTHAGORAS, ON NORMS.** `LovelockOrthogonality.ip_self_eq` says the three self-contractions
add up; with `norm_arrEquiv` that is the theorem it was always the shadow of — the squared length
of a curvature tensor is the sum of the squared lengths of its three summands. -/
theorem norm_sq_eq (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    ‖arrEquiv n R‖ ^ 2 = ‖arrEquiv n (weylPart R)‖ ^ 2 + ‖arrEquiv n (ricciPart R)‖ ^ 2
      + ‖arrEquiv n (scalPart R)‖ ^ 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_arrEquiv]
  exact ip_self_eq hn0 hn1 hn2 hR

/-! ## 5. The three invariants are frame-independent NORMS

`LovelockInnerInvariant` proved the three squared lengths unchanged by an orthogonal change of
frame and then said *"no `InnerProductSpace` instance, no completeness, no norm"*. With
`norm_arrEquiv` they are norms, and the invariance is invariance of a length. -/

/-- **THE LENGTH OF A CURVATURE TENSOR DOES NOT DEPEND ON THE FRAME.** -/
theorem norm_arrEquiv_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ‖arrEquiv n (act Q R)‖ = ‖arrEquiv n R‖ := by
  rw [norm_arrEquiv, norm_arrEquiv, ip_self_act hQ]

/-- **NOR THE LENGTH OF ITS WEYL SUMMAND**, `|Weyl|` as a norm rather than as a number. -/
theorem norm_arrEquiv_weylPart_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ‖arrEquiv n (weylPart (act Q R))‖ = ‖arrEquiv n (weylPart R)‖ := by
  rw [norm_arrEquiv, norm_arrEquiv, ip_weylPart_act hQ]

/-- **NOR `|Ric₀|`.** -/
theorem norm_arrEquiv_ricciPart_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ‖arrEquiv n (ricciPart (act Q R))‖ = ‖arrEquiv n (ricciPart R)‖ := by
  rw [norm_arrEquiv, norm_arrEquiv, ip_ricciPart_act hQ]

/-- **NOR `|scal|`.** -/
theorem norm_arrEquiv_scalPart_act (hQ : IsOrth Q) (R : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ‖arrEquiv n (scalPart (act Q R))‖ = ‖arrEquiv n (scalPart R)‖ := by
  rw [norm_arrEquiv, norm_arrEquiv, ip_scalPart_act hQ]

/-! ## 6. The consumer -/

/-- **TAKING THE WEYL SUMMAND DOES NOT INCREASE A CONTRACTION.** The whole tensor stands on the
right where the summand would: `|ip (weylPart R) S| ≤ √(ip R R) · √(ip S S)`. Cauchy–Schwarz
supplies the summand's own bound and `LovelockInnerPositive.ip_weylPart_le_self` replaces it by
the tensor's; neither half gives this alone. -/
theorem ip_weylPart_abs_le (hn0 : (n : ℝ) ≠ 0) (hn1 : (n : ℝ) - 1 ≠ 0) (hn2 : (n : ℝ) - 2 ≠ 0)
    {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R)
    (S : Fin n → Fin n → Fin n → Fin n → ℝ) :
    |ip (weylPart R) S| ≤ Real.sqrt (ip R R) * Real.sqrt (ip S S) := by
  refine (ip_abs_le (weylPart R) S).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  exact Real.sqrt_le_sqrt (ip_weylPart_le_self hn0 hn1 hn2 hR)

end LovelockInnerSpace
