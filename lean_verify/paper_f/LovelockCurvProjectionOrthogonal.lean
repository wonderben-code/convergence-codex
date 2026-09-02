import LovelockInnerSpace
import LovelockCurvProjectionUnique

/-!
# The hand-built projection is Mathlib's orthogonal projection

`LovelockCurvProjection` built `curvProj` — antisymmetrise, symmetrise the pair swap, subtract the
cyclic part — and said what it was not:

> no `Submodule`, no `orthogonalProjection` instance, no uniqueness statement.

`LovelockCurvProjectionUnique` closed the third clause and repeated the other two: *"And it is
still not a bundled projection. No `Submodule`, no `orthogonalProjection`."* **Both were blocked on
the same thing — there was no inner-product space for a submodule to sit in.**
`LovelockInnerSpace.arrEquiv` supplies one, so this file closes them.

## What is proved

* **`algCurv`** — the algebraic curvature tensors as a `Submodule ℝ (EuclideanSpace ℝ (ArrIdx n))`.
  The content is `LovelockProjections`' three closure lemmas; the submodule is the packaging;
* **`inner_sub_curvProj`** — `A − curvProj A` is orthogonal to every algebraic curvature tensor.
  This is `LovelockCurvProjection.ip_curvProj` read through `inner_arrEquiv`, and it is the
  hypothesis both theorems below need;
* **`starProjection_arrEquiv`** — **`curvProj` IS Mathlib's orthogonal projection onto `algCurv`.**
  Not "behaves like": the two functions are equal, by Mathlib's own characterisation of its
  projection as the unique member of the subspace whose difference is orthogonal to it;
* **`norm_curvProj_le`** — projecting to algebraic curvature never increases length;
* **`curvProj_minimal`** — **`curvProj A` is the CLOSEST algebraic curvature tensor to `A`.**

## Why the last one is the point (`ERRATUM 48`)

**A construction that produces no new member has its usefulness merely asserted.** `curvProj` was
built by algebra and characterised by a pairing identity; **nothing said it was a best
approximation**, and nothing in the estate could say it, because "closest" needs a metric.
`curvProj_minimal` is that statement, and its proof is Pythagoras against `inner_sub_curvProj` —
available only once the carrier exists. `norm_curvProj_le` is the same fact in the special case
`B = 0`, kept separately because it is the one a bound would cite.

## What this does not do

**It is not a claim about `KillsWeyl`**, and the watchlist item does not move: every theorem here
says the projection is canonical, which is what `LovelockCurvProjectionUnique` already said of
itself in a different vocabulary. **And no instance is placed on the array type** —
`LovelockInnerSpace`'s decision stands, so the estate's own statements about `curvProj` are still
statements about the bare form, and this file is the bridge rather than a replacement.


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

namespace LovelockCurvProjectionOrthogonal

open AlgebraicCurvature LovelockProjections LovelockOrthogonality LovelockInnerSpace
  LovelockCurvProjection

variable {n : ℕ}

/-! ## 1. The submodule -/

/-- **THE ALGEBRAIC CURVATURE TENSORS AS A SUBMODULE.** The three closure lemmas are
`LovelockProjections`'; this is only the packaging, and it is the packaging that was missing. -/
def algCurv (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (ArrIdx n)) where
  carrier := {x | IsAlgCurv ((arrEquiv n).symm x)}
  zero_mem' := isAlgCurv_zero
  add_mem' hx hy := isAlgCurv_add hx hy
  smul_mem' c _ hx := isAlgCurv_smul c hx

@[simp] theorem mem_algCurv {x : EuclideanSpace ℝ (ArrIdx n)} :
    x ∈ algCurv n ↔ IsAlgCurv ((arrEquiv n).symm x) := Iff.rfl

theorem arrEquiv_mem_algCurv {R : Fin n → Fin n → Fin n → Fin n → ℝ} (hR : IsAlgCurv R) :
    arrEquiv n R ∈ algCurv n := hR

instance : (algCurv n).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-! ## 2. The orthogonality, which is `ip_curvProj` read through the identification -/

/-- **`A − curvProj A` IS ORTHOGONAL TO EVERY ALGEBRAIC CURVATURE TENSOR.** -/
theorem inner_sub_curvProj (A : Fin n → Fin n → Fin n → Fin n → ℝ)
    {w : EuclideanSpace ℝ (ArrIdx n)} (hw : w ∈ algCurv n) :
    inner ℝ (arrEquiv n A - arrEquiv n (curvProj A)) w = 0 := by
  have hwe : w = arrEquiv n ((arrEquiv n).symm w) := ((arrEquiv n).apply_symm_apply w).symm
  rw [inner_sub_left, hwe, inner_arrEquiv, inner_arrEquiv, sub_eq_zero]
  exact (ip_curvProj hw A).symm

/-! ## 3. The identification -/

/-- **`curvProj` IS MATHLIB'S ORTHOGONAL PROJECTION ONTO `algCurv`.** -/
theorem starProjection_arrEquiv (A : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (algCurv n).starProjection (arrEquiv n A) = arrEquiv n (curvProj A) :=
  Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (arrEquiv_mem_algCurv (isAlgCurv_curvProj A))
    (fun _ hw => inner_sub_curvProj A hw)

/-! ## 4. What the identification buys -/

/-- **`curvProj A` IS THE CLOSEST ALGEBRAIC CURVATURE TENSOR TO `A`.** Nothing in the estate could
state this before: "closest" needs a metric, and `curvProj` was characterised by a pairing
identity. Pythagoras against `inner_sub_curvProj`. -/
theorem curvProj_minimal (A : Fin n → Fin n → Fin n → Fin n → ℝ)
    {B : Fin n → Fin n → Fin n → Fin n → ℝ} (hB : IsAlgCurv B) :
    ‖arrEquiv n A - arrEquiv n (curvProj A)‖ ≤ ‖arrEquiv n A - arrEquiv n B‖ := by
  set u := arrEquiv n A
  set P := arrEquiv n (curvProj A)
  set b := arrEquiv n B
  have hmem : P - b ∈ algCurv n :=
    Submodule.sub_mem _ (arrEquiv_mem_algCurv (isAlgCurv_curvProj A)) (arrEquiv_mem_algCurv hB)
  have hsplit : u - b = (u - P) + (P - b) := by abel
  have hpy : ‖u - b‖ * ‖u - b‖ = ‖u - P‖ * ‖u - P‖ + ‖P - b‖ * ‖P - b‖ := by
    rw [hsplit]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_real (inner_sub_curvProj A hmem)
  nlinarith [norm_nonneg (u - P), norm_nonneg (u - b), norm_nonneg (P - b),
    mul_self_nonneg ‖P - b‖]

/-- **PROJECTING TO ALGEBRAIC CURVATURE NEVER INCREASES LENGTH.** This is **not**
`curvProj_minimal` at `B = 0` — that reads `‖A − curvProj A‖ ≤ ‖A‖`, about the *remainder*. Both
are halves of the one Pythagoras identity `‖A‖² = ‖A − curvProj A‖² + ‖curvProj A‖²`, and this is
the half a bound cites. The length is `√(ip R R)` by `LovelockInnerSpace.norm_arrEquiv`. -/
theorem norm_curvProj_le (A : Fin n → Fin n → Fin n → Fin n → ℝ) :
    ‖arrEquiv n (curvProj A)‖ ≤ ‖arrEquiv n A‖ := by
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real
    (inner_sub_curvProj A (arrEquiv_mem_algCurv (isAlgCurv_curvProj A)))
  have h : arrEquiv n A - arrEquiv n (curvProj A) + arrEquiv n (curvProj A) = arrEquiv n A := by
    abel
  rw [h] at hpy
  nlinarith [norm_nonneg (arrEquiv n A), norm_nonneg (arrEquiv n (curvProj A)),
    mul_self_nonneg ‖arrEquiv n A - arrEquiv n (curvProj A)‖]

end LovelockCurvProjectionOrthogonal
