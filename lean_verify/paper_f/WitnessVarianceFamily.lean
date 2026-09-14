/-
  WitnessVarianceFamily.lean — the variance bound for the WHOLE one-column
  family, not for one observable.

  WHY THIS FILE EXISTS. `WitnessVarianceUniform`'s "What this does NOT do" says,
  in its own words:

  > It bounds the variance of ONE observable, `absCoordField v`, and says
  > nothing about **a family of them**.

  This file removes that restriction, and the removal costs nothing because the
  proof never used the observable. What it used is the SHAPE of the Stein tuple:
  `γ j ω = ((√G)⁻¹) j v · s ω`, one column of `(√G)⁻¹` scaled by a bounded
  factor. The sign function was the only bounded factor to hand on 2026-08-29;
  it is not the only one.

  AND THE SAME REMOVAL, DONE WITH THE OPERATOR NORM INSTEAD OF THE COLUMN,
  IS THE STEP `UNLOCK_WATCHLIST`'s volume-uniform item has called its residue
  since 2 September: *"threading the bound into `LatticeUniformStein`'s
  pointwise `ℓ²` gradient constant. Not attempted, not costed, not estimated."*
  §2b is that threading.

  WHAT THIS FILE PROVES.

  1. **`var_le_of_columnTuple`** — for ANY Stein pair against the field whose
     tuple is `column v` times a factor bounded by `B`, the variance is at most
     `m⁻²·B²·(deg v + m²)`, at every finite graph. The hypothesis names the
     tuple's shape and nothing about the observable.
  2. `var_le_of_columnTuple_of_degree`, **`var_le_of_columnTuple_boxGraph`** —
     the same under a degree bound and on the `d`-dimensional box, where the
     constant is `m⁻²·B²·(2d + m²)` **at every side length**.
  3. **`var_le_of_gradient_norm`** — the NORM route, and the residue above.
     `SqrtGreenOpNorm.norm_inv_sqrt_green_le_of_le` turns a Loewner floor
     `c⁻¹ • 1 ≼ green` into `‖(√G)⁻¹‖ ≤ √c`; `gradient_sq_le_of_norm` spends
     that inside the pointwise `ℓ²` constant, and the tuple may now be `(√G)⁻¹`
     applied to ANY bounded vector field — the case a column identity cannot
     reach. **`var_le_of_gradient_norm_boxGraph`**: `m⁻²·(4d + m²)·L²` at every
     side length `n ≥ 1`.
  4. **`absCoordField_var_le_of_family`** — and `WitnessVarianceUniform`'s
     theorem back out of §1, at `s = sgn(…)` and `B = 1`. The specialisation is
     PROVED and not asserted, which is the same discipline
     `MvPolynomialFDeriv.fderiv_eval_single_of_apply` follows and which
     `ERRATUM 548` is the entry about.

  **THE TWO ROUTES ARE INCOMPARABLE, NOT ORDERED.** §1 is sharper where it
  applies — `2d + m²` against §2b's `4d + m²` on the box, because
  `sqrtGreenInv_col_sq` is an equality and a norm bound is not. §2b applies
  where §1 cannot, because it does not need the tuple to be one column. This is
  the same trade `SqrtGreenOpNorm.col_sq_le_of_le`'s own docstring records when
  it calls itself *"a consistency check and not an improvement"*.

  WHAT THIS DOES NOT DO. **IT DOES NOT CLOSE THE WATCHLIST ITEM**, and that is
  deliberate rather than cautious: that item's 2 September STATUS says in its own
  words that *nothing is marked closed on my initiative* and that whether an item
  in its position counts as closed is `ASSUMPTIONS_LEDGER` **51**, under
  DECISIONS NEEDED. §2b supplies the step the item names and leaves the ruling to
  the author. **`WitnessVarianceUniform` is not withdrawn** — it proves its
  theorem directly, holds the column identity that is the real content of both,
  and is the file a reader of that chain has in hand. **NEITHER FAMILY HAS A SECOND
  INHABITANT HERE**: `SteinPairField` is produced by exactly three theorems in
  this estate and only `LatticeFieldWitness.absCoordField_steinPairField` has a
  tuple of either shape, so what is added is generality with one inhabitant. §4
  gives the count, the query behind it, and why no second is manufactured.
  **`OS4` does not move**, for the reason it has not moved throughout this
  chain: a constant that does not blow up is an ingredient of a tightness
  argument and not one. **No published tag moves.**

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import WitnessVarianceUniform
import SqrtGreenOpNorm

namespace WitnessVarianceFamily

open MeasureTheory Matrix GraphLaplacian
open LatticeSqrtEquiv LatticeFieldProduct LatticeFieldWitness LatticeUniformStein
open LatticeCorrelatedStein
open AbsSteinWitness WitnessVarianceUniform
open scoped MatrixOrder

variable {W : Type*} [Fintype W] [DecidableEq W] {K : SimpleGraph W}
  [DecidableRel K.Adj] {m : ℝ}

/-! ## 1. The family -/

/-- The pointwise `ℓ²` bound `LatticeUniformStein.poincare_uniform_stein_of_bounded`
consumes, for a tuple that is one column of `(√G)⁻¹` times a bounded factor.
`sqrtGreenInv_col_sq` makes the column's contribution an EQUALITY; the factor
contributes `B²`. -/
theorem columnTuple_sq_le (hm : m ≠ 0) (v : W) {s : EuclideanSpace ℝ W → ℝ}
    {B : ℝ} (hs : ∀ ω, |s ω| ≤ B) (ω : EuclideanSpace ℝ W) :
    ∑ j, ((CFC.sqrt (green K m))⁻¹ j v * s ω) ^ 2
      ≤ B ^ 2 * ((K.degree v : ℝ) + m ^ 2) := by
  classical
  have hsq : (s ω) ^ 2 ≤ B ^ 2 := by
    have h := hs ω
    nlinarith [abs_nonneg (s ω), sq_abs (s ω)]
  have hcol : ∑ j, ((CFC.sqrt (green K m))⁻¹ j v * s ω) ^ 2
      = (∑ j, ((CFC.sqrt (green K m))⁻¹ j v) ^ 2) * (s ω) ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_pow]
  rw [hcol, sqrtGreenInv_col_sq (K := K) hm v, mul_comm]
  have hnn : (0 : ℝ) ≤ (K.degree v : ℝ) + m ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_right hsq hnn

/-- **THE FAMILY BOUND.** Every Stein pair against the field whose tuple is the
`v`-th column of `(√G)⁻¹` scaled by a factor bounded by `B` has variance at most
`m⁻²·B²·(deg v + m²)` — at every finite graph, with no hypothesis on the
observable beyond membership. -/
theorem var_le_of_columnTuple (hm : m ≠ 0) (v : W)
    {Φ : EuclideanSpace ℝ W → ℝ} {s : EuclideanSpace ℝ W → ℝ} {B : ℝ}
    (hs : ∀ ω, |s ω| ≤ B)
    (h : SteinPairField K m Φ
      (fun j ω => (CFC.sqrt (green K m))⁻¹ j v * s ω)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m))
        - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * (B ^ 2 * ((K.degree v : ℝ) + m ^ 2)) := by
  classical
  have hnn : (0 : ℝ) ≤ B ^ 2 * ((K.degree v : ℝ) + m ^ 2) := by positivity
  have hL : ∀ ω, ∑ j, ((CFC.sqrt (green K m))⁻¹ j v * s ω) ^ 2
      ≤ (Real.sqrt (B ^ 2 * ((K.degree v : ℝ) + m ^ 2))) ^ 2 := by
    intro ω
    rw [Real.sq_sqrt hnn]
    exact columnTuple_sq_le (K := K) hm v hs ω
  have hmain := poincare_uniform_stein_of_bounded (K := K) hm h hL
  rwa [Real.sq_sqrt hnn] at hmain

/-! ## 2. And the box does not see the side length -/

/-- Under a degree bound the constant loses the vertex, exactly as it does for
the single observable. -/
theorem var_le_of_columnTuple_of_degree (hm : m ≠ 0) {Δ : ℝ}
    (hΔ : ∀ p : W, (K.degree p : ℝ) ≤ Δ) (v : W)
    {Φ : EuclideanSpace ℝ W → ℝ} {s : EuclideanSpace ℝ W → ℝ} {B : ℝ}
    (hs : ∀ ω, |s ω| ≤ B)
    (h : SteinPairField K m Φ
      (fun j ω => (CFC.sqrt (green K m))⁻¹ j v * s ω)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m))
        - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * (B ^ 2 * (Δ + m ^ 2)) := by
  refine (var_le_of_columnTuple (K := K) hm v hs h).trans ?_
  have hpos : (0 : ℝ) ≤ (m ^ 2)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  have hB : (0 : ℝ) ≤ B ^ 2 := sq_nonneg B
  exact mul_le_mul_of_nonneg_left (by linarith [hΔ v]) hB

open BoxGraph BoxDegree in
/-- **THE FAMILY BOUND ON THE BOX**, at every side length: `m⁻²·B²·(2d + m²)`,
naming the dimension, the mass and the factor's bound and nothing else. -/
theorem var_le_of_columnTuple_boxGraph (d n : ℕ) {m : ℝ} (hm : m ≠ 0)
    (v : Site d n) {Φ : EuclideanSpace ℝ (Site d n) → ℝ}
    {s : EuclideanSpace ℝ (Site d n) → ℝ} {B : ℝ} (hs : ∀ ω, |s ω| ≤ B)
    (h : SteinPairField (boxGraph d n) m Φ
      (fun j ω => (CFC.sqrt (green (boxGraph d n) m))⁻¹ j v * s ω)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField (boxGraph d n) m))
        - (∫ ω, Φ ω ∂(gaussianField (boxGraph d n) m)) ^ 2
      ≤ (m ^ 2)⁻¹ * (B ^ 2 * (2 * (d : ℝ) + m ^ 2)) := by
  refine var_le_of_columnTuple_of_degree hm (fun p => ?_) v hs h
  have hb := boxGraph_degree_le (d := d) (n := n) p
  have : ((boxGraph d n).degree p : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by exact_mod_cast hb
  simpa using this

/-! ## 2b. The NORM route — the threading the watchlist item names -/

/-- The pointwise `ℓ²` bound for a tuple that is `(√G)⁻¹` applied to a BOUNDED
VECTOR FIELD rather than to one column. This is where the operator norm does
work the column identity cannot: `u ω` is allowed to point anywhere. -/
theorem gradient_sq_le_of_norm [Nonempty W] {c : ℝ} (hpos : 0 < c) (hm : m ≠ 0)
    (hg : c⁻¹ • (1 : Matrix W W ℝ) ≤ green K m)
    (y : EuclideanSpace ℝ W) :
    ∑ j, (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp y)) j) ^ 2 ≤ c * ‖y‖ ^ 2 := by
  classical
  set A := (CFC.sqrt (green K m))⁻¹ with hA
  have hb := PosSemidefNormBound.norm_mulVec_le
    (SqrtGreenOpNorm.nonneg_inv_sqrt_green_of_le K hpos hm hg)
    (SqrtGreenBound.inv_sqrt_green_le_of_le K hpos hm hg) y
  have hsq := PosSemidefNormBound.norm_sq_eq_dotProduct
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) y)
  rw [Matrix.ofLp_toEuclideanCLM] at hsq
  have hdot : (A *ᵥ (WithLp.ofLp y)) ⬝ᵥ (A *ᵥ (WithLp.ofLp y))
      = ∑ j, ((A *ᵥ (WithLp.ofLp y)) j) ^ 2 := by
    simp [dotProduct, pow_two]
  rw [hdot] at hsq
  have hnn : (0 : ℝ) ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A) y‖ := norm_nonneg _
  nlinarith [hb, hsq, hnn, Real.sq_sqrt hpos.le, Real.sqrt_nonneg c, norm_nonneg y]

/-- **THE THREADING THE ITEM ASKS FOR.** `SqrtGreenOpNorm.norm_inv_sqrt_green_le_of_le`
turns a Loewner floor on `green` into an operator-norm bound on `(√G)⁻¹`; this
spends that bound inside `LatticeUniformStein`'s pointwise `ℓ²` gradient
constant. The tuple may be `(√G)⁻¹` applied to ANY bounded vector field, which
is the case §1 cannot reach. -/
theorem var_le_of_gradient_norm [Nonempty W] {c : ℝ} (hpos : 0 < c) (hm : m ≠ 0)
    (hg : c⁻¹ • (1 : Matrix W W ℝ) ≤ green K m)
    {Φ : EuclideanSpace ℝ W → ℝ}
    {u : EuclideanSpace ℝ W → EuclideanSpace ℝ W} {L : ℝ}
    (hu : ∀ ω, ‖u ω‖ ≤ L)
    (h : SteinPairField K m Φ
      (fun j ω => ((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp (u ω))) j)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField K m))
        - (∫ ω, Φ ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * (c * L ^ 2) := by
  classical
  have hL2 : (0 : ℝ) ≤ L := le_trans (norm_nonneg _) (hu (0 : EuclideanSpace ℝ W))
  have hnn : (0 : ℝ) ≤ c * L ^ 2 := by positivity
  have hL : ∀ ω, ∑ j, (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp (u ω))) j) ^ 2
      ≤ (Real.sqrt (c * L ^ 2)) ^ 2 := by
    intro ω
    rw [Real.sq_sqrt hnn]
    refine (gradient_sq_le_of_norm (K := K) hpos hm hg (u ω)).trans ?_
    have h2 : ‖u ω‖ ^ 2 ≤ L ^ 2 := by nlinarith [norm_nonneg (u ω), hu ω]
    exact mul_le_mul_of_nonneg_left h2 hpos.le
  have hmain := poincare_uniform_stein_of_bounded (K := K) hm h hL
  rwa [Real.sq_sqrt hnn] at hmain

open BoxGraph in
/-- **AND ON THE BOX IT DOES NOT SEE THE SIDE LENGTH EITHER**: `m⁻²·(4d + m²)·L²`
for every `n ≥ 1`. The `4d` rather than `2d` is the price of the norm: on a
tuple that is one column, §1's exact identity is strictly sharper, and the two
routes are incomparable rather than ordered. -/
theorem var_le_of_gradient_norm_boxGraph (d : ℕ) {n : ℕ} (hn : 1 ≤ n) {m : ℝ}
    (hm : m ≠ 0) {Φ : EuclideanSpace ℝ (Site d n) → ℝ}
    {u : EuclideanSpace ℝ (Site d n) → EuclideanSpace ℝ (Site d n)} {L : ℝ}
    (hu : ∀ ω, ‖u ω‖ ≤ L)
    (h : SteinPairField (boxGraph d n) m Φ
      (fun j ω => ((CFC.sqrt (green (boxGraph d n) m))⁻¹ *ᵥ (WithLp.ofLp (u ω))) j)) :
    (∫ ω, Φ ω * Φ ω ∂(gaussianField (boxGraph d n) m))
        - (∫ ω, Φ ω ∂(gaussianField (boxGraph d n) m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ((4 * (d : ℝ) + m ^ 2) * L ^ 2) := by
  haveI : Nonempty (Site d n) := ⟨fun _ => ⟨0, hn⟩⟩
  have hpos : (0 : ℝ) < 4 * (d : ℝ) + m ^ 2 := by positivity
  refine var_le_of_gradient_norm hpos hm ?_ hu h
  exact LaplacianDegreeBound.smul_one_le_green_boxGraph d n hm

/-! ## 3. The witness is the `s = sgn` member -/

/-- **`WitnessVarianceUniform.absCoordField_var_le`, DERIVED.** The sign is a
factor bounded by `1`, so the single-observable theorem is the family theorem at
`B = 1`. Proved rather than asserted: the claim that a general statement
subsumes a special one is itself a claim (`ERRATUM 548`). -/
theorem absCoordField_var_le_of_family (hm : m ≠ 0) (v : W) :
    (∫ ω, absCoordField K m v ω * absCoordField K m v ω ∂(gaussianField K m))
        - (∫ ω, absCoordField K m v ω ∂(gaussianField K m)) ^ 2
      ≤ (m ^ 2)⁻¹ * ((K.degree v : ℝ) + m ^ 2) := by
  have h := var_le_of_columnTuple (K := K) (v := v) (B := 1) hm
    (s := fun ω => sgn (((CFC.sqrt (green K m))⁻¹ *ᵥ (WithLp.ofLp ω)) v))
    (fun ω => abs_sgn_le _)
    (absCoordField_steinPairField (K := K) hm v)
  simpa [one_pow, one_mul] using h

/-! ## 4. Review round 72 — the ways this could be hollow

**"A family with one member is not a family."** Correct, and the header says so
rather than leaving it to be noticed. The estate has exactly one Stein pair of
this shape, `absCoordField v`, and §3 derives its bound. What §1 adds is that
the bound never depended on the observable: `WitnessVarianceUniform`'s proof
reads the tuple, bounds the sign by `1`, and computes the column — and the first
two of those three steps work for any bounded factor.

**"So name the second member."** The nearest one is the LINEAR observable
`ω ↦ ((√G)⁻¹ ω) v`, whose tuple is the same column at `s ≡ 1`. It is **not
written here** because its `SteinPairField` membership is a separate proof —
the pair transported through `sqrtMapOf` is the coordinate `y ↦ y v` against
`SteinPairOf`, and this estate's coordinate Stein pairs are stated for
`gaussPi`, not for `SteinPairOf W`. That is a unit and not a corollary, and
inventing it here to make a family look populated is the thing `ERRATUM 246`
is about.

**"This makes the earlier theorem redundant."** It makes it a corollary. The
earlier file proves it directly, is the one a reader of that chain has in hand,
and is where the column identity `sqrtGreenInv_col_sq` — the actual content of
both — lives. Nothing here reproves it.

**"The generality is free, so the earlier file should have had it."** Yes, and
that is the honest reading: the restriction to one observable was not a
decision, it was the shape of the day's application. §1's hypothesis is what
that proof actually used, read off it afterwards.

**"§2b should have closed the item."** It supplies the step the item names, and
the item is left open on purpose. Its own 2 September STATUS declines to close
it *on my initiative* and routes the question to `ASSUMPTIONS_LEDGER` 51 under
DECISIONS NEEDED, so closing it here would be answering a question already
handed to the author.

**"§2b is what §1 already did."** It is not, and the difference is which object
is bounded. §1 bounds `∑ⱼ (γⱼ ω)²` by computing ONE COLUMN of `(√G)⁻¹` exactly;
§2b bounds it by the operator norm applied to an arbitrary vector. Neither
implies the other: on the box §1 gives `2d + m²` where §2b gives `4d + m²`, and
§2b covers tuples §1 has no statement about. **A reader who has only the
watchlist's summary of this item will think one of these is the other**, which
is how this file's author read it first.

**"`OS4`."** Unmoved. A variance bound uniform in the box is an ingredient of a
tightness argument; no sequence of measures, no limit and no compactness appears
in this file or in the one below it.
-/

end WitnessVarianceFamily
