/-
  ConfigSpread.lean — carrying a finite-volume bound into the ambient space, without making the
  author's choice.

  WHY. `FieldTightness` grades the three things between this estate and tightness; `ConfigSpace`
  built the carrier, so item (2) is all that is left:

  > 2. **A pushforward of each finite-volume field into it** — extend a field on a box or a torus to
  >    all of `ℤ^d`. **This is a choice, not a construction**, and it is `ASSUMPTIONS_LEDGER` 47, an
  >    author's decision. By zero and by periodic repetition give different limits.

  **THE CHOICE IS REAL AND IT IS NOT NEEDED FOR TIGHTNESS.** Both candidates — extend by zero, and
  repeat periodically — are placements of the same shape: *each ambient site either carries a
  finite-volume site or carries nothing*, which is a map `ι → Option V`. Extension by zero sends
  sites outside the box to `none`; periodic repetition sends every ambient site to `some` of its
  residue, and **many ambient sites to the same one**, which the `Option` form allows because it
  never asks the placement to be injective. So this file proves the transfer for **an arbitrary
  placement**, and the author's decision moves from *"which construction"* to *"which placement the
  estate's narrative uses"* — a choice between two instances of one theorem rather than between two
  theorems.

  WHAT IS PROVED.

  * `spread π ev` — the placement, acting on any measurable space with measurable site
    evaluations, so it applies to `EuclideanSpace ℝ V` (where `gaussianField` lives) and to
    `V → ℝ` alike; `measurable_spread`;
  * **`map_spread_site_none`** — at an ambient site carrying nothing the pushed-forward field is
    `0`, so its exceptional set is null for every nonnegative radius. **This is where extension by
    zero pays**: outside the volume there is no tail to bound;
  * **`map_spread_site_some`** — at an ambient site carrying `v` the exceptional set is exactly the
    finite-volume one at `v`. An equality, not an estimate;
  * **`isTightMeasureSet_map_spread`** — a family of finite-volume measures with uniform per-site
    tail bounds, placed by arbitrary placements, is tight on `Config ι`. The volumes may differ
    from member to member, in vertex type as well as in size.

  WHAT IS STILL NOT DONE, AND IT IS NOT THIS. The hypothesis is a *uniform* per-site bound with a
  summable weight, and `FieldTightness.meas_abs_ge_radius_le` supplies the per-site half at every
  finite graph at once. **Choosing the weight and the placements for a particular sequence of
  boxes is the author's `ASSUMPTIONS 47`**, and nothing here chooses them. **And it still would not
  close W2's leg**: compactness gives *a* limit, and identifying it needs `G_n → G`.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import ConfigSpace

namespace ConfigSpread

open MeasureTheory Set ConfigSpace

noncomputable section

variable {ι : Type*}

/-! ## 1. The placement -/

/-- **A PLACEMENT**: each ambient site either carries a finite-volume site or carries nothing.
Extension by zero and periodic repetition are both of this shape; the second is why the placement
is not required to be injective. -/
def spread {V Ω : Type*} (π : ι → Option V) (ev : V → Ω → ℝ) (w : Ω) : Config ι :=
  fun x => (π x).elim 0 fun v => ev v w

@[simp] theorem spread_apply_none {V Ω : Type*} (π : ι → Option V) (ev : V → Ω → ℝ) (w : Ω)
    {x : ι} (h : π x = none) : spread π ev w x = 0 := by
  simp [spread, h]

@[simp] theorem spread_apply_some {V Ω : Type*} (π : ι → Option V) (ev : V → Ω → ℝ) (w : Ω)
    {x : ι} {v : V} (h : π x = some v) : spread π ev w x = ev v w := by
  simp [spread, h]

theorem measurable_spread {V Ω : Type*} [MeasurableSpace Ω] (π : ι → Option V)
    {ev : V → Ω → ℝ} (hev : ∀ v, Measurable (ev v)) : Measurable (spread π ev) := by
  refine measurable_pi_lambda _ fun x => ?_
  cases hx : π x with
  | none => simp [spread, hx]
  | some v => simpa [spread, hx] using hev v

/-! ## 2. What one ambient site sees -/

/-- The exceptional set at one ambient site is measurable — used twice below, and stated once. -/
theorem measurableSet_site_tail (x : ι) (a : ℝ) :
    MeasurableSet {ω : Config ι | a < |ω x|} := by
  have habs : Measurable fun t : ℝ => |t| := continuous_abs.measurable
  exact measurableSet_lt measurable_const (habs.comp (measurable_pi_apply x))

/-- **AN AMBIENT SITE CARRYING NOTHING HAS NO TAIL.** The pushed-forward field is `0` there, so for
any nonnegative radius the exceptional set is null — and that is the whole of what extension by
zero contributes. -/
theorem map_spread_site_none {V Ω : Type*} [MeasurableSpace Ω] (π : ι → Option V)
    {ev : V → Ω → ℝ} (hev : ∀ v, Measurable (ev v)) (μ : Measure Ω)
    {x : ι} (hx : π x = none) {a : ℝ} (ha : 0 ≤ a) :
    (μ.map (spread π ev)) {ω : Config ι | a < |ω x|} = 0 := by
  have hmeas : MeasurableSet {ω : Config ι | a < |ω x|} := measurableSet_site_tail x a
  rw [Measure.map_apply (measurable_spread π hev) hmeas]
  convert measure_empty (μ := μ)
  ext w
  simp only [mem_preimage, mem_setOf_eq, spread_apply_none π ev w hx, abs_zero, mem_empty_iff_false,
    iff_false, not_lt]
  exact ha

/-- **AN AMBIENT SITE CARRYING `v` SEES EXACTLY `v`'s TAIL.** An equality, so nothing is lost in
the transfer. -/
theorem map_spread_site_some {V Ω : Type*} [MeasurableSpace Ω] (π : ι → Option V)
    {ev : V → Ω → ℝ} (hev : ∀ v, Measurable (ev v)) (μ : Measure Ω)
    {x : ι} {v : V} (hx : π x = some v) (a : ℝ) :
    (μ.map (spread π ev)) {ω : Config ι | a < |ω x|} = μ {w : Ω | a < |ev v w|} := by
  have hmeas : MeasurableSet {ω : Config ι | a < |ω x|} := measurableSet_site_tail x a
  rw [Measure.map_apply (measurable_spread π hev) hmeas]
  congr 1
  ext w
  simp [spread_apply_some π ev w hx]

/-! ## 3. Tightness of a placed family

The volumes may differ from member to member — in vertex type as well as in size — which is what
`Λ`-indexed `V` and `Ω` are for. -/

/-- **A FAMILY OF FINITE-VOLUME MEASURES WITH UNIFORM PER-SITE TAIL BOUNDS, PLACED ANY WAY AT ALL,
IS TIGHT.** The placement is arbitrary: extension by zero and periodic repetition are two of its
instances, and the theorem does not distinguish them. -/
theorem isTightMeasureSet_map_spread [Countable ι]
    {Λ : Type*} {V Ω : Λ → Type*} [∀ l, MeasurableSpace (Ω l)]
    (μ : ∀ l, Measure (Ω l)) (π : ∀ l, ι → Option (V l)) (ev : ∀ l, V l → Ω l → ℝ)
    (hev : ∀ l v, Measurable (ev l v))
    (r : ENNReal → ι → ℝ) (hr : ∀ ε x, 0 ≤ r ε x)
    (w : ι → ENNReal) (hw : ∑' x, w x ≤ 1)
    (h : ∀ ε : ENNReal, 0 < ε → ∀ l, ∀ x : ι, ∀ v : V l, π l x = some v →
      (μ l) {y : Ω l | r ε x < |ev l v y|} ≤ w x * ε) :
    IsTightMeasureSet (Set.range fun l => (μ l).map (spread (π l) (ev l))) := by
  refine isTightMeasureSet_of_site_tail r w hw ?_
  rintro ε hε ν ⟨l, rfl⟩ x
  cases hx : π l x with
  | none =>
      rw [map_spread_site_none (π l) (hev l) (μ l) hx (hr ε x)]
      exact zero_le _
  | some v =>
      rw [map_spread_site_some (π l) (hev l) (μ l) hx]
      exact h ε hε l x v hx

end

end ConfigSpread
