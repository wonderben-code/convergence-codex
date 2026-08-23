/-
  ConfigSpace.lean — the carrier `FieldTightness` said was missing, and the tightness criterion
  its bounds feed.

  WHY. `FieldTightness`'s header names three things standing between this estate and a tightness
  statement, and grades them honestly:

  > 1. **A single space** — `Π _ : ℤ^d, ℝ` … **is not defined anywhere in this estate**.
  > 2. **A pushforward of each finite-volume field into it** … **This is a choice, not a
  >    construction**, and it is `ASSUMPTIONS_LEDGER` 47, an author's decision.
  > 3. **The union bound over sites** … provable in finite volume right now.

  (3) is done — `FieldTightness.meas_exists_abs_ge_radius_le_of_sum_le`, with the constant `∑ₓ wₓ`
  and nothing else about the graph. (2) belongs to the author. **(1) is a construction nobody had
  made, and it is not blocked by (2)**, which is why this file exists: it removes the piece that is
  neither done nor a decision, and leaves exactly the decision.

  WHAT IS BUILT.

  * `cube a` — the configurations bounded by `a x` at each site. `cube_eq_pi` identifies it with a
    product of intervals and **`isCompact_cube` is Tychonoff**: compact for EVERY index type, with
    no countability, no metric and no bound on `a`. That is the shape the estate's tail bounds
    produce, and the reason they produce a compact set rather than merely a small one;
  * `compl_cube` — its complement is `{ω | ∃ x, a x < |ω x|}`, **which is the set
    `FieldTightness`'s union bound is stated about**, verbatim;
  * **`isTightMeasureSet_of_tail`** — a family of measures with per-site tail bounds of that exact
    shape is tight **in Mathlib's sense** (`MeasureTheory.IsTightMeasureSet`). Not a private
    notion: the conclusion is the hypothesis of Mathlib's Prokhorov machinery;
  * `isTightMeasureSet_of_tail_radius` — the same with the radius supplied as a function of the
    tolerance, which is the quantifier order an infinite-volume argument needs and the one
    `FieldTightness.radius` was defined to have;
  * `measure_exists_le_tsum` and **`isTightMeasureSet_of_site_tail`** — the union bound on a
    countable site set, and the criterion in the form the estate can actually feed it: **Chebyshev
    bounds one site at a time**, a summable weight distributes the tolerance, and `∑ₓ wₓ ≤ 1` is
    the only global hypothesis. `FieldTightness` §4 is this argument in finite volume with
    `Finset.sum`; here it is `tsum`, and nothing else changes.

  WHAT THIS IS NOT. **It is not tightness of the lattice field, and nothing here mentions a
  graph.** The criterion takes tail bounds and returns tightness; the estate has tail bounds on
  `EuclideanSpace ℝ V`, one space per graph, and carrying them here is (2). **After this file the
  only thing between `FieldTightness` and a tightness theorem is an author's decision**, which is
  a smaller sentence than the one that file could write.

  AND IT WOULD STILL NOT CLOSE W2'S LEG. `FieldTightness` says so and it is still true:
  compactness produces *a* limit measure, and showing it is the `ℤ^d` free field needs
  `G_n(x,y) → G(x,y)`, which nothing here touches.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Compactness.Compact

namespace ConfigSpace

open MeasureTheory Set

noncomputable section

variable {ι : Type*}

/-! ## 1. The carrier and its compact sets

`Config ι` is `ι → ℝ` with the product topology and the product σ-algebra — both instances Mathlib
supplies, which is the whole reason the header calls this a construction rather than a theory. -/

/-- **The configuration space**: one real number per site. -/
abbrev Config (ι : Type*) : Type _ := ι → ℝ

/-- The configurations bounded by `a x` at every site `x`. -/
def cube (a : ι → ℝ) : Set (Config ι) := {ω | ∀ x, |ω x| ≤ a x}

theorem cube_eq_pi (a : ι → ℝ) :
    cube a = Set.univ.pi fun x => Set.Icc (-a x) (a x) := by
  ext ω
  simp only [cube, mem_setOf_eq, mem_univ_pi, mem_Icc, abs_le]

/-- **THE CUBE IS COMPACT, FOR EVERY INDEX TYPE.** Tychonoff, and nothing else: no countability,
no metric, no bound on `a`. If some `a x` is negative the cube is empty, which is compact too. -/
theorem isCompact_cube (a : ι → ℝ) : IsCompact (cube a) := by
  rw [cube_eq_pi]
  exact isCompact_univ_pi fun x => isCompact_Icc

theorem isClosed_cube (a : ι → ℝ) : IsClosed (cube a) := by
  rw [cube_eq_pi]
  exact isClosed_set_pi fun x _ => isClosed_Icc

/-- **AND ITS COMPLEMENT IS THE SET THE ESTATE'S UNION BOUND IS ABOUT.**
`FieldTightness.meas_exists_abs_ge_radius_le_of_sum_le` bounds exactly this set. -/
theorem compl_cube (a : ι → ℝ) :
    (cube a)ᶜ = {ω : Config ι | ∃ x, a x < |ω x|} := by
  ext ω
  simp only [cube, mem_compl_iff, mem_setOf_eq, not_forall, not_le]

/-! ## 2. The criterion -/

/-- **PER-SITE TAIL BOUNDS GIVE TIGHTNESS.** If for every tolerance there is a radius function `a`
whose exceptional set has measure at most `ε` for every member of the family, the family is tight
in Mathlib's sense.

The compact set is `cube a`, produced by §1 rather than assumed to exist, and the hypothesis is
stated on `{ω | ∃ x, a x < |ω x|}` because that is the set the estate's union bound is about. -/
theorem isTightMeasureSet_of_tail {S : Set (Measure (Config ι))}
    (h : ∀ ε : ENNReal, 0 < ε →
      ∃ a : ι → ℝ, ∀ μ ∈ S, μ {ω : Config ι | ∃ x, a x < |ω x|} ≤ ε) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨a, ha⟩ := h ε hε
  refine ⟨cube a, isCompact_cube a, fun μ hμ => ?_⟩
  rw [compl_cube]
  exact ha μ hμ

/-- The same with the radius presented as a function of the tolerance rather than chosen inside an
existential. **That quantifier order is the one `FieldTightness.radius` was made a `def` to have**:
an existential would let the witness depend silently on the member of the family. -/
theorem isTightMeasureSet_of_tail_radius {S : Set (Measure (Config ι))}
    (r : ENNReal → ι → ℝ)
    (h : ∀ ε : ENNReal, 0 < ε → ∀ μ ∈ S, μ {ω : Config ι | ∃ x, r ε x < |ω x|} ≤ ε) :
    IsTightMeasureSet S :=
  isTightMeasureSet_of_tail fun ε hε => ⟨r ε, h ε hε⟩

/-! ## 3. The union bound, on a countable site set

`FieldTightness` §4 does this in finite volume with the weight as a parameter and the constant
`∑ₓ wₓ`. On a countable index it is the same argument with `tsum` in place of `Finset.sum`, and it
is what turns **per-site** bounds — the only kind Chebyshev gives — into the **all-sites** bound
the criterion wants. -/

/-- The exceptional set is the union of the per-site exceptional sets. -/
theorem measure_exists_le_tsum [Countable ι] (μ : Measure (Config ι)) (a : ι → ℝ) :
    μ {ω : Config ι | ∃ x, a x < |ω x|} ≤ ∑' x, μ {ω : Config ι | a x < |ω x|} := by
  have hU : {ω : Config ι | ∃ x, a x < |ω x|} = ⋃ x, {ω : Config ι | a x < |ω x|} := by
    ext ω
    simp
  rw [hU]
  exact measure_iUnion_le _

/-- **PER-SITE TAIL BOUNDS, WEIGHTED BY A SUMMABLE WEIGHT, GIVE TIGHTNESS.** This is the shape the
estate can actually produce: Chebyshev bounds one site at a time, the weight distributes the
tolerance, and `∑ₓ wₓ ≤ 1` is the only global hypothesis. -/
theorem isTightMeasureSet_of_site_tail [Countable ι] {S : Set (Measure (Config ι))}
    (r : ENNReal → ι → ℝ) (w : ι → ENNReal) (hw : ∑' x, w x ≤ 1)
    (h : ∀ ε : ENNReal, 0 < ε → ∀ μ ∈ S, ∀ x, μ {ω : Config ι | r ε x < |ω x|} ≤ w x * ε) :
    IsTightMeasureSet S := by
  refine isTightMeasureSet_of_tail_radius r fun ε hε μ hμ => ?_
  refine (measure_exists_le_tsum μ _).trans ?_
  calc ∑' x, μ {ω : Config ι | r ε x < |ω x|}
      ≤ ∑' x, w x * ε := ENNReal.tsum_le_tsum (h ε hε μ hμ)
    _ = (∑' x, w x) * ε := by rw [ENNReal.tsum_mul_right]
    _ ≤ 1 * ε := by gcongr
    _ = ε := one_mul ε

/-! ## 4. Two degenerate checks, so the criterion is not vacuous

`ERRATUM 48`: a hypothesis nothing satisfies makes an empty class, and a criterion nobody can feed
proves nothing. These are the two cheapest witnesses that the hypothesis is satisfiable, and they
are labelled as cheap. -/

/-- A family supported in one cube satisfies the hypothesis, with a constant radius. -/
theorem isTightMeasureSet_of_forall_le {S : Set (Measure (Config ι))} (a : ι → ℝ)
    (h : ∀ μ ∈ S, μ {ω : Config ι | ∃ x, a x < |ω x|} = 0) :
    IsTightMeasureSet S :=
  isTightMeasureSet_of_tail fun ε hε => ⟨a, fun μ hμ => by rw [h μ hμ]; exact zero_le ε⟩

/-- In particular the empty family is tight, which is the statement that fails first if the
criterion is stated backwards. -/
theorem isTightMeasureSet_empty : IsTightMeasureSet (∅ : Set (Measure (Config ι))) :=
  isTightMeasureSet_of_tail fun _ _ => ⟨fun _ => 0, fun _ hμ => absurd hμ (notMem_empty _)⟩

end

end ConfigSpace
