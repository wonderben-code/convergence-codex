import SharpThreshold

/-!
# The comparison route cannot give a uniform field strength — and that is a theorem

Four units have now sharpened `IsingBoundaryField.MagnetisationBound`'s residue without moving it.
Each ended with the same sentence — *the threshold still grows, so no single field strength serves
every box* — and each time that was a remark about **the formula produced**, not about the method.
A reader could reasonably ask whether a cleverer choice of the free parameters rescues it.

**It does not, and this file proves it does not.**

> **`no_uniform_field_from_stratum`** — for **any** `β`, `m` and **any fixed** `h`, it is false
> that `(1 + e^{(16−2h)β})^B − 1 ≤ (1−m)/(1+m)` for every box.

The reading intended is `β > 0` and `0 ≤ m < 1`, where `(1−m)/(1+m)` is the ceiling of an actual
assembly; the refutation itself needs no hypothesis at all, and carrying one would have suggested
the failure was conditional.

Two facts make that the end of the route rather than one more failed attempt.

**The tolerance is capped by a constant.** `FieldThreshold.magnetisationBoundAt_of_bound` needs
`m(1+u) + u ≤ q`, and `q` cannot exceed `1` because `q·n²` is being compared with an average of
the magnetisation, which is at most `n²`. So `u ≤ (1−m)/(1+m)` — **a ceiling that does not depend
on the box** (`u_le_of_admissible`). No choice of `u`, `q` or the intermediate `ε` raises it.

**And the estimate's factor exceeds any constant.** At fixed `h` the base `1 + e^{(16−2h)β}` is
strictly greater than `1`, and the boundary grows, so the factor diverges
(`binomialFactor_atTop`). It therefore breaks the ceiling at some finite box, whatever `h` is.

So the two meet: the supply grows without bound and the demand is bounded, at every fixed field
strength. **`BoundaryStratum.sum_offPlus_le` is exhausted as a route to a uniform `h`** — not
"has not yet worked".

## What this does and does not rule out

**Ruled out**: every assembly that feeds a bound of the form *off-`+` mass `≤ u · Zplus` with `u`
constant* into `magnetisationBoundAt_of_bound`. That covers both thresholds this campaign has
built, and it is the whole of the comparison-against-the-`+`-class idea.

**Not ruled out, and not even addressed**: that `MagnetisationBound` is true. Nothing here is
evidence either way about the statement — only about one method. The Peierls contour argument
runs *with* the field rather than comparing to a field-free class
(`FieldBoundaryEnergy.down_prob_le_cluster_sum` is that inequality, already proved), and it is
untouched by anything below. **Whether that route yields a uniform `h` is not decided here**, and
this file deliberately makes no claim about what it would need — `ERRATUM 126` was exactly the
error of tracing a route by resemblance rather than by reading it.
-/

namespace StratumExhausted

open IsingFiniteVolume IsingBoundaryField BoundaryFieldLimit SharpThreshold
open Filter

set_option linter.style.openClassical false
open scoped Classical

/-! ## 1. The tolerance is capped, and the cap does not depend on the box -/

/-- **THE ASSEMBLY CANNOT TOLERATE A LARGE `u`.** `magnetisationBoundAt_of_bound`'s arithmetic
hypothesis `m(1+u) + u ≤ q`, together with `q ≤ 1` — forced because `q·n²` is compared against an
average of the magnetisation, which never exceeds `n²` — pins `u` below a constant. -/
theorem u_le_of_admissible {m u q : ℝ} (hm0 : 0 ≤ m) (hq : q ≤ 1)
    (hmq : m * (1 + u) + u ≤ q) : u ≤ (1 - m) / (1 + m) := by
  have hm1 : (0 : ℝ) < 1 + m := by linarith
  rw [le_div_iff₀ hm1]
  nlinarith

/-! ## 2. The estimate's factor exceeds every constant -/

/-- The base is strictly above `1` at every field strength, because `exp` is positive. This is the
only place the argument uses anything about `h`, and it uses nothing: no sign, no size. -/
theorem one_lt_base (β h : ℝ) : 1 < 1 + Real.exp ((16 - 2 * h) * β) := by
  have := Real.exp_pos ((16 - 2 * h) * β)
  linarith

/-- **THE FACTOR DIVERGES IN THE BOUNDARY SIZE.** -/
theorem binomialFactor_atTop (β h : ℝ) :
    Tendsto (fun B : ℕ => (1 + Real.exp ((16 - 2 * h) * β)) ^ B - 1) atTop atTop :=
  Filter.tendsto_atTop_add_const_right atTop (-1)
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_base β h))

/-! ## 3. So no fixed field strength works, for any admissible tolerance -/

/-- **THE ROUTE IS EXHAUSTED.** At any fixed `h`, the estimate's factor breaks the ceiling the
assembly imposes, at some finite box. Stated as a refutation of the universally quantified
statement, because that is the shape a would-be uniform threshold would have to satisfy.

*Three hypotheses were carried by the first draft and are gone:* `0 < β`, `0 ≤ m` and `m < 1`. The
refutation needs none of them — the base exceeds `1` whatever `β` and `h` are, and the ceiling
enters only as an atom the arithmetic never inspects. They belong to the **reading**, not the
proof: `u_le_of_admissible` is where `0 ≤ m` is genuinely needed, and `β > 0` is what makes
`(1−m)/(1+m)` the ceiling of an actual assembly rather than an arbitrary constant. Stated at full
strength here and interpreted narrowly in the header. -/
theorem no_uniform_field_from_stratum {β m : ℝ} (h : ℝ) :
    ¬ ∀ n : ℕ, (1 + Real.exp ((16 - 2 * h) * β)) ^ (bdrySites n).card - 1
        ≤ (1 - m) / (1 + m) := by
  intro hall
  set r : ℝ := 1 + Real.exp ((16 - 2 * h) * β) with hr
  have hr1 : 1 < r := one_lt_base β h
  obtain ⟨N, hN⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hr1).eventually_ge_atTop
      ((1 - m) / (1 + m) + 2)).exists
  have hNB : N ≤ (bdrySites (max N 1)).card :=
    le_trans (le_max_left N 1) (card_bdrySites_ge (lt_of_lt_of_le one_pos (le_max_right N 1)))
  have hmono : r ^ N ≤ r ^ (bdrySites (max N 1)).card :=
    pow_le_pow_right₀ hr1.le hNB
  have hbad := hall (max N 1)
  linarith

/-! ## 4. The same statement about the two thresholds this campaign built

Both `FieldThreshold.magnetisation_threshold` and `SharpThreshold.magnetisation_sharp_threshold`
produce a threshold **per box**, and both were accompanied by a proof that it grows. §3 is the
stronger fact: it is not that these two particular formulas grow, it is that **the shared method
admits no formula that does not.** -/

/-- **AND THE SHARP THRESHOLD GROWS, RESTATED FROM §3 RATHER THAN FROM ITS FORMULA.** Kept because
the two arguments are genuinely different: `sharpThreshold_atTop` reads the growth off the
expression `8 + log(B/…)/(2β)`, while this reads it off the *estimate the expression came from*.
The second survives a change of formula and the first does not. -/
theorem no_uniform_of_growth {β m : ℝ} :
    ∀ h : ℝ, ∃ n : ℕ, ¬ ((1 + Real.exp ((16 - 2 * h) * β)) ^ (bdrySites n).card - 1
        ≤ (1 - m) / (1 + m)) := by
  intro h
  by_contra hcon
  push Not at hcon
  exact no_uniform_field_from_stratum (β := β) (m := m) h hcon

end StratumExhausted
