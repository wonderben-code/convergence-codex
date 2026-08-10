import BoundaryFieldRatio

/-!
# A strong boundary field is a `+` boundary condition, in the limit

`BoundaryFieldRatio` refuted `h → 0`. It did not say which limit, if any, replaces it, and
`ERRATUM 86`'s rule forbids naming one without checking. This file derives the answer from
the weight, rather than asserting it: **`h → +∞`**, and not as an analogy — the boundary-field
expectation of **every** observable converges to its `+`-boundary-conditioned expectation.

## Where the answer comes from, rather than where it is remembered from

Write `B` for the number of boundary sites and `D σ` for how many of them are **down** in `σ`.
Then `boundaryTerm = B - 2 D`, so the Gibbs weight factors:

`exp (-β H_h σ) = exp (β h B) · exp (-β H σ) · exp (-2βh · D σ)`.

The first factor does not depend on `σ` and cancels out of every ratio. The last is `1`
exactly when `D σ = 0` — that is, exactly on the `+`-boundary configurations — and for every
other `σ` it decays in `h`, at a rate proportional to how many boundary spins are wrong.
**So the field does not tilt the measure towards `+`; it deletes everything else, and the
parameter that runs the deletion is `βh → ∞`, not `h → 0`.** `tendsto_sum` is that sentence
as a limit of finite sums, and `tendsto_integral` is the same statement about the estate's
measure:

> **`tendsto_integral`** — for `β > 0`, every box and every observable `f`,
> `∫ f ∂(isingMeasure n h β) → (∑_{σ ∈ +} f σ e^{-βH σ}) / (∑_{σ ∈ +} e^{-βH σ})` as `h → ∞`.

That limit is exactly the object `PlusMagnetisation.magnetisation_ge` is stated with — not
every theorem in the chain, since the earlier ones divide by the **full** partition function
and only `PlusCondition` onwards has `+` on both sides. **The comparison `ERRATUM 86`
recorded as unexamined is examined**: `h → 0` is false
(`BoundaryFieldRatio`), `h → ∞` is true, and the direction is read off the weight rather than
recalled from a textbook.

## What that gives, and the one thing it does not

Composing with `PlusMagnetisation.magnetisation_ge`:

> **`magnetisation_eventually`** — for every `ε > 0`, at every low enough temperature, for
> **every box**, `(1 - 2ε) n² ≤ ∫ magnetisation ∂(isingMeasure n h β)` **for all large enough
> `h`**.

Compare that with the estate's target. **Fix a `m < 1` and a low enough temperature** — those
two are what `∀ᶠ β` and the arbitrary `ε` buy, and fixing them is fair, because
`MagnetisationBound` is a statement *about* a given `β` and a given `m`. Then, at the same
`β` and the same `m`:

* `MagnetisationBound β h m`     is  `∀ n,        MagnetisationBoundAt n β h m`
* what is proved here            is  `∀ n, ∀ᶠ h,  MagnetisationBoundAt n β h m`

— that second line is `magnetisation_eventually_of_lt_one`, stated at `m` and not at
`1 - 2ε` precisely so that the two lines can be compared symbol by symbol.
**With `β` and `m` fixed, the whole remaining distance is the position of one quantifier.**
`magnetisationBound_iff` is the `Iff.rfl` certifying that the first line is the target and not
a paraphrase of it. So the residue is not a vague "packaging" any more: it is the demand that
a **single** field strength serve **every** box, where this file delivers a threshold per box.

**And that swap is not free.** Say exactly why, as a fact about the proof rather than a
guess about the mathematics: the limit above is taken with the box **fixed**, and no rate is
exhibited for it anywhere, so there is nothing in this argument from which a threshold
independent of `n` could be extracted. Whether one exists is **not decided here**. What is
established is that the value at `h = ∞` is a *limit* of the finite-`h` values, so any route
to `MagnetisationBound` must add information about how that limit is approached — information
this file does not have and does not guess at.

`MagnetisationBound` remains untouched, and remains false at `h = 0` for positive `m`.
-/

namespace BoundaryFieldLimit

open IsingFiniteVolume IsingBoundaryField DualObstruction
open MeasureTheory Filter

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The boundary, and how many of it is down -/

/-- The boundary sites, as a `Finset`. -/
def bdrySites (n : ℕ) : Finset (Site n) :=
  (Finset.univ : Finset (Site n)).filter fun p => isBoundary p = true

/-- How many boundary sites are **down** in `σ`. This is the only feature of `σ` the field
term sees. -/
def downCount (n : ℕ) (σ : Config n) : ℕ :=
  ((bdrySites n).filter fun p => σ p = false).card

theorem boundaryTerm_eq_sum (n : ℕ) (σ : Config n) :
    boundaryTerm n σ = ∑ p ∈ bdrySites n, spin (σ p) := by
  rw [boundaryTerm, bdrySites, Finset.sum_filter]

/-- **The field term counts the down boundary spins and nothing else.** `B - 2D`, with `B`
the size of the boundary. -/
theorem boundaryTerm_eq (n : ℕ) (σ : Config n) :
    boundaryTerm n σ = ((bdrySites n).card : ℝ) - 2 * (downCount n σ : ℝ) := by
  classical
  rw [boundaryTerm_eq_sum,
    ← Finset.sum_filter_add_sum_filter_not (bdrySites n) (fun p => σ p = false)]
  have hdown : ∀ p ∈ (bdrySites n).filter (fun p => σ p = false), spin (σ p) = (-1 : ℝ) := by
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
    simp [spin]
  have hup : ∀ p ∈ (bdrySites n).filter (fun p => ¬ σ p = false), spin (σ p) = (1 : ℝ) := by
    intro p hp
    have hne := (Finset.mem_filter.mp hp).2
    cases hb : σ p
    · exact absurd hb hne
    · simp [spin]
  have hcard : ((bdrySites n).filter (fun p => σ p = false)).card
      + ((bdrySites n).filter (fun p => ¬ σ p = false)).card = (bdrySites n).card :=
    Finset.card_filter_add_card_filter_not (fun p => σ p = false)
  rw [Finset.sum_congr rfl hdown, Finset.sum_congr rfl hup, Finset.sum_const,
    Finset.sum_const, downCount, ← hcard]
  push_cast
  ring

/-- **The field term is maximal exactly on the `+` class.** -/
theorem downCount_eq_zero_iff (n : ℕ) (σ : Config n) :
    downCount n σ = 0 ↔ PlusBoundary σ := by
  classical
  rw [downCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro hemp p hp
    have hmem : p ∈ bdrySites n :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
    have hne := hemp hmem
    cases hb : σ p
    · exact absurd hb hne
    · rfl
  · intro hplus p hp
    have hb := Finset.mem_filter.mp hp
    rw [hplus p hb.2]
    exact Bool.noConfusion

/-! ## 2. The weight factors, and the constant cancels

`exp (-β H_h σ) = exp (β h B) · exp (-β H σ) · exp (-2βh · D σ)`. The first factor is the
same for every configuration, so it disappears from every ratio; the third is `1` on the
`+` class and decays off it. -/

theorem exp_isingHB_factor (n : ℕ) (h β : ℝ) (σ : Config n) :
    Real.exp (-β * isingHB n h σ)
      = Real.exp (β * h * ((bdrySites n).card : ℝ)) *
        (Real.exp (-β * isingH n σ) * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) := by
  rw [isingHB, boundaryTerm_eq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem sum_factor (n : ℕ) (h β : ℝ) (g : Config n → ℝ) :
    ∑ σ : Config n, g σ * Real.exp (-β * isingHB n h σ)
      = Real.exp (β * h * ((bdrySites n).card : ℝ)) *
        ∑ σ : Config n, (g σ * Real.exp (-β * isingH n σ)) *
          Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [exp_isingHB_factor]
  ring

/-- The integral, with the field-independent factor cancelled: a ratio in which `h` appears
only through `exp (-2βh · D σ)`. -/
theorem integral_eq (n : ℕ) (h β : ℝ) (f : Config n → ℝ) :
    ∫ σ, f σ ∂(isingMeasure n h β) =
      (∑ σ : Config n, (f σ * Real.exp (-β * isingH n σ)) *
          Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) /
        (∑ σ : Config n, (Real.exp (-β * isingH n σ)) *
          Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) := by
  rw [BoundaryFieldRatio.integral_isingMeasure, sum_factor n h β f]
  have hden : ∑ σ : Config n, Real.exp (-β * isingHB n h σ)
      = Real.exp (β * h * ((bdrySites n).card : ℝ)) *
        ∑ σ : Config n, (Real.exp (-β * isingH n σ)) *
          Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := by
    have := sum_factor n h β (fun _ => 1)
    simpa using this
  rw [hden]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

/-! ## 3. As the field grows, the sum collapses onto the `+` class

Off the `+` class `D σ ≥ 1`, so the factor `exp (-(2βh) D σ)` tends to zero; on it the factor
is `1`. Finitely many terms, so the sum follows termwise. -/

/-- **The collapse.** For `β > 0` and any weights `g`, the `h`-weighted sum tends to the
plain sum over the `+`-boundary configurations. -/
theorem tendsto_sum (n : ℕ) {β : ℝ} (hβ : 0 < β) (g : Config n → ℝ) :
    Tendsto (fun h : ℝ => ∑ σ : Config n, g σ *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) atTop
      (nhds (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ), g σ)) := by
  classical
  have hsplit : ∀ h : ℝ, ∑ σ : Config n, g σ *
        Real.exp (-(2 * β * h) * (downCount n σ : ℝ))
      = (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
            g σ * Real.exp (-(2 * β * h) * (downCount n σ : ℝ)))
        + ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
            g σ * Real.exp (-(2 * β * h) * (downCount n σ : ℝ)) := fun h =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  simp only [hsplit]
  have hplus : ∀ h : ℝ,
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          g σ * Real.exp (-(2 * β * h) * (downCount n σ : ℝ)))
        = ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ), g σ := by
    intro h
    refine Finset.sum_congr rfl fun σ hσ => ?_
    have h0 : downCount n σ = 0 :=
      (downCount_eq_zero_iff n σ).mpr (Finset.mem_filter.mp hσ).2
    rw [h0]
    simp
  simp only [hplus]
  have hrest : Tendsto (fun h : ℝ =>
      ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
        g σ * Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) atTop (nhds 0) := by
    have hterm : ∀ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ¬ PlusBoundary σ),
        Tendsto (fun h : ℝ => g σ * Real.exp (-(2 * β * h) * (downCount n σ : ℝ)))
          atTop (nhds 0) := by
      intro σ hσ
      have hne : downCount n σ ≠ 0 := fun h0 =>
        (Finset.mem_filter.mp hσ).2 ((downCount_eq_zero_iff n σ).mp h0)
      have hpos : 0 < 2 * β * (downCount n σ : ℝ) := by
        have : (0 : ℝ) < (downCount n σ : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hne
        positivity
      have harg : Tendsto (fun h : ℝ => -(2 * β * h) * (downCount n σ : ℝ)) atTop atBot := by
        have hlin : Tendsto (fun h : ℝ => (2 * β * (downCount n σ : ℝ)) * h) atTop atTop :=
          Filter.tendsto_id.const_mul_atTop hpos
        have hneg := tendsto_neg_atTop_atBot.comp hlin
        refine hneg.congr fun h => ?_
        simp only [Function.comp_apply]
        ring
      have hexp : Tendsto (fun h : ℝ => Real.exp (-(2 * β * h) * (downCount n σ : ℝ)))
          atTop (nhds 0) := Real.tendsto_exp_atBot.comp harg
      simpa using hexp.const_mul (g σ)
    simpa using tendsto_finset_sum _ hterm
  simpa using (tendsto_const_nhds (x := ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
    (fun σ => PlusBoundary σ), g σ) (f := (atTop : Filter ℝ))).add hrest

/-! ## 4. So the boundary-field expectation converges to the `+`-conditioned one -/

/-- **THE LIMIT THAT RELATES THE TWO SET-UPS, DERIVED RATHER THAN NAMED.** For `β > 0`, in
every box and for every observable, the boundary-field expectation converges as `h → +∞` to
the expectation conditioned on `+` boundary — the object the whole Peierls chain is stated
with.

`ERRATUM 86` recorded that this comparison had been asserted (`h → 0⁺`) without checking;
`BoundaryFieldRatio` showed that assertion false; this is the true statement, read off the
factorisation `exp (-β H_h σ) = exp (β h B) · exp (-β H σ) · exp (-2βh · D σ)`. -/
theorem tendsto_integral (n : ℕ) {β : ℝ} (hβ : 0 < β) (f : Config n → ℝ) :
    Tendsto (fun h : ℝ => ∫ σ, f σ ∂(isingMeasure n h β)) atTop
      (nhds ((∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
              f σ * Real.exp (-β * isingH n σ)) /
            (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
              Real.exp (-β * isingH n σ)))) := by
  classical
  have heq : (fun h : ℝ => ∫ σ, f σ ∂(isingMeasure n h β))
      = fun h : ℝ =>
        (∑ σ : Config n, (f σ * Real.exp (-β * isingH n σ)) *
            Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) /
          (∑ σ : Config n, (Real.exp (-β * isingH n σ)) *
            Real.exp (-(2 * β * h) * (downCount n σ : ℝ))) := by
    funext h
    exact integral_eq n h β f
  rw [heq]
  exact (tendsto_sum n hβ fun σ => f σ * Real.exp (-β * isingH n σ)).div
    (tendsto_sum n hβ fun σ => Real.exp (-β * isingH n σ))
    (PeierlsConditional.plus_partition_pos β).ne'

/-! ## 5. The magnetisation bound, for every box, at every large enough field -/

/-- **THE PEIERLS CONCLUSION, AGAINST THE ESTATE'S OWN MEASURE.** For every `ε > 0`, at
every low enough temperature, for **every box**, and for **all large enough field strengths**,
the boundary-field expectation of the magnetisation is at least `(1 - 2ε) n²`.

The threshold in `h` is produced per box. That is the entire distance to
`IsingBoundaryField.MagnetisationBound`, which demands one field strength for all boxes at
once — see `magnetisationBound_iff`. -/
theorem magnetisation_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ (n : ℕ), 0 < n → ∀ᶠ h : ℝ in atTop,
      (1 - 2 * ε) * ((n : ℝ) * n) ≤ ∫ σ, magnetisation n σ ∂(isingMeasure n h β) := by
  classical
  filter_upwards [PlusMagnetisation.magnetisation_ge (half_pos hε),
    eventually_gt_atTop (0 : ℝ)] with β hβ hβ0 n hn
  have hlim := tendsto_integral n hβ0 (magnetisation n)
  have hge := hβ n hn
  have hn2 : (0 : ℝ) < (n : ℝ) * n := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hlt : (1 - 2 * ε) * ((n : ℝ) * n) <
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          magnetisation n σ * Real.exp (-β * isingH n σ)) /
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
          Real.exp (-β * isingH n σ)) := by
    nlinarith [hge, mul_pos hε hn2]
  exact (hlim.eventually (lt_mem_nhds hlt)).mono fun h hh => hh.le

/-! ## 6. The residue, named as an object

`MagnetisationBound` is a `∀ n` of the statement below; what §5 proves is the same `∀ n` with
an `∀ᶠ h` inserted **inside** it. Writing the per-box statement down makes the difference a
quantifier position rather than a paragraph. -/

/-- `IsingBoundaryField.MagnetisationBound` for one box. -/
def MagnetisationBoundAt (n : ℕ) (β h m : ℝ) : Prop :=
  0 < n → m * ((n : ℝ) * n) ≤ ∫ σ, magnetisation n σ ∂(isingMeasure n h β)

/-- **The target is exactly the per-box statement, quantified over boxes.** Nothing else
differs — so the distance from `magnetisation_eventually` is the position of its `∀ᶠ h`. -/
theorem magnetisationBound_iff (β h m : ℝ) :
    MagnetisationBound β h m ↔ ∀ n : ℕ, MagnetisationBoundAt n β h m :=
  Iff.rfl

/-- **What is proved, in the per-box vocabulary.** Compare with `magnetisationBound_iff`:
the target needs the `h` chosen before the box, and this supplies it after. -/
theorem magnetisation_eventually_at {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ n : ℕ, ∀ᶠ h : ℝ in atTop,
      MagnetisationBoundAt n β h (1 - 2 * ε) := by
  filter_upwards [magnetisation_eventually hε] with β hβ n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Eventually.of_forall fun _ hcon => absurd hcon (lt_irrefl 0)
  · exact (hβ n hn).mono fun h hh _ => hh

/-- **The same statement at a bare `m`, so that the comparison with `magnetisationBound_iff`
is symbol by symbol.** For every `m < 1`, at every low enough temperature and in every box,
`MagnetisationBoundAt n β h m` holds for all large enough `h`. Set this beside
`MagnetisationBound β h m = ∀ n, MagnetisationBoundAt n β h m`: one `∀ᶠ h`, on the inside. -/
theorem magnetisation_eventually_of_lt_one {m : ℝ} (hm : m < 1) :
    ∀ᶠ β : ℝ in atTop, ∀ n : ℕ, ∀ᶠ h : ℝ in atTop, MagnetisationBoundAt n β h m := by
  have hε : 0 < (1 - m) / 2 := by linarith
  have hval : 1 - 2 * ((1 - m) / 2) = m := by ring
  filter_upwards [magnetisation_eventually_at hε] with β hβ n
  rw [hval] at hβ
  exact hβ n

/-- **And a uniform threshold would finish it.** Stated so that the missing hypothesis is an
object a later unit can aim at, rather than a sentence: if one field strength works for every
box, `MagnetisationBound` follows immediately. Whether such an `h` exists is **not** decided
here. -/
theorem magnetisationBound_of_uniform (β h m : ℝ)
    (huniform : ∀ n : ℕ, MagnetisationBoundAt n β h m) :
    MagnetisationBound β h m :=
  (magnetisationBound_iff β h m).mpr huniform

end BoundaryFieldLimit
