import MirrorDominanceConverse

/-!
# Reflection positivity is monotone in the mass, and the good masses form a downward-closed set

`GreenLargeMass.reflectionPositive_all_or_bounded` says every graph with a mirror reflection is
reflection positive either at **every** nonzero mass or only **below a threshold**, and that there
is no third behaviour. It says nothing about which masses below the threshold are good, and it was
proved by an estimate: the large-mass expansion, with a witness-dependent constant.

Now that `MirrorDominanceConverse.reflectionPositive_iff_mirrorDominated` makes reflection
positivity **equal** to a condition written directly against the operator, the dichotomy sharpens
to a monotonicity, and the proof stops being an estimate:

**If a graph is reflection positive at `m`, it is reflection positive at every smaller nonzero
mass.** So the good set is not merely bounded — it is **downward closed**.

## Why, in one line

The condition is `crossForm u ≤ 2⟪u, N w⟫ − ⟪w, N w⟫` for some `w` on the fixed layer. Lower the
mass and keep the same `w`:

* **the coupling does not move** — `crossForm_mass_independent`;
* **the earning term `⟪u, N w⟫` does not move either**, because `u` lives on the half and `w` on
  the mirror, those are disjoint, and off the diagonal the operator is pure adjacency;
* **the cost `⟪w, N w⟫` goes down**, because the only mass in it is `m²` on the diagonal.

So the same witness pays for more at a lower mass. **`mirrorDominated_of_sq_le` uses no inverse,
no estimate, no threshold and nothing about the graph** — it does not even need the mass to be
nonzero. (Scoped deliberately: `reflectionPositive_of_sq_le` routes through the criterion, which
is a statement about the propagator, so the claim is about §2's first theorem and not about the
file. `ERRATUM 158` is the same sentence written one unit ago without the scope.)

## What it sharpens, and what it explains

* `reflectionPositive_all_or_bounded` becomes `reflectionPositive_downward_closed`: *all or
  bounded* becomes *all or an initial segment* — and §2 **re-derives that dichotomy** from
  downward-closure (`all_or_bounded_of_downward_closed`), so the sharpening is checked against
  the statement it sharpens rather than asserted to contain it.
* One failure now propagates upward — `not_reflectionPositive_of_le`. `MirrorConverseFails` proved
  `mirGraph` not reflection positive at `m = 11` by the large-mass estimate; §3 extends that to
  **every** mass at or above `11` for free, and the same graph's positivity at `m = 1/2` extends
  down to every smaller mass.
* **It is a mirror phenomenon and nothing else.** On a fixed-point-free reflection
  `ReflectionConverse.reflectionPositive_mass_independent` already says the good set is everything
  or nothing, so monotonicity there is vacuous — §4 states that, because a theorem whose content
  vanishes on the estate's main case should say so itself.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace MirrorMassMonotone

open Matrix GraphLaplacian GraphReflection GraphMirrorReflection MirrorDominance

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. The three pieces of the condition, under a change of mass -/

/-- **THE HALF-TO-MIRROR COUPLING DOES NOT SEE THE MASS.** The half and the fixed layer are
disjoint, so every entry involved is off the diagonal, and off the diagonal the operator is minus
the adjacency. -/
theorem massive_half_mir_mass_free (hM : IsMirrorHalf θ H Mir) (m m' : ℝ) {p r : V}
    (hp : p ∈ H) (hr : r ∈ Mir) : massive G m p r = massive G m' p r := by
  have hne : p ≠ r := fun hc => hM.disj p hp (hc ▸ hr)
  simp only [GraphLaplacian.massive_apply, if_neg hne]

/-- **THE ONLY MASS IN THE OPERATOR IS `m²` ON THE DIAGONAL.** -/
theorem massive_diff (m m' : ℝ) (r s : V) :
    massive G m' r s - massive G m r s = if r = s then m' ^ 2 - m ^ 2 else 0 := by
  rw [GraphLaplacian.massive_apply, GraphLaplacian.massive_apply]
  by_cases hrs : r = s
  · rw [if_pos hrs, if_pos hrs, if_pos hrs]; ring
  · rw [if_neg hrs, if_neg hrs, if_neg hrs]; ring

/-- **THE COST CHANGES BY THE MASS ALONE**, and by it on the diagonal only. -/
theorem mir_cost_diff (m m' : ℝ) (w : V → ℝ) :
    ∑ r ∈ Mir, ∑ s ∈ Mir, w r * w s * massive G m' r s
      = (∑ r ∈ Mir, ∑ s ∈ Mir, w r * w s * massive G m r s)
        + (m' ^ 2 - m ^ 2) * ∑ r ∈ Mir, w r * w r := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hpt : ∀ s : V, w r * w s * massive G m' r s
      = w r * w s * massive G m r s + (if r = s then (m' ^ 2 - m ^ 2) * (w r * w r) else 0) := by
    intro s
    have hd : massive G m' r s = massive G m r s + (if r = s then m' ^ 2 - m ^ 2 else 0) := by
      rw [← massive_diff (G := G) m m' r s]; ring
    rw [hd]
    by_cases hrs : r = s
    · rw [if_pos hrs, if_pos hrs, hrs]; ring
    · rw [if_neg hrs, if_neg hrs]; ring
  rw [Finset.sum_congr rfl (fun s _ => hpt s), Finset.sum_add_distrib,
    Finset.sum_ite_eq Mir r (fun _ => (m' ^ 2 - m ^ 2) * (w r * w r)), if_pos hr]

/-! ## 2. Monotonicity of the condition, and hence of reflection positivity -/

/-- **THE SAME WITNESS PAYS FOR MORE AT A LOWER MASS.** Nothing about the graph enters. -/
theorem mirrorDominated_of_sq_le (hM : IsMirrorHalf θ H Mir) {m m' : ℝ}
    (hle : m' ^ 2 ≤ m ^ 2) (hdom : MirrorDominated G m θ H Mir) :
    MirrorDominated G m' θ H Mir := by
  intro u
  obtain ⟨w, hwsupp, hwbound⟩ := hdom u
  refine ⟨w, hwsupp, ?_⟩
  -- the coupling is the same
  have hcf : crossForm G m' θ H u = crossForm G m θ H u :=
    crossForm_mass_independent hM m' m u
  -- the earning term is the same
  have hE : ∑ p ∈ H, ∑ r ∈ Mir, u p * w r * massive G m' p r
      = ∑ p ∈ H, ∑ r ∈ Mir, u p * w r * massive G m p r :=
    Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun r hr => by
      rw [massive_half_mir_mass_free hM m' m hp hr]
  -- the cost is no larger
  have hD := mir_cost_diff (G := G) (Mir := Mir) m m' w
  have hsq : 0 ≤ ∑ r ∈ Mir, w r * w r :=
    Finset.sum_nonneg fun r _ => mul_self_nonneg (w r)
  have hneg : (m' ^ 2 - m ^ 2) * ∑ r ∈ Mir, w r * w r ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hsq
  rw [hcf, hE]
  linarith [hwbound, hD, hneg]

/-- **REFLECTION POSITIVITY IS MONOTONE IN THE MASS.** Positive at `m` implies positive at every
smaller nonzero mass, on every finite graph carrying a mirror reflection. -/
theorem reflectionPositive_of_sq_le (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) {m m' : ℝ}
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hle : m' ^ 2 ≤ m ^ 2)
    (hrp : GraphReflection.ReflectionPositive G m θ H) :
    GraphReflection.ReflectionPositive G m' θ H :=
  MirrorDominance.reflectionPositive_of_mirrorDominated hM h hm'
    (mirrorDominated_of_sq_le hM hle
      (MirrorDominanceConverse.mirrorDominated_of_reflectionPositive hM h hm hrp))

/-- **AND SO THE GOOD MASSES ARE A DOWNWARD-CLOSED SET.** This is what
`GreenLargeMass.reflectionPositive_all_or_bounded` becomes: *all or bounded above* sharpens to
*all or an initial segment*, and the proof is no longer an estimate. -/
theorem reflectionPositive_downward_closed (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) :
    ∀ m ∈ {m : ℝ | m ≠ 0 ∧ GraphReflection.ReflectionPositive G m θ H},
      ∀ m' : ℝ, m' ≠ 0 → m' ^ 2 ≤ m ^ 2 →
        m' ∈ {m : ℝ | m ≠ 0 ∧ GraphReflection.ReflectionPositive G m θ H} := by
  rintro m ⟨hm, hrp⟩ m' hm' hle
  exact ⟨hm', reflectionPositive_of_sq_le hM h hm hm' hle hrp⟩

/-- **AND THE OLD DICHOTOMY IS A CONSEQUENCE.** `GreenLargeMass.reflectionPositive_all_or_bounded`
was proved by the large-mass expansion, with a witness-dependent constant; downward-closure gives
it with no constant at all, taking the threshold to be the absolute value of any bad mass. Stated
so that the sharpening is checked against what it sharpens. -/
theorem all_or_bounded_of_downward_closed (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) :
    (∀ m : ℝ, m ≠ 0 → GraphReflection.ReflectionPositive G m θ H)
      ∨ ∃ M : ℝ, ∀ m : ℝ, M < m → m ≠ 0 → ¬ GraphReflection.ReflectionPositive G m θ H := by
  by_cases hall : ∀ m : ℝ, m ≠ 0 → GraphReflection.ReflectionPositive G m θ H
  · exact Or.inl hall
  · obtain ⟨m₀, hm₀, hbad⟩ : ∃ m : ℝ, m ≠ 0 ∧ ¬ GraphReflection.ReflectionPositive G m θ H := by
      by_contra hc
      exact hall fun m hm => not_not.mp fun hn => hc ⟨m, hm, hn⟩
    refine Or.inr ⟨|m₀|, fun m hlt hm hrp => hbad ?_⟩
    have habs : (0 : ℝ) ≤ |m₀| := abs_nonneg m₀
    have hsq : m₀ ^ 2 ≤ m ^ 2 := by
      have h1 : |m₀| ^ 2 ≤ m ^ 2 := by nlinarith
      rwa [sq_abs] at h1
    exact reflectionPositive_of_sq_le hM h hm hm₀ hsq hrp

/-- **AND A SINGLE FAILURE PROPAGATES UPWARD.** The contrapositive, stated separately because it
is the form the estate's witnesses are in. -/
theorem not_reflectionPositive_of_le (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) {m m' : ℝ}
    (hm : m ≠ 0) (hm' : m' ≠ 0) (hle : m' ^ 2 ≤ m ^ 2)
    (hfail : ¬ GraphReflection.ReflectionPositive G m' θ H) :
    ¬ GraphReflection.ReflectionPositive G m θ H :=
  fun hrp => hfail (reflectionPositive_of_sq_le hM h hm hm' hle hrp)

/-! ## 3. The witness, decided on two rays instead of at two points

`MirrorConverseFails` decided `mirGraph` at `m = 1/2` and at `m = 11`. §2 turns each point into a
ray at no cost.
-/

open MirrorConverseFails

/-- **POSITIVE ON THE WHOLE RAY BELOW `1/2`.** -/
theorem mirGraph_reflectionPositive_of_le {m : ℝ} (hm : m ≠ 0) (hle : m ^ 2 ≤ (1 / 2 : ℝ) ^ 2) :
    GraphReflection.ReflectionPositive mirGraph m tau Hm :=
  reflectionPositive_of_sq_le isMirrorHalf_Hm isRefl_tau (by norm_num) hm hle
    reflectionPositive_half

/-- **AND NEGATIVE ON THE WHOLE RAY ABOVE `11`.** `MirrorConverseFails` got the single point by
the large-mass estimate; the ray is free. -/
theorem mirGraph_not_reflectionPositive_of_ge {m : ℝ} (hm : m ≠ 0)
    (hge : (11 : ℝ) ^ 2 ≤ m ^ 2) :
    ¬ GraphReflection.ReflectionPositive mirGraph m tau Hm :=
  not_reflectionPositive_of_le isMirrorHalf_Hm isRefl_tau hm (by norm_num) hge
    not_reflectionPositive_eleven

/-- **THE TWO RAYS, TOGETHER**, so that the shape of the answer is visible: an initial segment of
good masses and a final segment of bad ones, with the changeover somewhere between. -/
theorem mirGraph_two_rays :
    (∀ m : ℝ, m ≠ 0 → m ^ 2 ≤ (1 / 2 : ℝ) ^ 2 →
        GraphReflection.ReflectionPositive mirGraph m tau Hm)
      ∧ (∀ m : ℝ, m ≠ 0 → (11 : ℝ) ^ 2 ≤ m ^ 2 →
        ¬ GraphReflection.ReflectionPositive mirGraph m tau Hm) :=
  ⟨fun _ hm hle => mirGraph_reflectionPositive_of_le hm hle,
   fun _ hm hge => mirGraph_not_reflectionPositive_of_ge hm hge⟩

/-! ## 4. On a fixed-point-free reflection the theorem says nothing, and that is correct

`ReflectionConverse.reflectionPositive_mass_independent` already makes the good set everything or
nothing, so §2 adds no information there. Stated rather than left implicit, because a theorem
whose content vanishes on the estate's main case should say so itself — and because it is the
check that §2 is a **mirror** phenomenon rather than a general one.
-/

/-- This **is** `ReflectionConverse.reflectionPositive_mass_independent`, re-exported under a name
that says what it means here. Not a new theorem, and named so that nobody reads it as one. -/
theorem monotone_vacuous_of_isHalf (hH : GraphHalfSpace.IsHalf θ H) (h : IsRefl G θ)
    {m m' : ℝ} (hm : m ≠ 0) (hm' : m' ≠ 0) :
    (GraphReflection.ReflectionPositive G m θ H
        ↔ GraphReflection.ReflectionPositive G m' θ H) :=
  ReflectionConverse.reflectionPositive_mass_independent hH h hm hm'

end MirrorMassMonotone
