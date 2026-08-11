import FieldCover

/-!
# The energy estimate for the case the `+`-cut hypothesis excludes

`FieldEnergy.gibbs_field_bound_of_cut` bounds the boundary-field weight of the configurations
whose contour contains a given bond set — but only when that set is a **`+`-cut**, realised by
a configuration that is `false` at every boundary site. `FieldCover` and `FieldInterior` spend
that estimate on the branch where the down cluster misses the boundary, which is exactly the
branch where the cut *is* a `+`-cut.

The other branch is the one `UNLOCK_WATCHLIST` calls **S3b**: the cluster reaches the edge of
the box. There the cluster configuration is `true` at the boundary sites it contains, the
`+`-cut hypothesis fails, and the estimate does not apply. **This file removes that
hypothesis.**

## What replaces it, and it is an equality rather than a loss

Let `ν` be `true` exactly on the cluster and let `σ` be **down wherever `ν` is up** — which is
free, since a down cluster consists of down sites. Flipping the cluster up moves each of its
`k` boundary sites from `-1` to `+1`, so `boundaryTerm` rises by exactly `2k` and

`exp (-β H_h σ) = exp (-4β|∂C|) · exp (-2βhk) · exp (-β H_h (σ xor ν))`,

**`exp_isingHB_xorC_cluster`**, with no inequality anywhere.

> **`gibbs_field_bound_of_cluster`** — for **any** `ν`, the boundary-field weight of the
> configurations that are down on `ν`'s support and whose contour contains `ν`'s is at most
> `exp (-4β|contour ν|) · exp (-2βhk)` times the total partition sum, at every `h` and `β`,
> with `k` the number of boundary sites `ν` occupies.

**`cluster_factor_le`**: at `β, h > 0` and `k ≥ 1` the new factor is at most `exp (-2βh) < 1`,
so a boundary-reaching cluster is suppressed *more* than the field-free estimate suppresses it
— the watchlist's arithmetic, checked rather than asserted.

## The trade, stated exactly, because the two estimates are incomparable

This is **not** strictly stronger than `gibbs_field_bound_of_cut`. It drops `IsPlusCut` and
gains the factor, and it pays for both with a hypothesis on the *event*: `σ` must be **down**
wherever `ν` is up. At `k = 0` (`bdryUp_eq_empty`) the factor is `1` and what is left is
`FieldEnergy`'s bound over a **smaller** set of configurations, so the specialisation is
weaker there, not equal. The hypothesis is needed and not decoration: without it a boundary
site of `ν` where `σ` is already up moves the other way, `-2` instead of `+2`, and the
exchange relation would carry `exp (+2βh)`.

**In the intended use it costs nothing**, and that is a theorem rather than a remark: a down
cluster is down, so every configuration with `σ x = false` lies in the event of its own
cluster (`clusterEvent_cluster`), and the fibres of the cluster map exhaust that event
(`down_prob_le_cluster_sum`).

## What this is not

**It is S3b-i and nothing more.** The boundary-reaching branch needs a second Peierls
estimate, and this is only its **energy** half. The entropy half — S3b-ii, how many clusters of
a given perimeter reach the boundary from `x` — asks for a count of dual **paths** between
boundary points, and the estate counts only closed walks (`WalkCount`, `PlaqLocal`,
`PeierlsCover`). Nothing here begins it. Consequently:

* this is **not** a bound on the probability that `x` is down with a boundary-reaching cluster
  — that needs the union bound over clusters, which needs the count;
* `FieldInterior.interiorDown_expectation_le`'s missing second term is **not** supplied;
* `IsingBoundaryField.MagnetisationBound` is untouched, and stays false at `h = 0`
  (`BoundaryFieldRatio.magnetisationBound_zero_field_iff`).
-/

namespace FieldBoundaryEnergy

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField DualObstruction
open PlusCondition PeierlsConditional FieldCover

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The boundary sites a cluster occupies -/

/-- The boundary sites on which `ν` is up. For a cluster indicator this is the set of boundary
sites the cluster contains, and its cardinality is the `k` of the estimate. -/
def bdryUp (ν : Config n) : Finset (Site n) :=
  (Finset.univ : Finset (Site n)).filter (fun p => isBoundary p = true ∧ ν p = true)

/-- **The `+`-cut case is `k = 0`.** A configuration that is `false` at every boundary site
occupies none of them, so the correction factor below is `1` and the estimate collapses to
`FieldEnergy.gibbs_field_bound_of_cut`'s. This is what makes the file a generalisation rather
than a different theorem. -/
theorem bdryUp_eq_empty {ν : Config n} (hν : ∀ p : Site n, isBoundary p = true → ν p = false) :
    bdryUp ν = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun p _ => ?_
  rintro ⟨hb, hv⟩
  rw [hν p hb] at hv
  exact Bool.noConfusion hv

/-! ## 2. Flipping the cluster up raises the boundary term by exactly `2k` -/

/-- **THE ARITHMETIC THE `+`-CUT HYPOTHESIS WAS HIDING.** If `σ` is down wherever `ν` is up,
then exclusive-or with `ν` moves each of `ν`'s `k` boundary sites from `-1` to `+1` and leaves
the rest of the boundary alone, so `boundaryTerm` rises by `2k`.

Compare `FieldEnergy.boundaryTerm_xorC`, which is this at `k = 0`: there `ν` is `false` on the
boundary, nothing moves, and the field term is invariant. -/
theorem boundaryTerm_xorC_of_down {σ ν : Config n}
    (hdown : ∀ p : Site n, ν p = true → σ p = false) :
    boundaryTerm n (xorC σ ν) = boundaryTerm n σ + 2 * ((bdryUp ν).card : ℝ) := by
  classical
  have hsum : boundaryTerm n (xorC σ ν) - boundaryTerm n σ
      = ∑ p : Site n, (if isBoundary p = true ∧ ν p = true then (2 : ℝ) else 0) := by
    rw [boundaryTerm, boundaryTerm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hb : isBoundary p = true
    · by_cases hv : ν p = true
      · have hs : σ p = false := hdown p hv
        simp [hb, hv, hs, xorC, spin]
        norm_num
      · have hv' : ν p = false := Bool.not_eq_true _ ▸ hv
        simp [hb, hv', xorC]
    · simp [hb]
  have hcount : (∑ p : Site n, (if isBoundary p = true ∧ ν p = true then (2 : ℝ) else 0))
      = 2 * ((bdryUp ν).card : ℝ) := by
    rw [← Finset.sum_filter, bdryUp, Finset.sum_const, nsmul_eq_mul]
    ring
  linarith [hsum, hcount]

/-! ## 3. The exchange relation, with the boundary sites paid for -/

/-- **THE EXCHANGE RELATION FOR A CLUSTER THAT REACHES THE BOUNDARY.** No `+`-cut hypothesis,
no inequality, and the field contributes an explicit `exp (-2βhk)` rather than cancelling. -/
theorem exp_isingHB_xorC_cluster {σ ν : Config n} (hsub : contour ν ⊆ contour σ)
    (hdown : ∀ p : Site n, ν p = true → σ p = false) (h β : ℝ) :
    Real.exp (-β * isingHB n h σ)
      = Real.exp (-(4 * β) * ((contour ν).card : ℝ))
        * Real.exp (-(2 * β * h) * ((bdryUp ν).card : ℝ))
        * Real.exp (-β * isingHB n h (xorC σ ν)) := by
  classical
  have hcard : ((contour (xorC σ ν)).card : ℝ)
      = ((contour σ).card : ℝ) - ((contour ν).card : ℝ) := by
    rw [contour_xor_of_subset hsub, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub,
      Nat.cast_sub (Finset.card_le_card hsub)]
  have hfree : Real.exp (-β * isingH n σ)
      = Real.exp (-(4 * β) * ((contour ν).card : ℝ)) * Real.exp (-β * isingH n (xorC σ ν)) := by
    rw [IsingContourGibbs.peierls_weight n β σ,
      IsingContourGibbs.peierls_weight n β (xorC σ ν), hcard]
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [FieldEnergy.exp_isingHB_split, FieldEnergy.exp_isingHB_split, hfree,
    boundaryTerm_xorC_of_down hdown]
  simp only [← Real.exp_add]
  ring_nf

/-! ## 4. The summed estimate -/

/-- The configurations the estimate is about: down on `ν`'s support, and with `ν`'s contour
inside their own. A configuration that is **down at `x`** belongs to the event of its own down
cluster (`clusterEvent_cluster`), which is how the estimate is meant to be used. -/
def ClusterEvent (ν σ : Config n) : Prop :=
  (∀ p : Site n, ν p = true → σ p = false) ∧ contour ν ⊆ contour σ

/-- **THE PEIERLS ENERGY ESTIMATE WITHOUT THE `+`-CUT HYPOTHESIS.** For **any** `ν`, at
**every** field strength and temperature: the boundary-field weight of the configurations that
are down on `ν`'s support and whose contour contains `ν`'s is at most
`exp (-4β|contour ν|) · exp (-2βhk)` times the whole partition sum, where `k` is the number of
boundary sites `ν` occupies.

At `k = 0` this is `FieldEnergy.gibbs_field_bound_of_cut` (`bdryUp_eq_empty`); at `k ≥ 1` with
`β, h > 0` it is strictly sharper (`cluster_factor_le`). -/
theorem gibbs_field_bound_of_cluster (ν : Config n) (h β : ℝ) :
    ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => ClusterEvent ν σ),
        Real.exp (-β * isingHB n h σ)
      ≤ Real.exp (-(4 * β) * ((contour ν).card : ℝ))
          * Real.exp (-(2 * β * h) * ((bdryUp ν).card : ℝ))
        * ∑ σ : Config n, Real.exp (-β * isingHB n h σ) := by
  classical
  set A := (Finset.univ : Finset (Config n)).filter (fun σ => ClusterEvent ν σ) with hA
  have hfac : ∀ σ ∈ A, Real.exp (-β * isingHB n h σ)
      = Real.exp (-(4 * β) * ((contour ν).card : ℝ))
          * Real.exp (-(2 * β * h) * ((bdryUp ν).card : ℝ))
        * Real.exp (-β * isingHB n h (xorC σ ν)) := by
    intro σ hσ
    obtain ⟨hdown, hsub⟩ := (Finset.mem_filter.mp hσ).2
    exact exp_isingHB_xorC_cluster hsub hdown h β
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
  have hinj : ∀ a ∈ A, ∀ b ∈ A, xorC a ν = xorC b ν → a = b := fun a _ b _ hEq => by
    have := congrArg (fun c => xorC c ν) hEq
    simpa [xorC_involutive ν a, xorC_involutive ν b] using this
  rw [← Finset.sum_image (f := fun c : Config n => Real.exp (-β * isingHB n h c)) hinj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun _ _ _ => Real.exp_nonneg _

/-- **AND THE CORRECTION IS AN IMPROVEMENT, NOT A COST.** At positive temperature and positive
field, a cluster touching the boundary at `k ≥ 1` sites is suppressed by a further factor of at
least `exp (-2βh)` relative to the field-free estimate. -/
theorem cluster_factor_le {ν : Config n} {h β : ℝ} (hβ : 0 < β) (hh : 0 < h)
    (hk : 1 ≤ (bdryUp ν).card) :
    Real.exp (-(2 * β * h) * ((bdryUp ν).card : ℝ)) ≤ Real.exp (-(2 * β * h)) := by
  refine Real.exp_le_exp.mpr ?_
  have h1 : (1 : ℝ) ≤ ((bdryUp ν).card : ℝ) := by exact_mod_cast hk
  nlinarith [mul_pos hβ hh]

/-! ## 5. Every configuration is in the event of its own down cluster -/

/-- The indicator of the down cluster of `x`: `true` exactly on it. The complement of
`FieldCover.clusterOff`, which is `false` there. -/
noncomputable def clusterOn (σ : Config n) (x : Site n) : Config n :=
  fun p => !(clusterOff σ x p)

theorem clusterOn_eq_true_iff {σ : Config n} {x p : Site n} :
    clusterOn σ x p = true ↔ (downGraph σ).Reachable x p := by
  rw [clusterOn, Bool.not_eq_true', clusterOff_eq_false_iff]

/-- Negating a configuration everywhere leaves its contour where it was: a bond is broken
exactly when its ends differ, and negation preserves difference. -/
theorem contour_not (τ : Config n) : contour (fun p => !(τ p)) = contour τ := by
  classical
  ext e
  induction e using Sym2.ind with
  | _ p q =>
    rw [mem_contour, mem_contour]
    constructor
    · rintro ⟨hadj, hne⟩
      exact ⟨hadj, fun hc => hne (by rw [hc])⟩
    · rintro ⟨hadj, hne⟩
      exact ⟨hadj, fun hc => hne (Bool.not_inj hc)⟩

theorem contour_clusterOn_subset {σ : Config n} {x : Site n} (hx : σ x = false) :
    contour (clusterOn σ x) ⊆ contour σ := by
  have : contour (clusterOn σ x) = contour (clusterOff σ x) := contour_not _
  rw [this]
  exact contour_clusterOff_subset hx

/-- **THE BRIDGE.** A configuration that is down at `x` belongs to the cluster event of its
own down cluster — with no hypothesis about whether that cluster reaches the boundary. So the
estimate above applies to the boundary-reaching branch, which is what it was built for. -/
theorem clusterEvent_cluster {σ : Config n} {x : Site n} (hx : σ x = false) :
    ClusterEvent (clusterOn σ x) σ :=
  ⟨fun _ hp => down_of_reachable hx (clusterOn_eq_true_iff.mp hp),
    contour_clusterOn_subset hx⟩

/-- **THE ESTIMATE ON A FIBRE OF THE CLUSTER MAP**, which is the form the union bound over
clusters would consume. Fixing the cluster shape `ν`, the configurations that are down at `x`
with exactly that cluster carry weight at most `exp (-4β|contour ν|) · exp (-2βhk)` of the
total.

**This is not yet a bound on the probability that `x` is down with a boundary-reaching
cluster.** That is the sum of these over all admissible `ν`, and how many there are — S3b-ii,
a count of dual paths between boundary points — is not addressed anywhere in the estate. -/
theorem gibbs_field_bound_at (ν : Config n) (x : Site n) (h β : ℝ) :
    ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => σ x = false ∧ clusterOn σ x = ν), Real.exp (-β * isingHB n h σ)
      ≤ Real.exp (-(4 * β) * ((contour ν).card : ℝ))
          * Real.exp (-(2 * β * h) * ((bdryUp ν).card : ℝ))
        * ∑ σ : Config n, Real.exp (-β * isingHB n h σ) := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.exp_nonneg _)
    (gibbs_field_bound_of_cluster ν h β)
  intro σ hσ
  obtain ⟨-, hx, hcl⟩ := Finset.mem_filter.mp hσ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hcl ▸ clusterEvent_cluster hx⟩

/-! ## 6. The fibres exhaust the event, so the estimate loses nothing -/

/-- The cluster shapes that actually occur at `x`: the image of the down configurations under
the cluster map. A finite set, and the one the entropy question is about. -/
noncomputable def clusters (x : Site n) : Finset (Config n) :=
  ((Finset.univ : Finset (Config n)).filter (fun σ => σ x = false)).image
    (fun σ => clusterOn σ x)

/-- **THE WHOLE DOWN-SITE PROBABILITY, REDUCED TO A SUM OVER CLUSTER SHAPES.** At every field
strength and temperature, with no boundary condition and **no case split**:

`P(x down) ≤ ∑_{ν occurring at x} exp (-4β|contour ν|) · exp (-2βh·k(ν))`.

Both branches of the dichotomy are here at once — a cluster that misses the boundary
contributes `k = 0`, one that reaches it contributes `k ≥ 1` and is suppressed further. The
`hdown` hypothesis of `gibbs_field_bound_of_cluster` costs nothing, because the fibres of the
cluster map partition the event and each configuration sits in its own fibre.

**AND THIS IS EXACTLY WHERE THE ROUTE STOPS.** The right-hand side is a sum over `clusters x`,
and **nothing in the estate bounds how many terms it has of each perimeter.** For the
boundary-*missing* shapes the interior chain answers it by counting dual circuits
(`PeierlsCover`, `SideLength`, `SeriesBound`); for the boundary-*reaching* shapes the edge
boundary is a dual **path** between boundary points, and no count of those exists here or in
Mathlib. That gap is `UNLOCK_WATCHLIST`'s S3b-ii, and this inequality is the precise statement
whose right-hand side it would have to bound. -/
theorem down_prob_le_cluster_sum (x : Site n) (h β : ℝ) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => σ x = false),
        Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ ∑ ν ∈ clusters x, Real.exp (-(4 * β) * ((contour ν).card : ℝ))
          * Real.exp (-(2 * β * h) * ((bdryUp ν).card : ℝ)) := by
  classical
  rw [div_le_iff₀ (FieldEnergy.partition_pos n h β)]
  have hmaps : ∀ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => σ x = false),
      clusterOn σ x ∈ clusters x := fun σ hσ => Finset.mem_image_of_mem _ hσ
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun σ => clusterOn σ x) (t := clusters x) hmaps
    (fun σ => Real.exp (-β * isingHB n h σ)), Finset.sum_mul]
  refine Finset.sum_le_sum fun ν _ => ?_
  rw [Finset.filter_filter]
  exact gibbs_field_bound_at ν x h β

end FieldBoundaryEnergy
