import PlusCondition

/-!
# Peierls, conditioned: the probability of a down site given `+` boundary conditions

`PlusCondition` proved the energy estimate with `+`-boundary configurations on both sides
and left the union bound to be re-run against `+`-boundary denominators. This file does
that, and the result is the first statement in this chain that is a **conditional
probability**:

> **`peierls_conditional_small`** — for every `ε > 0`, at every low enough temperature, for
> **every box** and every interior site, the Gibbs probability that the site is down,
> **conditioned on `+` boundary conditions**, is less than `ε`.

## What had to be generalised, and why that is a review finding

`PlusCondition.gibbs_plus_bound` is stated for `bonds σ H` — a circuit of a particular
configuration's decomposition. The union bound needs it for **each member of the family**,
and membership in the family does not carry that data. **The proof never used it.** What it
used was: there is a configuration whose contour is `γ` and which is `false` on the
boundary. That is `IsPlusCut` below, and `gibbs_plus_bound_of_cut` is the same argument
against it — so the earlier theorem was **stated less generally than it was proved**, which
is the mirror image of the failure this project usually catches, and is recorded as such.

## The covering, re-derived

`PeierlsCover.cover_cycCandidates` returns a family member together with the two facts its
own file needed. This file needs a third — that the member is a `+`-cut — so the covering
is re-derived here from `RayWalk.exists_circuit_near_of_down` with that component added —
thirty-odd lines duplicated, the alternative being to move `IsPlusCut` backwards through
five files so that `PeierlsCover` could mention it.

## What is left

`IsingBoundaryField.MagnetisationBound` is stated for `isingMeasure n h β` — the
boundary-**field** Hamiltonian over **all** configurations. This is the field-free
Hamiltonian **conditioned** on `+` boundary. Three things still separate them, none begun:
the `h → 0⁺` limit relating the two set-ups, the extension from interior sites to all sites,
and the passage from a probability to `∫ magnetisation`. **Untouched.**
-/

namespace PeierlsConditional

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingContourPlaquette IsingBoundaryField IsingContourInvariant
open DualObstruction PlaquetteLattice DualGraph DualBonds RayWalk CircuitCut
open DualFamily PeierlsCover SideLength SeriesBound PlusCondition Filter SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Bond sets that can be removed without leaving the `+` class -/

/-- A bond set is a **`+`-cut** when some configuration realising it is `false` on the whole
boundary. Exclusive-or with that configuration is then an involution of the `+` class that
removes exactly these bonds. -/
def IsPlusCut (γ : Finset (Sym2 (Site n))) : Prop :=
  ∃ τ : Config n, contour τ = γ ∧ ∀ p : Site n, isBoundary p = true → τ p = false

/-- **A circuit's bonds are a `+`-cut** — `CircuitCut` for the contour and
`PlusCondition.tau_boundary_false` for the boundary. -/
theorem isPlusCut_bonds {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) : IsPlusCut (bonds σ H) :=
  ⟨tau σ H, contour_tau hσ hle hcyc, fun _ hp => tau_boundary_false hσ hle hcyc hp⟩

/-! ## 2. The energy estimate against a `+`-cut

The same argument as `PlusCondition.gibbs_plus_bound`, with the cut configuration taken from
the hypothesis instead of built from a circuit. -/

theorem plus_partition_pos (β : ℝ) :
    0 < ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
      Real.exp (-β * isingH n σ) := by
  refine Finset.sum_pos (fun σ _ => Real.exp_pos _) ⟨fun _ => true, ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩

/-- **THE CONDITIONED ENERGY ESTIMATE.** For a `+`-cut `γ`, the weight of the `+`-boundary
configurations whose contour contains `γ` is at most `exp (-4β |γ|)` times the weight of all
`+`-boundary configurations. -/
theorem gibbs_plus_bound_of_cut {γ : Finset (Sym2 (Site n))} (hγ : IsPlusCut γ) (β : ℝ) :
    ∑ σ' ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ' => PlusBoundary σ' ∧ γ ⊆ contour σ'), Real.exp (-β * isingH n σ') ≤
      Real.exp (-(4 * β) * (γ.card : ℝ)) *
        ∑ σ' ∈ (Finset.univ : Finset (Config n)).filter (fun σ' => PlusBoundary σ'),
          Real.exp (-β * isingH n σ') := by
  classical
  obtain ⟨τ, hcon, hbdy⟩ := hγ
  set A := (Finset.univ : Finset (Config n)).filter
    (fun σ' => PlusBoundary σ' ∧ γ ⊆ contour σ') with hA
  have hfac : ∀ σ' ∈ A, Real.exp (-β * isingH n σ') =
      Real.exp (-(4 * β) * (γ.card : ℝ)) * Real.exp (-β * isingH n (xorC σ' τ)) := by
    intro σ' hσ'
    obtain ⟨-, -, hsub⟩ := Finset.mem_filter.mp hσ'
    have hsub' : contour τ ⊆ contour σ' := hcon ▸ hsub
    have hcard : ((contour (xorC σ' τ)).card : ℝ) =
        ((contour σ').card : ℝ) - (γ.card : ℝ) := by
      rw [contour_xor_of_subset hsub', Finset.card_sdiff, Finset.inter_eq_left.mpr hsub',
        hcon, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [IsingContourGibbs.peierls_weight n β σ',
      IsingContourGibbs.peierls_weight n β (xorC σ' τ), hcard]
    simp only [← Real.exp_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  have hinj : ∀ a ∈ A, ∀ b ∈ A, xorC a τ = xorC b τ → a = b := fun a _ b _ hEq => by
    have := congrArg (fun c => xorC c τ) hEq
    simpa [xorC_involutive τ a, xorC_involutive τ b] using this
  rw [← Finset.sum_image (f := fun c : Config n => Real.exp (-β * isingH n c)) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.exp_nonneg _
  intro c hc
  obtain ⟨σ', hσ'A, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨-, hplus, -⟩ := Finset.mem_filter.mp hσ'A
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => ?_⟩
  simp only [xorC, hplus p hp, hbdy p hp]
  rfl

/-! ## 3. The family, filtered to `+`-cuts, and the covering -/

/-- The Peierls family, kept only where its members can be removed inside the `+` class. -/
noncomputable def plusFamily (P₀ : Plaq n) : Finset (Finset (Sym2 (Site n))) :=
  (peierlsFamily P₀).filter fun γ => IsPlusCut γ

/-- **The covering, with the `+`-cut property.** Re-derived from
`RayWalk.exists_circuit_near_of_down` because `PeierlsCover.cover_cycCandidates` returns
only what its own file needed. -/
theorem cover_plusFamily {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n) {x : Site n}
    (hx : σ x = false) (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    ∃ γ ∈ plusFamily (plaqOf x hi hj), γ ⊆ contour σ := by
  classical
  obtain ⟨Ls, H, v, p, P, hcyc, hpair, hsup, hHL, hp, hH, hPs, -, -, -, -, hball⟩ :=
    RayWalk.exists_circuit_near_of_down hσ hn hx
  have hle : H ≤ dualGraph σ := hsup ▸ le_foldr_sup_of_mem hHL
  have hfull : H ≤ fullDual n := le_trans hle (dualGraph_le_fullDual σ)
  set q : (fullDual n).Walk P P := (p.rotate P hPs).mapLe hfull with hq
  have hedges : ∀ e, e ∈ q.edges ↔ e ∈ p.edges := by
    intro e
    rw [hq, Walk.edges_mapLe_eq_edges]
    exact (p.rotate_edges P hPs).mem_iff
  have hlen : q.length = p.length := by
    rw [hq, Walk.length_mapLe, ← Walk.length_edges, ← Walk.length_edges]
    exact ((p.rotate_edges P hPs).perm).length_eq
  have hgraph : (q.toSubgraph.spanningCoe : SimpleGraph (Plaq n)) = H := by
    rw [← hH]
    exact spanningCoe_eq_of_edges_iff hedges
  have hqcyc : q.IsCycle := ((hp.rotate hPs).mapLe hfull)
  have hlenle : p.length ≤ Fintype.card (Plaq n) := by
    have := hp.support_nodup.length_le_card
    simpa using this
  refine ⟨sideBonds H, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_biUnion.mpr ⟨p.length, Finset.mem_range.mpr (by omega), ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · -- the rotated cycle exhibits the member, based at the anchor plaquette
    refine Finset.mem_biUnion.mpr ⟨P, ?_, ?_⟩
    · rwa [plaqAt_eq_plaqOf hσ hx hi hj] at hball
    · exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr
        ⟨mem_finsetWalkLength_iff.mpr (by rw [hlen]), hqcyc⟩, by rw [hgraph]⟩
  · exact sideBonds_mem_realised hσ hle (hcyc H hHL)
  · exact bonds_eq_sideBonds hle ▸ isPlusCut_bonds hσ hle (hcyc H hHL)
  · exact bonds_eq_sideBonds hle ▸ bonds_subset σ H

/-! ## 4. The union bound, conditioned -/

/-- **THE CONDITIONAL PEIERLS BOUND.** The Gibbs probability that `x` is down, **given `+`
boundary conditions**, is at most the Peierls sum over the family. -/
theorem peierls_conditional (hn : 0 < n) (β : ℝ) {x : Site n}
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
        Real.exp (-β * isingH n σ)) ≤
      ∑ γ ∈ plusFamily (plaqOf x hi hj), Real.exp (-(4 * β) * (γ.card : ℝ)) := by
  classical
  rw [div_le_iff₀ (plus_partition_pos β)]
  set A := (Finset.univ : Finset (Config n)).filter
    (fun σ => PlusBoundary σ ∧ σ x = false) with hA
  have hcov : ∀ σ ∈ A, ∃ γ, γ ∈ plusFamily (plaqOf x hi hj) ∧ γ ⊆ contour σ := by
    intro σ hσ
    obtain ⟨-, hplus, hdown⟩ := Finset.mem_filter.mp hσ
    obtain ⟨γ, hγ, hsub⟩ := cover_plusFamily hplus hn hdown hi hj
    exact ⟨γ, hγ, hsub⟩
  choose! g hgS hgsub using hcov
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := plusFamily (plaqOf x hi hj)) hgS
    (fun σ => Real.exp (-β * isingH n σ)), Finset.sum_mul]
  refine Finset.sum_le_sum fun γ hγ => ?_
  calc ∑ σ ∈ A.filter (fun σ => g σ = γ), Real.exp (-β * isingH n σ)
      ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter
          (fun σ => PlusBoundary σ ∧ γ ⊆ contour σ), Real.exp (-β * isingH n σ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.exp_nonneg _
        intro σ hσ
        obtain ⟨hσA, hgσ⟩ := Finset.mem_filter.mp hσ
        obtain ⟨-, hplus, -⟩ := Finset.mem_filter.mp hσA
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hplus, hgσ ▸ hgsub σ hσA⟩
    _ ≤ Real.exp (-(4 * β) * (γ.card : ℝ)) *
          ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
            Real.exp (-β * isingH n σ) :=
        gibbs_plus_bound_of_cut (Finset.mem_filter.mp hγ).2 β

/-! ## 5. And it is small at low temperature, uniformly in the box -/

theorem plusFamily_sum_le (P₀ : Plaq n) (β : ℝ) :
    ∑ γ ∈ plusFamily P₀, Real.exp (-(4 * β) * (γ.card : ℝ)) ≤
      ∑ L ∈ Finset.Ico 3 (Fintype.card (Plaq n) + 1),
        ((2 * (L + 1) + 1) ^ 2 * 4 ^ L : ℕ) * Real.exp (-(4 * β) * (L : ℝ)) :=
  le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun _ _ _ => Real.exp_nonneg _)
    (sum_family_le P₀ β)

/-- **PEIERLS, CONDITIONED AND SMALL.** For every `ε > 0`, at every low enough temperature,
for **every box** and every interior site, the Gibbs probability that the site is down
**given `+` boundary conditions** is less than `ε`.

This is the Peierls estimate in the shape the argument is usually quoted in. What it is
**not** is `IsingBoundaryField.MagnetisationBound`, which is stated for the boundary-field
measure over all configurations; the header lists the three things that still separate
them. -/
theorem peierls_conditional_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ β : ℝ in atTop, ∀ (n : ℕ), 0 < n → ∀ x : Site n,
      ∀ (_ : x.1.val + 1 < n) (_ : x.2.val + 1 < n),
        (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
            (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
          (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => PlusBoundary σ),
            Real.exp (-β * isingH n σ)) < ε := by
  filter_upwards [eventually_threshold, tendsto_bound.eventually (gt_mem_nhds hε)]
    with β hthr hsmall n hn x hi hj
  refine lt_of_le_of_lt (le_trans (peierls_conditional hn β hi hj) ?_) hsmall
  exact le_trans (plusFamily_sum_le _ β) (sum_le_cube β hthr _)

end PeierlsConditional
