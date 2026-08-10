import FieldEnergy
import SeriesBound

/-!
# The classical half of Peierls, for the boundary-field model

The mapped field-model route splits a down site into two cases: its **down cluster** misses
the box boundary, or it reaches it. This file does the first case, in full, for the model
**with** the field and **without** any boundary condition — steps S1, S3a and the union bound
of the route, joined to `FieldEnergy`'s S4.

## The trick, and it is the whole file

The existing chain proves everything about a configuration that is up all along the boundary.
A configuration of the field model is not. But if the down cluster of `x` misses the
boundary, then **the configuration that is down exactly on that cluster and up everywhere
else is `+`** — by construction, not by hypothesis — and

* its contour is contained in the original's (a bond leaving the cluster has its far end up,
  or that end would be in the cluster), and
* it is down at `x`.

So `PeierlsConditional.cover_plusFamily` applies **to it**, and the containment carries the
circuit it produces back into the original's contour. **The chain is not generalised; it is
applied to a different configuration.**

## What comes out

> **`field_peierls_small`** — for the boundary-field Hamiltonian at **any** field strength
> `h`, with `8 e^{-4β} ≤ 1/2`, in **every** box and at every interior site: the probability
> that `x` is down **and its down cluster never touches the boundary** is at most
> `22 (8 e^{-4β})³`.

No boundary condition, no limit in `h`, an explicit temperature, and uniform in the box.

## What is missing, and it is one case

The other branch — the cluster **does** reach the boundary — is untouched, and it is not a
detail: at a fixed field strength most configurations in a large box have *some* boundary
spin down (`PlusClassVanishes`), so the event this file bounds is not the typical one. What
that branch needs is the geometric step S3b of the map: a cluster stretching from `x` to the
edge is long, and a long cluster has a long perimeter. **Not begun.**

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace FieldCover

open IsingFiniteVolume IsingContourEnergy IsingBoundaryField DualObstruction
open PlusCondition PeierlsConditional PeierlsCover SeriesBound

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. The down cluster -/

/-- Sites that are down, joined when they are lattice neighbours. The connected component of
`x` in this graph is the **down cluster** of `x`. -/
def downGraph (σ : Config n) : SimpleGraph (Site n) where
  Adj p q := adj p q ∧ σ p = false ∧ σ q = false
  symm := fun _ _ h => ⟨(adj_symm _ _).mp h.1, h.2.2, h.2.1⟩
  loopless := ⟨fun p h => adj_irrefl p h.1⟩

/-- Everything the cluster reaches is down. -/
theorem down_of_reachable {σ : Config n} {x p : Site n} (hx : σ x = false)
    (hr : (downGraph σ).Reachable x p) : σ p = false := by
  obtain ⟨w⟩ := hr
  induction w with
  | nil => exact hx
  | cons hadj _ ih => exact ih hadj.2.2

/-- The configuration that is down exactly on the down cluster of `x`. -/
noncomputable def clusterOff (σ : Config n) (x : Site n) : Config n :=
  fun p => if (downGraph σ).Reachable x p then false else true

theorem clusterOff_self (σ : Config n) (x : Site n) : clusterOff σ x x = false := by
  rw [clusterOff, if_pos (SimpleGraph.Reachable.refl x)]

theorem clusterOff_eq_false_iff {σ : Config n} {x p : Site n} :
    clusterOff σ x p = false ↔ (downGraph σ).Reachable x p := by
  rw [clusterOff]
  split <;> simp_all

/-- **If the cluster misses the boundary, the cluster configuration is `+`.** -/
theorem plusBoundary_clusterOff {σ : Config n} {x : Site n}
    (hmiss : ∀ p : Site n, (downGraph σ).Reachable x p → isBoundary p = false) :
    PlusBoundary (clusterOff σ x) := by
  intro p hp
  rw [clusterOff, if_neg]
  intro hr
  rw [hmiss p hr] at hp
  exact Bool.noConfusion hp

/-- **And its contour is inside the original's.** A bond leaving the cluster has its far end
up in `σ` — otherwise that end would be in the cluster — so the bond is broken in `σ` too. -/
theorem contour_clusterOff_subset {σ : Config n} {x : Site n} (hx : σ x = false) :
    contour (clusterOff σ x) ⊆ contour σ := by
  classical
  intro e he
  induction e using Sym2.ind with
  | _ p q =>
    obtain ⟨hadj, hne⟩ := (mem_contour _ p q).mp he
    -- exactly one endpoint is in the cluster
    have hkey : ∀ a b : Site n, adj a b → clusterOff σ x a = false →
        ¬ clusterOff σ x b = false → σ a ≠ σ b := by
      intro a b hab ha hb
      have hra : (downGraph σ).Reachable x a := clusterOff_eq_false_iff.mp ha
      have hda : σ a = false := down_of_reachable hx hra
      have hdb : σ b = true := by
        cases hcb : σ b
        · exact absurd (clusterOff_eq_false_iff.mpr
            (hra.trans (SimpleGraph.Adj.reachable ⟨hab, hda, hcb⟩))) hb
        · rfl
      rw [hda, hdb]
      exact Bool.noConfusion
    refine (mem_contour σ p q).mpr ⟨hadj, ?_⟩
    cases hp : clusterOff σ x p
    · exact hkey p q hadj hp (by rw [hp] at hne; intro hq; exact hne hq.symm)
    · have hq : clusterOff σ x q = false := by
        cases hq : clusterOff σ x q
        · rfl
        · exact absurd (hp.trans hq.symm) hne
      exact (hkey q p ((adj_symm p q).mp hadj) hq (by rw [hp]; exact Bool.noConfusion)).symm

/-! ## 2. So the covering applies, with no boundary condition on `σ` -/

/-- **THE COVERING, FOR THE FIELD MODEL.** If `x` is down and its down cluster never touches
the boundary, then some member of the Peierls family sits inside `σ`'s contour — with **no**
hypothesis on `σ` at the boundary. The chain is applied to `clusterOff σ x`, which is `+` by
construction, and the containment brings the circuit back. -/
theorem cover_field {σ : Config n} (hn : 0 < n) {x : Site n} (hx : σ x = false)
    (hmiss : ∀ p : Site n, (downGraph σ).Reachable x p → isBoundary p = false)
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    ∃ γ ∈ plusFamily (plaqOf x hi hj), γ ⊆ contour σ := by
  obtain ⟨γ, hγ, hsub⟩ := cover_plusFamily (plusBoundary_clusterOff hmiss) hn
    (clusterOff_self σ x) hi hj
  exact ⟨γ, hγ, hsub.trans (contour_clusterOff_subset hx)⟩

/-! ## 3. The union bound, against the boundary-field weight -/

/-- The event this file bounds: `x` is down and its down cluster stays off the boundary. -/
def DownInside (σ : Config n) (x : Site n) : Prop :=
  σ x = false ∧ ∀ p : Site n, (downGraph σ).Reachable x p → isBoundary p = false

/-- **THE PEIERLS BOUND FOR THE FIELD MODEL, INTERIOR CASE.** -/
theorem field_peierls (hn : 0 < n) (h β : ℝ) {x : Site n}
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x),
        Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ ∑ γ ∈ plusFamily (plaqOf x hi hj), Real.exp (-(4 * β) * (γ.card : ℝ)) := by
  classical
  rw [div_le_iff₀ (FieldEnergy.partition_pos n h β)]
  set A := (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x) with hA
  have hcov : ∀ σ ∈ A, ∃ γ, γ ∈ plusFamily (plaqOf x hi hj) ∧ γ ⊆ contour σ := by
    intro σ hσ
    obtain ⟨-, hx, hmiss⟩ := Finset.mem_filter.mp hσ
    exact cover_field hn hx hmiss hi hj
  choose! g hgS hgsub using hcov
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := plusFamily (plaqOf x hi hj)) hgS
    (fun σ => Real.exp (-β * isingHB n h σ)), Finset.sum_mul]
  refine Finset.sum_le_sum fun γ hγ => ?_
  calc ∑ σ ∈ A.filter (fun σ => g σ = γ), Real.exp (-β * isingHB n h σ)
      ≤ ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => γ ⊆ contour σ),
          Real.exp (-β * isingHB n h σ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.exp_nonneg _
        intro σ hσ
        obtain ⟨hσA, hgσ⟩ := Finset.mem_filter.mp hσ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hgσ ▸ hgsub σ hσA⟩
    _ ≤ Real.exp (-(4 * β) * (γ.card : ℝ)) * ∑ σ : Config n, Real.exp (-β * isingHB n h σ) :=
        FieldEnergy.gibbs_field_bound_of_cut (Finset.mem_filter.mp hγ).2 h β

/-- **AND IT IS SMALL, AT AN EXPLICIT TEMPERATURE, UNIFORMLY IN THE BOX AND THE FIELD.**
Under `8 e^{-4β} ≤ 1/2`, the boundary-field probability that `x` is down with a down cluster
that never touches the boundary is at most `22 (8 e^{-4β})³`.

**This is one of the two cases.** The other — the cluster reaches the boundary — is the
typical one at fixed `h` in a large box (`PlusClassVanishes`) and is not treated here. -/
theorem field_peierls_small (hn : 0 < n) (h : ℝ) {β : ℝ}
    (hβ : 8 * Real.exp (-(4 * β)) ≤ 1 / 2) {x : Site n}
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => DownInside σ x),
        Real.exp (-β * isingHB n h σ)) /
      (∑ σ : Config n, Real.exp (-β * isingHB n h σ))
      ≤ 22 * (8 * Real.exp (-(4 * β))) ^ 3 :=
  le_trans (field_peierls hn h β hi hj)
    (le_trans (plusFamily_sum_le _ β) (sum_le_cube β hβ _))

end FieldCover
