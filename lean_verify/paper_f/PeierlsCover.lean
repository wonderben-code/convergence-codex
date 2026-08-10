import DualFamily

/-!
# The family covers, and the Peierls bound over an explicit family

`DualFamily` built the family and bounded its size; what it did not prove is that the family
**catches every down configuration**, which is what `PeierlsUnion`'s union bound needs. This
file proves it, and assembles the two into a bound whose right-hand side is a sum over an
explicitly constructed finite set of contours.

## The covering, and the one move it needs

`RayWalk.exists_circuit_near_of_down` gives, for a down site `x`, a circuit of the dual
decomposition together with a cycle walk `p` traversing it and a plaquette `P` of that
circuit lying in `PlaqLocal.ball (plaqAt x) (L + 1)`. The family is indexed by walks **based
at** a plaquette of the ball, and `p` is based wherever the decomposition happened to start
it. **`Walk.rotate` is the whole difference**: rotate `p` to start at `P`. Rotation permutes
the edge list (`Walk.rotate_edges`), and a walk's `toSubgraph` is read off its edge list, so
the rotated walk cuts out the same graph and therefore the same bonds — and
`Walk.IsCycle.rotate` keeps it a cycle.

## What is proved

* **`cover_cycCandidates`** — a `+`-boundary down site's circuit is a member of the family,
  at `r = L + 1` and its own length `L`, and is a realised contour;
* **`peierls_family_bound`** — hence the weight of the **`+`-boundary** configurations with
  `x` down, over the **full** partition function, is at most `∑_{γ ∈ S} exp (-4β |γ|)`,
  where `S` is the union over `L ≤ card (Plaq n)` of the family.

`S` is a finite set built without reference to any configuration, and
`card_peierlsFamily_le` bounds it by `∑_{L} (2L + 3) ^ 2 * 4 ^ L`.

## What is still missing — three things, and none of them is geometry

1. **It is not the conditional probability.** The numerator is restricted to `+`-boundary
   configurations, because that is where the covering holds, while the denominator is the
   whole partition function. The ratio is therefore *smaller* than
   `P(x down | + boundary)`, so the statement is true and weaker. Conditioning properly
   needs `ContourSubtract`'s injection redone **inside** the `+` class — which is possible,
   the boundary ring staying monochromatic when a contour is removed from it, and is not
   done.
2. **The lengths are not read off.** To reach `∑_L (2L + 3) ^ 2 * 4 ^ L * exp (-4βL)` one
   needs `|γ| = L` for a member coming from a length-`L` cycle — which is
   `CircuitLength.card_bonds_eq_length` **re-proved without a configuration**, its
   hypothesis being `H ≤ dualGraph σ` where the family has only `H ≤ fullDual`. The proof
   transfers unchanged; it is not transferred here.
3. **The series.** Its convergence for large `β` is unformalised.

**`IsingBoundaryField.MagnetisationBound` is untouched.**
-/

namespace PeierlsCover

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds PlaqLocal DualFamily
open SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Walks with the same edges cut out the same graph -/

/-- If two closed walks have the same edges, their spanning subgraphs agree — and hence so
do their bond sets. `Walk.adj_toSubgraph_iff_mem_edges` is the whole content. -/
theorem spanningCoe_eq_of_edges_iff {G G' : SimpleGraph (Plaq n)} {u v : Plaq n}
    {p : G.Walk u u} {q : G'.Walk v v} (h : ∀ e, e ∈ p.edges ↔ e ∈ q.edges) :
    (p.toSubgraph.spanningCoe : SimpleGraph (Plaq n)) = q.toSubgraph.spanningCoe := by
  ext a b
  simp only [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_iff_mem_edges]
  exact h _

/-! ## 2. The cycle-filtered family

Filtering to cycles costs nothing in the count and is what makes the length of the walk
equal to the size of the bond set — the step this file does **not** take, but which the
next one will want. -/

/-- The bond sets of closed dual **cycles** of length `L` based within `r` of `P₀`. -/
noncomputable def cycCandidates (P₀ : Plaq n) (r L : ℕ) : Finset (Finset (Sym2 (Site n))) :=
  (ball P₀ r).biUnion fun Q =>
    (((fullDual n).finsetWalkLength L Q Q).filter fun w => w.IsCycle).image fun w =>
      sideBonds (w.toSubgraph.spanningCoe : SimpleGraph (Plaq n))

theorem card_cycCandidates_le (P₀ : Plaq n) (r L : ℕ) :
    (cycCandidates P₀ r L).card ≤ (2 * r + 1) ^ 2 * 4 ^ L := by
  calc (cycCandidates P₀ r L).card
      ≤ ∑ Q ∈ ball P₀ r,
          ((((fullDual n).finsetWalkLength L Q Q).filter fun w => w.IsCycle).image fun w =>
            sideBonds (w.toSubgraph.spanningCoe : SimpleGraph (Plaq n))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ Q ∈ ball P₀ r, ((fullDual n).finsetWalkLength L Q Q).card :=
        Finset.sum_le_sum fun Q _ =>
          le_trans Finset.card_image_le (Finset.card_filter_le _ _)
    _ ≤ (2 * r + 1) ^ 2 * 4 ^ L := DualFamily.card_closed_walks_ball_le P₀ r L

/-! ## 3. The covering -/

/-- **A down site's circuit is in the family.** The rotation is the only move: the
decomposition's cycle starts wherever it starts, and the family is indexed by cycles based
at a plaquette of the ball. -/
theorem cover_cycCandidates {σ : Config n} (hσ : PlusBoundary σ) (hn : 0 < n) {x : Site n}
    (hx : σ x = false) :
    ∃ L : ℕ, ∃ γ ∈ cycCandidates (RayWalk.plaqAt hσ hx) (L + 1) L,
      γ ⊆ contour σ ∧ γ ∈ IsingContourInvariant.realisedContours n ∧
        L ≤ Fintype.card (Plaq n) := by
  classical
  obtain ⟨Ls, H, v, p, P, hcyc, hpair, hsup, hHL, hp, hH, hPs, -, -, -, -, hball⟩ :=
    RayWalk.exists_circuit_near_of_down hσ hn hx
  have hle : H ≤ dualGraph σ := hsup ▸ le_foldr_sup_of_mem hHL
  have hfull : H ≤ fullDual n := le_trans hle (dualGraph_le_fullDual σ)
  -- rotate the cycle to start at the anchor plaquette, then move it into the full dual
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
  refine ⟨p.length, sideBonds H, ?_, ?_, sideBonds_mem_realised hσ hle (hcyc H hHL), ?_⟩
  · refine Finset.mem_biUnion.mpr ⟨P, hball, ?_⟩
    refine Finset.mem_image.mpr ⟨q, ?_, by rw [hgraph]⟩
    exact Finset.mem_filter.mpr
      ⟨mem_finsetWalkLength_iff.mpr (by rw [hlen]), hqcyc⟩
  · rw [← bonds_eq_sideBonds hle]
    exact bonds_subset σ H
  · -- a cycle's length is at most the number of vertices, its support tail being nodup
    have hnodup := hp.support_nodup
    have : p.support.tail.length ≤ Fintype.card (Plaq n) := hnodup.length_le_card
    simpa using this

/-! ## 4. The family, and the bound over it

Two things the draft of this section got wrong, both fixed by narrowing the statement
rather than by widening a claim.

**The members must be known to be realised contours**, and an arbitrary cycle of `fullDual`
is not known to be one: `DualFamily.sideBonds_mem_realised` needs the cycle to sit inside
some `dualGraph σ`. So the family is **filtered** to the realised ones. Nothing is lost —
the member the covering produces is realised, by that very lemma — and the size bound
survives a filter untouched.

**And the configurations must be the `+`-boundary ones.** The covering only holds under `+`
boundary conditions, so the numerator counts `+`-boundary down configurations. The
denominator is the **full** partition function, which makes the ratio smaller than the
conditional probability — so this is a true statement and a weaker one. Getting the
conditional probability instead needs `ContourSubtract`'s injection redone **inside** the
`+` class, which is not done. -/

/-- The plaquette at an interior site, named without a down-ness proof in it. -/
def plaqOf (x : Site n) (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) : Plaq n :=
  ⟨x.1.val, x.2.val, hi, hj⟩

theorem plaqAt_eq_plaqOf {σ : Config n} (hσ : PlusBoundary σ) {x : Site n}
    (hx : σ x = false) (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    RayWalk.plaqAt hσ hx = plaqOf x hi hj := rfl

/-- The whole family: the **realised** bond sets of dual cycles of every length a cycle can
have, anchored within `L + 1` of `P₀`. -/
noncomputable def peierlsFamily (P₀ : Plaq n) : Finset (Finset (Sym2 (Site n))) :=
  ((Finset.range (Fintype.card (Plaq n) + 1)).biUnion fun L =>
    cycCandidates P₀ (L + 1) L).filter fun γ => γ ∈ IsingContourInvariant.realisedContours n

theorem card_peierlsFamily_le (P₀ : Plaq n) :
    (peierlsFamily P₀).card ≤
      ∑ L ∈ Finset.range (Fintype.card (Plaq n) + 1), (2 * (L + 1) + 1) ^ 2 * 4 ^ L :=
  le_trans (Finset.card_filter_le _ _)
    (le_trans Finset.card_biUnion_le
      (Finset.sum_le_sum fun L _ => card_cycCandidates_le P₀ (L + 1) L))

/-- **THE PEIERLS BOUND OVER AN EXPLICIT FAMILY.** The Boltzmann weight of the
`+`-boundary configurations with `x` down, over the full partition function, is at most the
sum of `exp (-4β |γ|)` over `peierlsFamily (plaqOf x)` — a finite set of contours built with
**no reference to any configuration**, whose size `card_peierlsFamily_le` bounds by
`∑_L (2L + 3) ^ 2 * 4 ^ L`.

**Two honest narrowings**, both forced and both stated in §4: the numerator is restricted to
`+`-boundary configurations, because that is where the covering holds; and the denominator
is the full partition function rather than the `+`-boundary one, which makes this weaker
than the conditional probability the textbook bounds.

**And the last simplification is missing**: turning `∑_{γ ∈ S} exp (-4β |γ|)` into
`∑_L (2L + 3) ^ 2 * 4 ^ L * exp (-4βL)` needs `|γ| = L` for members coming from length-`L`
cycles — `CircuitLength.card_bonds_eq_length` re-proved for `fullDual` — and then the
series. -/
theorem peierls_family_bound (hn : 0 < n) (β : ℝ) {x : Site n}
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
      (∑ σ : Config n, Real.exp (-β * isingH n σ)) ≤
      ∑ γ ∈ peierlsFamily (plaqOf x hi hj), Real.exp (-(4 * β) * (γ.card : ℝ)) := by
  classical
  refine PeierlsUnion.peierls_ratio_bound hn β _ _ (fun γ hγ => (Finset.mem_filter.mp hγ).2) ?_
  intro σ hσ
  obtain ⟨-, hplus, hdown⟩ := Finset.mem_filter.mp hσ
  obtain ⟨L, γ, hγ, hsub, hreal, hL⟩ := cover_cycCandidates hplus hn hdown
  refine ⟨γ, Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr
    ⟨L, Finset.mem_range.mpr (by omega), ?_⟩, hreal⟩, hsub⟩
  rwa [plaqAt_eq_plaqOf hplus hdown hi hj] at hγ

end PeierlsCover
