import PeierlsCover

/-!
# A member of the family has as many bonds as the cycle is long

`PeierlsCover` bounds the down-weight by `∑_{γ ∈ S} exp (-4β |γ|)` over an explicit family
`S`, and named the reason that was not yet the textbook's `∑_L (2L + 3)^2 4^L exp(-4βL)`:
**`|γ| = L` is not read off the cycle**. `CircuitLength.card_bonds_eq_length` says exactly
that, and its hypothesis is `H ≤ dualGraph σ` where the family has only `H ≤ fullDual`.

Its proof never used the configuration. This file transfers it, and the transfer is
literal: `CircuitLength.sideOf_eq_iff_edge_eq` — the bijection's whole content — already
takes nothing but two adjacencies. What had to be re-made are the three private helpers
that name a witness for a bond, because they were stated against `DualBonds.bonds`.

## What it gives

* **`card_sideBonds_eq_ncard_edgeSet`** — for `H ≤ fullDual`, the bonds `H` crosses are as
  many as `H` has edges;
* **`card_sideBonds_cycle`** — hence for a cycle, as many as the cycle is long;
* **`card_of_mem_cycCandidates`** — so **every member of `PeierlsCover.cycCandidates P₀ r L`
  has exactly `L` bonds**, which is what makes the family graded by length;
* and therefore §4: **`peierls_closed_form`**, the estimate with an explicit right-hand
  side, `∑_{3 ≤ L ≤ card (Plaq n)} (2L + 3)^2 * 4^L * exp (-4βL)`. The grading is what makes the
  sum split by cardinality; each fibre is then bounded by the walk count.

## What is still missing — two things, and they are not the same kind

1. **It is not the conditional probability**, exactly as `PeierlsCover` records: the
   numerator is restricted to `+`-boundary configurations and the denominator is the whole
   partition function. Conditioning properly needs `ContourSubtract`'s injection redone
   inside the `+` class.
2. **Nothing says the right-hand side is small.** It is small for large `β`, by a geometric
   comparison, and **that comparison is not formalised**. Until it is, `peierls_closed_form`
   is a true inequality that excludes nothing — which is worth saying plainly, because a
   closed form is exactly the kind of result that reads as finished.

`IsingBoundaryField.MagnetisationBound` is untouched.
-/

namespace SideLength

open IsingFiniteVolume IsingContourEnergy IsingContourPlaquette IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds DualUnique CircuitLength
open DualFamily PeierlsCover SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Naming a witness, against `sideBonds` this time -/

private theorem exists_pickS {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)}
    (he : e ∈ sideBonds H) :
    ∃ pd : Plaq n × Fin 4, H.Adj pd.1 (partnerOf pd.1 pd.2) ∧ sideOf pd.1 pd.2 = e := by
  obtain ⟨P, d, h1, h2⟩ := mem_sideBonds.mp he
  exact ⟨(P, d), h1, h2⟩

private noncomputable def pickS {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)}
    (he : e ∈ sideBonds H) : Plaq n × Fin 4 := (exists_pickS he).choose

private theorem pickS_spec {H : SimpleGraph (Plaq n)} {e : Sym2 (Site n)}
    (he : e ∈ sideBonds H) :
    H.Adj (pickS he).1 (partnerOf (pickS he).1 (pickS he).2) ∧
      sideOf (pickS he).1 (pickS he).2 = e := (exists_pickS he).choose_spec

/-! ## 2. The count, without a configuration

The bijection is "the bond this edge crosses", exactly as in `CircuitLength`; the only
change is that surjectivity now reads the direction off `fullDual`'s adjacency rather than
off `dualAdj`, which carries one component fewer. -/

/-- **A subgraph of the full dual graph crosses as many primal bonds as it has edges.** -/
theorem card_sideBonds_eq_ncard_edgeSet {H : SimpleGraph (Plaq n)} (hle : H ≤ fullDual n) :
    (sideBonds H).card = H.edgeSet.ncard := by
  have hedge : H.edgeSet.ncard = H.edgeFinset.card := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [hedge]
  refine Finset.card_bij (fun e he => s((pickS he).1, partnerOf (pickS he).1 (pickS he).2))
    (fun e he => ?_) (fun e he e' he' hEq => ?_) (fun f hf => ?_)
  · rw [mem_edgeFinset, mem_edgeSet]
    exact (pickS_spec he).1
  · have h1 := pickS_spec he
    have h2 := pickS_spec he'
    rw [← h1.2, ← h2.2]
    exact (sideOf_eq_iff_edge_eq h1.1 h2.1).mpr hEq
  · rw [mem_edgeFinset] at hf
    induction f using Sym2.ind with
    | _ P Q =>
      have hadj : H.Adj P Q := hf
      obtain ⟨d, hQ, -⟩ := hle hadj
      have hadj' : H.Adj P (partnerOf P d) := hQ ▸ hadj
      have hmem : sideOf P d ∈ sideBonds H := mem_sideBonds.mpr ⟨P, d, hadj', rfl⟩
      refine ⟨sideOf P d, hmem, ?_⟩
      have h1 := pickS_spec hmem
      rw [hQ]
      exact (sideOf_eq_iff_edge_eq h1.1 hadj').mp h1.2

/-- **And for a cycle of the full dual graph, as many bonds as the cycle is long.** -/
theorem card_sideBonds_cycle {v : Plaq n} {w : (fullDual n).Walk v v} (hw : w.IsCycle) :
    (sideBonds (w.toSubgraph.spanningCoe : SimpleGraph (Plaq n))).card = w.length := by
  rw [card_sideBonds_eq_ncard_edgeSet (Subgraph.spanningCoe_le _)]
  exact ncard_edgeSet_spanningCoe_toSubgraph hw

/-! ## 3. So the family is graded by length -/

/-- **Every member of the family at length `L` has exactly `L` bonds.** This is what makes
the family graded: a member determines the `L` it came from, so the sum over the family can
be split by length. -/
theorem card_of_mem_cycCandidates {P₀ : Plaq n} {r L : ℕ} {γ : Finset (Sym2 (Site n))}
    (hγ : γ ∈ cycCandidates P₀ r L) : γ.card = L := by
  obtain ⟨Q, -, hγQ⟩ := Finset.mem_biUnion.mp hγ
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hγQ
  obtain ⟨hlen, hcyc⟩ := Finset.mem_filter.mp hw
  rw [card_sideBonds_cycle hcyc]
  exact mem_finsetWalkLength_iff.mp hlen

/-- The same for the whole family: a member that came from length `L` has `L` bonds, so the
family's members are sorted by their own cardinality. -/
theorem mem_peierlsFamily_card {P₀ : Plaq n} {γ : Finset (Sym2 (Site n))}
    (hγ : γ ∈ peierlsFamily P₀) :
    γ ∈ cycCandidates P₀ (γ.card + 1) γ.card ∧ γ.card ≤ Fintype.card (Plaq n) := by
  obtain ⟨hbi, -⟩ := Finset.mem_filter.mp hγ
  obtain ⟨L, hL, hγL⟩ := Finset.mem_biUnion.mp hbi
  have hcard : γ.card = L := card_of_mem_cycCandidates hγL
  exact ⟨hcard ▸ hγL, by rw [hcard]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hL)⟩

/-! ## 4. The closed form

With the length determined by the member, the sum over the family splits by cardinality —
`Finset.sum_fiberwise_of_maps_to` again — and each fibre is bounded by the walk count. -/

/-- **A member of the family has at least three bonds**, a cycle having length at least
three. Without this the closed form below would keep its `L = 0, 1, 2` terms, which
contribute at least `9` **at every `β`** — so the bound could never be small, and the claim
that it is small for large `β` would be false rather than merely unproved (ERRATUM 85). -/
theorem three_le_card_of_mem_cycCandidates {P₀ : Plaq n} {r L : ℕ}
    {γ : Finset (Sym2 (Site n))} (hγ : γ ∈ cycCandidates P₀ r L) : 3 ≤ γ.card := by
  obtain ⟨Q, -, hγQ⟩ := Finset.mem_biUnion.mp hγ
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hγQ
  obtain ⟨-, hcyc⟩ := Finset.mem_filter.mp hw
  rw [card_sideBonds_cycle hcyc]
  exact hcyc.three_le_length

theorem three_le_card_of_mem_peierlsFamily {P₀ : Plaq n} {γ : Finset (Sym2 (Site n))}
    (hγ : γ ∈ peierlsFamily P₀) : 3 ≤ γ.card :=
  three_le_card_of_mem_cycCandidates (mem_peierlsFamily_card hγ).1

/-- **The sum over the family, in closed form.** Every member of cardinality `L` came from
a length-`L` cycle, so the fibre at `L` sits inside `cycCandidates P₀ (L + 1) L`, whose size
`PeierlsCover.card_cycCandidates_le` bounds. No sign hypothesis on `β`. -/
theorem sum_family_le (P₀ : Plaq n) (β : ℝ) :
    ∑ γ ∈ peierlsFamily P₀, Real.exp (-(4 * β) * (γ.card : ℝ)) ≤
      ∑ L ∈ Finset.Ico 3 (Fintype.card (Plaq n) + 1),
        ((2 * (L + 1) + 1) ^ 2 * 4 ^ L : ℕ) * Real.exp (-(4 * β) * (L : ℝ)) := by
  classical
  have hmaps : ∀ γ ∈ peierlsFamily P₀,
      γ.card ∈ Finset.Ico 3 (Fintype.card (Plaq n) + 1) := fun γ hγ =>
    Finset.mem_Ico.mpr ⟨three_le_card_of_mem_peierlsFamily hγ,
      Nat.lt_succ_of_le (mem_peierlsFamily_card hγ).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun γ => Real.exp (-(4 * β) * (γ.card : ℝ)))]
  refine Finset.sum_le_sum fun L _ => ?_
  have hval : ∀ γ ∈ (peierlsFamily P₀).filter (fun γ => γ.card = L),
      Real.exp (-(4 * β) * (γ.card : ℝ)) = Real.exp (-(4 * β) * (L : ℝ)) := by
    intro γ hγ
    rw [(Finset.mem_filter.mp hγ).2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  have hsub : (peierlsFamily P₀).filter (fun γ => γ.card = L) ⊆ cycCandidates P₀ (L + 1) L := by
    intro γ hγ
    obtain ⟨hfam, hcard⟩ := Finset.mem_filter.mp hγ
    exact hcard ▸ (mem_peierlsFamily_card hfam).1
  exact_mod_cast Nat.cast_le.mpr
    (le_trans (Finset.card_le_card hsub) (card_cycCandidates_le P₀ (L + 1) L))

/-- **THE SAME SUM WITH THE TEXTBOOK CONSTANT `3`.** Identical to `sum_family_le` except
that the fibre bound is `PeierlsCover.card_cycCandidates_le_two_three`, which keeps the
`IsCycle` hypothesis instead of discarding it. The sum starts at `3`, so the `1 ≤ L` side
condition is free.

`ERRATUM 126`: this is the count the threshold actually consumes, which a paragraph in
`WalkCount` got wrong earlier the same day. -/
theorem sum_family_le_three (P₀ : Plaq n) (β : ℝ) :
    ∑ γ ∈ peierlsFamily P₀, Real.exp (-(4 * β) * (γ.card : ℝ)) ≤
      ∑ L ∈ Finset.Ico 3 (Fintype.card (Plaq n) + 1),
        ((2 * (L + 1) + 1) ^ 2 * (2 * 3 ^ L) : ℕ) * Real.exp (-(4 * β) * (L : ℝ)) := by
  classical
  have hmaps : ∀ γ ∈ peierlsFamily P₀,
      γ.card ∈ Finset.Ico 3 (Fintype.card (Plaq n) + 1) := fun γ hγ =>
    Finset.mem_Ico.mpr ⟨three_le_card_of_mem_peierlsFamily hγ,
      Nat.lt_succ_of_le (mem_peierlsFamily_card hγ).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun γ => Real.exp (-(4 * β) * (γ.card : ℝ)))]
  refine Finset.sum_le_sum fun L _ => ?_
  have hval : ∀ γ ∈ (peierlsFamily P₀).filter (fun γ => γ.card = L),
      Real.exp (-(4 * β) * (γ.card : ℝ)) = Real.exp (-(4 * β) * (L : ℝ)) := by
    intro γ hγ
    rw [(Finset.mem_filter.mp hγ).2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  have hsub : (peierlsFamily P₀).filter (fun γ => γ.card = L) ⊆ cycCandidates P₀ (L + 1) L := by
    intro γ hγ
    obtain ⟨hfam, hcard⟩ := Finset.mem_filter.mp hγ
    exact hcard ▸ (mem_peierlsFamily_card hfam).1
  exact_mod_cast Nat.cast_le.mpr
    (le_trans (Finset.card_le_card hsub)
      (card_cycCandidates_le_two_three P₀ (L + 1) L))

/-- **THE PEIERLS ESTIMATE, IN CLOSED FORM.** The weight of the `+`-boundary configurations
with `x` down, over the full partition function, is at most

`∑_{3 ≤ L ≤ card (Plaq n)} (2L + 3) ^ 2 * 4 ^ L * exp (-4βL)`.

The sum **starts at three**, a cycle having length at least three, and that is not
cosmetic: with `L = 0, 1, 2` present the right-hand side would exceed `9` at every `β` and
could never be small (ERRATUM 85).

Every factor is explicit and none mentions the box except the range of the sum. **What this
is not**, exactly as `PeierlsCover` records: it is not the *conditional* probability — the
numerator is restricted to `+` boundary and the denominator is not — and **nothing here says
the right-hand side is small**. It is small for large `β`, by a geometric comparison that is
**not formalised**; without that this is a true inequality that does not yet exclude
anything. `IsingBoundaryField.MagnetisationBound` is untouched. -/
theorem peierls_closed_form (hn : 0 < n) (β : ℝ) {x : Site n}
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
      (∑ σ : Config n, Real.exp (-β * isingH n σ)) ≤
      ∑ L ∈ Finset.Ico 3 (Fintype.card (Plaq n) + 1),
        ((2 * (L + 1) + 1) ^ 2 * 4 ^ L : ℕ) * Real.exp (-(4 * β) * (L : ℝ)) :=
  le_trans (peierls_family_bound hn β hi hj) (sum_family_le _ β)

/-- The same, with `2 · 3 ^ L` in place of `4 ^ L`. -/
theorem peierls_closed_form_three (hn : 0 < n) (β : ℝ) {x : Site n}
    (hi : x.1.val + 1 < n) (hj : x.2.val + 1 < n) :
    (∑ σ ∈ (Finset.univ : Finset (Config n)).filter
        (fun σ => PlusBoundary σ ∧ σ x = false), Real.exp (-β * isingH n σ)) /
      (∑ σ : Config n, Real.exp (-β * isingH n σ)) ≤
      ∑ L ∈ Finset.Ico 3 (Fintype.card (Plaq n) + 1),
        ((2 * (L + 1) + 1) ^ 2 * (2 * 3 ^ L) : ℕ) * Real.exp (-(4 * β) * (L : ℝ)) :=
  le_trans (peierls_family_bound hn β hi hj) (sum_family_le_three _ β)

end SideLength
