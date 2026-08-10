import CircuitCut

/-!
# Removing a cut from a contour, and the energy side of Peierls' estimate

`CircuitCut` proved that a circuit's bonds are a realised contour, and named what the energy
side does with that: **remove the circuit from the contour**. This file builds the removal
and draws the estimate.

## The removal

If `δ ⊆ γ` are both realised contours then so is `γ \ δ`. The proof is parity bookkeeping,
not geometry: along any closed walk the crossings of `γ \ δ` and of `δ` add up to those of
`γ` (each edge lies in exactly one of the two, or in neither), so evenness of two of them
gives evenness of the third, and `IsingContourCocycle.realised_iff_cocycle` — *contours are
exactly the cocycles* — turns that back into a contour.

## The estimate

> **`peierls_energy_bound`** — for a realised contour `δ`, the Boltzmann weight of the
> configurations whose contour contains `δ` is at most `exp (-4β |δ|)` times the whole
> partition function.

That is Peierls' energy half, **in unnormalised form**: the sum over contours containing
`δ` is matched one-for-one with a sum over contours not containing it, by removing `δ`;
each term loses exactly `exp (-4β |δ|)` because the cardinalities subtract; and the
matched-into terms are a subset of all of them. `IsingContourEnergy`'s
`H(σ) = H(ground) + 4|γ(σ)|` enters only in `gibbs_bound_of_subset`, which is the same
statement written in Boltzmann weights. **Dividing by the partition function to get a
probability is not written here** — it is positive, so the division is routine, and it is
still not written. No β-sign hypothesis: the inequality holds at every temperature and is
*informative* only when β is positive, which is a fact about its use, not its truth.

## What this is not

**It is not the Peierls estimate.** That needs this bound summed over the circuits that can
surround a fixed site — for which the anchor set is `RayWalk.exists_circuit_near_of_down`
and the count is `PlaqLocal.card_closed_walks_ball_le`, and **the summation over lengths is
not begun**. `IsingBoundaryField.MagnetisationBound` is untouched.

The theorem itself does not mention circuits: `δ` is any realised contour. §5 connects it
to them — `bonds_mem_realised` puts a circuit's bonds in `realisedContours` via
`CircuitCut.exists_cut`, and `gibbs_bound_of_circuit` is the bound with a circuit in it.
-/

namespace ContourSubtract

open IsingFiniteVolume IsingContourEnergy IsingContourSeparation IsingContourClosed
open IsingContourInvariant IsingContourCocycle IsingBoundaryField
open DualObstruction PlaquetteLattice DualGraph DualBonds SimpleGraph

set_option linter.style.openClassical false
open scoped Classical

variable {n : ℕ}

/-! ## 1. Crossings split along a subset -/

/-- **Along any walk, the crossings of `γ \ δ` and of `δ` add to those of `γ`** when
`δ ⊆ γ`. Each edge of the walk is in `δ`, or in `γ \ δ`, or in neither. -/
theorem crossings_sdiff_add {γ δ : Finset (Sym2 (Site n))} (hsub : δ ⊆ γ) {u v : Site n}
    (w : (latticeGraph n).Walk u v) :
    crossings (γ \ δ) w + crossings δ w = crossings γ w := by
  induction w with
  | nil => simp
  | @cons a c d h p ih =>
    rw [crossings_cons, crossings_cons, crossings_cons]
    by_cases hd : s(a, c) ∈ δ
    · rw [if_pos hd, if_pos (hsub hd), if_neg (by simp [hd])]
      omega
    · by_cases hg : s(a, c) ∈ γ
      · rw [if_neg hd, if_pos hg, if_pos (Finset.mem_sdiff.mpr ⟨hg, hd⟩)]
        omega
      · rw [if_neg hd, if_neg hg, if_neg (by simp [hg])]
        omega

/-- **A cocycle minus a cocycle is a cocycle.** -/
theorem isCocycle_sdiff {γ δ : Finset (Sym2 (Site n))} (hsub : δ ⊆ γ) (hγ : IsCocycle γ)
    (hδ : IsCocycle δ) : IsCocycle (γ \ δ) := by
  intro u w
  have hadd := crossings_sdiff_add hsub w
  obtain ⟨a, ha⟩ := hγ u w
  obtain ⟨b, hb⟩ := hδ u w
  exact ⟨a - b, by omega⟩

/-! ## 2. So a realised contour minus a realised contour is realised

`realised_iff_cocycle` needs to know the bond set consists of adjacent pairs; for a subset
of a contour that is `IsingContourEnergy.mem_contour`. -/

theorem adj_of_mem_realised {γ : Finset (Sym2 (Site n))} (hγ : γ ∈ realisedContours n) :
    ∀ e ∈ γ, ∃ p q : Site n, e = s(p, q) ∧ adj p q := by
  simp only [realisedContours] at hγ
  obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hγ
  intro e he
  induction e using Sym2.ind with
  | _ p q => exact ⟨p, q, rfl, ((mem_contour σ p q).mp he).1⟩

/-- **Removing one realised contour from another leaves a realised contour.** -/
theorem realised_sdiff (hn : 0 < n) {γ δ : Finset (Sym2 (Site n))}
    (hγ : γ ∈ realisedContours n) (hδ : δ ∈ realisedContours n) (hsub : δ ⊆ γ) :
    γ \ δ ∈ realisedContours n := by
  refine (realised_iff_cocycle hn (γ \ δ) fun e he =>
    adj_of_mem_realised hγ e (Finset.mem_sdiff.mp he).1).mpr ?_
  exact isCocycle_sdiff hsub
    ((realised_iff_cocycle hn γ (adj_of_mem_realised hγ)).mp hγ)
    ((realised_iff_cocycle hn δ (adj_of_mem_realised hδ)).mp hδ)

/-! ## 3. The energy side

The map `γ ↦ γ \ δ` is injective on the contours containing `δ` — `δ` can be put back —
and the weight factorises because the cardinalities subtract. -/

theorem sdiff_injOn {δ : Finset (Sym2 (Site n))} :
    Set.InjOn (fun γ : Finset (Sym2 (Site n)) => γ \ δ)
      {γ | δ ⊆ γ} := by
  intro γ hγ γ' hγ' hEq
  have hEq' : γ \ δ = γ' \ δ := hEq
  have h1 : γ \ δ ∪ δ = γ := Finset.sdiff_union_of_subset hγ
  have h2 : γ' \ δ ∪ δ = γ' := Finset.sdiff_union_of_subset hγ'
  rw [← h1, ← h2, hEq']

set_option maxHeartbeats 1000000 in
-- The filters below are over `Finset (Sym2 (Site n))` with a classical decidability
-- instance, and the `Finset.sum_image` step unifies two sums over an image of that type;
-- elaboration exceeds the default budget on this box's instance stack.
/-- **PEIERLS' ENERGY ESTIMATE.** The Boltzmann weight of the configurations whose contour
contains a given realised contour `δ` is at most `exp (-4β |δ|)` times the partition
function.

Everything conditional has been discharged: no boundary condition, no positivity of `β`, no
hypothesis on `δ` beyond being realised — which `CircuitCut.exists_cut` supplies for the
bonds of a dual circuit. -/
theorem peierls_energy_bound (hn : 0 < n) (β : ℝ) {δ : Finset (Sym2 (Site n))}
    (hδ : δ ∈ realisedContours n) :
    ∑ γ ∈ (realisedContours n).filter (fun γ => δ ⊆ γ), Real.exp (-(4 * β) * (γ.card : ℝ)) ≤
      Real.exp (-(4 * β) * (δ.card : ℝ)) *
        ∑ γ ∈ realisedContours n, Real.exp (-(4 * β) * (γ.card : ℝ)) := by
  classical
  have hfac : ∀ γ ∈ (realisedContours n).filter (fun γ => δ ⊆ γ),
      Real.exp (-(4 * β) * (γ.card : ℝ)) =
        Real.exp (-(4 * β) * (δ.card : ℝ)) * Real.exp (-(4 * β) * ((γ \ δ).card : ℝ)) := by
    intro γ hγ
    have hsub : δ ⊆ γ := (Finset.mem_filter.mp hγ).2
    have hcardN : (γ \ δ).card = γ.card - δ.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
    have hcard : ((γ \ δ).card : ℝ) = (γ.card : ℝ) - (δ.card : ℝ) := by
      rw [hcardN, Nat.cast_sub (Finset.card_le_card hsub)]
    rw [← Real.exp_add, hcard]
    ring_nf
  rw [Finset.sum_congr rfl hfac, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
  have hinj : ∀ γ ∈ (realisedContours n).filter (fun γ => δ ⊆ γ),
      ∀ γ' ∈ (realisedContours n).filter (fun γ => δ ⊆ γ), γ \ δ = γ' \ δ → γ = γ' :=
    fun γ hγ γ' hγ' hEq =>
      sdiff_injOn (Finset.mem_filter.mp hγ).2 (Finset.mem_filter.mp hγ').2 hEq
  calc ∑ γ ∈ (realisedContours n).filter (fun γ => δ ⊆ γ),
          Real.exp (-(4 * β) * ((γ \ δ).card : ℝ))
      = ∑ γ' ∈ ((realisedContours n).filter (fun γ => δ ⊆ γ)).image (fun γ => γ \ δ),
          Real.exp (-(4 * β) * (γ'.card : ℝ)) :=
        (Finset.sum_image
          (f := fun x : Finset (Sym2 (Site n)) => Real.exp (-(4 * β) * (x.card : ℝ)))
          hinj).symm
    _ ≤ ∑ γ ∈ realisedContours n, Real.exp (-(4 * β) * (γ.card : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => Real.exp_nonneg _
        intro γ' hγ'
        obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hγ'
        exact realised_sdiff hn (Finset.mem_filter.mp hγ).1 hδ (Finset.mem_filter.mp hγ).2

/-! ## 4. The same bound on the Gibbs weights

Read through `IsingContourGibbs.peierls_weight`, so that the statement is about
`Real.exp (-β * isingH n σ)` — the weight the finite-volume Gibbs measure is built from —
rather than about the reindexed contour sum. -/

/-- **The energy estimate, as a statement about configurations.** -/
theorem gibbs_bound_of_subset (hn : 0 < n) (β : ℝ) {δ : Finset (Sym2 (Site n))}
    (hδ : δ ∈ realisedContours n) :
    ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => δ ⊆ contour σ),
        Real.exp (-β * isingH n σ) ≤
      Real.exp (-(4 * β) * (δ.card : ℝ)) * ∑ σ : Config n, Real.exp (-β * isingH n σ) := by
  classical
  have hw : ∀ σ : Config n, Real.exp (-β * isingH n σ) =
      Real.exp (-(4 * β) * ((contour σ).card : ℝ)) *
        Real.exp (-β * isingH n (fun _ => true)) :=
    fun σ => IsingContourGibbs.peierls_weight n β σ
  have hL : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => δ ⊆ contour σ),
      Real.exp (-β * isingH n σ) =
      (∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => δ ⊆ contour σ),
        Real.exp (-(4 * β) * ((contour σ).card : ℝ))) *
          Real.exp (-β * isingH n (fun _ => true)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => hw σ
  have hR : ∑ σ : Config n, Real.exp (-β * isingH n σ) =
      (∑ σ : Config n, Real.exp (-(4 * β) * ((contour σ).card : ℝ))) *
        Real.exp (-β * isingH n (fun _ => true)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun σ _ => hw σ
  rw [hL, hR, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
  have hleft : ∑ σ ∈ (Finset.univ : Finset (Config n)).filter (fun σ => δ ⊆ contour σ),
      Real.exp (-(4 * β) * ((contour σ).card : ℝ)) =
        2 • ∑ γ ∈ (realisedContours n).filter (fun γ => δ ⊆ γ),
          Real.exp (-(4 * β) * (γ.card : ℝ)) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact sum_over_contours hn (fun γ => if δ ⊆ γ then Real.exp (-(4 * β) * (γ.card : ℝ)) else 0)
  have hright : ∑ σ : Config n, Real.exp (-(4 * β) * ((contour σ).card : ℝ)) =
      2 • ∑ γ ∈ realisedContours n, Real.exp (-(4 * β) * (γ.card : ℝ)) :=
    sum_over_contours hn (fun γ => Real.exp (-(4 * β) * (γ.card : ℝ)))
  rw [hleft, hright, nsmul_eq_mul, nsmul_eq_mul]
  have hkey := peierls_energy_bound hn β hδ
  nlinarith [Real.exp_nonneg (-(4 * β) * (δ.card : ℝ))]

/-! ## 5. With a circuit in it

`CircuitCut.exists_cut` says a circuit's bonds are the contour of something, which is
exactly membership in `realisedContours`. So the estimate applies to them, and this is the
form Peierls' comparison consumes. -/

/-- **A circuit's bonds are a realised contour.** -/
theorem bonds_mem_realised {σ : Config n} (hσ : PlusBoundary σ) {H : SimpleGraph (Plaq n)}
    (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    bonds σ H ∈ realisedContours n := by
  obtain ⟨τ, hτ⟩ := CircuitCut.exists_cut hσ hle hcyc
  exact hτ ▸ Finset.mem_image_of_mem contour (Finset.mem_univ τ)

/-- **THE ENERGY SIDE, WITH A CIRCUIT.** The Boltzmann weight of the configurations whose
contour contains a given dual circuit's bonds is at most `exp (-4β L)` times the partition
function, where `L` is the circuit's length — `CircuitLength.card_bonds_eq_length` being
what turns `(bonds σ H).card` into that length.

Together with `RayWalk.exists_circuit_near_of_down` (a down site has such a circuit within
`L + 1` of it) and `PlaqLocal.card_closed_walks_ball_le` (how many there can be), this is
the third of the three inputs Peierls' comparison needs. **The comparison — the summation
over `L` — is not here.** -/
theorem gibbs_bound_of_circuit (hn : 0 < n) (β : ℝ) {σ : Config n} (hσ : PlusBoundary σ)
    {H : SimpleGraph (Plaq n)} (hle : H ≤ dualGraph σ) (hcyc : IsCycleGraph H) :
    ∑ σ' ∈ (Finset.univ : Finset (Config n)).filter (fun σ' => bonds σ H ⊆ contour σ'),
        Real.exp (-β * isingH n σ') ≤
      Real.exp (-(4 * β) * ((bonds σ H).card : ℝ)) *
        ∑ σ' : Config n, Real.exp (-β * isingH n σ') :=
  gibbs_bound_of_subset hn β (bonds_mem_realised hσ hle hcyc)

end ContourSubtract
