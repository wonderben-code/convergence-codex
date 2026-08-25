/-
  IsingWalkChainEnergy.lean — the box's walk model, evaluated: its region energy really is a field
  at one end and a bond on each step, and nothing else.

  WHY. `IsingChainClosedForm` rewrote the chain's energy as a sum so that the two sides could be
  compared. This file computes the other side. `IsingRegionSplit.eL` — the energy of the box's
  comparison model restricted to the walk's sites — is a sum over **every** index of the box: one
  term per ordered pair of sites and one per site, some `n⁴` of them. The claim is that all but
  `m + 1` vanish, and that what survives is exactly a field at `γ m` and a bond on each of the
  walk's `m` steps.

  **THE THREE VANISHINGS ARE THREE DIFFERENT ARGUMENTS AND ONLY ONE IS BOOKKEEPING.** A pair that is
  not one of the walk's bonds dies because `pathCoup` gives it coupling `0`. A site off the walk
  dies because `keep` switches off every term not lying inside the region. **A site on the walk
  other than `γ m` dies for a third reason entirely** — it carries no field, and that is
  `exists_boundary_walk`'s fifth clause, the one asserting the walk touches the boundary only at its
  end. Without that clause the interior of the walk could sit on the boundary and the energy would
  have extra field terms; the fifth clause is what makes "a field at one end" true rather than
  merely plausible.

  **AND THE BONDS ARE COUNTED ONCE, NOT TWICE**, which is a real hazard here: the box has one term
  per **ordered** pair, so an unordered bond appears twice in the index type. `walkBonds` contains
  only `(γ j, γ (j+1))`, never its reverse, and `reverse_not_mem` **proves** the reverse absent
  rather than assuming it — it would force `k = j + 1` and `k + 1 = j` at once.

  WHAT REMAINS. This is one side of the comparison and `IsingChainClosedForm.chainE_field` is the
  other. Putting them together — carrying a configuration of the walk's sites across
  `IsingChainIndex.chainWalk` and matching the two sums term by term — is the next step, is **not
  attempted here**, and its cost is not claimed (`ERRATUM 246`). **No wall moves and nothing here is
  a bound on anything**; this is an identity between two expressions for one finite sum.

  Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/
import IsingBoxRegion
import IsingChainClosedForm

namespace IsingWalkChainEnergy

open Finset Real
open IsingFiniteVolume IsingBoundaryField IsingBoxInteraction IsingPathComparison IsingBoxRegion

variable {n : ℕ}

/-- The index predicate `IsingBoxRegion` uses: the term lies wholly on the walk. -/
abbrev Pin (γ : ℕ → Site n) (m : ℕ) : BoxIdx n → Prop :=
  fun i => ∀ v ∈ boxSet n i, v ∈ walkSites γ m

/-! ## 1. The field terms: one survives, and the fifth clause is why -/

theorem field_half (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
    (hbnd : isBoundary (γ m) = true) (hoff : ∀ i, i < m → isBoundary (γ i) = false)
    (σ : Site n → Bool) :
    ∑ p : Site n, IsingRegionSplit.keep (Pin γ m) (pathCoup n β h (walkBonds γ m)) (Sum.inr p)
        * ∏ v ∈ boxSet n (Sum.inr p), IsingTransfer2D.spin (σ v)
      = β * h * IsingTransfer2D.spin (σ (γ m)) := by
  rw [Finset.sum_eq_single (γ m)]
  · have hmem : Pin γ m (Sum.inr (γ m)) := by
      intro v hv
      rw [Finset.mem_singleton.mp hv]
      exact mem_walkSites γ m m le_rfl
    rw [IsingRegionSplit.keep, if_pos hmem, pathCoup, if_pos hbnd, boxSet, Finset.prod_singleton]
  · intro p _ hp
    by_cases hin : Pin γ m (Sum.inr p)
    · have hpw : p ∈ walkSites γ m := hin p (Finset.mem_singleton_self p)
      obtain ⟨i, hi⟩ := IsingWalkOrder.exists_index γ m hpw
      have hib : i.val < m := by
        rcases Nat.lt_or_ge i.val m with hlt | hge
        · exact hlt
        · have hval : i.val = m := by have := i.isLt; omega
          exact absurd (by rw [← hi, hval] : p = γ m) hp
      rw [IsingRegionSplit.keep, if_pos hin, pathCoup, if_neg, zero_mul]
      rw [← hi]
      simp [hoff i.val hib]
    · rw [IsingRegionSplit.keep, if_neg hin, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## 2. The bond terms: the walk's `m` bonds survive, each counted once -/

/-- **THE WALK'S BONDS ARE `m` DISTINCT PAIRS.** Injectivity of the walk, read on bonds rather than
sites, and the reason `Finset.sum_image` applies below without over- or under-counting. -/
theorem walkBonds_inj (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) :
    ∀ x ∈ Finset.range m, ∀ y ∈ Finset.range m, (γ x, γ (x + 1)) = (γ y, γ (y + 1)) → x = y := by
  intro i hi j hj hij
  exact hinj i (by have := Finset.mem_range.mp hi; omega)
    j (by have := Finset.mem_range.mp hj; omega) (congrArg Prod.fst hij)

/-- **THE REVERSE OF A WALK BOND IS NOT A WALK BOND.** The box has one term per **ordered** pair, so
an unordered bond has two indices and could be counted twice; `walkBonds` holds only one of each
pair. The header asserted this and the review found nothing proving it, so it is proved here rather
than the sentence weakened: the reverse being present would force `k = j + 1` and `k + 1 = j` at
once. Nothing below depends on it — `Finset.sum_image` counts the image faithfully whatever it
contains — which is exactly why the claim needed its own proof instead of being read off a step
that never made it. -/
theorem reverse_not_mem (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) (j : ℕ) (hj : j < m) :
    (γ (j + 1), γ j) ∉ walkBonds γ m := by
  rw [walkBonds]
  intro hmem
  obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp hmem
  have hkm := Finset.mem_range.mp hk
  have e1 : k = j + 1 := hinj k (by omega) (j + 1) (by omega) (congrArg Prod.fst hkeq)
  have e2 : k + 1 = j := hinj (k + 1) (by omega) j (by omega) (congrArg Prod.snd hkeq)
  omega

theorem sum_walkBonds (γ : ℕ → Site n) (m : ℕ)
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) (F : Site n × Site n → ℝ) :
    ∑ pq ∈ walkBonds γ m, F pq = ∑ j ∈ Finset.range m, F (γ j, γ (j + 1)) := by
  rw [walkBonds, Finset.sum_image (walkBonds_inj γ m hinj)]

theorem bond_half (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
    (hadj : ∀ k, k < m → adj (γ k) (γ (k + 1)))
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j) (σ : Site n → Bool) :
    ∑ pq : Site n × Site n,
        IsingRegionSplit.keep (Pin γ m) (pathCoup n β h (walkBonds γ m)) (Sum.inl pq)
          * ∏ v ∈ boxSet n (Sum.inl pq), IsingTransfer2D.spin (σ v)
      = β * ∑ j ∈ Finset.range m,
          IsingTransfer2D.spin (σ (γ j)) * IsingTransfer2D.spin (σ (γ (j + 1))) := by
  have hvanish : ∀ pq ∈ (Finset.univ : Finset (Site n × Site n)), pq ∉ walkBonds γ m →
      IsingRegionSplit.keep (Pin γ m) (pathCoup n β h (walkBonds γ m)) (Sum.inl pq)
        * ∏ v ∈ boxSet n (Sum.inl pq), IsingTransfer2D.spin (σ v) = 0 := by
    rintro ⟨p, q⟩ _ hpq
    rw [IsingRegionSplit.keep]
    by_cases hin : Pin γ m (Sum.inl (p, q))
    · rw [if_pos hin, pathCoup, if_neg (fun hc => hpq hc.1), zero_mul]
    · rw [if_neg hin, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ (walkBonds γ m)) hvanish,
      sum_walkBonds γ m hinj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm := Finset.mem_range.mp hj
  have hmem : Pin γ m (Sum.inl (γ j, γ (j + 1))) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv'
    · exact mem_walkSites γ m j (by omega)
    · rw [Finset.mem_singleton.mp hv']
      exact mem_walkSites γ m (j + 1) (by omega)
  rw [IsingRegionSplit.keep, if_pos hmem, pathCoup_walk_eq β h γ m hadj j hjm,
      prod_boxSet_inl _ _ (hadj j hjm)]

/-! ## 3. The two halves together -/

/-- **THE BOX'S WALK MODEL, EVALUATED.** Of the box's `n⁴`-odd interaction terms, `m + 1` survive:
one field at the walk's far end and one bond on each step. Both sides are finite sums in the box;
**nothing is estimated and no wall moves.** -/
theorem eL_walk (β h : ℝ) (γ : ℕ → Site n) (m : ℕ)
    (hadj : ∀ k, k < m → adj (γ k) (γ (k + 1)))
    (hinj : ∀ i ≤ m, ∀ j ≤ m, γ i = γ j → i = j)
    (hbnd : isBoundary (γ m) = true) (hoff : ∀ i, i < m → isBoundary (γ i) = false)
    (a : {v // v ∈ walkSites γ m} → Bool) :
    IsingRegionSplit.eL (boxSet n) (pathCoup n β h (walkBonds γ m)) (Pin γ m) a
      = β * h * IsingTransfer2D.spin (IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ m))
        + β * ∑ j ∈ Finset.range m,
            IsingTransfer2D.spin (IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ j))
              * IsingTransfer2D.spin
                  (IsingRegionSplit.glue (Sum.elim a (fun _ => true)) (γ (j + 1))) := by
  rw [IsingRegionSplit.eL, Fintype.sum_sum_type, bond_half β h γ m hadj hinj,
      field_half β h γ m hbnd hoff]
  ring

end IsingWalkChainEnergy
