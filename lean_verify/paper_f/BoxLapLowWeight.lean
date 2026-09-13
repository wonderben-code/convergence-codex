import BoxLapGap

/-!
# Every low level of the box's spectrum, with the exact boundary where the argument stops

`BoxLapGap` computed the box's spectral gap and closed by predicting that the **third**-smallest
value is where the count becomes side-length-dependent, and that the comparison would be
`2·gapVal` against `term 2`. **The prediction was wrong in both halves, and the correction is this
file** (`ERRATUM 538`).

**It is wrong about uniformity.** `2·gapVal < term 2` holds at **every** side length, with no
exception, because `cos(2θ) = 2cos²θ − 1` turns the comparison into `c² < c` for `c = cos(π/n)`,
which is true for every `c` strictly between `0` and `1`. So the third-smallest value is `2·gapVal`
uniformly.

**And it is wrong about where the dependence starts.** It starts at the **fourth**, and the
boundary is exact and pretty: `r·gapVal < term 2` exactly when `r < 2(1 + cos(π/n))`. At `n = 3`
that reads `r < 3` — and **`r = 3` is an equality, not a near miss**: `3·gapVal = term 2` at side
length three, because `cos(π/3)` is exactly `½`.

## What is proved

**`r_gapVal_lt_term_two_iff`** — the boundary, as a biconditional: `r · gapVal m < term m 2` exactly
when `(r : ℝ) < 2 * (1 + cos(π/(m+1)))`. One application of `Real.cos_two_mul`.

**`two_gapVal_lt_term_two`** — hence the `r = 2` case holds at every side length `≥ 3`, which is the
half of the prediction that was uniform all along.

**`boxLapEig_eq_weight_iff`** — **THE CHARACTERISATION, FOR EVERY `r` BELOW THE BOUNDARY.** If
`r · gapVal < term 2`, a frequency vector's eigenvalue is `r · gapVal` exactly when **every
coordinate is `0` or `1` and exactly `r` of them are `1`.** The proof is shorter than `BoxLapGap`'s
special case: any coordinate at `2` or above already exceeds the target, so all coordinates are `0`
or `1`, and then the sum is the number of ones times `gapVal`.

**`finrank_weight_box`** — so **the eigenspace there has dimension `d.choose r`**, in every
dimension and at every side length below the boundary. `r = 0` is the ground state, `r = 1` is the
gap, and `r = 2` is the third level — the previous two files are the first two instances.

**`finrank_weight_boxSignless`** — and all of them transfer to `Q`, the box being two-colourable.

**`three_gapVal_eq_term_two`** — **AND THE BOUNDARY IS ATTAINED, NOT APPROACHED.** At side length
three, `3 · gapVal = term 2` exactly. So at `r = 3` and `n = 3` two genuinely different shapes —
three coordinates at frequency one, and one coordinate at frequency two — **share an eigenvalue**,
which is precisely the kind of coincidence that makes the general count hard.

## What is NOT here

* **THIS IS NOT THE FIRST COLLISION IN THE ESTATE, AND IT WOULD HAVE BEEN EASY TO SAY SO.**
  `BoxLapMultiplicity.sporadic_eq` exhibits `(0, 3)` and `(2, 2)` sharing an eigenvalue at side
  length **six**, in dimension **two**, and has since that file was written. This one is at side
  length **three** and needs dimension **three**; the two minimise different things and neither is
  "the smallest". Grepped before the claim was written (`ERRATUM 531`'s rule).
* **NO COUNT AT OR ABOVE THE BOUNDARY.** Everything here is strictly below `2(1 + cos(π/n))`, which
  is at most `4`, so **at most four levels are covered and the rest of the spectrum is untouched**
  (`ERRATUM 246`). The open `d ≥ 2` clause is about what happens above, and this file's contribution
  to it is a precise statement of where "above" begins.
* **NO CLAIM THAT THE COLLISION AT `n = 3` IS THE ONLY ONE AT ITS LEVEL**, or that the fibre there
  is exactly the two shapes named. The equality is proved; the fibre over it is not computed.
* **NOTHING OVER `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): a dimension `d`, a side length `m + 1`,
`1 ≤ m`, and the boundary condition `r · gapVal m < term m 2` — which is a hypothesis about numbers
and not about the box, and is exactly what `r_gapVal_lt_term_two_iff` makes checkable.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace BoxLapLowWeight

open Real Finset BoxGraph BoxLapSpectrum BoxLapExtremes BoxLapGap

/-! ## 1. The boundary -/

theorem cos_pi_div_lt_one {m : ℕ} (hm : 1 ≤ m) :
    Real.cos (((1 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1)) < 1 := by
  have h := gapVal_pos hm
  rw [gapVal] at h
  linarith

/-- **THE BOUNDARY, AS A BICONDITIONAL.** `cos(2θ) = 2cos²θ − 1` turns the comparison into a
quadratic. -/
theorem r_gapVal_lt_term_two_iff {m : ℕ} (hm : 2 ≤ m) (r : ℕ) :
    (r : ℝ) * gapVal m < 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1))
      ↔ (r : ℝ) < 2 * (1 + Real.cos (((1 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1))) := by
  have hm1 : 1 ≤ m := le_trans one_le_two hm
  set c := Real.cos (((1 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1)) with hc
  have hdouble : Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1)) = 2 * c ^ 2 - 1 := by
    rw [hc, ← Real.cos_two_mul]
    congr 1
    push_cast
    ring
  have hclt : c < 1 := by rw [hc]; exact cos_pi_div_lt_one hm1
  have hgap : gapVal m = 2 - 2 * c := by rw [gapVal, hc]
  rw [hdouble, hgap]
  constructor
  · intro h
    nlinarith [h, hclt]
  · intro h
    nlinarith [h, hclt]

/-- The `r = 2` case, at every side length: the half of `BoxLapGap`'s prediction that was right. -/
theorem two_gapVal_lt_term_two {m : ℕ} (hm : 2 ≤ m) :
    (2 : ℝ) * gapVal m < 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
  have h := (r_gapVal_lt_term_two_iff hm 2).mpr ?_
  · exact_mod_cast h
  · have hm1 : 1 ≤ m := le_trans one_le_two hm
    have hpos : 0 < Real.cos (((1 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
      have hlt : ((1 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1) < Real.pi / 2 := by
        have hmr : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
        push_cast
        nlinarith [Real.pi_pos]
      exact Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos, angle_nonneg m 1], hlt⟩
    push_cast
    linarith

/-- **AND THE BOUNDARY IS ATTAINED AT SIDE LENGTH THREE**, because `cos(π/3)` is exactly `½`. -/
theorem three_gapVal_eq_term_two :
    (3 : ℝ) * gapVal 2 = 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((2 : ℕ) + 1)) := by
  have h1 : ((1 : ℕ) : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1) = Real.pi / 3 := by push_cast; ring
  have h2 : ((2 : ℕ) : ℝ) * Real.pi / (((2 : ℕ) : ℝ) + 1) = 2 * (Real.pi / 3) := by
    push_cast; ring
  rw [gapVal, h1, h2, Real.cos_two_mul, Real.cos_pi_div_three]
  norm_num

/-! ## 2. Below the boundary, the fibre is a weight class -/

/-- **THE CHARACTERISATION.** Below the boundary a frequency vector hits `r · gapVal` exactly when
every coordinate is `0` or `1` and exactly `r` of them are `1`. -/
theorem boxLapEig_eq_weight_iff {d m r : ℕ} (hm : 1 ≤ m)
    (hr : (r : ℝ) * gapVal m < 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1)))
    {k : Fin d → ℕ} (hk : ∀ i, k i ≤ m) :
    boxLapEig d (m + 1) k = (r : ℝ) * gapVal m
      ↔ (∀ i, k i ≤ 1) ∧ (Finset.univ.filter (fun i => k i = 1)).card = r := by
  classical
  rw [boxLapEig_eq]
  constructor
  · intro h
    have hle : ∀ i, k i ≤ 1 := by
      intro i
      by_contra hno
      have h2 : 2 ≤ k i := by omega
      have hbig : 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1))
          ≤ 2 - 2 * Real.cos ((k i : ℝ) * Real.pi / ((m : ℝ) + 1)) := by
        rcases eq_or_lt_of_le h2 with he | hlt
        · rw [← he]
        · exact (term_strictMono hlt (hk i)).le
      have hterm : 2 - 2 * Real.cos ((k i : ℝ) * Real.pi / ((m : ℝ) + 1))
          ≤ ∑ l, (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1))) :=
        Finset.single_le_sum (fun l _ => term_nonneg m (k l)) (Finset.mem_univ i)
      linarith
    refine ⟨hle, ?_⟩
    -- the sum is (number of ones) · gapVal
    have hsum : ∑ l, (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1)))
        = ((Finset.univ.filter (fun i => k i = 1)).card : ℝ) * gapVal m := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => k i = 1)]
      have hone : ∑ l ∈ Finset.univ.filter (fun i => k i = 1),
          (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1)))
          = ((Finset.univ.filter (fun i => k i = 1)).card : ℝ) * gapVal m := by
        rw [Finset.sum_congr rfl fun l hl => by
          rw [(Finset.mem_filter.mp hl).2], Finset.sum_const, nsmul_eq_mul, gapVal]
      have hzero : ∑ l ∈ Finset.univ.filter (fun i => ¬ k i = 1),
          (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1))) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        have : k l = 0 := by
          have := (Finset.mem_filter.mp hl).2
          have := hle l
          omega
        rw [this]
        simp
      rw [hone, hzero, add_zero]
    rw [hsum] at h
    have hgp := gapVal_pos hm
    have : ((Finset.univ.filter (fun i => k i = 1)).card : ℝ) = (r : ℝ) :=
      mul_right_cancel₀ (ne_of_gt hgp) h
    exact_mod_cast this
  · rintro ⟨hle, hcard⟩
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => k i = 1)]
    have hone : ∑ l ∈ Finset.univ.filter (fun i => k i = 1),
        (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1)))
        = (r : ℝ) * gapVal m := by
      rw [Finset.sum_congr rfl fun l hl => by
        rw [(Finset.mem_filter.mp hl).2], Finset.sum_const, hcard, nsmul_eq_mul, gapVal]
    have hzero : ∑ l ∈ Finset.univ.filter (fun i => ¬ k i = 1),
        (2 - 2 * Real.cos ((k l : ℝ) * Real.pi / ((m : ℝ) + 1))) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have : k l = 0 := by
        have := (Finset.mem_filter.mp hl).2
        have := hle l
        omega
      rw [this]
      simp
    rw [hone, hzero, add_zero]

/-! ## 3. So the fibre is a binomial coefficient -/

/-- **THE COUNT.** Below the boundary the eigenspace at `r · gapVal` has dimension `d.choose r`. -/
theorem finrank_weight_box (d : ℕ) {m r : ℕ} (hm : 1 ≤ m)
    (hr : (r : ℝ) * gapVal m < 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1))) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' ((boxGraph d (m + 1)).lapMatrix ℝ)
          - ((r : ℝ) * gapVal m) • LinearMap.id)) = d.choose r := by
  classical
  rw [BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m ((r : ℝ) * gapVal m)]
  set e : Finset (Fin d) → Site d (m + 1) :=
    fun S j => if j ∈ S then ⟨1, by omega⟩ else ⟨0, by omega⟩ with he
  have hmem : ∀ k : Site d (m + 1),
      (boxLapEig d (m + 1) fun i => (k i : ℕ)) = (r : ℝ) * gapVal m
        ↔ ∃ S ∈ Finset.univ.powersetCard r, k = e S := by
    intro k
    rw [boxLapEig_eq_weight_iff hm hr (fun i => Nat.lt_succ_iff.mp (k i).isLt)]
    constructor
    · rintro ⟨hle, hcard⟩
      refine ⟨Finset.univ.filter (fun i => (k i : ℕ) = 1), ?_, ?_⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hcard⟩
      · funext j
        refine Fin.ext ?_
        by_cases hj : (k j : ℕ) = 1
        · have hmemj : j ∈ Finset.univ.filter (fun i => (k i : ℕ) = 1) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
          simp [he, hmemj, hj]
        · have hnotj : j ∉ Finset.univ.filter (fun i => (k i : ℕ) = 1) := by simp [hj]
          have hz : (k j : ℕ) = 0 := by have := hle j; omega
          simp [he, hnotj, hz]
    · rintro ⟨S, hS, rfl⟩
      rw [Finset.mem_powersetCard] at hS
      constructor
      · intro i
        rw [he]
        by_cases hi : i ∈ S <;> simp [hi]
      · have : Finset.univ.filter (fun i => ((e S i : Fin (m + 1)) : ℕ) = 1) = S := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, he]
          by_cases hi : i ∈ S <;> simp [hi]
        rw [this, hS.2]
  have hinj : Set.InjOn e
      ((Finset.univ.powersetCard r : Finset (Finset (Fin d))) : Set (Finset (Fin d))) := by
    intro A _ B _ hAB
    ext i
    have hi := congrFun hAB i
    simp only [he] at hi
    constructor
    · intro hA
      by_contra hB
      rw [if_pos hA, if_neg hB] at hi
      exact absurd (congrArg Fin.val hi) (by simp)
    · intro hB
      by_contra hA
      rw [if_neg hA, if_pos hB] at hi
      exact absurd (congrArg Fin.val hi) (by simp)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : Finset.univ.filter (fun k : Site d (m + 1) =>
      (boxLapEig d (m + 1) fun i => (k i : ℕ)) = (r : ℝ) * gapVal m)
      = (Finset.univ.powersetCard r).image e := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, hmem k]
    exact ⟨fun ⟨S, hS, hk⟩ => ⟨S, hS, hk.symm⟩, fun ⟨S, hS, hk⟩ => ⟨S, hS, hk.symm⟩⟩
  rw [hset, Finset.card_image_of_injOn hinj, Finset.card_powersetCard, Finset.card_univ,
    Fintype.card_fin]

/-- **AND ALL OF THEM TRANSFER TO `Q`.** -/
theorem finrank_weight_boxSignless (d : ℕ) {m r : ℕ} (hm : 1 ≤ m)
    (hr : (r : ℝ) * gapVal m < 2 - 2 * Real.cos (((2 : ℕ) : ℝ) * Real.pi / ((m : ℝ) + 1))) :
    Module.finrank ℝ (LinearMap.ker
        (Matrix.toLin' (LaplacianSignless.signlessLap (boxGraph d (m + 1)))
          - ((r : ℝ) * gapVal m) • LinearMap.id)) = d.choose r := by
  rw [SignlessConjugateMultiplicity.finrank_eigenspace_boxSignlessLap d m ((r : ℝ) * gapVal m),
    ← BoxLapMultiplicityExact.finrank_eigenspace_boxLap d m ((r : ℝ) * gapVal m)]
  exact finrank_weight_box d hm hr

end BoxLapLowWeight
