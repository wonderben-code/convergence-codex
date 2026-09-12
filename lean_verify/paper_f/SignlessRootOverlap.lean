import SignlessOverlapBound

/-!
# The second overlap, and the bound meets a computed spectrum at a second graph

`SignlessOverlapBound` corrected the previous unit's diagnosis — the refined bound's slack is
family **overlap**, not the root family — and paid the first of the two overlaps, a value that is
both a part value and a pole. It left the second open and named what paying it would need: *an
iff for when a part value satisfies the secular equation*. **That iff was proved four entries
earlier and the unit that asked for it did not know**:
`SecularPartValueAbove.part_value_secular_root_iff` says a part value is a secular root exactly
when the off-size terms sum to `k_{nⱼ} − 1`. What was actually missing is smaller — the
observation that such a value lies in **two** of the three families — and it is three lines.

**AND THE TWO GRAPHS SPLIT CLEANLY.** `K_{1,1,2,2}` has the first overlap and not the second;
`K_{1,3,3}` has the second and not the first — it has no doubling at all, which is why
`SignlessOverlapBound` could not touch it. With both paid, both graphs' sharpened bounds are
**exact**.

## What is proved

**`mem_inter_of_partRoot`** — **the second overlap in general**: if a part has at least two
vertices, no size is exactly half of it, and its part value satisfies the secular equation, then
that value lies in **both** the surviving part values and the roots. The middle hypothesis is what
puts the value in the roots finset at all — that finset is characterised with pole-disjointness
built in, which is `SecularRootsOffPoles`'s discarded conjunct (`ERRATUM 521`) doing useful work a
fourth time.

**`card_spectrum_add_one_le_refined_of_partRoot`** — so the bound drops by one, exactly as the
doubling overlap does: `#spec + 1 ≤ #bigSizes + #repSizes + s`.

**`exact_Part133`** — at `K_{1,3,3}` the sharpened bound is `3`, and
`SignlessPart133Complete.isEigenvalue_signless_part133` says the spectrum is `{1, 4, 9}`, so **the
bound is attained**. It is the **second** graph where a general upper bound in this chain meets an
independently computed spectrum, and the first where the two sides were computed twenty-four
entries apart by arguments with nothing in common — that spectrum came from a Hermitian fibre
count, and this bound from three families of candidates.

**`card_spectrum_add_two_le_refined`** — **and both at once drop it by two.** The obstacle a
first draft of this header named — *the two overlapping values must be shown distinct* — **is not
one**, and `claims_scan` flagging that paragraph as an undated estate-scope claim is what sent me
to check. Inclusion–exclusion counts `|P ∩ Q|` and `|(P ∪ Q) ∩ R|` in separate terms, so the two
are subtracted independently whether or not they are the same value; no distinctness hypothesis
appears, and none is needed. (They are distinct here anyway: the root hypothesis already says no
size is half of `nⱼ`, which is exactly what would make them coincide.)

**`P1123`, `double_P1123`, `rep_P1123`, `root_P1123`, `bound_P1123`** — **and a graph with both,
found by searching size multisets rather than by inspection.** `K_{1,1,2,3}`, on **seven**
vertices — smaller than four of the graphs already in this chain: `2 = 2 · 1` with `1` shared gives
the first overlap, and the part value `7 − 3 = 4` satisfies the secular equation (`1 + 1 − 2 − 1`)
giving the second. Its refined bound is `2 + 1 + 3 = 6` and the two overlaps take it to **`4`**.

## What is NOT here

* **A THIRD OVERLAP, POLE WITH ROOT, IS NEITHER RULED OUT NOR LOOKED FOR, as of 2026-09-12
  (entry 64).** The two paid here are part-value/pole and part-value/root; a pole that is also a
  root would be a third, and nothing in this file addresses it. Not attempted (`ERRATUM 246`).
* **THE EXACT COUNT AT `K_{1,1,2,3}` IS NOT PROVED, as of 2026-09-12 (entry 64).** The
  two-overlap bound gives `≤ 4` and `exists_spectrum_bracket` gives `≥ 3`. Closing it would mean
  exhibiting the two irrational roots `6 ± √17` — the cubic is `μ³ − 16μ² + 67μ − 76`, whose
  rational root is the part value `4` — which is the work `SignlessP1122Exact` did for its own
  graph and is not repeated here.
* **NO CLAIM THAT THE BOUND IS NOW TIGHT.** It is attained at the two graphs where the chain can
  compute the spectrum, and those are the only two. A third overlap — pole with root — is not
  ruled out and is not looked for.
* **THE HYPOTHESIS IS NOT DECIDABLE BY INSPECTION.** *Its part value satisfies the secular
  equation* is an equation over the reals; `part_value_secular_root_iff` turns it into arithmetic
  on the sizes, and `SecularPositivePart` and `SecularPartValueAbove` give sufficient conditions
  for it to **fail**, on both sides. Nothing here gives a sufficient condition for it to **hold**
  other than checking.
* **NO MULTIPLICITIES, NOTHING OVER `ℂ`, NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `∀ i, Nonempty (V i)`,
`2 ≤ Fintype.card ι`, a part of at least two vertices with no size exactly half of it, and that
part value satisfying the secular equation. **No mass, no propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessRootOverlap

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessSpectrumComplete SignlessOverlapBound SecularRootExact
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The second overlap -/

omit [DecidableEq ι] [∀ i, DecidableEq (V i)] in
/-- **A PART VALUE THAT IS ALSO A SECULAR ROOT LIES IN TWO FAMILIES.** -/
theorem mem_inter_of_partRoot {j : ι} (h2 : 2 ≤ Fintype.card (V j))
    (hnp : ∀ k : ι, 2 * Fintype.card (V k) ≠ Fintype.card (V j))
    (hroot : secularSum (V := V)
      ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) = -1)
    {R : Finset ℝ}
    (hR : ∀ μ : ℝ, μ ∈ R ↔ secularSum (V := V) μ = -1
      ∧ ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ ≠ 0) :
    ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) ∈ partValuesBig V ∩ R := by
  refine Finset.mem_inter.mpr ⟨Finset.mem_image_of_mem _ (mem_bigSizes (V := V) h2),
    (hR _).mpr ⟨hroot, fun k hk => ?_⟩⟩
  have : (Fintype.card (V j) : ℝ) = 2 * Fintype.card (V k) := by linarith
  exact hnp k (by exact_mod_cast this.symm)

/-! ## 2. So the bound drops by one, again -/

/-- **`#spec + 1 ≤ #bigSizes + #repSizes + s`** when a part value is a secular root. -/
theorem card_spectrum_add_one_le_refined_of_partRoot (hne : ∀ i, Nonempty (V i))
    (htwo : 2 ≤ Fintype.card ι) {j : ι} (h2 : 2 ≤ Fintype.card (V j))
    (hnp : ∀ k : ι, 2 * Fintype.card (V k) ≠ Fintype.card (V j))
    (hroot : secularSum (V := V)
      ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) = -1) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card + 1 ≤ (bigSizes V).card + (repSizes V).card
          + (Finset.univ.image (fun k : ι => Fintype.card (V k))).card := by
  classical
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  have hsub := subset_cover (V := V) hne htwo hS hR
  have hcard := Finset.card_le_card hsub
  have hP : (partValuesBig V).card ≤ (bigSizes V).card := Finset.card_image_le
  have hQ : (polesRep V).card ≤ (repSizes V).card := Finset.card_image_le
  have hUR := Finset.card_union_add_card_inter (partValuesBig V ∪ polesRep V) R
  have hPQ : (partValuesBig V ∪ polesRep V).card
      ≤ (partValuesBig V).card + (polesRep V).card := Finset.card_union_le _ _
  have hmem := mem_inter_of_partRoot (V := V) h2 hnp hroot hR
  have hpos : 0 < ((partValuesBig V ∪ polesRep V) ∩ R).card := by
    refine Finset.card_pos.mpr ⟨_, Finset.mem_inter.mpr ⟨?_, (Finset.mem_inter.mp hmem).2⟩⟩
    exact Finset.mem_union_left _ (Finset.mem_inter.mp hmem).1
  omega

/-! ## 3. And it is attained at `K_{1,3,3}` -/

/-- **AT `K_{1,3,3}` THE SHARPENED BOUND IS `3`, WHICH IS THE EXACT COUNT.** -/
theorem exact_Part133 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen SecularRootAtPartValue.Part133 μ)
      ∧ S.card ≤ 3 ∧ 3 ≤ S.card := by
  classical
  obtain ⟨S, hS, hcard⟩ := card_spectrum_add_one_le_refined_of_partRoot
    (V := SecularRootAtPartValue.Part133) (fun _ => ⟨0⟩) (by decide) (j := 1) (by decide)
    (fun k => SecularRootAtPartValue.half_part133 k)
    (by rw [SecularRootAtPartValue.part_value_four]
        exact SecularRootAtPartValue.secularSum_part133_four)
  rw [show (bigSizes SecularRootAtPartValue.Part133).card = 1 from by decide,
    show (repSizes SecularRootAtPartValue.Part133).card = 1 from by decide,
    show (Finset.univ.image (fun k : Fin 3 =>
      Fintype.card (SecularRootAtPartValue.Part133 k))).card = 2 from by decide] at hcard
  refine ⟨S, hS, by omega, ?_⟩
  have hT : S = ({1, 4, 9} : Finset ℝ) := by
    refine Finset.ext fun μ => ?_
    rw [hS μ]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact SignlessPart133Complete.isEigenvalue_signless_part133 μ
  rw [hT]
  norm_num

/-! ## 4. Both overlaps at once -/

/-- **BOTH OVERLAPS DROP THE BOUND BY TWO**, and no distinctness hypothesis is needed: the two
intersections enter inclusion–exclusion in separate terms. -/
theorem card_spectrum_add_two_le_refined (hne : ∀ i, Nonempty (V i))
    (htwo : 2 ≤ Fintype.card ι) {i k : ι}
    (hdouble : Fintype.card (V k) = 2 * Fintype.card (V i))
    (hrep : Fintype.card (V i) ∈ repSizes V)
    {j : ι} (h2 : 2 ≤ Fintype.card (V j))
    (hnp : ∀ m : ι, 2 * Fintype.card (V m) ≠ Fintype.card (V j))
    (hroot : secularSum (V := V)
      ((Fintype.card (Σ i, V i) : ℝ) - Fintype.card (V j)) = -1) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card + 2 ≤ (bigSizes V).card + (repSizes V).card
          + (Finset.univ.image (fun m : ι => Fintype.card (V m))).card := by
  classical
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  have hsub := subset_cover (V := V) hne htwo hS hR
  have hcard := Finset.card_le_card hsub
  have hP : (partValuesBig V).card ≤ (bigSizes V).card := Finset.card_image_le
  have hQ : (polesRep V).card ≤ (repSizes V).card := Finset.card_image_le
  have hU1 := Finset.card_union_add_card_inter (partValuesBig V ∪ polesRep V) R
  have hU2 := Finset.card_union_add_card_inter (partValuesBig V) (polesRep V)
  have hpos1 : 0 < (partValuesBig V ∩ polesRep V).card :=
    Finset.card_pos.mpr ⟨_, mem_inter_of_double (V := V) hne hdouble hrep⟩
  have hmem := mem_inter_of_partRoot (V := V) h2 hnp hroot hR
  have hpos2 : 0 < ((partValuesBig V ∪ polesRep V) ∩ R).card :=
    Finset.card_pos.mpr ⟨_, Finset.mem_inter.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_inter.mp hmem).1, (Finset.mem_inter.mp hmem).2⟩⟩
  omega

/-! ## 5. And a graph with both, on seven vertices -/

/-- `K_{1,1,2,3}`: `2 = 2 · 1` with `1` shared, and the part value `4` is a secular root. -/
abbrev P1123 : Fin 4 → Type := fun i => Fin (max 1 i.1)

theorem nonempty_P1123 (i : Fin 4) : Nonempty (P1123 i) := ⟨⟨0, by omega⟩⟩

theorem card_P1123 (i : Fin 4) : Fintype.card (P1123 i) = max 1 i.1 := by simp [P1123]

theorem total_P1123 : Fintype.card (Σ i, P1123 i) = 7 := by decide

theorem sizes_P1123 :
    (Finset.univ.image (fun i : Fin 4 => Fintype.card (P1123 i))).card = 3 := by decide

theorem double_P1123 : Fintype.card (P1123 2) = 2 * Fintype.card (P1123 0) := by decide

theorem rep_P1123 : Fintype.card (P1123 0) ∈ repSizes P1123 := by decide

theorem root_P1123 :
    secularSum (V := P1123)
      ((Fintype.card (Σ i, P1123 i) : ℝ) - Fintype.card (P1123 3)) = -1 := by
  simp only [secularSum, total_P1123, card_P1123, Fin.sum_univ_four]
  norm_num

/-- **BOTH OVERLAPS TAKE `K_{1,1,2,3}`'s BOUND FROM `6` TO `4`.** -/
theorem bound_P1123 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1123 μ) ∧ S.card ≤ 4 := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_add_two_le_refined (V := P1123) nonempty_P1123
    (by decide) (i := 0) (k := 2) double_P1123 rep_P1123 (j := 3) (by decide)
    (by decide) root_P1123
  refine ⟨S, hS, ?_⟩
  rw [show (bigSizes P1123).card = 2 from by decide,
    show (repSizes P1123).card = 1 from by decide, sizes_P1123] at hcard
  omega

end SignlessRootOverlap
