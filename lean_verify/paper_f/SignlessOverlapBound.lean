import SignlessSpectrumComplete

/-!
# The refined bound's slack is family overlap, and one of the two overlaps is now paid

`SignlessSpectrumComplete` bounded the spectrum by `#bigSizes + #repSizes + s` and said, in four
places, that the gap to the true count *is the root family, counted at its maximum*. **That is
false at both graphs it quoted** (`ERRATUM 526`, and the four copies are annotated in place). The
bound adds the sizes of three families and the spectrum is their **union**, so the gap is exactly
the **overlap** — and at both graphs the root family is at its maximum and contributes nothing to
the gap.

**WHERE THE OVERLAPS ARE.** At `K_{1,1,2,2}` (`N = 6`) the surviving part values are `{4}`, the
surviving poles `{2, 4}` and the roots `{6 ± 2√2}`: **`4` is a part value and a pole**. At
`K_{1,3,3}` (`N = 7`) they are `{4}`, `{1}` and — the secular equation being `μ² − 13μ + 36 = 0` —
`{9, 4}`: **`4` is a part value and a root**. Two different overlaps, and the chain already had a
theorem about the first and an example of the second.

## What is proved

**`partValuesBig`, `polesRep`, `subset_cover`** — the two surviving families as `Finset ℝ`s and
the containment `spectrum ⊆ partValuesBig ∪ polesRep ∪ roots`, extracted from the previous unit's
proof so that a bound can be taken twice without re-deriving it.

**`mem_inter_of_double`** — **the first overlap, in general**: if one size is twice another and
the smaller size is shared by two parts, then `N − 2nᵢ` is in **both** surviving families. The
second hypothesis is what the previous unit's `repSizes` filter needs and `SignlessDoublingFails`
did not have to care about, because it worked with the unfiltered families.

**`card_spectrum_add_one_le_refined_of_double`** — **so the bound drops by one**:
`#spec + 1 ≤ #bigSizes + #repSizes + s`. Stated with `+ 1` on the left because the right-hand side
is a natural number and subtraction there is a trap.

**`exact_P1122`** — and at `K_{1,1,2,2}` the sharpened bound is `4`, which
`SignlessP1122Exact.card_spectrum_P1122_eq_four` says is the **exact count**. The bound is
therefore attained, and this is the first graph in the chain where a general upper bound meets an
independently computed spectrum.

## What is NOT here

* **THE SECOND OVERLAP IS NOT PAID.** A part value that is also a **secular root** is the gap at
  `K_{1,3,3}`, and it is real — `SecularRootAtPartValue.part_value_eq_secular_root` exhibits it.
  Paying it needs the roots finset to be intersected with the part values, which needs a criterion
  for when a part value satisfies the secular equation; `SecularPositivePart` and
  `SecularPartValueAbove` give **sufficient conditions for it to fail**, in both directions, and
  neither is an iff. Not attempted (`ERRATUM 246`).
* **NO CLAIM THAT THE SHARPENED BOUND IS TIGHT IN GENERAL.** It is attained at one graph. At
  `K_{1,3,3}` it does not apply at all — that graph has no doubling — and the bound there is still
  `4` against a count of `3`.
* **NOTHING NEW ABOUT ROOTS, MULTIPLICITIES OR `ℂ`. NO WALL MOVES AND NO PUBLISHED TAG MOVES.**

**THE HYPOTHESES, READ FROM `#check`** (`ERRATUM 455`): `∀ i, Nonempty (V i)`, `2 ≤ Fintype.card ι`
and, for the sharpened bound, one size twice another with the smaller shared. **No mass, no
propagator, no metric.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry in this file, 0 new axioms.

-/

namespace SignlessOverlapBound

open Matrix Finset SimpleGraph LaplacianSignless SignlessSpectrumTrichotomy
open SignlessSpectrumComplete SignlessDoublingFails SecularRootExact
open UnbalancedMultipartite UnbalancedMultipartiteSecular
open UnbalancedMultipartiteSecularEquation

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, Fintype (V i)]
  [∀ i, DecidableEq (V i)]

/-! ## 1. The two surviving families, and the containment -/

/-- The part values that survive `isEigen_iff`'s first clause. -/
noncomputable def partValuesBig (V : ι → Type*) [Fintype ι] [∀ i, Fintype (V i)] : Finset ℝ :=
  (bigSizes V).image (fun n : ℕ => (Fintype.card (Σ i, V i) : ℝ) - n)

/-- The poles that survive `isEigen_iff`'s second clause. -/
noncomputable def polesRep (V : ι → Type*) [Fintype ι] [DecidableEq ι] [∀ i, Fintype (V i)] :
    Finset ℝ :=
  (repSizes V).image (fun n : ℕ => (Fintype.card (Σ i, V i) : ℝ) - 2 * n)

theorem subset_cover (hne : ∀ i, Nonempty (V i)) (htwo : 2 ≤ Fintype.card ι)
    {S : Finset ℝ} (hS : ∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ) {R : Finset ℝ}
    (hR : ∀ μ : ℝ, μ ∈ R ↔ secularSum (V := V) μ = -1
      ∧ ∀ k : ι, (Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V k) - μ ≠ 0) :
    S ⊆ partValuesBig V ∪ polesRep V ∪ R := by
  intro μ hμ
  rcases (isEigen_iff (V := V) hne htwo μ).mp ((hS μ).mp hμ) with
    ⟨j, rfl, h2⟩ | ⟨i, rfl, h2⟩ | ⟨hval, hpole, hs⟩
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (mem_bigSizes (V := V) h2)))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image_of_mem _ (mem_repSizes (V := V) h2)))
  · exact Finset.mem_union_right _ ((hR _).mpr ⟨hs, fun k => sub_ne_zero_of_ne
      (Ne.symm (hpole k))⟩)

/-! ## 2. The first overlap -/

omit [∀ i, DecidableEq (V i)] in
/-- **A SIZE THAT DOUBLES A SHARED SIZE PUTS ONE VALUE IN BOTH FAMILIES.** -/
theorem mem_inter_of_double (hne : ∀ i, Nonempty (V i)) {i k : ι}
    (hdouble : Fintype.card (V k) = 2 * Fintype.card (V i))
    (hrep : Fintype.card (V i) ∈ repSizes V) :
    ((Fintype.card (Σ i, V i) : ℝ) - 2 * Fintype.card (V i))
      ∈ partValuesBig V ∩ polesRep V := by
  refine Finset.mem_inter.mpr ⟨?_, Finset.mem_image_of_mem _ hrep⟩
  have hbig : Fintype.card (V k) ∈ bigSizes V := by
    refine mem_bigSizes (V := V) ?_
    have := Fintype.card_pos_iff.mpr (hne i)
    omega
  have hval := Finset.mem_image_of_mem
    (fun n : ℕ => (Fintype.card (Σ i, V i) : ℝ) - n) hbig
  have hcast : ((Fintype.card (V k) : ℕ) : ℝ) = 2 * (Fintype.card (V i) : ℝ) := by
    rw [hdouble]; push_cast; ring
  rw [partValuesBig]
  simpa [hcast] using hval

/-! ## 3. So the bound drops by one -/

/-- **`#spec + 1 ≤ #bigSizes + #repSizes + s`** when one size doubles a shared size. -/
theorem card_spectrum_add_one_le_refined_of_double (hne : ∀ i, Nonempty (V i))
    (htwo : 2 ≤ Fintype.card ι) {i k : ι}
    (hdouble : Fintype.card (V k) = 2 * Fintype.card (V i))
    (hrep : Fintype.card (V i) ∈ repSizes V) :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen V μ)
      ∧ S.card + 1 ≤ (bigSizes V).card + (repSizes V).card
          + (Finset.univ.image (fun j : ι => Fintype.card (V j))).card := by
  classical
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨S, hS, -, -⟩ := exists_spectrum_bracket (V := V) hne hι
  obtain ⟨R, hRcard, hR⟩ := exists_roots_finset_exact (V := V) hne hι
  refine ⟨S, hS, ?_⟩
  have hsub := subset_cover (V := V) hne htwo hS hR
  have hcard := Finset.card_le_card hsub
  have hP : (partValuesBig V).card ≤ (bigSizes V).card := Finset.card_image_le
  have hQ : (polesRep V).card ≤ (repSizes V).card := Finset.card_image_le
  have hUR : (partValuesBig V ∪ polesRep V ∪ R).card
      ≤ (partValuesBig V ∪ polesRep V).card + R.card := Finset.card_union_le _ _
  have hPQ := Finset.card_union_add_card_inter (partValuesBig V) (polesRep V)
  have hpos : 0 < (partValuesBig V ∩ polesRep V).card :=
    Finset.card_pos.mpr ⟨_, mem_inter_of_double (V := V) hne hdouble hrep⟩
  omega

/-! ## 4. And it is attained -/

/-- **AT `K_{1,1,2,2}` THE SHARPENED BOUND IS `4`, WHICH IS THE EXACT COUNT.** -/
theorem exact_P1122 :
    ∃ S : Finset ℝ, (∀ μ : ℝ, μ ∈ S ↔ IsEigen P1122 μ) ∧ S.card ≤ 4 ∧ 4 ≤ S.card := by
  obtain ⟨S, hS, hcard⟩ := card_spectrum_add_one_le_refined_of_double (V := P1122)
    (fun _ => ⟨0⟩) (by decide) (i := 0) (k := 2) (by decide) (by decide)
  obtain ⟨T, hT, hT4⟩ := SignlessP1122Exact.card_spectrum_P1122_eq_four
  have hST : S = T := Finset.ext fun μ => by rw [hS μ, hT μ]
  rw [show (bigSizes P1122).card = 1 from by decide,
    show (repSizes P1122).card = 2 from by decide, sizes_P1122] at hcard
  exact ⟨S, hS, by omega, by rw [hST, hT4]⟩

end SignlessOverlapBound
