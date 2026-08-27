import HalfBlockStructure

/-!
# The number of blocks, as a number — and strictness as its maximality

`CrossBlockStructure` proved the coupling's kernel is combinatorial: on a block cut the form
vanishes exactly when every block sum vanishes, one linear condition per block, and it recorded the
reading — *"the degeneracy of the coupling is therefore the number of blocks"* — with the sentence
**"That is the shape `StrictBiconditional`'s machinery consumes, and it is not followed up here."**

`HalfBlockStructure` followed it up qualitatively: the two halves of `ReflectedFormCongr` §7 differ
because one cut is a perfect matching and the other is a single block of size two. **This makes the
count a number.**

## The number

**`CrossPosSemidef.cls_card_pos` is used rather than re-proved.** This file first contained a
`one_le_card_cls` saying no class is empty; `ERRATUM 176`'s **statement-level** grep — the one that
compares shapes rather than names — found the estate already had it, under a name no name-grep
would have matched. Deleted and cited.

`form_eq_sum_cls_sq` weights the site `k` by `|cls k|⁻¹`, so a class of size `c` is counted `c`
times at weight `1/c` — once. **`blockCount` is that sum**, and it is the number of blocks without
a quotient type anywhere in it.

> **`blockCount_eq_card_blockClasses`** — `blockCount` **is** the number of blocks. §5 proves the
> name rather than leaving it to a docstring.
>
> **`blockCount_le_card`** — `blockCount ≤ |H|`, always.
>
> **`strict_iff_blockCount_eq`** — on a block cut, **the reflected form is strict exactly when
> `blockCount = |H|`.**

Equality forces both things at once, which is why the criterion is one equation rather than two:
every class must be a singleton (or the weights drop below one) **and** every site of `H` must lie
in a block at all (or the sum has fewer terms than `H` has elements). Those are precisely the two
clauses of `strict_iff_cut_perfect`.

## The two halves, computed

`blockCount_rotHalf` says the contiguous half scores exactly its own size;
`blockCount_torusHalf_ne` says the antipodal half does not. **So the invariant separates them**,
and `ReflectedFormCongr` §7's finding — same graph, same reflection, two halves, two answers — is
the count reaching `|H|` against the count falling short.

## What this is NOT

**It is not the dimension statement.** *"The degeneracy of the coupling is the number of blocks"*
in the sense of `Module.finrank` — the kernel of the coupling form on families supported in `H` has
dimension `|H| − blockCount` — **is not proved here**. That needs rank-nullity against the map
sending a family to its tuple of block sums, and this file does not build it. What is proved is the
*criterion*: strictness is the count reaching its maximum. **Recorded as not done rather than as
hard**, per `ERRATUM 194`.

**⚠ ANSWERED 2026-08-27, sentence kept as written (`ERRATUM 94`, found by `ERRATUM 309`).**
`BlockDimension` builds exactly that map (`blockSums`), proves it surjective, and
`finrank_couplingKer_add_blockCount` is the dimension together with the identification of that
kernel with the coupling's (`mem_ker_blockSums_iff`) — its docstring calls itself *"the statement
the phrase asked for, in one place"*. *"Not proved here"* stays true of this file; what was missing
was the **forward pointer**, and a reader following this paragraph spent the search. **This one is
outside `fences_scan.py`'s reach and is named in that file as a known miss**: `BlockDimension`
answers positionally, quoting no word of this sentence, so no matcher keyed on quotation can see
it.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockCount

open SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure
open CrossPosSemidef

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The count -/

/-- **THE NUMBER OF BLOCKS OF THE CUT.** Each site of a class of size `c` contributes `1/c`, so
each class contributes exactly `1`. Sites of `H` joined to no mirror at all are not in `blk` and
contribute nothing — which is the right convention, since they are invisible to the coupling. -/
noncomputable def blockCount (G : SimpleGraph V) [DecidableRel G.Adj] (θ : V ≃ V) (H : Finset V) :
    ℝ :=
  ∑ k ∈ blk (crossMatrix G θ H) H, ((cls (crossMatrix G θ H) H k).card : ℝ)⁻¹

omit [Fintype V] in
/-- **THE COUNT NEVER EXCEEDS THE SIZE OF THE HALF.** Each term is at most `1` because no class is
empty, and there are at most `|H|` terms because `blk ⊆ H`. -/
theorem blockCount_le_card : blockCount G θ H ≤ (H.card : ℝ) := by
  classical
  have hterm : ∀ k ∈ blk (crossMatrix G θ H) H,
      ((cls (crossMatrix G θ H) H k).card : ℝ)⁻¹ ≤ 1 := by
    intro k hk
    have h1 : (1 : ℝ) ≤ ((cls (crossMatrix G θ H) H k).card : ℝ) := by
      exact_mod_cast cls_card_pos hk
    simpa using inv_le_one_of_one_le₀ h1
  calc blockCount G θ H ≤ ∑ _k ∈ blk (crossMatrix G θ H) H, (1 : ℝ) :=
        Finset.sum_le_sum hterm
    _ = ((blk (crossMatrix G θ H) H).card : ℝ) := by simp
    _ ≤ (H.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

/-! ## 2. Maximality is exactly the perfect cut -/

omit [Fintype V] in
/-- **THE COUNT REACHES `|H|` EXACTLY WHEN EVERY CLASS IS A SINGLETON AND EVERY SITE IS IN A
BLOCK.** One equation, two clauses — the terms can only sum to `|H|` if none of them is below `1`
and none of them is missing. -/
theorem blockCount_eq_card_iff :
    blockCount G θ H = (H.card : ℝ)
      ↔ (blk (crossMatrix G θ H) H = H ∧
          ∀ k ∈ blk (crossMatrix G θ H) H, (cls (crossMatrix G θ H) H k).card = 1) := by
  classical
  set B := blk (crossMatrix G θ H) H with hB
  have hsub : B ⊆ H := Finset.filter_subset _ _
  constructor
  · intro heq
    have hterm : ∀ k ∈ B, ((cls (crossMatrix G θ H) H k).card : ℝ)⁻¹ ≤ 1 := by
      intro k hk
      have h1 : (1 : ℝ) ≤ ((cls (crossMatrix G θ H) H k).card : ℝ) := by
        exact_mod_cast cls_card_pos hk
      simpa using inv_le_one_of_one_le₀ h1
    have hle : blockCount G θ H ≤ (B.card : ℝ) := by
      calc blockCount G θ H ≤ ∑ _k ∈ B, (1 : ℝ) := Finset.sum_le_sum hterm
        _ = (B.card : ℝ) := by simp
    have hcard : B.card = H.card := by
      have hR : (H.card : ℝ) ≤ (B.card : ℝ) := heq ▸ hle
      have hN : H.card ≤ B.card := by exact_mod_cast hR
      exact le_antisymm (Finset.card_le_card hsub) hN
    have hBeq : B = H := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    refine ⟨hBeq, fun k hk => ?_⟩
    by_contra hne
    have h2 : 2 ≤ (cls (crossMatrix G θ H) H k).card :=
      lt_of_le_of_ne (cls_card_pos hk) (Ne.symm hne)
    have hstrict : ((cls (crossMatrix G θ H) H k).card : ℝ)⁻¹ < 1 := by
      have : (2 : ℝ) ≤ ((cls (crossMatrix G θ H) H k).card : ℝ) := by exact_mod_cast h2
      rw [inv_lt_one_iff₀]
      right; linarith
    have hlt : blockCount G θ H < (B.card : ℝ) := by
      calc blockCount G θ H < ∑ _k ∈ B, (1 : ℝ) :=
            Finset.sum_lt_sum hterm ⟨k, hk, hstrict⟩
        _ = (B.card : ℝ) := by simp
    rw [heq, ← hBeq] at hlt
    exact absurd hlt (lt_irrefl _)
  · rintro ⟨hBeq, hone⟩
    have : blockCount G θ H = ∑ _k ∈ B, (1 : ℝ) :=
      Finset.sum_congr rfl fun k hk => by rw [hone k hk]; norm_num
    rw [this]
    simp [hBeq]

/-! ## 3. Hence the criterion, as one equation -/

omit [Fintype V] in
/-- Membership of `blk` and of a class, said in terms of adjacency rather than of the matrix. -/
theorem mem_blk_iff {k : V} :
    k ∈ blk (crossMatrix G θ H) H ↔ k ∈ H ∧ G.Adj k (θ k) := by
  classical
  simp only [blk, Finset.mem_filter, crossMatrix_eq_one_iff, CrossRel]
  tauto

omit [Fintype V] in
theorem mem_cls_iff {k i : V} :
    i ∈ cls (crossMatrix G θ H) H k
      ↔ (i ∈ H ∧ G.Adj i (θ i)) ∧ (k ∈ H ∧ G.Adj k (θ i)) := by
  classical
  simp only [cls, Finset.mem_filter, mem_blk_iff, crossMatrix_eq_one_iff, CrossRel]
  tauto

/-- **STRICTNESS IS THE COUNT REACHING ITS MAXIMUM.** On a block cut, the reflected form is strict
exactly when `blockCount = |H|`.

The two clauses of `strict_iff_cut_perfect` are the two ways the sum can fall short: a site of `H`
outside every block drops a term, and a class of size two or more drops a term below `1`. -/
theorem strict_iff_blockCount_eq (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hC : IsCrossBlock G θ H) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ blockCount G θ H = (H.card : ℝ) := by
  classical
  rw [strict_iff_cut_perfect hM h hm hC, blockCount_eq_card_iff]
  constructor
  · intro hperf
    constructor
    · refine Finset.Subset.antisymm (Finset.filter_subset _ _) (fun k hk => ?_)
      exact mem_blk_iff.mpr ⟨hk, (hperf k hk k hk).mpr rfl⟩
    · intro k hk
      obtain ⟨hkH, -⟩ := mem_blk_iff.mp hk
      refine Finset.card_eq_one.mpr ⟨k, Finset.eq_singleton_iff_unique_mem.mpr
        ⟨self_mem_cls hk, fun i hi => ?_⟩⟩
      obtain ⟨⟨hiH, -⟩, -, hki⟩ := mem_cls_iff.mp hi
      exact ((hperf k hkH i hiH).mp hki).symm
  · rintro ⟨hBeq, hone⟩ s hs q hq
    have hsblk : s ∈ blk (crossMatrix G θ H) H := (Finset.ext_iff.mp hBeq s).mpr hs
    obtain ⟨-, hss⟩ := mem_blk_iff.mp hsblk
    refine ⟨fun ha => ?_, ?_⟩
    · have hqblk : q ∈ blk (crossMatrix G θ H) H := (Finset.ext_iff.mp hBeq q).mpr hq
      obtain ⟨-, hqq⟩ := mem_blk_iff.mp hqblk
      have hmem : q ∈ cls (crossMatrix G θ H) H s := mem_cls_iff.mpr ⟨⟨hq, hqq⟩, hs, ha⟩
      obtain ⟨a, ha'⟩ := Finset.card_eq_one.mp (hone s hsblk)
      have h1 : s = a := by
        have := self_mem_cls hsblk
        rwa [ha', Finset.mem_singleton] at this
      have h2 : q = a := by rwa [ha', Finset.mem_singleton] at hmem
      rw [h1, h2]
    · rintro rfl
      exact hss

/-! ## 4. The two halves of `ReflectedFormCongr` §7, counted -/

open ReflectedFormCongr HalfBlockStructure

/-- **THE CONTIGUOUS HALF SCORES `2`, WHICH IS ITS SIZE.** Perfect cut, count maximal, strict. -/
theorem blockCount_rotHalf :
    blockCount (TorusReflection.torusGraph 1 4) torusRho rotHalf = (rotHalf.card : ℝ) := by
  refine blockCount_eq_card_iff.mpr ⟨?_, ?_⟩
  · ext k
    simp only [mem_blk_iff]
    constructor
    · exact fun hk => hk.1
    · intro hk
      exact ⟨hk, touching_rotHalf k hk⟩
  · intro k hk
    obtain ⟨hkH, -⟩ := mem_blk_iff.mp hk
    refine Finset.card_eq_one.mpr ⟨k, Finset.eq_singleton_iff_unique_mem.mpr
      ⟨self_mem_cls hk, fun i hi => ?_⟩⟩
    obtain ⟨⟨hiH, -⟩, -, hki⟩ := mem_cls_iff.mp hi
    exact (crossDiag_rotHalf k hkH i hiH hki).symm

/-- **AND THE ANTIPODAL HALF SCORES `1`, WHICH IS NOT ITS SIZE.** One block of size two, count
short by one, degenerate.

**So the invariant separates the two halves numerically**, and `ReflectedFormCongr` §7 is
`2 = 2` against `1 ≠ 2`. -/
theorem blockCount_torusHalf_ne :
    blockCount (TorusReflection.torusGraph 1 4) torusRho torusHalf ≠ (torusHalf.card : ℝ) := by
  intro hc
  have hstrict := (strict_iff_blockCount_eq isMirrorHalf_torusHalf isRefl_torusRho (m := 1)
    one_ne_zero isCrossBlock_torusHalf).mpr hc
  exact not_cutPerfect_torusHalf
    ((strict_iff_cut_perfect isMirrorHalf_torusHalf isRefl_torusRho (m := 1) one_ne_zero
      isCrossBlock_torusHalf).mp hstrict)

/-! ## 5. The name is a theorem: `blockCount` really counts the blocks

Until this section `blockCount` is a **name for a sum of reciprocals** and the claim that it counts
blocks lives in a docstring. The docstring's argument — *"a class of size `c` is counted `c` times
at weight `1/c`"* — is correct and is exactly the sort of sentence this project does not accept on
its own. Here it is proved: the classes partition the block, so the sum telescopes to their number.
-/

/-- The distinct classes of the cut, as a finset of finsets. **These are the blocks.** -/
noncomputable def blockClasses (G : SimpleGraph V) [DecidableRel G.Adj] (θ : V ≃ V)
    (H : Finset V) : Finset (Finset V) :=
  (blk (crossMatrix G θ H) H).image (cls (crossMatrix G θ H) H)

omit [Fintype V] in
theorem cls_subset_blk {k : V} :
    cls (crossMatrix G θ H) H k ⊆ blk (crossMatrix G θ H) H :=
  Finset.filter_subset _ _

omit [Fintype V] in
/-- **EVERY MEMBER OF A BLOCK HAS THAT BLOCK AS ITS CLASS.** This is what makes the classes a
partition rather than merely a covering. -/
theorem cls_eq_of_mem_blockClasses (h : IsRefl G θ) (hC : IsCrossBlock G θ H)
    {B : Finset V} (hB : B ∈ blockClasses G θ H) {k : V} (hk : k ∈ B) :
    cls (crossMatrix G θ H) H k = B := by
  classical
  have hbo : IsBlockOnes (crossMatrix G θ H) H := (isBlockOnes_iff_isCrossBlock h).mpr hC
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
  have hkblk : k ∈ blk (crossMatrix G θ H) H := cls_subset_blk hk
  have hjk : crossMatrix G θ H j k = 1 := (Finset.mem_filter.mp hk).2
  exact (cls_eq_of_rel hbo.symm (fun i _ a _ l _ hij hjl => hbo.trans i a l hij hjl)
    hj hkblk hjk).symm

omit [Fintype V] in
/-- **THE BLOCK IS COVERED BY ITS CLASSES — AND THIS NEEDS NO HYPOTHESIS AT ALL.** Both
containments are `self_mem_cls` and `cls ⊆ blk`, neither of which knows about reflections or block
structure.

**The linter found that**: the first version of this theorem carried `IsRefl` and `IsCrossBlock`
and used neither. **Being a covering is free; being DISJOINT is what needs the cut to be in
blocks**, and that is where those hypotheses are actually spent, in
`blockCount_eq_card_blockClasses` below. -/
theorem blk_eq_biUnion :
    blk (crossMatrix G θ H) H = (blockClasses G θ H).biUnion id := by
  classical
  ext k
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · intro hk
    exact ⟨cls (crossMatrix G θ H) H k, Finset.mem_image_of_mem _ hk, self_mem_cls hk⟩
  · rintro ⟨B, hB, hkB⟩
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    exact cls_subset_blk hkB

omit [Fintype V] in
/-- **AND THE COUNT IS THEIR NUMBER.** Each class contributes `|B|` terms of size `|B|⁻¹`. -/
theorem blockCount_eq_card_blockClasses (h : IsRefl G θ) (hC : IsCrossBlock G θ H) :
    blockCount G θ H = ((blockClasses G θ H).card : ℝ) := by
  classical
  have hdisj : (blockClasses G θ H : Set (Finset V)).PairwiseDisjoint id := by
    intro B hB B' hB' hne
    simp only [Finset.disjoint_left, id_eq]
    intro x hx hx'
    exact hne ((cls_eq_of_mem_blockClasses h hC hB hx).symm.trans
      (cls_eq_of_mem_blockClasses h hC hB' hx'))
  have hstep : blockCount G θ H
      = ∑ B ∈ blockClasses G θ H, ∑ _k ∈ B, ((B.card : ℝ))⁻¹ := by
    rw [blockCount, blk_eq_biUnion, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun B hB => ?_
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [cls_eq_of_mem_blockClasses h hC hB hk]
  rw [hstep]
  have hone : ∀ B ∈ blockClasses G θ H, ∑ _k ∈ B, ((B.card : ℝ))⁻¹ = 1 := by
    intro B hB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    have hpos : 0 < (cls (crossMatrix G θ H) H j).card := cls_card_pos hj
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hpos.ne')
  rw [Finset.sum_congr rfl hone, Finset.sum_const, nsmul_eq_mul, mul_one]

omit [Fintype V] in
/-- **SO THE COUNT IS A WHOLE NUMBER**, which the definition as a sum of reciprocals does not
show. -/
theorem exists_nat_blockCount (h : IsRefl G θ) (hC : IsCrossBlock G θ H) :
    ∃ n : ℕ, blockCount G θ H = (n : ℝ) :=
  ⟨(blockClasses G θ H).card, blockCount_eq_card_blockClasses h hC⟩

end BlockCount
