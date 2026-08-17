import BlockCount
import NullSpaceDimension

/-!
# The degeneracy of the coupling, as a dimension

`CrossBlockStructure` wrote *"the degeneracy of the coupling is therefore the number of blocks"* and
recorded that it was not following the reading up. `BlockCount` made the count a number and proved
the name (`blockCount_eq_card_blockClasses`). **The word `degeneracy` was still doing work no
theorem had done: a degeneracy is a dimension.** This file supplies it.

> **`finrank_couplingKer_add_blockCount`** — among the families supported on the half, the ones the
> coupling annihilates form a subspace of dimension **`|H| − blockCount`**.
>
> **`strict_iff_finrank_ker_eq_zero`** — and the reflected form is strict exactly when that
> dimension is **zero**. Three statements, one fact: the cut is perfect, the count is maximal, the
> kernel vanishes.

## Why the question is well posed here, when the estate says elsewhere that it is not

`UNLOCK_WATCHLIST` records, about the **reflected form's** null set at even side, that *"`finrank`
is the wrong question there rather than a hard one"* — the null set of a form that is not
semidefinite need not be a subspace at all. **That caveat does not transfer.** On a block cut the
coupling is a *negative* sum of squares (`crossForm_eq_neg_sum_cls_sq`), so its zero set is cut out
by **linear** conditions — one per block, by `crossForm_eq_zero_iff` — and is a subspace at every
side and in every dimension. The two objects are different and only one of them is a quadric.

## The proof, in one line

The block sums are a linear map from the supported families onto the blocks, **surjective because
distinct blocks are disjoint** so a representative of one lies in no other. Rank–nullity, with
`NullSpaceDimension.finrank_supportedOn` giving `|H|` on the left and
`BlockCount.blockCount_eq_card_blockClasses` turning the block count into `blockCount` on the right.

## What this is NOT

**It is not a statement about the reflected form.** The coupling is one ingredient of it; a null
direction of the coupling is not by itself a null direction of the reflected form, and this file
proves nothing about the latter. `NullSpaceDimension` is the estate's result there, at odd-side box
only, and it is untouched.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace BlockDimension

open SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure
open CrossPosSemidef BlockCount NullSpaceDimension

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V}

/-! ## 1. Blocks are nonempty, and distinct blocks are disjoint -/

omit [Fintype V] in
theorem blockClasses_nonempty {B : Finset V} (hB : B ∈ blockClasses G θ H) : B.Nonempty := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
  exact ⟨j, self_mem_cls hj⟩

omit [Fintype V] in
theorem blockClasses_subset {B : Finset V} (hB : B ∈ blockClasses G θ H) : B ⊆ H := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
  exact fun x hx => (Finset.mem_filter.mp (cls_subset_blk hx)).1

omit [Fintype V] in
/-- Distinct blocks are disjoint — `BlockCount.cls_eq_of_mem_blockClasses` read contrapositively.
This is the one fact the surjectivity below needs, and it is where the block structure is spent. -/
theorem blockClasses_disjoint (h : IsRefl G θ) (hC : IsCrossBlock G θ H)
    {B B' : Finset V} (hB : B ∈ blockClasses G θ H) (hB' : B' ∈ blockClasses G θ H)
    (hne : B ≠ B') {x : V} (hx : x ∈ B) : x ∉ B' := by
  intro hx'
  exact hne ((cls_eq_of_mem_blockClasses h hC hB hx).symm.trans
    (cls_eq_of_mem_blockClasses h hC hB' hx'))

/-! ## 2. The block-sum map -/

/-- **A SUPPORTED FAMILY GOES TO ITS TUPLE OF BLOCK SUMS.** Linear by inspection. -/
noncomputable def blockSums (G : SimpleGraph V) [DecidableRel G.Adj] (θ : V ≃ V) (H : Finset V) :
    supportedOn H →ₗ[ℝ] (blockClasses G θ H → ℝ) where
  toFun w := fun B => ∑ i ∈ (B : Finset V), (w : V → ℝ) i
  map_add' u v := by funext B; simpa using Finset.sum_add_distrib
  map_smul' c v := by funext B; simpa using (Finset.mul_sum _ _ c).symm

omit [Fintype V] in
@[simp] theorem blockSums_apply (w : supportedOn H) (B : blockClasses G θ H) :
    blockSums G θ H w B = ∑ i ∈ (B : Finset V), (w : V → ℝ) i := rfl

/-- A chosen member of each block. -/
noncomputable def rep (B : blockClasses G θ H) : V :=
  (blockClasses_nonempty B.2).choose

omit [Fintype V] in
theorem rep_mem (B : blockClasses G θ H) : rep B ∈ (B : Finset V) :=
  (blockClasses_nonempty B.2).choose_spec

omit [Fintype V] in
/-- **THE BLOCK SUMS ARE ONTO.** Put the required value on one representative of each block; the
representatives lie in no other block, so the tuples do not interfere.

**Disjointness is the whole of it** — with overlapping blocks the same construction would leak. -/
theorem blockSums_surjective (h : IsRefl G θ) (hC : IsCrossBlock G θ H) :
    Function.Surjective (blockSums G θ H) := by
  classical
  intro t
  set w : V → ℝ := fun i => ∑ B : blockClasses G θ H, if rep B = i then t B else 0 with hwdef
  have hsupp : w ∈ supportedOn H := by
    intro p hp
    refine Finset.sum_eq_zero fun B _ => ?_
    refine if_neg fun hrep => hp ?_
    exact blockClasses_subset B.2 (hrep ▸ rep_mem B)
  refine ⟨⟨w, hsupp⟩, ?_⟩
  funext B₀
  simp only [blockSums_apply]
  rw [hwdef, Finset.sum_comm, Finset.sum_eq_single B₀]
  · rw [Finset.sum_ite_eq (B₀ : Finset V) (rep B₀) (fun _ => t B₀), if_pos (rep_mem B₀)]
  · intro B _ hBne
    rw [Finset.sum_ite_eq (B₀ : Finset V) (rep B) (fun _ => t B), if_neg]
    exact blockClasses_disjoint h hC B.2 B₀.2 (fun hc => hBne (Subtype.ext hc)) (rep_mem B)
  · intro hc
    exact absurd (Finset.mem_univ B₀) hc

/-! ## 3. Rank–nullity -/

omit [Fintype V] in
/-- **THE DEGENERACY OF THE COUPLING IS A DIMENSION, AND IT IS `|H| − blockCount`.**

Stated additively so that no subtraction on `ℕ` appears. **`[Finite V]` replaces the section's
`[Fintype V]`**: the statement needs neither, but the proof needs the ambient space to be
finite-dimensional, so the linter's own suggestion — `Finite` plus `Fintype.ofFinite` — is taken
rather than the omission being forced. -/
theorem finrank_ker_blockSums_add [Finite V] (h : IsRefl G θ) (hC : IsCrossBlock G θ H) :
    Module.finrank ℝ (LinearMap.ker (blockSums G θ H)) + (blockClasses G θ H).card = H.card := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have hrange : LinearMap.range (blockSums G θ H) = ⊤ :=
    LinearMap.range_eq_top.mpr (blockSums_surjective h hC)
  have hfr : Module.finrank ℝ (LinearMap.range (blockSums G θ H))
      = (blockClasses G θ H).card := by
    rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have := LinearMap.finrank_range_add_finrank_ker (blockSums G θ H)
  rw [hfr, finrank_supportedOn] at this
  omega

omit [Fintype V] in
/-- The same, with the count written as `blockCount`. -/
theorem finrank_ker_blockSums_add_blockCount [Finite V] (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) :
    (Module.finrank ℝ (LinearMap.ker (blockSums G θ H)) : ℝ) + blockCount G θ H
      = (H.card : ℝ) := by
  rw [blockCount_eq_card_blockClasses h hC]
  exact_mod_cast finrank_ker_blockSums_add h hC

/-! ## 4. And that kernel is the coupling's -/

/-- **THE KERNEL OF THE BLOCK SUMS IS EXACTLY WHERE THE COUPLING VANISHES.**
`CrossBlockStructure.crossForm_eq_zero_iff` indexes the conditions by members of `blk`; this
re-indexes them by the blocks themselves, which is the same family of conditions listed once
each. -/
theorem mem_ker_blockSums_iff (h : IsRefl G θ) (hC : IsCrossBlock G θ H) (hM : IsMirrorHalf θ H Mir)
    (m : ℝ) (w : supportedOn H) :
    w ∈ LinearMap.ker (blockSums G θ H) ↔ crossForm G m θ H (w : V → ℝ) = 0 := by
  classical
  rw [crossForm_eq_zero_iff hM h hC m, LinearMap.mem_ker]
  constructor
  · intro hk k hkblk
    have := congrFun hk ⟨cls (crossMatrix G θ H) H k, Finset.mem_image_of_mem _ hkblk⟩
    simpa using this
  · intro hall
    funext B
    obtain ⟨j, hj, hBj⟩ := Finset.mem_image.mp B.2
    have : (B : Finset V) = cls (crossMatrix G θ H) H j := hBj.symm
    rw [blockSums_apply, this]
    simpa using hall j hj

/-- **AND STRICTNESS IS THE KERNEL BEING TRIVIAL.**

This is what `CrossBlockStructure` meant by *"the shape `StrictBiconditional`'s machinery
consumes"*: the reflected form is strict exactly when the coupling annihilates no nonzero family
supported on the half. Three statements now say one thing — the cut is perfect, the count is
maximal, the kernel is zero. -/
theorem strict_iff_finrank_ker_eq_zero (h : IsRefl G θ) (hC : IsCrossBlock G θ H)
    (hM : IsMirrorHalf θ H Mir) {m : ℝ} (hm : m ≠ 0) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ Module.finrank ℝ (LinearMap.ker (blockSums G θ H)) = 0 := by
  rw [BlockCount.strict_iff_blockCount_eq hM h hm hC, blockCount_eq_card_blockClasses h hC]
  have hadd := finrank_ker_blockSums_add h hC
  constructor
  · intro heq
    have : (blockClasses G θ H).card = H.card := by exact_mod_cast heq
    omega
  · intro hz
    have : (blockClasses G θ H).card = H.card := by omega
    exact_mod_cast this

/-- **THE STATEMENT THE PHRASE ASKED FOR, IN ONE PLACE.** A packaging of the two theorems above and
nothing more — the dimension, and the identification of that kernel with the coupling's. -/
theorem finrank_couplingKer_add_blockCount (h : IsRefl G θ) (hC : IsCrossBlock G θ H)
    (hM : IsMirrorHalf θ H Mir) (m : ℝ) :
    (Module.finrank ℝ
        (LinearMap.ker (blockSums G θ H)) : ℝ) + blockCount G θ H = (H.card : ℝ)
      ∧ ∀ w : supportedOn H,
          w ∈ LinearMap.ker (blockSums G θ H) ↔ crossForm G m θ H (w : V → ℝ) = 0 :=
  ⟨finrank_ker_blockSums_add_blockCount h hC, mem_ker_blockSums_iff h hC hM m⟩

/-! ## 5. The two halves, measured

`PROOF_STRATEGY` §6 Q3: §§1–4 are a criterion and nothing had been measured with it. These are the
two halves of `ReflectedFormCongr` §7, and the criterion returns a dimension for each — **derived
from the strictness facts already proved, through `strict_iff_finrank_ker_eq_zero`**, with no new
computation at all.

**A route that was tried and abandoned, recorded as what it is.** The first attempt computed
`blockClasses` directly at each half — `blk`, `cls`, then the image — in order to read off `1` and
`2` and get the exact dimensions. `blk` and `cls` filter on a **real** matrix entry, so they are
`noncomputable` and the arithmetic had to be routed through
`BlockCount.mem_blk_iff` / `mem_cls_iff` into adjacency, where `decide` can work. **That build did
not finish in a reasonable time and was killed.** This is a fact about that attempt and this build
machine, **not a claim that the computation is hard** (`ERRATUM 194`): the route below makes it
unnecessary, so nothing was learned about the cost of the one abandoned.
-/

open HalfBlockStructure ReflectedFormCongr

/-- **THE CONTIGUOUS HALF: THE COUPLING IS BLIND IN NO DIRECTION.**

`ReflectedFormCongr.torusFour_strict_rotHalf` says the reflected form is strict there; §3 says
strictness *is* the kernel vanishing. -/
theorem finrank_ker_rotHalf {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (LinearMap.ker
        (blockSums (TorusReflection.torusGraph 1 4) torusRho rotHalf)) = 0 :=
  (strict_iff_finrank_ker_eq_zero isRefl_torusRho
      (isCrossBlock_of_cross_diag crossDiag_rotHalf) isMirrorHalf_rotHalf (m := m) hm).mp
    (fun c hc0 hcs => torusFour_strict_rotHalf m hm c hc0 hcs)

/-- **THE ANTIPODAL HALF: THE COUPLING IS BLIND IN AT LEAST ONE.**

`ReflectedFormCongr.torusFour_not_strict` says the reflected form is *not* strict there, so by §3
the kernel is not trivial. **This is the dimension statement doing work**: a degeneracy that §7
could only report as a failed inequality is here a positive number of directions. -/
theorem finrank_ker_torusHalf_pos {m : ℝ} (hm : m ≠ 0) :
    0 < Module.finrank ℝ (LinearMap.ker
        (blockSums (TorusReflection.torusGraph 1 4) torusRho torusHalf)) := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ (LinearMap.ker
      (blockSums (TorusReflection.torusGraph 1 4) torusRho torusHalf))) with hz | hpos
  · exact absurd ((strict_iff_finrank_ker_eq_zero isRefl_torusRho isCrossBlock_torusHalf
      isMirrorHalf_torusHalf (m := m) hm).mpr hz) (torusFour_not_strict m hm)
  · exact hpos

/-- **AND SO THE TWO HALVES ARE SEPARATED BY A DIMENSION**, not only by an inequality holding or
failing. One graph, one reflection, one mass, two halves: blind in no direction, blind in at least
one.

**Not the exact value.** That the antipodal half's kernel has dimension exactly `1` would follow
from `finrank_ker_blockSums_add` together with the block count there being `1`, and the block count
is what the abandoned route was computing. **Recorded as not done.** -/
theorem finrank_ker_two_halves {m : ℝ} (hm : m ≠ 0) :
    Module.finrank ℝ (LinearMap.ker
        (blockSums (TorusReflection.torusGraph 1 4) torusRho rotHalf)) = 0
      ∧ 0 < Module.finrank ℝ (LinearMap.ker
        (blockSums (TorusReflection.torusGraph 1 4) torusRho torusHalf)) :=
  ⟨finrank_ker_rotHalf hm, finrank_ker_torusHalf_pos hm⟩

end BlockDimension
