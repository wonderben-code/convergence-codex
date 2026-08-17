import BlockDimension

/-!
# How far from strict: the reach kernel's dimension is exactly `|H| − blockCount`

`CrossBlockStructure.strict_iff_reachKernel_trivial` reads: the reflected form is strict exactly
when the **reach kernel** — the families supported on the half that the massive operator does not
push out of the region — contains nothing but zero. That is a yes/no answer, and it was the last
word the estate had on degeneracy. When a half is *not* strict, nothing said **how far from strict
it is**.

`StrictBiconditional.InReachKernel`'s own docstring calls it *"a linear condition, though nothing
here needs it to be"* — and then nothing uses that. It is two linear conditions, so the reach
kernel is a subspace and has a dimension. This file takes that dimension and computes it.

> **`finrank_reachKer_add_blockCount`** — on a block cut,
> **`finrank (reachKer) + blockCount = |H|`.**

Every block of the cut buys back exactly one dimension of the half, and what is left over is the
space the reflected form degenerates on. `strict_iff_reachKer_eq_bot` is then the case `= 0` of a
statement that now has a value at every half, not only at the strict ones.

## Two things that fall out of the identity

* **`reachKer_eq_of_mass`** — on a block cut the reach kernel does not depend on `m`. The
  right-hand side of the identity is combinatorial, so the left-hand side cannot move with the
  mass. Nothing before this said that; `InReachKernel` mentions `m` in its definition.
* **`two_le_finrank_reachKer`** — two blocks short of `|H|` means degeneracy in **two independent
  directions**. The biconditional could not distinguish "not strict" from "very far from strict";
  this does, and it is the first statement in the estate that does.

## What this file corrected in its own drafting, recorded because it was nearly committed

The first version of this file defined the three clauses of
`StrictBiconditional.SupportedIsotropic` as a submodule and proved *strictness is that submodule
being `⊥`*. It compiled, it was green, and it was **a weaker restatement of
`CrossBlockStructure.strict_iff_reachKernel_trivial`**: that file's
`crossForm_eq_zero_of_inReachKernel` already proves the isotropy clause is implied by the other
two, **with no block hypothesis at all**, so the draft's third clause was redundant and its
`IsCrossBlock` hypothesis was pure cost. The statement-level grep of ERRATUM 176 caught it; a
name-level grep would not have, because no name collided.

What survives from that draft is the observation that drove it — the criterion is an existential
over a set that is secretly linear — and it is used here on the *right* set, the one that needs no
block hypothesis to be a subspace.

## What this does NOT do

`UNLOCK_WATCHLIST` says of the **reflected form's null set** at even side that *"the null set need
not be a subspace at all — `finrank` is the wrong question there rather than a hard one."*
**That clause stands and this file does not touch it.** The set it describes is
`{c | reflectedForm c = 0}` among admissible families, a genuine quadric in the coefficients.
`reachKer` is a different object: the families the *operator* keeps inside the region. **Nothing
here says the quadric is a subspace.**

**SUPERSEDED THE SAME DAY, BY `TorusBlockCount`.** This header said:

> *"The **exact** value of `finrank (reachKer)` at the estate's `torusHalf` is still NOT DONE, for
> the same reason `BlockDimension` §5 recorded: it needs the exact block count there, which no file
> computes. The identity above turns that into a purely combinatorial question, which is a change
> of difficulty and not a proof."*

The first clause was true when written and is now false:
`TorusBlockCount.card_blockClasses_torusHalf` computes the block count (**one block**) and
`TorusBlockCount.finrank_reachKer_torusHalf` reads the value off this file's identity —
**exactly one dimension**. The last clause was right about itself:
the change of difficulty was the whole of it, and the combinatorial question took one file.

**No published tag moves**, `OS4` does not move, and no spectral gap is claimed.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace ReachKernelDimension

open Matrix SimpleGraph GraphReflection GraphMirrorReflection CrossFormMatrix CrossBlockStructure
open CrossPosSemidef BlockCount BlockDimension NullSpaceDimension

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {θ : V ≃ V} {H Mir : Finset V} {m : ℝ}

/-! ## 1. The reach kernel, as a subspace -/

/-- **THE REACH KERNEL AS A SUBSPACE.** Supported on the half, and not pushed out of the region by
the massive operator. Both clauses are linear; no block hypothesis is needed for that. -/
def reachKer (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℝ) (H Mir : Finset V) :
    Submodule ℝ (V → ℝ) where
  carrier := {v | (∀ p, p ∉ H → v p = 0)
    ∧ ∀ p, p ∉ H → p ∉ Mir → (GraphLaplacian.massive G m *ᵥ v) p = 0}
  add_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨fun p hp => by simp [hu1 p hp, hv1 p hp], fun p hp hpm => ?_⟩
    rw [Matrix.mulVec_add]
    simp [hu2 p hp hpm, hv2 p hp hpm]
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ _ => by simp⟩
  smul_mem' := by
    rintro c v ⟨hv1, hv2⟩
    refine ⟨fun p hp => by simp [hv1 p hp], fun p hp hpm => ?_⟩
    rw [Matrix.mulVec_smul]
    simp [hv2 p hp hpm]

@[simp] theorem mem_reachKer {v : V → ℝ} :
    v ∈ reachKer G m H Mir ↔ StrictBiconditional.InReachKernel G m H Mir v := Iff.rfl

/-- The reach kernel lives on the half, which is what makes its dimension comparable with `|H|`. -/
theorem reachKer_le_supported : reachKer G m H Mir ≤ supportedOn H := fun _ hv => hv.1

/-- **STRICTNESS IS THE REACH KERNEL BEING `⊥`.**

This is `CrossBlockStructure.strict_iff_reachKernel_trivial` with `= ⊥` written where that theorem
writes a quantifier, and **it is packaging and nothing more**. It earns its place only because
`⊥` is a value of something that has other values, and §4 computes them. -/
theorem strict_iff_reachKer_eq_bot (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hm : m ≠ 0)
    (hC : IsCrossBlock G θ H) :
    (∀ c : V → ℝ, c ≠ 0 → (∀ p, p ∉ H → p ∉ Mir → c p = 0) →
        0 < GraphReflection.reflectedForm G m θ c)
      ↔ reachKer G m H Mir = ⊥ := by
  have hcross : ∀ w : V → ℝ, crossForm G m θ H w ≤ 0 :=
    (hcross_iff_isCrossBlock hM h m).mpr hC
  rw [strict_iff_reachKernel_trivial hM h hm hcross, Submodule.eq_bot_iff]
  exact ⟨fun htriv v hv => htriv v hv, fun hbot v hv => hbot v hv⟩

/-! ## 2. A row of the cut matrix is a block sum -/

omit [Fintype V] in
/-- **ON A BLOCK CUT, ONE ENTRY FORCES BOTH ITS SITES INTO `blk`.** `IsCrossBlock.loop` says a
half-site with any cross-neighbour is joined to its own mirror; applied at both ends of the entry
it puts both ends in `blk`. -/
theorem mem_blk_of_entry (h : IsRefl G θ) (hC : IsCrossBlock G θ H) {s q : V}
    (hsq : crossMatrix G θ H s q = 1) :
    s ∈ blk (crossMatrix G θ H) H ∧ q ∈ blk (crossMatrix G θ H) H := by
  have hr : CrossRel G θ H s q := (crossMatrix_eq_one_iff s q).mp hsq
  have hqs : CrossRel G θ H q s :=
    (crossMatrix_eq_one_iff q s).mp ((crossMatrix_symm h q s).trans hsq)
  exact ⟨mem_blk_iff.mpr ⟨hr.1, hC.loop s q hr⟩, mem_blk_iff.mpr ⟨hr.2.1, hC.loop q s hqs⟩⟩

omit [Fintype V] in
/-- A half-site outside `blk` has an empty class: it meets the cut nowhere. -/
theorem cls_eq_empty_of_notMem_blk (h : IsRefl G θ) (hC : IsCrossBlock G θ H) {s : V}
    (hs : s ∉ blk (crossMatrix G θ H) H) : cls (crossMatrix G θ H) H s = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr fun q hq => hs ?_
  have hq1 : crossMatrix G θ H s q = 1 := by
    rw [crossMatrix_eq_one_iff]
    obtain ⟨⟨hqH, _⟩, hsH, hadj⟩ := mem_cls_iff.mp hq
    exact ⟨hsH, hqH, hadj⟩
  exact (mem_blk_of_entry h hC hq1).1

omit [Fintype V] in
/-- **A ROW OF THE CUT MATRIX, APPLIED TO A FAMILY, IS THAT FAMILY'S BLOCK SUM.** Off the class the
entries are zero, on it they are one. This is the step that turns
`CrossBlockStructure.inReachKernel_iff_rows` — one linear equation per half-site — into one linear
equation per block. -/
theorem row_eq_cls_sum (h : IsRefl G θ) (hC : IsCrossBlock G θ H) (s : V) (v : V → ℝ) :
    ∑ q ∈ H, crossMatrix G θ H s q * v q = ∑ q ∈ cls (crossMatrix G θ H) H s, v q := by
  classical
  have hsub : cls (crossMatrix G θ H) H s ⊆ H := fun q hq => (mem_cls_iff.mp hq).1.1
  have hzero : ∀ q ∈ H, q ∉ cls (crossMatrix G θ H) H s →
      crossMatrix G θ H s q * v q = 0 := by
    intro q _ hq
    rcases crossMatrix_entries (G := G) (θ := θ) (H := H) s q with h0 | h1
    · rw [h0, zero_mul]
    · refine absurd ?_ hq
      obtain ⟨hs, hq'⟩ := mem_blk_of_entry h hC h1
      obtain ⟨_, _, hadj⟩ := (crossMatrix_eq_one_iff s q).mp h1
      exact mem_cls_iff.mpr ⟨mem_blk_iff.mp hq', ⟨(mem_blk_iff.mp hs).1, hadj⟩⟩
  rw [← Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl fun q hq => by
    obtain ⟨⟨hqH, _⟩, hsH, hadj⟩ := mem_cls_iff.mp hq
    rw [(crossMatrix_eq_one_iff s q).mpr ⟨hsH, hqH, hadj⟩, one_mul]

/-! ## 3. And so membership is a block condition -/

/-- **MEMBERSHIP OF THE REACH KERNEL IS ONE LINEAR CONDITION PER BLOCK.** The half-sites outside
`blk` impose nothing, because their classes are empty. -/
theorem mem_reachKer_iff_blk (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) {v : V → ℝ} :
    v ∈ reachKer G m H Mir
      ↔ (∀ p, p ∉ H → v p = 0)
        ∧ ∀ k ∈ blk (crossMatrix G θ H) H, ∑ i ∈ cls (crossMatrix G θ H) H k, v i = 0 := by
  rw [mem_reachKer, inReachKernel_iff_rows hM h m v]
  constructor
  · rintro ⟨hv, hrows⟩
    refine ⟨hv, fun k hk => ?_⟩
    rw [← row_eq_cls_sum h hC k v]
    exact hrows k (mem_blk_iff.mp hk).1
  · rintro ⟨hv, hblk⟩
    refine ⟨hv, fun s _ => ?_⟩
    rw [row_eq_cls_sum h hC s v]
    by_cases hsb : s ∈ blk (crossMatrix G θ H) H
    · exact hblk s hsb
    · rw [cls_eq_empty_of_notMem_blk h hC hsb, Finset.sum_empty]

omit [Fintype V] in
/-- Indexing the block conditions by the blocks or by their members is the same family of
conditions. -/
theorem blockSums_zero_iff {v : V → ℝ} :
    (∀ B ∈ blockClasses G θ H, ∑ i ∈ B, v i = 0)
      ↔ ∀ k ∈ blk (crossMatrix G θ H) H, (∑ i ∈ cls (crossMatrix G θ H) H k, v i) = 0 := by
  constructor
  · intro hB k hk
    exact hB _ (Finset.mem_image_of_mem _ hk)
  · rintro hk B hB
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
    exact hk j hj

/-- The same, indexed by the blocks themselves. -/
theorem mem_reachKer_iff_blockSums (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) {v : V → ℝ} :
    v ∈ reachKer G m H Mir
      ↔ (∀ p, p ∉ H → v p = 0) ∧ ∀ B ∈ blockClasses G θ H, ∑ i ∈ B, v i = 0 := by
  rw [mem_reachKer_iff_blk hM h hC, blockSums_zero_iff]

/-- **THE CONVERSE OF `crossForm_eq_zero_of_inReachKernel`, ON A BLOCK CUT.** That theorem says a
vector in the reach kernel is annihilated by the coupling, on every graph. The converse is false in
general — the coupling's vanishing is one scalar equation and the reach condition is `|H|` of them
— but on a block cut both sides are the same list of block sums. -/
theorem mem_reachKer_iff_crossForm (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) {v : V → ℝ} (hv : ∀ p, p ∉ H → v p = 0) :
    v ∈ reachKer G m H Mir ↔ crossForm G m θ H v = 0 := by
  rw [mem_reachKer_iff_blk hM h hC, crossForm_eq_zero_iff hM h hC m v]
  exact ⟨fun hx => hx.2, fun hx => ⟨hv, hx⟩⟩

/-- **THE REACH KERNEL DOES NOT MOVE WITH THE MASS.** Its description in §3 is combinatorial, and
the mass appears nowhere in it. `InReachKernel` mentions `m` in its definition, so this is not
visible from the definition — it is a consequence of the block hypothesis.

`CrossFormMatrix.crossForm_mass_independent` already says the *coupling* is mass-free; that is the
reason the right-hand side of §3 has no `m` in it. What is new is that the property crosses to the
reach kernel, which is defined through `GraphLaplacian.massive G m` and therefore does move with
the mass on a graph whose cut is not in blocks. -/
theorem reachKer_eq_of_mass (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) (m₁ m₂ : ℝ) :
    reachKer G m₁ H Mir = reachKer G m₂ H Mir := by
  ext v
  rw [mem_reachKer_iff_blockSums (m := m₁) hM h hC, mem_reachKer_iff_blockSums (m := m₂) hM h hC]

/-! ## 4. The dimension -/

/-- The reach kernel, seen inside the supported families, is the kernel of the block sums. -/
theorem comap_reachKer (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ) (hC : IsCrossBlock G θ H) :
    Submodule.comap (supportedOn H).subtype (reachKer G m H Mir)
      = LinearMap.ker (blockSums G θ H) := by
  ext w
  rw [Submodule.mem_comap, mem_ker_blockSums_iff h hC hM m]
  exact mem_reachKer_iff_crossForm hM h hC w.2

/-- **HOW FAR FROM STRICT, EXACTLY.** On a block cut the reflected form degenerates on a space of
dimension `|H| − blockCount`, written additively so that no subtraction on `ℕ` appears.

Before this the left-hand side was known only to be zero or not zero.

**Where the content is.** The rank–nullity is `BlockDimension.finrank_ker_blockSums_add` and
nothing here reproves it; this is that theorem carried across `comap_reachKer`. The work is §2–§3
— the identification of the reach kernel with the block-sum kernel — and the value of the carry is
that `reachKer` is the object the strictness criterion is stated about, while `blockSums` is an
auxiliary map defined to count blocks. -/
theorem finrank_reachKer_add (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) :
    Module.finrank ℝ (reachKer G m H Mir) + (blockClasses G θ H).card = H.card := by
  have he := (Submodule.comapSubtypeEquivOfLe
    (reachKer_le_supported (G := G) (m := m) (H := H) (Mir := Mir))).finrank_eq
  rw [comap_reachKer hM h hC] at he
  rw [← he]
  exact finrank_ker_blockSums_add h hC

/-- The same, with the count written as `blockCount`. -/
theorem finrank_reachKer_add_blockCount (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) :
    (Module.finrank ℝ (reachKer G m H Mir) : ℝ) + blockCount G θ H = (H.card : ℝ) := by
  rw [blockCount_eq_card_blockClasses h hC]
  exact_mod_cast finrank_reachKer_add (m := m) hM h hC

/-! ## 5. What the number buys -/

/-- **TWO BLOCKS SHORT IS TWO DIMENSIONS OF DEGENERACY.** The biconditional could say only "not
strict"; this separates "not strict" from "far from strict", and the separation is by a
combinatorial count. -/
theorem two_le_finrank_reachKer (hM : IsMirrorHalf θ H Mir) (h : IsRefl G θ)
    (hC : IsCrossBlock G θ H) (hgap : (blockClasses G θ H).card + 2 ≤ H.card) :
    2 ≤ Module.finrank ℝ (reachKer G m H Mir) := by
  have := finrank_reachKer_add (m := m) (Mir := Mir) hM h hC
  omega

/-- **THE HALF BOUNDS THE DEGENERACY, WITH NO BLOCK HYPOTHESIS.** From §1's containment alone: the
reflected form cannot degenerate in more directions than the half has sites. -/
theorem finrank_reachKer_le_card : Module.finrank ℝ (reachKer G m H Mir) ≤ H.card := by
  have hle := Submodule.finrank_mono (reachKer_le_supported (G := G) (m := m) (H := H) (Mir := Mir))
  rwa [finrank_supportedOn] at hle

end ReachKernelDimension
