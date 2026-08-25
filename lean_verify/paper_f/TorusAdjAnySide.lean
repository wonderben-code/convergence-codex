import TorusInnerSupport
import TorusAnySide

/-!
# Adjacency to the mirror on the torus, at every side length

`TorusReflection.adj_torus_revSite_iff` characterises when a site of the lower half is adjacent to
the mirror of another, and it carries `Even n`. `TorusAnySide.torus_cross_diag_any` proves the
*consequence* — that adjacency forces equality — at every side, for `strictLower`. This file
supplies the characterisation itself at every side. **`Even n` was load-bearing in exactly two
places on this route, and they are the same phenomenon**: here, and in
`NullSpaceEven.anti_eq_self_of_mem`, which uses it only to know that `lowerHalf` is a half. Both
are discharged below, so the odd torus's null space needs nothing further with a parity
hypothesis.

> `adj_torus_revSite_iff_any` — for `p q ∈ strictLower i n`, at **every** `n`,
> `p ~ revSite i q ↔ p = q ∧ (2·pᵢ + 2 = n ∨ pᵢ = 0)`.

## Where the parity went

Nowhere. It was never in the geometry; it was in the SET.

`lowerHalf` asks `2·pᵢ < n` and `strictLower` asks `2·pᵢ + 1 < n`, and on an even side those are
the same condition — which is why the even proof could be stated with the weaker one. Every step
of that proof that consumed `Even n` consumed it to recover, from `2·pᵢ < n`, the fact that
`2·pᵢ + 1 ≠ n`; on an odd side that fact is false for the midline and true for everything below
it. Asking for `strictLower` supplies it directly. **What is checked rather than asserted**: the
proof below is the even proof with `obtain ⟨t, ht⟩ := hn` deleted and nothing put in its place, and
it compiles — so no step needed the parity for anything the stronger bound does not already give.
Two of the steps were traced by hand (the coordinate-pinning `omega`, and the loop-freeness
obligation `pᵢ ≠ revᵢ`, which is literally `2·pᵢ + 1 ≠ n`); the rest are covered by the compile and
not by a reading. `adj_torus_revSite_iff'` re-derives the even statement from the general one, to
check that the generalisation really covers the case it was extracted from.

## Which two layers, and why they are parity-blind

`adjT` has four cases and two survive, exactly as `TorusAnySide` §1 describes: `pᵢ + 1 = revᵢ`
forces `n = 2·pᵢ + 2`, the innermost layer against the cut, and `pᵢ = 0` is the seam wrapping
round to `n − 1`. **Neither case mentions parity.** What parity decides is only whether the first
is *inhabited*: at odd `n` no site satisfies `2·pᵢ + 2 = n`, so the disjunction collapses to the
seam alone and the odd torus has ONE layer where the even torus has two.

**The count across both lattices, stated because I got it wrong once.** The box has ZERO crossing
layers at odd side — `BoxOddReflection.crossForm_odd_eq_zero` is an equality with zero, not an
estimate — and ONE at even side. The torus has one at odd side and two at even. So the torus is
uniformly *the box plus the seam*, and the seam is there at every side
(`exists_adj_revSite_torus`, which needs `2 ≤ n` and no parity at all). The draft of this header
said the odd box has one layer where the even box has two; it has none.

## And the set was already right

`torusInner i n = {p : 1 ≤ pᵢ ∧ 2·pᵢ + 2 < n}` was defined for the even side, but
`mem_torusInner_iff_sdiff` shows it is `strictLower` minus both layers **at every `n`**, with no
parity hypothesis, because `2·pᵢ + 1 < n` together with `2·pᵢ + 2 ≠ n` simply *is* `2·pᵢ + 2 < n`.
`TorusInnerSupport.massive_mulVec_supported_torus` already had no parity hypothesis either. So the
odd torus needs no new set and no new support lemma — only the characterisation above.

## What is NOT proved

The null space itself. That is the next file: the cross form at every side, the description, and
the dimension. Everything it needs is either here or already parity-free.
-/

namespace TorusAdjAnySide

open Finset BoxGraph BoxOddReflection GraphHalfSpace GraphReflection
open TorusReflection TorusInnerSupport GraphMirrorReflection

variable {d n : ℕ}

/-! ## 1. The characterisation, at every side length -/

/-- **ADJACENCY TO THE MIRROR, AT EVERY SIDE.** `TorusReflection.adj_torus_revSite_iff` with
`Even n` deleted and `lowerHalf` replaced by `strictLower` — which on an even side is the same
set, and on an odd side is the half the reflection machinery actually uses. -/
theorem adj_torus_revSite_iff_any (i : Fin d) (n : ℕ) {p q : Site d n}
    (hp : p ∈ strictLower i n) (hq : q ∈ strictLower i n) :
    (torusGraph d n).Adj p (revSite (n := n) i q)
      ↔ (p = q ∧ (2 * (p i).val + 2 = n ∨ (p i).val = 0)) := by
  classical
  rw [mem_strictLower] at hp hq
  have hrevq : (Fin.rev (q i)).val = n - ((q i).val + 1) := Fin.val_rev (q i)
  have hqlt : (q i).val < n := (q i).isLt
  have hplt : (p i).val < n := (p i).isLt
  constructor
  · rintro ⟨k, h1, hne, h2⟩
    have hki : k = i := by
      by_contra hk
      have hcoord : p i = revSite (n := n) i q i := h1 i (Ne.symm hk)
      rw [revSite_apply_self] at hcoord
      have : (p i).val = n - ((q i).val + 1) := by rw [hcoord, hrevq]
      omega
    subst hki
    rw [revSite_apply_self] at h2
    have hval : (Fin.rev (q k)).val = n - ((q k).val + 1) := hrevq
    have hpk : (p k).val = (q k).val := by
      rcases h2 with h | h | ⟨h, h'⟩ | ⟨h, h'⟩ <;> omega
    refine ⟨?_, by omega⟩
    funext j
    by_cases hj : j = k
    · subst hj; exact Fin.ext hpk
    · have := h1 j hj
      rwa [revSite_apply_ne hj] at this
  · rintro ⟨rfl, hlayer⟩
    refine ⟨i, fun j hj => (revSite_apply_ne hj p).symm, ?_, ?_⟩
    · intro hc
      have : (p i).val = (Fin.rev (p i)).val := by
        rw [← revSite_apply_self (n := n) i p, ← hc]
      have hrp : (Fin.rev (p i)).val = n - ((p i).val + 1) := Fin.val_rev (p i)
      omega
    · rw [revSite_apply_self]
      have hrp : (Fin.rev (p i)).val = n - ((p i).val + 1) := Fin.val_rev (p i)
      rcases hlayer with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))

/-- **THE CASE IT CAME FROM, RECOVERED.** `TorusReflection.adj_torus_revSite_iff` in one line
from the general statement, which is the check that the generalisation is one — the estate's
convention since `SmallSideStrict.reflectionPositive_box_one_strict'`. At even side `lowerHalf`
and `strictLower` are the same set, and `strictLower_eq_lowerHalf_of_even` is the equality. -/
theorem strictLower_eq_lowerHalf_of_even (i : Fin d) (hn : Even n) :
    strictLower i n = lowerHalf i n := by
  ext p
  rw [mem_strictLower, lowerHalf, Finset.mem_filter]
  obtain ⟨t, ht⟩ := hn
  constructor
  · intro h; exact ⟨Finset.mem_univ p, by omega⟩
  · rintro ⟨-, h⟩; omega

theorem adj_torus_revSite_iff' (i : Fin d) (hn : Even n) {p q : Site d n}
    (hp : p ∈ lowerHalf i n) (hq : q ∈ lowerHalf i n) :
    (torusGraph d n).Adj p (revSite (n := n) i q)
      ↔ (p = q ∧ (2 * (p i).val + 2 = n ∨ (p i).val = 0)) :=
  adj_torus_revSite_iff_any i n
    (by rw [strictLower_eq_lowerHalf_of_even i hn]; exact hp)
    (by rw [strictLower_eq_lowerHalf_of_even i hn]; exact hq)

/-! ## 2. The interior set was already the right one, at every side -/

/-- **`torusInner` IS `strictLower` MINUS BOTH LAYERS, AT EVERY SIDE.** No parity hypothesis:
`2·pᵢ + 1 < n` says `2·pᵢ + 2 ≤ n`, so adding `2·pᵢ + 2 ≠ n` gives `2·pᵢ + 2 < n` outright.
This is why the odd torus needs no new set — and why
`TorusInnerSupport.lowerHalf_sdiff_torusInner`, which does use `Even n`, is a statement about
`lowerHalf` and not about the interior. -/
theorem mem_torusInner_iff_sdiff (i : Fin d) {p : Site d n} :
    p ∈ torusInner i n
      ↔ p ∈ strictLower i n ∧ ¬ (2 * (p i).val + 2 = n ∨ (p i).val = 0) := by
  rw [mem_torusInner, mem_strictLower]
  omega

theorem torusInner_subset_strictLower (i : Fin d) (n : ℕ) :
    torusInner i n ⊆ strictLower i n :=
  fun _ hp => ((mem_torusInner_iff_sdiff i).mp hp).1

/-- **THE DEFICIENCY AT EVERY SIDE**, as a set identity, against `strictLower` rather than
`lowerHalf`. `TorusInnerSupport.lowerHalf_sdiff_torusInner` is the even-side statement against
`lowerHalf`; the two agree there because the sets do, and only this one survives at odd side. -/
theorem strictLower_sdiff_torusInner (i : Fin d) (n : ℕ) :
    (strictLower i n) \ (torusInner i n)
      = (strictLower i n).filter (fun p => 2 * (p i).val + 2 = n ∨ (p i).val = 0) := by
  classical
  ext p
  rw [Finset.mem_sdiff, Finset.mem_filter, mem_torusInner_iff_sdiff]
  tauto

/-! ## 2b. The second parity-bound ingredient, discharged the same way -/

/-- **ANTISYMMETRISATION IS THE IDENTITY ON `strictLower`, AT EVERY SIDE.**
`NullSpaceEven.anti_eq_self_of_mem` is this for `lowerHalf` and it takes `Even n` — used for
nothing but `isHalf_lowerHalf`. `BoxOddReflection.isMirrorHalf_strictLower` is already parity-free,
so the same two lines go through with no hypothesis. This is the second and last place the even
route consumed parity, and it consumed it for the same reason as the first: to know that the set
it was handed is a half. -/
theorem anti_eq_self_of_mem_any (i : Fin d) (n : ℕ) {v : Site d n → ℝ}
    (hv : ∀ p, p ∉ strictLower i n → v p = 0) {p : Site d n} (hp : p ∈ strictLower i n) :
    anti (revSite (n := n) i) v p = v p := by
  have hM := isMirrorHalf_strictLower i n
  have hsplit := hM.split p (hM.disj p hp)
  rw [anti, hv _ (hsplit.mp hp), sub_zero]

/-! ## 3. What parity decides: whether the innermost layer exists at all -/

/-- **AT ODD SIDE THE INNERMOST LAYER IS EMPTY**, so the disjunction above collapses to the seam.
This is the whole difference between the two parities on the torus, and it is one line. -/
theorem inner_layer_empty_of_odd (i : Fin d) (hn : Odd n) (p : Site d n) :
    ¬ (2 * (p i).val + 2 = n) := by
  obtain ⟨t, ht⟩ := hn
  omega

/-- **SO AT ODD SIDE, ADJACENCY TO THE MIRROR IS THE SEAM AND NOTHING ELSE.** -/
theorem adj_torus_revSite_iff_odd (i : Fin d) (hn : Odd n) {p q : Site d n}
    (hp : p ∈ strictLower i n) (hq : q ∈ strictLower i n) :
    (torusGraph d n).Adj p (revSite (n := n) i q) ↔ (p = q ∧ (p i).val = 0) := by
  rw [adj_torus_revSite_iff_any i n hp hq]
  constructor
  · rintro ⟨rfl, h | h⟩
    · exact absurd h (inner_layer_empty_of_odd i hn p)
    · exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, Or.inr h⟩

/-- **AND THE TORUS IS THE BOX PLUS THE SEAM.** On the box
`BoxOddReflection.crossForm_odd_eq_zero` says that at odd side no site of the half is adjacent to
any mirror at all; on the torus the seam always is.

**The hypothesis is `2 ≤ n` and NOT `Odd n`**, which is not what I expected when I wrote the
statement — the compiler reported `hn` unused and it was right. The seam is adjacent to its own
mirror at every side length from two, and parity has nothing to do with it. What parity decides is
only whether the seam has company: at even side the innermost layer is adjacent too, at odd side
it is empty (`inner_layer_empty_of_odd`) and the seam is alone. So the contrast with the box is
sharpest at odd side but it is not a fact about odd side. -/
theorem exists_adj_revSite_torus (i : Fin d) (h2 : 2 ≤ n) :
    ∃ p ∈ strictLower i n, (torusGraph d n).Adj p (revSite (n := n) i p) := by
  have hmem : (fun _ => ⟨0, by omega⟩ : Site d n) ∈ strictLower i n := by
    rw [mem_strictLower]; simp; omega
  exact ⟨_, hmem, (adj_torus_revSite_iff_any i n hmem hmem).mpr ⟨rfl, Or.inr (by simp)⟩⟩

end TorusAdjAnySide
