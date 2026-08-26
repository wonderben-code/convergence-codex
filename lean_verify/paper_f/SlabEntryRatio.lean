import SpectralEntryRatio
import IsingSlabTopRatio

/-!
# The entry-ratio route, at an arbitrary cross-section, and one stale sentence

`IsingSlabTopRatio.UniformSubTopRatioFam` is `WALLS` §W4 §6 item 3 for an arbitrary indexed family
of cross-sections, and its docstring ends: *"No route is recorded, in any dimension."*

**That sentence was true when written and is not now.** `SpectralEntryRatio.subTop_ratio_le` is a
route, and it is stated for an arbitrary finite Hermitian matrix — so it applies at every
cross-section in every dimension, with nothing to adapt. This file says so as a theorem rather
than as a remark, which is the only way to retire a sentence of that shape.

> `subTopRatioG_le_of_entries` — at any cross-section, if every entry of the transfer matrix lies
> in `[a, b]` with `0 < a`, then `subTopRatioG β E ≤ √(b² − a²)/a`.
>
> `uniformSubTopRatioFam_of_entries` — and if one such pair `[a, b]` serves a whole FAMILY, with
> `b² < 2a²`, then `UniformSubTopRatioFam` holds for that family. **That is the item, discharged
> under a hypothesis.**

## What the hypothesis costs, and it is the same number as before

The hypothesis is that a single interval `[a, b]` with `b < a√2` contains the entries of every
member's transfer matrix at once. `IsingSlabTransfer.transferG_apply` gives those entries as
`exp(β·E σ/2)·exp(β·interG σ τ)·exp(β·E τ/2)`, and both the section energy `E` and the coupling
`interG` are sums over the cross-section — so their range, and with it the entry ratio, grows with
the cross-section. **The hypothesis therefore fails for the Ising family at every `β > 0`, for
exactly the reason `SpectralEntryRatio`'s header computes in the two-dimensional case**, and the
generalisation to arbitrary cross-sections changes nothing about that.

**So the item does not move and this file does not claim it does.** What changes is that
*"no route is recorded"* becomes *"a route is recorded, and here is the hypothesis it needs and
why the Ising family does not satisfy it"* — which is a smaller statement and a true one.

**And the family version is worth stating separately from the single-matrix one**, because the
item's whole content is a quantifier order: `∀ i, subTopRatioG < 1` is proved and
`∃ δ, ∀ i, ≤ 1 − δ` is not. `uniformSubTopRatioFam_of_entries` produces the `δ` **before** the
`i` — it is `1 − √(b² − a²)/a`, built from the family's shared interval and nothing else — so it
is a statement of the right shape, waiting on a hypothesis rather than on a rearrangement.
-/

namespace SlabEntryRatio

open Finset IsingSlabTransfer IsingSlabTopRatio

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## 1. At one cross-section -/

/-- **THE ENTRY-RATIO BOUND AT AN ARBITRARY CROSS-SECTION.** `SpectralEntryRatio.subTop_ratio_le`
bounds each ratio off the top; `subTopRatioG` is their supremum, so the same number bounds it. -/
theorem subTopRatioG_le_of_entries [Nonempty V] (β : ℝ) (E : Cross V → ℝ) {a b : ℝ} (ha : 0 < a)
    (hlo : ∀ σ τ, a ≤ transferG β E σ τ) (hhi : ∀ σ τ, transferG β E σ τ ≤ b) :
    subTopRatioG β E ≤ Real.sqrt (b ^ 2 - a ^ 2) / a := by
  refine Finset.sup'_le _ _ fun q hq => ?_
  exact SpectralEntryRatio.subTop_ratio_le (transferG_isHermitian β E) ha hlo hhi
    (topIndexG_max β E) inferInstance (Finset.mem_erase.mp hq).1

/-! ## 2. Along a family, which is where the item lives -/

/-- **THE ITEM, DISCHARGED UNDER A HYPOTHESIS.** If one interval `[a, b]` with `b² < 2a²` contains
the entries of every member's transfer matrix, the family has a uniform sub-top ratio — and the
`δ` is produced from `a` and `b` alone, before any member is named.

**The hypothesis is not satisfied by the Ising family at any `β > 0`**; this file's header says
why, and the reason is the one `SpectralEntryRatio` computes. -/
theorem uniformSubTopRatioFam_of_entries {ι : Type*} {W : ι → Type*} [∀ i, Fintype (W i)]
    [∀ i, DecidableEq (W i)] [∀ i, Nonempty (W i)] (E : ∀ i, Cross (W i) → ℝ) (β : ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : b ^ 2 < 2 * a ^ 2)
    (hlo : ∀ (i : ι) (σ τ : Cross (W i)), a ≤ transferG β (E i) σ τ)
    (hhi : ∀ (i : ι) (σ τ : Cross (W i)), transferG β (E i) σ τ ≤ b) :
    UniformSubTopRatioFam E β := by
  have hlt : Real.sqrt (b ^ 2 - a ^ 2) < a := (Real.sqrt_lt' ha).mpr (by linarith)
  refine ⟨1 - Real.sqrt (b ^ 2 - a ^ 2) / a, ?_, fun i => ?_⟩
  · have : Real.sqrt (b ^ 2 - a ^ 2) / a < 1 := by
      rw [div_lt_one ha]; exact hlt
    linarith
  · have := subTopRatioG_le_of_entries (V := W i) β (E i) ha (hlo i) (hhi i)
    linarith

end SlabEntryRatio
