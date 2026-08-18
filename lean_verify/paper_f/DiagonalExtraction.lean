import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Diagonal extraction: one subsequence for countably many bounded sequences

`F4_3h_InfiniteVolumeLimit.diagonal_extraction` proves `0 < 1 ∧ 1 ≤ 1` and describes, in its
docstring, the statement it is standing in for: given countably many observables `O₁, O₂, …`, a
**single** subsequence of volumes along which **all** of `⟨Oⱼ⟩_L` converge at once.

`ERRATUM 197`'s audit corrected that placeholder's recorded reason — it said the real statement
*"requires topology/sequences in Mathlib"*, and Mathlib has had Bolzano–Weierstrass throughout
(`F4_3h.bolzano_weierstrass_real`, 17 Aug). The **diagonal** half was then recorded, in the same
correction, as *"a **construction** — nested subsequences and a diagonal — which nobody in this
estate has built"*.

> **`exists_subseq_tendsto_pi`** — that construction, built. Countably many uniformly bounded real
> sequences have one common convergent subsequence.

## And it is not a diagonal argument

Nested subsequences and a diagonal is how the statement is proved by hand. It is **not** how it is
proved here, and the difference is the whole content of this file: the tuple of all the sequences is
a single point moving in the product `∏ⱼ [−Cⱼ, Cⱼ]`, that product is **compact** by Tychonoff
(`isCompact_univ_pi`), a countable product of metric spaces is **first countable**, and a compact
first-countable space is sequentially compact (`IsCompact.tendsto_subseq`). Convergence in the
product topology **is** simultaneous convergence in every coordinate (`tendsto_pi_nhds`).

So the recorded obstacle was real — nobody had built it — but the thing to build was an application
of two library facts, not an induction. That is the same shape `ERRATUM 197` records: **the
obstacle was named correctly and its size was not.**

## What this does NOT do

**It does not touch `OS4` or the infinite-volume limit.** `F4_3h`'s docstring wants this for a
sequence of finite-volume expectations, and **nothing here supplies those expectations, their
uniform bounds, or the identification of the limit as a state.** This is the extraction lemma alone;
the physics input — that the finite-volume expectations *are* uniformly bounded — is exactly what
`W2` records as missing, and it is untouched.

**And a common subsequence is not a limit that is independent of it.** Different subsequences may
give different limits; nothing here says the limit is unique, and uniqueness is a separate
statement about the sequence.

**No published tag moves.**

## SUPERSEDED IN PART THE SAME DAY BY §1, AND THE THREE WORDS THAT DATED IT

The summary line above says *"countably many uniformly bounded **real** sequences"*, and the
compactness paragraph says the product is *"`∏ⱼ [−Cⱼ, Cⱼ]`"*. **Both sentences are quoted, not
edited** (`ERRATUM 94`), and both are narrower than the argument they describe. §1 removes three
hypotheses that were never used — the index is any **countable** type rather than `ℕ`, the values
lie in any first-countable spaces rather than in `ℝ`, and the confinement is to any **compact
sets** rather than to intervals — and gains a conclusion, since the limit is now known to stay in
the same compact set instead of having that recovered afterwards by `limit_abs_le`. The `ℝ`-valued
`ℕ`-indexed statements in §2 are unchanged in **statement**, because `F4_3h` cites one of them;
their proofs now run through §1.

**This is not a correction of an error.** §2 was true and its route was the route. What it was
was *specific* — and the specificity was in the write-up, not in the mathematics, which is worth
recording separately from the cases where a narrow statement reflects a narrow proof.

**`exists_subseq_tendsto_pi_norm` is the shape the application actually has**: correlation
functions are complex-valued and indexed by test functions rather than by `ℕ`. **That does not
bring the application any closer** — the missing input is still the uniform bounds, and §"What this
does NOT do" above stands word for word.

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace DiagonalExtraction

open Filter Topology

/-! ## 1. The statement with nothing real, nothing countable-by-`ℕ`, and nothing bounded in it

**ADDED 18 AUGUST 2026, ONE HYPOTHESIS AT A TIME.** §2 below was written first, for sequences of
**reals** indexed by **`ℕ`** and confined to **intervals**. None of the three is used. What the
argument needs is that the *product* be compact and first-countable, so the index may be any
countable type, the values may live in any first-countable spaces, and the confinement may be to
any compact sets. The conclusion gains a clause for free: **the limit stays in the same compact
set**, which the interval version had to recover afterwards (`limit_abs_le`). -/

/-- **ONE SUBSEQUENCE FOR A COUNTABLE FAMILY OF SEQUENCES CONFINED TO COMPACT SETS.** The index
type `ι` is any countable type, the `j`-th sequence lives in its own space `X j`, and `s j` is a
compact set containing it. -/
theorem exists_subseq_tendsto_pi_of_isCompact {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ j, TopologicalSpace (X j)] [∀ j, FirstCountableTopology (X j)]
    (s : ∀ j, Set (X j)) (hs : ∀ j, IsCompact (s j))
    (f : ∀ j, ℕ → X j) (hf : ∀ j n, f j n ∈ s j) :
    ∃ (a : ∀ j, X j) (φ : ℕ → ℕ), StrictMono φ ∧ (∀ j, a j ∈ s j) ∧
      ∀ j, Tendsto (fun k => f j (φ k)) atTop (𝓝 (a j)) := by
  have hK : IsCompact (Set.pi Set.univ s) := isCompact_univ_pi hs
  have hmem : ∀ n, (fun j => f j n) ∈ Set.pi Set.univ s := fun n j _ => hf j n
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact ⟨a, φ, hφ, fun j => ha j (Set.mem_univ j), fun j => (tendsto_pi_nhds.mp hlim) j⟩

/-- **THE NORMED-SPACE FORM, WHICH IS THE ONE AN OBSERVABLE FAMILY HAS.** Correlation functions are
complex and are indexed by test functions, not by `ℕ`; this asks only that the index be countable
and the target proper (`ℂ`, `ℝ`, and every finite-dimensional normed space are). -/
theorem exists_subseq_tendsto_pi_norm {ι : Type*} [Countable ι] {E : Type*}
    [NormedAddCommGroup E] [ProperSpace E] (f : ι → ℕ → E) (C : ι → ℝ)
    (hb : ∀ j n, ‖f j n‖ ≤ C j) :
    ∃ (a : ι → E) (φ : ℕ → ℕ), StrictMono φ ∧ (∀ j, ‖a j‖ ≤ C j) ∧
      ∀ j, Tendsto (fun k => f j (φ k)) atTop (𝓝 (a j)) := by
  obtain ⟨a, φ, hφ, hmem, hlim⟩ :=
    exists_subseq_tendsto_pi_of_isCompact (fun j => Metric.closedBall (0 : E) (C j))
      (fun j => isCompact_closedBall 0 (C j)) f (fun j n => by
        simpa [Metric.mem_closedBall, dist_zero_right] using hb j n)
  exact ⟨a, φ, hφ, fun j => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hmem j, hlim⟩

/-! ## 2. The real, `ℕ`-indexed case, which is now a corollary

The statements below are unchanged — `F4_3h_InfiniteVolumeLimit.diagonal_extraction_real` cites the
first of them — but their **proofs** now go through §1 rather than through `Set.Icc` directly. -/

/-- **COUNTABLY MANY UNIFORMLY BOUNDED REAL SEQUENCES HAVE ONE COMMON CONVERGENT SUBSEQUENCE.**
`f j n` is the `j`-th sequence at index `n`, bounded by `C j` uniformly in `n`. -/
theorem exists_subseq_tendsto_pi (f : ℕ → ℕ → ℝ) (C : ℕ → ℝ) (hb : ∀ j n, |f j n| ≤ C j) :
    ∃ (a : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ j, Tendsto (fun k => f j (φ k)) atTop (𝓝 (a j)) := by
  obtain ⟨a, φ, hφ, -, hlim⟩ :=
    exists_subseq_tendsto_pi_norm f C (fun j n => by simpa [Real.norm_eq_abs] using hb j n)
  exact ⟨a, φ, hφ, hlim⟩

/-- The same with a single bound, which is the shape a uniform estimate produces. -/
theorem exists_subseq_tendsto_pi_of_uniform (f : ℕ → ℕ → ℝ) (C : ℝ) (hb : ∀ j n, |f j n| ≤ C) :
    ∃ (a : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ j, Tendsto (fun k => f j (φ k)) atTop (𝓝 (a j)) :=
  exists_subseq_tendsto_pi f (fun _ => C) fun j n => hb j n

/-- **AND THE LIMITS INHERIT THE BOUND.** Worth stating because the next step in an
infinite-volume argument is to check the limit is a state, and boundedness is the first thing it
needs. -/
theorem limit_abs_le (f : ℕ → ℕ → ℝ) (C : ℕ → ℝ) (hb : ∀ j n, |f j n| ≤ C j)
    {a : ℕ → ℝ} {φ : ℕ → ℕ} (hlim : ∀ j, Tendsto (fun k => f j (φ k)) atTop (𝓝 (a j))) (j : ℕ) :
    |a j| ≤ C j := by
  refine le_of_tendsto ((hlim j).abs) ?_
  exact Eventually.of_forall fun k => hb j (φ k)

end DiagonalExtraction
