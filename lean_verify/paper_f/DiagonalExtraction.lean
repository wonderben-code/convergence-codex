import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace DiagonalExtraction

open Filter Topology

/-- **COUNTABLY MANY UNIFORMLY BOUNDED REAL SEQUENCES HAVE ONE COMMON CONVERGENT SUBSEQUENCE.**
`f j n` is the `j`-th sequence at index `n`, bounded by `C j` uniformly in `n`. -/
theorem exists_subseq_tendsto_pi (f : ℕ → ℕ → ℝ) (C : ℕ → ℝ) (hb : ∀ j n, |f j n| ≤ C j) :
    ∃ (a : ℕ → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ j, Tendsto (fun k => f j (φ k)) atTop (𝓝 (a j)) := by
  have hK : IsCompact (Set.pi Set.univ (fun j => Set.Icc (-C j) (C j))) :=
    isCompact_univ_pi fun j => isCompact_Icc
  have hmem : ∀ n, (fun j => f j n) ∈ Set.pi Set.univ (fun j => Set.Icc (-C j) (C j)) := by
    intro n j _
    exact abs_le.mp (hb j n)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  exact ⟨a, φ, hφ, fun j => (tendsto_pi_nhds.mp hlim) j⟩

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
