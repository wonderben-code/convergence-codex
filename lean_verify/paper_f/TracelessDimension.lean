import SlAbelianGeneral

/-!
# `dim sl(ι) = |ι|² − 1`, at every finite index type, once instead of three times

`CascadeFoundation` proves the dimension of the traceless complex matrices **three times**:

```
traceless_dim_2 : finrank ℂ (TracelessMatrix 2) = 3
traceless_dim_3 : finrank ℂ (TracelessMatrix 3) = 8
traceless_dim_4 : finrank ℂ (TracelessMatrix 4) = 15
```

each by its own rank–nullity argument, and there is no statement at general `n`. **That is the
restriction `PROOF_STRATEGY` §7 rule 3 asks to remove**, and `SlAbelianGeneral.tracelessSub` — the
traceless matrices at an arbitrary finite index type — is already in the estate, built for the
abelian-subalgebra count and never used for this.

**The asymmetry is worth naming.** The corresponding **real, skew-Hermitian** statement has been
general since it was written: `TracelessSkewDimension.finrank_traceless_add` gives
`finrank ℝ (traceless n) + 1 = n²` *"for every `n ≥ 1`"*, and derives `3`, `8`, `15` as instances.
**The complex side is the one that stayed at three cases**, and it stayed there while a file two
directories away did the same argument once.

## What is proved

> **`finrank_tracelessSub`** — for every finite nonempty `ι`,
> `finrank ℂ (tracelessSub ι) = (card ι)² − 1`. Rank–nullity on `Matrix.traceLinearMap`, which is
> surjective because `Matrix.single i i c` has trace `c`.
>
> **`finrank_tracelessMatrix`** — the same at `ι = Fin n`, `0 < n`:
> `finrank ℂ (TracelessMatrix n) = n² − 1`, which is the statement `CascadeFoundation` did not have.
>
> **`traceless_dim_two_three_four`** — and it reproduces the estate's three numbers, `3`, `8`, `15`,
> from the general theorem.

**`CascadeFoundation`'s three theorems are kept and are not withdrawn.** They are correct, they are
cited across the estate, and nothing here replaces them. What this file adds is the statement they
are instances of — which is the thing a fourth case would otherwise have needed a fourth proof for.

## What this is NOT

**It is no deeper than rank–nullity.** The content is that `trace` is onto and that
`Matrix ι ι ℂ` has dimension `|ι|²`; both are Mathlib's. The value here is the quantifier, not the
argument.

**It says nothing about `su(n)`**, the real form. `TracelessSkewDimension` has that case and this
file neither imports nor touches it; `ERRATUM 316` is the record of what confusing the two costs.

**It is not a Lie-algebra statement.** `tracelessSub ι` is a submodule of matrices; no bracket, no
`LieSubalgebra`, and the name `sl(ι)` in this header is prose.

**No wall moves. No published tag moves.**

Machine verification: Lean 4.29.1 + Mathlib v4.29.1. 0 sorry, 0 new axioms.
-/

namespace TracelessDimension

open Matrix SlAbelianGeneral

/-- **THE TRACE IS ONTO**, witnessed by a single matrix unit on the diagonal. -/
theorem traceLinearMap_surjective (ι : Type*) [Fintype ι] [Nonempty ι] :
    Function.Surjective (Matrix.traceLinearMap ι ℂ ℂ) := by
  classical
  intro c
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact ⟨Matrix.single i₀ i₀ c, Matrix.trace_single_eq_same i₀ c⟩

/-- **`dim sl(ι) = |ι|² − 1`, AT EVERY FINITE NONEMPTY INDEX TYPE.** -/
theorem finrank_tracelessSub (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι] :
    Module.finrank ℂ (tracelessSub ι) = Fintype.card ι ^ 2 - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap ι ℂ ℂ)
  rw [LinearMap.range_eq_top.mpr (traceLinearMap_surjective ι), finrank_top,
    Module.finrank_self, Module.finrank_matrix, Module.finrank_self, mul_one] at h
  have hc : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ‹Nonempty ι›
  have hsq : Fintype.card ι * Fintype.card ι = Fintype.card ι ^ 2 := by ring
  rw [hsq] at h
  have h' : 1 + Module.finrank ℂ (tracelessSub ι) = Fintype.card ι ^ 2 := h
  omega

/-- The same at `Fin n`, which is the form `CascadeFoundation` states three instances of and no
general case. `SlAbelianGeneral.tracelessSub_fin` is the `rfl` that connects them. -/
theorem finrank_tracelessMatrix (n : ℕ) (hn : 0 < n) :
    Module.finrank ℂ (TracelessMatrix n) = n ^ 2 - 1 := by
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [← tracelessSub_fin n, finrank_tracelessSub (Fin n), Fintype.card_fin]

/-- **AND IT REPRODUCES THE ESTATE'S THREE NUMBERS.** `CascadeFoundation.traceless_dim_2`, `_3` and
`_4` are kept and are not withdrawn; this records that they are instances of one statement rather
than three separate facts. -/
theorem traceless_dim_two_three_four :
    Module.finrank ℂ (TracelessMatrix 2) = 3
      ∧ Module.finrank ℂ (TracelessMatrix 3) = 8
      ∧ Module.finrank ℂ (TracelessMatrix 4) = 15 :=
  ⟨by rw [finrank_tracelessMatrix 2 (by norm_num)]; norm_num,
   by rw [finrank_tracelessMatrix 3 (by norm_num)]; norm_num,
   by rw [finrank_tracelessMatrix 4 (by norm_num)]; norm_num⟩

end TracelessDimension
